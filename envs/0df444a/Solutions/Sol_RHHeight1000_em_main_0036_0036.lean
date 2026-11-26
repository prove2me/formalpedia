-- Prove2me | solution 1 for RHHeight1000.em_main_0036_0036
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T09:39:13.651188+00:00
-- url     : https://prove2.me/submissions/6c4b6564-36cf-4353-a36a-2eab5f1b8378

import Definitions.Def_RHT1000_Support_20261118_S005
/- Copyright (c) 2026 Salvatore Mercuri, Bhavik Mehta.
Apache 2.0 license; see the source project LICENSE. -/
set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def EMRow36.d0 := @PSigma Zeta.Certificates.ZIntervalEM fun (I : Zeta.Certificates.ZIntervalEM) => Zeta.Certificates.ZIntervalEM.Certificate I

noncomputable def EMRow36.d1 := @NonemptyInterval Real Real.instLE

noncomputable def EMRow36.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h

noncomputable def EMRow36.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) (fc sc fb sb : Nat) => Zeta.Certificates.ZIntervalEM.mk (EMRow36.d2 a b h) fc sc fb sb

noncomputable def ep0 := nat_lit 26986075409044028275299783

noncomputable def ep1 := nat_lit 4294967296000000000000000

noncomputable def ep2 := nat_lit 26986075409044045455168967

noncomputable abbrev qz268 := (@instHMul Real Real.instMul)

noncomputable abbrev qz0 := qz268

noncomputable abbrev qz269 := (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 2 1) Real.pi)

noncomputable def ep3 := @BSN.isNear_log_image_fff qz269 884279719003555 140737488355328 1 500000000000000 ep0 ep1 ep2 ep1 4138529546116343 2251799813685248 31250000017321 8660500000000000000 4138529546116343 2251799813685248 31250000017321 8660500000000000000 963576 524288

noncomputable abbrev qz270 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 2 1) Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) BSN.pi_near_15 rfl)

noncomputable def ep4 := @ep3 3 524288 qz270 rfl rfl rfl rfl

noncomputable def ep5 := nat_lit 53972150818088056550599566

noncomputable def ep6 := nat_lit 34359738368000000000000000

noncomputable def ep7 := nat_lit 9806206225044028275299783

noncomputable def ep8 := nat_lit 44165944593044028275299783

noncomputable def ep9 := nat_lit 13681445815609410487519367394620474863599256634174726093703677122907123617368241606644861540940610176751640793056574796245399519365549113997355475306157239709119582688278313060810592403844863400465080549957745

noncomputable def ep10 := nat_lit 231714499556395493334623298703961145503103241611736774613091488581016477543539392410113701224645713379230392133956226737605624599560350113120270717249177907454870984269546186598262646369758174842349131395304

noncomputable def ep11 := nat_lit 8978369550011295664474073352761810093897501552430546263638635096022803738134167562509900960712119243631997923545019968443113540909076206607473711060286601587364321108377403290080403445693385008949995305

noncomputable def ep12 := BSN.log_dyadic_bound ep7 ep8 5 4 ep9 1048576 277136 ep10 ep11 473518 ep5 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep7) (BSN.artanhQ ep8) 0 4 ep10 ep9 ep11 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz271 := (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))

noncomputable abbrev qz1 := qz271

noncomputable def ep13 := ep4 rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep1 4138529546116343 2251799813685248 31250000017321 8660500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep0) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 69433004117575847641088 37778931862957161709568 1000000000554272 277136000000000000000 4138529546116343 2251799813685248 31250000017321 8660500000000000000 (BSN.log_rat_reduce_isNear ep0 ep1 2 ep5 ep6 473518 1048576 24973259072661432 36028797018963968 277136 1000000000000000 rfl rfl rfl rfl (ep12 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep14 := nat_lit 53972150818088090910337934

noncomputable def ep15 := nat_lit 9806206225044045455168967

noncomputable def ep16 := nat_lit 44165944593044045455168967

noncomputable def ep17 := nat_lit 13681445815609453062485491347592146866046743284321690683909457683007658987562290830600045658905080811372395010565947827677605470036294121079488508864180301737865471494204890974265645509835068840465080549957745

noncomputable def ep18 := nat_lit 231714499556396865510889920206523150079811393376960301632499817942333196803513131357563499488546302200815366867712007119763002650772307103678175657719139104636874731038771518520299266622696414842349131395304

noncomputable def ep19 := nat_lit 8978369550011421500876706511871067098718760264493934208903156435737864998391937547068187824077011975074541700434630537294838404525415248443919841847024664017658842168336182958576672102333385008949995305

noncomputable def ep20 := BSN.log_dyadic_bound ep15 ep16 5 4 ep17 1048576 277136 ep18 ep19 473518 ep14 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep15) (BSN.artanhQ ep16) 0 4 ep18 ep17 ep19 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep21 := ep13 (BSN.isNear_log_sfrac ep2 ep1 4138529546116343 2251799813685248 31250000017321 8660500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep2) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 69433004117575847641088 37778931862957161709568 1000000000554272 277136000000000000000 4138529546116343 2251799813685248 31250000017321 8660500000000000000 (BSN.log_rat_reduce_isNear ep2 ep1 2 ep14 ep6 473518 1048576 24973259072661432 36028797018963968 277136 1000000000000000 rfl rfl rfl rfl (ep20 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable abbrev qz272 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)

noncomputable abbrev qz2 := (Real.log qz272)

theorem EMRow36.d4 : Enclosure.Real.IsNear qz2 Bool.false 120447 65536 3 524288 := @Enclosure.Real.IsNear.of_eq qz2 (Real.log qz269) Bool.false 120447 65536 3 524288 BSN.log_two_pi_eq (@Enclosure.Real.IsNear.recentre' (Real.log qz269) Bool.false 963576 524288 3 524288 120447 65536 3 524288 (ep21 rfl rfl rfl rfl rfl rfl rfl rfl) rfl)

noncomputable def ep22 := nat_lit 8589934592000000000000000

noncomputable def ep23 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 ep0 ep22 ep2 ep22 1200336 1048576 1 277136 1200336 1048576 1 277136 600168 524288 2 524288 BSN.pi_near_15 rfl rfl rfl

noncomputable def ep24 := nat_lit 17179869184000000000000000

noncomputable def ep25 := nat_lit 18396140817044028275299783

noncomputable def ep26 := nat_lit 35576010001044028275299783

noncomputable def ep27 := nat_lit 145019262663961446558303139663424756232419223153299357158415217874016130572233056993847515999529612750616182853355499335896178729185698845314776375864537073527142908641610750276034469165612529925303649396973267518946591078603565291376312767403717761600170009932259137778521478520425507632472584532570900560707662248426541531715360699177249902784721815296292248142738824858695953661559845440650653128788875447728828657762006237171740033404723254477174341920697506370253193455781322964835857351124092897592956162654178130575

noncomputable def ep28 := nat_lit 15500762873619990602332184736899274490522931101512051618692838888825382235673431503644115344741331161500627469184702974962114537943617674254904297224139410345221262767191485292268260077615645253784097850065864022184521411511133693085443040736512010941548648374196772723338837137976260321103066698629790037694560548409922339907589559883712609967105556007429010014773911317423638534096849366294542840133852248768895750397896505791271178551667935288585787166713880920071720072716082683081155281219708172458141800988558163320

noncomputable def ep29 := nat_lit 12900190794487083783367107939442176642390171280542213571554777169279725287102813254708993369099729304728646904879886535518616983985412662170766446331701281703998252143668221340329975389245922410714088123244705567402747658401492589451585970559635763980329972215329212888079422466283203384882259392047898400615815810081169907384366653346471604103896809335921621947903075223769953790093549808584241881353287841076643853121427928248525828402335494512605306631304432120211393210317325496757155861061354331245840675149075

noncomputable def ep30 := BSN.log_dyadic_bound ep25 ep26 11 10 ep27 1048576 277136 ep28 ep29 1200336 ep5 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep25) (BSN.artanhQ ep26) 0 10 ep28 ep27 ep29 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep31 := nat_lit 18396140817044045455168967

noncomputable def ep32 := nat_lit 35576010001044045455168967

noncomputable def ep33 := nat_lit 145019262663962847171784895425483977818796535899227200426399035286881207006285364467913811844950531107314785650583974625982406238691319033447632878979985852280879486690814033867010958364699188952871572448188560932645032521756218245629809291975913196623825614492380080480004685076434733043183791438169545293975334857826316990371107134320667652578346815517853870648072772035977941843998949310557583393428557296298890786965786350523173236912472938174255438182435383147950274229549088258679583524155427309880956162654178130575

noncomputable def ep34 := nat_lit 15500762873620157189619721156942591192100275120160672416764593300158228469749443299607348495591439275767946573253526107895503597951484257520435868240203420954375895980141891044871083424251900562230440202302413072793440172565998181227591194192658878334739610458454844032013325963992941389843551995646587189684848765634635122388286241104146031552341815777883628509454807838726994150833304950745987647656768534710890974432620160470644835720379148964170536679305861738540146791997074363921127776563807649880221800988558163320

noncomputable def ep35 := nat_lit 12900190794487324729109480814509220959173684627296055849229843377126536688487849343376525559792931631054411655715865486295286288812423905434305314401904993536755333953308594664509631000767632482919425633906965368325056855874260596615770736441041599390097968820060635361729170158825410327022636428624381203910573184452046894301676992229743752846881064485858738985580654099214803581683226335297196686880535448467637789069028262446657986458573827723305156755787640135484017403116612632808333639900906331245840675149075

noncomputable def ep36 := BSN.log_dyadic_bound ep31 ep32 11 10 ep33 1048576 277136 ep34 ep35 1200336 ep14 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep31) (BSN.artanhQ ep32) 0 10 ep34 ep33 ep35 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep37 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 600168 524288 2 524288 75021 65536 1 262144 (ep23 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep22 1200336 1048576 1 277136 Bool.false (BSN.logfrac_isNear ep5 ep24 1 ep0 ep22 1200336 1048576 277136 rfl rfl rfl (ep30 rfl))) (BSN.isNear_log_sfrac ep2 ep22 1200336 1048576 1 277136 Bool.false (BSN.logfrac_isNear ep14 ep24 1 ep2 ep22 1200336 1048576 277136 rfl rfl rfl (ep36 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl

theorem EMRow36.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 75021 65536 1 262144 := ep37

noncomputable abbrev qz577 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 113311 1000)))

noncomputable abbrev qz530 := qz577

noncomputable abbrev qz273 := qz530

noncomputable abbrev qz3 := (BSN.headSumC qz273 9)

noncomputable abbrev qz578 := (@instHAdd Complex Complex.instAdd)

noncomputable abbrev qz531 := qz578

noncomputable abbrev qz274 := qz531

noncomputable abbrev qz4 := qz274

noncomputable abbrev qz5 := qz273

noncomputable abbrev qz532 := (@instHPow Complex Complex Complex.instPow)

noncomputable abbrev qz275 := qz532

noncomputable abbrev qz6 := qz275

noncomputable abbrev qz533 := (@Neg.neg Complex Complex.instNeg qz577)

noncomputable abbrev qz276 := qz533

noncomputable abbrev qz7 := qz276

noncomputable abbrev qz277 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 8) qz7)

noncomputable def ep38 := @Enclosure.Complex.IsNear.of_eq qz3 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 8) qz277) Bool.false 693346171273 549755813888 26565759242575 9522320452354048 Bool.true 32672618383 274877906944 26538242894123 9522320452354048

noncomputable def ep39 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 8) qz277 Bool.false 443856017507 274877906944 5944402555093 2380580113088512 Bool.true 33075969359 274877906944 23759137287267 9522320452354048 Bool.true

noncomputable abbrev qz278 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 7) qz7)

noncomputable def ep40 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 8) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 7) qz278) Bool.false 443856017507 274877906944 5944402555093 2380580113088512 Bool.true 33075969359 274877906944 23759137287267 9522320452354048

noncomputable def ep41 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 7) qz278 Bool.false 1428119320303 1099511627776 41598128231531 19044640904708096 Bool.false 47956766307 549755813888 1298949592565 595145028272128 Bool.false

noncomputable def ep42 := nat_lit 1952099409229177293897728

noncomputable abbrev qz279 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 6) qz7)

noncomputable def ep43 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 7) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 6) qz279) Bool.false 1428119320303 1099511627776 41598128231531 19044640904708096 Bool.false 47956766307 549755813888 1298949592565 595145028272128

noncomputable def ep44 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 6) qz279 Bool.false 800056664501 549755813888 17582884544975 9522320452354048 Bool.false 510528163827 1099511627776 35124210866613 19044640904708096 Bool.true

noncomputable abbrev qz280 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 5) qz7)

noncomputable def ep45 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 6) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 5) qz280) Bool.false 800056664501 549755813888 17582884544975 9522320452354048 Bool.false 510528163827 1099511627776 35124210866613 19044640904708096

noncomputable def ep46 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 5) qz280 Bool.false 557124789525 549755813888 878411003763 595145028272128 Bool.false 586163012557 1099511627776 28082746411805 19044640904708096 Bool.false

noncomputable abbrev qz281 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 4) qz7)

noncomputable def ep47 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 5) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 4) qz281) Bool.false 557124789525 549755813888 878411003763 595145028272128 Bool.false 586163012557 1099511627776 28082746411805 19044640904708096

noncomputable def ep48 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 4) qz281 Bool.false 282248455443 549755813888 5057651801921 4761160226177024 Bool.false 73453156125 137438953472 1263894719151 1190290056544256 Bool.false

noncomputable abbrev qz534 := (@Nat.cast Complex Complex.instNatCast 3)

noncomputable abbrev qz282 := qz534

noncomputable abbrev qz8 := qz282

noncomputable def ep49 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 4) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz7)) Bool.false 282248455443 549755813888 5057651801921 4761160226177024 Bool.false 73453156125 137438953472 1263894719151 1190290056544256

noncomputable def ep50 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz7) Bool.false 322040451151 1099511627776 11147276792391 19044640904708096 Bool.false 3707275 4294967296 695571037231 1190290056544256 Bool.false

noncomputable abbrev qz535 := (@Nat.cast Complex Complex.instNatCast 2)

noncomputable abbrev qz283 := qz535

noncomputable abbrev qz9 := qz283

noncomputable def ep51 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 3) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz7)) Bool.false 322040451151 1099511627776 11147276792391 19044640904708096 Bool.false 3707275 4294967296 695571037231 1190290056544256

noncomputable def ep52 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz7) Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.true

noncomputable abbrev qz284 := (Enclosure.sfrac Bool.false 0 1)

noncomputable abbrev qz10 := qz284

noncomputable def ep53 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz10) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz5)

noncomputable abbrev qz536 := (@Nat.cast Real Real.instNatCast 2)

noncomputable abbrev qz11 := (@Inv.inv Real Real.instInv (Real.sqrt qz536))

noncomputable abbrev qz579 := (Enclosure.sfrac Bool.false 113311 1000)

noncomputable abbrev qz537 := qz579

noncomputable abbrev qz285 := qz537

noncomputable abbrev qz286 := (Enclosure.sfrac Bool.false 2 1)

noncomputable abbrev qz12 := (@HMul.hMul Real Real Real qz268 qz285 (Real.log qz286))

noncomputable abbrev qz13 := qz285

noncomputable abbrev qz287 := (@Eq.refl Real qz537)

noncomputable abbrev qz14 := qz287

noncomputable def ep54 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz9 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz11 (Real.cos qz12)) (@HMul.hMul Real Real Real qz0 qz11 (@Neg.neg Real Real.instNeg (Real.sin qz12)))) Bool.true 777471176625 1099511627776 11147276792391 19044640904708096 Bool.false 3707275 4294967296 695571037231 1190290056544256 (BSN.cpow_neg_s_mk qz13 113311 1000 2 qz14 rfl)

noncomputable abbrev qz15 := (@Nat.cast Real Real.instNatCast 1)

noncomputable def ep55 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz536) 1482911 1048576 1 1048576 370727 370728 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz536) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz536 qz15)) Bool.false 1482911 1048576 1 1048576 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz536 qz15)) Bool.false 1482911 1048576 1 1048576 1482911 1048576 1 1048576 (BSN.sqrt_enclosure 2 1 741455 741456 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep56 := BSN.log_dyadic_bound 1 3 6 5 613814355 524288 138568 24381081 945 363408 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 1) (BSN.artanhQ 3) 0 5 24381081 613814355 945 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz288 := (BSN.cosEvenQ 2147483648)

noncomputable abbrev qz289 := (BSN.cosOddQ 2147483648)

noncomputable def ep57 := BSN.cos_dyadic_bound_f 2622549 2147483648 1 0 1048576 277407 0 1 1 0 1 1 1048575 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 2622549) qz288 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 2622549) qz289 0 0 rfl) rfl rfl

noncomputable abbrev qz16 := (@Nat.cast Real Real.instNatCast 1048576)

noncomputable abbrev qz17 := (Real.log qz286)

noncomputable abbrev qz18 := (Enclosure.Real.IsNear.const Bool.false 113311 1000)

noncomputable abbrev qz19 := (@Nat.cast Real Real.instNatCast 151115727451828646838272)

noncomputable abbrev qz290 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 82356247) qz16)

noncomputable abbrev qz291 := (BSN.isNear_log_sfrac 2 1 363408 524288 1 138568 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 363408 524288 138568 rfl rfl rfl (ep56 rfl)))

noncomputable def ep58 := @Enclosure.Real.IsNear.cos_image qz12 qz290 Bool.false 82356247 1048576 859 1048576 Bool.true 1048575 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz12 Bool.false 2573632743 32768000 113311 138568000 82356247 1048576 859 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz17 113311 1000 0 1 363408 524288 1 138568 2573632743 32768000 113311 138568000 qz18 qz291 rfl) rfl) (Enclosure.sfrac_false_div 82356247 1048576) (BSN.cos_reduce2 qz290 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 184545513083328528384) qz19) 226375608064910080 72057594037927936 Bool.false 1048575 1048576 12 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q2 82356247 1048576 226375608064910080 72057594037927936 12 184545513083328528384 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1048575 1048576 184545513083328528384 151115727451828646838272 2622549 2147483648 277407 277136 (ep57 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz292 := (BSN.sinEvenQ 2147483648)

noncomputable abbrev qz293 := (BSN.sinOddQ 2147483648)

noncomputable def ep59 := BSN.sin_dyadic_bound_f 2622549 2147483648 1 0 1048576 277407 0 1 1 0 1 1 1280 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 2622549) qz292 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 2622549) qz293 0 0 rfl) rfl rfl

noncomputable def ep60 := @Enclosure.Real.IsNear.sin_image qz12 qz290 Bool.false 82356247 1048576 859 1048576 Bool.true 1280 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz12 Bool.false 2573632743 32768000 113311 138568000 82356247 1048576 859 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz17 113311 1000 0 1 363408 524288 1 138568 2573632743 32768000 113311 138568000 qz18 qz291 rfl) rfl) (Enclosure.sfrac_false_div 82356247 1048576) (BSN.sin_reduce2 qz290 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 184545513083328528384) qz19) 226375608064910080 72057594037927936 Bool.false 1280 1048576 12 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q2 82356247 1048576 226375608064910080 72057594037927936 12 184545513083328528384 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1280 1048576 184545513083328528384 151115727451828646838272 2622549 2147483648 277407 277136 (ep59 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz294 := (@Enclosure.Real.IsNear.recentre' qz11 Bool.false 741455 1048576 1 1048576 741455 1048576 1 1048576 (ep55 rfl rfl) rfl)

noncomputable def ep61 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz11 (Real.cos qz12)) (@HMul.hMul Real Real Real qz0 qz11 (@Neg.neg Real Real.instNeg (Real.sin qz12))) Bool.true 777471176625 1099511627776 11147276792391 19044640904708096 Bool.false 3707275 4294967296 695571037231 1190290056544256 (@Enclosure.Real.IsNear.mulLit_ft qz11 (Real.cos qz12) 741455 1048576 1 1048576 1048575 1048576 15009811 18162384896 777471176625 1099511627776 11147276792391 19044640904708096 qz294 (@Enclosure.Real.IsNear.recentre' (Real.cos qz12) Bool.true 1048575 1048576 120078488 145299079168 1048575 1048576 15009811 18162384896 (ep58 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz11 (@Neg.neg Real Real.instNeg (Real.sin qz12)) 741455 1048576 1 1048576 5 4096 15009811 18162384896 3707275 4294967296 695571037231 1190290056544256 qz294 (@Enclosure.Real.IsNear.neg (Real.sin qz12) Bool.true 5 4096 15009811 18162384896 (@Enclosure.Real.IsNear.recentre' (Real.sin qz12) Bool.true 1280 1048576 120078488 145299079168 5 4096 15009811 18162384896 (ep60 rfl rfl) rfl)) rfl)

noncomputable abbrev qz295 := (Enclosure.Real.IsNear.const Bool.false 0 1)

noncomputable abbrev qz20 := qz295

noncomputable def ep62 := @ep52 777471176625 1099511627776 11147276792391 19044640904708096 Bool.false 3707275 4294967296 695571037231 1190290056544256 Bool.false 322040451151 322040451151 1099511627776 11147276792391 19044640904708096 Bool.false 3707275 3707275 4294967296 695571037231 1190290056544256 (ep53 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz10 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz20)) (ep54 ep61) rfl rfl

noncomputable abbrev qz296 := (@Nat.cast Real Real.instNatCast 3)

noncomputable abbrev qz21 := (@Inv.inv Real Real.instInv (Real.sqrt qz296))

noncomputable abbrev qz22 := (@HMul.hMul Real Real Real qz268 qz285 (Real.log (Enclosure.sfrac Bool.false 3 1)))

noncomputable def ep63 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz8 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz21 (Real.cos qz22)) (@HMul.hMul Real Real Real qz0 qz21 (@Neg.neg Real Real.instNeg (Real.sin qz22)))) Bool.false 242456459735 1099511627776 9083330415293 19044640904708096 Bool.false 73334523325 137438953472 4440028765 9299141066752 (BSN.cpow_neg_s_mk qz13 113311 1000 3 qz14 rfl)

noncomputable def ep64 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz296) 1816187 1048576 1 1048576 302697 302698 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz296) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz296 qz15)) Bool.false 1816187 1048576 1 1048576 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz296 qz15)) Bool.false 1816187 1048576 1 1048576 1816187 1048576 1 1048576 (BSN.sqrt_enclosure 3 1 908093 908094 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep65 := BSN.log_dyadic_bound 1 2 10 9 171633298636800 524288 138568 16925142283965 34459425 575989 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP 1) (BSN.artanhQ 2) 0 9 16925142283965 171633298636800 34459425 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep66 := nat_lit 501648638704125244453903077862119841

noncomputable def ep67 := nat_lit 2552117751907038475975309555738261585920

noncomputable def ep68 := nat_lit 17864824263349269331827166890167831101440

noncomputable def ep69 := BSN.sin_dyadic_bound_f 841588727 2147483648 2 1 1048576 277407 ep66 ep67 ep66 ep66 ep68 ep66 400493 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 841588727) qz292 0 1 ep66 ep67 ep66 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 841588727) qz293 0 1 ep66 ep68 ep66 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz23 := (Real.log (Enclosure.sfrac Bool.false 3 1))

noncomputable abbrev qz297 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 130531779) qz16)

noncomputable abbrev qz298 := (BSN.isNear_log_sfrac 3 1 575989 524288 1 138568 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 575989 524288 138568 rfl rfl rfl (ep65 rfl)))

noncomputable def ep70 := @Enclosure.Real.IsNear.cos_image qz22 qz297 Bool.false 130531779 1048576 429 524288 Bool.false 400493 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz22 Bool.false 65265889579 524288000 113311 138568000 130531779 1048576 429 524288 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz23 113311 1000 0 1 575989 524288 1 138568 65265889579 524288000 113311 138568000 qz18 qz298 rfl) rfl) (Enclosure.sfrac_false_div 130531779 1048576) (BSN.cos_reduce3 qz297 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 59221541881632908115968) qz19) 226375608064910080 72057594037927936 Bool.false 400493 1048576 19 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q3 130531779 1048576 226375608064910080 72057594037927936 19 59221541881632908115968 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 400493 1048576 59221541881632908115968 151115727451828646838272 841588727 2147483648 277407 277136 (ep69 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep71 := nat_lit 510423550381407695195061911147652317184

noncomputable def ep72 := nat_lit 7656353255721115427925928667214784757760

noncomputable def ep73 := BSN.cos_dyadic_bound_f 841588727 2147483648 2 1 1048576 277407 ep66 ep71 ep66 ep66 ep72 ep66 969080 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 841588727) qz288 0 1 ep66 ep71 ep66 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 841588727) qz289 0 1 ep66 ep72 ep66 rfl rfl rfl rfl) rfl rfl

noncomputable def ep74 := @Enclosure.Real.IsNear.sin_image qz22 qz297 Bool.false 130531779 1048576 429 524288 Bool.true 969080 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz22 Bool.false 65265889579 524288000 113311 138568000 130531779 1048576 429 524288 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz23 113311 1000 0 1 575989 524288 1 138568 65265889579 524288000 113311 138568000 qz18 qz298 rfl) rfl) (Enclosure.sfrac_false_div 130531779 1048576) (BSN.sin_reduce3 qz297 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 59221541881632908115968) qz19) 226375608064910080 72057594037927936 Bool.false 969080 1048576 19 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q3 130531779 1048576 226375608064910080 72057594037927936 19 59221541881632908115968 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 969080 1048576 59221541881632908115968 151115727451828646838272 841588727 2147483648 277407 277136 (ep73 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz299 := (@Enclosure.Real.IsNear.recentre' qz21 Bool.false 605395 1048576 1 1048576 605395 1048576 1 1048576 (ep64 rfl rfl) rfl)

noncomputable def ep75 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz21 (Real.cos qz22)) (@HMul.hMul Real Real Real qz0 qz21 (@Neg.neg Real Real.instNeg (Real.sin qz22))) Bool.false 242456459735 1099511627776 9083330415293 19044640904708096 Bool.false 73334523325 137438953472 4440028765 9299141066752 (@Enclosure.Real.IsNear.mulLit_ff qz21 (Real.cos qz22) 605395 1048576 1 1048576 400493 1048576 7496245 9081192448 242456459735 1099511627776 9083330415293 19044640904708096 qz299 (@Enclosure.Real.IsNear.recentre' (Real.cos qz22) Bool.false 400493 1048576 59969960 72649539584 400493 1048576 7496245 9081192448 (ep70 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz21 (@Neg.neg Real Real.instNeg (Real.sin qz22)) 605395 1048576 1 1048576 121135 131072 7496245 9081192448 73334523325 137438953472 4440028765 9299141066752 qz299 (@Enclosure.Real.IsNear.neg (Real.sin qz22) Bool.true 121135 131072 7496245 9081192448 (@Enclosure.Real.IsNear.recentre' (Real.sin qz22) Bool.true 969080 1048576 59969960 72649539584 121135 131072 7496245 9081192448 (ep74 rfl rfl) rfl)) rfl)

noncomputable def ep76 := @ep50 242456459735 1099511627776 9083330415293 19044640904708096 Bool.false 73334523325 137438953472 4440028765 9299141066752 Bool.false 620670917362789474369536 282248455443 549755813888 5057651801921 4761160226177024 Bool.false 315478903344857088000 73453156125 137438953472 1263894719151 1190290056544256 (ep51 (BSN.head_sum_c_succ qz5 2 3 rfl rfl) (ep62 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep63 ep75) rfl rfl

noncomputable abbrev qz538 := (@Nat.cast Real Real.instNatCast 4)

noncomputable abbrev qz24 := (@Inv.inv Real Real.instInv (Real.sqrt qz538))

noncomputable abbrev qz25 := (@HMul.hMul Real Real Real qz268 qz285 (Real.log (Enclosure.sfrac Bool.false 4 1)))

noncomputable def ep77 := @Enclosure.Complex.IsNear.of_eq qz281 (Complex.mk (@HMul.hMul Real Real Real qz0 qz24 (Real.cos qz25)) (@HMul.hMul Real Real Real qz0 qz24 (@Neg.neg Real Real.instNeg (Real.sin qz25)))) Bool.false 137438167041 274877906944 1969636228183 4761160226177024 Bool.true 1462236443 1099511627776 7860430905389 19044640904708096 (BSN.cpow_neg_s_mk qz13 113311 1000 4 qz14 rfl)

noncomputable def ep78 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz538) 2097153 1048576 1 1048576 262143 262144 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz538) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz538 qz15)) Bool.false 2097153 1048576 1 1048576 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz538 qz15)) Bool.false 2097153 1048576 1 1048576 2097153 1048576 1 1048576 (BSN.sqrt_enclosure 4 1 1048576 1048577 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep79 := nat_lit 318077276165597140789031982421875

noncomputable def ep80 := nat_lit 49379992292270016474244603430625

noncomputable def ep81 := nat_lit 20095619060363156210525625

noncomputable def ep82 := BSN.log_dyadic_bound 3 5 14 13 ep79 524288 138568 ep80 ep81 726817 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base13 (BSN.artanhP 3) (BSN.artanhQ 5) 0 13 ep80 ep79 ep81 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep83 := BSN.cos_dyadic_bound_f 5712042 2147483648 1 0 1048576 277407 0 1 1 0 1 1 1048572 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 5712042) qz288 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 5712042) qz289 0 0 rfl) rfl rfl

noncomputable abbrev qz26 := (@Nat.cast Real Real.instNatCast 524288)

noncomputable abbrev qz27 := (Real.log (Enclosure.sfrac Bool.false 4 1))

noncomputable abbrev qz300 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 82356361) qz26)

noncomputable abbrev qz301 := (BSN.isNear_log_sfrac 4 1 726817 524288 1 138568 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 726817 524288 138568 rfl rfl rfl (ep82 rfl)))

noncomputable abbrev qz302 := (@Nat.cast Real Real.instNatCast 75557863725914323419136)

noncomputable def ep84 := @Enclosure.Real.IsNear.cos_image qz25 qz300 Bool.false 82356361 524288 429 524288 Bool.false 1048572 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz25 Bool.false 82356361087 524288000 113311 138568000 82356361 524288 429 524288 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz27 113311 1000 0 1 726817 524288 1 138568 82356361087 524288000 113311 138568000 qz18 qz301 rfl) rfl) (Enclosure.sfrac_false_div 82356361 524288) (BSN.cos_reduce0 qz300 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 200974644523976097792) qz302) 226375608064910080 72057594037927936 Bool.false 1048572 1048576 25 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q0 82356361 524288 226375608064910080 72057594037927936 25 200974644523976097792 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1048572 1048576 200974644523976097792 75557863725914323419136 5712042 2147483648 277407 277136 (ep83 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep85 := BSN.sin_dyadic_bound_f 5712042 2147483648 1 0 1048576 277407 0 1 1 0 1 1 2789 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 5712042) qz292 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 5712042) qz293 0 0 rfl) rfl rfl

noncomputable def ep86 := @Enclosure.Real.IsNear.sin_image qz25 qz300 Bool.false 82356361 524288 429 524288 Bool.false 2789 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz25 Bool.false 82356361087 524288000 113311 138568000 82356361 524288 429 524288 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz27 113311 1000 0 1 726817 524288 1 138568 82356361087 524288000 113311 138568000 qz18 qz301 rfl) rfl) (Enclosure.sfrac_false_div 82356361 524288) (BSN.sin_reduce0 qz300 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 200974644523976097792) qz302) 226375608064910080 72057594037927936 Bool.false 2789 1048576 25 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q0 82356361 524288 226375608064910080 72057594037927936 25 200974644523976097792 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 2789 1048576 200974644523976097792 75557863725914323419136 5712042 2147483648 277407 277136 (ep85 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz303 := (@Enclosure.Real.IsNear.recentre' qz24 Bool.false 524287 1048576 1 1048576 524287 1048576 1 1048576 (ep78 rfl rfl) rfl)

noncomputable def ep87 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz24 (Real.cos qz25)) (@HMul.hMul Real Real Real qz0 qz24 (@Neg.neg Real Real.instNeg (Real.sin qz25))) Bool.false 137438167041 274877906944 1969636228183 4761160226177024 Bool.true 1462236443 1099511627776 7860430905389 19044640904708096 (@Enclosure.Real.IsNear.mulLit_ff qz24 (Real.cos qz25) 524287 1048576 1 1048576 262143 262144 7496245 9081192448 137438167041 274877906944 1969636228183 4761160226177024 qz303 (@Enclosure.Real.IsNear.recentre' (Real.cos qz25) Bool.false 1048572 1048576 59969960 72649539584 262143 262144 7496245 9081192448 (ep84 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz24 (@Neg.neg Real Real.instNeg (Real.sin qz25)) 524287 1048576 1 1048576 2789 1048576 7496245 9081192448 1462236443 1099511627776 7860430905389 19044640904708096 qz303 (@Enclosure.Real.IsNear.neg (Real.sin qz25) Bool.false 2789 1048576 7496245 9081192448 (@Enclosure.Real.IsNear.recentre' (Real.sin qz25) Bool.false 2789 1048576 59969960 72649539584 2789 1048576 7496245 9081192448 (ep86 rfl rfl) rfl)) rfl)

noncomputable def ep88 := @ep48 137438167041 274877906944 1969636228183 4761160226177024 Bool.true 1462236443 1099511627776 7860430905389 19044640904708096 Bool.false 153141296051248535961600 557124789525 549755813888 878411003763 595145028272128 Bool.false 80561631009828874747904 586163012557 1099511627776 28082746411805 19044640904708096 (ep49 (BSN.head_sum_c_succ qz5 3 4 rfl rfl) (ep76 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep77 ep87) rfl rfl

noncomputable abbrev qz539 := (@Nat.cast Real Real.instNatCast 5)

noncomputable abbrev qz28 := (@Inv.inv Real Real.instInv (Real.sqrt qz539))

noncomputable abbrev qz29 := (@HMul.hMul Real Real Real qz268 qz285 (Real.log (Enclosure.sfrac Bool.false 5 1)))

noncomputable def ep89 := @Enclosure.Complex.IsNear.of_eq qz280 (Complex.mk (@HMul.hMul Real Real Real qz0 qz28 (Real.cos qz29)) (@HMul.hMul Real Real Real qz0 qz28 (@Neg.neg Real Real.instNeg (Real.sin qz29)))) Bool.false 7591621093 17179869184 3528308484767 9522320452354048 Bool.true 37817424365 549755813888 880183056851 2380580113088512 (BSN.cpow_neg_s_mk qz13 113311 1000 5 qz14 rfl)

noncomputable def ep90 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz539) 2344687 1048576 1 1048576 234468 234469 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz539) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz539 qz15)) Bool.false 2344687 1048576 1 1048576 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz539 qz15)) Bool.false 2344687 1048576 1 1048576 2344687 1048576 1 1048576 (BSN.sqrt_enclosure 5 1 1172343 1172344 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep91 := nat_lit 11734546589655452485523914939250625

noncomputable def ep92 := nat_lit 2429970938528035899633153341031900

noncomputable def ep93 := nat_lit 824199001261152424427520000

noncomputable def ep94 := BSN.log_dyadic_bound 2 3 17 16 ep91 524288 138568 ep92 ep93 843808 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base16 (BSN.artanhP 2) (BSN.artanhQ 3) 0 16 ep92 ep91 ep93 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep95 := nat_lit 12096786465687377101185285390340096

noncomputable def ep96 := BSN.cos_dyadic_bound_f 331640456 2147483648 2 1 1048576 277407 ep95 ep71 ep95 ep95 ep72 ep95 1036096 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 331640456) qz288 0 1 ep95 ep71 ep95 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 331640456) qz289 0 1 ep95 ep72 ep95 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz30 := (Real.log (Enclosure.sfrac Bool.false 5 1))

noncomputable abbrev qz304 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11951591) (@Nat.cast Real Real.instNatCast 65536))

noncomputable abbrev qz305 := (BSN.isNear_log_sfrac 5 1 843808 524288 1 138568 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 843808 524288 138568 rfl rfl rfl (ep94 rfl)))

noncomputable abbrev qz306 := (@Nat.cast Real Real.instNatCast 9444732965739290427392)

noncomputable def ep97 := @Enclosure.Real.IsNear.cos_image qz29 qz304 Bool.false 11951591 65536 859 1048576 Bool.false 1036096 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz29 Bool.false 2987897759 16384000 113311 138568000 11951591 65536 859 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz30 113311 1000 0 1 843808 524288 1 138568 2987897759 16384000 113311 138568000 qz18 qz305 rfl) rfl) (Enclosure.sfrac_false_div 11951591 65536) (BSN.cos_reduce0 qz304 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 1458570154240504758272) qz306) 226375608064910080 72057594037927936 Bool.false 1036096 1048576 29 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q0 11951591 65536 226375608064910080 72057594037927936 29 1458570154240504758272 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1036096 1048576 1458570154240504758272 9444732965739290427392 331640456 2147483648 277407 277136 (ep96 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep98 := BSN.sin_dyadic_bound_f 331640456 2147483648 1 0 1048576 277407 0 1 1 0 1 1 161290 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 331640456) qz292 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 331640456) qz293 0 0 rfl) rfl rfl

noncomputable def ep99 := @Enclosure.Real.IsNear.sin_image qz29 qz304 Bool.false 11951591 65536 859 1048576 Bool.false 161290 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz29 Bool.false 2987897759 16384000 113311 138568000 11951591 65536 859 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz30 113311 1000 0 1 843808 524288 1 138568 2987897759 16384000 113311 138568000 qz18 qz305 rfl) rfl) (Enclosure.sfrac_false_div 11951591 65536) (BSN.sin_reduce0 qz304 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 1458570154240504758272) qz306) 226375608064910080 72057594037927936 Bool.false 161290 1048576 29 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q0 11951591 65536 226375608064910080 72057594037927936 29 1458570154240504758272 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 161290 1048576 1458570154240504758272 9444732965739290427392 331640456 2147483648 277407 277136 (ep98 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz307 := (@Enclosure.Real.IsNear.recentre' qz28 Bool.false 468937 1048576 1 1048576 468937 1048576 1 1048576 (ep90 rfl rfl) rfl)

noncomputable def ep100 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz28 (Real.cos qz29)) (@HMul.hMul Real Real Real qz0 qz28 (@Neg.neg Real Real.instNeg (Real.sin qz29))) Bool.false 7591621093 17179869184 3528308484767 9522320452354048 Bool.true 37817424365 549755813888 880183056851 2380580113088512 (@Enclosure.Real.IsNear.mulLit_ff qz28 (Real.cos qz29) 468937 1048576 1 1048576 16189 16384 15009811 18162384896 7591621093 17179869184 3528308484767 9522320452354048 qz307 (@Enclosure.Real.IsNear.recentre' (Real.cos qz29) Bool.false 1036096 1048576 120078488 145299079168 16189 16384 15009811 18162384896 (ep97 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz28 (@Neg.neg Real Real.instNeg (Real.sin qz29)) 468937 1048576 1 1048576 80645 524288 15009811 18162384896 37817424365 549755813888 880183056851 2380580113088512 qz307 (@Enclosure.Real.IsNear.neg (Real.sin qz29) Bool.false 80645 524288 15009811 18162384896 (@Enclosure.Real.IsNear.recentre' (Real.sin qz29) Bool.false 161290 1048576 120078488 145299079168 80645 524288 15009811 18162384896 (ep99 rfl rfl) rfl)) rfl)

noncomputable def ep101 := @ep46 7591621093 17179869184 3528308484767 9522320452354048 Bool.true 37817424365 549755813888 880183056851 2380580113088512 Bool.false 13744868835914556637184 800056664501 549755813888 17582884544975 9522320452354048 Bool.false 280665826217458585829376 510528163827 1099511627776 35124210866613 19044640904708096 (ep47 (BSN.head_sum_c_succ qz5 4 5 rfl rfl) (ep88 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep89 ep100) rfl rfl

noncomputable abbrev qz308 := (@Nat.cast Real Real.instNatCast 6)

noncomputable abbrev qz31 := (@Inv.inv Real Real.instInv (Real.sqrt qz308))

noncomputable abbrev qz540 := (Real.log (Enclosure.sfrac Bool.false 6 1))

noncomputable abbrev qz32 := (@HMul.hMul Real Real Real qz268 qz285 qz540)

noncomputable def ep102 := @Enclosure.Complex.IsNear.of_eq qz279 (Complex.mk (@HMul.hMul Real Real Real qz0 qz31 (Real.cos qz32)) (@HMul.hMul Real Real Real qz0 qz31 (@Neg.neg Real Real.instNeg (Real.sin qz32)))) Bool.true 171994008699 1099511627776 6432359141581 19044640904708096 Bool.true 414614631213 1099511627776 6442176095467 19044640904708096 (BSN.cpow_neg_s_mk qz13 113311 1000 6 qz14 rfl)

noncomputable abbrev qz309 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6) qz15)

noncomputable def ep103 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz308) 2568477 1048576 1 1048576 214039 214040 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz308) (Real.sqrt qz309) Bool.false 2568477 1048576 1 1048576 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz309) Bool.false 2568477 1048576 1 1048576 2568477 1048576 1 1048576 (BSN.sqrt_enclosure 6 1 1284238 1284239 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep104 := BSN.log_dyadic_bound 2 10 4 3 105000000 524288 138568 1434560 960 212580 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 2) (BSN.artanhQ 10) 0 3 1434560 105000000 960 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep105 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz540 113311 1000 0 1 4034681531866359 2251799813685248 62500000017321 8660500000000000000 457173799057309004649 2251799813685248000 7081937501962659831 8660500000000000000000 qz18 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 62500000017321 8660500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz309) Bool.false 33845361775666394038272 18889465931478580854784 1000000000277136 138568000000000000000 4034681531866359 2251799813685248 62500000017321 8660500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 212580 524288 24973259072661432 36028797018963968 138568 1000000000000000 rfl rfl rfl rfl (ep104 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep106 := nat_lit 508488042706243186583276398909510801

noncomputable def ep107 := BSN.sin_dyadic_bound_f 844442701 2147483648 2 1 1048576 277407 ep106 ep67 ep106 ep106 ep68 ep106 401781 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 844442701) qz292 0 1 ep106 ep67 ep106 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 844442701) qz293 0 1 ep106 ep68 ep106 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz310 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 212888139) qz16)

noncomputable def ep108 := @Enclosure.Real.IsNear.cos_image qz32 qz310 Bool.false 212888139 1048576 859 1048576 Bool.true 401781 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz32 Bool.false 457173799057309004649 2251799813685248000 7081937501962659831 8660500000000000000000 212888139 1048576 859 1048576 (ep105 rfl) rfl) (Enclosure.sfrac_false_div 212888139 1048576) (BSN.cos_reduce1 qz310 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 59422372410968808357888) qz19) 226375608064910080 72057594037927936 Bool.false 401781 1048576 32 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q1 212888139 1048576 226375608064910080 72057594037927936 32 59422372410968808357888 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 401781 1048576 59422372410968808357888 151115727451828646838272 844442701 2147483648 277407 277136 (ep107 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep109 := BSN.cos_dyadic_bound_f 844442701 2147483648 2 1 1048576 277407 ep106 ep71 ep106 ep106 ep72 ep106 968547 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 844442701) qz288 0 1 ep106 ep71 ep106 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 844442701) qz289 0 1 ep106 ep72 ep106 rfl rfl rfl rfl) rfl rfl

noncomputable def ep110 := @Enclosure.Real.IsNear.sin_image qz32 qz310 Bool.false 212888139 1048576 859 1048576 Bool.false 968547 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz32 Bool.false 457173799057309004649 2251799813685248000 7081937501962659831 8660500000000000000000 212888139 1048576 859 1048576 (ep105 rfl) rfl) (Enclosure.sfrac_false_div 212888139 1048576) (BSN.sin_reduce1 qz310 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 59422372410968808357888) qz19) 226375608064910080 72057594037927936 Bool.false 968547 1048576 32 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q1 212888139 1048576 226375608064910080 72057594037927936 32 59422372410968808357888 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 968547 1048576 59422372410968808357888 151115727451828646838272 844442701 2147483648 277407 277136 (ep109 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz311 := (@Enclosure.Real.IsNear.recentre' qz31 Bool.false 428079 1048576 1 1048576 428079 1048576 1 1048576 (ep103 rfl rfl) rfl)

noncomputable def ep111 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz31 (Real.cos qz32)) (@HMul.hMul Real Real Real qz0 qz31 (@Neg.neg Real Real.instNeg (Real.sin qz32))) Bool.true 171994008699 1099511627776 6432359141581 19044640904708096 Bool.true 414614631213 1099511627776 6442176095467 19044640904708096 (@Enclosure.Real.IsNear.mulLit_ft qz31 (Real.cos qz32) 428079 1048576 1 1048576 401781 1048576 15009811 18162384896 171994008699 1099511627776 6432359141581 19044640904708096 qz311 (@Enclosure.Real.IsNear.recentre' (Real.cos qz32) Bool.true 401781 1048576 120078488 145299079168 401781 1048576 15009811 18162384896 (ep108 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz31 (@Neg.neg Real Real.instNeg (Real.sin qz32)) 428079 1048576 1 1048576 968547 1048576 15009811 18162384896 414614631213 1099511627776 6442176095467 19044640904708096 qz311 (@Enclosure.Real.IsNear.neg (Real.sin qz32) Bool.false 968547 1048576 15009811 18162384896 (@Enclosure.Real.IsNear.recentre' (Real.sin qz32) Bool.false 968547 1048576 120078488 145299079168 968547 1048576 15009811 18162384896 (ep110 rfl rfl) rfl)) rfl)

noncomputable def ep112 := @ep44 171994008699 1099511627776 6432359141581 19044640904708096 Bool.true 414614631213 1099511627776 6442176095467 19044640904708096 Bool.false 785116899262353127768064 1428119320303 1099511627776 41598128231531 19044640904708096 Bool.false 105458044370165604286464 47956766307 549755813888 1298949592565 595145028272128 (ep45 (BSN.head_sum_c_succ qz5 5 6 rfl rfl) (ep101 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep102 ep111) rfl rfl

noncomputable abbrev qz312 := (@Nat.cast Real Real.instNatCast 7)

noncomputable abbrev qz33 := (@Inv.inv Real Real.instInv (Real.sqrt qz312))

noncomputable abbrev qz541 := (Real.log (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz34 := (@HMul.hMul Real Real Real qz268 qz285 qz541)

noncomputable def ep113 := @Enclosure.Complex.IsNear.of_eq qz278 (Complex.mk (@HMul.hMul Real Real Real qz0 qz33 (Real.cos qz34)) (@HMul.hMul Real Real Real qz0 qz33 (@Neg.neg Real Real.instNeg (Real.sin qz34)))) Bool.false 347304749725 1099511627776 5957092209213 19044640904708096 Bool.true 114108705025 549755813888 2975943806227 9522320452354048 (BSN.cpow_neg_s_mk qz13 113311 1000 7 qz14 rfl)

noncomputable abbrev qz313 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 7) qz15)

noncomputable def ep114 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz312) 2774271 1048576 1 1048576 198162 198163 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz312) (Real.sqrt qz313) Bool.false 2774271 1048576 1 1048576 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz313) Bool.false 2774271 1048576 1 1048576 2774271 1048576 1 1048576 (BSN.sqrt_enclosure 7 1 1387135 1387136 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep115 := BSN.log_dyadic_bound 3 11 5 4 202569142545 524288 138568 5259111624 688905 293399 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 3) (BSN.artanhQ 11) 0 4 5259111624 202569142545 688905 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep116 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz541 113311 1000 0 1 4381796493761783 2251799813685248 62500000017321 8660500000000000000 496505742504641393513 2251799813685248000 7081937501962659831 8660500000000000000000 qz18 (BSN.isNear_log_sfrac 7 1 4381796493761783 2251799813685248 62500000017321 8660500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz313) Bool.false 36757173121942042968064 18889465931478580854784 1000000000277136 138568000000000000000 4381796493761783 2251799813685248 62500000017321 8660500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 293399 524288 24973259072661432 36028797018963968 138568 1000000000000000 rfl rfl rfl rfl (ep115 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep117 := nat_lit 2429354288890759183312199560701800625

noncomputable def ep118 := BSN.cos_dyadic_bound_f 1248454485 2147483648 2 1 1048576 277407 ep117 ep71 ep117 ep117 ep72 ep117 876313 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1248454485) qz288 0 1 ep117 ep71 ep117 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1248454485) qz289 0 1 ep117 ep72 ep117 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz314 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 231203503) qz16)

noncomputable def ep119 := @Enclosure.Real.IsNear.cos_image qz34 qz314 Bool.false 231203503 1048576 429 524288 Bool.false 876313 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz34 Bool.false 496505742504641393513 2251799813685248000 7081937501962659831 8660500000000000000000 231203503 1048576 429 524288 (ep116 rfl) rfl) (Enclosure.sfrac_false_div 231203503 1048576) (BSN.cos_reduce0 qz314 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 87852174323746043068416) qz19) 226375608064910080 72057594037927936 Bool.false 876313 1048576 35 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q0 231203503 1048576 226375608064910080 72057594037927936 35 87852174323746043068416 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 876313 1048576 87852174323746043068416 151115727451828646838272 1248454485 2147483648 277407 277136 (ep118 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep120 := BSN.sin_dyadic_bound_f 1248454485 2147483648 2 1 1048576 277407 ep117 ep67 ep117 ep117 ep68 ep117 575834 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1248454485) qz292 0 1 ep117 ep67 ep117 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1248454485) qz293 0 1 ep117 ep68 ep117 rfl rfl rfl rfl) rfl rfl

noncomputable def ep121 := @Enclosure.Real.IsNear.sin_image qz34 qz314 Bool.false 231203503 1048576 429 524288 Bool.false 575834 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz34 Bool.false 496505742504641393513 2251799813685248000 7081937501962659831 8660500000000000000000 231203503 1048576 429 524288 (ep116 rfl) rfl) (Enclosure.sfrac_false_div 231203503 1048576) (BSN.sin_reduce0 qz314 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 87852174323746043068416) qz19) 226375608064910080 72057594037927936 Bool.false 575834 1048576 35 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q0 231203503 1048576 226375608064910080 72057594037927936 35 87852174323746043068416 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 575834 1048576 87852174323746043068416 151115727451828646838272 1248454485 2147483648 277407 277136 (ep120 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz315 := (@Enclosure.Real.IsNear.recentre' qz33 Bool.false 396325 1048576 1 1048576 396325 1048576 1 1048576 (ep114 rfl rfl) rfl)

noncomputable def ep122 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz33 (Real.cos qz34)) (@HMul.hMul Real Real Real qz0 qz33 (@Neg.neg Real Real.instNeg (Real.sin qz34))) Bool.false 347304749725 1099511627776 5957092209213 19044640904708096 Bool.true 114108705025 549755813888 2975943806227 9522320452354048 (@Enclosure.Real.IsNear.mulLit_ff qz33 (Real.cos qz34) 396325 1048576 1 1048576 876313 1048576 7496245 9081192448 347304749725 1099511627776 5957092209213 19044640904708096 qz315 (@Enclosure.Real.IsNear.recentre' (Real.cos qz34) Bool.false 876313 1048576 59969960 72649539584 876313 1048576 7496245 9081192448 (ep119 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz33 (@Neg.neg Real Real.instNeg (Real.sin qz34)) 396325 1048576 1 1048576 287917 524288 7496245 9081192448 114108705025 549755813888 2975943806227 9522320452354048 qz315 (@Enclosure.Real.IsNear.neg (Real.sin qz34) Bool.false 287917 524288 7496245 9081192448 (@Enclosure.Real.IsNear.recentre' (Real.sin qz34) Bool.false 575834 1048576 59969960 72649539584 287917 524288 7496245 9081192448 (ep121 rfl rfl) rfl)) rfl)

noncomputable def ep123 := @ep41 347304749725 1099511627776 5957092209213 19044640904708096 Bool.true 114108705025 549755813888 2975943806227 9522320452354048 Bool.false ep42 443856017507 274877906944 5944402555093 2380580113088512 Bool.true 36367412910183189315584 33075969359 274877906944 23759137287267 9522320452354048 (ep43 (BSN.head_sum_c_succ qz5 6 7 rfl rfl) (ep112 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep113 ep122) rfl rfl

noncomputable abbrev qz316 := (@Nat.cast Real Real.instNatCast 8)

noncomputable abbrev qz35 := (@Inv.inv Real Real.instInv (Real.sqrt qz316))

noncomputable abbrev qz542 := (Real.log (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz36 := (@HMul.hMul Real Real Real qz268 qz285 qz542)

noncomputable def ep124 := @Enclosure.Complex.IsNear.of_eq qz277 (Complex.mk (@HMul.hMul Real Real Real qz0 qz35 (Real.cos qz36)) (@HMul.hMul Real Real Real qz0 qz35 (@Neg.neg Real Real.instNeg (Real.sin qz36)))) Bool.true 194365863741 549755813888 2788149022203 9522320452354048 Bool.false 6302359 4294967296 347388200857 1190290056544256 (BSN.cpow_neg_s_mk qz13 113311 1000 8 qz14 rfl)

noncomputable abbrev qz317 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8) qz15)

noncomputable def ep125 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz316) 2965821 1048576 1 1048576 185363 185364 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz316) (Real.sqrt qz317) Bool.false 2965821 1048576 1 1048576 (BSN.sqrt_natCast_div_one 8) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz317) Bool.false 2965821 1048576 1 1048576 2965821 1048576 1 1048576 (BSN.sqrt_enclosure 8 1 1482910 1482911 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep126 := BSN.log_dyadic_bound 0 16 1 0 1 524288 138568 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl

noncomputable def ep127 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz542 113311 1000 0 1 9364972152248037 4503599627370496 125000000051963 17321000000000000000 1061154359543377320507 4503599627370496000 14163875005887979493 17321000000000000000000 qz18 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 125000000051963 17321000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz317) Bool.false 39279540158062550581248 18889465931478580854784 1000000000415704 138568000000000000000 9364972152248037 4503599627370496 125000000051963 17321000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 524288 24973259072661432 36028797018963968 138568 1000000000000000 rfl rfl rfl rfl (ep126 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep128 := BSN.cos_dyadic_bound_f 8914176 2147483648 1 0 1048576 277407 0 1 1 0 1 1 1048566 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 8914176) qz288 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 8914176) qz289 0 0 rfl) rfl rfl

noncomputable abbrev qz543 := (@Nat.cast Real Real.instNatCast 262144)

noncomputable abbrev qz318 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 61767313) qz543)

noncomputable abbrev qz319 := (@Nat.cast Real Real.instNatCast 37778931862957161709568)

noncomputable def ep129 := @Enclosure.Real.IsNear.cos_image qz36 qz318 Bool.false 61767313 262144 429 524288 Bool.true 1048566 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz36 Bool.false 1061154359543377320507 4503599627370496000 14163875005887979493 17321000000000000000000 61767313 262144 429 524288 (ep127 rfl) rfl) (Enclosure.sfrac_false_div 61767313 262144) (BSN.cos_reduce2 qz318 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 156819850089186983936) qz319) 226375608064910080 72057594037927936 Bool.false 1048566 1048576 37 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q2 61767313 262144 226375608064910080 72057594037927936 37 156819850089186983936 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1048566 1048576 156819850089186983936 37778931862957161709568 8914176 2147483648 277407 277136 (ep128 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep130 := BSN.sin_dyadic_bound_f 8914176 2147483648 1 0 1048576 277407 0 1 1 0 1 1 4352 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 8914176) qz292 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 8914176) qz293 0 0 rfl) rfl rfl

noncomputable def ep131 := @Enclosure.Real.IsNear.sin_image qz36 qz318 Bool.false 61767313 262144 429 524288 Bool.true 4352 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz36 Bool.false 1061154359543377320507 4503599627370496000 14163875005887979493 17321000000000000000000 61767313 262144 429 524288 (ep127 rfl) rfl) (Enclosure.sfrac_false_div 61767313 262144) (BSN.sin_reduce2 qz318 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 156819850089186983936) qz319) 226375608064910080 72057594037927936 Bool.false 4352 1048576 37 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q2 61767313 262144 226375608064910080 72057594037927936 37 156819850089186983936 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 4352 1048576 156819850089186983936 37778931862957161709568 8914176 2147483648 277407 277136 (ep130 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz320 := (@Enclosure.Real.IsNear.recentre' qz35 Bool.false 370727 1048576 1 1048576 370727 1048576 1 1048576 (ep125 rfl rfl) rfl)

noncomputable def ep132 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz35 (Real.cos qz36)) (@HMul.hMul Real Real Real qz0 qz35 (@Neg.neg Real Real.instNeg (Real.sin qz36))) Bool.true 194365863741 549755813888 2788149022203 9522320452354048 Bool.false 6302359 4294967296 347388200857 1190290056544256 (@Enclosure.Real.IsNear.mulLit_ft qz35 (Real.cos qz36) 370727 1048576 1 1048576 524283 524288 7496245 9081192448 194365863741 549755813888 2788149022203 9522320452354048 qz320 (@Enclosure.Real.IsNear.recentre' (Real.cos qz36) Bool.true 1048566 1048576 59969960 72649539584 524283 524288 7496245 9081192448 (ep129 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz35 (@Neg.neg Real Real.instNeg (Real.sin qz36)) 370727 1048576 1 1048576 17 4096 7496245 9081192448 6302359 4294967296 347388200857 1190290056544256 qz320 (@Enclosure.Real.IsNear.neg (Real.sin qz36) Bool.true 17 4096 7496245 9081192448 (@Enclosure.Real.IsNear.recentre' (Real.sin qz36) Bool.true 4352 1048576 59969960 72649539584 17 4096 7496245 9081192448 (ep131 rfl rfl) rfl)) rfl)

noncomputable def ep133 := @ep39 194365863741 549755813888 2788149022203 9522320452354048 Bool.false 6302359 4294967296 347388200857 1190290056544256 Bool.false 190585544347158380019712 693346171273 549755813888 26565759242575 9522320452354048 Bool.true 140327827429673402368 32672618383 274877906944 26538242894123 9522320452354048 (ep40 (BSN.head_sum_c_succ qz5 7 8 rfl rfl) (ep123 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep124 ep132) rfl rfl

theorem EMRow36.d6 : Enclosure.Complex.IsNear qz3 Bool.false 693346171273 549755813888 26565759242575 9522320452354048 Bool.true 32672618383 274877906944 26538242894123 9522320452354048 := ep38 (BSN.head_sum_c_succ qz5 8 9 rfl rfl) (ep133 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz37 := (BSN.headSumC qz273 17)

noncomputable abbrev qz38 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 16) qz276)

noncomputable def ep134 := @Enclosure.Complex.IsNear.of_eq qz37 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 16) qz38) Bool.false 1083916429507 1099511627776 89269635227647 19044640904708096 Bool.false 60463601213 274877906944 22306732233447 4761160226177024

noncomputable def ep135 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 16) qz38 Bool.false 404522013785 549755813888 10665160229831 2380580113088512 Bool.false 30421985353 137438953472 5331039819009 1190290056544256 Bool.false

noncomputable abbrev qz39 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 15) qz276)

noncomputable def ep136 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 16) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 15) qz39) Bool.false 404522013785 549755813888 10665160229831 2380580113088512 Bool.false 30421985353 137438953472 5331039819009 1190290056544256

noncomputable def ep137 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 15) qz39 Bool.false 165383510653 274877906944 2539001826559 595145028272128 Bool.false 407615275 549755813888 20304333181997 4761160226177024 Bool.false

noncomputable abbrev qz40 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 14) qz276)

noncomputable def ep138 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 15) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 14) qz40) Bool.false 165383510653 274877906944 2539001826559 595145028272128 Bool.false 407615275 549755813888 20304333181997 4761160226177024

noncomputable def ep139 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 14) qz40 Bool.false 113361409125 137438953472 9628310520421 2380580113088512 Bool.true 40224467907 274877906944 38500464120169 9522320452354048 Bool.true

noncomputable abbrev qz41 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 13) qz276)

noncomputable def ep140 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 14) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 13) qz41) Bool.false 113361409125 137438953472 9628310520421 2380580113088512 Bool.true 40224467907 274877906944 38500464120169 9522320452354048

noncomputable def ep141 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 13) qz41 Bool.false 459460146963 549755813888 36332795910203 9522320452354048 Bool.false 143814544029 1099511627776 72622604094939 19044640904708096 Bool.true

noncomputable abbrev qz42 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 12) qz276)

noncomputable def ep142 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 13) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 12) qz42) Bool.false 459460146963 549755813888 36332795910203 9522320452354048 Bool.false 143814544029 1099511627776 72622604094939 19044640904708096

noncomputable def ep143 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 12) qz42 Bool.false 796896776589 1099511627776 68120412623545 19044640904708096 Bool.true 4662275697 34359738368 34033820409725 9522320452354048 Bool.false

noncomputable abbrev qz43 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 11) qz276)

noncomputable def ep144 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 12) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 11) qz43) Bool.false 796896776589 1099511627776 68120412623545 19044640904708096 Bool.true 4662275697 34359738368 34033820409725 9522320452354048

noncomputable def ep145 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 11) qz43 Bool.false 783654856801 1099511627776 63379691497361 19044640904708096 Bool.false 182057196719 1099511627776 63309497278811 19044640904708096 Bool.false

noncomputable abbrev qz44 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 10) qz276)

noncomputable def ep146 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 11) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 10) qz44) Bool.false 783654856801 1099511627776 63379691497361 19044640904708096 Bool.false 182057196719 1099511627776 63309497278811 19044640904708096

noncomputable def ep147 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 10) qz44 Bool.false 281783245099 274877906944 7298080777927 2380580113088512 Bool.false 128063233493 1099511627776 58329573601607 19044640904708096 Bool.true

noncomputable abbrev qz321 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 9) qz7)

noncomputable def ep148 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 10) (@HAdd.hAdd Complex Complex Complex qz4 qz3 qz321) Bool.false 281783245099 274877906944 7298080777927 2380580113088512 Bool.false 128063233493 1099511627776 58329573601607 19044640904708096

noncomputable def ep149 := @Enclosure.Complex.IsNear.addLitP qz3 qz321 Bool.false 693346171273 549755813888 26565759242575 9522320452354048 Bool.true 32672618383 274877906944 26538242894123 9522320452354048 Bool.true

noncomputable abbrev qz322 := (@Nat.cast Real Real.instNatCast 9)

noncomputable abbrev qz45 := (@Inv.inv Real Real.instInv (Real.sqrt qz322))

noncomputable abbrev qz544 := (Real.log (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz46 := (@HMul.hMul Real Real Real qz268 qz285 qz544)

noncomputable def ep150 := @Enclosure.Complex.IsNear.of_eq qz321 (Complex.mk (@HMul.hMul Real Real Real qz0 qz45 (Real.cos qz46)) (@HMul.hMul Real Real Real qz0 qz45 (@Neg.neg Real Real.instNeg (Real.sin qz46)))) Bool.true 129779681075 549755813888 2626563869133 9522320452354048 Bool.false 258753707025 1099511627776 5253087813361 19044640904708096 (BSN.cpow_neg_s_mk qz13 113311 1000 9 qz14 rfl)

noncomputable abbrev qz323 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9) qz15)

noncomputable def ep151 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz322) 3145729 1048576 1 1048576 174762 174763 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz322) (Real.sqrt qz323) Bool.false 3145729 1048576 1 1048576 (BSN.sqrt_natCast_div_one 9) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz323) Bool.false 3145729 1048576 1 1048576 3145729 1048576 1 1048576 (BSN.sqrt_enclosure 9 1 1572864 1572865 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep152 := BSN.log_dyadic_bound 1 17 2 1 867 524288 138568 1 1 61752 18 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1) (BSN.artanhQ 17) 0 1 1 867 1 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep153 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz544 113311 1000 0 1 9895417793173221 4503599627370496 125000000051963 17321000000000000000 1121259685562250844731 4503599627370496000 14163875005887979493 17321000000000000000000 qz18 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 125000000051963 17321000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz323) Bool.false 41504390431577613533184 18889465931478580854784 1000000000415704 138568000000000000000 9895417793173221 4503599627370496 125000000051963 17321000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 61752 524288 24973259072661432 36028797018963968 138568 1000000000000000 rfl rfl rfl rfl (ep152 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep154 := nat_lit 286922301398419029809344356857942058694256302578866218515703106885449920126081

noncomputable def ep155 := nat_lit 18237254054877300779212430138868345486890022584838388836214569481246317918289920

noncomputable def ep156 := nat_lit 64457872992477703836448652143217527371994405588985642067031279655557635201

noncomputable def ep157 := nat_lit 860637988449272134020360173269539741028024918925420684262975258097038645107841

noncomputable def ep158 := nat_lit 820676432469478535064559356249075546910051016317727497629655626656084306323046400

noncomputable def ep159 := BSN.cos_dyadic_bound_f 1683292143 2147483648 3 2 1048576 277407 ep154 ep155 ep156 ep157 ep158 ep156 742606 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1683292143) qz288 0 2 ep154 ep155 ep156 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1683292143) qz289 0 2 ep157 ep158 ep156 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz324 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 130531807) qz26)

noncomputable def ep160 := @Enclosure.Real.IsNear.cos_image qz46 qz324 Bool.false 130531807 524288 429 524288 Bool.true 742606 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz46 Bool.false 1121259685562250844731 4503599627370496000 14163875005887979493 17321000000000000000000 130531807 524288 429 524288 (ep153 rfl) rfl) (Enclosure.sfrac_false_div 130531807 524288) (BSN.cos_reduce2 qz324 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 59225577106899032080384) qz302) 226375608064910080 72057594037927936 Bool.false 742606 1048576 39 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q2 130531807 524288 226375608064910080 72057594037927936 39 59225577106899032080384 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 742606 1048576 59225577106899032080384 75557863725914323419136 1683292143 2147483648 277407 277136 (ep159 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep161 := nat_lit 8028566060790538443662236062631937601

noncomputable def ep162 := BSN.sin_dyadic_bound_f 1683292143 2147483648 2 1 1048576 277407 ep161 ep67 ep161 ep161 ep68 ep161 740301 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1683292143) qz292 0 1 ep161 ep67 ep161 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1683292143) qz293 0 1 ep161 ep68 ep161 rfl rfl rfl rfl) rfl rfl

noncomputable def ep163 := @Enclosure.Real.IsNear.sin_image qz46 qz324 Bool.false 130531807 524288 429 524288 Bool.true 740301 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz46 Bool.false 1121259685562250844731 4503599627370496000 14163875005887979493 17321000000000000000000 130531807 524288 429 524288 (ep153 rfl) rfl) (Enclosure.sfrac_false_div 130531807 524288) (BSN.sin_reduce2 qz324 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 59225577106899032080384) qz302) 226375608064910080 72057594037927936 Bool.false 740301 1048576 39 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q2 130531807 524288 226375608064910080 72057594037927936 39 59225577106899032080384 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 740301 1048576 59225577106899032080384 75557863725914323419136 1683292143 2147483648 277407 277136 (ep162 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz325 := (@Enclosure.Real.IsNear.recentre' qz45 Bool.false 349525 1048576 1 1048576 349525 1048576 1 1048576 (ep151 rfl rfl) rfl)

noncomputable def ep164 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz45 (Real.cos qz46)) (@HMul.hMul Real Real Real qz0 qz45 (@Neg.neg Real Real.instNeg (Real.sin qz46))) Bool.true 129779681075 549755813888 2626563869133 9522320452354048 Bool.false 258753707025 1099511627776 5253087813361 19044640904708096 (@Enclosure.Real.IsNear.mulLit_ft qz45 (Real.cos qz46) 349525 1048576 1 1048576 371303 524288 7496245 9081192448 129779681075 549755813888 2626563869133 9522320452354048 qz325 (@Enclosure.Real.IsNear.recentre' (Real.cos qz46) Bool.true 742606 1048576 59969960 72649539584 371303 524288 7496245 9081192448 (ep160 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz45 (@Neg.neg Real Real.instNeg (Real.sin qz46)) 349525 1048576 1 1048576 740301 1048576 7496245 9081192448 258753707025 1099511627776 5253087813361 19044640904708096 qz325 (@Enclosure.Real.IsNear.neg (Real.sin qz46) Bool.true 740301 1048576 7496245 9081192448 (@Enclosure.Real.IsNear.recentre' (Real.sin qz46) Bool.true 740301 1048576 59969960 72649539584 740301 1048576 7496245 9081192448 (ep163 rfl rfl) rfl)) rfl)

noncomputable def ep165 := @ep149 129779681075 549755813888 2626563869133 9522320452354048 Bool.false 258753707025 1099511627776 5253087813361 19044640904708096 Bool.false 309823954498805064269824 281783245099 274877906944 7298080777927 2380580113088512 Bool.false 35201753579036598075392 128063233493 1099511627776 58329573601607 19044640904708096 EMRow36.d6 (ep150 ep164) rfl rfl

noncomputable abbrev qz326 := (@Nat.cast Real Real.instNatCast 10)

noncomputable abbrev qz47 := (@Inv.inv Real Real.instInv (Real.sqrt qz326))

noncomputable abbrev qz545 := (Real.log (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz48 := (@HMul.hMul Real Real Real qz268 qz285 qz545)

noncomputable def ep166 := @Enclosure.Complex.IsNear.of_eq qz44 (Complex.mk (@HMul.hMul Real Real Real qz0 qz47 (Real.cos qz48)) (@HMul.hMul Real Real Real qz0 qz47 (@Neg.neg Real Real.instNeg (Real.sin qz48)))) Bool.true 343478123595 1099511627776 4995045273945 19044640904708096 Bool.false 26996981613 549755813888 1244980919301 4761160226177024 (BSN.cpow_neg_s_mk qz13 113311 1000 10 qz14 rfl)

noncomputable abbrev qz327 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 10) qz15)

noncomputable def ep167 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz326) 3315889 1048576 1 1048576 165794 165795 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz326) (Real.sqrt qz327) Bool.false 3315889 1048576 1 1048576 (BSN.sqrt_natCast_div_one 10) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz327) Bool.false 3315889 1048576 1 1048576 3315889 1048576 1 1048576 (BSN.sqrt_enclosure 10 1 1657944 1657945 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep168 := BSN.log_dyadic_bound 2 18 3 2 1574640 524288 138568 6528 48 116991 20 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 2) (BSN.artanhQ 18) 0 2 6528 1574640 48 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep169 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz545 113311 1000 0 1 10369917190100709 4503599627370496 125000000051963 17321000000000000000 1175025686727501437499 4503599627370496000 14163875005887979493 17321000000000000000000 qz18 (BSN.isNear_log_sfrac 10 1 10369917190100709 4503599627370496 125000000051963 17321000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz327) Bool.false 43494585150108164161536 18889465931478580854784 1000000000415704 138568000000000000000 10369917190100709 4503599627370496 125000000051963 17321000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 116991 524288 24973259072661432 36028797018963968 138568 1000000000000000 rfl rfl rfl rfl (ep168 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep170 := nat_lit 12570795752063643790941672045610000

noncomputable def ep171 := BSN.cos_dyadic_bound_f 334842590 2147483648 2 1 1048576 277407 ep170 ep71 ep170 ep170 ep72 ep170 1035855 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 334842590) qz288 0 1 ep170 ep71 ep170 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 334842590) qz289 0 1 ep170 ep72 ep170 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz328 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 136790993) qz26)

noncomputable def ep172 := @Enclosure.Real.IsNear.cos_image qz48 qz328 Bool.false 136790993 524288 859 1048576 Bool.true 1035855 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz48 Bool.false 1175025686727501437499 4503599627370496000 14163875005887979493 17321000000000000000000 136790993 524288 859 1048576 (ep169 rfl) rfl) (Enclosure.sfrac_false_div 136790993 524288) (BSN.cos_reduce2 qz328 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11781226289578435936256) qz302) 226375608064910080 72057594037927936 Bool.false 1035855 1048576 41 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q2 136790993 524288 226375608064910080 72057594037927936 41 11781226289578435936256 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1035855 1048576 11781226289578435936256 75557863725914323419136 334842590 2147483648 277407 277136 (ep171 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep173 := BSN.sin_dyadic_bound_f 334842590 2147483648 1 0 1048576 277407 0 1 1 0 1 1 162834 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 334842590) qz292 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 334842590) qz293 0 0 rfl) rfl rfl

noncomputable def ep174 := @Enclosure.Real.IsNear.sin_image qz48 qz328 Bool.false 136790993 524288 859 1048576 Bool.true 162834 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz48 Bool.false 1175025686727501437499 4503599627370496000 14163875005887979493 17321000000000000000000 136790993 524288 859 1048576 (ep169 rfl) rfl) (Enclosure.sfrac_false_div 136790993 524288) (BSN.sin_reduce2 qz328 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11781226289578435936256) qz302) 226375608064910080 72057594037927936 Bool.false 162834 1048576 41 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q2 136790993 524288 226375608064910080 72057594037927936 41 11781226289578435936256 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 162834 1048576 11781226289578435936256 75557863725914323419136 334842590 2147483648 277407 277136 (ep173 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz329 := (@Enclosure.Real.IsNear.recentre' qz47 Bool.false 331589 1048576 1 1048576 331589 1048576 1 1048576 (ep167 rfl rfl) rfl)

noncomputable def ep175 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz47 (Real.cos qz48)) (@HMul.hMul Real Real Real qz0 qz47 (@Neg.neg Real Real.instNeg (Real.sin qz48))) Bool.true 343478123595 1099511627776 4995045273945 19044640904708096 Bool.false 26996981613 549755813888 1244980919301 4761160226177024 (@Enclosure.Real.IsNear.mulLit_ft qz47 (Real.cos qz48) 331589 1048576 1 1048576 1035855 1048576 15009811 18162384896 343478123595 1099511627776 4995045273945 19044640904708096 qz329 (@Enclosure.Real.IsNear.recentre' (Real.cos qz48) Bool.true 1035855 1048576 120078488 145299079168 1035855 1048576 15009811 18162384896 (ep172 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz47 (@Neg.neg Real Real.instNeg (Real.sin qz48)) 331589 1048576 1 1048576 81417 524288 15009811 18162384896 26996981613 549755813888 1244980919301 4761160226177024 qz329 (@Enclosure.Real.IsNear.neg (Real.sin qz48) Bool.true 81417 524288 15009811 18162384896 (@Enclosure.Real.IsNear.recentre' (Real.sin qz48) Bool.true 162834 1048576 120078488 145299079168 81417 524288 15009811 18162384896 (ep174 rfl rfl) rfl)) rfl)

noncomputable def ep176 := @ep147 343478123595 1099511627776 4995045273945 19044640904708096 Bool.false 26996981613 549755813888 1244980919301 4761160226177024 Bool.false 215409406803958923526144 783654856801 1099511627776 63379691497361 19044640904708096 Bool.false 100087002356421568233472 182057196719 1099511627776 63309497278811 19044640904708096 (ep148 (BSN.head_sum_c_succ qz5 9 10 rfl rfl) (ep165 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep166 ep175) rfl rfl

noncomputable abbrev qz330 := (@Nat.cast Real Real.instNatCast 11)

noncomputable abbrev qz49 := (@Inv.inv Real Real.instInv (Real.sqrt qz330))

noncomputable abbrev qz546 := (Real.log (Enclosure.sfrac Bool.false 11 1))

noncomputable abbrev qz50 := (@HMul.hMul Real Real Real qz268 qz285 qz546)

noncomputable def ep177 := @Enclosure.Complex.IsNear.of_eq qz43 (Complex.mk (@HMul.hMul Real Real Real qz0 qz49 (Real.cos qz50)) (@HMul.hMul Real Real Real qz0 qz49 (@Neg.neg Real Real.instNeg (Real.sin qz50)))) Bool.false 3310479947 274877906944 592590140773 2380580113088512 Bool.true 331250019023 1099511627776 4758143540639 19044640904708096 (BSN.cpow_neg_s_mk qz13 113311 1000 11 qz14 rfl)

noncomputable abbrev qz331 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11) qz15)

noncomputable def ep178 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz330) 3477733 1048576 1 1048576 158078 158079 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz330) (Real.sqrt qz331) Bool.false 3477733 1048576 1 1048576 (BSN.sqrt_natCast_div_one 11) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz331) Bool.false 3477733 1048576 1 1048576 3477733 1048576 1 1048576 (BSN.sqrt_enclosure 11 1 1738866 1738867 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep179 := BSN.log_dyadic_bound 3 19 4 3 4939817505 524288 138568 41676111 10935 166961 22 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 3) (BSN.artanhQ 19) 0 3 41676111 4939817505 10935 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep180 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz546 113311 1000 0 1 10799156221662949 4503599627370496 125000000051963 17321000000000000000 1223663190632850414139 4503599627370496000 14163875005887979493 17321000000000000000000 qz18 (BSN.isNear_log_sfrac 11 1 10799156221662949 4503599627370496 125000000051963 17321000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz331) Bool.false 45294944137145793642496 18889465931478580854784 1000000000415704 138568000000000000000 10799156221662949 4503599627370496 125000000051963 17321000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 166961 524288 24973259072661432 36028797018963968 138568 1000000000000000 rfl rfl rfl rfl (ep179 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep181 := nat_lit 4186838417331224283526583238110094872816508873838006513880745625983003313370241

noncomputable def ep182 := nat_lit 13642066111666223297202063605850810748535111553696677320417695242882533880961

noncomputable def ep183 := nat_lit 12533231119770340403985345587118582996952456398406626187001401487463244872348801

noncomputable def ep184 := BSN.cos_dyadic_bound_f 3287456529 2147483648 3 2 1048576 277407 ep181 ep155 ep182 ep183 ep158 ep182 41884 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3287456529) qz288 0 2 ep181 ep155 ep182 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3287456529) qz289 0 2 ep183 ep158 ep182 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz332 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 17806643) (@Nat.cast Real Real.instNatCast 65536))

noncomputable def ep185 := @Enclosure.Real.IsNear.cos_image qz50 qz332 Bool.false 17806643 65536 429 524288 Bool.false 41884 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz50 Bool.false 1223663190632850414139 4503599627370496000 14163875005887979493 17321000000000000000000 17806643 65536 429 524288 (ep180 rfl) rfl) (Enclosure.sfrac_false_div 17806643 65536) (BSN.cos_reduce0 qz332 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14458386720207547662336) qz306) 226375608064910080 72057594037927936 Bool.false 41884 1048576 43 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q0 17806643 65536 226375608064910080 72057594037927936 43 14458386720207547662336 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 41884 1048576 14458386720207547662336 9444732965739290427392 3287456529 2147483648 277407 277136 (ep184 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep186 := nat_lit 7525395498306870731710088177713490122470887883665454383129007970575099936961665

noncomputable def ep187 := nat_lit 164135286493895707012911871249815109382010203263545499525931125331216861264609280

noncomputable def ep188 := nat_lit 19687282007575297078664284743411572817640411419465443049676249368732023351473281

noncomputable def ep189 := nat_lit 3009146919054754628570050972913277005336853726498334157975403964405642456517836800

noncomputable def ep190 := BSN.sin_dyadic_bound_f 3287456529 2147483648 3 2 1048576 277407 ep186 ep187 ep182 ep188 ep189 ep182 1047739 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3287456529) qz292 0 2 ep186 ep187 ep182 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3287456529) qz293 0 2 ep188 ep189 ep182 rfl rfl rfl rfl) rfl rfl

noncomputable def ep191 := @Enclosure.Real.IsNear.sin_image qz50 qz332 Bool.false 17806643 65536 429 524288 Bool.false 1047739 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz50 Bool.false 1223663190632850414139 4503599627370496000 14163875005887979493 17321000000000000000000 17806643 65536 429 524288 (ep180 rfl) rfl) (Enclosure.sfrac_false_div 17806643 65536) (BSN.sin_reduce0 qz332 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14458386720207547662336) qz306) 226375608064910080 72057594037927936 Bool.false 1047739 1048576 43 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q0 17806643 65536 226375608064910080 72057594037927936 43 14458386720207547662336 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1047739 1048576 14458386720207547662336 9444732965739290427392 3287456529 2147483648 277407 277136 (ep190 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz333 := (@Enclosure.Real.IsNear.recentre' qz49 Bool.false 316157 1048576 1 1048576 316157 1048576 1 1048576 (ep178 rfl rfl) rfl)

noncomputable def ep192 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz49 (Real.cos qz50)) (@HMul.hMul Real Real Real qz0 qz49 (@Neg.neg Real Real.instNeg (Real.sin qz50))) Bool.false 3310479947 274877906944 592590140773 2380580113088512 Bool.true 331250019023 1099511627776 4758143540639 19044640904708096 (@Enclosure.Real.IsNear.mulLit_ff qz49 (Real.cos qz50) 316157 1048576 1 1048576 10471 262144 7496245 9081192448 3310479947 274877906944 592590140773 2380580113088512 qz333 (@Enclosure.Real.IsNear.recentre' (Real.cos qz50) Bool.false 41884 1048576 59969960 72649539584 10471 262144 7496245 9081192448 (ep185 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz49 (@Neg.neg Real Real.instNeg (Real.sin qz50)) 316157 1048576 1 1048576 1047739 1048576 7496245 9081192448 331250019023 1099511627776 4758143540639 19044640904708096 qz333 (@Enclosure.Real.IsNear.neg (Real.sin qz50) Bool.false 1047739 1048576 7496245 9081192448 (@Enclosure.Real.IsNear.recentre' (Real.sin qz50) Bool.false 1047739 1048576 59969960 72649539584 1047739 1048576 7496245 9081192448 (ep191 rfl rfl) rfl)) rfl)

noncomputable def ep193 := @ep145 3310479947 274877906944 592590140773 2380580113088512 Bool.true 331250019023 1099511627776 4758143540639 19044640904708096 Bool.false 219049317999204699734016 796896776589 1099511627776 68120412623545 19044640904708096 Bool.true 164039242903966558715904 4662275697 34359738368 34033820409725 9522320452354048 (ep146 (BSN.head_sum_c_succ qz5 10 11 rfl rfl) (ep176 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep177 ep192) rfl rfl

noncomputable abbrev qz334 := (@Nat.cast Real Real.instNatCast 12)

noncomputable abbrev qz51 := (@Inv.inv Real Real.instInv (Real.sqrt qz334))

noncomputable abbrev qz547 := (Real.log (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz52 := (@HMul.hMul Real Real Real qz268 qz285 qz547)

noncomputable def ep194 := @Enclosure.Complex.IsNear.of_eq qz42 (Complex.mk (@HMul.hMul Real Real Real qz0 qz51 (Real.cos qz52)) (@HMul.hMul Real Real Real qz0 qz51 (@Neg.neg Real Real.instNeg (Real.sin qz52)))) Bool.false 122023517337 1099511627776 4545179196861 19044640904708096 Bool.false 293007366333 1099511627776 4554963275489 19044640904708096 (BSN.cpow_neg_s_mk qz13 113311 1000 12 qz14 rfl)

noncomputable abbrev qz335 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 12) qz15)

noncomputable def ep195 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz334) 3632373 1048576 1 1048576 151348 151349 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz334) (Real.sqrt qz335) Bool.false 3632373 1048576 1 1048576 (BSN.sqrt_natCast_div_one 12) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz335) Bool.false 3632373 1048576 1 1048576 3632373 1048576 1 1048576 (BSN.sqrt_enclosure 12 1 1816186 1816187 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep196 := BSN.log_dyadic_bound 4 20 4 3 6720000000 524288 138568 91811840 61440 212580 24 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 4) (BSN.artanhQ 20) 0 3 91811840 6720000000 61440 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep197 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz547 113311 1000 0 1 11191020447815397 4503599627370496 125000000051963 17321000000000000000 1268065717962410449467 4503599627370496000 14163875005887979493 17321000000000000000000 qz18 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 125000000051963 17321000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz335) Bool.false 46938541828353910898688 18889465931478580854784 1000000000415704 138568000000000000000 11191020447815397 4503599627370496 125000000051963 17321000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 212580 524288 24973259072661432 36028797018963968 138568 1000000000000000 rfl rfl rfl rfl (ep196 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep198 := nat_lit 515686221104367347942452630630855696

noncomputable def ep199 := BSN.sin_dyadic_bound_f 847415458 2147483648 2 1 1048576 277407 ep198 ep67 ep198 ep198 ep68 ep198 403121 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 847415458) qz292 0 1 ep198 ep67 ep198 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 847415458) qz293 0 1 ep198 ep68 ep198 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz336 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 295244557) qz16)

noncomputable def ep200 := @Enclosure.Real.IsNear.cos_image qz52 qz336 Bool.false 295244557 1048576 429 524288 Bool.false 403121 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz52 Bool.false 1268065717962410449467 4503599627370496000 14163875005887979493 17321000000000000000000 295244557 1048576 429 524288 (ep197 rfl) rfl) (Enclosure.sfrac_false_div 295244557 1048576) (BSN.cos_reduce3 qz336 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 59631561621213108240384) qz19) 226375608064910080 72057594037927936 Bool.false 403121 1048576 44 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q3 295244557 1048576 226375608064910080 72057594037927936 44 59631561621213108240384 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 403121 1048576 59631561621213108240384 151115727451828646838272 847415458 2147483648 277407 277136 (ep199 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep201 := BSN.cos_dyadic_bound_f 847415458 2147483648 2 1 1048576 277407 ep198 ep71 ep198 ep198 ep72 ep198 967989 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 847415458) qz288 0 1 ep198 ep71 ep198 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 847415458) qz289 0 1 ep198 ep72 ep198 rfl rfl rfl rfl) rfl rfl

noncomputable def ep202 := @Enclosure.Real.IsNear.sin_image qz52 qz336 Bool.false 295244557 1048576 429 524288 Bool.true 967989 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz52 Bool.false 1268065717962410449467 4503599627370496000 14163875005887979493 17321000000000000000000 295244557 1048576 429 524288 (ep197 rfl) rfl) (Enclosure.sfrac_false_div 295244557 1048576) (BSN.sin_reduce3 qz336 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 59631561621213108240384) qz19) 226375608064910080 72057594037927936 Bool.false 967989 1048576 44 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q3 295244557 1048576 226375608064910080 72057594037927936 44 59631561621213108240384 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 967989 1048576 59631561621213108240384 151115727451828646838272 847415458 2147483648 277407 277136 (ep201 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz337 := (@Enclosure.Real.IsNear.recentre' qz51 Bool.false 302697 1048576 1 1048576 302697 1048576 1 1048576 (ep195 rfl rfl) rfl)

noncomputable def ep203 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz51 (Real.cos qz52)) (@HMul.hMul Real Real Real qz0 qz51 (@Neg.neg Real Real.instNeg (Real.sin qz52))) Bool.false 122023517337 1099511627776 4545179196861 19044640904708096 Bool.false 293007366333 1099511627776 4554963275489 19044640904708096 (@Enclosure.Real.IsNear.mulLit_ff qz51 (Real.cos qz52) 302697 1048576 1 1048576 403121 1048576 7496245 9081192448 122023517337 1099511627776 4545179196861 19044640904708096 qz337 (@Enclosure.Real.IsNear.recentre' (Real.cos qz52) Bool.false 403121 1048576 59969960 72649539584 403121 1048576 7496245 9081192448 (ep200 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz51 (@Neg.neg Real Real.instNeg (Real.sin qz52)) 302697 1048576 1 1048576 967989 1048576 7496245 9081192448 293007366333 1099511627776 4554963275489 19044640904708096 qz337 (@Enclosure.Real.IsNear.neg (Real.sin qz52) Bool.true 967989 1048576 7496245 9081192448 (@Enclosure.Real.IsNear.recentre' (Real.sin qz52) Bool.true 967989 1048576 59969960 72649539584 967989 1048576 7496245 9081192448 (ep202 rfl rfl) rfl)) rfl)

noncomputable def ep204 := @ep143 122023517337 1099511627776 4545179196861 19044640904708096 Bool.false 293007366333 1099511627776 4554963275489 19044640904708096 Bool.false 1010363548170976625688576 459460146963 549755813888 36332795910203 9522320452354048 Bool.false 4941430106349656604672 143814544029 1099511627776 72622604094939 19044640904708096 (ep144 (BSN.head_sum_c_succ qz5 11 12 rfl rfl) (ep193 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep194 ep203) rfl rfl

noncomputable abbrev qz338 := (@Nat.cast Real Real.instNatCast 13)

noncomputable abbrev qz53 := (@Inv.inv Real Real.instInv (Real.sqrt qz338))

noncomputable abbrev qz548 := (Real.log (Enclosure.sfrac Bool.false 13 1))

noncomputable abbrev qz54 := (@HMul.hMul Real Real Real qz268 qz285 qz548)

noncomputable def ep205 := @Enclosure.Complex.IsNear.of_eq qz41 (Complex.mk (@HMul.hMul Real Real Real qz0 qz53 (Real.cos qz54)) (@HMul.hMul Real Real Real qz0 qz53 (@Neg.neg Real Real.instNeg (Real.sin qz54)))) Bool.true 6014510463 549755813888 2180446171481 9522320452354048 Bool.true 304712415657 1099511627776 4378324145399 19044640904708096 (BSN.cpow_neg_s_mk qz13 113311 1000 13 qz14 rfl)

noncomputable abbrev qz339 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13) qz15)

noncomputable def ep206 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz338) 3780695 1048576 1 1048576 145411 145412 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz338) (Real.sqrt qz339) Bool.false 3780695 1048576 1 1048576 (BSN.sqrt_natCast_div_one 13) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz339) Bool.false 3780695 1048576 1 1048576 3780695 1048576 1 1048576 (BSN.sqrt_enclosure 13 1 1890347 1890348 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep207 := BSN.log_dyadic_bound 5 21 5 4 35742602096145 524288 138568 699352521000 41015625 254545 26 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 5) (BSN.artanhQ 21) 0 4 699352521000 35742602096145 41015625 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep208 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz548 113311 1000 0 1 11551497052968677 4503599627370496 125000000051963 17321000000000000000 1308911682568933759547 4503599627370496000 14163875005887979493 17321000000000000000000 qz18 (BSN.isNear_log_sfrac 13 1 11551497052968677 4503599627370496 125000000051963 17321000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz339) Bool.false 48450490295254733815808 18889465931478580854784 1000000000415704 138568000000000000000 11551497052968677 4503599627370496 125000000051963 17321000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 254545 524288 24973259072661432 36028797018963968 138568 1000000000000000 rfl rfl rfl rfl (ep207 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep209 := BSN.sin_dyadic_bound_f 84732117 2147483648 1 0 1048576 277407 0 1 1 0 1 1 41362 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 84732117) qz292 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 84732117) qz293 0 0 rfl) rfl rfl

noncomputable abbrev qz340 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 304754749) qz16)

noncomputable def ep210 := @Enclosure.Real.IsNear.cos_image qz54 qz340 Bool.false 304754749 1048576 429 524288 Bool.true 41362 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz54 Bool.false 1308911682568933759547 4503599627370496000 14163875005887979493 17321000000000000000000 304754749 1048576 429 524288 (ep208 rfl) rfl) (Enclosure.sfrac_false_div 304754749 1048576) (BSN.cos_reduce1 qz340 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 5962492725086103011328) qz19) 226375608064910080 72057594037927936 Bool.false 41362 1048576 46 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q1 304754749 1048576 226375608064910080 72057594037927936 46 5962492725086103011328 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 41362 1048576 5962492725086103011328 151115727451828646838272 84732117 2147483648 277407 277136 (ep209 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep211 := BSN.cos_dyadic_bound_f 84732117 2147483648 1 0 1048576 277407 0 1 1 0 1 1 1047759 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 84732117) qz288 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 84732117) qz289 0 0 rfl) rfl rfl

noncomputable def ep212 := @Enclosure.Real.IsNear.sin_image qz54 qz340 Bool.false 304754749 1048576 429 524288 Bool.false 1047759 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz54 Bool.false 1308911682568933759547 4503599627370496000 14163875005887979493 17321000000000000000000 304754749 1048576 429 524288 (ep208 rfl) rfl) (Enclosure.sfrac_false_div 304754749 1048576) (BSN.sin_reduce1 qz340 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 5962492725086103011328) qz19) 226375608064910080 72057594037927936 Bool.false 1047759 1048576 46 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q1 304754749 1048576 226375608064910080 72057594037927936 46 5962492725086103011328 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1047759 1048576 5962492725086103011328 151115727451828646838272 84732117 2147483648 277407 277136 (ep211 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz341 := (@Enclosure.Real.IsNear.recentre' qz53 Bool.false 290823 1048576 1 1048576 290823 1048576 1 1048576 (ep206 rfl rfl) rfl)

noncomputable def ep213 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz53 (Real.cos qz54)) (@HMul.hMul Real Real Real qz0 qz53 (@Neg.neg Real Real.instNeg (Real.sin qz54))) Bool.true 6014510463 549755813888 2180446171481 9522320452354048 Bool.true 304712415657 1099511627776 4378324145399 19044640904708096 (@Enclosure.Real.IsNear.mulLit_ft qz53 (Real.cos qz54) 290823 1048576 1 1048576 20681 524288 7496245 9081192448 6014510463 549755813888 2180446171481 9522320452354048 qz341 (@Enclosure.Real.IsNear.recentre' (Real.cos qz54) Bool.true 41362 1048576 59969960 72649539584 20681 524288 7496245 9081192448 (ep210 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz53 (@Neg.neg Real Real.instNeg (Real.sin qz54)) 290823 1048576 1 1048576 1047759 1048576 7496245 9081192448 304712415657 1099511627776 4378324145399 19044640904708096 qz341 (@Enclosure.Real.IsNear.neg (Real.sin qz54) Bool.false 1047759 1048576 7496245 9081192448 (@Enclosure.Real.IsNear.recentre' (Real.sin qz54) Bool.false 1047759 1048576 59969960 72649539584 1047759 1048576 7496245 9081192448 (ep212 rfl rfl) rfl)) rfl)

noncomputable def ep214 := @ep141 6014510463 549755813888 2180446171481 9522320452354048 Bool.true 304712415657 1099511627776 4378324145399 19044640904708096 Bool.false 249284374948019699712000 113361409125 137438953472 9628310520421 2380580113088512 Bool.true 176909080739396167139328 40224467907 274877906944 38500464120169 9522320452354048 (ep142 (BSN.head_sum_c_succ qz5 12 13 rfl rfl) (ep204 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep205 ep213) rfl rfl

noncomputable abbrev qz342 := (@Nat.cast Real Real.instNatCast 14)

noncomputable abbrev qz55 := (@Inv.inv Real Real.instInv (Real.sqrt qz342))

noncomputable abbrev qz549 := (Real.log (Enclosure.sfrac Bool.false 14 1))

noncomputable abbrev qz56 := (@HMul.hMul Real Real Real qz268 qz285 qz549)

noncomputable def ep215 := @Enclosure.Complex.IsNear.of_eq qz40 (Complex.mk (@HMul.hMul Real Real Real qz0 qz55 (Real.cos qz56)) (@HMul.hMul Real Real Real qz0 qz55 (@Neg.neg Real Real.instNeg (Real.sin qz56)))) Bool.true 61339307597 274877906944 527696785815 2380580113088512 Bool.false 80856551089 549755813888 2108202243825 9522320452354048 (BSN.cpow_neg_s_mk qz13 113311 1000 14 qz14 rfl)

noncomputable abbrev qz343 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14) qz15)

noncomputable def ep216 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz342) 3923413 1048576 1 1048576 140121 140122 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz342) (Real.sqrt qz343) Bool.false 3923413 1048576 1 1048576 (BSN.sqrt_natCast_div_one 14) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz343) Bool.false 3923413 1048576 1 1048576 3923413 1048576 1 1048576 (BSN.sqrt_enclosure 14 1 1961706 1961707 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep217 := BSN.log_dyadic_bound 6 22 5 4 51857700491520 524288 138568 1346332575744 176359680 293399 28 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 6) (BSN.artanhQ 22) 0 4 1346332575744 51857700491520 176359680 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep218 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz549 113311 1000 0 1 11885250371606245 4503599627370496 125000000051963 17321000000000000000 269345920971415045439 900719925474099200 14163875005887979493 17321000000000000000000 qz18 (BSN.isNear_log_sfrac 14 1 11885250371606245 4503599627370496 125000000051963 17321000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz343) Bool.false 49850353174629559828480 18889465931478580854784 1000000000415704 138568000000000000000 11885250371606245 4503599627370496 125000000051963 17321000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 293399 524288 24973259072661432 36028797018963968 138568 1000000000000000 rfl rfl rfl rfl (ep217 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep219 := nat_lit 2452559642735656945715091234983400625

noncomputable def ep220 := BSN.cos_dyadic_bound_f 1251425195 2147483648 2 1 1048576 277407 ep219 ep71 ep219 ep219 ep72 ep219 875516 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1251425195) qz288 0 1 ep219 ep71 ep219 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1251425195) qz289 0 1 ep219 ep72 ep219 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz344 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 19597495) (@Nat.cast Real Real.instNatCast 65536))

noncomputable def ep221 := @Enclosure.Real.IsNear.cos_image qz56 qz344 Bool.false 19597495 65536 859 1048576 Bool.true 875516 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz56 Bool.false 269345920971415045439 900719925474099200 14163875005887979493 17321000000000000000000 19597495 65536 859 1048576 (ep218 rfl) rfl) (Enclosure.sfrac_false_div 19597495 65536) (BSN.cos_reduce2 qz344 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 5503826213675141693440) qz306) 226375608064910080 72057594037927936 Bool.false 875516 1048576 47 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q2 19597495 65536 226375608064910080 72057594037927936 47 5503826213675141693440 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 875516 1048576 5503826213675141693440 9444732965739290427392 1251425195 2147483648 277407 277136 (ep220 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep222 := BSN.sin_dyadic_bound_f 1251425195 2147483648 2 1 1048576 277407 ep219 ep67 ep219 ep219 ep68 ep219 577046 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1251425195) qz292 0 1 ep219 ep67 ep219 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1251425195) qz293 0 1 ep219 ep68 ep219 rfl rfl rfl rfl) rfl rfl

noncomputable def ep223 := @Enclosure.Real.IsNear.sin_image qz56 qz344 Bool.false 19597495 65536 859 1048576 Bool.true 577046 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz56 Bool.false 269345920971415045439 900719925474099200 14163875005887979493 17321000000000000000000 19597495 65536 859 1048576 (ep218 rfl) rfl) (Enclosure.sfrac_false_div 19597495 65536) (BSN.sin_reduce2 qz344 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 5503826213675141693440) qz306) 226375608064910080 72057594037927936 Bool.false 577046 1048576 47 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q2 19597495 65536 226375608064910080 72057594037927936 47 5503826213675141693440 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 577046 1048576 5503826213675141693440 9444732965739290427392 1251425195 2147483648 277407 277136 (ep222 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz345 := (@Enclosure.Real.IsNear.recentre' qz55 Bool.false 280243 1048576 1 1048576 280243 1048576 1 1048576 (ep216 rfl rfl) rfl)

noncomputable def ep224 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz55 (Real.cos qz56)) (@HMul.hMul Real Real Real qz0 qz55 (@Neg.neg Real Real.instNeg (Real.sin qz56))) Bool.true 61339307597 274877906944 527696785815 2380580113088512 Bool.false 80856551089 549755813888 2108202243825 9522320452354048 (@Enclosure.Real.IsNear.mulLit_ft qz55 (Real.cos qz56) 280243 1048576 1 1048576 218879 262144 15009811 18162384896 61339307597 274877906944 527696785815 2380580113088512 qz345 (@Enclosure.Real.IsNear.recentre' (Real.cos qz56) Bool.true 875516 1048576 120078488 145299079168 218879 262144 15009811 18162384896 (ep221 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz55 (@Neg.neg Real Real.instNeg (Real.sin qz56)) 280243 1048576 1 1048576 288523 524288 15009811 18162384896 80856551089 549755813888 2108202243825 9522320452354048 qz345 (@Enclosure.Real.IsNear.neg (Real.sin qz56) Bool.true 288523 524288 15009811 18162384896 (@Enclosure.Real.IsNear.recentre' (Real.sin qz56) Bool.true 577046 1048576 120078488 145299079168 288523 524288 15009811 18162384896 (ep223 rfl rfl) rfl)) rfl)

noncomputable def ep225 := @ep139 61339307597 274877906944 527696785815 2380580113088512 Bool.false 80856551089 549755813888 2108202243825 9522320452354048 Bool.false 22730136625673683337216 165383510653 274877906944 2539001826559 595145028272128 Bool.false 112044433630402969600 407615275 549755813888 20304333181997 4761160226177024 (ep140 (BSN.head_sum_c_succ qz5 13 14 rfl rfl) (ep214 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep215 ep224) rfl rfl

noncomputable abbrev qz346 := (@Nat.cast Real Real.instNatCast 15)

noncomputable abbrev qz57 := (@Inv.inv Real Real.instInv (Real.sqrt qz346))

noncomputable abbrev qz550 := (Real.log (Enclosure.sfrac Bool.false 15 1))

noncomputable abbrev qz58 := (@HMul.hMul Real Real Real qz268 qz285 qz550)

noncomputable def ep226 := @Enclosure.Complex.IsNear.of_eq qz39 (Complex.mk (@HMul.hMul Real Real Real qz0 qz57 (Real.cos qz58)) (@HMul.hMul Real Real Real qz0 qz57 (@Neg.neg Real Real.instNeg (Real.sin qz58)))) Bool.false 73754992479 549755813888 509152923595 2380580113088512 Bool.false 121280326137 549755813888 1019826094039 4761160226177024 (BSN.cpow_neg_s_mk qz13 113311 1000 15 qz14 rfl)

noncomputable abbrev qz347 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 15) qz15)

noncomputable def ep227 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz346) 4061117 1048576 1 1048576 135370 135371 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz346) (Real.sqrt qz347) Bool.false 4061117 1048576 1 1048576 (BSN.sqrt_natCast_div_one 15) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz347) Bool.false 4061117 1048576 1 1048576 4061117 1048576 1 1048576 (BSN.sqrt_enclosure 15 1 2030558 2030559 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep228 := BSN.log_dyadic_bound 7 23 6 5 430628584065881355 524288 138568 14087658153505881 266939110305 329571 30 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 7) (BSN.artanhQ 23) 0 5 14087658153505881 430628584065881355 266939110305 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep229 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz550 113311 1000 0 1 12195965485668069 4503599627370496 125000000051963 17321000000000000000 1381937045146534566459 4503599627370496000 14163875005887979493 17321000000000000000000 qz18 (BSN.isNear_log_sfrac 15 1 12195965485668069 4503599627370496 125000000051963 17321000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz347) Bool.false 51153586820399524478976 18889465931478580854784 1000000000415704 138568000000000000000 12195965485668069 4503599627370496 125000000051963 17321000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 329571 524288 24973259072661432 36028797018963968 138568 1000000000000000 rfl rfl rfl rfl (ep228 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep230 := nat_lit 1895401578537178987333898467547283456

noncomputable def ep231 := BSN.sin_dyadic_bound_f 1173343872 2147483648 2 1 1048576 277407 ep230 ep67 ep230 ep230 ep68 ep230 544838 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1173343872) qz292 0 1 ep230 ep67 ep230 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1173343872) qz293 0 1 ep230 ep68 ep230 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz348 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 321757291) qz16)

noncomputable def ep232 := @Enclosure.Real.IsNear.cos_image qz58 qz348 Bool.false 321757291 1048576 859 1048576 Bool.false 544838 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz58 Bool.false 1381937045146534566459 4503599627370496000 14163875005887979493 17321000000000000000000 321757291 1048576 859 1048576 (ep229 rfl) rfl) (Enclosure.sfrac_false_div 321757291 1048576) (BSN.cos_reduce3 qz348 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 82566734800013232177152) qz19) 226375608064910080 72057594037927936 Bool.false 544838 1048576 48 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q3 321757291 1048576 226375608064910080 72057594037927936 48 82566734800013232177152 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 544838 1048576 82566734800013232177152 151115727451828646838272 1173343872 2147483648 277407 277136 (ep231 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep233 := BSN.cos_dyadic_bound_f 1173343872 2147483648 2 1 1048576 277407 ep230 ep71 ep230 ep230 ep72 ep230 895914 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1173343872) qz288 0 1 ep230 ep71 ep230 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1173343872) qz289 0 1 ep230 ep72 ep230 rfl rfl rfl rfl) rfl rfl

noncomputable def ep234 := @Enclosure.Real.IsNear.sin_image qz58 qz348 Bool.false 321757291 1048576 859 1048576 Bool.true 895914 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz58 Bool.false 1381937045146534566459 4503599627370496000 14163875005887979493 17321000000000000000000 321757291 1048576 859 1048576 (ep229 rfl) rfl) (Enclosure.sfrac_false_div 321757291 1048576) (BSN.sin_reduce3 qz348 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 82566734800013232177152) qz19) 226375608064910080 72057594037927936 Bool.false 895914 1048576 48 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q3 321757291 1048576 226375608064910080 72057594037927936 48 82566734800013232177152 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 895914 1048576 82566734800013232177152 151115727451828646838272 1173343872 2147483648 277407 277136 (ep233 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz349 := (@Enclosure.Real.IsNear.recentre' qz57 Bool.false 270741 1048576 1 1048576 270741 1048576 1 1048576 (ep227 rfl rfl) rfl)

noncomputable def ep235 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz57 (Real.cos qz58)) (@HMul.hMul Real Real Real qz0 qz57 (@Neg.neg Real Real.instNeg (Real.sin qz58))) Bool.false 73754992479 549755813888 509152923595 2380580113088512 Bool.false 121280326137 549755813888 1019826094039 4761160226177024 (@Enclosure.Real.IsNear.mulLit_ff qz57 (Real.cos qz58) 270741 1048576 1 1048576 272419 524288 15009811 18162384896 73754992479 549755813888 509152923595 2380580113088512 qz349 (@Enclosure.Real.IsNear.recentre' (Real.cos qz58) Bool.false 544838 1048576 120078488 145299079168 272419 524288 15009811 18162384896 (ep232 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz57 (@Neg.neg Real Real.instNeg (Real.sin qz58)) 270741 1048576 1 1048576 447957 524288 15009811 18162384896 121280326137 549755813888 1019826094039 4761160226177024 qz349 (@Enclosure.Real.IsNear.neg (Real.sin qz58) Bool.true 447957 524288 15009811 18162384896 (@Enclosure.Real.IsNear.recentre' (Real.sin qz58) Bool.true 895914 1048576 120078488 145299079168 447957 524288 15009811 18162384896 (ep234 rfl rfl) rfl)) rfl)

noncomputable def ep236 := @ep137 73754992479 549755813888 509152923595 2380580113088512 Bool.false 121280326137 549755813888 1019826094039 4761160226177024 Bool.false 111194164461992715223040 404522013785 549755813888 10665160229831 2380580113088512 Bool.false 66898653271309319929856 30421985353 137438953472 5331039819009 1190290056544256 (ep138 (BSN.head_sum_c_succ qz5 14 15 rfl rfl) (ep225 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep226 ep235) rfl rfl

noncomputable abbrev qz350 := (@Nat.cast Real Real.instNatCast 16)

noncomputable abbrev qz59 := (@Inv.inv Real Real.instInv (Real.sqrt qz350))

noncomputable abbrev qz551 := (Real.log (Enclosure.sfrac Bool.false 16 1))

noncomputable abbrev qz60 := (@HMul.hMul Real Real Real qz268 qz285 qz551)

noncomputable def ep237 := @Enclosure.Complex.IsNear.of_eq qz38 (Complex.mk (@HMul.hMul Real Real Real qz0 qz59 (Real.cos qz60)) (@HMul.hMul Real Real Real qz0 qz59 (@Neg.neg Real Real.instNeg (Real.sin qz60)))) Bool.false 274872401937 1099511627776 3948353388999 19044640904708096 Bool.true 380369493 274877906944 982572957411 4761160226177024 (BSN.cpow_neg_s_mk qz13 113311 1000 16 qz14 rfl)

noncomputable abbrev qz351 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16) qz15)

noncomputable def ep238 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz350) 4194305 1048576 1 1048576 131071 131072 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz350) (Real.sqrt qz351) Bool.false 4194305 1048576 1 1048576 (BSN.sqrt_natCast_div_one 16) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz351) Bool.false 4194305 1048576 1 1048576 4194305 1048576 1 1048576 (BSN.sqrt_enclosure 16 1 2097152 2097153 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep239 := BSN.log_dyadic_bound 0 32 1 0 1 524288 138568 0 1 0 32 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 32) 0 0 rfl) rfl rfl rfl

noncomputable def ep240 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz551 113311 1000 0 1 3121657384082679 1125899906842624 31250000017321 4330250000000000000 353718119847792440169 1125899906842624000 3540968751962659831 4330250000000000000000 qz18 (BSN.isNear_log_sfrac 16 1 3121657384082679 1125899906842624 31250000017321 4330250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz351) Bool.false 52372720210750067441664 18889465931478580854784 1000000000554272 138568000000000000000 3121657384082679 1125899906842624 31250000017321 4330250000000000000 (BSN.log_rat_reduce_isNear 16 1 4 32 32 0 524288 24973259072661432 36028797018963968 138568 1000000000000000 rfl rfl rfl rfl (ep239 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep241 := BSN.cos_dyadic_bound_f 11886933 2147483648 1 0 1048576 277407 0 1 1 0 1 1 1048559 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 11886933) qz288 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 11886933) qz289 0 0 rfl) rfl rfl

noncomputable abbrev qz352 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 164712835) qz26)

noncomputable def ep242 := @Enclosure.Real.IsNear.cos_image qz60 qz352 Bool.false 164712835 524288 429 524288 Bool.false 1048559 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz60 Bool.false 353718119847792440169 1125899906842624000 3540968751962659831 4330250000000000000000 164712835 524288 429 524288 (ep240 rfl) rfl) (Enclosure.sfrac_false_div 164712835 524288) (BSN.cos_reduce0 qz352 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 418234305300523909120) qz302) 226375608064910080 72057594037927936 Bool.false 1048559 1048576 50 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q0 164712835 524288 226375608064910080 72057594037927936 50 418234305300523909120 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1048559 1048576 418234305300523909120 75557863725914323419136 11886933 2147483648 277407 277136 (ep241 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep243 := BSN.sin_dyadic_bound_f 11886933 2147483648 1 0 1048576 277407 0 1 1 0 1 1 5804 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 11886933) qz292 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 11886933) qz293 0 0 rfl) rfl rfl

noncomputable def ep244 := @Enclosure.Real.IsNear.sin_image qz60 qz352 Bool.false 164712835 524288 429 524288 Bool.false 5804 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz60 Bool.false 353718119847792440169 1125899906842624000 3540968751962659831 4330250000000000000000 164712835 524288 429 524288 (ep240 rfl) rfl) (Enclosure.sfrac_false_div 164712835 524288) (BSN.sin_reduce0 qz352 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 418234305300523909120) qz302) 226375608064910080 72057594037927936 Bool.false 5804 1048576 50 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q0 164712835 524288 226375608064910080 72057594037927936 50 418234305300523909120 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 5804 1048576 418234305300523909120 75557863725914323419136 11886933 2147483648 277407 277136 (ep243 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz353 := (@Enclosure.Real.IsNear.recentre' qz59 Bool.false 262143 1048576 1 1048576 262143 1048576 1 1048576 (ep238 rfl rfl) rfl)

noncomputable def ep245 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz59 (Real.cos qz60)) (@HMul.hMul Real Real Real qz0 qz59 (@Neg.neg Real Real.instNeg (Real.sin qz60))) Bool.false 274872401937 1099511627776 3948353388999 19044640904708096 Bool.true 380369493 274877906944 982572957411 4761160226177024 (@Enclosure.Real.IsNear.mulLit_ff qz59 (Real.cos qz60) 262143 1048576 1 1048576 1048559 1048576 7496245 9081192448 274872401937 1099511627776 3948353388999 19044640904708096 qz353 (@Enclosure.Real.IsNear.recentre' (Real.cos qz60) Bool.false 1048559 1048576 59969960 72649539584 1048559 1048576 7496245 9081192448 (ep242 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz59 (@Neg.neg Real Real.instNeg (Real.sin qz60)) 262143 1048576 1 1048576 1451 262144 7496245 9081192448 380369493 274877906944 982572957411 4761160226177024 qz353 (@Enclosure.Real.IsNear.neg (Real.sin qz60) Bool.false 1451 262144 7496245 9081192448 (@Enclosure.Real.IsNear.recentre' (Real.sin qz60) Bool.false 5804 1048576 59969960 72649539584 1451 262144 7496245 9081192448 (ep244 rfl rfl) rfl)) rfl)

noncomputable def ep246 := @ep135 274872401937 1099511627776 3948353388999 19044640904708096 Bool.true 380369493 274877906944 982572957411 4761160226177024 Bool.false 595889358890195763593216 1083916429507 1099511627776 89269635227647 19044640904708096 Bool.false 8310054073863069761536 60463601213 274877906944 22306732233447 4761160226177024 (ep136 (BSN.head_sum_c_succ qz5 15 16 rfl rfl) (ep236 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep237 ep245) rfl rfl

theorem EMRow36.d7 : Enclosure.Complex.IsNear qz37 Bool.false 1083916429507 1099511627776 89269635227647 19044640904708096 Bool.false 60463601213 274877906944 22306732233447 4761160226177024 := ep134 (BSN.head_sum_c_succ qz5 16 17 rfl rfl) (ep246 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

theorem EMRow36.d8 : @Eq Nat (BSN.factNat (Nat.mul 2 1)) 2 := @Eq.refl Nat 2

theorem EMRow36.d9 : @Eq Nat (Nat.pow 23 1) 23 := @Eq.refl Nat 23

noncomputable def ep247 := nat_lit 2478645784533728767900093412027547

noncomputable def ep248 := nat_lit 1361884158127105469979434156032000

noncomputable def ep249 := nat_lit 538442317881488380480151336851713039669

noncomputable def ep250 := nat_lit 81717691061214056999628833269410588262400

noncomputable abbrev qz580 := (@instHMul Complex Complex.instMul)

noncomputable abbrev qz552 := qz580

noncomputable abbrev qz354 := qz552

noncomputable abbrev qz61 := qz354

noncomputable abbrev qz553 := (@instHSub Complex Complex.instSub)

noncomputable abbrev qz355 := qz553

noncomputable abbrev qz62 := qz355

noncomputable abbrev qz581 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (4 : Complex))

noncomputable abbrev qz582 := (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid))

noncomputable abbrev qz554 := (@HAdd.hAdd Complex Complex Complex qz578 (@HAdd.hAdd Complex Complex Complex qz578 qz581 (@HMul.hMul Complex Complex Complex qz580 Complex.I (@HDiv.hDiv Complex Complex Complex qz582 (↑qz579) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz356 := qz554

noncomputable abbrev qz63 := (Complex.Stirling.logGammaStirling 1 qz356)

noncomputable abbrev qz555 := (@HAdd.hAdd Complex Complex Complex qz578 qz581 (@HMul.hMul Complex Complex Complex qz580 Complex.I (@HDiv.hDiv Complex Complex Complex qz582 (↑qz579) (2 : Complex))))

noncomputable abbrev qz357 := qz555

noncomputable abbrev qz64 := qz357

noncomputable abbrev qz65 := (@HMul.hMul Real Real Real qz268 (@HDiv.hDiv Real Real Real qz271 qz285 (2 : Real)) (Real.log Real.pi))

noncomputable abbrev qz358 := (@instHSub Real Real.instSub)

noncomputable def ep251 := Complex.re (@HMul.hMul Complex Complex Complex qz61 (Complex.exp (@HMul.hMul Complex Complex Complex qz61 Complex.I ↑(@HSub.hSub Real Real Real qz358 (Complex.im (@HSub.hSub Complex Complex Complex qz62 qz63 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz64 (@Nat.cast Complex Complex.instNatCast j))))) qz65))) (zetaApproximant qz5 1 23))

noncomputable def ep252 := @Enclosure.Real.IsNear.of_eq ep251 (@HSub.hSub Real Real Real qz358 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz358 (Complex.im (@HSub.hSub Complex Complex Complex qz62 qz63 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz64 (@Nat.cast Complex Complex.instNatCast j))))) qz65)) (Complex.re (zetaApproximant qz5 1 23))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz358 (Complex.im (@HSub.hSub Complex Complex Complex qz62 qz63 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz64 (@Nat.cast Complex Complex.instNatCast j))))) qz65)) (Complex.im (zetaApproximant qz5 1 23))))

noncomputable def ep253 := nat_lit 99146693880111103098814981553613

noncomputable def ep254 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz358 (Complex.im (@HSub.hSub Complex Complex Complex qz62 qz63 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz64 (@Nat.cast Complex Complex.instNatCast j))))) qz65)) (Complex.re (zetaApproximant qz5 1 23))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz358 (Complex.im (@HSub.hSub Complex Complex Complex qz62 qz63 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz64 (@Nat.cast Complex Complex.instNatCast j))))) qz65)) (Complex.im (zetaApproximant qz5 1 23))) ep253

noncomputable def ep255 := nat_lit 54475366325084218799177366241280

noncomputable def ep256 := nat_lit 8042600068720486974534758391165999272137

noncomputable def ep257 := nat_lit 1225765365918210854994432499041158823936000

noncomputable def ep258 := nat_lit 10781234524404785140563406389

noncomputable def ep259 := nat_lit 680942079063552734989717078016000

noncomputable def ep260 := nat_lit 17017349750919366333755830804848161449

noncomputable def ep261 := nat_lit 612882682959105427497216249520579411968000

noncomputable def ep262 := nat_lit 67512568551300321260553980560005671832124496125154134677604270080

noncomputable def ep263 := @Enclosure.Real.IsNear.mulLit_ff (Real.cos (@HSub.hSub Real Real Real qz358 (Complex.im (@HSub.hSub Complex Complex Complex qz62 qz63 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz64 (@Nat.cast Complex Complex.instNatCast j))))) qz65)) (Complex.re (zetaApproximant qz5 1 23)) 1048575 1048576 6176101

noncomputable def ep264 := nat_lit 2363843642088336625868797691

noncomputable def ep265 := nat_lit 1298793943526368589381632000

noncomputable def ep266 := nat_lit 400911313853053690563885771829

noncomputable def ep267 := nat_lit 67489229687460691010037743616000

noncomputable def ep268 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz358 (Complex.im (@HSub.hSub Complex Complex Complex qz62 qz63 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz64 (@Nat.cast Complex Complex.instNatCast j))))) qz65)) Bool.false 1048575 1048576 49408808

noncomputable abbrev qz359 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 56001493) qz26)

noncomputable def ep269 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz358 (Complex.im (@HSub.hSub Complex Complex Complex qz62 qz63 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz64 (@Nat.cast Complex Complex.instNatCast j))))) qz65) qz359 Bool.false 56001493 524288 349

noncomputable def ep270 := nat_lit 9041410533165048778488331

noncomputable def ep271 := nat_lit 27243577344000000000000000000

noncomputable def ep272 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz358 (Complex.im (@HSub.hSub Complex Complex Complex qz62 qz63 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz64 (@Nat.cast Complex Complex.instNatCast j))))) qz65) Bool.false 76967866322940680763 720575940379279360 ep270 ep271

noncomputable def ep273 := nat_lit 3153431040165048778488331

noncomputable def ep274 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz62 qz63 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz64 (@Nat.cast Complex Complex.instNatCast j))))) qz65 3092524592588845600707 18014398509481984000 ep273 ep271 8500704531 131072000

noncomputable def ep275 := nat_lit 252208304367012022724198400000

noncomputable def ep276 := nat_lit 2270298112000000000000000000

noncomputable def ep277 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz62 qz63 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz64 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 80240284051290826937 900719925474099200 485977429334251349574083 ep276 Bool.false 3092524592588845600707 18014398509481984000

noncomputable def ep278 := nat_lit 2956823040137805201144331

noncomputable def ep279 := @Enclosure.Complex.IsNear.subLitP qz63 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz64 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 72967663621982174737 900719925474099200 477785429309278070342083 ep276 Bool.false 3148641632976132832707 18014398509481984000 ep278

noncomputable def ep280 := nat_lit 361370113353496121341861798715850752

noncomputable def ep281 := nat_lit 870468287676076250197527067248033792

noncomputable abbrev qz583 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex))

noncomputable abbrev qz556 := qz583

noncomputable abbrev qz360 := (@HSub.hSub Complex Complex Complex qz553 qz554 qz556)

noncomputable abbrev qz361 := (Complex.log qz554)

noncomputable abbrev qz66 := (@HSub.hSub Complex Complex Complex qz355 (@HMul.hMul Complex Complex Complex qz354 qz360 qz361) qz356)

noncomputable abbrev qz362 := qz556

noncomputable abbrev qz67 := (@HMul.hMul Complex Complex Complex qz354 qz362 ↑(Real.log qz272))

noncomputable abbrev qz557 := qz582

noncomputable abbrev qz363 := qz557

noncomputable abbrev qz68 := qz363

noncomputable abbrev qz69 := (@instHMul Nat instMulNat)

noncomputable abbrev qz558 := (@instHPow Complex Int (@ZPow.toPow Complex (@DivInvMonoid.toZPow Complex Complex.instDivInvMonoid)))

noncomputable abbrev qz364 := qz558

noncomputable abbrev qz70 := qz364

noncomputable abbrev qz71 := qz356

noncomputable abbrev qz365 := (@OfNat.ofNat Int 1 (@instOfNat 1))

noncomputable abbrev qz72 := qz365

noncomputable abbrev qz366 := (@OfNat.ofNat Int 2 (@instOfNat 2))

noncomputable abbrev qz73 := qz366

noncomputable abbrev qz367 := (@instHSub Int Int.instSub)

noncomputable abbrev qz368 := (@instHMul Int Int.instMul)

noncomputable def ep282 := @Enclosure.Complex.IsNear.of_eq qz63 (@HAdd.hAdd Complex Complex Complex qz4 (@HAdd.hAdd Complex Complex Complex qz4 qz66 qz67) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz69 2 k))) (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz61 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz70 qz71 (@HSub.hSub Int Int Int qz367 qz72 (@HMul.hMul Int Int Int qz368 qz73 (@Nat.cast Int instNatCastInt k)))))) Bool.true 72967663621982174737

noncomputable def ep283 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz4 qz66 qz67) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz69 2 k))) (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz61 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz70 qz71 (@HSub.hSub Int Int Int qz367 qz72 (@HMul.hMul Int Int Int qz368 qz73 (@Nat.cast Int instNatCastInt k))))) Bool.true 72967716153830981137 900719925474099200

noncomputable def ep284 := nat_lit 2507149831375538777522979209216

noncomputable def ep285 := nat_lit 54093251361826102660113616601088000

noncomputable def ep286 := @ep283 7290424058321595103 34642000000000000000000 Bool.false 3148668088248666619331 18014398509481984000 7519437521649881641 69284000000000000000000 Bool.false 2003931 34359738368 3 34359738368 Bool.true 25229713949 17179869184000 113311 51539607552000 Bool.true ep284 72967663621982174737 900719925474099200 477785429309278070342083 ep276 Bool.false ep285

noncomputable def ep287 := @Enclosure.Complex.IsNear.addLitP qz66 qz67 Bool.true 73795421635273080337 900719925474099200 14382625002629518331 69284000000000000000000

noncomputable def ep288 := nat_lit 9564024491714934359588864

noncomputable def ep289 := @ep287 Bool.false 3148668088248666619331 18014398509481984000 7519437521649881641 69284000000000000000000 Bool.false 120447 131072 3 1048576 Bool.false 0 1 0 1 Bool.true ep288 72967716153830981137 900719925474099200 7290424058321595103 34642000000000000000000 Bool.false 3148668088248666619331 3148668088248666619331 18014398509481984000

noncomputable abbrev qz74 := (@HMul.hMul Complex Complex Complex qz354 qz360 qz361)

noncomputable def ep290 := @Enclosure.Complex.IsNear.subLitP qz74 qz71 Bool.true 71768801802956357137 900719925474099200 14382625002629518331 69284000000000000000000 Bool.false 4169282843002623163843

noncomputable def ep291 := nat_lit 12594672352994666477324000

noncomputable def ep292 := @ep290 18014398509481984000 7519437521649881641 69284000000000000000000 Bool.false 9000 4000 0 1 Bool.false 226622 4000 0 1 Bool.true 295181686541092321348000 73795421635273080337 900719925474099200 14382625002629518331 69284000000000000000000 Bool.false ep291 3148668088248666619331 18014398509481984000 7519437521649881641 69284000000000000000000

noncomputable abbrev qz75 := qz360

noncomputable abbrev qz76 := qz361

noncomputable def ep293 := @Enclosure.Complex.IsNear.mul qz75 qz76 Bool.true 71768801802956357137 900719925474099200 14382625002629518331 69284000000000000000000 Bool.false 4169282843002623163843 18014398509481984000 7519437521649881641

noncomputable abbrev qz77 := (Complex.re qz360)

noncomputable abbrev qz78 := (Complex.re qz361)

noncomputable abbrev qz79 := (Complex.im qz360)

noncomputable abbrev qz80 := (Complex.im qz361)

noncomputable def ep294 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz77 qz78) (@HMul.hMul Real Real Real qz0 qz79 qz80) 254583414863279691 36028797018963968 437500001333717 138568000000000000000 19533346793634587353 225179981368524800

noncomputable def ep295 := nat_lit 646435898113242462984520212785659904

noncomputable def ep296 := @Enclosure.Real.IsNear.mulLit_ff qz77 qz78 7000 4000 0 1 36369059266182813 9007199254740992 62500000190531 34642000000000000000

noncomputable def ep297 := @Enclosure.Complex.IsNear.re_isNear qz75 Bool.false 7000 4000 0 1 Bool.false 226622 4000 0 1

noncomputable abbrev qz369 := (Enclosure.sfrac Bool.false 226622 4000)

noncomputable abbrev qz81 := qz369

noncomputable def ep298 := @Enclosure.Complex.IsNear.of_eq qz75 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz81) Bool.false 7000 4000 0 1 Bool.false 226622 4000 0

noncomputable abbrev qz370 := (Enclosure.sfrac Bool.false 9000 4000)

noncomputable abbrev qz82 := qz370

noncomputable abbrev qz371 := (Complex.log (Complex.mk qz82 qz81))

noncomputable def ep299 := @Enclosure.Complex.IsNear.of_eq qz76 qz371 Bool.false 36369059266182813 9007199254740992 62500000190531 34642000000000000000 Bool.false 861935151646115 562949953421312 125000000017321 34642000000000000000

noncomputable def ep300 := nat_lit 2388900243950474885487826020045826548681521953640320117902531792141442178071272960042270720

noncomputable def ep301 := nat_lit 40343809524351947419802109124066307069858243604453246159285556068423582095787929828327424

noncomputable def ep302 := nat_lit 1550395985030684953182922549459226084764233460672117803968728764304240217490778030080

noncomputable def ep303 := BSN.log_dyadic_bound 18670530884 84206530884 5 4 ep300 1048576 277136 ep301 ep302 472839 102877061768 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 18670530884) (BSN.artanhQ 84206530884) 0 4 ep301 ep300 ep302 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz83 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz372 := (Enclosure.Real.IsNear.const Bool.false 1 2)

noncomputable abbrev qz373 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable abbrev qz559 := (Real.log (Enclosure.sfrac Bool.false 51438530884 16000000))

noncomputable def ep304 := @Enclosure.Real.IsNear.mulLit_ff qz83 qz559 1 2 0 1 36369059266182813 4503599627370496 62500000190531 17321000000000000000 36369059266182813 9007199254740992 62500000190531 34642000000000000000 qz372 (BSN.isNear_log_sfrac 51438530884 16000000 36369059266182813 4503599627370496 62500000190531 17321000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 51438530884) qz373)) Bool.false 305085781512775274594304 37778931862957161709568 1000000003048496 277136000000000000000 36369059266182813 4503599627370496 62500000190531 17321000000000000000 (BSN.log_rat_reduce_isNear 51438530884 16000000 11 102877061768 65536000000 472839 1048576 24973259072661432 36028797018963968 277136 1000000000000000 rfl rfl rfl rfl (ep303 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep305 := BSN.arctan_dyadic_bound_f 9000 226622 1 0 1048576 277136 0 1 1 0 1 1 41620 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 226622) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 226622) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz84 := (@HMul.hMul Real Real Real qz268 (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz85 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 2) Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 qz372 BSN.pi_near_15 rfl)

noncomputable abbrev qz374 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 226622)))

noncomputable def ep306 := @Enclosure.Real.IsNear.subLit_ff_p qz84 qz374 884279719003555 562949953421312 1 2000000000000000 41620 1048576 1 277136 903804513572476682240 861935151646115 562949953421312 125000000017321 34642000000000000000 qz85 (ep305 rfl) rfl rfl

noncomputable abbrev qz375 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 226622) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep307 := @Enclosure.Complex.IsNear.re_isNear qz76 Bool.false 36369059266182813 9007199254740992 62500000190531 34642000000000000000 Bool.false 861935151646115 562949953421312 125000000017321 34642000000000000000 (ep299 (@congrArg Complex Complex qz71 (Complex.mk qz82 qz81) Complex.log (BSN.w_shift_mk qz13 Bool.false 113311 1000 2 qz14 rfl)) (@Enclosure.Complex.IsNear.of_parts qz371 Bool.false 36369059266182813 9007199254740992 62500000190531 34642000000000000000 Bool.false 861935151646115 562949953421312 125000000017321 34642000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz371) (@HMul.hMul Real Real Real qz0 qz83 qz559) Bool.false 36369059266182813 9007199254740992 62500000190531 34642000000000000000 (Enclosure.clog_re_eq 9000 226622 4000 51438530884 16000000 rfl rfl rfl) (ep304 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz371) qz375 Bool.false 861935151646115 562949953421312 125000000017321 34642000000000000000 (Enclosure.clog_im_eq 9000 226622 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz375 (@HSub.hSub Real Real Real qz358 qz84 qz374) Bool.false 861935151646115 562949953421312 125000000017321 34642000000000000000 (BSN.arctan_recip 226622 9000 rfl rfl) ep306))))

noncomputable def ep308 := @Enclosure.Real.IsNear.mulLit_ff qz79 qz80 226622 4000 0 1 861935151646115 562949953421312 125000000017321 34642000000000000000

noncomputable def ep309 := @Enclosure.Complex.IsNear.im_isNear qz75 Bool.false 7000 4000 0 1 Bool.false 226622 4000 0 1

noncomputable def ep310 := @Enclosure.Complex.IsNear.im_isNear qz76 Bool.false 36369059266182813 9007199254740992 62500000190531 34642000000000000000 Bool.false 861935151646115 562949953421312 125000000017321 34642000000000000000 (ep299 (@congrArg Complex Complex qz71 (Complex.mk qz82 qz81) Complex.log (BSN.w_shift_mk qz13 Bool.false 113311 1000 2 qz14 rfl)) (@Enclosure.Complex.IsNear.of_parts qz371 Bool.false 36369059266182813 9007199254740992 62500000190531 34642000000000000000 Bool.false 861935151646115 562949953421312 125000000017321 34642000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz371) (@HMul.hMul Real Real Real qz0 qz83 qz559) Bool.false 36369059266182813 9007199254740992 62500000190531 34642000000000000000 (Enclosure.clog_re_eq 9000 226622 4000 51438530884 16000000 rfl rfl rfl) (ep304 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz371) qz375 Bool.false 861935151646115 562949953421312 125000000017321 34642000000000000000 (Enclosure.clog_im_eq 9000 226622 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz375 (@HSub.hSub Real Real Real qz358 qz84 qz374) Bool.false 861935151646115 562949953421312 125000000017321 34642000000000000000 (BSN.arctan_recip 226622 9000 rfl rfl) ep306))))

noncomputable abbrev qz376 := (Enclosure.Real.IsNear.const Bool.false 226622 4000)

noncomputable abbrev qz86 := (@ep298 1 (BSN.w_sub_half_mk qz285 Bool.false 113311 1000 2 qz287 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz369 Bool.false 7000 4000 0 1 Bool.false 226622 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) qz376))

noncomputable def ep311 := @ep294 14163875001962659831 69284000000000000000000 ep295 71768801802956357137 900719925474099200 14382625002629518331 69284000000000000000000 (@ep296 254583414863279691 36028797018963968 437500001333717 138568000000000000000 (ep297 qz86) ep307 rfl) (@ep308 19533346793634587353 225179981368524800 14163875001962659831 69284000000000000000000 (ep309 qz86) ep310 rfl) rfl

noncomputable def ep312 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz77 qz80) (@HMul.hMul Real Real Real qz0 qz79 qz78) 6033546061522805 2251799813685248 875000000121247 138568000000000000000 4121014474510440723843 18014398509481984000

noncomputable def ep313 := nat_lit 9388390329074407928452997279136088064

noncomputable def ep314 := @Enclosure.Real.IsNear.mulLit_ff qz77 qz80 7000 4000 0 1 861935151646115 562949953421312 125000000017321 34642000000000000000

noncomputable def ep315 := @Enclosure.Real.IsNear.mulLit_ff qz79 qz78 226622 4000 0 1 36369059266182813 9007199254740992 62500000190531 34642000000000000000

noncomputable def ep316 := @ep312 7081937521589258141 69284000000000000000000 ep313 4169282843002623163843 18014398509481984000 7519437521649881641 69284000000000000000000 (@ep314 6033546061522805 2251799813685248 875000000121247 138568000000000000000 (ep297 qz86) ep310 rfl) (@ep315 4121014474510440723843 18014398509481984000 7081937521589258141 69284000000000000000000 (ep309 qz86) ep307 rfl) rfl

noncomputable def ep317 := @Enclosure.Complex.IsNear.of_eq qz71 (Complex.mk qz82 qz81) Bool.false 9000 4000 0 1 Bool.false 226622 4000 0 1 (BSN.w_shift_mk qz13 Bool.false 113311 1000 2 qz14 rfl)

noncomputable abbrev qz377 := (ep317 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9000 4000) (Enclosure.sfrac Bool.false 226622 4000) Bool.false 9000 4000 0 1 Bool.false 226622 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 226622 4000)))

noncomputable abbrev qz87 := qz377

noncomputable def ep318 := ep292 (@ep293 69284000000000000000000 (ep311 rfl) (ep316 rfl)) qz87 rfl rfl rfl rfl rfl rfl

noncomputable abbrev qz88 := qz362

noncomputable def ep319 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re qz88) (Complex.re ↑qz2)) (@HMul.hMul Real Real Real qz0 (Complex.im qz88) (Complex.im ↑qz2)) 120447 131072 3 1048576 0 1 0 1 120447 120447

noncomputable def ep320 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz88) (Complex.re ↑qz2) 1 2 0 1 120447 65536 3 524288 120447 131072 3 1048576

noncomputable abbrev qz89 := (@Enclosure.Complex.IsNear.of_eq qz362 (Complex.mk (Enclosure.sfrac Bool.false 1 2) qz284) Bool.false 1 2 0 1 Bool.false 0 1 0 1 BSN.half_c_mk (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 2) qz284 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz372 qz295))

noncomputable def ep321 := ep320 (@Enclosure.Complex.IsNear.re_isNear qz88 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz89) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz2) qz2 Bool.false 120447 65536 3 524288 (Complex.ofReal_re qz2) EMRow36.d4)

noncomputable def ep322 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz88) (Complex.im ↑qz2) 0 1 0 1 0 1 0 1 0 1 0 1

noncomputable def ep323 := ep322 (@Enclosure.Complex.IsNear.im_isNear qz88 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz89) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz2) qz10 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz2) (0 : Real) qz10 (Complex.ofReal_im qz2) Enclosure.sfrac_zero_eq) qz20)

noncomputable def ep324 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re qz88) (Complex.im ↑qz2)) (@HMul.hMul Real Real Real qz0 (Complex.im qz88) (Complex.re ↑qz2)) 0 1 0 1 0 1 0 1 0 0

noncomputable def ep325 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz88) (Complex.im ↑qz2) 1 2 0 1 0 1 0 1 0 1 0 1

noncomputable def ep326 := ep325 (@Enclosure.Complex.IsNear.re_isNear qz88 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz89) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz2) qz10 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz2) (0 : Real) qz10 (Complex.ofReal_im qz2) Enclosure.sfrac_zero_eq) qz20)

noncomputable def ep327 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz88) (Complex.re ↑qz2) 0 1 0 1 120447 65536 3 524288 0 1 0 1

noncomputable def ep328 := ep327 (@Enclosure.Complex.IsNear.im_isNear qz88 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz89) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz2) qz2 Bool.false 120447 65536 3 524288 (Complex.ofReal_re qz2) EMRow36.d4)

noncomputable def ep329 := @ep289 7519437521649881641 69284000000000000000000 (ep318 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz88 (↑qz2) Bool.false 120447 131072 3 1048576 Bool.false 0 1 0 1 (@ep319 131072 3 1048576 (ep321 rfl) (ep323 rfl) rfl rfl) (@ep324 1 0 1 (ep326 rfl) (ep328 rfl) rfl rfl))

noncomputable abbrev qz90 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)

noncomputable abbrev qz378 := (@Nat.cast Complex Complex.instNatCast 1)

noncomputable abbrev qz91 := (@HMul.hMul Complex Complex Complex qz354 (@HMul.hMul Complex Complex Complex qz354 (2 : Complex) qz378) (@HSub.hSub Complex Complex Complex qz355 (@HMul.hMul Complex Complex Complex qz354 (2 : Complex) qz378) (1 : Complex)))

noncomputable abbrev qz379 := (@HPow.hPow Complex Int Complex qz558 qz554 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz92 := qz379

noncomputable def ep330 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz69 2 k))) (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz61 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz70 qz71 (@HSub.hSub Int Int Int qz367 qz72 (@HMul.hMul Int Int Int qz368 qz73 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz69 2 k))) (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz61 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz70 qz71 (@HSub.hSub Int Int Int qz367 qz72 (@HMul.hMul Int Int Int qz368 qz73 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 (@Rat.cast Complex Complex.instRatCast (bernoulli qz90)) qz91) qz92)) Bool.false 2003931 34359738368 3 34359738368

noncomputable def ep331 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz69 2 k))) (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz61 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz70 qz71 (@HSub.hSub Int Int Int qz367 qz72 (@HMul.hMul Int Int Int qz368 qz73 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 (@Rat.cast Complex Complex.instRatCast (bernoulli qz90)) qz91) qz92) Bool.false 0 1 0 1 Bool.false

noncomputable def ep332 := @ep331 0 1 0 1 Bool.false 2003931 34359738368 3 34359738368 Bool.true 25229713949 17179869184000 113311 51539607552000 Bool.false 2003931 2003931 34359738368 3 34359738368 Bool.true 25229713949 25229713949 17179869184000 113311

noncomputable def ep333 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz69 2 k))) (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz61 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz70 qz71 (@HSub.hSub Int Int Int qz367 qz72 (@HMul.hMul Int Int Int qz368 qz73 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep334 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz68 (@Rat.cast Complex Complex.instRatCast (bernoulli qz90)) qz91) qz92 Bool.false 2003931 34359738368 3 34359738368 Bool.true 25229713949 17179869184000 113311 51539607552000

noncomputable abbrev qz93 := (Complex.re qz379)

noncomputable abbrev qz94 := (Complex.im qz379)

noncomputable def ep335 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz68 (@Rat.cast Complex Complex.instRatCast (bernoulli qz90)) qz91)) qz93) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz68 (@Rat.cast Complex Complex.instRatCast (bernoulli qz90)) qz91)) qz94) 2003931 34359738368 3 34359738368 0 1 0

noncomputable def ep336 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz68 (@Rat.cast Complex Complex.instRatCast (bernoulli qz90)) qz91)) qz93 1 12 0 1 6011793 8589934592 9 8589934592 2003931

noncomputable def ep337 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz68 (@Rat.cast Complex Complex.instRatCast (bernoulli qz90)) qz91) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz10) Bool.false 1 12 0 1 Bool.false 0 1 0 1

noncomputable abbrev qz380 := (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 12) qz10 Bool.false 1 12 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 12) qz20)

noncomputable def ep338 := @Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz68 (@Rat.cast Complex Complex.instRatCast (bernoulli qz90)) qz91) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep337 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz380)

noncomputable def ep339 := @Enclosure.Complex.IsNear.re_isNear qz92 Bool.false 6011793 8589934592 9 8589934592 Bool.true 75689141847 4294967296000 113311 4294967296000

noncomputable abbrev qz560 := (@instHPow Complex Nat (@NPow.toPow Complex (@Monoid.toNPow Complex (@Semiring.toMonoid Complex Complex.instSemiring))))

noncomputable abbrev qz381 := (@HPow.hPow Complex Nat Complex qz560 qz554 1)

noncomputable abbrev qz95 := (@Inv.inv Complex Complex.instInv qz381)

noncomputable def ep340 := @Enclosure.Complex.IsNear.of_eq qz92 qz95 Bool.false 6011793 8589934592 9 8589934592 Bool.true 75689141847 4294967296000 113311

noncomputable def ep341 := @Enclosure.Complex.IsNear.of_parts qz95 Bool.false 6011793 8589934592 9 8589934592 Bool.true 75689141847 4294967296000 113311

noncomputable abbrev qz96 := (Complex.re qz381)

noncomputable abbrev qz97 := (@MonoidWithZeroHom Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz98 := (@MonoidWithZeroHom.funLike Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz99 := qz381

noncomputable def ep342 := @Enclosure.Real.IsNear.mulLit_ff qz96 (@Inv.inv Real Real.instInv (@DFunLike.coe qz97 Complex (fun (x : Complex) => Real) qz98 Complex.normSq qz99)) 9000 4000 0 1 667977 2147483648 1 2147483648

noncomputable def ep343 := @Enclosure.Complex.IsNear.re_isNear qz99 Bool.false 9000 4000 0 1 Bool.false 226622 4000 0 1

noncomputable def ep344 := @Enclosure.Complex.IsNear.of_eq qz99 qz71 Bool.false 9000 4000 0 1 Bool.false 226622 4000 0

noncomputable def ep345 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz97 Complex (fun (x : Complex) => Real) qz98 Complex.normSq qz99)) Bool.false 667977 2147483648 1 2147483648 667977 2147483648 1

noncomputable abbrev qz100 := (Complex.im qz381)

noncomputable abbrev qz382 := (@instHAdd Real Real.instAdd)

noncomputable def ep346 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz97 Complex (fun (x : Complex) => Real) qz98 Complex.normSq qz99) (@HAdd.hAdd Real Real Real qz382 (@HMul.hMul Real Real Real qz0 qz96 qz96) (@HMul.hMul Real Real Real qz0 qz100 qz100)) Bool.false 12859632721 4000000 0 1

noncomputable def ep347 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz96 qz96) (@HMul.hMul Real Real Real qz0 qz100 qz100) 81 16 0 1 12839382721 4000000

noncomputable def ep348 := @Enclosure.Real.IsNear.mulLit_ff qz96 qz96 9000 4000 0 1 9000 4000 0 1

noncomputable def ep349 := @Enclosure.Real.IsNear.mulLit_ff qz100 qz100 226622 4000 0 1 226622 4000 0 1

noncomputable def ep350 := @Enclosure.Complex.IsNear.im_isNear qz99 Bool.false 9000 4000 0 1 Bool.false 226622 4000 0 1

noncomputable abbrev qz101 := (ep343 (@ep344 1 (BSN.pow_one_c qz356) qz377))

noncomputable abbrev qz102 := (ep350 (@ep344 1 (BSN.pow_one_c qz356) qz377))

noncomputable def ep351 := @ep347 0 1 205754123536 12859632721 4000000 0 1 (@ep348 81 16 0 1 qz101 qz101 rfl) (@ep349 12839382721 4000000 0 1 qz102 qz102 rfl)

noncomputable def ep352 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz97 Complex (fun (x : Complex) => Real) qz98 Complex.normSq qz99) 12859632721 4000000 0 1 333988 333989 1073741824 (ep346 (Enclosure.Complex.normSq_eq_mul_add_mul qz99) (ep351 rfl rfl)) rfl

noncomputable def ep353 := @Enclosure.Real.IsNear.of_eq (Complex.re qz95) (@HMul.hMul Real Real Real qz0 qz96 (@Inv.inv Real Real.instInv (@DFunLike.coe qz97 Complex (fun (x : Complex) => Real) qz98 Complex.normSq qz99))) Bool.false 6011793 8589934592 9 8589934592 (Enclosure.Complex.inv_re_eq_mul qz99) (@ep342 6011793 8589934592 9 8589934592 qz101 (@ep345 2147483648 (ep352 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep354 := @Enclosure.Real.IsNear.of_eq (Complex.im qz95) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz100) (@Inv.inv Real Real.instInv (@DFunLike.coe qz97 Complex (fun (x : Complex) => Real) qz98 Complex.normSq qz99))) Bool.true 75689141847 4294967296000 113311 4294967296000 (Enclosure.Complex.inv_im_eq_mul qz99)

noncomputable def ep355 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz100) (@Inv.inv Real Real.instInv (@DFunLike.coe qz97 Complex (fun (x : Complex) => Real) qz98 Complex.normSq qz99)) 226622 4000 0 1 667977 2147483648 1

noncomputable def ep356 := @ep355 2147483648 75689141847 4294967296000 113311 4294967296000 (@Enclosure.Real.IsNear.neg qz100 Bool.false 226622 4000 0 1 qz102) (@ep345 2147483648 (ep352 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep357 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz68 (@Rat.cast Complex Complex.instRatCast (bernoulli qz90)) qz91)) qz94 0 1 0 1 75689141847 4294967296000 113311 4294967296000 0

noncomputable def ep358 := @Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz68 (@Rat.cast Complex Complex.instRatCast (bernoulli qz90)) qz91) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep337 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz380)

noncomputable def ep359 := @Enclosure.Complex.IsNear.im_isNear qz92 Bool.false 6011793 8589934592 9 8589934592 Bool.true 75689141847 4294967296000 113311 4294967296000

noncomputable abbrev qz103 := (@ep340 4294967296000 (BSN.zpow_one_sub_two_mul qz356 1 1 rfl rfl) (@ep341 4294967296000 ep353 (ep354 ep356)))

noncomputable def ep360 := @ep335 1 2003931 2003931 34359738368 3 34359738368 (@ep336 34359738368 3 34359738368 ep338 (ep339 qz103) rfl) (@ep357 1 0 1 ep358 (ep359 qz103) rfl) rfl

noncomputable def ep361 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz68 (@Rat.cast Complex Complex.instRatCast (bernoulli qz90)) qz91)) qz94) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz68 (@Rat.cast Complex Complex.instRatCast (bernoulli qz90)) qz91)) qz93) 25229713949 17179869184000 113311 51539607552000 0 1 0

noncomputable def ep362 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz68 (@Rat.cast Complex Complex.instRatCast (bernoulli qz90)) qz91)) qz94 1 12 0 1 75689141847 4294967296000 113311 4294967296000 25229713949

noncomputable def ep363 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz68 (@Rat.cast Complex Complex.instRatCast (bernoulli qz90)) qz91)) qz93 0 1 0 1 6011793 8589934592 9 8589934592 0

noncomputable def ep364 := @ep361 1 25229713949 25229713949 17179869184000 113311 51539607552000 (@ep362 17179869184000 113311 51539607552000 ep338 (ep359 qz103) rfl) (@ep363 1 0 1 ep358 (ep339 qz103) rfl) rfl

noncomputable abbrev qz104 := (@Enclosure.Complex.IsNear.mk qz284 qz284 Bool.false 0 1 0 1 Bool.false 0 1 0 1 qz295 qz295)

noncomputable def ep365 := @ep332 51539607552000 (@ep333 0 1 0 1 (BSN.stirling_sum_base qz71) qz104) (ep334 (ep360 rfl) (ep364 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep366 := @ep286 3148641632976132832707 18014398509481984000 ep278 ep271 (ep329 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep330 Bool.true 25229713949 17179869184000 113311 51539607552000 (BSN.stirling_sum_succ qz71 0 1 rfl) (ep365 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep367 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz64 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz13 2) Bool.false 36363102146543261 4503599627370496 62500000190531 17321000000000000000 Bool.false 876828756051363 281474976710656

noncomputable abbrev qz105 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz274 qz357 qz378))

noncomputable def ep368 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz13 2) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz13 1) qz105) Bool.false 36363102146543261 4503599627370496 62500000190531 17321000000000000000 Bool.false 876828756051363 281474976710656 125000000017321 17321000000000000000

noncomputable def ep369 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz13 1) qz105 Bool.false 36362049879555741 9007199254740992 62500000190531 34642000000000000000 Bool.false 881796154164643 562949953421312 125000000017321 34642000000000000000 Bool.false

noncomputable def ep370 := nat_lit 655059413108830053887397356109824

noncomputable def ep371 := nat_lit 987221414755163486610901696512

noncomputable abbrev qz106 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz274 qz357 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep372 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz13 1) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz13 0) qz106) Bool.false 36362049879555741 9007199254740992 62500000190531 34642000000000000000 Bool.false 881796154164643 562949953421312 125000000017321 34642000000000000000

noncomputable def ep373 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz13 0) qz106 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz383 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz81))

noncomputable def ep374 := @Enclosure.Complex.IsNear.of_eq qz106 qz383 Bool.false 36362049879555741 9007199254740992 62500000190531 34642000000000000000 Bool.false 881796154164643 562949953421312 125000000017321 34642000000000000000

noncomputable def ep375 := nat_lit 2370803999306957184653908016586404734842273181885222713430116299596414679321864908842270720

noncomputable def ep376 := nat_lit 39763206447346511209547633043230937096204592661216799646415684318039993195144130788327424

noncomputable def ep377 := nat_lit 1498040775771882084201313570636934226498417994186343980031304740582671794373978030080

noncomputable def ep378 := BSN.log_dyadic_bound 18590530884 84126530884 5 4 ep375 1048576 277136 ep376 ep377 471207 102717061768 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 18590530884) (BSN.artanhQ 84126530884) 0 4 ep376 ep375 ep377 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep379 := @Enclosure.Real.IsNear.mulLit_ff qz83 (Real.log (Enclosure.sfrac Bool.false 51358530884 16000000)) 1 2 0 1 36362049879555741 4503599627370496 62500000190531 17321000000000000000 36362049879555741 9007199254740992 62500000190531 34642000000000000000 qz372 (BSN.isNear_log_sfrac 51358530884 16000000 36362049879555741 4503599627370496 62500000190531 17321000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 51358530884) qz373)) Bool.false 305026982516040325398528 37778931862957161709568 1000000003048496 277136000000000000000 36362049879555741 4503599627370496 62500000190531 17321000000000000000 (BSN.log_rat_reduce_isNear 51358530884 16000000 11 102717061768 65536000000 471207 1048576 24973259072661432 36028797018963968 277136 1000000000000000 rfl rfl rfl rfl (ep378 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep380 := BSN.arctan_dyadic_bound_f 1000 226622 1 0 1048576 277136 0 1 1 0 1 1 4626 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 226622) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 226622) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz384 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable abbrev qz385 := (@Nat.cast Real Real.instNatCast 226622)

noncomputable def ep381 := @Enclosure.Real.IsNear.subLit_ff_p qz84 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz384 qz385)) 884279719003555 562949953421312 1 2000000000000000 4626 1048576 1 277136 924630284149344698368 881796154164643 562949953421312 125000000017321 34642000000000000000 qz85 (ep380 rfl) rfl rfl

noncomputable abbrev qz107 := (@HAdd.hAdd Complex Complex Complex qz274 qz357 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz386 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz81)

noncomputable def ep382 := @ep373 36362049879555741 9007199254740992 62500000190531 34642000000000000000 Bool.false 881796154164643 562949953421312 125000000017321 34642000000000000000 Bool.false 36362049879555741 36362049879555741 9007199254740992 62500000190531 34642000000000000000 Bool.false 881796154164643 881796154164643 562949953421312 125000000017321 34642000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz13 0) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz13) qz104) (ep374 (@congrArg Complex Complex qz107 qz386 Complex.log (BSN.w_shift_mk qz13 Bool.false 113311 1000 0 qz14 rfl)) (@Enclosure.Complex.IsNear.of_parts qz383 Bool.false 36362049879555741 9007199254740992 62500000190531 34642000000000000000 Bool.false 881796154164643 562949953421312 125000000017321 34642000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz383) (@HMul.hMul Real Real Real qz0 qz83 (Real.log (Enclosure.sfrac Bool.false 51358530884 16000000))) Bool.false 36362049879555741 9007199254740992 62500000190531 34642000000000000000 (Enclosure.clog_re_eq 1000 226622 4000 51358530884 16000000 rfl rfl rfl) (ep379 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz383) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz385 qz384)) Bool.false 881796154164643 562949953421312 125000000017321 34642000000000000000 (Enclosure.clog_im_eq 1000 226622 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz385 qz384)) (@HSub.hSub Real Real Real qz358 qz84 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz384 qz385))) Bool.false 881796154164643 562949953421312 125000000017321 34642000000000000000 (BSN.arctan_recip 226622 1000 rfl rfl) ep381)))) rfl rfl

noncomputable abbrev qz387 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz81))

noncomputable def ep383 := @Enclosure.Complex.IsNear.of_eq qz105 qz387 Bool.false 36364154413530781 9007199254740992 62500000190531 34642000000000000000 Bool.false 871861357938083 562949953421312 125000000017321 34642000000000000000

noncomputable def ep384 := nat_lit 2376220235210559100069272835587321415933313852170218554277554889158510693518847324202270720

noncomputable def ep385 := nat_lit 39936680487522185523698780300989234302368075603787649464641086303580364639609270500327424

noncomputable def ep386 := nat_lit 1513582386694743338916589702925952182315160087471860778788173322801872561309018030080

noncomputable def ep387 := BSN.log_dyadic_bound 18614530884 84150530884 5 4 ep384 1048576 277136 ep385 ep386 471697 102765061768 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 18614530884) (BSN.artanhQ 84150530884) 0 4 ep385 ep384 ep386 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep388 := @Enclosure.Real.IsNear.mulLit_ff qz83 (Real.log (Enclosure.sfrac Bool.false 51382530884 16000000)) 1 2 0 1 36364154413530781 4503599627370496 62500000190531 17321000000000000000 36364154413530781 9007199254740992 62500000190531 34642000000000000000 qz372 (BSN.isNear_log_sfrac 51382530884 16000000 36364154413530781 4503599627370496 62500000190531 17321000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 51382530884) qz373)) Bool.false 305044636626579617742848 37778931862957161709568 1000000003048496 277136000000000000000 36364154413530781 4503599627370496 62500000190531 17321000000000000000 (BSN.log_rat_reduce_isNear 51382530884 16000000 11 102765061768 65536000000 471697 1048576 24973259072661432 36028797018963968 277136 1000000000000000 rfl rfl rfl rfl (ep387 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep389 := BSN.arctan_dyadic_bound_f 5000 226622 1 0 1048576 277136 0 1 1 0 1 1 23131 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 226622) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 226622) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz388 := (@Nat.cast Real Real.instNatCast 5000)

noncomputable def ep390 := @Enclosure.Real.IsNear.subLit_ff_p qz84 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz388 qz385)) 884279719003555 562949953421312 1 2000000000000000 23131 1048576 1 277136 914212895261283319808 871861357938083 562949953421312 125000000017321 34642000000000000000 qz85 (ep389 rfl) rfl rfl

noncomputable abbrev qz108 := (@HAdd.hAdd Complex Complex Complex qz274 qz357 qz378)

noncomputable abbrev qz389 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz81)

noncomputable def ep391 := @ep369 36364154413530781 9007199254740992 62500000190531 34642000000000000000 Bool.false 871861357938083 562949953421312 125000000017321 34642000000000000000 Bool.false ep370 36363102146543261 4503599627370496 62500000190531 17321000000000000000 Bool.false ep371 876828756051363 281474976710656 125000000017321 17321000000000000000 (ep372 (BSN.log_sum_c_succ qz13 0 1 rfl) (ep382 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep383 (@congrArg Complex Complex qz108 qz389 Complex.log (BSN.w_shift_mk qz13 Bool.false 113311 1000 1 qz14 rfl)) (@Enclosure.Complex.IsNear.of_parts qz387 Bool.false 36364154413530781 9007199254740992 62500000190531 34642000000000000000 Bool.false 871861357938083 562949953421312 125000000017321 34642000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz387) (@HMul.hMul Real Real Real qz0 qz83 (Real.log (Enclosure.sfrac Bool.false 51382530884 16000000))) Bool.false 36364154413530781 9007199254740992 62500000190531 34642000000000000000 (Enclosure.clog_re_eq 5000 226622 4000 51382530884 16000000 rfl rfl rfl) (ep388 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz387) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz385 qz388)) Bool.false 871861357938083 562949953421312 125000000017321 34642000000000000000 (Enclosure.clog_im_eq 5000 226622 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz385 qz388)) (@HSub.hSub Real Real Real qz358 qz84 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz388 qz385))) Bool.false 871861357938083 562949953421312 125000000017321 34642000000000000000 (BSN.arctan_recip 226622 5000 rfl rfl) ep390)))) rfl rfl

noncomputable def ep392 := @ep279 ep271 Bool.false 36363102146543261 4503599627370496 62500000190531 17321000000000000000 Bool.false 876828756051363 281474976710656 125000000017321 17321000000000000000 Bool.true ep280 80240284051290826937 900719925474099200 485977429334251349574083 ep276 Bool.false ep281 3092524592588845600707 18014398509481984000 ep273 ep271 (@ep282 900719925474099200 477785429309278070342083 ep276 Bool.false 3148641632976132832707 18014398509481984000 ep278 ep271 (BSN.logGammaStirling_unfold 1 qz71) (ep366 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep367 125000000017321 17321000000000000000 (BSN.log_sum_c_eq qz13 2) (ep368 (BSN.log_sum_c_succ qz13 1 2 rfl) (ep391 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz109 := (@HDiv.hDiv Real Real Real qz271 qz285 (2 : Real))

noncomputable def ep393 := @Enclosure.Real.IsNear.mulLit_ff qz109 (Real.log Real.pi) 113311 2000 0 1 75021 65536 1 262144 8500704531 131072000 113311 524288000 (@Enclosure.Real.IsNear.of_eq qz109 (Enclosure.sfrac Bool.false 113311 2000) Bool.false 113311 2000 0 1 (BSN.t_half_eq qz13 Bool.false 113311 1000 qz14) (Enclosure.Real.IsNear.const Bool.false 113311 2000)) EMRow36.d5 rfl

noncomputable def ep394 := @ep274 113311 524288000 ep275 76967866322940680763 720575940379279360 ep270 ep271 (@ep277 ep273 ep271 (ep392 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep393 rfl rfl

noncomputable def ep395 := BSN.cos_dyadic_bound_f 474351 2147483648 1 0 1048576 277407 0 1 1 0 1 1 1048575 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 474351) qz288 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 474351) qz289 0 0 rfl) rfl rfl

noncomputable def ep396 := @ep269 1048576 Bool.false 1048575 1048576 1 138568 (@ep272 56001493 524288 349 1048576 ep394 rfl) (Enclosure.sfrac_false_div 56001493 524288) (BSN.cos_reduce0 qz359 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16689746506915250176) qz302) 226375608064910080 72057594037927936 Bool.false 1048575 1048576 17 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q0 56001493 524288 226375608064910080 72057594037927936 17 16689746506915250176 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1048575 1048576 16689746506915250176 75557863725914323419136 474351 2147483648 277407 277136 (ep395 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep397 := nat_lit 46672010928159243032742019

noncomputable def ep398 := nat_lit 649396971763184294690816000

noncomputable def ep399 := nat_lit 200344873536814730187996437101

noncomputable def ep400 := nat_lit 33744614843730345505018871808000

noncomputable abbrev qz390 := (@HPow.hPow Complex Complex Complex qz532 (@Nat.cast Complex Complex.instNatCast 23) qz533)

noncomputable abbrev qz110 := qz390

noncomputable abbrev qz391 := (@Nat.cast Complex Complex.instNatCast 23)

noncomputable abbrev qz111 := (@HAdd.hAdd Complex Complex Complex qz274 (@HDiv.hDiv Complex Complex Complex qz363 qz391 (@HSub.hSub Complex Complex Complex qz355 qz273 (1 : Complex))) qz362)

noncomputable abbrev qz112 := (@instHSub Nat instSubNat)

noncomputable abbrev qz392 := qz560

noncomputable abbrev qz113 := qz392

noncomputable abbrev qz114 := qz391

noncomputable def ep401 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz5 1 23) (@HAdd.hAdd Complex Complex Complex qz4 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 23, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz7) (@HMul.hMul Complex Complex Complex qz61 qz110 (@HAdd.hAdd Complex Complex Complex qz4 qz111 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz69 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz69 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz112 (@HMul.hMul Nat Nat Nat qz69 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz113 qz114 (@HSub.hSub Nat Nat Nat qz112 (@HMul.hMul Nat Nat Nat qz69 2 k) 1))))))) Bool.false ep264 ep265 ep266

noncomputable def ep402 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 23, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz7) (@HMul.hMul Complex Complex Complex qz61 qz110 (@HAdd.hAdd Complex Complex Complex qz4 qz111 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz69 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz69 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz112 (@HMul.hMul Nat Nat Nat qz69 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz113 qz114 (@HSub.hSub Nat Nat Nat qz112 (@HMul.hMul Nat Nat Nat qz69 2 k) 1)))))) Bool.false 531185917809 274877906944 6925005157199 1190290056544256

noncomputable def ep403 := nat_lit 146001767486089288541554309

noncomputable def ep404 := nat_lit 8264781126451706020842507829

noncomputable def ep405 := nat_lit 7844180919965848678311981

noncomputable def ep406 := nat_lit 4125994659618458973122483101

noncomputable def ep407 := nat_lit 649768392680123836873310314859860066304

noncomputable def ep408 := nat_lit 51316418707199629902270164175362719744

noncomputable def ep409 := @ep402 Bool.false 92302843169 1099511627776 110741168753773 19044640904708096 Bool.true ep403 ep265 ep404 ep267 Bool.true ep405 ep398 ep406 ep400 Bool.false ep407 ep264 ep265 ep266 ep267 Bool.false ep408 ep397 ep398

noncomputable def ep410 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 23, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz7) (BSN.headSumC qz5 23) Bool.false 531185917809 274877906944 6925005157199 1190290056544256 Bool.false 92302843169 1099511627776 110741168753773

noncomputable abbrev qz115 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 22) qz276)

noncomputable def ep411 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 23) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 22) qz115) Bool.false 531185917809 274877906944 6925005157199 1190290056544256 Bool.false 92302843169 1099511627776 110741168753773 19044640904708096

noncomputable def ep412 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 22) qz115 Bool.false 2133783198531 1099511627776 107443818813011 19044640904708096 Bool.true 141939287203 1099511627776 107367456551719 19044640904708096 Bool.true

noncomputable def ep413 := nat_lit 2336180372567448549851136

noncomputable abbrev qz116 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 21) qz276)

noncomputable def ep414 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 22) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 21) qz116) Bool.false 2133783198531 1099511627776 107443818813011 19044640904708096 Bool.true 141939287203 1099511627776 107367456551719 19044640904708096

noncomputable def ep415 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 21) qz116 Bool.false 1935411263975 1099511627776 103983204646447 19044640904708096 Bool.true 276907355685 1099511627776 103916441440861 19044640904708096 Bool.false

noncomputable abbrev qz117 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 20) qz276)

noncomputable def ep416 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 21) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 20) qz117) Bool.false 1935411263975 1099511627776 103983204646447 19044640904708096 Bool.true 276907355685 1099511627776 103916441440861 19044640904708096

noncomputable def ep417 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 20) qz117 Bool.false 1692588602443 1099511627776 100449977403559 19044640904708096 Bool.true 238391601993 1099511627776 100398307024533 19044640904708096 Bool.false

noncomputable abbrev qz118 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 19) qz276)

noncomputable def ep418 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 20) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 19) qz118) Bool.false 1692588602443 1099511627776 100449977403559 19044640904708096 Bool.true 238391601993 1099511627776 100398307024533 19044640904708096

noncomputable def ep419 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 19) qz118 Bool.false 1488545496407 1099511627776 96824525527915 19044640904708096 Bool.true 45044812321 549755813888 24194217171101 4761160226177024 Bool.false

noncomputable abbrev qz119 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 18) qz276)

noncomputable def ep420 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 19) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 18) qz119) Bool.false 1488545496407 1099511627776 96824525527915 19044640904708096 Bool.true 45044812321 549755813888 24194217171101 4761160226177024

noncomputable def ep421 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 18) qz119 Bool.false 326315752669 274877906944 46550987897571 9522320452354048 Bool.false 46565165943 549755813888 23263580833461 4761160226177024 Bool.false

noncomputable abbrev qz120 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 17) qz276)

noncomputable def ep422 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 18) (@HAdd.hAdd Complex Complex Complex qz4 qz37 qz120) Bool.false 326315752669 274877906944 46550987897571 9522320452354048 Bool.false 46565165943 549755813888 23263580833461 4761160226177024

noncomputable def ep423 := @Enclosure.Complex.IsNear.addLitP qz37 qz120 Bool.false 1083916429507 1099511627776 89269635227647 19044640904708096 Bool.false 60463601213 274877906944 22306732233447 4761160226177024 Bool.false

noncomputable def ep424 := nat_lit 1435151857544171226136576

noncomputable abbrev qz393 := (@Nat.cast Real Real.instNatCast 17)

noncomputable abbrev qz121 := (@Inv.inv Real Real.instInv (Real.sqrt qz393))

noncomputable abbrev qz561 := (Real.log (Enclosure.sfrac Bool.false 17 1))

noncomputable abbrev qz122 := (@HMul.hMul Real Real Real qz268 qz285 qz561)

noncomputable def ep425 := @Enclosure.Complex.IsNear.of_eq qz120 (Complex.mk (@HMul.hMul Real Real Real qz0 qz121 (Real.cos qz122)) (@HMul.hMul Real Real Real qz0 qz121 (@Neg.neg Real Real.instNeg (Real.sin qz122)))) Bool.false 221346581169 1099511627776 3832340567495 19044640904708096 Bool.true 74362036483 549755813888 478424300007 2380580113088512 (BSN.cpow_neg_s_mk qz13 113311 1000 17 qz14 rfl)

noncomputable abbrev qz394 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 17) qz15)

noncomputable def ep426 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz393) 4323389 1048576 1 1048576 127158 127159 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz393) (Real.sqrt qz394) Bool.false 4323389 1048576 1 1048576 (BSN.sqrt_natCast_div_one 17) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz394) Bool.false 4323389 1048576 1 1048576 4323389 1048576 1 1048576 (BSN.sqrt_enclosure 17 1 2161694 2161695 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep427 := BSN.log_dyadic_bound 1 33 2 1 3267 524288 138568 1 1 31784 34 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1) (BSN.artanhQ 33) 0 1 1 3267 1 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep428 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz561 113311 1000 0 1 3189913004350711 1125899906842624 31250000017321 4330250000000000000 361452232435983414121 1125899906842624000 3540968751962659831 4330250000000000000000 qz18 (BSN.isNear_log_sfrac 17 1 3189913004350711 1125899906842624 31250000017321 4330250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz394) Bool.false 53517859495200818200576 18889465931478580854784 1000000000554272 138568000000000000000 3189913004350711 1125899906842624 31250000017321 4330250000000000000 (BSN.log_rat_reduce_isNear 17 1 4 34 32 31784 524288 24973259072661432 36028797018963968 138568 1000000000000000 rfl rfl rfl rfl (ep427 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep429 := nat_lit 2605520764947415402911536424596727441

noncomputable def ep430 := BSN.cos_dyadic_bound_f 1270496973 2147483648 2 1 1048576 277407 ep429 ep71 ep429 ep429 ep72 ep429 870357 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1270496973) qz288 0 1 ep429 ep71 ep429 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1270496973) qz289 0 1 ep429 ep72 ep429 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz395 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 336628623) qz16)

noncomputable def ep431 := @Enclosure.Real.IsNear.cos_image qz122 qz395 Bool.false 336628623 1048576 859 1048576 Bool.false 870357 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz122 Bool.false 361452232435983414121 1125899906842624000 3540968751962659831 4330250000000000000000 336628623 1048576 859 1048576 (ep428 rfl) rfl) (Enclosure.sfrac_false_div 336628623 1048576) (BSN.cos_reduce0 qz395 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 89403276498066720423936) qz19) 226375608064910080 72057594037927936 Bool.false 870357 1048576 51 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q0 336628623 1048576 226375608064910080 72057594037927936 51 89403276498066720423936 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 870357 1048576 89403276498066720423936 151115727451828646838272 1270496973 2147483648 277407 277136 (ep430 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep432 := BSN.sin_dyadic_bound_f 1270496973 2147483648 2 1 1048576 277407 ep429 ep67 ep429 ep429 ep68 ep429 584798 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1270496973) qz292 0 1 ep429 ep67 ep429 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1270496973) qz293 0 1 ep429 ep68 ep429 rfl rfl rfl rfl) rfl rfl

noncomputable def ep433 := @Enclosure.Real.IsNear.sin_image qz122 qz395 Bool.false 336628623 1048576 859 1048576 Bool.false 584798 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz122 Bool.false 361452232435983414121 1125899906842624000 3540968751962659831 4330250000000000000000 336628623 1048576 859 1048576 (ep428 rfl) rfl) (Enclosure.sfrac_false_div 336628623 1048576) (BSN.sin_reduce0 qz395 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 89403276498066720423936) qz19) 226375608064910080 72057594037927936 Bool.false 584798 1048576 51 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q0 336628623 1048576 226375608064910080 72057594037927936 51 89403276498066720423936 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 584798 1048576 89403276498066720423936 151115727451828646838272 1270496973 2147483648 277407 277136 (ep432 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz396 := (@Enclosure.Real.IsNear.recentre' qz121 Bool.false 254317 1048576 1 1048576 254317 1048576 1 1048576 (ep426 rfl rfl) rfl)

noncomputable def ep434 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz121 (Real.cos qz122)) (@HMul.hMul Real Real Real qz0 qz121 (@Neg.neg Real Real.instNeg (Real.sin qz122))) Bool.false 221346581169 1099511627776 3832340567495 19044640904708096 Bool.true 74362036483 549755813888 478424300007 2380580113088512 (@Enclosure.Real.IsNear.mulLit_ff qz121 (Real.cos qz122) 254317 1048576 1 1048576 870357 1048576 15009811 18162384896 221346581169 1099511627776 3832340567495 19044640904708096 qz396 (@Enclosure.Real.IsNear.recentre' (Real.cos qz122) Bool.false 870357 1048576 120078488 145299079168 870357 1048576 15009811 18162384896 (ep431 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz121 (@Neg.neg Real Real.instNeg (Real.sin qz122)) 254317 1048576 1 1048576 292399 524288 15009811 18162384896 74362036483 549755813888 478424300007 2380580113088512 qz396 (@Enclosure.Real.IsNear.neg (Real.sin qz122) Bool.false 292399 524288 15009811 18162384896 (@Enclosure.Real.IsNear.recentre' (Real.sin qz122) Bool.false 584798 1048576 120078488 145299079168 292399 524288 15009811 18162384896 (ep433 rfl rfl) rfl)) rfl)

noncomputable def ep435 := @ep423 221346581169 1099511627776 3832340567495 19044640904708096 Bool.true 74362036483 549755813888 478424300007 2380580113088512 Bool.false ep424 326315752669 274877906944 46550987897571 9522320452354048 Bool.false 12799735350911872008192 46565165943 549755813888 23263580833461 4761160226177024 EMRow36.d7 (ep425 ep434) rfl rfl

noncomputable abbrev qz397 := (@Nat.cast Real Real.instNatCast 18)

noncomputable abbrev qz123 := (@Inv.inv Real Real.instInv (Real.sqrt qz397))

noncomputable abbrev qz562 := (Real.log (Enclosure.sfrac Bool.false 18 1))

noncomputable abbrev qz124 := (@HMul.hMul Real Real Real qz268 qz285 qz562)

noncomputable def ep436 := @Enclosure.Complex.IsNear.of_eq qz119 (Complex.mk (@HMul.hMul Real Real Real qz0 qz123 (Real.cos qz124)) (@HMul.hMul Real Real Real qz0 qz123 (@Neg.neg Real Real.instNeg (Real.sin qz124)))) Bool.false 183282485731 1099511627776 3722549732773 19044640904708096 Bool.true 11451247283 68719476736 116329542205 595145028272128 (BSN.cpow_neg_s_mk qz13 113311 1000 18 qz14 rfl)

noncomputable abbrev qz398 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 18) qz15)

noncomputable def ep437 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz397) 4448731 1048576 1 1048576 123575 123576 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz397) (Real.sqrt qz398) Bool.false 4448731 1048576 1 1048576 (BSN.sqrt_natCast_div_one 18) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz398) Bool.false 4448731 1048576 1 1048576 4448731 1048576 1 1048576 (BSN.sqrt_enclosure 18 1 2224365 2224366 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep438 := BSN.log_dyadic_bound 2 34 2 1 3468 524288 138568 4 4 61752 36 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 2) (BSN.artanhQ 34) 0 1 4 3468 4 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep439 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz562 113311 1000 0 1 3254268794313975 1125899906842624 31250000017321 4330250000000000000 14749778054100432849 45035996273704960 3540968751962659831 4330250000000000000000 qz18 (BSN.isNear_log_sfrac 18 1 3254268794313975 1125899906842624 31250000017321 4330250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz398) Bool.false 54597570484265130393600 18889465931478580854784 1000000000554272 138568000000000000000 3254268794313975 1125899906842624 31250000017321 4330250000000000000 (BSN.log_rat_reduce_isNear 18 1 4 36 32 61752 524288 24973259072661432 36028797018963968 138568 1000000000000000 rfl rfl rfl rfl (ep438 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep440 := nat_lit 288953594838744179471506737686975550682799418078058091408109010536733291380736

noncomputable def ep441 := nat_lit 65373566921604362091701526445461262173196433968900515610183018462964678656

noncomputable def ep442 := nat_lit 866730037382389329690336810008035729524051861366236473193106665573273944784896

noncomputable def ep443 := BSN.cos_dyadic_bound_f 1686262852 2147483648 3 2 1048576 277407 ep440 ep155 ep441 ep442 ep158 ep441 741581 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1686262852) qz288 0 2 ep440 ep155 ep441 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1686262852) qz289 0 2 ep442 ep158 ep441 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz399 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 343420031) qz16)

noncomputable def ep444 := @Enclosure.Real.IsNear.cos_image qz124 qz399 Bool.false 343420031 1048576 859 1048576 Bool.false 741581 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz124 Bool.false 14749778054100432849 45035996273704960 3540968751962659831 4330250000000000000000 343420031 1048576 859 1048576 (ep439 rfl) rfl) (Enclosure.sfrac_false_div 343420031 1048576) (BSN.cos_reduce0 qz399 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 118660199308854288187392) qz19) 226375608064910080 72057594037927936 Bool.false 741581 1048576 52 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q0 343420031 1048576 226375608064910080 72057594037927936 52 118660199308854288187392 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 741581 1048576 118660199308854288187392 151115727451828646838272 1686262852 2147483648 277407 277136 (ep443 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep445 := nat_lit 8085392193431581590349903251522601216

noncomputable def ep446 := BSN.sin_dyadic_bound_f 1686262852 2147483648 2 1 1048576 277407 ep445 ep67 ep445 ep445 ep68 ep445 741328 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1686262852) qz292 0 1 ep445 ep67 ep445 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1686262852) qz293 0 1 ep445 ep68 ep445 rfl rfl rfl rfl) rfl rfl

noncomputable def ep447 := @Enclosure.Real.IsNear.sin_image qz124 qz399 Bool.false 343420031 1048576 859 1048576 Bool.false 741328 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz124 Bool.false 14749778054100432849 45035996273704960 3540968751962659831 4330250000000000000000 343420031 1048576 859 1048576 (ep439 rfl) rfl) (Enclosure.sfrac_false_div 343420031 1048576) (BSN.sin_reduce0 qz399 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 118660199308854288187392) qz19) 226375608064910080 72057594037927936 Bool.false 741328 1048576 52 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q0 343420031 1048576 226375608064910080 72057594037927936 52 118660199308854288187392 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 741328 1048576 118660199308854288187392 151115727451828646838272 1686262852 2147483648 277407 277136 (ep446 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz400 := (@Enclosure.Real.IsNear.recentre' qz123 Bool.false 247151 1048576 1 1048576 247151 1048576 1 1048576 (ep437 rfl rfl) rfl)

noncomputable def ep448 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz123 (Real.cos qz124)) (@HMul.hMul Real Real Real qz0 qz123 (@Neg.neg Real Real.instNeg (Real.sin qz124))) Bool.false 183282485731 1099511627776 3722549732773 19044640904708096 Bool.true 11451247283 68719476736 116329542205 595145028272128 (@Enclosure.Real.IsNear.mulLit_ff qz123 (Real.cos qz124) 247151 1048576 1 1048576 741581 1048576 15009811 18162384896 183282485731 1099511627776 3722549732773 19044640904708096 qz400 (@Enclosure.Real.IsNear.recentre' (Real.cos qz124) Bool.false 741581 1048576 120078488 145299079168 741581 1048576 15009811 18162384896 (ep444 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz123 (@Neg.neg Real Real.instNeg (Real.sin qz124)) 247151 1048576 1 1048576 46333 65536 15009811 18162384896 11451247283 68719476736 116329542205 595145028272128 qz400 (@Enclosure.Real.IsNear.neg (Real.sin qz124) Bool.false 46333 65536 15009811 18162384896 (@Enclosure.Real.IsNear.recentre' (Real.sin qz124) Bool.false 741328 1048576 120078488 145299079168 46333 65536 15009811 18162384896 (ep447 rfl rfl) rfl)) rfl)

noncomputable def ep449 := @ep421 183282485731 1099511627776 3722549732773 19044640904708096 Bool.true 11451247283 68719476736 116329542205 595145028272128 Bool.false 409168270443273632350208 1488545496407 1099511627776 96824525527915 19044640904708096 Bool.true 3095455932370445664256 45044812321 549755813888 24194217171101 4761160226177024 (ep422 (BSN.head_sum_c_succ qz5 17 18 rfl rfl) (ep435 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep436 ep448) rfl rfl

noncomputable abbrev qz401 := (@Nat.cast Real Real.instNatCast 19)

noncomputable abbrev qz125 := (@Inv.inv Real Real.instInv (Real.sqrt qz401))

noncomputable abbrev qz563 := (Real.log (Enclosure.sfrac Bool.false 19 1))

noncomputable abbrev qz126 := (@HMul.hMul Real Real Real qz268 qz285 qz563)

noncomputable def ep450 := @Enclosure.Complex.IsNear.of_eq qz118 (Complex.mk (@HMul.hMul Real Real Real qz0 qz125 (Real.cos qz126)) (@HMul.hMul Real Real Real qz0 qz125 (@Neg.neg Real Real.instNeg (Real.sin qz126)))) Bool.false 51010776509 274877906944 906362968911 4761160226177024 Bool.true 148301977351 1099511627776 3621438340129 19044640904708096 (BSN.cpow_neg_s_mk qz13 113311 1000 19 qz14 rfl)

noncomputable abbrev qz402 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 19) qz15)

noncomputable def ep451 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz401) 4570637 1048576 1 1048576 120279 120280 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz401) (Real.sqrt qz402) Bool.false 4570637 1048576 1 1048576 (BSN.sqrt_natCast_div_one 19) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz402) Bool.false 4570637 1048576 1 1048576 4570637 1048576 1 1048576 (BSN.sqrt_enclosure 19 1 2285318 2285319 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep452 := BSN.log_dyadic_bound 3 35 3 2 22509375 524288 138568 55368 243 90099 38 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 3) (BSN.artanhQ 35) 0 2 55368 22509375 243 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep453 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz563 113311 1000 0 1 3315143513283831 1125899906842624 31250000017321 4330250000000000000 375642226633704174441 1125899906842624000 3540968751962659831 4330250000000000000000 qz18 (BSN.isNear_log_sfrac 19 1 3315143513283831 1125899906842624 31250000017321 4330250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz402) Bool.false 55618878793361701994496 18889465931478580854784 1000000000554272 138568000000000000000 3315143513283831 1125899906842624 31250000017321 4330250000000000000 (BSN.log_rat_reduce_isNear 19 1 4 38 32 90099 524288 24973259072661432 36028797018963968 138568 1000000000000000 rfl rfl rfl rfl (ep452 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep454 := nat_lit 3318434209277067587579671385817760000

noncomputable def ep455 := BSN.cos_dyadic_bound_f 1349687740 2147483648 2 1 1048576 277407 ep454 ep71 ep454 ep454 ep72 ep454 848204 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1349687740) qz288 0 1 ep454 ep71 ep454 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1349687740) qz289 0 1 ep454 ep72 ep454 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz403 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 349844085) qz16)

noncomputable def ep456 := @Enclosure.Real.IsNear.cos_image qz126 qz403 Bool.false 349844085 1048576 859 1048576 Bool.false 848204 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz126 Bool.false 375642226633704174441 1125899906842624000 3540968751962659831 4330250000000000000000 349844085 1048576 859 1048576 (ep453 rfl) rfl) (Enclosure.sfrac_false_div 349844085 1048576) (BSN.cos_reduce0 qz403 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 94975831319223897948160) qz19) 226375608064910080 72057594037927936 Bool.false 848204 1048576 53 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q0 349844085 1048576 226375608064910080 72057594037927936 53 94975831319223897948160 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 848204 1048576 94975831319223897948160 151115727451828646838272 1349687740 2147483648 277407 277136 (ep455 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep457 := BSN.sin_dyadic_bound_f 1349687740 2147483648 2 1 1048576 277407 ep454 ep67 ep454 ep454 ep68 ep454 616489 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1349687740) qz292 0 1 ep454 ep67 ep454 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1349687740) qz293 0 1 ep454 ep68 ep454 rfl rfl rfl rfl) rfl rfl

noncomputable def ep458 := @Enclosure.Real.IsNear.sin_image qz126 qz403 Bool.false 349844085 1048576 859 1048576 Bool.false 616489 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz126 Bool.false 375642226633704174441 1125899906842624000 3540968751962659831 4330250000000000000000 349844085 1048576 859 1048576 (ep453 rfl) rfl) (Enclosure.sfrac_false_div 349844085 1048576) (BSN.sin_reduce0 qz403 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 94975831319223897948160) qz19) 226375608064910080 72057594037927936 Bool.false 616489 1048576 53 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q0 349844085 1048576 226375608064910080 72057594037927936 53 94975831319223897948160 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 616489 1048576 94975831319223897948160 151115727451828646838272 1349687740 2147483648 277407 277136 (ep457 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz404 := (@Enclosure.Real.IsNear.recentre' qz125 Bool.false 240559 1048576 1 1048576 240559 1048576 1 1048576 (ep451 rfl rfl) rfl)

noncomputable def ep459 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz125 (Real.cos qz126)) (@HMul.hMul Real Real Real qz0 qz125 (@Neg.neg Real Real.instNeg (Real.sin qz126))) Bool.false 51010776509 274877906944 906362968911 4761160226177024 Bool.true 148301977351 1099511627776 3621438340129 19044640904708096 (@Enclosure.Real.IsNear.mulLit_ff qz125 (Real.cos qz126) 240559 1048576 1 1048576 212051 262144 15009811 18162384896 51010776509 274877906944 906362968911 4761160226177024 qz404 (@Enclosure.Real.IsNear.recentre' (Real.cos qz126) Bool.false 848204 1048576 120078488 145299079168 212051 262144 15009811 18162384896 (ep456 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz125 (@Neg.neg Real Real.instNeg (Real.sin qz126)) 240559 1048576 1 1048576 616489 1048576 15009811 18162384896 148301977351 1099511627776 3621438340129 19044640904708096 qz404 (@Enclosure.Real.IsNear.neg (Real.sin qz126) Bool.false 616489 1048576 15009811 18162384896 (@Enclosure.Real.IsNear.recentre' (Real.sin qz126) Bool.false 616489 1048576 120078488 145299079168 616489 1048576 15009811 18162384896 (ep458 rfl rfl) rfl)) rfl)

noncomputable def ep460 := @ep419 51010776509 274877906944 906362968911 4761160226177024 Bool.true 148301977351 1099511627776 3621438340129 19044640904708096 Bool.false 465255212356801965064192 1692588602443 1099511627776 100449977403559 19044640904708096 Bool.true 131057169177725877878784 238391601993 1099511627776 100398307024533 19044640904708096 (ep420 (BSN.head_sum_c_succ qz5 18 19 rfl rfl) (ep449 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep450 ep459) rfl rfl

noncomputable abbrev qz405 := (@Nat.cast Real Real.instNatCast 20)

noncomputable abbrev qz127 := (@Inv.inv Real Real.instInv (Real.sqrt qz405))

noncomputable abbrev qz564 := (Real.log (Enclosure.sfrac Bool.false 20 1))

noncomputable abbrev qz128 := (@HMul.hMul Real Real Real qz268 qz285 qz564)

noncomputable def ep461 := @Enclosure.Complex.IsNear.of_eq qz117 (Complex.mk (@HMul.hMul Real Real Real qz0 qz127 (Real.cos qz128)) (@HMul.hMul Real Real Real qz0 qz127 (@Neg.neg Real Real.instNeg (Real.sin qz128)))) Bool.false 60705665383 274877906944 441653405361 2380580113088512 Bool.true 9628938423 274877906944 439766802041 2380580113088512 (BSN.cpow_neg_s_mk qz13 113311 1000 20 qz14 rfl)

noncomputable abbrev qz406 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 20) qz15)

noncomputable def ep462 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz405) 4689375 1048576 1 1048576 117234 117235 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz405) (Real.sqrt qz406) Bool.false 4689375 1048576 1 1048576 (BSN.sqrt_natCast_div_one 20) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz406) Bool.false 4689375 1048576 1 1048576 4689375 1048576 1 1048576 (BSN.sqrt_enclosure 20 1 2344687 2344688 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep463 := BSN.log_dyadic_bound 4 36 3 2 25194240 524288 138568 104448 768 116991 40 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 4) (BSN.artanhQ 36) 0 2 104448 25194240 768 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep464 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz564 113311 1000 0 1 3372893643545847 1125899906842624 31250000017321 4330250000000000000 382185951643823469417 1125899906842624000 3540968751962659831 4330250000000000000000 qz18 (BSN.isNear_log_sfrac 20 1 3372893643545847 1125899906842624 31250000017321 4330250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz406) Bool.false 56587765202795681021952 18889465931478580854784 1000000000554272 138568000000000000000 3372893643545847 1125899906842624 31250000017321 4330250000000000000 (BSN.log_rat_reduce_isNear 20 1 4 40 32 116991 524288 24973259072661432 36028797018963968 138568 1000000000000000 rfl rfl rfl rfl (ep463 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep465 := nat_lit 13023193787177233728392503921307281

noncomputable def ep466 := BSN.cos_dyadic_bound_f 337815347 2147483648 2 1 1048576 277407 ep465 ep71 ep465 ep465 ep72 ep465 1035628 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 337815347) qz288 0 1 ep465 ep71 ep465 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 337815347) qz289 0 1 ep465 ep72 ep465 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz407 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 88984601) qz543)

noncomputable def ep467 := @Enclosure.Real.IsNear.cos_image qz128 qz407 Bool.false 88984601 262144 429 524288 Bool.false 1035628 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz128 Bool.false 382185951643823469417 1125899906842624000 3540968751962659831 4330250000000000000000 88984601 262144 429 524288 (ep464 rfl) rfl) (Enclosure.sfrac_false_div 88984601 262144) (BSN.cos_reduce0 qz407 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 5942910447350292938752) qz319) 226375608064910080 72057594037927936 Bool.false 1035628 1048576 54 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q0 88984601 262144 226375608064910080 72057594037927936 54 5942910447350292938752 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1035628 1048576 5942910447350292938752 37778931862957161709568 337815347 2147483648 277407 277136 (ep466 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep468 := BSN.sin_dyadic_bound_f 337815347 2147483648 1 0 1048576 277407 0 1 1 0 1 1 164268 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 337815347) qz292 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 337815347) qz293 0 0 rfl) rfl rfl

noncomputable def ep469 := @Enclosure.Real.IsNear.sin_image qz128 qz407 Bool.false 88984601 262144 429 524288 Bool.false 164268 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz128 Bool.false 382185951643823469417 1125899906842624000 3540968751962659831 4330250000000000000000 88984601 262144 429 524288 (ep464 rfl) rfl) (Enclosure.sfrac_false_div 88984601 262144) (BSN.sin_reduce0 qz407 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 5942910447350292938752) qz319) 226375608064910080 72057594037927936 Bool.false 164268 1048576 54 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q0 88984601 262144 226375608064910080 72057594037927936 54 5942910447350292938752 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 164268 1048576 5942910447350292938752 37778931862957161709568 337815347 2147483648 277407 277136 (ep468 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz408 := (@Enclosure.Real.IsNear.recentre' qz127 Bool.false 234469 1048576 1 1048576 234469 1048576 1 1048576 (ep462 rfl rfl) rfl)

noncomputable def ep470 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz127 (Real.cos qz128)) (@HMul.hMul Real Real Real qz0 qz127 (@Neg.neg Real Real.instNeg (Real.sin qz128))) Bool.false 60705665383 274877906944 441653405361 2380580113088512 Bool.true 9628938423 274877906944 439766802041 2380580113088512 (@Enclosure.Real.IsNear.mulLit_ff qz127 (Real.cos qz128) 234469 1048576 1 1048576 258907 262144 7496245 9081192448 60705665383 274877906944 441653405361 2380580113088512 qz408 (@Enclosure.Real.IsNear.recentre' (Real.cos qz128) Bool.false 1035628 1048576 59969960 72649539584 258907 262144 7496245 9081192448 (ep467 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz127 (@Neg.neg Real Real.instNeg (Real.sin qz128)) 234469 1048576 1 1048576 41067 262144 7496245 9081192448 9628938423 274877906944 439766802041 2380580113088512 qz408 (@Enclosure.Real.IsNear.neg (Real.sin qz128) Bool.false 41067 262144 7496245 9081192448 (@Enclosure.Real.IsNear.recentre' (Real.sin qz128) Bool.false 164268 1048576 59969960 72649539584 41067 262144 7496245 9081192448 (ep469 rfl rfl) rfl)) rfl)

noncomputable def ep471 := @ep417 60705665383 274877906944 441653405361 2380580113088512 Bool.true 9628938423 274877906944 439766802041 2380580113088512 Bool.false 532001797317289469542400 1935411263975 1099511627776 103983204646447 19044640904708096 Bool.true 76115714348090539376640 276907355685 1099511627776 103916441440861 19044640904708096 (ep418 (BSN.head_sum_c_succ qz5 19 20 rfl rfl) (ep460 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep461 ep470) rfl rfl

noncomputable abbrev qz409 := (@Nat.cast Real Real.instNatCast 21)

noncomputable abbrev qz129 := (@Inv.inv Real Real.instInv (Real.sqrt qz409))

noncomputable abbrev qz565 := (Real.log (Enclosure.sfrac Bool.false 21 1))

noncomputable abbrev qz130 := (@HMul.hMul Real Real Real qz268 qz285 qz565)

noncomputable def ep472 := @Enclosure.Complex.IsNear.of_eq qz116 (Complex.mk (@HMul.hMul Real Real Real qz0 qz129 (Real.cos qz130)) (@HMul.hMul Real Real Real qz0 qz129 (@Neg.neg Real Real.instNeg (Real.sin qz130)))) Bool.false 49592983639 274877906944 865153541641 4761160226177024 Bool.false 67484034241 549755813888 1725507555429 9522320452354048 (BSN.cpow_neg_s_mk qz13 113311 1000 21 qz14 rfl)

noncomputable abbrev qz410 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 21) qz15)

noncomputable def ep473 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz409) 4805179 1048576 1 1048576 114408 114410 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz409) (Real.sqrt qz410) Bool.false 4805179 1048576 1 1048576 (BSN.sqrt_natCast_div_one 21) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz410) Bool.false 4805179 1048576 1 1048576 4805179 1048576 1 1048576 (BSN.sqrt_enclosure 21 1 2402589 2402590 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep474 := BSN.log_dyadic_bound 5 37 3 2 28112415 524288 138568 173000 1875 142571 42 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 5) (BSN.artanhQ 37) 0 2 173000 28112415 1875 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep475 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz565 113311 1000 0 1 3427826275261687 1125899906842624 31250000017321 4330250000000000000 388410423076177015657 1125899906842624000 3540968751962659831 4330250000000000000000 qz18 (BSN.isNear_log_sfrac 21 1 3427826275261687 1125899906842624 31250000017321 4330250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz410) Bool.false 57509381830540779323392 18889465931478580854784 1000000000554272 138568000000000000000 3427826275261687 1125899906842624 31250000017321 4330250000000000000 (BSN.log_rat_reduce_isNear 21 1 4 42 32 142571 524288 24973259072661432 36028797018963968 138568 1000000000000000 rfl rfl rfl rfl (ep474 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep476 := nat_lit 1228127756247910564606606110403175100003840831947853200583460762715446765875745

noncomputable def ep477 := nat_lit 364440645791911122190587106397846100994023610038354376008668137606409548321

noncomputable def ep478 := nat_lit 3215935029127531241676612195740814463465592807351934380157430820603378771358241

noncomputable def ep479 := BSN.sin_dyadic_bound_f 2090274637 2147483648 3 2 1048576 277407 ep476 ep187 ep477 ep478 ep189 ep477 866942 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2090274637) qz292 0 2 ep476 ep187 ep477 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2090274637) qz293 0 2 ep478 ep189 ep477 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz411 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 361735395) qz16)

noncomputable def ep480 := @Enclosure.Real.IsNear.cos_image qz130 qz411 Bool.false 361735395 1048576 429 524288 Bool.false 866942 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz130 Bool.false 388410423076177015657 1125899906842624000 3540968751962659831 4330250000000000000000 361735395 1048576 429 524288 (ep475 rfl) rfl) (Enclosure.sfrac_false_div 361735395 1048576) (BSN.cos_reduce3 qz411 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 147090001221631522897920) qz19) 226375608064910080 72057594037927936 Bool.false 866942 1048576 54 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q3 361735395 1048576 226375608064910080 72057594037927936 54 147090001221631522897920 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 866942 1048576 147090001221631522897920 151115727451828646838272 2090274637 2147483648 277407 277136 (ep479 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep481 := nat_lit 682455171535857829724643655604607431602575583797713268935704276236406607508001

noncomputable def ep482 := nat_lit 2046636633315989666929549792601026602605738704173063098055095492434007003427361

noncomputable def ep483 := BSN.cos_dyadic_bound_f 2090274637 2147483648 3 2 1048576 277407 ep481 ep155 ep477 ep482 ep158 ep477 589849 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2090274637) qz288 0 2 ep481 ep155 ep477 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2090274637) qz289 0 2 ep482 ep158 ep477 rfl rfl rfl rfl) rfl rfl

noncomputable def ep484 := @Enclosure.Real.IsNear.sin_image qz130 qz411 Bool.false 361735395 1048576 429 524288 Bool.true 589849 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz130 Bool.false 388410423076177015657 1125899906842624000 3540968751962659831 4330250000000000000000 361735395 1048576 429 524288 (ep475 rfl) rfl) (Enclosure.sfrac_false_div 361735395 1048576) (BSN.sin_reduce3 qz411 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 147090001221631522897920) qz19) 226375608064910080 72057594037927936 Bool.false 589849 1048576 54 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q3 361735395 1048576 226375608064910080 72057594037927936 54 147090001221631522897920 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 589849 1048576 147090001221631522897920 151115727451828646838272 2090274637 2147483648 277407 277136 (ep483 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz412 := (@Enclosure.Real.IsNear.recentre' qz129 Bool.false 228818 1048576 2 1048576 114409 524288 1 524288 (ep473 rfl rfl) rfl)

noncomputable def ep485 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz129 (Real.cos qz130)) (@HMul.hMul Real Real Real qz0 qz129 (@Neg.neg Real Real.instNeg (Real.sin qz130))) Bool.false 49592983639 274877906944 865153541641 4761160226177024 Bool.false 67484034241 549755813888 1725507555429 9522320452354048 (@Enclosure.Real.IsNear.mulLit_ff qz129 (Real.cos qz130) 114409 524288 1 524288 433471 524288 7496245 9081192448 49592983639 274877906944 865153541641 4761160226177024 qz412 (@Enclosure.Real.IsNear.recentre' (Real.cos qz130) Bool.false 866942 1048576 59969960 72649539584 433471 524288 7496245 9081192448 (ep480 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz129 (@Neg.neg Real Real.instNeg (Real.sin qz130)) 114409 524288 1 524288 589849 1048576 7496245 9081192448 67484034241 549755813888 1725507555429 9522320452354048 qz412 (@Enclosure.Real.IsNear.neg (Real.sin qz130) Bool.true 589849 1048576 7496245 9081192448 (@Enclosure.Real.IsNear.recentre' (Real.sin qz130) Bool.true 589849 1048576 59969960 72649539584 589849 1048576 7496245 9081192448 (ep484 rfl rfl) rfl)) rfl)

noncomputable def ep486 := @ep415 49592983639 274877906944 865153541641 4761160226177024 Bool.false 67484034241 549755813888 1725507555429 9522320452354048 Bool.false 586529859484474895499264 2133783198531 1099511627776 107443818813011 19044640904708096 Bool.true 78031948358967848075264 141939287203 1099511627776 107367456551719 19044640904708096 (ep416 (BSN.head_sum_c_succ qz5 20 21 rfl rfl) (ep471 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep472 ep485) rfl rfl

noncomputable abbrev qz413 := (@Nat.cast Real Real.instNatCast 22)

noncomputable abbrev qz131 := (@Inv.inv Real Real.instInv (Real.sqrt qz413))

noncomputable abbrev qz566 := (Real.log (Enclosure.sfrac Bool.false 22 1))

noncomputable abbrev qz132 := (@HMul.hMul Real Real Real qz268 qz285 qz566)

noncomputable def ep487 := @Enclosure.Complex.IsNear.of_eq qz115 (Complex.mk (@HMul.hMul Real Real Real qz0 qz131 (Real.cos qz132)) (@HMul.hMul Real Real Real qz0 qz131 (@Neg.neg Real Real.instNeg (Real.sin qz132)))) Bool.true 9039527295 1099511627776 3356263702173 19044640904708096 Bool.false 58560532593 274877906944 1686856101027 9522320452354048 (BSN.cpow_neg_s_mk qz13 113311 1000 22 qz14 rfl)

noncomputable abbrev qz414 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 22) qz15)

noncomputable def ep488 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz413) 4918257 1048576 1 1048576 111778 111779 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz413) (Real.sqrt qz414) Bool.false 4918257 1048576 1 1048576 (BSN.sqrt_natCast_div_one 22) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz414) Bool.false 4918257 1048576 1 1048576 4918257 1048576 1 1048576 (BSN.sqrt_enclosure 22 1 2459128 2459129 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep489 := BSN.log_dyadic_bound 6 38 4 3 316148320320 524288 138568 2667271104 699840 166961 44 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 6) (BSN.artanhQ 38) 0 3 2667271104 316148320320 699840 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep490 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz566 113311 1000 0 1 3480203401436407 1125899906842624 31250000017321 4330250000000000000 394345327620160713577 1125899906842624000 3540968751962659831 4330250000000000000000 qz18 (BSN.isNear_log_sfrac 22 1 3480203401436407 1125899906842624 31250000017321 4330250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz414) Bool.false 58388124189833310502912 18889465931478580854784 1000000000554272 138568000000000000000 3480203401436407 1125899906842624 31250000017321 4330250000000000000 (BSN.log_rat_reduce_isNear 22 1 4 44 32 166961 524288 24973259072661432 36028797018963968 138568 1000000000000000 rfl rfl rfl rfl (ep489 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep491 := nat_lit 4202042244989817360300816679233733328001041644089507679582972195422805694976961

noncomputable def ep492 := nat_lit 13740999814019860674872641468537334976667479382720354295005345037926978130881

noncomputable def ep493 := nat_lit 12578644735341412359552704754764125314049789973503082330158905896192563128669121

noncomputable def ep494 := BSN.cos_dyadic_bound_f 3290427239 2147483648 3 2 1048576 277407 ep491 ep155 ep492 ep493 ep158 ep492 40435 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3290427239) qz288 0 2 ep491 ep155 ep492 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3290427239) qz289 0 2 ep493 ep158 ep492 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz415 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 367262705) qz16)

noncomputable def ep495 := @Enclosure.Real.IsNear.cos_image qz132 qz415 Bool.false 367262705 1048576 859 1048576 Bool.true 40435 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz132 Bool.false 394345327620160713577 1125899906842624000 3540968751962659831 4330250000000000000000 367262705 1048576 859 1048576 (ep490 rfl) rfl) (Enclosure.sfrac_false_div 367262705 1048576) (BSN.cos_reduce2 qz415 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 231543232618376986624000) qz19) 226375608064910080 72057594037927936 Bool.false 40435 1048576 55 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q2 367262705 1048576 226375608064910080 72057594037927936 55 231543232618376986624000 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 40435 1048576 231543232618376986624000 151115727451828646838272 3290427239 2147483648 277407 277136 (ep494 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep496 := nat_lit 7552683241130455360001571909445890122420540975854937539813345675730708668453825

noncomputable def ep497 := nat_lit 19758589727071350930340037390933032730663002827286146316366849068280926643262401

noncomputable def ep498 := BSN.sin_dyadic_bound_f 3290427239 2147483648 3 2 1048576 277407 ep496 ep187 ep492 ep497 ep189 ep492 1047796 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3290427239) qz292 0 2 ep496 ep187 ep492 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3290427239) qz293 0 2 ep497 ep189 ep492 rfl rfl rfl rfl) rfl rfl

noncomputable def ep499 := @Enclosure.Real.IsNear.sin_image qz132 qz415 Bool.false 367262705 1048576 859 1048576 Bool.true 1047796 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz132 Bool.false 394345327620160713577 1125899906842624000 3540968751962659831 4330250000000000000000 367262705 1048576 859 1048576 (ep490 rfl) rfl) (Enclosure.sfrac_false_div 367262705 1048576) (BSN.sin_reduce2 qz415 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 231543232618376986624000) qz19) 226375608064910080 72057594037927936 Bool.false 1047796 1048576 55 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q2 367262705 1048576 226375608064910080 72057594037927936 55 231543232618376986624000 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1047796 1048576 231543232618376986624000 151115727451828646838272 3290427239 2147483648 277407 277136 (ep498 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz416 := (@Enclosure.Real.IsNear.recentre' qz131 Bool.false 223557 1048576 1 1048576 223557 1048576 1 1048576 (ep488 rfl rfl) rfl)

noncomputable def ep500 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz131 (Real.cos qz132)) (@HMul.hMul Real Real Real qz0 qz131 (@Neg.neg Real Real.instNeg (Real.sin qz132))) Bool.true 9039527295 1099511627776 3356263702173 19044640904708096 Bool.false 58560532593 274877906944 1686856101027 9522320452354048 (@Enclosure.Real.IsNear.mulLit_ft qz131 (Real.cos qz132) 223557 1048576 1 1048576 40435 1048576 15009811 18162384896 9039527295 1099511627776 3356263702173 19044640904708096 qz416 (@Enclosure.Real.IsNear.recentre' (Real.cos qz132) Bool.true 40435 1048576 120078488 145299079168 40435 1048576 15009811 18162384896 (ep495 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz131 (@Neg.neg Real Real.instNeg (Real.sin qz132)) 223557 1048576 1 1048576 261949 262144 15009811 18162384896 58560532593 274877906944 1686856101027 9522320452354048 qz416 (@Enclosure.Real.IsNear.neg (Real.sin qz132) Bool.true 261949 262144 15009811 18162384896 (@Enclosure.Real.IsNear.recentre' (Real.sin qz132) Bool.true 1047796 1048576 120078488 145299079168 261949 262144 15009811 18162384896 (ep499 rfl rfl) rfl)) rfl)

noncomputable def ep501 := @ep412 9039527295 1099511627776 3356263702173 19044640904708096 Bool.false 58560532593 274877906944 1686856101027 9522320452354048 Bool.false ep413 531185917809 274877906944 6925005157199 1190290056544256 Bool.false 25372012335275008065536 92302843169 1099511627776 110741168753773 19044640904708096 (ep414 (BSN.head_sum_c_succ qz5 21 22 rfl rfl) (ep486 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep487 ep500) rfl rfl

noncomputable def ep502 := @Enclosure.Complex.IsNear.mul qz110 (@HAdd.hAdd Complex Complex Complex qz4 qz111 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz69 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz69 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz112 (@HMul.hMul Nat Nat Nat qz69 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz113 qz114 (@HSub.hSub Nat Nat Nat qz112 (@HMul.hMul Nat Nat Nat qz69 2 k) 1))))) Bool.true ep403 ep265 ep404 ep267 Bool.true

noncomputable def ep503 := nat_lit 1298793943526368589381632

noncomputable def ep504 := nat_lit 5849791866300064644902557

noncomputable abbrev qz133 := (Complex.re qz390)

noncomputable abbrev qz134 := (Complex.im qz390)

noncomputable def ep505 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 qz133 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz111 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz69 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz69 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz112 (@HMul.hMul Nat Nat Nat qz69 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz113 qz114 (@HSub.hSub Nat Nat Nat qz112 (@HMul.hMul Nat Nat Nat qz69 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz134 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz111 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz69 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz69 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz112 (@HMul.hMul Nat Nat Nat qz69 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz113 qz114 (@HSub.hSub Nat Nat Nat qz112 (@HMul.hMul Nat Nat Nat qz69 2 k) 1))))))) 130153832551498063663217 ep503 ep504

noncomputable def ep506 := nat_lit 67489229687460691010037743616

noncomputable def ep507 := nat_lit 56469301892450808233984000

noncomputable def ep508 := nat_lit 804996420050547125313316943

noncomputable def ep509 := nat_lit 22496409895820230336679247872000

noncomputable def ep510 := nat_lit 8244617885003384744079473165288409733038715437056

noncomputable def ep511 := @Enclosure.Real.IsNear.mulLit_tf qz133 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz111 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz69 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz69 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz112 (@HMul.hMul Nat Nat Nat qz69 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz113 qz114 (@HSub.hSub Nat Nat Nat qz112 (@HMul.hMul Nat Nat Nat qz69 2 k) 1)))))) 109982020503 549755813888 1647721818521 9522320452354048 3550230263717

noncomputable abbrev qz417 := (@Nat.cast Real Real.instNatCast 23)

noncomputable abbrev qz135 := (@Inv.inv Real Real.instInv (Real.sqrt qz417))

noncomputable abbrev qz418 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) qz537 (Real.log (Enclosure.sfrac Bool.false 23 1)))

noncomputable abbrev qz136 := (Real.cos qz418)

noncomputable abbrev qz137 := (Real.sin qz418)

noncomputable abbrev qz419 := (@Neg.neg Real Real.instNeg qz137)

noncomputable def ep512 := @Enclosure.Complex.IsNear.of_eq qz110 (Complex.mk (@HMul.hMul Real Real Real qz0 qz135 qz136) (@HMul.hMul Real Real Real qz0 qz135 qz419)) Bool.true 109982020503 549755813888 1647721818521 9522320452354048 Bool.false 64635025017 1099511627776 3283138400259 19044640904708096 (BSN.cpow_neg_s_mk qz13 113311 1000 23 qz14 rfl)

noncomputable abbrev qz420 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 23) qz15)

noncomputable def ep513 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz417) 5028793 1048576 1 1048576 109321 109322 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz417) (Real.sqrt qz420) Bool.false 5028793 1048576 1 1048576 (BSN.sqrt_natCast_div_one 23) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz420) Bool.false 5028793 1048576 1 1048576 5028793 1048576 1 1048576 (BSN.sqrt_enclosure 23 1 2514396 2514397 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep514 := BSN.log_dyadic_bound 7 39 4 3 369468094905 524288 138568 4046006391 1764735 190266 46 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 7) (BSN.artanhQ 39) 0 3 4046006391 369468094905 1764735 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz421 := (Real.log (Enclosure.sfrac Bool.false 23 1))

noncomputable abbrev qz138 := qz421

noncomputable abbrev qz422 := (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 23) qz15))

noncomputable def ep515 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz138 113311 1000 0 1 3530250507853047 1125899906842624 31250000017321 4330250000000000000 400016215295336608617 1125899906842624000 3540968751962659831 4330250000000000000000 qz18 (BSN.isNear_log_sfrac 23 1 3530250507853047 1125899906842624 31250000017321 4330250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz422 Bool.false 59227775304360265777152 18889465931478580854784 1000000000554272 138568000000000000000 3530250507853047 1125899906842624 31250000017321 4330250000000000000 (BSN.log_rat_reduce_isNear 23 1 4 46 32 190266 524288 24973259072661432 36028797018963968 138568 1000000000000000 rfl rfl rfl rfl (ep514 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep516 := nat_lit 141894633161239966658523182440104976

noncomputable def ep517 := BSN.cos_dyadic_bound_f 613749982 2147483648 2 1 1048576 277407 ep516 ep71 ep516 ep516 ep72 ep516 1006042 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 613749982) qz288 0 1 ep516 ep71 ep516 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 613749982) qz289 0 1 ep516 ep72 ep516 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz139 := qz418

noncomputable abbrev qz423 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 372544131) qz16)

noncomputable def ep518 := @Enclosure.Real.IsNear.cos_image qz139 qz423 Bool.false 372544131 1048576 429 524288 Bool.true 1006042 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz139 Bool.false 400016215295336608617 1125899906842624000 3540968751962659831 4330250000000000000000 372544131 1048576 429 524288 (ep515 rfl) rfl) (Enclosure.sfrac_false_div 372544131 1048576) (BSN.cos_reduce2 qz423 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 43188815508007553073152) qz19) 226375608064910080 72057594037927936 Bool.false 1006042 1048576 56 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q2 372544131 1048576 226375608064910080 72057594037927936 56 43188815508007553073152 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1006042 1048576 43188815508007553073152 151115727451828646838272 613749982 2147483648 277407 277136 (ep517 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep519 := BSN.sin_dyadic_bound_f 613749982 2147483648 2 1 1048576 277407 ep516 ep67 ep516 ep516 ep68 ep516 295619 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 613749982) qz292 0 1 ep516 ep67 ep516 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 613749982) qz293 0 1 ep516 ep68 ep516 rfl rfl rfl rfl) rfl rfl

noncomputable def ep520 := @Enclosure.Real.IsNear.sin_image qz139 qz423 Bool.false 372544131 1048576 429 524288 Bool.true 295619 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz139 Bool.false 400016215295336608617 1125899906842624000 3540968751962659831 4330250000000000000000 372544131 1048576 429 524288 (ep515 rfl) rfl) (Enclosure.sfrac_false_div 372544131 1048576) (BSN.sin_reduce2 qz423 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 43188815508007553073152) qz19) 226375608064910080 72057594037927936 Bool.false 295619 1048576 56 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q2 372544131 1048576 226375608064910080 72057594037927936 56 43188815508007553073152 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 295619 1048576 43188815508007553073152 151115727451828646838272 613749982 2147483648 277407 277136 (ep519 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz424 := (@Enclosure.Real.IsNear.recentre' qz135 Bool.false 218643 1048576 1 1048576 218643 1048576 1 1048576 (ep513 rfl rfl) rfl)

noncomputable def ep521 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz135 qz136) (@HMul.hMul Real Real Real qz0 qz135 qz419) Bool.true 109982020503 549755813888 1647721818521 9522320452354048 Bool.false 64635025017 1099511627776 3283138400259 19044640904708096 (@Enclosure.Real.IsNear.mulLit_ft qz135 qz136 218643 1048576 1 1048576 503021 524288 7496245 9081192448 109982020503 549755813888 1647721818521 9522320452354048 qz424 (@Enclosure.Real.IsNear.recentre' qz136 Bool.true 1006042 1048576 59969960 72649539584 503021 524288 7496245 9081192448 (ep518 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz135 qz419 218643 1048576 1 1048576 295619 1048576 7496245 9081192448 64635025017 1099511627776 3283138400259 19044640904708096 qz424 (@Enclosure.Real.IsNear.neg qz137 Bool.true 295619 1048576 7496245 9081192448 (@Enclosure.Real.IsNear.recentre' qz137 Bool.true 295619 1048576 59969960 72649539584 295619 1048576 7496245 9081192448 (ep520 rfl rfl) rfl)) rfl)

noncomputable def ep522 := @ep511 7087477261992 0 1 130153832551498063663217 ep503 ep504 ep506 (@Enclosure.Complex.IsNear.re_isNear qz110 Bool.true 109982020503 549755813888 1647721818521 9522320452354048 Bool.false 64635025017 1099511627776 3283138400259 19044640904708096 (ep512 ep521))

noncomputable def ep523 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz111 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz69 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz69 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz112 (@HMul.hMul Nat Nat Nat qz69 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz113 qz114 (@HSub.hSub Nat Nat Nat qz112 (@HMul.hMul Nat Nat Nat qz69 2 k) 1))))) Bool.false 3550230263717 7087477261992 0 1 Bool.false

noncomputable def ep524 := @Enclosure.Complex.IsNear.addLitP qz111 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz69 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz69 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz112 (@HMul.hMul Nat Nat Nat qz69 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz113 qz114 (@HSub.hSub Nat Nat Nat qz112 (@HMul.hMul Nat Nat Nat qz69 2 k) 1)))) Bool.false 12816632721 25679265442 0 1 Bool.true 2606153000

noncomputable def ep525 := @ep524 12839632721 0 1 Bool.false 1 552 0 1 Bool.false 113311 276000 0 1 Bool.false 7100460527434 3550230263717 7087477261992 0 1 Bool.false 735573395249231 735573395249231 3543738630996000 0 1

noncomputable abbrev qz140 := (@HDiv.hDiv Complex Complex Complex qz363 qz391 (@HSub.hSub Complex Complex Complex qz355 qz273 (1 : Complex)))

noncomputable def ep526 := @Enclosure.Complex.IsNear.addLitP qz140 qz88 Bool.true 46000000 51358530884 0 1 Bool.true 10424612000 51358530884 0 1

noncomputable def ep527 := @Enclosure.Complex.IsNear.of_eq qz140 (Complex.mk (Enclosure.sfrac Bool.true 46000000 51358530884) (Enclosure.sfrac Bool.true 10424612000 51358530884)) Bool.true 46000000 51358530884 0 1 Bool.true 10424612000 51358530884 0 1

noncomputable def ep528 := @ep526 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 51266530884 12816632721 25679265442 0 1 Bool.true 10424612000 2606153000 12839632721 0 1 (ep527 (BSN.N_div_s_sub_one_mk qz13 113311 1000 23 qz14 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 46000000 51358530884) (Enclosure.sfrac Bool.true 10424612000 51358530884) Bool.true 46000000 51358530884 0 1 Bool.true 10424612000 51358530884 0 1 (Enclosure.Real.IsNear.const Bool.true 46000000 51358530884) (Enclosure.Real.IsNear.const Bool.true 10424612000 51358530884))) qz89 rfl

noncomputable abbrev qz141 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)))

noncomputable abbrev qz142 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz392 qz391 1))

noncomputable def ep529 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz69 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz69 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz112 (@HMul.hMul Nat Nat Nat qz69 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz113 qz114 (@HSub.hSub Nat Nat Nat qz112 (@HMul.hMul Nat Nat Nat qz69 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz69 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz69 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz112 (@HMul.hMul Nat Nat Nat qz69 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz113 qz114 (@HSub.hSub Nat Nat Nat qz112 (@HMul.hMul Nat Nat Nat qz69 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz90)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz142)) Bool.false 1 552 0 1

noncomputable def ep530 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz69 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz69 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz112 (@HMul.hMul Nat Nat Nat qz69 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz113 qz114 (@HSub.hSub Nat Nat Nat qz112 (@HMul.hMul Nat Nat Nat qz69 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz90)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz142) Bool.false 0 1 0 1 Bool.false

noncomputable def ep531 := @ep530 0 1 0 1 Bool.false 1 552 0 1 Bool.false 113311 276000 0 1 Bool.false 1 1 552 0 1 Bool.false 113311 113311 276000 0

noncomputable def ep532 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz69 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz69 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz112 (@HMul.hMul Nat Nat Nat qz69 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz113 qz114 (@HSub.hSub Nat Nat Nat qz112 (@HMul.hMul Nat Nat Nat qz69 2 k) 1)))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep533 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz90)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz142 Bool.false 1 552 0 1 Bool.false 113311 276000 0 1

noncomputable def ep534 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz90)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz142)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz90)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz142)) 1 552 0 1 0 1 0

noncomputable def ep535 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz90)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz142) 1 24 0 1 1 23 0 1 1

noncomputable def ep536 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz90)) ↑qz141)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz90)) ↑qz141)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep537 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz90)) ↑qz141)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep538 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz90)) ↑qz141) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz10) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 1 1 6 2 Bool.false BSN.bern_real_1 EMRow36.d8 rfl) qz380

noncomputable def ep539 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz5 Bool.false 1 2 0 1 Bool.false 113311 1000 0 1 (BSN.ascPochhammer_one_eval qz5)

noncomputable def ep540 := ep539 (@Enclosure.Complex.IsNear.of_eq qz5 (Complex.mk qz83 qz13) Bool.false 1 2 0 1 Bool.false 113311 1000 0 1 (BSN.s_crit_mk qz13 Bool.false 113311 1000 qz14) (@Enclosure.Complex.IsNear.mk qz83 qz13 Bool.false 1 2 0 1 Bool.false 113311 1000 0 1 qz372 qz18))

noncomputable def ep541 := @ep537 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz90)) ↑qz141) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep538) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 113311 1000 0 1 ep540)

noncomputable def ep542 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz90)) ↑qz141)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 113311 1000 0 1 0 1 0

noncomputable def ep543 := @ep542 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz90)) ↑qz141) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep538) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 113311 1000 0 1 ep540)

noncomputable def ep544 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz90)) ↑qz141)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz90)) ↑qz141)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) 113311 12000 0 1 0 1 0 1 113311

noncomputable def ep545 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz90)) ↑qz141)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 113311 1000 0 1 113311 12000 0

noncomputable def ep546 := @ep545 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz90)) ↑qz141) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep538) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 113311 1000 0 1 ep540)

noncomputable def ep547 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz90)) ↑qz141)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep548 := @ep547 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz90)) ↑qz141) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep538) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 113311 1000 0 1 ep540)

noncomputable def ep549 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz90)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 113311 12000 0 1 (@ep536 1 24 0 1 (ep541 rfl) (ep543 rfl) rfl rfl) (@ep544 113311 12000 0 1 (ep546 rfl) (ep548 rfl) rfl rfl)

noncomputable def ep550 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz90)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 113311 12000 0 1 ep549

noncomputable abbrev qz143 := (@Enclosure.Complex.IsNear.of_eq (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz392 qz391 1)) (Complex.mk (Enclosure.sfrac Bool.false 1 23) qz284) Bool.false 1 23 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 23 1 23 EMRow36.d9 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 23) qz284 Bool.false 1 23 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 23) qz295))

noncomputable def ep551 := @ep535 552 0 1 ep550 (@Enclosure.Complex.IsNear.re_isNear qz142 Bool.false 1 23 0 1 Bool.false 0 1 0 1 qz143)

noncomputable def ep552 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz90)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz142) 113311 12000 0 1 0 1 0 1 0

noncomputable def ep553 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz90)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 113311 12000 0 1 ep549

noncomputable def ep554 := @ep552 1 0 1 ep553 (@Enclosure.Complex.IsNear.im_isNear qz142 Bool.false 1 23 0 1 Bool.false 0 1 0 1 qz143)

noncomputable def ep555 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz90)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz142)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz90)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz142)) 0 1 0 1 113311 276000 0

noncomputable def ep556 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz90)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz142) 1 24 0 1 0 1 0 1 0

noncomputable def ep557 := @ep556 1 0 1 ep550 (@Enclosure.Complex.IsNear.im_isNear qz142 Bool.false 1 23 0 1 Bool.false 0 1 0 1 qz143)

noncomputable def ep558 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz90)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz142) 113311 12000 0 1 1 23 0 1 113311

noncomputable def ep559 := @ep558 276000 0 1 ep553 (@Enclosure.Complex.IsNear.re_isNear qz142 Bool.false 1 23 0 1 Bool.false 0 1 0 1 qz143)

noncomputable def ep560 := @ep531 1 (@ep532 0 1 0 1 (BSN.bern_sum_base qz5 23) qz104) (ep533 (@ep534 1 1 1 552 0 1 (ep551 rfl) (ep554 rfl) rfl rfl) (@ep555 1 113311 113311 276000 0 1 (ep557 rfl) (ep559 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep561 := ep525 (ep528 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep529 Bool.false 113311 276000 0 1 (BSN.bern_sum_succ qz5 23 0 1 1 rfl rfl) (ep560 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep562 := @Enclosure.Real.IsNear.mulLit_ff qz134 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz111 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz69 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz69 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz112 (@HMul.hMul Nat Nat Nat qz69 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz113 qz114 (@HSub.hSub Nat Nat Nat qz112 (@HMul.hMul Nat Nat Nat qz69 2 k) 1)))))) 64635025017 1099511627776 3283138400259 19044640904708096 735573395249231

noncomputable def ep563 := @ep562 3543738630996000 0 1 689040649330053255579883 ep507 ep508 ep509 (@Enclosure.Complex.IsNear.im_isNear qz110 Bool.true 109982020503 549755813888 1647721818521 9522320452354048 Bool.false 64635025017 1099511627776 3283138400259 19044640904708096 (ep512 ep521))

noncomputable def ep564 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz111 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz69 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz69 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz112 (@HMul.hMul Nat Nat Nat qz69 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz113 qz114 (@HSub.hSub Nat Nat Nat qz112 (@HMul.hMul Nat Nat Nat qz69 2 k) 1))))) Bool.false 3550230263717 7087477261992 0 1 Bool.false

noncomputable def ep565 := nat_lit 26966616079254082212327731

noncomputable def ep566 := nat_lit 1212020332475729205346807351

noncomputable def ep567 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 qz133 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz111 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz69 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz69 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz112 (@HMul.hMul Nat Nat Nat qz69 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz113 qz114 (@HSub.hSub Nat Nat Nat qz112 (@HMul.hMul Nat Nat Nat qz69 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz134 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz111 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz69 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz69 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz112 (@HMul.hMul Nat Nat Nat qz69 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz113 qz114 (@HSub.hSub Nat Nat Nat qz112 (@HMul.hMul Nat Nat Nat qz69 2 k) 1))))))) ep565 ep398 ep566

noncomputable def ep568 := nat_lit 3885299102856973023700901

noncomputable def ep569 := nat_lit 44992819791640460673358495744

noncomputable def ep570 := nat_lit 885910840937108041386338481475659313353597124608

noncomputable def ep571 := @Enclosure.Real.IsNear.mulLit_tf qz133 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz111 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz69 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz69 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz112 (@HMul.hMul Nat Nat Nat qz69 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz113 qz114 (@HSub.hSub Nat Nat Nat qz112 (@HMul.hMul Nat Nat Nat qz69 2 k) 1)))))) 109982020503 549755813888 1647721818521 9522320452354048 735573395249231

noncomputable def ep572 := @ep571 3543738630996000 0 1 ep565 ep398 ep566 ep400 (@Enclosure.Complex.IsNear.re_isNear qz110 Bool.true 109982020503 549755813888 1647721818521 9522320452354048 Bool.false 64635025017 1099511627776 3283138400259 19044640904708096 (ep512 ep521))

noncomputable def ep573 := @Enclosure.Real.IsNear.mulLit_ff qz134 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz111 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz69 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz69 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz112 (@HMul.hMul Nat Nat Nat qz69 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz113 qz114 (@HSub.hSub Nat Nat Nat qz112 (@HMul.hMul Nat Nat Nat qz69 2 k) 1)))))) 64635025017 1099511627776 3283138400259 19044640904708096 3550230263717

noncomputable def ep574 := @ep573 7087477261992 0 1 3325640897267518875481 112938603784901616467968 ep568 ep569 (@Enclosure.Complex.IsNear.im_isNear qz110 Bool.true 109982020503 549755813888 1647721818521 9522320452354048 Bool.false 64635025017 1099511627776 3283138400259 19044640904708096 (ep512 ep521))

noncomputable abbrev qz425 := (ep561 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep575 := @ep502 ep405 ep398 ep406 ep400 (@ep505 ep506 689040649330053255579883 ep507 ep508 ep509 ep510 ep403 ep265 ep404 ep267 (ep522 (@ep523 735573395249231 3543738630996000 0 1 qz425) rfl) (ep563 (@ep564 735573395249231 3543738630996000 0 1 qz425) rfl) rfl rfl) (@ep567 ep400 3325640897267518875481 112938603784901616467968 ep568 ep569 ep570 ep405 ep398 ep406 ep400 (ep572 (@ep564 735573395249231 3543738630996000 0 1 qz425) rfl) (ep574 (@ep523 735573395249231 3543738630996000 0 1 qz425) rfl) rfl rfl)

noncomputable def ep576 := @ep409 ep399 ep400 (@ep410 19044640904708096 (BSN.head_sum_c_eq qz5 23) (ep411 (BSN.head_sum_c_succ qz5 22 23 rfl rfl) (ep501 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep575 rfl rfl rfl

noncomputable def ep577 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz5 1 23) Bool.false ep264 ep265 ep266 ep267 Bool.false ep397 ep398 ep399 ep400 (@ep401 ep267 Bool.false ep397 ep398 ep399 ep400 (BSN.zetaApproximant_eq_folded' qz5 1 23 rfl) (ep576 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep578 := @Enclosure.Real.IsNear.mulLit_ff (Real.sin (@HSub.hSub Real Real Real qz358 (Complex.im (@HSub.hSub Complex Complex Complex qz62 qz63 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz64 (@Nat.cast Complex Complex.instNatCast j))))) qz65)) (Complex.im (zetaApproximant qz5 1 23)) 231 1048576 6176101

noncomputable def ep579 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz358 (Complex.im (@HSub.hSub Complex Complex Complex qz62 qz63 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz64 (@Nat.cast Complex Complex.instNatCast j))))) qz65)) Bool.false 231 1048576 49408808

noncomputable def ep580 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz358 (Complex.im (@HSub.hSub Complex Complex Complex qz62 qz63 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz64 (@Nat.cast Complex Complex.instNatCast j))))) qz65) qz359 Bool.false 56001493 524288 349

noncomputable def ep581 := BSN.sin_dyadic_bound_f 474351 2147483648 1 0 1048576 277407 0 1 1 0 1 1 231 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 474351) qz292 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 474351) qz293 0 0 rfl) rfl rfl

noncomputable def ep582 := @ep580 1048576 Bool.false 231 1048576 1 138568 (@ep272 56001493 524288 349 1048576 ep394 rfl) (Enclosure.sfrac_false_div 56001493 524288) (BSN.sin_reduce0 qz359 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16689746506915250176) qz302) 226375608064910080 72057594037927936 Bool.false 231 1048576 17 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q0 56001493 524288 226375608064910080 72057594037927936 17 16689746506915250176 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 231 1048576 16689746506915250176 75557863725914323419136 474351 2147483648 277407 277136 (ep581 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep583 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz5 1 23) Bool.false ep264 ep265 ep266 ep267 Bool.false ep397 ep398 ep399 ep400 (@ep401 ep267 Bool.false ep397 ep398 ep399 ep400 (BSN.zetaApproximant_eq_folded' qz5 1 23 rfl) (ep576 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow36.d10 : Enclosure.Real.IsNear (hardyZApproximantEM 1 23 qz13) Bool.false ep247 ep248 ep249 ep250 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 23 qz13) ep251 Bool.false ep247 ep248 ep249 ep250 (@Eq.refl Real ep251) (@ep252 Bool.false ep247 ep248 ep249 ep250 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz358 (Complex.im (@HSub.hSub Complex Complex Complex qz62 qz63 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz64 (@Nat.cast Complex Complex.instNatCast j))))) qz65) (zetaApproximant qz5 1 23)) (@ep254 ep255 ep256 ep257 ep258 ep259 ep260 ep261 ep262 ep247 ep248 ep249 ep250 (@ep263 18162384896 ep264 ep265 ep266 ep267 ep253 ep255 ep256 ep257 (@ep268 145299079168 1048575 1048576 6176101 18162384896 (ep396 rfl rfl) rfl) ep577 rfl) (@ep578 18162384896 ep397 ep398 ep399 ep400 ep258 ep259 ep260 ep261 (@ep579 145299079168 231 1048576 6176101 18162384896 (ep582 rfl rfl) rfl) ep583 rfl) rfl rfl))

noncomputable abbrev qz584 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 115476 1000)))

noncomputable abbrev qz567 := qz584

noncomputable abbrev qz426 := qz567

noncomputable abbrev qz144 := (BSN.headSumC qz426 9)

noncomputable abbrev qz145 := qz426

noncomputable abbrev qz568 := (@Neg.neg Complex Complex.instNeg qz584)

noncomputable abbrev qz427 := qz568

noncomputable abbrev qz146 := qz427

noncomputable abbrev qz428 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 8) qz146)

noncomputable def ep584 := @Enclosure.Complex.IsNear.of_eq qz144 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz145 8) qz428) Bool.false 819227130201 1099511627776 54106027581381 19044640904708096 Bool.false 284046628153 549755813888 27066206823989 9522320452354048

noncomputable def ep585 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz145 8) qz428 Bool.false 46226191741 68719476736 24217504434515 9522320452354048 Bool.false 474294827105 549755813888 24223668458785 9522320452354048 Bool.false

noncomputable abbrev qz429 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 7) qz146)

noncomputable def ep586 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz145 8) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz145 7) qz429) Bool.false 46226191741 68719476736 24217504434515 9522320452354048 Bool.false 474294827105 549755813888 24223668458785 9522320452354048

noncomputable def ep587 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz145 7) qz429 Bool.false 176409540589 274877906944 5296863651221 2380580113088512 Bool.false 267202332205 549755813888 5296327600913 2380580113088512 Bool.false

noncomputable abbrev qz430 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 6) qz146)

noncomputable def ep588 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz145 7) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz145 6) qz430) Bool.false 176409540589 274877906944 5296863651221 2380580113088512 Bool.false 267202332205 549755813888 5296327600913 2380580113088512

noncomputable def ep589 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz145 6) qz430 Bool.false 299520899293 1099511627776 35814440557271 19044640904708096 Bool.false 343208744087 1099511627776 35818848336067 19044640904708096 Bool.false

noncomputable abbrev qz431 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 5) qz146)

noncomputable def ep590 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz145 6) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz145 5) qz431) Bool.false 299520899293 1099511627776 35814440557271 19044640904708096 Bool.false 343208744087 1099511627776 35818848336067 19044640904708096

noncomputable def ep591 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz145 5) qz431 Bool.false 365842164345 549755813888 7157461875121 4761160226177024 Bool.false 108647394561 1099511627776 28641554054223 19044640904708096 Bool.true

noncomputable abbrev qz432 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 4) qz146)

noncomputable def ep592 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz145 5) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz145 4) qz432) Bool.false 365842164345 549755813888 7157461875121 4761160226177024 Bool.false 108647394561 1099511627776 28641554054223 19044640904708096

noncomputable def ep593 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz145 4) qz432 Bool.false 1276241836971 1099511627776 20597093949925 19044640904708096 Bool.false 46014815945 274877906944 10312149892405 9522320452354048 Bool.true

noncomputable def ep594 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz145 4) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz145 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz146)) Bool.false 1276241836971 1099511627776 20597093949925 19044640904708096 Bool.false 46014815945 274877906944 10312149892405 9522320452354048

noncomputable def ep595 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz145 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz146) Bool.false 261493902739 274877906944 2833962305079 4761160226177024 Bool.false 775626436585 1099511627776 11352717847759 19044640904708096 Bool.false

noncomputable def ep596 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz145 3) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz145 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz146)) Bool.false 261493902739 274877906944 2833962305079 4761160226177024 Bool.false 775626436585 1099511627776 11352717847759 19044640904708096

noncomputable def ep597 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz145 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz146) Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.true

noncomputable def ep598 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz145 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz10) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz145)

noncomputable abbrev qz585 := (Enclosure.sfrac Bool.false 115476 1000)

noncomputable abbrev qz569 := qz585

noncomputable abbrev qz433 := qz569

noncomputable abbrev qz147 := (@HMul.hMul Real Real Real qz268 qz433 (Real.log qz286))

noncomputable abbrev qz148 := qz433

noncomputable abbrev qz434 := (@Eq.refl Real qz569)

noncomputable abbrev qz149 := qz434

noncomputable def ep599 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz9 qz146) (Complex.mk (@HMul.hMul Real Real Real qz0 qz11 (Real.cos qz147)) (@HMul.hMul Real Real Real qz0 qz11 (@Neg.neg Real Real.instNeg (Real.sin qz147)))) Bool.true 13384004205 274877906944 2833962305079 4761160226177024 Bool.false 775626436585 1099511627776 11352717847759 19044640904708096 (BSN.cpow_neg_s_mk qz148 115476 1000 2 qz149 rfl)

noncomputable def ep600 := nat_lit 3877973906883556729407773225325863418533684564047112823913034709972787567190625

noncomputable def ep601 := nat_lit 11709158672275637561595252019160332925451143969978497168142757239641250390625

noncomputable def ep602 := nat_lit 11610503403306118913100129171939269589750151404201381477402818615439080200790625

noncomputable def ep603 := BSN.cos_dyadic_bound_f 3225267285 2147483648 3 2 1048576 277407 ep600 ep155 ep601 ep602 ep158 ep601 72204 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3225267285) qz288 0 2 ep600 ep155 ep601 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3225267285) qz289 0 2 ep602 ep158 ep601 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz150 := (Enclosure.Real.IsNear.const Bool.false 115476 1000)

noncomputable abbrev qz435 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 20982451) qz543)

noncomputable def ep604 := @Enclosure.Real.IsNear.cos_image qz147 qz435 Bool.false 20982451 262144 875 1048576 Bool.true 72204 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz147 Bool.false 655701597 8192000 28869 34642000 20982451 262144 875 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz148 qz17 115476 1000 0 1 363408 524288 1 138568 655701597 8192000 28869 34642000 qz150 qz291 rfl) rfl) (Enclosure.sfrac_false_div 20982451 262144) (BSN.cos_reduce2 qz435 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 56739502129040716726272) qz319) 226375608064910080 72057594037927936 Bool.false 72204 1048576 12 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q2 20982451 262144 226375608064910080 72057594037927936 12 56739502129040716726272 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 72204 1048576 56739502129040716726272 37778931862957161709568 3225267285 2147483648 277407 277136 (ep603 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep605 := nat_lit 6970985705452581602884715603971225887020271300108820285308948272159304620630625

noncomputable def ep606 := nat_lit 18238385828811172213407862840465046307935694410047897466108347677267331029590625

noncomputable def ep607 := BSN.sin_dyadic_bound_f 3225267285 2147483648 3 2 1048576 277407 ep605 ep187 ep601 ep606 ep189 ep601 1046087 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3225267285) qz292 0 2 ep605 ep187 ep601 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3225267285) qz293 0 2 ep606 ep189 ep601 rfl rfl rfl rfl) rfl rfl

noncomputable def ep608 := @Enclosure.Real.IsNear.sin_image qz147 qz435 Bool.false 20982451 262144 875 1048576 Bool.true 1046087 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz147 Bool.false 655701597 8192000 28869 34642000 20982451 262144 875 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz148 qz17 115476 1000 0 1 363408 524288 1 138568 655701597 8192000 28869 34642000 qz150 qz291 rfl) rfl) (Enclosure.sfrac_false_div 20982451 262144) (BSN.sin_reduce2 qz435 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 56739502129040716726272) qz319) 226375608064910080 72057594037927936 Bool.false 1046087 1048576 12 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q2 20982451 262144 226375608064910080 72057594037927936 12 56739502129040716726272 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1046087 1048576 56739502129040716726272 37778931862957161709568 3225267285 2147483648 277407 277136 (ep607 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep609 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz11 (Real.cos qz147)) (@HMul.hMul Real Real Real qz0 qz11 (@Neg.neg Real Real.instNeg (Real.sin qz147))) Bool.true 13384004205 274877906944 2833962305079 4761160226177024 Bool.false 775626436585 1099511627776 11352717847759 19044640904708096 (@Enclosure.Real.IsNear.mulLit_ft qz11 (Real.cos qz147) 741455 1048576 1 1048576 18051 262144 15286947 18162384896 13384004205 274877906944 2833962305079 4761160226177024 qz294 (@Enclosure.Real.IsNear.recentre' (Real.cos qz147) Bool.true 72204 1048576 122295576 145299079168 18051 262144 15286947 18162384896 (ep604 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz11 (@Neg.neg Real Real.instNeg (Real.sin qz147)) 741455 1048576 1 1048576 1046087 1048576 15286947 18162384896 775626436585 1099511627776 11352717847759 19044640904708096 qz294 (@Enclosure.Real.IsNear.neg (Real.sin qz147) Bool.true 1046087 1048576 15286947 18162384896 (@Enclosure.Real.IsNear.recentre' (Real.sin qz147) Bool.true 1046087 1048576 122295576 145299079168 1046087 1048576 15286947 18162384896 (ep608 rfl rfl) rfl)) rfl)

noncomputable def ep610 := @ep597 13384004205 274877906944 2833962305079 4761160226177024 Bool.false 775626436585 1099511627776 11352717847759 19044640904708096 Bool.false 261493902739 261493902739 274877906944 2833962305079 4761160226177024 Bool.false 775626436585 775626436585 1099511627776 11352717847759 19044640904708096 (ep598 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz10 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz20)) (ep599 ep609) rfl rfl

noncomputable abbrev qz151 := (@HMul.hMul Real Real Real qz268 qz433 (Real.log (Enclosure.sfrac Bool.false 3 1)))

noncomputable def ep611 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz8 qz146) (Complex.mk (@HMul.hMul Real Real Real qz0 qz21 (Real.cos qz151)) (@HMul.hMul Real Real Real qz0 qz21 (@Neg.neg Real Real.instNeg (Real.sin qz151)))) Bool.false 230266226015 1099511627776 9261244729609 19044640904708096 Bool.true 591567172805 1099511627776 9271581937051 19044640904708096 (BSN.cpow_neg_s_mk qz148 115476 1000 3 qz149 rfl)

noncomputable def ep612 := nat_lit 1575502919866163000091122699787189237371726343813835052910313128385762308360801

noncomputable def ep613 := nat_lit 1939594580282112117722998315466583072551821724429838824670971399075090369121

noncomputable def ep614 := nat_lit 4722629570437924776037922102730634545970075387992645481081597442359136744344161

noncomputable def ep615 := BSN.cos_dyadic_bound_f 2576106837 2147483648 3 2 1048576 277407 ep612 ep155 ep613 ep614 ep158 ep613 380357 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2576106837) qz288 0 2 ep612 ep155 ep613 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2576106837) qz289 0 2 ep614 ep158 ep613 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz436 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 133025811) qz16)

noncomputable def ep616 := @Enclosure.Real.IsNear.cos_image qz151 qz436 Bool.false 133025811 1048576 875 1048576 Bool.false 380357 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz151 Bool.false 16628226441 131072000 28869 34642000 133025811 1048576 875 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz148 qz23 115476 1000 0 1 575989 524288 1 138568 16628226441 131072000 28869 34642000 qz150 qz298 rfl) rfl) (Enclosure.sfrac_false_div 133025811 1048576) (BSN.cos_reduce0 qz436 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 181277403026564728225792) qz19) 226375608064910080 72057594037927936 Bool.false 380357 1048576 20 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q0 133025811 1048576 226375608064910080 72057594037927936 20 181277403026564728225792 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 380357 1048576 181277403026564728225792 151115727451828646838272 2576106837 2147483648 277407 277136 (ep615 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep617 := nat_lit 2834353580094867710469842460964567360811065961485359224178826853975112082754145

noncomputable def ep618 := nat_lit 7420166699499434869706607305253587667625803140145911562371269711479171975187041

noncomputable def ep619 := BSN.sin_dyadic_bound_f 2576106837 2147483648 3 2 1048576 277407 ep617 ep187 ep613 ep618 ep189 ep613 977159 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2576106837) qz292 0 2 ep617 ep187 ep613 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2576106837) qz293 0 2 ep618 ep189 ep613 rfl rfl rfl rfl) rfl rfl

noncomputable def ep620 := @Enclosure.Real.IsNear.sin_image qz151 qz436 Bool.false 133025811 1048576 875 1048576 Bool.false 977159 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz151 Bool.false 16628226441 131072000 28869 34642000 133025811 1048576 875 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz148 qz23 115476 1000 0 1 575989 524288 1 138568 16628226441 131072000 28869 34642000 qz150 qz298 rfl) rfl) (Enclosure.sfrac_false_div 133025811 1048576) (BSN.sin_reduce0 qz436 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 181277403026564728225792) qz19) 226375608064910080 72057594037927936 Bool.false 977159 1048576 20 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q0 133025811 1048576 226375608064910080 72057594037927936 20 181277403026564728225792 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 977159 1048576 181277403026564728225792 151115727451828646838272 2576106837 2147483648 277407 277136 (ep619 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep621 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz21 (Real.cos qz151)) (@HMul.hMul Real Real Real qz0 qz21 (@Neg.neg Real Real.instNeg (Real.sin qz151))) Bool.false 230266226015 1099511627776 9261244729609 19044640904708096 Bool.true 591567172805 1099511627776 9271581937051 19044640904708096 (@Enclosure.Real.IsNear.mulLit_ff qz21 (Real.cos qz151) 605395 1048576 1 1048576 380357 1048576 15286947 18162384896 230266226015 1099511627776 9261244729609 19044640904708096 qz299 (@Enclosure.Real.IsNear.recentre' (Real.cos qz151) Bool.false 380357 1048576 122295576 145299079168 380357 1048576 15286947 18162384896 (ep616 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz21 (@Neg.neg Real Real.instNeg (Real.sin qz151)) 605395 1048576 1 1048576 977159 1048576 15286947 18162384896 591567172805 1099511627776 9271581937051 19044640904708096 qz299 (@Enclosure.Real.IsNear.neg (Real.sin qz151) Bool.false 977159 1048576 15286947 18162384896 (@Enclosure.Real.IsNear.recentre' (Real.sin qz151) Bool.false 977159 1048576 122295576 145299079168 977159 1048576 15286947 18162384896 (ep620 rfl rfl) rfl)) rfl)

noncomputable def ep622 := @ep595 230266226015 1099511627776 9261244729609 19044640904708096 Bool.true 591567172805 1099511627776 9271581937051 19044640904708096 Bool.false 350810684900954156826624 1276241836971 1099511627776 20597093949925 19044640904708096 Bool.false 202375300725999958753280 46014815945 274877906944 10312149892405 9522320452354048 (ep596 (BSN.head_sum_c_succ qz145 2 3 rfl rfl) (ep610 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep611 ep621) rfl rfl

noncomputable abbrev qz152 := (@HMul.hMul Real Real Real qz268 qz433 (Real.log (Enclosure.sfrac Bool.false 4 1)))

noncomputable def ep623 := @Enclosure.Complex.IsNear.of_eq qz432 (Complex.mk (@HMul.hMul Real Real Real qz0 qz24 (Real.cos qz152)) (@HMul.hMul Real Real Real qz0 qz24 (@Neg.neg Real Real.instNeg (Real.sin qz152)))) Bool.true 544557508281 1099511627776 8032753550559 19044640904708096 Bool.true 75411869219 1099511627776 8017254269413 19044640904708096 (BSN.cpow_neg_s_mk qz148 115476 1000 4 qz149 rfl)

noncomputable def ep624 := nat_lit 5778819226927683807545388081671663019455494460047916019821034141952568889180160

noncomputable def ep625 := nat_lit 8051276174151772708002885790604034553121172280082868126873347198517904408576

noncomputable def ep626 := nat_lit 15121967337671497578234487922621948995011717878338693503516342095363889531191296

noncomputable def ep627 := BSN.sin_dyadic_bound_f 3077748232 2147483648 3 2 1048576 277407 ep624 ep187 ep625 ep626 ep189 ep625 1038663 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3077748232) qz292 0 2 ep624 ep187 ep625 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3077748232) qz293 0 2 ep626 ep189 ep625 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz437 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 167859839) qz16)

noncomputable def ep628 := @Enclosure.Real.IsNear.cos_image qz152 qz437 Bool.false 167859839 1048576 875 1048576 Bool.true 1038663 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz152 Bool.false 20982479973 131072000 28869 34642000 167859839 1048576 875 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz148 qz27 115476 1000 0 1 726817 524288 1 138568 20982479973 131072000 28869 34642000 qz150 qz301 rfl) rfl) (Enclosure.sfrac_false_div 167859839 1048576) (BSN.cos_reduce1 qz437 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 216577278038500104470528) qz19) 226375608064910080 72057594037927936 Bool.false 1038663 1048576 25 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q1 167859839 1048576 226375608064910080 72057594037927936 25 216577278038500104470528 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1038663 1048576 216577278038500104470528 151115727451828646838272 3077748232 2147483648 277407 277136 (ep627 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep629 := nat_lit 3214033471037225125395439105724525692832217443262212396845851566506324007059456

noncomputable def ep630 := nat_lit 9625997860763371830770311545592369009390409985226471454283808005121936212361216

noncomputable def ep631 := BSN.cos_dyadic_bound_f 3077748232 2147483648 3 2 1048576 277407 ep629 ep155 ep625 ep630 ep158 ep625 143837 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3077748232) qz288 0 2 ep629 ep155 ep625 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3077748232) qz289 0 2 ep630 ep158 ep625 rfl rfl rfl rfl) rfl rfl

noncomputable def ep632 := @Enclosure.Real.IsNear.sin_image qz152 qz437 Bool.false 167859839 1048576 875 1048576 Bool.false 143837 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz152 Bool.false 20982479973 131072000 28869 34642000 167859839 1048576 875 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz148 qz27 115476 1000 0 1 726817 524288 1 138568 20982479973 131072000 28869 34642000 qz150 qz301 rfl) rfl) (Enclosure.sfrac_false_div 167859839 1048576) (BSN.sin_reduce1 qz437 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 216577278038500104470528) qz19) 226375608064910080 72057594037927936 Bool.false 143837 1048576 25 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q1 167859839 1048576 226375608064910080 72057594037927936 25 216577278038500104470528 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 143837 1048576 216577278038500104470528 151115727451828646838272 3077748232 2147483648 277407 277136 (ep631 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep633 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz24 (Real.cos qz152)) (@HMul.hMul Real Real Real qz0 qz24 (@Neg.neg Real Real.instNeg (Real.sin qz152))) Bool.true 544557508281 1099511627776 8032753550559 19044640904708096 Bool.true 75411869219 1099511627776 8017254269413 19044640904708096 (@Enclosure.Real.IsNear.mulLit_ft qz24 (Real.cos qz152) 524287 1048576 1 1048576 1038663 1048576 15286947 18162384896 544557508281 1099511627776 8032753550559 19044640904708096 qz303 (@Enclosure.Real.IsNear.recentre' (Real.cos qz152) Bool.true 1038663 1048576 122295576 145299079168 1038663 1048576 15286947 18162384896 (ep628 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz24 (@Neg.neg Real Real.instNeg (Real.sin qz152)) 524287 1048576 1 1048576 143837 1048576 15286947 18162384896 75411869219 1099511627776 8017254269413 19044640904708096 qz303 (@Enclosure.Real.IsNear.neg (Real.sin qz152) Bool.false 143837 1048576 15286947 18162384896 (@Enclosure.Real.IsNear.recentre' (Real.sin qz152) Bool.false 143837 1048576 122295576 145299079168 143837 1048576 15286947 18162384896 (ep632 rfl rfl) rfl)) rfl)

noncomputable def ep634 := @ep593 544557508281 1099511627776 8032753550559 19044640904708096 Bool.true 75411869219 1099511627776 8017254269413 19044640904708096 Bool.false 804495427256131717693440 365842164345 549755813888 7157461875121 4761160226177024 Bool.false 29864768411846609731584 108647394561 1099511627776 28641554054223 19044640904708096 (ep594 (BSN.head_sum_c_succ qz145 3 4 rfl rfl) (ep622 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep623 ep633) rfl rfl

noncomputable abbrev qz153 := (@HMul.hMul Real Real Real qz268 qz433 (Real.log (Enclosure.sfrac Bool.false 5 1)))

noncomputable def ep635 := @Enclosure.Complex.IsNear.of_eq qz431 (Complex.mk (@HMul.hMul Real Real Real qz0 qz28 (Real.cos qz153)) (@HMul.hMul Real Real Real qz0 qz28 (@Neg.neg Real Real.instNeg (Real.sin qz153)))) Bool.true 432163429397 1099511627776 7184593056787 19044640904708096 Bool.false 117280674763 549755813888 1794323570461 4761160226177024 (BSN.cpow_neg_s_mk qz148 115476 1000 5 qz149 rfl)

noncomputable def ep636 := nat_lit 1300422286959022925086371079530168576

noncomputable def ep637 := BSN.cos_dyadic_bound_f 1067876676 2147483648 2 1 1048576 277407 ep636 ep71 ep636 ep636 ep72 ep636 921581 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1067876676) qz288 0 1 ep636 ep71 ep636 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1067876676) qz289 0 1 ep636 ep72 ep636 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz438 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 194879145) qz16)

noncomputable def ep638 := @Enclosure.Real.IsNear.cos_image qz153 qz438 Bool.false 194879145 1048576 875 1048576 Bool.true 921581 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz153 Bool.false 761246661 4096000 28869 34642000 194879145 1048576 875 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz148 qz30 115476 1000 0 1 843808 524288 1 138568 761246661 4096000 28869 34642000 qz150 qz305 rfl) rfl) (Enclosure.sfrac_false_div 194879145 1048576) (BSN.cos_reduce2 qz438 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 75145140668991537152000) qz19) 226375608064910080 72057594037927936 Bool.false 921581 1048576 29 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q2 194879145 1048576 226375608064910080 72057594037927936 29 75145140668991537152000 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 921581 1048576 75145140668991537152000 151115727451828646838272 1067876676 2147483648 277407 277136 (ep637 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep639 := BSN.sin_dyadic_bound_f 1067876676 2147483648 2 1 1048576 277407 ep636 ep67 ep636 ep636 ep68 ep636 500198 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1067876676) qz292 0 1 ep636 ep67 ep636 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1067876676) qz293 0 1 ep636 ep68 ep636 rfl rfl rfl rfl) rfl rfl

noncomputable def ep640 := @Enclosure.Real.IsNear.sin_image qz153 qz438 Bool.false 194879145 1048576 875 1048576 Bool.true 500198 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz153 Bool.false 761246661 4096000 28869 34642000 194879145 1048576 875 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz148 qz30 115476 1000 0 1 843808 524288 1 138568 761246661 4096000 28869 34642000 qz150 qz305 rfl) rfl) (Enclosure.sfrac_false_div 194879145 1048576) (BSN.sin_reduce2 qz438 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 75145140668991537152000) qz19) 226375608064910080 72057594037927936 Bool.false 500198 1048576 29 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q2 194879145 1048576 226375608064910080 72057594037927936 29 75145140668991537152000 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 500198 1048576 75145140668991537152000 151115727451828646838272 1067876676 2147483648 277407 277136 (ep639 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep641 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz28 (Real.cos qz153)) (@HMul.hMul Real Real Real qz0 qz28 (@Neg.neg Real Real.instNeg (Real.sin qz153))) Bool.true 432163429397 1099511627776 7184593056787 19044640904708096 Bool.false 117280674763 549755813888 1794323570461 4761160226177024 (@Enclosure.Real.IsNear.mulLit_ft qz28 (Real.cos qz153) 468937 1048576 1 1048576 921581 1048576 15286947 18162384896 432163429397 1099511627776 7184593056787 19044640904708096 qz307 (@Enclosure.Real.IsNear.recentre' (Real.cos qz153) Bool.true 921581 1048576 122295576 145299079168 921581 1048576 15286947 18162384896 (ep638 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz28 (@Neg.neg Real Real.instNeg (Real.sin qz153)) 468937 1048576 1 1048576 250099 524288 15286947 18162384896 117280674763 549755813888 1794323570461 4761160226177024 qz307 (@Enclosure.Real.IsNear.neg (Real.sin qz153) Bool.true 250099 524288 15286947 18162384896 (@Enclosure.Real.IsNear.recentre' (Real.sin qz153) Bool.true 500198 1048576 122295576 145299079168 250099 524288 15286947 18162384896 (ep640 rfl rfl) rfl)) rfl)

noncomputable def ep642 := @ep591 432163429397 1099511627776 7184593056787 19044640904708096 Bool.false 117280674763 549755813888 1794323570461 4761160226177024 Bool.false 164663355767288898781184 299520899293 1099511627776 35814440557271 19044640904708096 Bool.false 188681002439026992480256 343208744087 1099511627776 35818848336067 19044640904708096 (ep592 (BSN.head_sum_c_succ qz145 4 5 rfl rfl) (ep634 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep635 ep641) rfl rfl

noncomputable abbrev qz154 := (@HMul.hMul Real Real Real qz268 qz433 qz540)

noncomputable def ep643 := @Enclosure.Complex.IsNear.of_eq qz430 (Complex.mk (@HMul.hMul Real Real Real qz0 qz31 (Real.cos qz154)) (@HMul.hMul Real Real Real qz0 qz31 (@Neg.neg Real Real.instNeg (Real.sin qz154)))) Bool.false 406117263063 1099511627776 6560468652497 19044640904708096 Bool.false 191195920323 1099511627776 6551772471237 19044640904708096 (BSN.cpow_neg_s_mk qz148 115476 1000 6 qz149 rfl)

noncomputable def ep644 := @Enclosure.Real.IsNear.mulLit_ff qz148 qz540 115476 1000 0 1 4034681531866359 2251799813685248 62500000017321 8660500000000000000 116477221143449917971 562949953421312000 1804312500500039949 2165125000000000000000 qz150 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 62500000017321 8660500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz309) Bool.false 33845361775666394038272 18889465931478580854784 1000000000277136 138568000000000000000 4034681531866359 2251799813685248 62500000017321 8660500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 212580 524288 24973259072661432 36028797018963968 138568 1000000000000000 rfl rfl rfl rfl (ep104 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep645 := nat_lit 2237593980624781286983914811807258435580991955781454245982707329095520978206720

noncomputable def ep646 := nat_lit 1209178916181868846109863910565242647107191827999044017815782113551262416896

noncomputable def ep647 := nat_lit 5858407469105370821111789489354285509854900621229905525354436500399662422818816

noncomputable def ep648 := BSN.sin_dyadic_bound_f 2428350216 2147483648 3 2 1048576 277407 ep645 ep187 ep646 ep647 ep189 ep646 948697 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2428350216) qz292 0 2 ep645 ep187 ep646 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2428350216) qz293 0 2 ep647 ep189 ep646 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz439 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 108477865) qz26)

noncomputable def ep649 := @Enclosure.Real.IsNear.cos_image qz154 qz439 Bool.false 108477865 524288 875 1048576 Bool.false 948697 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz154 Bool.false 116477221143449917971 562949953421312000 1804312500500039949 2165125000000000000000 108477865 524288 875 1048576 (ep644 rfl) rfl) (Enclosure.sfrac_false_div 108477865 524288) (BSN.cos_reduce3 qz439 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 85439977593542583255040) qz302) 226375608064910080 72057594037927936 Bool.false 948697 1048576 32 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q3 108477865 524288 226375608064910080 72057594037927936 32 85439977593542583255040 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 948697 1048576 85439977593542583255040 75557863725914323419136 2428350216 2147483648 277407 277136 (ep648 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep650 := nat_lit 1243645179865403767811557057186505905388154282913251933998311085992423326744576

noncomputable def ep651 := nat_lit 3728517181763847565742451443738387230870248465083757713959301693750167455399936

noncomputable def ep652 := BSN.cos_dyadic_bound_f 2428350216 2147483648 3 2 1048576 277407 ep650 ep155 ep646 ep651 ep158 ep646 446637 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2428350216) qz288 0 2 ep650 ep155 ep646 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2428350216) qz289 0 2 ep651 ep158 ep646 rfl rfl rfl rfl) rfl rfl

noncomputable def ep653 := @Enclosure.Real.IsNear.sin_image qz154 qz439 Bool.false 108477865 524288 875 1048576 Bool.true 446637 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz154 Bool.false 116477221143449917971 562949953421312000 1804312500500039949 2165125000000000000000 108477865 524288 875 1048576 (ep644 rfl) rfl) (Enclosure.sfrac_false_div 108477865 524288) (BSN.sin_reduce3 qz439 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 85439977593542583255040) qz302) 226375608064910080 72057594037927936 Bool.false 446637 1048576 32 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q3 108477865 524288 226375608064910080 72057594037927936 32 85439977593542583255040 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 446637 1048576 85439977593542583255040 75557863725914323419136 2428350216 2147483648 277407 277136 (ep652 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep654 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz31 (Real.cos qz154)) (@HMul.hMul Real Real Real qz0 qz31 (@Neg.neg Real Real.instNeg (Real.sin qz154))) Bool.false 406117263063 1099511627776 6560468652497 19044640904708096 Bool.false 191195920323 1099511627776 6551772471237 19044640904708096 (@Enclosure.Real.IsNear.mulLit_ff qz31 (Real.cos qz154) 428079 1048576 1 1048576 948697 1048576 15286947 18162384896 406117263063 1099511627776 6560468652497 19044640904708096 qz311 (@Enclosure.Real.IsNear.recentre' (Real.cos qz154) Bool.false 948697 1048576 122295576 145299079168 948697 1048576 15286947 18162384896 (ep649 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz31 (@Neg.neg Real Real.instNeg (Real.sin qz154)) 428079 1048576 1 1048576 446637 1048576 15286947 18162384896 191195920323 1099511627776 6551772471237 19044640904708096 qz311 (@Enclosure.Real.IsNear.neg (Real.sin qz154) Bool.true 446637 1048576 15286947 18162384896 (@Enclosure.Real.IsNear.recentre' (Real.sin qz154) Bool.true 446637 1048576 122295576 145299079168 446637 1048576 15286947 18162384896 (ep653 rfl rfl) rfl)) rfl)

noncomputable def ep655 := @ep589 406117263063 1099511627776 6560468652497 19044640904708096 Bool.false 191195920323 1099511627776 6551772471237 19044640904708096 Bool.false 775857364512910927200256 176409540589 274877906944 5296863651221 2380580113088512 Bool.false 587584142456526114652160 267202332205 549755813888 5296327600913 2380580113088512 (ep590 (BSN.head_sum_c_succ qz145 5 6 rfl rfl) (ep642 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep643 ep654) rfl rfl

noncomputable abbrev qz155 := (@HMul.hMul Real Real Real qz268 qz433 qz541)

noncomputable def ep656 := @Enclosure.Complex.IsNear.of_eq qz429 (Complex.mk (@HMul.hMul Real Real Real qz0 qz33 (Real.cos qz155)) (@HMul.hMul Real Real Real qz0 qz33 (@Neg.neg Real Real.instNeg (Real.sin qz155)))) Bool.false 8495226375 274877906944 3030049829631 9522320452354048 Bool.false 51773123725 137438953472 3038358055133 9522320452354048 (BSN.cpow_neg_s_mk qz148 115476 1000 7 qz149 rfl)

noncomputable def ep657 := @Enclosure.Real.IsNear.mulLit_ff qz148 qz541 115476 1000 0 1 4381796493761783 2251799813685248 62500000017321 8660500000000000000 126498082978408913427 562949953421312000 1804312500500039949 2165125000000000000000 qz150 (BSN.isNear_log_sfrac 7 1 4381796493761783 2251799813685248 62500000017321 8660500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz313) Bool.false 36757173121942042968064 18889465931478580854784 1000000000277136 138568000000000000000 4381796493761783 2251799813685248 62500000017321 8660500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 293399 524288 24973259072661432 36028797018963968 138568 1000000000000000 rfl rfl rfl rfl (ep115 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep658 := BSN.sin_dyadic_bound_f 175791983 2147483648 1 0 1048576 277407 0 1 1 0 1 1 85740 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 175791983) qz292 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 175791983) qz293 0 0 rfl) rfl rfl

noncomputable abbrev qz440 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14726315) (@Nat.cast Real Real.instNatCast 65536))

noncomputable def ep659 := @Enclosure.Real.IsNear.cos_image qz155 qz440 Bool.false 14726315 65536 875 1048576 Bool.false 85740 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz155 Bool.false 126498082978408913427 562949953421312000 1804312500500039949 2165125000000000000000 14726315 65536 875 1048576 (ep657 rfl) rfl) (Enclosure.sfrac_false_div 14726315 65536) (BSN.cos_reduce3 qz440 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 773141318999044259840) qz306) 226375608064910080 72057594037927936 Bool.false 85740 1048576 35 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q3 14726315 65536 226375608064910080 72057594037927936 35 773141318999044259840 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 85740 1048576 773141318999044259840 9444732965739290427392 175791983 2147483648 277407 277136 (ep658 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep660 := nat_lit 954984363500728204465037111699521

noncomputable def ep661 := BSN.cos_dyadic_bound_f 175791983 2147483648 2 1 1048576 277407 ep660 ep71 ep660 ep660 ep72 ep660 1045064 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 175791983) qz288 0 1 ep660 ep71 ep660 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 175791983) qz289 0 1 ep660 ep72 ep660 rfl rfl rfl rfl) rfl rfl

noncomputable def ep662 := @Enclosure.Real.IsNear.sin_image qz155 qz440 Bool.false 14726315 65536 875 1048576 Bool.true 1045064 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz155 Bool.false 126498082978408913427 562949953421312000 1804312500500039949 2165125000000000000000 14726315 65536 875 1048576 (ep657 rfl) rfl) (Enclosure.sfrac_false_div 14726315 65536) (BSN.sin_reduce3 qz440 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 773141318999044259840) qz306) 226375608064910080 72057594037927936 Bool.false 1045064 1048576 35 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q3 14726315 65536 226375608064910080 72057594037927936 35 773141318999044259840 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1045064 1048576 773141318999044259840 9444732965739290427392 175791983 2147483648 277407 277136 (ep661 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep663 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz33 (Real.cos qz155)) (@HMul.hMul Real Real Real qz0 qz33 (@Neg.neg Real Real.instNeg (Real.sin qz155))) Bool.false 8495226375 274877906944 3030049829631 9522320452354048 Bool.false 51773123725 137438953472 3038358055133 9522320452354048 (@Enclosure.Real.IsNear.mulLit_ff qz33 (Real.cos qz155) 396325 1048576 1 1048576 21435 262144 15286947 18162384896 8495226375 274877906944 3030049829631 9522320452354048 qz315 (@Enclosure.Real.IsNear.recentre' (Real.cos qz155) Bool.false 85740 1048576 122295576 145299079168 21435 262144 15286947 18162384896 (ep659 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz33 (@Neg.neg Real Real.instNeg (Real.sin qz155)) 396325 1048576 1 1048576 130633 131072 15286947 18162384896 51773123725 137438953472 3038358055133 9522320452354048 qz315 (@Enclosure.Real.IsNear.neg (Real.sin qz155) Bool.true 130633 131072 15286947 18162384896 (@Enclosure.Real.IsNear.recentre' (Real.sin qz155) Bool.true 1045064 1048576 122295576 145299079168 130633 131072 15286947 18162384896 (ep662 rfl rfl) rfl)) rfl)

noncomputable def ep664 := @ep587 8495226375 274877906944 3030049829631 9522320452354048 Bool.false 51773123725 137438953472 3038358055133 9522320452354048 Bool.false 50826235327032397398016 46226191741 68719476736 24217504434515 9522320452354048 Bool.false 65186584674494379458560 474294827105 549755813888 24223668458785 9522320452354048 (ep588 (BSN.head_sum_c_succ qz145 6 7 rfl rfl) (ep655 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep656 ep663) rfl rfl

noncomputable abbrev qz156 := (@HMul.hMul Real Real Real qz268 qz433 qz542)

noncomputable def ep665 := @Enclosure.Complex.IsNear.of_eq qz428 (Complex.mk (@HMul.hMul Real Real Real qz0 qz35 (Real.cos qz156)) (@HMul.hMul Real Real Real qz0 qz35 (@Neg.neg Real Real.instNeg (Real.sin qz156)))) Bool.false 79608062345 1099511627776 5671018712351 19044640904708096 Bool.true 23781024869 68719476736 710634591301 2380580113088512 (BSN.cpow_neg_s_mk qz148 115476 1000 8 qz149 rfl)

noncomputable def ep666 := @Enclosure.Real.IsNear.mulLit_ff qz148 qz542 115476 1000 0 1 9364972152248037 4503599627370496 125000000051963 17321000000000000000 270357381063248580153 1125899906842624000 3608625001500119847 4330250000000000000000 qz150 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 125000000051963 17321000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz317) Bool.false 39279540158062550581248 18889465931478580854784 1000000000415704 138568000000000000000 9364972152248037 4503599627370496 125000000051963 17321000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 524288 24973259072661432 36028797018963968 138568 1000000000000000 rfl rfl rfl rfl (ep126 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep667 := nat_lit 2639981307443859030916853871653467694305161969202021312581622063296452493377536

noncomputable def ep668 := nat_lit 5436927596118708343296962307125386530408488201206840748978532172996458643456

noncomputable def ep669 := nat_lit 7909070067139339676063967690346152309854668931203650256246909125543364562845696

noncomputable def ep670 := BSN.cos_dyadic_bound_f 2930347964 2147483648 3 2 1048576 277407 ep667 ep155 ep668 ep669 ep158 ep668 214735 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2930347964) qz288 0 2 ep667 ep155 ep668 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2930347964) qz289 0 2 ep669 ep158 ep668 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz441 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 62947483) qz543)

noncomputable def ep671 := @Enclosure.Real.IsNear.cos_image qz156 qz441 Bool.false 62947483 262144 875 1048576 Bool.false 214735 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz156 Bool.false 270357381063248580153 1125899906842624000 3608625001500119847 4330250000000000000000 62947483 262144 875 1048576 (ep666 rfl) rfl) (Enclosure.sfrac_false_div 62947483 262144) (BSN.cos_reduce0 qz441 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 51551226560436435419136) qz319) 226375608064910080 72057594037927936 Bool.false 214735 1048576 38 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q0 62947483 262144 226375608064910080 72057594037927936 38 51551226560436435419136 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 214735 1048576 51551226560436435419136 37778931862957161709568 2930347964 2147483648 277407 277136 (ep670 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep672 := nat_lit 4747616811322051288975699399130541540524964754002672890047736888195217321164800

noncomputable def ep673 := nat_lit 12425431861164037371904350963511310551754246327205046493674298036040717765246976

noncomputable def ep674 := BSN.sin_dyadic_bound_f 2930347964 2147483648 3 2 1048576 277407 ep672 ep187 ep668 ep673 ep189 ep668 1026352 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2930347964) qz292 0 2 ep672 ep187 ep668 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2930347964) qz293 0 2 ep673 ep189 ep668 rfl rfl rfl rfl) rfl rfl

noncomputable def ep675 := @Enclosure.Real.IsNear.sin_image qz156 qz441 Bool.false 62947483 262144 875 1048576 Bool.false 1026352 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz156 Bool.false 270357381063248580153 1125899906842624000 3608625001500119847 4330250000000000000000 62947483 262144 875 1048576 (ep666 rfl) rfl) (Enclosure.sfrac_false_div 62947483 262144) (BSN.sin_reduce0 qz441 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 51551226560436435419136) qz319) 226375608064910080 72057594037927936 Bool.false 1026352 1048576 38 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q0 62947483 262144 226375608064910080 72057594037927936 38 51551226560436435419136 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1026352 1048576 51551226560436435419136 37778931862957161709568 2930347964 2147483648 277407 277136 (ep674 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep676 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz35 (Real.cos qz156)) (@HMul.hMul Real Real Real qz0 qz35 (@Neg.neg Real Real.instNeg (Real.sin qz156))) Bool.false 79608062345 1099511627776 5671018712351 19044640904708096 Bool.true 23781024869 68719476736 710634591301 2380580113088512 (@Enclosure.Real.IsNear.mulLit_ff qz35 (Real.cos qz156) 370727 1048576 1 1048576 214735 1048576 15286947 18162384896 79608062345 1099511627776 5671018712351 19044640904708096 qz320 (@Enclosure.Real.IsNear.recentre' (Real.cos qz156) Bool.false 214735 1048576 122295576 145299079168 214735 1048576 15286947 18162384896 (ep671 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz35 (@Neg.neg Real Real.instNeg (Real.sin qz156)) 370727 1048576 1 1048576 64147 65536 15286947 18162384896 23781024869 68719476736 710634591301 2380580113088512 qz320 (@Enclosure.Real.IsNear.neg (Real.sin qz156) Bool.false 64147 65536 15286947 18162384896 (@Enclosure.Real.IsNear.recentre' (Real.sin qz156) Bool.false 1026352 1048576 122295576 145299079168 64147 65536 15286947 18162384896 (ep675 rfl rfl) rfl)) rfl)

noncomputable def ep677 := @ep585 79608062345 1099511627776 5671018712351 19044640904708096 Bool.true 23781024869 68719476736 710634591301 2380580113088512 Bool.false 56296859715347662503936 819227130201 1099511627776 54106027581381 19044640904708096 Bool.false 19519535655299326148608 284046628153 549755813888 27066206823989 9522320452354048 (ep586 (BSN.head_sum_c_succ qz145 7 8 rfl rfl) (ep664 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep665 ep676) rfl rfl

theorem EMRow36.d11 : Enclosure.Complex.IsNear qz144 Bool.false 819227130201 1099511627776 54106027581381 19044640904708096 Bool.false 284046628153 549755813888 27066206823989 9522320452354048 := ep584 (BSN.head_sum_c_succ qz145 8 9 rfl rfl) (ep677 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz157 := (BSN.headSumC qz426 17)

noncomputable abbrev qz158 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 16) qz427)

noncomputable def ep678 := @Enclosure.Complex.IsNear.of_eq qz157 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz145 16) qz158) Bool.false 750794019435 1099511627776 90929008505687 19044640904708096 Bool.false 265414407243 1099511627776 90949250692337 19044640904708096

noncomputable def ep679 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz145 16) qz158 Bool.false 121561333281 274877906944 43452073558251 9522320452354048 Bool.false 23846705553 137438953472 21734234349419 4761160226177024 Bool.false

noncomputable abbrev qz159 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 15) qz427)

noncomputable def ep680 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz145 16) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz145 15) qz159) Bool.false 121561333281 274877906944 43452073558251 9522320452354048 Bool.false 23846705553 137438953472 21734234349419 4761160226177024

noncomputable def ep681 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz145 15) qz159 Bool.false 450535948929 1099511627776 82763043958533 19044640904708096 Bool.true 90863868603 1099511627776 82780100674715 19044640904708096 Bool.false

noncomputable abbrev qz160 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 14) qz427)

noncomputable def ep682 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz145 15) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz145 14) qz160) Bool.false 450535948929 1099511627776 82763043958533 19044640904708096 Bool.true 90863868603 1099511627776 82780100674715 19044640904708096

noncomputable def ep683 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz145 14) qz160 Bool.false 23261454087 34359738368 4904103880069 1190290056544256 Bool.true 23679092281 274877906944 9812580186773 2380580113088512 Bool.true

noncomputable abbrev qz161 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 13) qz427)

noncomputable def ep684 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz145 14) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz145 13) qz161) Bool.false 23261454087 34359738368 4904103880069 1190290056544256 Bool.true 23679092281 274877906944 9812580186773 2380580113088512

noncomputable def ep685 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz145 13) qz161 Bool.false 137527390749 274877906944 18503329675851 4761160226177024 Bool.false 140354989307 1099511627776 74045867270023 19044640904708096 Bool.false

noncomputable abbrev qz162 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 12) qz427)

noncomputable def ep686 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz145 13) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz145 12) qz162) Bool.false 137527390749 274877906944 18503329675851 4761160226177024 Bool.false 140354989307 1099511627776 74045867270023 19044640904708096

noncomputable def ep687 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz145 12) qz162 Bool.false 176178165285 274877906944 34688571842503 9522320452354048 Bool.true 34211838967 274877906944 34701338424121 9522320452354048 Bool.true

noncomputable abbrev qz163 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 11) qz427)

noncomputable def ep688 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz145 12) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz145 11) qz163) Bool.false 176178165285 274877906944 34688571842503 9522320452354048 Bool.true 34211838967 274877906944 34701338424121 9522320452354048

noncomputable def ep689 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz145 11) qz163 Bool.false 404647103969 1099511627776 64533089855035 19044640904708096 Bool.false 4086898493 1099511627776 64567341197201 19044640904708096 Bool.false

noncomputable abbrev qz164 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 10) qz427)

noncomputable def ep690 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz145 11) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz145 10) qz164) Bool.false 404647103969 1099511627776 64533089855035 19044640904708096 Bool.false 4086898493 1099511627776 64567341197201 19044640904708096

noncomputable def ep691 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz145 10) qz164 Bool.false 274578950413 549755813888 14864135595583 4761160226177024 Bool.false 160164482403 549755813888 29740911554657 9522320452354048 Bool.true

noncomputable abbrev qz442 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 9) qz146)

noncomputable def ep692 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz145 10) (@HAdd.hAdd Complex Complex Complex qz4 qz144 qz442) Bool.false 274578950413 549755813888 14864135595583 4761160226177024 Bool.false 160164482403 549755813888 29740911554657 9522320452354048

noncomputable def ep693 := @Enclosure.Complex.IsNear.addLitP qz144 qz442 Bool.false 819227130201 1099511627776 54106027581381 19044640904708096 Bool.false 284046628153 549755813888 27066206823989 9522320452354048 Bool.true

noncomputable abbrev qz165 := (@HMul.hMul Real Real Real qz268 qz433 qz544)

noncomputable def ep694 := @Enclosure.Complex.IsNear.of_eq qz442 (Complex.mk (@HMul.hMul Real Real Real qz0 qz45 (Real.cos qz165)) (@HMul.hMul Real Real Real qz0 qz45 (@Neg.neg Real Real.instNeg (Real.sin qz165)))) Bool.true 270069229375 1099511627776 5350514800951 19044640904708096 Bool.true 61941072875 274877906944 668676182667 2380580113088512 (BSN.cpow_neg_s_mk qz148 115476 1000 9 qz149 rfl)

noncomputable def ep695 := @Enclosure.Real.IsNear.mulLit_ff qz148 qz544 115476 1000 0 1 9895417793173221 4503599627370496 125000000051963 17321000000000000000 285670816271117717049 1125899906842624000 3608625001500119847 4330250000000000000000 qz150 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 125000000051963 17321000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz323) Bool.false 41504390431577613533184 18889465931478580854784 1000000000415704 138568000000000000000 9895417793173221 4503599627370496 125000000051963 17321000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 61752 524288 24973259072661432 36028797018963968 138568 1000000000000000 rfl rfl rfl rfl (ep152 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep696 := nat_lit 10017863410861996109142954800033304576

noncomputable def ep697 := BSN.sin_dyadic_bound_f 1779073032 2147483648 2 1 1048576 277407 ep696 ep67 ep696 ep696 ep68 ep696 772675 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1779073032) qz292 0 1 ep696 ep67 ep696 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1779073032) qz293 0 1 ep696 ep68 ep696 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz443 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8314115) (@Nat.cast Real Real.instNatCast 32768))

noncomputable def ep698 := @Enclosure.Real.IsNear.cos_image qz165 qz443 Bool.false 8314115 32768 437 524288 Bool.true 772675 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz165 Bool.false 285670816271117717049 1125899906842624000 3608625001500119847 4330250000000000000000 8314115 32768 437 524288 (ep695 rfl) rfl) (Enclosure.sfrac_false_div 8314115 32768) (BSN.cos_reduce1 qz443 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3912222972867709501440) (@Nat.cast Real Real.instNatCast 4722366482869645213696)) 226375608064910080 72057594037927936 Bool.false 772675 1048576 40 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q1 8314115 32768 226375608064910080 72057594037927936 40 3912222972867709501440 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 772675 1048576 3912222972867709501440 4722366482869645213696 1779073032 2147483648 277407 277136 (ep697 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep699 := nat_lit 358035096245891204136815929154395400999984237745959371665782829630140926918656

noncomputable def ep700 := nat_lit 100357587318687546663434183993252610230395527624700351666003438794782539776

noncomputable def ep701 := nat_lit 1073904573563036237317120919095199697779491922182628714294016482012833215676416

noncomputable def ep702 := BSN.cos_dyadic_bound_f 1779073032 2147483648 3 2 1048576 277407 ep699 ep155 ep700 ep701 ep158 ep700 708860 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1779073032) qz288 0 2 ep699 ep155 ep700 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1779073032) qz289 0 2 ep701 ep158 ep700 rfl rfl rfl rfl) rfl rfl

noncomputable def ep703 := @Enclosure.Real.IsNear.sin_image qz165 qz443 Bool.false 8314115 32768 437 524288 Bool.false 708860 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz165 Bool.false 285670816271117717049 1125899906842624000 3608625001500119847 4330250000000000000000 8314115 32768 437 524288 (ep695 rfl) rfl) (Enclosure.sfrac_false_div 8314115 32768) (BSN.sin_reduce1 qz443 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3912222972867709501440) (@Nat.cast Real Real.instNatCast 4722366482869645213696)) 226375608064910080 72057594037927936 Bool.false 708860 1048576 40 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q1 8314115 32768 226375608064910080 72057594037927936 40 3912222972867709501440 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 708860 1048576 3912222972867709501440 4722366482869645213696 1779073032 2147483648 277407 277136 (ep702 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep704 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz45 (Real.cos qz165)) (@HMul.hMul Real Real Real qz0 qz45 (@Neg.neg Real Real.instNeg (Real.sin qz165))) Bool.true 270069229375 1099511627776 5350514800951 19044640904708096 Bool.true 61941072875 274877906944 668676182667 2380580113088512 (@Enclosure.Real.IsNear.mulLit_ft qz45 (Real.cos qz165) 349525 1048576 1 1048576 772675 1048576 7634813 9081192448 270069229375 1099511627776 5350514800951 19044640904708096 qz325 (@Enclosure.Real.IsNear.recentre' (Real.cos qz165) Bool.true 772675 1048576 61078504 72649539584 772675 1048576 7634813 9081192448 (ep698 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz45 (@Neg.neg Real Real.instNeg (Real.sin qz165)) 349525 1048576 1 1048576 177215 262144 7634813 9081192448 61941072875 274877906944 668676182667 2380580113088512 qz325 (@Enclosure.Real.IsNear.neg (Real.sin qz165) Bool.false 177215 262144 7634813 9081192448 (@Enclosure.Real.IsNear.recentre' (Real.sin qz165) Bool.false 708860 1048576 61078504 72649539584 177215 262144 7634813 9081192448 (ep703 rfl rfl) rfl)) rfl)

noncomputable def ep705 := @ep693 270069229375 1099511627776 5350514800951 19044640904708096 Bool.true 61941072875 274877906944 668676182667 2380580113088512 Bool.false 603805497443246434942976 274578950413 549755813888 14864135595583 4761160226177024 Bool.false 44025677689705759506432 160164482403 549755813888 29740911554657 9522320452354048 EMRow36.d11 (ep694 ep704) rfl rfl

noncomputable abbrev qz166 := (@HMul.hMul Real Real Real qz268 qz433 qz545)

noncomputable def ep706 := @Enclosure.Complex.IsNear.of_eq qz164 (Complex.mk (@HMul.hMul Real Real Real qz0 qz47 (Real.cos qz166)) (@HMul.hMul Real Real Real qz0 qz47 (@Neg.neg Real Real.instNeg (Real.sin qz166)))) Bool.true 144510796857 1099511627776 5076547472703 19044640904708096 Bool.true 316242066313 1099511627776 5085518087887 19044640904708096 (BSN.cpow_neg_s_mk qz148 115476 1000 10 qz149 rfl)

noncomputable def ep707 := @Enclosure.Real.IsNear.mulLit_ff qz148 qz545 115476 1000 0 1 10369917190100709 4503599627370496 125000000051963 17321000000000000000 299369139361017368121 1125899906842624000 3608625001500119847 4330250000000000000000 qz150 (BSN.isNear_log_sfrac 10 1 10369917190100709 4503599627370496 125000000051963 17321000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz327) Bool.false 43494585150108164161536 18889465931478580854784 1000000000415704 138568000000000000000 10369917190100709 4503599627370496 125000000051963 17321000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 116991 524288 24973259072661432 36028797018963968 138568 1000000000000000 rfl rfl rfl rfl (ep168 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep708 := nat_lit 717871613760411557268812437323296161

noncomputable def ep709 := BSN.sin_dyadic_bound_f 920474359 2147483648 2 1 1048576 277407 ep708 ep67 ep708 ep708 ep68 ep708 435813 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 920474359) qz292 0 1 ep708 ep67 ep708 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 920474359) qz293 0 1 ep708 ep68 ep708 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz444 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 278809237) qz16)

noncomputable def ep710 := @Enclosure.Real.IsNear.cos_image qz166 qz444 Bool.false 278809237 1048576 875 1048576 Bool.true 435813 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz166 Bool.false 299369139361017368121 1125899906842624000 3608625001500119847 4330250000000000000000 278809237 1048576 875 1048576 (ep707 rfl) rfl) (Enclosure.sfrac_false_div 278809237 1048576) (BSN.cos_reduce1 qz444 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 64772624757049098502144) qz19) 226375608064910080 72057594037927936 Bool.false 435813 1048576 42 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q1 278809237 1048576 226375608064910080 72057594037927936 42 64772624757049098502144 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 435813 1048576 64772624757049098502144 151115727451828646838272 920474359 2147483648 277407 277136 (ep709 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep711 := BSN.cos_dyadic_bound_f 920474359 2147483648 2 1 1048576 277407 ep708 ep71 ep708 ep708 ep72 ep708 953717 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 920474359) qz288 0 1 ep708 ep71 ep708 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 920474359) qz289 0 1 ep708 ep72 ep708 rfl rfl rfl rfl) rfl rfl

noncomputable def ep712 := @Enclosure.Real.IsNear.sin_image qz166 qz444 Bool.false 278809237 1048576 875 1048576 Bool.false 953717 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz166 Bool.false 299369139361017368121 1125899906842624000 3608625001500119847 4330250000000000000000 278809237 1048576 875 1048576 (ep707 rfl) rfl) (Enclosure.sfrac_false_div 278809237 1048576) (BSN.sin_reduce1 qz444 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 64772624757049098502144) qz19) 226375608064910080 72057594037927936 Bool.false 953717 1048576 42 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q1 278809237 1048576 226375608064910080 72057594037927936 42 64772624757049098502144 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 953717 1048576 64772624757049098502144 151115727451828646838272 920474359 2147483648 277407 277136 (ep711 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep713 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz47 (Real.cos qz166)) (@HMul.hMul Real Real Real qz0 qz47 (@Neg.neg Real Real.instNeg (Real.sin qz166))) Bool.true 144510796857 1099511627776 5076547472703 19044640904708096 Bool.true 316242066313 1099511627776 5085518087887 19044640904708096 (@Enclosure.Real.IsNear.mulLit_ft qz47 (Real.cos qz166) 331589 1048576 1 1048576 435813 1048576 15286947 18162384896 144510796857 1099511627776 5076547472703 19044640904708096 qz329 (@Enclosure.Real.IsNear.recentre' (Real.cos qz166) Bool.true 435813 1048576 122295576 145299079168 435813 1048576 15286947 18162384896 (ep710 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz47 (@Neg.neg Real Real.instNeg (Real.sin qz166)) 331589 1048576 1 1048576 953717 1048576 15286947 18162384896 316242066313 1099511627776 5085518087887 19044640904708096 qz329 (@Enclosure.Real.IsNear.neg (Real.sin qz166) Bool.false 953717 1048576 15286947 18162384896 (@Enclosure.Real.IsNear.recentre' (Real.sin qz166) Bool.false 953717 1048576 122295576 145299079168 953717 1048576 15286947 18162384896 (ep712 rfl rfl) rfl)) rfl)

noncomputable def ep714 := @ep691 144510796857 1099511627776 5076547472703 19044640904708096 Bool.true 316242066313 1099511627776 5085518087887 19044640904708096 Bool.false 222457097979899750121472 404647103969 1099511627776 64533089855035 19044640904708096 Bool.false 2246796207296855670784 4086898493 1099511627776 64567341197201 19044640904708096 (ep692 (BSN.head_sum_c_succ qz145 9 10 rfl rfl) (ep705 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep706 ep713) rfl rfl

noncomputable abbrev qz167 := (@HMul.hMul Real Real Real qz268 qz433 qz546)

noncomputable def ep715 := @Enclosure.Complex.IsNear.of_eq qz163 (Complex.mk (@HMul.hMul Real Real Real qz0 qz49 (Real.cos qz167)) (@HMul.hMul Real Real Real qz0 qz49 (@Neg.neg Real Real.instNeg (Real.sin qz167)))) Bool.false 300065557171 1099511627776 4844053829971 19044640904708096 Bool.true 140934254361 1099511627776 4835335651041 19044640904708096 (BSN.cpow_neg_s_mk qz148 115476 1000 11 qz149 rfl)

noncomputable def ep716 := @Enclosure.Real.IsNear.mulLit_ff qz148 qz546 115476 1000 0 1 10799156221662949 4503599627370496 125000000051963 17321000000000000000 311760840963187674681 1125899906842624000 3608625001500119847 4330250000000000000000 qz150 (BSN.isNear_log_sfrac 11 1 10799156221662949 4503599627370496 125000000051963 17321000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz331) Bool.false 45294944137145793642496 18889465931478580854784 1000000000415704 138568000000000000000 10799156221662949 4503599627370496 125000000051963 17321000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 166961 524288 24973259072661432 36028797018963968 138568 1000000000000000 rfl rfl rfl rfl (ep179 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep717 := nat_lit 790611622847980475366322091810466721

noncomputable def ep718 := BSN.cos_dyadic_bound_f 942954633 2147483648 2 1 1048576 277407 ep717 ep71 ep717 ep717 ep72 ep717 949103 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 942954633) qz288 0 1 ep717 ep71 ep717 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 942954633) qz289 0 1 ep717 ep72 ep717 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz445 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 290349909) qz16)

noncomputable def ep719 := @Enclosure.Real.IsNear.cos_image qz167 qz445 Bool.false 290349909 1048576 437 524288 Bool.false 949103 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz167 Bool.false 311760840963187674681 1125899906842624000 3608625001500119847 4330250000000000000000 290349909 1048576 437 524288 (ep716 rfl) rfl) (Enclosure.sfrac_false_div 290349909 1048576) (BSN.cos_reduce0 qz445 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 66354533342914772205568) qz19) 226375608064910080 72057594037927936 Bool.false 949103 1048576 44 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q0 290349909 1048576 226375608064910080 72057594037927936 44 66354533342914772205568 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 949103 1048576 66354533342914772205568 151115727451828646838272 942954633 2147483648 277407 277136 (ep718 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep720 := BSN.sin_dyadic_bound_f 942954633 2147483648 2 1 1048576 277407 ep717 ep67 ep717 ep717 ep68 ep717 445773 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 942954633) qz292 0 1 ep717 ep67 ep717 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 942954633) qz293 0 1 ep717 ep68 ep717 rfl rfl rfl rfl) rfl rfl

noncomputable def ep721 := @Enclosure.Real.IsNear.sin_image qz167 qz445 Bool.false 290349909 1048576 437 524288 Bool.false 445773 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz167 Bool.false 311760840963187674681 1125899906842624000 3608625001500119847 4330250000000000000000 290349909 1048576 437 524288 (ep716 rfl) rfl) (Enclosure.sfrac_false_div 290349909 1048576) (BSN.sin_reduce0 qz445 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 66354533342914772205568) qz19) 226375608064910080 72057594037927936 Bool.false 445773 1048576 44 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q0 290349909 1048576 226375608064910080 72057594037927936 44 66354533342914772205568 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 445773 1048576 66354533342914772205568 151115727451828646838272 942954633 2147483648 277407 277136 (ep720 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep722 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz49 (Real.cos qz167)) (@HMul.hMul Real Real Real qz0 qz49 (@Neg.neg Real Real.instNeg (Real.sin qz167))) Bool.false 300065557171 1099511627776 4844053829971 19044640904708096 Bool.true 140934254361 1099511627776 4835335651041 19044640904708096 (@Enclosure.Real.IsNear.mulLit_ff qz49 (Real.cos qz167) 316157 1048576 1 1048576 949103 1048576 7634813 9081192448 300065557171 1099511627776 4844053829971 19044640904708096 qz333 (@Enclosure.Real.IsNear.recentre' (Real.cos qz167) Bool.false 949103 1048576 61078504 72649539584 949103 1048576 7634813 9081192448 (ep719 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz49 (@Neg.neg Real Real.instNeg (Real.sin qz167)) 316157 1048576 1 1048576 445773 1048576 7634813 9081192448 140934254361 1099511627776 4835335651041 19044640904708096 qz333 (@Enclosure.Real.IsNear.neg (Real.sin qz167) Bool.false 445773 1048576 7634813 9081192448 (@Enclosure.Real.IsNear.recentre' (Real.sin qz167) Bool.false 445773 1048576 61078504 72649539584 445773 1048576 7634813 9081192448 (ep721 rfl rfl) rfl)) rfl)

noncomputable def ep723 := @ep689 300065557171 1099511627776 4844053829971 19044640904708096 Bool.true 140934254361 1099511627776 4835335651041 19044640904708096 Bool.false 774839765164398099824640 176178165285 274877906944 34688571842503 9522320452354048 Bool.true 150465259007266225389568 34211838967 274877906944 34701338424121 9522320452354048 (ep690 (BSN.head_sum_c_succ qz145 10 11 rfl rfl) (ep714 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep715 ep722) rfl rfl

noncomputable abbrev qz168 := (@HMul.hMul Real Real Real qz268 qz433 qz547)

noncomputable def ep724 := @Enclosure.Complex.IsNear.of_eq qz162 (Complex.mk (@HMul.hMul Real Real Real qz0 qz51 (Real.cos qz168)) (@HMul.hMul Real Real Real qz0 qz51 (@Neg.neg Real Real.instNeg (Real.sin qz168)))) Bool.true 4831346817 34359738368 2318087509199 9522320452354048 Bool.false 277202345175 1099511627776 4643190421781 19044640904708096 (BSN.cpow_neg_s_mk qz148 115476 1000 12 qz149 rfl)

noncomputable def ep725 := @Enclosure.Real.IsNear.mulLit_ff qz148 qz547 115476 1000 0 1 11191020447815397 4503599627370496 125000000051963 17321000000000000000 323073569307982695993 1125899906842624000 3608625001500119847 4330250000000000000000 qz150 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 125000000051963 17321000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz335) Bool.false 46938541828353910898688 18889465931478580854784 1000000000415704 138568000000000000000 11191020447815397 4503599627370496 125000000051963 17321000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 212580 524288 24973259072661432 36028797018963968 138568 1000000000000000 rfl rfl rfl rfl (ep196 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep726 := nat_lit 967478094873269648226615863008207361955581056757644162338112058209368256086016

noncomputable def ep727 := nat_lit 732094728408916858200509465790241011292449741521992068841262376886154100736

noncomputable def ep728 := nat_lit 2900970095162991110963446570093041603844158270789888502876653649874332460056576

noncomputable def ep729 := BSN.cos_dyadic_bound_f 2280714428 2147483648 3 2 1048576 277407 ep726 ep155 ep727 ep728 ep158 ep727 510752 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2280714428) qz288 0 2 ep726 ep155 ep727 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2280714428) qz289 0 2 ep728 ep158 ep727 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz446 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 75221427) qz543)

noncomputable def ep730 := @Enclosure.Real.IsNear.cos_image qz168 qz446 Bool.false 75221427 262144 875 1048576 Bool.true 510752 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz168 Bool.false 323073569307982695993 1125899906842624000 3608625001500119847 4330250000000000000000 75221427 262144 875 1048576 (ep725 rfl) rfl) (Enclosure.sfrac_false_div 75221427 262144) (BSN.cos_reduce2 qz446 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 40122752535925520072704) qz319) 226375608064910080 72057594037927936 Bool.false 510752 1048576 45 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q2 75221427 262144 226375608064910080 72057594037927936 45 40122752535925520072704 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 510752 1048576 40122752535925520072704 37778931862957161709568 2280714428 2147483648 277407 277136 (ep729 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep731 := nat_lit 1740874894989158233321348145842141058711011942370541898553528694875353937674240

noncomputable def ep732 := nat_lit 4558248952554180936166444319022899525462938739960383651909689299872873206317056

noncomputable def ep733 := BSN.sin_dyadic_bound_f 2280714428 2147483648 3 2 1048576 277407 ep731 ep187 ep727 ep732 ep189 ep727 915775 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2280714428) qz292 0 2 ep731 ep187 ep727 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2280714428) qz293 0 2 ep732 ep189 ep727 rfl rfl rfl rfl) rfl rfl

noncomputable def ep734 := @Enclosure.Real.IsNear.sin_image qz168 qz446 Bool.false 75221427 262144 875 1048576 Bool.true 915775 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz168 Bool.false 323073569307982695993 1125899906842624000 3608625001500119847 4330250000000000000000 75221427 262144 875 1048576 (ep725 rfl) rfl) (Enclosure.sfrac_false_div 75221427 262144) (BSN.sin_reduce2 qz446 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 40122752535925520072704) qz319) 226375608064910080 72057594037927936 Bool.false 915775 1048576 45 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q2 75221427 262144 226375608064910080 72057594037927936 45 40122752535925520072704 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 915775 1048576 40122752535925520072704 37778931862957161709568 2280714428 2147483648 277407 277136 (ep733 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep735 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz51 (Real.cos qz168)) (@HMul.hMul Real Real Real qz0 qz51 (@Neg.neg Real Real.instNeg (Real.sin qz168))) Bool.true 4831346817 34359738368 2318087509199 9522320452354048 Bool.false 277202345175 1099511627776 4643190421781 19044640904708096 (@Enclosure.Real.IsNear.mulLit_ft qz51 (Real.cos qz168) 302697 1048576 1 1048576 15961 32768 15286947 18162384896 4831346817 34359738368 2318087509199 9522320452354048 qz337 (@Enclosure.Real.IsNear.recentre' (Real.cos qz168) Bool.true 510752 1048576 122295576 145299079168 15961 32768 15286947 18162384896 (ep730 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz51 (@Neg.neg Real Real.instNeg (Real.sin qz168)) 302697 1048576 1 1048576 915775 1048576 15286947 18162384896 277202345175 1099511627776 4643190421781 19044640904708096 qz337 (@Enclosure.Real.IsNear.neg (Real.sin qz168) Bool.true 915775 1048576 15286947 18162384896 (@Enclosure.Real.IsNear.recentre' (Real.sin qz168) Bool.true 915775 1048576 122295576 145299079168 915775 1048576 15286947 18162384896 (ep734 rfl rfl) rfl)) rfl)

noncomputable def ep736 := @ep687 4831346817 34359738368 2318087509199 9522320452354048 Bool.false 277202345175 1099511627776 4643190421781 19044640904708096 Bool.false 4725405164569343557632 137527390749 274877906944 18503329675851 4761160226177024 Bool.false 38580485689855661047808 140354989307 1099511627776 74045867270023 19044640904708096 (ep688 (BSN.head_sum_c_succ qz145 11 12 rfl rfl) (ep723 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep724 ep735) rfl rfl

noncomputable abbrev qz169 := (@HMul.hMul Real Real Real qz268 qz433 qz548)

noncomputable def ep737 := @Enclosure.Complex.IsNear.of_eq qz161 (Complex.mk (@HMul.hMul Real Real Real qz0 qz53 (Real.cos qz169)) (@HMul.hMul Real Real Real qz0 qz53 (@Neg.neg Real Real.instNeg (Real.sin qz169)))) Bool.false 48564241947 274877906944 1113085844425 4761160226177024 Bool.true 235071358431 1099511627776 4454774224161 19044640904708096 (BSN.cpow_neg_s_mk qz148 115476 1000 13 qz149 rfl)

noncomputable def ep738 := @Enclosure.Real.IsNear.mulLit_ff qz148 qz548 115476 1000 0 1 11551497052968677 4503599627370496 125000000051963 17321000000000000000 333480168422152736313 1125899906842624000 3608625001500119847 4330250000000000000000 qz150 (BSN.isNear_log_sfrac 13 1 11551497052968677 4503599627370496 125000000051963 17321000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz339) Bool.false 48450490295254733815808 18889465931478580854784 1000000000415704 138568000000000000000 11551497052968677 4503599627370496 125000000051963 17321000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 254545 524288 24973259072661432 36028797018963968 138568 1000000000000000 rfl rfl rfl rfl (ep207 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep739 := nat_lit 456234750445617800423717539383107676734921206249146453708495334928439365358721

noncomputable def ep740 := nat_lit 162932973874001508351069220028624402839001955119805070216402914236244186241

noncomputable def ep741 := nat_lit 1368378385389105398254450479709265781399085614837199750985053198956845607703681

noncomputable def ep742 := BSN.cos_dyadic_bound_f 1890171119 2147483648 3 2 1048576 277407 ep739 ep155 ep740 ep741 ep158 ep740 667956 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1890171119) qz288 0 2 ep739 ep155 ep740 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1890171119) qz289 0 2 ep741 ep158 ep740 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz447 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 310577609) qz16)

noncomputable def ep743 := @Enclosure.Real.IsNear.cos_image qz169 qz447 Bool.false 310577609 1048576 437 524288 Bool.false 667956 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz169 Bool.false 333480168422152736313 1125899906842624000 3608625001500119847 4330250000000000000000 310577609 1048576 437 524288 (ep738 rfl) rfl) (Enclosure.sfrac_false_div 310577609 1048576) (BSN.cos_reduce0 qz447 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 133008967957650769707008) qz19) 226375608064910080 72057594037927936 Bool.false 667956 1048576 47 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q0 310577609 1048576 226375608064910080 72057594037927936 47 133008967957650769707008 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 667956 1048576 133008967957650769707008 151115727451828646838272 1890171119 2147483648 277407 277136 (ep742 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep744 := nat_lit 12764520119221149488480049961695289921

noncomputable def ep745 := BSN.sin_dyadic_bound_f 1890171119 2147483648 2 1 1048576 277407 ep744 ep67 ep744 ep744 ep68 ep744 808297 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1890171119) qz292 0 1 ep744 ep67 ep744 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1890171119) qz293 0 1 ep744 ep68 ep744 rfl rfl rfl rfl) rfl rfl

noncomputable def ep746 := @Enclosure.Real.IsNear.sin_image qz169 qz447 Bool.false 310577609 1048576 437 524288 Bool.false 808297 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz169 Bool.false 333480168422152736313 1125899906842624000 3608625001500119847 4330250000000000000000 310577609 1048576 437 524288 (ep738 rfl) rfl) (Enclosure.sfrac_false_div 310577609 1048576) (BSN.sin_reduce0 qz447 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 133008967957650769707008) qz19) 226375608064910080 72057594037927936 Bool.false 808297 1048576 47 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q0 310577609 1048576 226375608064910080 72057594037927936 47 133008967957650769707008 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 808297 1048576 133008967957650769707008 151115727451828646838272 1890171119 2147483648 277407 277136 (ep745 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep747 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz53 (Real.cos qz169)) (@HMul.hMul Real Real Real qz0 qz53 (@Neg.neg Real Real.instNeg (Real.sin qz169))) Bool.false 48564241947 274877906944 1113085844425 4761160226177024 Bool.true 235071358431 1099511627776 4454774224161 19044640904708096 (@Enclosure.Real.IsNear.mulLit_ff qz53 (Real.cos qz169) 290823 1048576 1 1048576 166989 262144 7634813 9081192448 48564241947 274877906944 1113085844425 4761160226177024 qz341 (@Enclosure.Real.IsNear.recentre' (Real.cos qz169) Bool.false 667956 1048576 61078504 72649539584 166989 262144 7634813 9081192448 (ep743 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz53 (@Neg.neg Real Real.instNeg (Real.sin qz169)) 290823 1048576 1 1048576 808297 1048576 7634813 9081192448 235071358431 1099511627776 4454774224161 19044640904708096 qz341 (@Enclosure.Real.IsNear.neg (Real.sin qz169) Bool.false 808297 1048576 7634813 9081192448 (@Enclosure.Real.IsNear.recentre' (Real.sin qz169) Bool.false 808297 1048576 61078504 72649539584 808297 1048576 7634813 9081192448 (ep746 rfl rfl) rfl)) rfl)

noncomputable def ep748 := @ep685 48564241947 274877906944 1113085844425 4761160226177024 Bool.true 235071358431 1099511627776 4454774224161 19044640904708096 Bool.false 51152478495268115841024 23261454087 34359738368 4904103880069 1190290056544256 Bool.true 104141749192561707188224 23679092281 274877906944 9812580186773 2380580113088512 (ep686 (BSN.head_sum_c_succ qz145 12 13 rfl rfl) (ep736 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep737 ep747) rfl rfl

noncomputable abbrev qz170 := (@HMul.hMul Real Real Real qz268 qz433 qz549)

noncomputable def ep749 := @Enclosure.Complex.IsNear.of_eq qz160 (Complex.mk (@HMul.hMul Real Real Real qz0 qz55 (Real.cos qz170)) (@HMul.hMul Real Real Real qz0 qz55 (@Neg.neg Real Real.instNeg (Real.sin qz170)))) Bool.true 293830581855 1099511627776 4297381877429 19044640904708096 Bool.false 3852500521 1099511627776 4279459180531 19044640904708096 (BSN.cpow_neg_s_mk qz148 115476 1000 14 qz149 rfl)

noncomputable def ep750 := @Enclosure.Real.IsNear.mulLit_ff qz148 qz549 115476 1000 0 1 11885250371606245 4503599627370496 125000000051963 17321000000000000000 68623058595580137381 225179981368524800 3608625001500119847 4330250000000000000000 qz150 (BSN.isNear_log_sfrac 14 1 11885250371606245 4503599627370496 125000000051963 17321000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz343) Bool.false 49850353174629559828480 18889465931478580854784 1000000000415704 138568000000000000000 11885250371606245 4503599627370496 125000000051963 17321000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 293399 524288 24973259072661432 36028797018963968 138568 1000000000000000 rfl rfl rfl rfl (ep217 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep751 := BSN.cos_dyadic_bound_f 28156194 2147483648 1 0 1048576 277407 0 1 1 0 1 1 1048485 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 28156194) qz288 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 28156194) qz289 0 0 rfl) rfl rfl

noncomputable abbrev qz448 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 159775509) qz26)

noncomputable def ep752 := @Enclosure.Real.IsNear.cos_image qz170 qz448 Bool.false 159775509 524288 437 524288 Bool.true 1048485 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz170 Bool.false 68623058595580137381 225179981368524800 3608625001500119847 4330250000000000000000 159775509 524288 437 524288 (ep750 rfl) rfl) (Enclosure.sfrac_false_div 159775509 524288) (BSN.cos_reduce2 qz448 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 990658030300810969088) qz302) 226375608064910080 72057594037927936 Bool.false 1048485 1048576 48 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q2 159775509 524288 226375608064910080 72057594037927936 48 990658030300810969088 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1048485 1048576 990658030300810969088 75557863725914323419136 28156194 2147483648 277407 277136 (ep751 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep753 := BSN.sin_dyadic_bound_f 28156194 2147483648 1 0 1048576 277407 0 1 1 0 1 1 13747 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 28156194) qz292 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 28156194) qz293 0 0 rfl) rfl rfl

noncomputable def ep754 := @Enclosure.Real.IsNear.sin_image qz170 qz448 Bool.false 159775509 524288 437 524288 Bool.true 13747 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz170 Bool.false 68623058595580137381 225179981368524800 3608625001500119847 4330250000000000000000 159775509 524288 437 524288 (ep750 rfl) rfl) (Enclosure.sfrac_false_div 159775509 524288) (BSN.sin_reduce2 qz448 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 990658030300810969088) qz302) 226375608064910080 72057594037927936 Bool.false 13747 1048576 48 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q2 159775509 524288 226375608064910080 72057594037927936 48 990658030300810969088 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 13747 1048576 990658030300810969088 75557863725914323419136 28156194 2147483648 277407 277136 (ep753 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep755 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz55 (Real.cos qz170)) (@HMul.hMul Real Real Real qz0 qz55 (@Neg.neg Real Real.instNeg (Real.sin qz170))) Bool.true 293830581855 1099511627776 4297381877429 19044640904708096 Bool.false 3852500521 1099511627776 4279459180531 19044640904708096 (@Enclosure.Real.IsNear.mulLit_ft qz55 (Real.cos qz170) 280243 1048576 1 1048576 1048485 1048576 7634813 9081192448 293830581855 1099511627776 4297381877429 19044640904708096 qz345 (@Enclosure.Real.IsNear.recentre' (Real.cos qz170) Bool.true 1048485 1048576 61078504 72649539584 1048485 1048576 7634813 9081192448 (ep752 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz55 (@Neg.neg Real Real.instNeg (Real.sin qz170)) 280243 1048576 1 1048576 13747 1048576 7634813 9081192448 3852500521 1099511627776 4279459180531 19044640904708096 qz345 (@Enclosure.Real.IsNear.neg (Real.sin qz170) Bool.true 13747 1048576 7634813 9081192448 (@Enclosure.Real.IsNear.recentre' (Real.sin qz170) Bool.true 13747 1048576 61078504 72649539584 13747 1048576 7634813 9081192448 (ep754 rfl rfl) rfl)) rfl)

noncomputable def ep756 := @ep683 293830581855 1099511627776 4297381877429 19044640904708096 Bool.false 3852500521 1099511627776 4279459180531 19044640904708096 Bool.false 15480297330579049807872 450535948929 1099511627776 82763043958533 19044640904708096 Bool.true 24976470018427277279232 90863868603 1099511627776 82780100674715 19044640904708096 (ep684 (BSN.head_sum_c_succ qz145 13 14 rfl rfl) (ep748 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep749 ep755) rfl rfl

noncomputable abbrev qz171 := (@HMul.hMul Real Real Real qz268 qz433 qz550)

noncomputable def ep757 := @Enclosure.Complex.IsNear.of_eq qz159 (Complex.mk (@HMul.hMul Real Real Real qz0 qz57 (Real.cos qz171)) (@HMul.hMul Real Real Real qz0 qz57 (@Neg.neg Real Real.instNeg (Real.sin qz171)))) Bool.false 35709384195 1099511627776 4141103157969 19044640904708096 Bool.false 281637513027 1099511627776 4156836722961 19044640904708096 (BSN.cpow_neg_s_mk qz148 115476 1000 15 qz149 rfl)

noncomputable def ep758 := @Enclosure.Real.IsNear.mulLit_ff qz148 qz550 115476 1000 0 1 12195965485668069 4503599627370496 125000000051963 17321000000000000000 352085327605751483961 1125899906842624000 3608625001500119847 4330250000000000000000 qz150 (BSN.isNear_log_sfrac 15 1 12195965485668069 4503599627370496 125000000051963 17321000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz347) Bool.false 51153586820399524478976 18889465931478580854784 1000000000415704 138568000000000000000 12195965485668069 4503599627370496 125000000051963 17321000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 329571 524288 24973259072661432 36028797018963968 138568 1000000000000000 rfl rfl rfl rfl (ep228 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep759 := BSN.sin_dyadic_bound_f 270840824 2147483648 1 0 1048576 277407 0 1 1 0 1 1 131895 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 270840824) qz292 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 270840824) qz293 0 0 rfl) rfl rfl

noncomputable abbrev qz449 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 327905013) qz16)

noncomputable def ep760 := @Enclosure.Real.IsNear.cos_image qz171 qz449 Bool.false 327905013 1048576 875 1048576 Bool.false 131895 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz171 Bool.false 352085327605751483961 1125899906842624000 3608625001500119847 4330250000000000000000 327905013 1048576 875 1048576 (ep758 rfl) rfl) (Enclosure.sfrac_false_div 327905013 1048576) (BSN.cos_reduce3 qz449 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 19058728659005437116416) qz19) 226375608064910080 72057594037927936 Bool.false 131895 1048576 49 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q3 327905013 1048576 226375608064910080 72057594037927936 49 19058728659005437116416 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 131895 1048576 19058728659005437116416 151115727451828646838272 270840824 2147483648 277407 277136 (ep759 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep761 := nat_lit 5380919632912331052493016641048576

noncomputable def ep762 := BSN.cos_dyadic_bound_f 270840824 2147483648 2 1 1048576 277407 ep761 ep71 ep761 ep761 ep72 ep761 1040247 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 270840824) qz288 0 1 ep761 ep71 ep761 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 270840824) qz289 0 1 ep761 ep72 ep761 rfl rfl rfl rfl) rfl rfl

noncomputable def ep763 := @Enclosure.Real.IsNear.sin_image qz171 qz449 Bool.false 327905013 1048576 875 1048576 Bool.true 1040247 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz171 Bool.false 352085327605751483961 1125899906842624000 3608625001500119847 4330250000000000000000 327905013 1048576 875 1048576 (ep758 rfl) rfl) (Enclosure.sfrac_false_div 327905013 1048576) (BSN.sin_reduce3 qz449 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 19058728659005437116416) qz19) 226375608064910080 72057594037927936 Bool.false 1040247 1048576 49 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q3 327905013 1048576 226375608064910080 72057594037927936 49 19058728659005437116416 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1040247 1048576 19058728659005437116416 151115727451828646838272 270840824 2147483648 277407 277136 (ep762 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep764 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz57 (Real.cos qz171)) (@HMul.hMul Real Real Real qz0 qz57 (@Neg.neg Real Real.instNeg (Real.sin qz171))) Bool.false 35709384195 1099511627776 4141103157969 19044640904708096 Bool.false 281637513027 1099511627776 4156836722961 19044640904708096 (@Enclosure.Real.IsNear.mulLit_ff qz57 (Real.cos qz171) 270741 1048576 1 1048576 131895 1048576 15286947 18162384896 35709384195 1099511627776 4141103157969 19044640904708096 qz349 (@Enclosure.Real.IsNear.recentre' (Real.cos qz171) Bool.false 131895 1048576 122295576 145299079168 131895 1048576 15286947 18162384896 (ep760 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz57 (@Neg.neg Real Real.instNeg (Real.sin qz171)) 270741 1048576 1 1048576 1040247 1048576 15286947 18162384896 281637513027 1099511627776 4156836722961 19044640904708096 qz349 (@Enclosure.Real.IsNear.neg (Real.sin qz171) Bool.true 1040247 1048576 15286947 18162384896 (@Enclosure.Real.IsNear.recentre' (Real.sin qz171) Bool.true 1040247 1048576 122295576 145299079168 1040247 1048576 15286947 18162384896 (ep763 rfl rfl) rfl)) rfl)

noncomputable def ep765 := @ep681 35709384195 1099511627776 4141103157969 19044640904708096 Bool.false 281637513027 1099511627776 4156836722961 19044640904708096 Bool.false 534632397721652611252224 121561333281 274877906944 43452073558251 9522320452354048 Bool.false 209757840317392065921024 23846705553 137438953472 21734234349419 4761160226177024 (ep682 (BSN.head_sum_c_succ qz145 14 15 rfl rfl) (ep756 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep757 ep764) rfl rfl

noncomputable abbrev qz172 := (@HMul.hMul Real Real Real qz268 qz433 qz551)

noncomputable def ep766 := @Enclosure.Complex.IsNear.of_eq qz158 (Complex.mk (@HMul.hMul Real Real Real qz0 qz59 (Real.cos qz172)) (@HMul.hMul Real Real Real qz0 qz59 (@Neg.neg Real Real.instNeg (Real.sin qz172)))) Bool.false 264548686311 1099511627776 4024861389185 19044640904708096 Bool.false 74640762819 1099511627776 4012313294661 19044640904708096 (BSN.cpow_neg_s_mk qz148 115476 1000 16 qz149 rfl)

noncomputable def ep767 := @Enclosure.Real.IsNear.mulLit_ff qz148 qz551 115476 1000 0 1 3121657384082679 1125899906842624 31250000017321 4330250000000000000 90119127021082860051 281474976710656000 902156250500039949 1082562500000000000000 qz150 (BSN.isNear_log_sfrac 16 1 3121657384082679 1125899906842624 31250000017321 4330250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz351) Bool.false 52372720210750067441664 18889465931478580854784 1000000000554272 138568000000000000000 3121657384082679 1125899906842624 31250000017321 4330250000000000000 (BSN.log_rat_reduce_isNear 16 1 4 32 32 0 524288 24973259072661432 36028797018963968 138568 1000000000000000 rfl rfl rfl rfl (ep239 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep768 := nat_lit 3859915890958281857847193811302765934974445757425345080392188934146650978717825

noncomputable def ep769 := nat_lit 3595371307535441009244270754374940937166290890039537096653862745186266058881

noncomputable def ep770 := nat_lit 10103482446583299866061016876952541830082422036577744531442102859272831942070401

noncomputable def ep771 := BSN.sin_dyadic_bound_f 2782710127 2147483648 3 2 1048576 277407 ep768 ep187 ep769 ep770 ep189 ep769 1009177 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2782710127) qz292 0 2 ep768 ep187 ep769 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2782710127) qz293 0 2 ep770 ep189 ep769 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz450 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 335719909) qz16)

noncomputable def ep772 := @Enclosure.Real.IsNear.cos_image qz172 qz450 Bool.false 335719909 1048576 875 1048576 Bool.false 1009177 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz172 Bool.false 90119127021082860051 281474976710656000 902156250500039949 1082562500000000000000 335719909 1048576 875 1048576 (ep767 rfl) rfl) (Enclosure.sfrac_false_div 335719909 1048576) (BSN.cos_reduce3 qz450 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 195815817083174579601408) qz19) 226375608064910080 72057594037927936 Bool.false 1009177 1048576 50 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q3 335719909 1048576 226375608064910080 72057594037927936 50 195815817083174579601408 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1009177 1048576 195815817083174579601408 151115727451828646838272 2782710127 2147483648 277407 277136 (ep771 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep773 := nat_lit 2145995660002394561474771793281258826513432661187431505594173346857111106424961

noncomputable def ep774 := nat_lit 6430796237392112802405826838335026597665965401782215442589212315080960787157121

noncomputable def ep775 := BSN.cos_dyadic_bound_f 2782710127 2147483648 3 2 1048576 277407 ep773 ep155 ep769 ep774 ep158 ep769 284733 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2782710127) qz288 0 2 ep773 ep155 ep769 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2782710127) qz289 0 2 ep774 ep158 ep769 rfl rfl rfl rfl) rfl rfl

noncomputable def ep776 := @Enclosure.Real.IsNear.sin_image qz172 qz450 Bool.false 335719909 1048576 875 1048576 Bool.true 284733 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz172 Bool.false 90119127021082860051 281474976710656000 902156250500039949 1082562500000000000000 335719909 1048576 875 1048576 (ep767 rfl) rfl) (Enclosure.sfrac_false_div 335719909 1048576) (BSN.sin_reduce3 qz450 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 195815817083174579601408) qz19) 226375608064910080 72057594037927936 Bool.false 284733 1048576 50 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q3 335719909 1048576 226375608064910080 72057594037927936 50 195815817083174579601408 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 284733 1048576 195815817083174579601408 151115727451828646838272 2782710127 2147483648 277407 277136 (ep775 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep777 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz59 (Real.cos qz172)) (@HMul.hMul Real Real Real qz0 qz59 (@Neg.neg Real Real.instNeg (Real.sin qz172))) Bool.false 264548686311 1099511627776 4024861389185 19044640904708096 Bool.false 74640762819 1099511627776 4012313294661 19044640904708096 (@Enclosure.Real.IsNear.mulLit_ff qz59 (Real.cos qz172) 262143 1048576 1 1048576 1009177 1048576 15286947 18162384896 264548686311 1099511627776 4024861389185 19044640904708096 qz353 (@Enclosure.Real.IsNear.recentre' (Real.cos qz172) Bool.false 1009177 1048576 122295576 145299079168 1009177 1048576 15286947 18162384896 (ep772 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz59 (@Neg.neg Real Real.instNeg (Real.sin qz172)) 262143 1048576 1 1048576 284733 1048576 15286947 18162384896 74640762819 1099511627776 4012313294661 19044640904708096 qz353 (@Enclosure.Real.IsNear.neg (Real.sin qz172) Bool.true 284733 1048576 15286947 18162384896 (@Enclosure.Real.IsNear.recentre' (Real.sin qz172) Bool.true 284733 1048576 122295576 145299079168 284733 1048576 15286947 18162384896 (ep776 rfl rfl) rfl)) rfl)

noncomputable def ep778 := @ep679 264548686311 1099511627776 4024861389185 19044640904708096 Bool.false 74640762819 1099511627776 4012313294661 19044640904708096 Bool.false 206376688608365657456640 750794019435 1099511627776 90929008505687 19044640904708096 Bool.false 36478278367869136797696 265414407243 1099511627776 90949250692337 19044640904708096 (ep680 (BSN.head_sum_c_succ qz145 15 16 rfl rfl) (ep765 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep766 ep777) rfl rfl

theorem EMRow36.d12 : Enclosure.Complex.IsNear qz157 Bool.false 750794019435 1099511627776 90929008505687 19044640904708096 Bool.false 265414407243 1099511627776 90949250692337 19044640904708096 := ep678 (BSN.head_sum_c_succ qz145 16 17 rfl rfl) (ep778 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

theorem EMRow36.d13 : @Eq Nat (Nat.pow 24 1) 24 := @Eq.refl Nat 24

noncomputable def ep779 := nat_lit 705795700984307885721396746867

noncomputable def ep780 := nat_lit 461224745984066651317107425280

noncomputable def ep781 := nat_lit 4690854810186028522146572224118194147

noncomputable def ep782 := nat_lit 691876417630581549374686612058170982400

noncomputable abbrev qz570 := (@HAdd.hAdd Complex Complex Complex qz578 (@HAdd.hAdd Complex Complex Complex qz578 qz581 (@HMul.hMul Complex Complex Complex qz580 Complex.I (@HDiv.hDiv Complex Complex Complex qz582 (↑qz585) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz451 := qz570

noncomputable abbrev qz173 := (Complex.Stirling.logGammaStirling 1 qz451)

noncomputable abbrev qz571 := (@HAdd.hAdd Complex Complex Complex qz578 qz581 (@HMul.hMul Complex Complex Complex qz580 Complex.I (@HDiv.hDiv Complex Complex Complex qz582 (↑qz585) (2 : Complex))))

noncomputable abbrev qz452 := qz571

noncomputable abbrev qz174 := qz452

noncomputable abbrev qz175 := (@HMul.hMul Real Real Real qz268 (@HDiv.hDiv Real Real Real qz271 qz433 (2 : Real)) (Real.log Real.pi))

noncomputable def ep783 := Complex.re (@HMul.hMul Complex Complex Complex qz61 (Complex.exp (@HMul.hMul Complex Complex Complex qz61 Complex.I ↑(@HSub.hSub Real Real Real qz358 (Complex.im (@HSub.hSub Complex Complex Complex qz62 qz173 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz174 (@Nat.cast Complex Complex.instNatCast j))))) qz175))) (zetaApproximant qz145 1 24))

noncomputable def ep784 := @Enclosure.Real.IsNear.of_eq ep783 (@HSub.hSub Real Real Real qz358 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz358 (Complex.im (@HSub.hSub Complex Complex Complex qz62 qz173 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz174 (@Nat.cast Complex Complex.instNatCast j))))) qz175)) (Complex.re (zetaApproximant qz145 1 24))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz358 (Complex.im (@HSub.hSub Complex Complex Complex qz62 qz173 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz174 (@Nat.cast Complex Complex.instNatCast j))))) qz175)) (Complex.im (zetaApproximant qz145 1 24))))

noncomputable def ep785 := nat_lit 705789350333700611825529946087

noncomputable def ep786 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz358 (Complex.im (@HSub.hSub Complex Complex Complex qz62 qz173 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz174 (@Nat.cast Complex Complex.instNatCast j))))) qz175)) (Complex.re (zetaApproximant qz145 1 24))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz358 (Complex.im (@HSub.hSub Complex Complex Complex qz62 qz173 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz174 (@Nat.cast Complex Complex.instNatCast j))))) qz175)) (Complex.im (zetaApproximant qz145 1 24))) ep785

noncomputable def ep787 := nat_lit 1557587753600761124309527063924305203

noncomputable def ep788 := nat_lit 230625472543527183124895537352723660800

noncomputable def ep789 := nat_lit 23061237299203332565855371264

noncomputable def ep790 := nat_lit 9045774691872574608995516172639269

noncomputable def ep791 := nat_lit 345938208815290774687343306029085491200

noncomputable def ep792 := nat_lit 16276522145156683278748933889256693748530801511068113829888

noncomputable def ep793 := @Enclosure.Real.IsNear.mulLit_tf (Real.cos (@HSub.hSub Real Real Real qz358 (Complex.im (@HSub.hSub Complex Complex Complex qz62 qz173 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz174 (@Nat.cast Complex Complex.instNatCast j))))) qz175)) (Complex.re (zetaApproximant qz145 1 24)) 1048575 1048576 6280027

noncomputable def ep794 := nat_lit 50482036358894257336780627

noncomputable def ep795 := nat_lit 32989364575200079773696000

noncomputable def ep796 := nat_lit 3555586458015172310026144063

noncomputable def ep797 := nat_lit 571408783807040581760188416000

noncomputable def ep798 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz358 (Complex.im (@HSub.hSub Complex Complex Complex qz62 qz173 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz174 (@Nat.cast Complex Complex.instNatCast j))))) qz175)) Bool.true 1048575 1048576 50240216

noncomputable abbrev qz453 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 28824183) qz543)

noncomputable def ep799 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz358 (Complex.im (@HSub.hSub Complex Complex Complex qz62 qz173 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz174 (@Nat.cast Complex Complex.instNatCast j))))) qz175) qz453 Bool.false 28824183 262144 355

noncomputable def ep800 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz358 (Complex.im (@HSub.hSub Complex Complex Complex qz62 qz173 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz174 (@Nat.cast Complex Complex.instNatCast j))))) qz175) Bool.false 495195695534484542817 4503599627370496000 767259884394613483280483 ep276

noncomputable def ep801 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz62 qz173 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz174 (@Nat.cast Complex Complex.instNatCast j))))) qz175 158571680769265117869 900719925474099200 267219935394613483280483 ep276 2165781249 32768000

noncomputable def ep802 := nat_lit 3245314510254797899805491200

noncomputable def ep803 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz62 qz173 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz174 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 408880462804607367577 4503599627370496000 494845269335480148427203 ep276 Bool.false 158571680769265117869 900719925474099200

noncomputable def ep804 := @Enclosure.Complex.IsNear.subLitP qz173 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz174 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 372346927765824234577 4503599627370496000 486653269310506869195203 ep276 Bool.false 161377979465228263469 900719925474099200 250835935392343185168483

noncomputable def ep805 := nat_lit 1841433899925905690448484905036808192

noncomputable def ep806 := nat_lit 44633960151498476958576817748312064

noncomputable abbrev qz454 := (@HSub.hSub Complex Complex Complex qz553 qz570 qz556)

noncomputable abbrev qz455 := (Complex.log qz570)

noncomputable abbrev qz176 := (@HSub.hSub Complex Complex Complex qz355 (@HMul.hMul Complex Complex Complex qz354 qz454 qz455) qz451)

noncomputable abbrev qz177 := qz451

noncomputable def ep807 := @Enclosure.Complex.IsNear.of_eq qz173 (@HAdd.hAdd Complex Complex Complex qz4 (@HAdd.hAdd Complex Complex Complex qz4 qz176 qz67) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz69 2 k))) (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz61 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz70 qz177 (@HSub.hSub Int Int Int qz367 qz72 (@HMul.hMul Int Int Int qz368 qz73 (@Nat.cast Int instNatCastInt k)))))) Bool.true 372346927765824234577

noncomputable def ep808 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz4 qz176 qz67) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz69 2 k))) (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz61 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz70 qz177 (@HSub.hSub Int Int Int qz367 qz72 (@HMul.hMul Int Int Int qz368 qz73 (@Nat.cast Int instNatCastInt k))))) Bool.true 372347180682748650577 4503599627370496000

noncomputable def ep809 := nat_lit 12793743020162315471939579150336

noncomputable def ep810 := nat_lit 3465565720488574803871132549120000

noncomputable def ep811 := @ep808 14851473116680690171 69284000000000000000000 Bool.false 806896387511644397793 4503599627370496000 956843752757797657 8660500000000000000000 Bool.false 1929603 34359738368 3 34359738368 Bool.true 6189523223 4294967296000 9623 4294967296000 Bool.true ep809 372346927765824234577 4503599627370496000 486653269310506869195203 ep276 Bool.false ep810

noncomputable def ep812 := @Enclosure.Complex.IsNear.addLitP qz176 qz67 Bool.true 376485708089959146577 4503599627370496000 1831656250333377287 8660500000000000000000

noncomputable def ep813 := nat_lit 48804289666449231128428544

noncomputable def ep814 := @ep812 Bool.false 806896387511644397793 4503599627370496000 956843752757797657 8660500000000000000000 Bool.false 120447 131072 3 1048576 Bool.false 0 1 0 1 Bool.true ep813 372347180682748650577 4503599627370496000 14851473116680690171 69284000000000000000000 Bool.false 806896387511644397793 806896387511644397793 4503599627370496000

noncomputable abbrev qz178 := (@HMul.hMul Complex Complex Complex qz354 qz454 qz455)

noncomputable def ep815 := @Enclosure.Complex.IsNear.subLitP qz178 qz177 Bool.true 366352608928375530577 4503599627370496000 1831656250333377287 8660500000000000000000 Bool.false 1066925222796762095841

noncomputable def ep816 := nat_lit 1505942832359836586308000

noncomputable def ep817 := nat_lit 3227585550046577591172000

noncomputable def ep818 := @ep815 4503599627370496000 956843752757797657 8660500000000000000000 Bool.false 9000 4000 0 1 Bool.false 230952 4000 0 1 Bool.true ep816 376485708089959146577 4503599627370496000 1831656250333377287 8660500000000000000000 Bool.false ep817 806896387511644397793 4503599627370496000 956843752757797657 8660500000000000000000

noncomputable abbrev qz179 := qz454

noncomputable abbrev qz180 := qz455

noncomputable def ep819 := @Enclosure.Complex.IsNear.mul qz179 qz180 Bool.true 366352608928375530577 4503599627370496000 1831656250333377287 8660500000000000000000 Bool.false 1066925222796762095841 4503599627370496000 956843752757797657

noncomputable abbrev qz181 := (Complex.re qz454)

noncomputable abbrev qz182 := (Complex.re qz455)

noncomputable abbrev qz183 := (Complex.im qz454)

noncomputable abbrev qz184 := (Complex.im qz455)

noncomputable def ep820 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz181 qz182) (@HMul.hMul Real Real Real qz0 qz183 qz184) 255774911805634123 36028797018963968 437500001333717 138568000000000000000 24895279556504987247 281474976710656000

noncomputable def ep821 := nat_lit 824952736528020542710015857677828096

noncomputable def ep822 := @Enclosure.Real.IsNear.mulLit_ff qz181 qz182 7000 4000 0 1 36539273115090589 9007199254740992 62500000190531 34642000000000000000

noncomputable def ep823 := @Enclosure.Complex.IsNear.re_isNear qz179 Bool.false 7000 4000 0 1 Bool.false 230952 4000 0 1

noncomputable abbrev qz456 := (Enclosure.sfrac Bool.false 230952 4000)

noncomputable abbrev qz185 := qz456

noncomputable def ep824 := @Enclosure.Complex.IsNear.of_eq qz179 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz185) Bool.false 7000 4000 0 1 Bool.false 230952 4000 0

noncomputable abbrev qz457 := (Complex.log (Complex.mk qz82 qz185))

noncomputable def ep825 := @Enclosure.Complex.IsNear.of_eq qz180 qz457 Bool.false 36539273115090589 9007199254740992 62500000190531 34642000000000000000 Bool.false 862353374086563 562949953421312 125000000017321 34642000000000000000

noncomputable def ep826 := nat_lit 2877393316316620227867606925209761048760752183259889660789518634065530307852027140002283520

noncomputable def ep827 := nat_lit 57046800954069501173890297079055609033886471464218043285667834347954960254033644102877184

noncomputable def ep828 := nat_lit 3474217539500180090565393951674276488063740703129816472597617740632030035819395809280

noncomputable def ep829 := BSN.log_dyadic_bound 20651826304 86187826304 5 4 ep826 1048576 277136 ep827 ep828 512470 106839652608 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 20651826304) (BSN.artanhQ 86187826304) 0 4 ep827 ep826 ep828 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz572 := (Real.log (Enclosure.sfrac Bool.false 53419826304 16000000))

noncomputable def ep830 := @Enclosure.Real.IsNear.mulLit_ff qz83 qz572 1 2 0 1 36539273115090589 4503599627370496 62500000190531 17321000000000000000 36539273115090589 9007199254740992 62500000190531 34642000000000000000 qz372 (BSN.isNear_log_sfrac 53419826304 16000000 36539273115090589 4503599627370496 62500000190531 17321000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 53419826304) qz373)) Bool.false 306513638767433835610112 37778931862957161709568 1000000003048496 277136000000000000000 36539273115090589 4503599627370496 62500000190531 17321000000000000000 (BSN.log_rat_reduce_isNear 53419826304 16000000 11 106839652608 65536000000 512470 1048576 24973259072661432 36028797018963968 277136 1000000000000000 rfl rfl rfl rfl (ep829 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep831 := BSN.arctan_dyadic_bound_f 9000 230952 1 0 1048576 277136 0 1 1 0 1 1 40841 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 230952) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 230952) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz458 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 230952)))

noncomputable def ep832 := @Enclosure.Real.IsNear.subLit_ff_p qz84 qz458 884279719003555 562949953421312 1 2000000000000000 40841 1048576 1 277136 904243051586191884288 862353374086563 562949953421312 125000000017321 34642000000000000000 qz85 (ep831 rfl) rfl rfl

noncomputable abbrev qz459 := (Complex.mk qz82 qz185)

noncomputable abbrev qz460 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 230952) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep833 := @Enclosure.Complex.IsNear.re_isNear qz180 Bool.false 36539273115090589 9007199254740992 62500000190531 34642000000000000000 Bool.false 862353374086563 562949953421312 125000000017321 34642000000000000000 (ep825 (@congrArg Complex Complex qz177 qz459 Complex.log (BSN.w_shift_mk qz148 Bool.false 115476 1000 2 qz149 rfl)) (@Enclosure.Complex.IsNear.of_parts qz457 Bool.false 36539273115090589 9007199254740992 62500000190531 34642000000000000000 Bool.false 862353374086563 562949953421312 125000000017321 34642000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz457) (@HMul.hMul Real Real Real qz0 qz83 qz572) Bool.false 36539273115090589 9007199254740992 62500000190531 34642000000000000000 (Enclosure.clog_re_eq 9000 230952 4000 53419826304 16000000 rfl rfl rfl) (ep830 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz457) qz460 Bool.false 862353374086563 562949953421312 125000000017321 34642000000000000000 (Enclosure.clog_im_eq 9000 230952 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz460 (@HSub.hSub Real Real Real qz358 qz84 qz458) Bool.false 862353374086563 562949953421312 125000000017321 34642000000000000000 (BSN.arctan_recip 230952 9000 rfl rfl) ep832))))

noncomputable def ep834 := @Enclosure.Real.IsNear.mulLit_ff qz183 qz184 230952 4000 0 1 862353374086563 562949953421312 125000000017321 34642000000000000000

noncomputable def ep835 := @Enclosure.Complex.IsNear.im_isNear qz179 Bool.false 7000 4000 0 1 Bool.false 230952 4000 0 1

noncomputable def ep836 := @Enclosure.Complex.IsNear.im_isNear qz180 Bool.false 36539273115090589 9007199254740992 62500000190531 34642000000000000000 Bool.false 862353374086563 562949953421312 125000000017321 34642000000000000000 (ep825 (@congrArg Complex Complex qz177 qz459 Complex.log (BSN.w_shift_mk qz148 Bool.false 115476 1000 2 qz149 rfl)) (@Enclosure.Complex.IsNear.of_parts qz457 Bool.false 36539273115090589 9007199254740992 62500000190531 34642000000000000000 Bool.false 862353374086563 562949953421312 125000000017321 34642000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz457) (@HMul.hMul Real Real Real qz0 qz83 qz572) Bool.false 36539273115090589 9007199254740992 62500000190531 34642000000000000000 (Enclosure.clog_re_eq 9000 230952 4000 53419826304 16000000 rfl rfl rfl) (ep830 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz457) qz460 Bool.false 862353374086563 562949953421312 125000000017321 34642000000000000000 (Enclosure.clog_im_eq 9000 230952 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz460 (@HSub.hSub Real Real Real qz358 qz84 qz458) Bool.false 862353374086563 562949953421312 125000000017321 34642000000000000000 (BSN.arctan_recip 230952 9000 rfl rfl) ep832))))

noncomputable abbrev qz461 := (Enclosure.Real.IsNear.const Bool.false 230952 4000)

noncomputable abbrev qz186 := (@ep824 1 (BSN.w_sub_half_mk qz433 Bool.false 115476 1000 2 qz434 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz456 Bool.false 7000 4000 0 1 Bool.false 230952 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) qz461))

noncomputable def ep837 := @ep820 3608625000500039949 17321000000000000000000 ep821 366352608928375530577 4503599627370496000 1831656250333377287 8660500000000000000000 (@ep822 255774911805634123 36028797018963968 437500001333717 138568000000000000000 (ep823 qz186) ep833 rfl) (@ep834 24895279556504987247 281474976710656000 3608625000500039949 17321000000000000000000 (ep835 qz186) ep836 rfl) rfl

noncomputable def ep838 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz181 qz184) (@HMul.hMul Real Real Real qz0 qz183 qz182) 6036473618605941 2251799813685248 875000000121247 138568000000000000000 1054852275559550213841 4503599627370496000

noncomputable def ep839 := nat_lit 2402502017909840599491287510383853568

noncomputable def ep840 := @Enclosure.Real.IsNear.mulLit_ff qz181 qz184 7000 4000 0 1 862353374086563 562949953421312 125000000017321 34642000000000000000

noncomputable def ep841 := @Enclosure.Real.IsNear.mulLit_ff qz183 qz182 230952 4000 0 1 36539273115090589 9007199254740992 62500000190531 34642000000000000000

noncomputable def ep842 := @ep838 1804312505500439439 17321000000000000000000 ep839 1066925222796762095841 4503599627370496000 956843752757797657 8660500000000000000000 (@ep840 6036473618605941 2251799813685248 875000000121247 138568000000000000000 (ep823 qz186) ep836 rfl) (@ep841 1054852275559550213841 4503599627370496000 1804312505500439439 17321000000000000000000 (ep835 qz186) ep833 rfl) rfl

noncomputable def ep843 := @Enclosure.Complex.IsNear.of_eq qz177 qz459 Bool.false 9000 4000 0 1 Bool.false 230952 4000 0 1 (BSN.w_shift_mk qz148 Bool.false 115476 1000 2 qz149 rfl)

noncomputable abbrev qz462 := (ep843 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9000 4000) (Enclosure.sfrac Bool.false 230952 4000) Bool.false 9000 4000 0 1 Bool.false 230952 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 230952 4000)))

noncomputable abbrev qz187 := qz462

noncomputable def ep844 := ep818 (@ep819 8660500000000000000000 (ep837 rfl) (ep842 rfl)) qz187 rfl rfl rfl rfl rfl rfl

noncomputable def ep845 := @ep814 956843752757797657 8660500000000000000000 (ep844 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz88 (↑qz2) Bool.false 120447 131072 3 1048576 Bool.false 0 1 0 1 (@ep319 131072 3 1048576 (ep321 rfl) (ep323 rfl) rfl rfl) (@ep324 1 0 1 (ep326 rfl) (ep328 rfl) rfl rfl))

noncomputable abbrev qz463 := (@HPow.hPow Complex Int Complex qz558 qz570 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz188 := qz463

noncomputable def ep846 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz69 2 k))) (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz61 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz70 qz177 (@HSub.hSub Int Int Int qz367 qz72 (@HMul.hMul Int Int Int qz368 qz73 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz69 2 k))) (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz61 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz70 qz177 (@HSub.hSub Int Int Int qz367 qz72 (@HMul.hMul Int Int Int qz368 qz73 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 (@Rat.cast Complex Complex.instRatCast (bernoulli qz90)) qz91) qz188)) Bool.false 1929603 34359738368 3 34359738368

noncomputable def ep847 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz69 2 k))) (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz61 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz70 qz177 (@HSub.hSub Int Int Int qz367 qz72 (@HMul.hMul Int Int Int qz368 qz73 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 (@Rat.cast Complex Complex.instRatCast (bernoulli qz90)) qz91) qz188) Bool.false 0 1 0 1 Bool.false

noncomputable def ep848 := @ep847 0 1 0 1 Bool.false 1929603 34359738368 3 34359738368 Bool.true 6189523223 4294967296000 9623 4294967296000 Bool.false 1929603 1929603 34359738368 3 34359738368 Bool.true 6189523223 6189523223 4294967296000 9623

noncomputable def ep849 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz69 2 k))) (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz61 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz70 qz177 (@HSub.hSub Int Int Int qz367 qz72 (@HMul.hMul Int Int Int qz368 qz73 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep850 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz68 (@Rat.cast Complex Complex.instRatCast (bernoulli qz90)) qz91) qz188 Bool.false 1929603 34359738368 3 34359738368 Bool.true 6189523223 4294967296000 9623 4294967296000

noncomputable abbrev qz189 := (Complex.re qz463)

noncomputable abbrev qz190 := (Complex.im qz463)

noncomputable def ep851 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz68 (@Rat.cast Complex Complex.instRatCast (bernoulli qz90)) qz91)) qz189) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz68 (@Rat.cast Complex Complex.instRatCast (bernoulli qz90)) qz91)) qz190) 1929603 34359738368 3 34359738368 0 1 0

noncomputable def ep852 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz68 (@Rat.cast Complex Complex.instRatCast (bernoulli qz90)) qz91)) qz189 1 12 0 1 5788809 8589934592 9 8589934592 1929603

noncomputable def ep853 := @Enclosure.Complex.IsNear.re_isNear qz188 Bool.false 5788809 8589934592 9 8589934592 Bool.true 18568569669 1073741824000 28869 1073741824000

noncomputable abbrev qz464 := (@HPow.hPow Complex Nat Complex qz560 qz570 1)

noncomputable abbrev qz191 := (@Inv.inv Complex Complex.instInv qz464)

noncomputable def ep854 := @Enclosure.Complex.IsNear.of_eq qz188 qz191 Bool.false 5788809 8589934592 9 8589934592 Bool.true 18568569669 1073741824000 28869

noncomputable def ep855 := @Enclosure.Complex.IsNear.of_parts qz191 Bool.false 5788809 8589934592 9 8589934592 Bool.true 18568569669 1073741824000 28869

noncomputable abbrev qz192 := (Complex.re qz464)

noncomputable abbrev qz193 := qz464

noncomputable def ep856 := @Enclosure.Real.IsNear.mulLit_ff qz192 (@Inv.inv Real Real.instInv (@DFunLike.coe qz97 Complex (fun (x : Complex) => Real) qz98 Complex.normSq qz193)) 9000 4000 0 1 643201 2147483648 1 2147483648

noncomputable def ep857 := @Enclosure.Complex.IsNear.re_isNear qz193 Bool.false 9000 4000 0 1 Bool.false 230952 4000 0 1

noncomputable def ep858 := @Enclosure.Complex.IsNear.of_eq qz193 qz177 Bool.false 9000 4000 0 1 Bool.false 230952 4000 0

noncomputable def ep859 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz97 Complex (fun (x : Complex) => Real) qz98 Complex.normSq qz193)) Bool.false 643201 2147483648 1 2147483648 643201 2147483648 1

noncomputable abbrev qz194 := (Complex.im qz464)

noncomputable def ep860 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz97 Complex (fun (x : Complex) => Real) qz98 Complex.normSq qz193) (@HAdd.hAdd Real Real Real qz382 (@HMul.hMul Real Real Real qz0 qz192 qz192) (@HMul.hMul Real Real Real qz0 qz194 qz194)) Bool.false 417342393 125000 0 1

noncomputable def ep861 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz192 qz192) (@HMul.hMul Real Real Real qz0 qz194 qz194) 81 16 0 1 833419161 250000

noncomputable def ep862 := @Enclosure.Real.IsNear.mulLit_ff qz192 qz192 9000 4000 0 1 9000 4000 0 1

noncomputable def ep863 := @Enclosure.Real.IsNear.mulLit_ff qz194 qz194 230952 4000 0 1 230952 4000 0 1

noncomputable def ep864 := @Enclosure.Complex.IsNear.im_isNear qz193 Bool.false 9000 4000 0 1 Bool.false 230952 4000 0 1

noncomputable abbrev qz195 := (ep857 (@ep858 1 (BSN.pow_one_c qz451) qz462))

noncomputable abbrev qz196 := (ep864 (@ep858 1 (BSN.pow_one_c qz451) qz462))

noncomputable def ep865 := @ep861 0 1 13354956576 417342393 125000 0 1 (@ep862 81 16 0 1 qz195 qz195 rfl) (@ep863 833419161 250000 0 1 qz196 qz196 rfl)

noncomputable def ep866 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz97 Complex (fun (x : Complex) => Real) qz98 Complex.normSq qz193) 417342393 125000 0 1 321600 321601 1073741824 (ep860 (Enclosure.Complex.normSq_eq_mul_add_mul qz193) (ep865 rfl rfl)) rfl

noncomputable def ep867 := @Enclosure.Real.IsNear.of_eq (Complex.re qz191) (@HMul.hMul Real Real Real qz0 qz192 (@Inv.inv Real Real.instInv (@DFunLike.coe qz97 Complex (fun (x : Complex) => Real) qz98 Complex.normSq qz193))) Bool.false 5788809 8589934592 9 8589934592 (Enclosure.Complex.inv_re_eq_mul qz193) (@ep856 5788809 8589934592 9 8589934592 qz195 (@ep859 2147483648 (ep866 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep868 := @Enclosure.Real.IsNear.of_eq (Complex.im qz191) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz194) (@Inv.inv Real Real.instInv (@DFunLike.coe qz97 Complex (fun (x : Complex) => Real) qz98 Complex.normSq qz193))) Bool.true 18568569669 1073741824000 28869 1073741824000 (Enclosure.Complex.inv_im_eq_mul qz193)

noncomputable def ep869 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz194) (@Inv.inv Real Real.instInv (@DFunLike.coe qz97 Complex (fun (x : Complex) => Real) qz98 Complex.normSq qz193)) 230952 4000 0 1 643201 2147483648 1

noncomputable def ep870 := @ep869 2147483648 18568569669 1073741824000 28869 1073741824000 (@Enclosure.Real.IsNear.neg qz194 Bool.false 230952 4000 0 1 qz196) (@ep859 2147483648 (ep866 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep871 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz68 (@Rat.cast Complex Complex.instRatCast (bernoulli qz90)) qz91)) qz190 0 1 0 1 18568569669 1073741824000 28869 1073741824000 0

noncomputable def ep872 := @Enclosure.Complex.IsNear.im_isNear qz188 Bool.false 5788809 8589934592 9 8589934592 Bool.true 18568569669 1073741824000 28869 1073741824000

noncomputable abbrev qz197 := (@ep854 1073741824000 (BSN.zpow_one_sub_two_mul qz451 1 1 rfl rfl) (@ep855 1073741824000 ep867 (ep868 ep870)))

noncomputable def ep873 := @ep851 1 1929603 1929603 34359738368 3 34359738368 (@ep852 34359738368 3 34359738368 ep338 (ep853 qz197) rfl) (@ep871 1 0 1 ep358 (ep872 qz197) rfl) rfl

noncomputable def ep874 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz68 (@Rat.cast Complex Complex.instRatCast (bernoulli qz90)) qz91)) qz190) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz68 (@Rat.cast Complex Complex.instRatCast (bernoulli qz90)) qz91)) qz189) 6189523223 4294967296000 9623 4294967296000 0 1 0

noncomputable def ep875 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz68 (@Rat.cast Complex Complex.instRatCast (bernoulli qz90)) qz91)) qz190 1 12 0 1 18568569669 1073741824000 28869 1073741824000 6189523223

noncomputable def ep876 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz68 (@Rat.cast Complex Complex.instRatCast (bernoulli qz90)) qz91)) qz189 0 1 0 1 5788809 8589934592 9 8589934592 0

noncomputable def ep877 := @ep874 1 6189523223 6189523223 4294967296000 9623 4294967296000 (@ep875 4294967296000 9623 4294967296000 ep338 (ep872 qz197) rfl) (@ep876 1 0 1 ep358 (ep853 qz197) rfl) rfl

noncomputable def ep878 := @ep848 4294967296000 (@ep849 0 1 0 1 (BSN.stirling_sum_base qz177) qz104) (ep850 (ep873 rfl) (ep877 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep879 := @ep811 161377979465228263469 900719925474099200 250835935392343185168483 ep276 (ep845 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep846 Bool.true 6189523223 4294967296000 9623 4294967296000 (BSN.stirling_sum_succ qz177 0 1 rfl) (ep878 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep880 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz174 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz148 2) Bool.false 36533535038783133 4503599627370496 62500000190531 17321000000000000000 Bool.false 876968342488483 281474976710656

noncomputable abbrev qz198 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz274 qz452 qz378))

noncomputable def ep881 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz148 2) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz148 1) qz198) Bool.false 36533535038783133 4503599627370496 62500000190531 17321000000000000000 Bool.false 876968342488483 281474976710656 125000000017321 17321000000000000000

noncomputable def ep882 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz148 1) qz198 Bool.false 36532521426501277 9007199254740992 62500000190531 34642000000000000000 Bool.false 881842325063075 562949953421312 125000000017321 34642000000000000000 Bool.false

noncomputable def ep883 := nat_lit 658129659148762707641681546575872

noncomputable def ep884 := nat_lit 987378575111713388403613499392

noncomputable abbrev qz199 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz274 qz452 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep885 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz148 1) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz148 0) qz199) Bool.false 36532521426501277 9007199254740992 62500000190531 34642000000000000000 Bool.false 881842325063075 562949953421312 125000000017321 34642000000000000000

noncomputable def ep886 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz148 0) qz199 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz465 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz185))

noncomputable def ep887 := @Enclosure.Complex.IsNear.of_eq qz199 qz465 Bool.false 36532521426501277 9007199254740992 62500000190531 34642000000000000000 Bool.false 881842325063075 562949953421312 125000000017321 34642000000000000000

noncomputable def ep888 := nat_lit 2856096106768604957078870079492742171339905744544836605270915945259209653458276816802283520

noncomputable def ep889 := nat_lit 56279184211775573460989305999952864000701117189693451786252261384209210162009262662877184

noncomputable def ep890 := nat_lit 3368000048152100483750829786709861210874366636340753473866988072815279796894595809280

noncomputable def ep891 := BSN.log_dyadic_bound 20571826304 86107826304 5 4 ep888 1048576 277136 ep889 ep890 510898 106679652608 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 20571826304) (BSN.artanhQ 86107826304) 0 4 ep889 ep888 ep890 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep892 := @Enclosure.Real.IsNear.mulLit_ff qz83 (Real.log (Enclosure.sfrac Bool.false 53339826304 16000000)) 1 2 0 1 36532521426501277 4503599627370496 62500000190531 17321000000000000000 36532521426501277 9007199254740992 62500000190531 34642000000000000000 qz372 (BSN.isNear_log_sfrac 53339826304 16000000 36532521426501277 4503599627370496 62500000190531 17321000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 53339826304) qz373)) Bool.false 306457001498520024252416 37778931862957161709568 1000000003048496 277136000000000000000 36532521426501277 4503599627370496 62500000190531 17321000000000000000 (BSN.log_rat_reduce_isNear 53339826304 16000000 11 106679652608 65536000000 510898 1048576 24973259072661432 36028797018963968 277136 1000000000000000 rfl rfl rfl rfl (ep891 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep893 := BSN.arctan_dyadic_bound_f 1000 230952 1 0 1048576 277136 0 1 1 0 1 1 4540 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 230952) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 230952) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz466 := (@Nat.cast Real Real.instNatCast 230952)

noncomputable def ep894 := @Enclosure.Real.IsNear.subLit_ff_p qz84 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz384 qz466)) 884279719003555 562949953421312 1 2000000000000000 4540 1048576 1 277136 924678697845338931200 881842325063075 562949953421312 125000000017321 34642000000000000000 qz85 (ep893 rfl) rfl rfl

noncomputable abbrev qz200 := (@HAdd.hAdd Complex Complex Complex qz274 qz452 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz467 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz185)

noncomputable def ep895 := @ep886 36532521426501277 9007199254740992 62500000190531 34642000000000000000 Bool.false 881842325063075 562949953421312 125000000017321 34642000000000000000 Bool.false 36532521426501277 36532521426501277 9007199254740992 62500000190531 34642000000000000000 Bool.false 881842325063075 881842325063075 562949953421312 125000000017321 34642000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz148 0) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz148) qz104) (ep887 (@congrArg Complex Complex qz200 qz467 Complex.log (BSN.w_shift_mk qz148 Bool.false 115476 1000 0 qz149 rfl)) (@Enclosure.Complex.IsNear.of_parts qz465 Bool.false 36532521426501277 9007199254740992 62500000190531 34642000000000000000 Bool.false 881842325063075 562949953421312 125000000017321 34642000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz465) (@HMul.hMul Real Real Real qz0 qz83 (Real.log (Enclosure.sfrac Bool.false 53339826304 16000000))) Bool.false 36532521426501277 9007199254740992 62500000190531 34642000000000000000 (Enclosure.clog_re_eq 1000 230952 4000 53339826304 16000000 rfl rfl rfl) (ep892 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz465) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz466 qz384)) Bool.false 881842325063075 562949953421312 125000000017321 34642000000000000000 (Enclosure.clog_im_eq 1000 230952 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz466 qz384)) (@HSub.hSub Real Real Real qz358 qz84 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz384 qz466))) Bool.false 881842325063075 562949953421312 125000000017321 34642000000000000000 (BSN.arctan_recip 230952 1000 rfl rfl) ep894)))) rfl rfl

noncomputable abbrev qz468 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz185))

noncomputable def ep896 := @Enclosure.Complex.IsNear.of_eq qz198 qz468 Bool.false 36534548651064989 9007199254740992 62500000190531 34642000000000000000 Bool.false 872094359913891 562949953421312 125000000017321 34642000000000000000

noncomputable def ep897 := nat_lit 2862470738684229514019076214551777185877222692528436893684577506036236247513361913762283520

noncomputable def ep898 := nat_lit 56508586127491905123437073998101514114754028530960273756642159585948036392048577094877184

noncomputable def ep899 := nat_lit 3399562760698186239566054423961175926244469674157895310410389757888942308572035809280

noncomputable def ep900 := BSN.log_dyadic_bound 20595826304 86131826304 5 4 ep897 1048576 277136 ep898 ep899 511370 106727652608 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 20595826304) (BSN.artanhQ 86131826304) 0 4 ep898 ep897 ep899 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep901 := @Enclosure.Real.IsNear.mulLit_ff qz83 (Real.log (Enclosure.sfrac Bool.false 53363826304 16000000)) 1 2 0 1 36534548651064989 4503599627370496 62500000190531 17321000000000000000 36534548651064989 9007199254740992 62500000190531 34642000000000000000 qz372 (BSN.isNear_log_sfrac 53363826304 16000000 36534548651064989 4503599627370496 62500000190531 17321000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 53363826304) qz373)) Bool.false 306474007090712975245312 37778931862957161709568 1000000003048496 277136000000000000000 36534548651064989 4503599627370496 62500000190531 17321000000000000000 (BSN.log_rat_reduce_isNear 53363826304 16000000 11 106727652608 65536000000 511370 1048576 24973259072661432 36028797018963968 277136 1000000000000000 rfl rfl rfl rfl (ep900 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep902 := BSN.arctan_dyadic_bound_f 5000 230952 1 0 1048576 277136 0 1 1 0 1 1 22697 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 230952) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 230952) 0 0 rfl) rfl rfl rfl

noncomputable def ep903 := @Enclosure.Real.IsNear.subLit_ff_p qz84 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz388 qz466)) 884279719003555 562949953421312 1 2000000000000000 22697 1048576 1 277136 914457215541068169216 872094359913891 562949953421312 125000000017321 34642000000000000000 qz85 (ep902 rfl) rfl rfl

noncomputable abbrev qz201 := (@HAdd.hAdd Complex Complex Complex qz274 qz452 qz378)

noncomputable abbrev qz469 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz185)

noncomputable def ep904 := @ep882 36534548651064989 9007199254740992 62500000190531 34642000000000000000 Bool.false 872094359913891 562949953421312 125000000017321 34642000000000000000 Bool.false ep883 36533535038783133 4503599627370496 62500000190531 17321000000000000000 Bool.false ep884 876968342488483 281474976710656 125000000017321 17321000000000000000 (ep885 (BSN.log_sum_c_succ qz148 0 1 rfl) (ep895 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep896 (@congrArg Complex Complex qz201 qz469 Complex.log (BSN.w_shift_mk qz148 Bool.false 115476 1000 1 qz149 rfl)) (@Enclosure.Complex.IsNear.of_parts qz468 Bool.false 36534548651064989 9007199254740992 62500000190531 34642000000000000000 Bool.false 872094359913891 562949953421312 125000000017321 34642000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz468) (@HMul.hMul Real Real Real qz0 qz83 (Real.log (Enclosure.sfrac Bool.false 53363826304 16000000))) Bool.false 36534548651064989 9007199254740992 62500000190531 34642000000000000000 (Enclosure.clog_re_eq 5000 230952 4000 53363826304 16000000 rfl rfl rfl) (ep901 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz468) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz466 qz388)) Bool.false 872094359913891 562949953421312 125000000017321 34642000000000000000 (Enclosure.clog_im_eq 5000 230952 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz466 qz388)) (@HSub.hSub Real Real Real qz358 qz84 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz388 qz466))) Bool.false 872094359913891 562949953421312 125000000017321 34642000000000000000 (BSN.arctan_recip 230952 5000 rfl rfl) ep903)))) rfl rfl

noncomputable def ep905 := @ep804 ep276 Bool.false 36533535038783133 4503599627370496 62500000190531 17321000000000000000 Bool.false 876968342488483 281474976710656 125000000017321 17321000000000000000 Bool.true ep805 408880462804607367577 4503599627370496000 494845269335480148427203 ep276 Bool.false ep806 158571680769265117869 900719925474099200 267219935394613483280483 ep276 (@ep807 4503599627370496000 486653269310506869195203 ep276 Bool.false 161377979465228263469 900719925474099200 250835935392343185168483 ep276 (BSN.logGammaStirling_unfold 1 qz177) (ep879 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep880 125000000017321 17321000000000000000 (BSN.log_sum_c_eq qz148 2) (ep881 (BSN.log_sum_c_succ qz148 1 2 rfl) (ep904 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz202 := (@HDiv.hDiv Real Real Real qz271 qz433 (2 : Real))

noncomputable def ep906 := @Enclosure.Real.IsNear.mulLit_ff qz202 (Real.log Real.pi) 115476 2000 0 1 75021 65536 1 262144 2165781249 32768000 28869 131072000 (@Enclosure.Real.IsNear.of_eq qz202 (Enclosure.sfrac Bool.false 115476 2000) Bool.false 115476 2000 0 1 (BSN.t_half_eq qz148 Bool.false 115476 1000 qz149) (Enclosure.Real.IsNear.const Bool.false 115476 2000)) EMRow36.d5 rfl

noncomputable def ep907 := @ep801 28869 131072000 ep802 495195695534484542817 4503599627370496000 767259884394613483280483 ep276 (@ep803 267219935394613483280483 ep276 (ep905 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep906 rfl rfl

noncomputable def ep908 := nat_lit 8339501083047080909305861699183199203744187071212877939439587670172554571612160

noncomputable def ep909 := nat_lit 16746792847428112866369059834787208516685049801295806823738024940567569432576

noncomputable def ep910 := nat_lit 21814436600513185436874564067652056719826809391593534725579534714833866860855296

noncomputable def ep911 := BSN.sin_dyadic_bound_f 3372806732 2147483648 3 2 1048576 277407 ep908 ep187 ep909 ep910 ep189 ep909 1048575 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3372806732) qz292 0 2 ep908 ep187 ep909 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3372806732) qz293 0 2 ep910 ep189 ep909 rfl rfl rfl rfl) rfl rfl

noncomputable def ep912 := @ep799 1048576 Bool.true 1048575 1048576 1 138568 (@ep800 28824183 262144 355 1048576 ep907 rfl) (Enclosure.sfrac_false_div 28824183 262144) (BSN.cos_reduce1 qz453 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 59335043538710163357696) qz319) 226375608064910080 72057594037927936 Bool.false 1048575 1048576 17 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q1 28824183 262144 226375608064910080 72057594037927936 17 59335043538710163357696 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1048575 1048576 59335043538710163357696 37778931862957161709568 3372806732 2147483648 277407 277136 (ep911 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep913 := nat_lit 237005242479218153231244409

noncomputable def ep914 := nat_lit 38093918920469372117345894400

noncomputable abbrev qz470 := (@HPow.hPow Complex Complex Complex qz532 (@Nat.cast Complex Complex.instNatCast 24) qz568)

noncomputable abbrev qz203 := qz470

noncomputable abbrev qz471 := (@Nat.cast Complex Complex.instNatCast 24)

noncomputable abbrev qz204 := (@HAdd.hAdd Complex Complex Complex qz274 (@HDiv.hDiv Complex Complex Complex qz363 qz471 (@HSub.hSub Complex Complex Complex qz355 qz426 (1 : Complex))) qz362)

noncomputable abbrev qz205 := qz471

noncomputable def ep915 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz145 1 24) (@HAdd.hAdd Complex Complex Complex qz4 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 24, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz146) (@HMul.hMul Complex Complex Complex qz61 qz203 (@HAdd.hAdd Complex Complex Complex qz4 qz204 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz69 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz69 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz112 (@HMul.hMul Nat Nat Nat qz69 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz113 qz205 (@HSub.hSub Nat Nat Nat qz112 (@HMul.hMul Nat Nat Nat qz69 2 k) 1))))))) Bool.false ep794 ep795 ep796

noncomputable def ep916 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 24, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz146) (@HMul.hMul Complex Complex Complex qz61 qz203 (@HAdd.hAdd Complex Complex Complex qz4 qz204 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz69 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz69 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz112 (@HMul.hMul Nat Nat Nat qz69 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz113 qz205 (@HSub.hSub Nat Nat Nat qz112 (@HMul.hMul Nat Nat Nat qz69 2 k) 1)))))) Bool.false 1753042911965 1099511627776 116224925567787 19044640904708096

noncomputable def ep917 := nat_lit 2115653631670940784859373

noncomputable def ep918 := nat_lit 68414203150810783837192063

noncomputable def ep919 := nat_lit 4557683864114597767553209

noncomputable def ep920 := nat_lit 55505585970415041019822297828191895552

noncomputable def ep921 := nat_lit 31739155393819837047178382251393024

noncomputable def ep922 := @ep916 Bool.false 169839202491 1099511627776 116209631575133 19044640904708096 Bool.true ep917 ep795 ep918 ep797 Bool.true 39077358034171881529931 439858194336001063649280 ep919 ep914 Bool.false ep920 ep794 ep795 ep796 ep797 Bool.false ep921 28866593669426799394549 439858194336001063649280

noncomputable def ep923 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 24, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz146) (BSN.headSumC qz145 24) Bool.false 1753042911965 1099511627776 116224925567787 19044640904708096 Bool.false 169839202491 1099511627776 116209631575133

noncomputable abbrev qz206 := (@HPow.hPow Complex Complex Complex qz275 qz391 qz427)

noncomputable def ep924 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz145 24) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz145 23) qz206) Bool.false 1753042911965 1099511627776 116224925567787 19044640904708096 Bool.false 169839202491 1099511627776 116209631575133 19044640904708096

noncomputable def ep925 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz145 23) qz206 Bool.false 957126712327 549755813888 28217438789059 4761160226177024 Bool.false 3413535741 549755813888 56427159219271 9522320452354048 Bool.true

noncomputable abbrev qz472 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 22) qz146)

noncomputable def ep926 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz145 23) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz145 22) qz472) Bool.false 957126712327 549755813888 28217438789059 4761160226177024 Bool.false 3413535741 549755813888 56427159219271 9522320452354048

noncomputable def ep927 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz145 22) qz472 Bool.false 1829408848457 1099511627776 109445662175569 19044640904708096 Bool.true 211696095549 1099511627776 109419868158073 19044640904708096 Bool.false

noncomputable def ep928 := nat_lit 2104743898917102109589504

noncomputable abbrev qz473 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 21) qz146)

noncomputable def ep929 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz145 22) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz145 21) qz473) Bool.false 1829408848457 1099511627776 109445662175569 19044640904708096 Bool.true 211696095549 1099511627776 109419868158073 19044640904708096

noncomputable def ep930 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz145 21) qz473 Bool.false 1599441953279 1099511627776 105912887025547 19044640904708096 Bool.true 280128923627 1099511627776 105911548527951 19044640904708096 Bool.false

noncomputable abbrev qz474 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 20) qz146)

noncomputable def ep931 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz145 21) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz145 20) qz474) Bool.false 1599441953279 1099511627776 105912887025547 19044640904708096 Bool.true 280128923627 1099511627776 105911548527951 19044640904708096

noncomputable def ep932 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz145 20) qz474 Bool.false 1369333607741 1099511627776 102315618953285 19044640904708096 Bool.true 96773395233 549755813888 51162441605691 9522320452354048 Bool.false

noncomputable abbrev qz475 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 19) qz146)

noncomputable def ep933 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz145 20) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz145 19) qz475) Bool.false 1369333607741 1099511627776 102315618953285 19044640904708096 Bool.true 96773395233 549755813888 51162441605691 9522320452354048

noncomputable def ep934 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz145 19) qz475 Bool.false 1179698542451 1099511627776 98624536665455 19044640904708096 Bool.true 13608299989 549755813888 49317739473695 9522320452354048 Bool.false

noncomputable abbrev qz476 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 18) qz146)

noncomputable def ep935 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz145 19) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz145 18) qz476) Bool.false 1179698542451 1099511627776 98624536665455 19044640904708096 Bool.true 13608299989 549755813888 49317739473695 9522320452354048

noncomputable def ep936 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz145 18) qz476 Bool.false 247949571859 274877906944 47416584295223 9522320452354048 Bool.false 151264730427 1099511627776 94844770975691 19044640904708096 Bool.false

noncomputable abbrev qz477 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 17) qz146)

noncomputable def ep937 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz145 18) (@HAdd.hAdd Complex Complex Complex qz4 qz157 qz477) Bool.false 247949571859 274877906944 47416584295223 9522320452354048 Bool.false 151264730427 1099511627776 94844770975691 19044640904708096

noncomputable def ep938 := @Enclosure.Complex.IsNear.addLitP qz157 qz477 Bool.false 750794019435 1099511627776 90929008505687 19044640904708096 Bool.false 265414407243 1099511627776 90949250692337 19044640904708096 Bool.false

noncomputable abbrev qz207 := (@HMul.hMul Real Real Real qz268 qz433 qz561)

noncomputable def ep939 := @Enclosure.Complex.IsNear.of_eq qz477 (Complex.mk (@HMul.hMul Real Real Real qz0 qz121 (Real.cos qz207)) (@HMul.hMul Real Real Real qz0 qz121 (@Neg.neg Real Real.instNeg (Real.sin qz207)))) Bool.false 241004268001 1099511627776 3904160084759 19044640904708096 Bool.true 7134354801 68719476736 1947760141677 9522320452354048 (BSN.cpow_neg_s_mk qz148 115476 1000 17 qz149 rfl)

noncomputable def ep940 := @Enclosure.Real.IsNear.mulLit_ff qz148 qz561 115476 1000 0 1 3189913004350711 1125899906842624 31250000017321 4330250000000000000 92089598522600675859 281474976710656000 902156250500039949 1082562500000000000000 qz150 (BSN.isNear_log_sfrac 17 1 3189913004350711 1125899906842624 31250000017321 4330250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz394) Bool.false 53517859495200818200576 18889465931478580854784 1000000000554272 138568000000000000000 3189913004350711 1125899906842624 31250000017321 4330250000000000000 (BSN.log_rat_reduce_isNear 17 1 4 34 32 31784 524288 24973259072661432 36028797018963968 138568 1000000000000000 rfl rfl rfl rfl (ep427 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep941 := nat_lit 814220747365819228429870698201760000

noncomputable def ep942 := BSN.cos_dyadic_bound_f 949916740 2147483648 2 1 1048576 277407 ep941 ep71 ep941 ep941 ep72 ep941 947653 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 949916740) qz288 0 1 ep941 ep71 ep941 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 949916740) qz289 0 1 ep941 ep72 ep941 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz478 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 343060487) qz16)

noncomputable def ep943 := @Enclosure.Real.IsNear.cos_image qz207 qz478 Bool.false 343060487 1048576 875 1048576 Bool.false 947653 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz207 Bool.false 92089598522600675859 281474976710656000 902156250500039949 1082562500000000000000 343060487 1048576 875 1048576 (ep940 rfl) rfl) (Enclosure.sfrac_false_div 343060487 1048576) (BSN.cos_reduce0 qz478 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 66844448127308764545024) qz19) 226375608064910080 72057594037927936 Bool.false 947653 1048576 52 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q0 343060487 1048576 226375608064910080 72057594037927936 52 66844448127308764545024 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 947653 1048576 66844448127308764545024 151115727451828646838272 949916740 2147483648 277407 277136 (ep942 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep944 := BSN.sin_dyadic_bound_f 949916740 2147483648 2 1 1048576 277407 ep941 ep67 ep941 ep941 ep68 ep941 448848 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 949916740) qz292 0 1 ep941 ep67 ep941 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 949916740) qz293 0 1 ep941 ep68 ep941 rfl rfl rfl rfl) rfl rfl

noncomputable def ep945 := @Enclosure.Real.IsNear.sin_image qz207 qz478 Bool.false 343060487 1048576 875 1048576 Bool.false 448848 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz207 Bool.false 92089598522600675859 281474976710656000 902156250500039949 1082562500000000000000 343060487 1048576 875 1048576 (ep940 rfl) rfl) (Enclosure.sfrac_false_div 343060487 1048576) (BSN.sin_reduce0 qz478 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 66844448127308764545024) qz19) 226375608064910080 72057594037927936 Bool.false 448848 1048576 52 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q0 343060487 1048576 226375608064910080 72057594037927936 52 66844448127308764545024 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 448848 1048576 66844448127308764545024 151115727451828646838272 949916740 2147483648 277407 277136 (ep944 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep946 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz121 (Real.cos qz207)) (@HMul.hMul Real Real Real qz0 qz121 (@Neg.neg Real Real.instNeg (Real.sin qz207))) Bool.false 241004268001 1099511627776 3904160084759 19044640904708096 Bool.true 7134354801 68719476736 1947760141677 9522320452354048 (@Enclosure.Real.IsNear.mulLit_ff qz121 (Real.cos qz207) 254317 1048576 1 1048576 947653 1048576 15286947 18162384896 241004268001 1099511627776 3904160084759 19044640904708096 qz396 (@Enclosure.Real.IsNear.recentre' (Real.cos qz207) Bool.false 947653 1048576 122295576 145299079168 947653 1048576 15286947 18162384896 (ep943 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz121 (@Neg.neg Real Real.instNeg (Real.sin qz207)) 254317 1048576 1 1048576 28053 65536 15286947 18162384896 7134354801 68719476736 1947760141677 9522320452354048 qz396 (@Enclosure.Real.IsNear.neg (Real.sin qz207) Bool.false 28053 65536 15286947 18162384896 (@Enclosure.Real.IsNear.recentre' (Real.sin qz207) Bool.false 448848 1048576 122295576 145299079168 28053 65536 15286947 18162384896 (ep945 rfl rfl) rfl)) rfl)

noncomputable def ep947 := @ep938 241004268001 1099511627776 3904160084759 19044640904708096 Bool.true 7134354801 68719476736 1947760141677 9522320452354048 Bool.false 1090493749444205489422336 247949571859 274877906944 47416584295223 9522320452354048 Bool.false 10394833123555537846272 151264730427 1099511627776 94844770975691 19044640904708096 EMRow36.d12 (ep939 ep946) rfl rfl

noncomputable abbrev qz208 := (@HMul.hMul Real Real Real qz268 qz433 qz562)

noncomputable def ep948 := @Enclosure.Complex.IsNear.of_eq qz476 (Complex.mk (@HMul.hMul Real Real Real qz0 qz123 (Real.cos qz208)) (@HMul.hMul Real Real Real qz0 qz123 (@Neg.neg Real Real.instNeg (Real.sin qz208)))) Bool.false 187900255015 1099511627776 3791368075009 19044640904708096 Bool.true 178481330405 1099511627776 3790707971699 19044640904708096 (BSN.cpow_neg_s_mk qz148 115476 1000 18 qz149 rfl)

noncomputable def ep949 := @Enclosure.Real.IsNear.mulLit_ff qz148 qz562 115476 1000 0 1 3254268794313975 1125899906842624 31250000017321 4330250000000000000 3757899432922005771 11258999068426240 902156250500039949 1082562500000000000000 qz150 (BSN.isNear_log_sfrac 18 1 3254268794313975 1125899906842624 31250000017321 4330250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz398) Bool.false 54597570484265130393600 18889465931478580854784 1000000000554272 138568000000000000000 3254268794313975 1125899906842624 31250000017321 4330250000000000000 (BSN.log_rat_reduce_isNear 18 1 4 36 32 61752 524288 24973259072661432 36028797018963968 138568 1000000000000000 rfl rfl rfl rfl (ep438 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep950 := nat_lit 253159454593132909116510077311194996069733332368060708554750126755147551932416

noncomputable def ep951 := nat_lit 50183230950324118439366957856092827010073738022683938782514705429273051136

noncomputable def ep952 := nat_lit 759377997317498079112651498017872802555179849628136757786685350854584109694976

noncomputable def ep953 := BSN.cos_dyadic_bound_f 1631435196 2147483648 3 2 1048576 277407 ep950 ep155 ep951 ep952 ep158 ep951 760265 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1631435196) qz288 0 2 ep950 ep155 ep951 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1631435196) qz289 0 2 ep952 ep158 ep951 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz479 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 349981657) qz16)

noncomputable def ep954 := @Enclosure.Real.IsNear.cos_image qz208 qz479 Bool.false 349981657 1048576 875 1048576 Bool.false 760265 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz208 Bool.false 3757899432922005771 11258999068426240 902156250500039949 1082562500000000000000 349981657 1048576 875 1048576 (ep949 rfl) rfl) (Enclosure.sfrac_false_div 349981657 1048576) (BSN.cos_reduce0 qz479 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 114802045973195541970944) qz19) 226375608064910080 72057594037927936 Bool.false 760265 1048576 53 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q0 349981657 1048576 226375608064910080 72057594037927936 53 114802045973195541970944 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 760265 1048576 114802045973195541970944 151115727451828646838272 1631435196 2147483648 277407 277136 (ep953 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep955 := nat_lit 7084012348261691055376635521332429056

noncomputable def ep956 := BSN.sin_dyadic_bound_f 1631435196 2147483648 2 1 1048576 277407 ep955 ep67 ep955 ep955 ep68 ep955 722155 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1631435196) qz292 0 1 ep955 ep67 ep955 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1631435196) qz293 0 1 ep955 ep68 ep955 rfl rfl rfl rfl) rfl rfl

noncomputable def ep957 := @Enclosure.Real.IsNear.sin_image qz208 qz479 Bool.false 349981657 1048576 875 1048576 Bool.false 722155 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz208 Bool.false 3757899432922005771 11258999068426240 902156250500039949 1082562500000000000000 349981657 1048576 875 1048576 (ep949 rfl) rfl) (Enclosure.sfrac_false_div 349981657 1048576) (BSN.sin_reduce0 qz479 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 114802045973195541970944) qz19) 226375608064910080 72057594037927936 Bool.false 722155 1048576 53 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q0 349981657 1048576 226375608064910080 72057594037927936 53 114802045973195541970944 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 722155 1048576 114802045973195541970944 151115727451828646838272 1631435196 2147483648 277407 277136 (ep956 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep958 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz123 (Real.cos qz208)) (@HMul.hMul Real Real Real qz0 qz123 (@Neg.neg Real Real.instNeg (Real.sin qz208))) Bool.false 187900255015 1099511627776 3791368075009 19044640904708096 Bool.true 178481330405 1099511627776 3790707971699 19044640904708096 (@Enclosure.Real.IsNear.mulLit_ff qz123 (Real.cos qz208) 247151 1048576 1 1048576 760265 1048576 15286947 18162384896 187900255015 1099511627776 3791368075009 19044640904708096 qz400 (@Enclosure.Real.IsNear.recentre' (Real.cos qz208) Bool.false 760265 1048576 122295576 145299079168 760265 1048576 15286947 18162384896 (ep954 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz123 (@Neg.neg Real Real.instNeg (Real.sin qz208)) 247151 1048576 1 1048576 722155 1048576 15286947 18162384896 178481330405 1099511627776 3790707971699 19044640904708096 qz400 (@Enclosure.Real.IsNear.neg (Real.sin qz208) Bool.false 722155 1048576 15286947 18162384896 (@Enclosure.Real.IsNear.recentre' (Real.sin qz208) Bool.false 722155 1048576 122295576 145299079168 722155 1048576 15286947 18162384896 (ep957 rfl rfl) rfl)) rfl)

noncomputable def ep959 := @ep936 187900255015 1099511627776 3791368075009 19044640904708096 Bool.true 178481330405 1099511627776 3790707971699 19044640904708096 Bool.false 324273066173818411679744 1179698542451 1099511627776 98624536665455 19044640904708096 Bool.true 29924968144339025788928 13608299989 549755813888 49317739473695 9522320452354048 (ep937 (BSN.head_sum_c_succ qz145 17 18 rfl rfl) (ep947 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep948 ep958) rfl rfl

noncomputable abbrev qz209 := (@HMul.hMul Real Real Real qz268 qz433 qz563)

noncomputable def ep960 := @Enclosure.Complex.IsNear.of_eq qz475 (Complex.mk (@HMul.hMul Real Real Real qz0 qz125 (Real.cos qz209)) (@HMul.hMul Real Real Real qz0 qz125 (@Neg.neg Real Real.instNeg (Real.sin qz209)))) Bool.false 94817532645 549755813888 1845541143915 9522320452354048 Bool.true 20791273811 137438953472 461175532999 2380580113088512 (BSN.cpow_neg_s_mk qz148 115476 1000 19 qz149 rfl)

noncomputable def ep961 := @Enclosure.Real.IsNear.mulLit_ff qz148 qz563 115476 1000 0 1 3315143513283831 1125899906842624 31250000017321 4330250000000000000 95704878084990917139 281474976710656000 902156250500039949 1082562500000000000000 qz150 (BSN.isNear_log_sfrac 19 1 3315143513283831 1125899906842624 31250000017321 4330250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz402) Bool.false 55618878793361701994496 18889465931478580854784 1000000000554272 138568000000000000000 3315143513283831 1125899906842624 31250000017321 4330250000000000000 (BSN.log_rat_reduce_isNear 19 1 4 38 32 90099 524288 24973259072661432 36028797018963968 138568 1000000000000000 rfl rfl rfl rfl (ep452 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep962 := nat_lit 204268312858222935540796074379849608751787612959295107992071703666284041973281

noncomputable def ep963 := nat_lit 32674245455444236559789979649047895710266277083323319306930563248947834401

noncomputable def ep964 := nat_lit 612739590083757918149268643180250730463942306323718677337601249872354230251041

noncomputable def ep965 := BSN.cos_dyadic_bound_f 1546235699 2147483648 3 2 1048576 277407 ep962 ep155 ep963 ep964 ep158 ep963 788310 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1546235699) qz288 0 2 ep962 ep155 ep963 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1546235699) qz289 0 2 ep964 ep158 ep963 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz480 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 356528453) qz16)

noncomputable def ep966 := @Enclosure.Real.IsNear.cos_image qz209 qz480 Bool.false 356528453 1048576 875 1048576 Bool.false 788310 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz209 Bool.false 95704878084990917139 281474976710656000 902156250500039949 1082562500000000000000 356528453 1048576 875 1048576 (ep961 rfl) rfl) (Enclosure.sfrac_false_div 356528453 1048576) (BSN.cos_reduce0 qz480 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 108806664398371853172736) qz19) 226375608064910080 72057594037927936 Bool.false 788310 1048576 54 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q0 356528453 1048576 226375608064910080 72057594037927936 54 108806664398371853172736 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 788310 1048576 108806664398371853172736 151115727451828646838272 1546235699 2147483648 277407 277136 (ep965 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep967 := nat_lit 5716139033949772338216664940469997201

noncomputable def ep968 := BSN.sin_dyadic_bound_f 1546235699 2147483648 2 1 1048576 277407 ep967 ep67 ep967 ep967 ep68 ep967 691432 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1546235699) qz292 0 1 ep967 ep67 ep967 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1546235699) qz293 0 1 ep967 ep68 ep967 rfl rfl rfl rfl) rfl rfl

noncomputable def ep969 := @Enclosure.Real.IsNear.sin_image qz209 qz480 Bool.false 356528453 1048576 875 1048576 Bool.false 691432 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz209 Bool.false 95704878084990917139 281474976710656000 902156250500039949 1082562500000000000000 356528453 1048576 875 1048576 (ep961 rfl) rfl) (Enclosure.sfrac_false_div 356528453 1048576) (BSN.sin_reduce0 qz480 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 108806664398371853172736) qz19) 226375608064910080 72057594037927936 Bool.false 691432 1048576 54 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q0 356528453 1048576 226375608064910080 72057594037927936 54 108806664398371853172736 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 691432 1048576 108806664398371853172736 151115727451828646838272 1546235699 2147483648 277407 277136 (ep968 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep970 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz125 (Real.cos qz209)) (@HMul.hMul Real Real Real qz0 qz125 (@Neg.neg Real Real.instNeg (Real.sin qz209))) Bool.false 94817532645 549755813888 1845541143915 9522320452354048 Bool.true 20791273811 137438953472 461175532999 2380580113088512 (@Enclosure.Real.IsNear.mulLit_ff qz125 (Real.cos qz209) 240559 1048576 1 1048576 394155 524288 15286947 18162384896 94817532645 549755813888 1845541143915 9522320452354048 qz404 (@Enclosure.Real.IsNear.recentre' (Real.cos qz209) Bool.false 788310 1048576 122295576 145299079168 394155 524288 15286947 18162384896 (ep966 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz125 (@Neg.neg Real Real.instNeg (Real.sin qz209)) 240559 1048576 1 1048576 86429 131072 15286947 18162384896 20791273811 137438953472 461175532999 2380580113088512 qz404 (@Enclosure.Real.IsNear.neg (Real.sin qz209) Bool.false 86429 131072 15286947 18162384896 (@Enclosure.Real.IsNear.recentre' (Real.sin qz209) Bool.false 691432 1048576 122295576 145299079168 86429 131072 15286947 18162384896 (ep969 rfl rfl) rfl)) rfl)

noncomputable def ep971 := @ep934 94817532645 549755813888 1845541143915 9522320452354048 Bool.true 20791273811 137438953472 461175532999 2380580113088512 Bool.false 752799112007844792107008 1369333607741 1099511627776 102315618953285 19044640904708096 Bool.true 13300434164755753598976 96773395233 549755813888 51162441605691 9522320452354048 (ep935 (BSN.head_sum_c_succ qz145 18 19 rfl rfl) (ep959 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep960 ep970) rfl rfl

noncomputable abbrev qz210 := (@HMul.hMul Real Real Real qz268 qz433 qz564)

noncomputable def ep972 := @Enclosure.Complex.IsNear.of_eq qz474 (Complex.mk (@HMul.hMul Real Real Real qz0 qz127 (Real.cos qz210)) (@HMul.hMul Real Real Real qz0 qz127 (@Neg.neg Real Real.instNeg (Real.sin qz210)))) Bool.false 115054172769 549755813888 1798634036131 9522320452354048 Bool.true 86582133161 1099511627776 3586665316569 19044640904708096 (BSN.cpow_neg_s_mk qz148 115476 1000 20 qz149 rfl)

noncomputable def ep973 := @Enclosure.Real.IsNear.mulLit_ff qz148 qz564 115476 1000 0 1 3372893643545847 1125899906842624 31250000017321 4330250000000000000 97372066595525057043 281474976710656000 902156250500039949 1082562500000000000000 qz150 (BSN.isNear_log_sfrac 20 1 3372893643545847 1125899906842624 31250000017321 4330250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz406) Bool.false 56587765202795681021952 18889465931478580854784 1000000000554272 138568000000000000000 3372893643545847 1125899906842624 31250000017321 4330250000000000000 (BSN.log_rat_reduce_isNear 20 1 4 40 32 116991 524288 24973259072661432 36028797018963968 138568 1000000000000000 rfl rfl rfl rfl (ep463 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep974 := nat_lit 356742749545551736027735863360405681

noncomputable def ep975 := BSN.cos_dyadic_bound_f 772838571 2147483648 2 1 1048576 277407 ep974 ep71 ep974 ep974 ep72 ep974 981402 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 772838571) qz288 0 1 ep974 ep71 ep974 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 772838571) qz289 0 1 ep974 ep72 ep974 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz481 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 362739215) qz16)

noncomputable def ep976 := @Enclosure.Real.IsNear.cos_image qz210 qz481 Bool.false 362739215 1048576 437 524288 Bool.false 981402 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz210 Bool.false 97372066595525057043 281474976710656000 902156250500039949 1082562500000000000000 362739215 1048576 437 524288 (ep973 rfl) rfl) (Enclosure.sfrac_false_div 362739215 1048576) (BSN.cos_reduce0 qz481 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 54383679713666012282880) qz19) 226375608064910080 72057594037927936 Bool.false 981402 1048576 55 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q0 362739215 1048576 226375608064910080 72057594037927936 55 54383679713666012282880 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 981402 1048576 54383679713666012282880 151115727451828646838272 772838571 2147483648 277407 277136 (ep975 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep977 := BSN.sin_dyadic_bound_f 772838571 2147483648 2 1 1048576 277407 ep974 ep67 ep974 ep974 ep68 ep974 369269 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 772838571) qz292 0 1 ep974 ep67 ep974 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 772838571) qz293 0 1 ep974 ep68 ep974 rfl rfl rfl rfl) rfl rfl

noncomputable def ep978 := @Enclosure.Real.IsNear.sin_image qz210 qz481 Bool.false 362739215 1048576 437 524288 Bool.false 369269 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz210 Bool.false 97372066595525057043 281474976710656000 902156250500039949 1082562500000000000000 362739215 1048576 437 524288 (ep973 rfl) rfl) (Enclosure.sfrac_false_div 362739215 1048576) (BSN.sin_reduce0 qz481 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 54383679713666012282880) qz19) 226375608064910080 72057594037927936 Bool.false 369269 1048576 55 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q0 362739215 1048576 226375608064910080 72057594037927936 55 54383679713666012282880 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 369269 1048576 54383679713666012282880 151115727451828646838272 772838571 2147483648 277407 277136 (ep977 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep979 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz127 (Real.cos qz210)) (@HMul.hMul Real Real Real qz0 qz127 (@Neg.neg Real Real.instNeg (Real.sin qz210))) Bool.false 115054172769 549755813888 1798634036131 9522320452354048 Bool.true 86582133161 1099511627776 3586665316569 19044640904708096 (@Enclosure.Real.IsNear.mulLit_ff qz127 (Real.cos qz210) 234469 1048576 1 1048576 490701 524288 7634813 9081192448 115054172769 549755813888 1798634036131 9522320452354048 qz408 (@Enclosure.Real.IsNear.recentre' (Real.cos qz210) Bool.false 981402 1048576 61078504 72649539584 490701 524288 7634813 9081192448 (ep976 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz127 (@Neg.neg Real Real.instNeg (Real.sin qz210)) 234469 1048576 1 1048576 369269 1048576 7634813 9081192448 86582133161 1099511627776 3586665316569 19044640904708096 qz408 (@Enclosure.Real.IsNear.neg (Real.sin qz210) Bool.false 369269 1048576 7634813 9081192448 (@Enclosure.Real.IsNear.recentre' (Real.sin qz210) Bool.false 369269 1048576 61078504 72649539584 369269 1048576 7634813 9081192448 (ep978 rfl rfl) rfl)) rfl)

noncomputable def ep980 := @ep932 115054172769 549755813888 1798634036131 9522320452354048 Bool.true 86582133161 1099511627776 3586665316569 19044640904708096 Bool.false 879302512791509115338752 1599441953279 1099511627776 105912887025547 19044640904708096 Bool.true 154002504402130777931776 280128923627 1099511627776 105911548527951 19044640904708096 (ep933 (BSN.head_sum_c_succ qz145 19 20 rfl rfl) (ep971 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep972 ep979) rfl rfl

noncomputable abbrev qz211 := (@HMul.hMul Real Real Real qz268 qz433 qz565)

noncomputable def ep981 := @Enclosure.Complex.IsNear.of_eq qz473 (Complex.mk (@HMul.hMul Real Real Real qz0 qz129 (Real.cos qz211)) (@HMul.hMul Real Real Real qz0 qz129 (@Neg.neg Real Real.instNeg (Real.sin qz211)))) Bool.false 114983447589 549755813888 1766387575011 9522320452354048 Bool.false 34216414039 549755813888 1754159815061 9522320452354048 (BSN.cpow_neg_s_mk qz148 115476 1000 21 qz149 rfl)

noncomputable def ep982 := @Enclosure.Real.IsNear.mulLit_ff qz148 qz565 115476 1000 0 1 3427826275261687 1125899906842624 31250000017321 4330250000000000000 98957916740529642003 281474976710656000 902156250500039949 1082562500000000000000 qz150 (BSN.isNear_log_sfrac 21 1 3427826275261687 1125899906842624 31250000017321 4330250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz410) Bool.false 57509381830540779323392 18889465931478580854784 1000000000554272 138568000000000000000 3427826275261687 1125899906842624 31250000017321 4330250000000000000 (BSN.log_rat_reduce_isNear 21 1 4 42 32 142571 524288 24973259072661432 36028797018963968 138568 1000000000000000 rfl rfl rfl rfl (ep474 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep983 := nat_lit 3692906307518741427904094448236883144123743430141012462181939902051152543416320

noncomputable def ep984 := nat_lit 3291240510280662754439087202471560572767761077015947913078142629649643012096

noncomputable def ep985 := nat_lit 9666568796961011238146393604197359041301513561006530628141049417305014382166016

noncomputable def ep986 := BSN.sin_dyadic_bound_f 2752136388 2147483648 3 2 1048576 277407 ep983 ep187 ep984 ep985 ep189 ep984 1005021 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2752136388) qz292 0 2 ep983 ep187 ep984 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2752136388) qz293 0 2 ep985 ep189 ep984 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz482 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 368646967) qz16)

noncomputable def ep987 := @Enclosure.Real.IsNear.cos_image qz211 qz482 Bool.false 368646967 1048576 875 1048576 Bool.false 1005021 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz211 Bool.false 98957916740529642003 281474976710656000 902156250500039949 1082562500000000000000 368646967 1048576 875 1048576 (ep982 rfl) rfl) (Enclosure.sfrac_false_div 368646967 1048576) (BSN.cos_reduce3 qz482 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 193664381492366235664384) qz19) 226375608064910080 72057594037927936 Bool.false 1005021 1048576 55 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q3 368646967 1048576 226375608064910080 72057594037927936 55 193664381492366235664384 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1005021 1048576 193664381492366235664384 151115727451828646838272 2752136388 2147483648 277407 277136 (ep986 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep988 := nat_lit 2053077388848314421170914287777144662545532021668125122506890231197151254347776

noncomputable def ep989 := nat_lit 6152649685524381938003864688926490866491060542850343471694514408332154477019136

noncomputable def ep990 := BSN.cos_dyadic_bound_f 2752136388 2147483648 3 2 1048576 277407 ep988 ep155 ep984 ep989 ep158 ep984 299071 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2752136388) qz288 0 2 ep988 ep155 ep984 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2752136388) qz289 0 2 ep989 ep158 ep984 rfl rfl rfl rfl) rfl rfl

noncomputable def ep991 := @Enclosure.Real.IsNear.sin_image qz211 qz482 Bool.false 368646967 1048576 875 1048576 Bool.true 299071 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz211 Bool.false 98957916740529642003 281474976710656000 902156250500039949 1082562500000000000000 368646967 1048576 875 1048576 (ep982 rfl) rfl) (Enclosure.sfrac_false_div 368646967 1048576) (BSN.sin_reduce3 qz482 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 193664381492366235664384) qz19) 226375608064910080 72057594037927936 Bool.false 299071 1048576 55 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q3 368646967 1048576 226375608064910080 72057594037927936 55 193664381492366235664384 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 299071 1048576 193664381492366235664384 151115727451828646838272 2752136388 2147483648 277407 277136 (ep990 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep992 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz129 (Real.cos qz211)) (@HMul.hMul Real Real Real qz0 qz129 (@Neg.neg Real Real.instNeg (Real.sin qz211))) Bool.false 114983447589 549755813888 1766387575011 9522320452354048 Bool.false 34216414039 549755813888 1754159815061 9522320452354048 (@Enclosure.Real.IsNear.mulLit_ff qz129 (Real.cos qz211) 114409 524288 1 524288 1005021 1048576 15286947 18162384896 114983447589 549755813888 1766387575011 9522320452354048 qz412 (@Enclosure.Real.IsNear.recentre' (Real.cos qz211) Bool.false 1005021 1048576 122295576 145299079168 1005021 1048576 15286947 18162384896 (ep987 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz129 (@Neg.neg Real Real.instNeg (Real.sin qz211)) 114409 524288 1 524288 299071 1048576 15286947 18162384896 34216414039 549755813888 1754159815061 9522320452354048 qz412 (@Enclosure.Real.IsNear.neg (Real.sin qz211) Bool.true 299071 1048576 15286947 18162384896 (@Enclosure.Real.IsNear.recentre' (Real.sin qz211) Bool.true 299071 1048576 122295576 145299079168 299071 1048576 15286947 18162384896 (ep991 rfl rfl) rfl)) rfl)

noncomputable def ep993 := @ep930 114983447589 549755813888 1766387575011 9522320452354048 Bool.false 34216414039 549755813888 1754159815061 9522320452354048 Bool.false 1005728150417386887970816 1829408848457 1099511627776 109445662175569 19044640904708096 Bool.true 116381159305452309184512 211696095549 1099511627776 109419868158073 19044640904708096 (ep931 (BSN.head_sum_c_succ qz145 20 21 rfl rfl) (ep980 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep981 ep992) rfl rfl

noncomputable abbrev qz212 := (@HMul.hMul Real Real Real qz268 qz433 qz566)

noncomputable def ep994 := @Enclosure.Complex.IsNear.of_eq qz472 (Complex.mk (@HMul.hMul Real Real Real qz0 qz131 (Real.cos qz212)) (@HMul.hMul Real Real Real qz0 qz131 (@Neg.neg Real Real.instNeg (Real.sin qz212)))) Bool.false 84844576197 1099511627776 3424092980667 19044640904708096 Bool.false 218523167031 1099511627776 3434450280469 19044640904708096 (BSN.cpow_neg_s_mk qz148 115476 1000 22 qz149 rfl)

noncomputable def ep995 := @Enclosure.Real.IsNear.mulLit_ff qz148 qz566 115476 1000 0 1 3480203401436407 1125899906842624 31250000017321 4330250000000000000 100469991996067633683 281474976710656000 902156250500039949 1082562500000000000000 qz150 (BSN.isNear_log_sfrac 22 1 3480203401436407 1125899906842624 31250000017321 4330250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz414) Bool.false 58388124189833310502912 18889465931478580854784 1000000000554272 138568000000000000000 3480203401436407 1125899906842624 31250000017321 4330250000000000000 (BSN.log_rat_reduce_isNear 22 1 4 44 32 166961 524288 24973259072661432 36028797018963968 138568 1000000000000000 rfl rfl rfl rfl (ep489 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep996 := nat_lit 400092690419413223279949078661939456

noncomputable def ep997 := BSN.sin_dyadic_bound_f 795316796 2147483648 2 1 1048576 277407 ep996 ep67 ep996 ep996 ep68 ep996 379521 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 795316796) qz292 0 1 ep996 ep67 ep996 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 795316796) qz293 0 1 ep996 ep68 ep996 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz483 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 187139943) qz26)

noncomputable def ep998 := @Enclosure.Real.IsNear.cos_image qz212 qz483 Bool.false 187139943 524288 875 1048576 Bool.false 379521 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz212 Bool.false 100469991996067633683 281474976710656000 902156250500039949 1082562500000000000000 187139943 524288 875 1048576 (ep995 rfl) rfl) (Enclosure.sfrac_false_div 187139943 524288) (BSN.cos_reduce3 qz483 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 27982722092171805065216) qz302) 226375608064910080 72057594037927936 Bool.false 379521 1048576 56 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q3 187139943 524288 226375608064910080 72057594037927936 56 27982722092171805065216 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 379521 1048576 27982722092171805065216 75557863725914323419136 795316796 2147483648 277407 277136 (ep997 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep999 := BSN.cos_dyadic_bound_f 795316796 2147483648 2 1 1048576 277407 ep996 ep71 ep996 ep996 ep72 ep996 977483 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 795316796) qz288 0 1 ep996 ep71 ep996 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 795316796) qz289 0 1 ep996 ep72 ep996 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1000 := @Enclosure.Real.IsNear.sin_image qz212 qz483 Bool.false 187139943 524288 875 1048576 Bool.true 977483 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz212 Bool.false 100469991996067633683 281474976710656000 902156250500039949 1082562500000000000000 187139943 524288 875 1048576 (ep995 rfl) rfl) (Enclosure.sfrac_false_div 187139943 524288) (BSN.sin_reduce3 qz483 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 27982722092171805065216) qz302) 226375608064910080 72057594037927936 Bool.false 977483 1048576 56 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q3 187139943 524288 226375608064910080 72057594037927936 56 27982722092171805065216 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 977483 1048576 27982722092171805065216 75557863725914323419136 795316796 2147483648 277407 277136 (ep999 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1001 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz131 (Real.cos qz212)) (@HMul.hMul Real Real Real qz0 qz131 (@Neg.neg Real Real.instNeg (Real.sin qz212))) Bool.false 84844576197 1099511627776 3424092980667 19044640904708096 Bool.false 218523167031 1099511627776 3434450280469 19044640904708096 (@Enclosure.Real.IsNear.mulLit_ff qz131 (Real.cos qz212) 223557 1048576 1 1048576 379521 1048576 15286947 18162384896 84844576197 1099511627776 3424092980667 19044640904708096 qz416 (@Enclosure.Real.IsNear.recentre' (Real.cos qz212) Bool.false 379521 1048576 122295576 145299079168 379521 1048576 15286947 18162384896 (ep998 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz131 (@Neg.neg Real Real.instNeg (Real.sin qz212)) 223557 1048576 1 1048576 977483 1048576 15286947 18162384896 218523167031 1099511627776 3434450280469 19044640904708096 qz416 (@Enclosure.Real.IsNear.neg (Real.sin qz212) Bool.true 977483 1048576 15286947 18162384896 (@Enclosure.Real.IsNear.recentre' (Real.sin qz212) Bool.true 977483 1048576 122295576 145299079168 977483 1048576 15286947 18162384896 (ep1000 rfl rfl) rfl)) rfl)

noncomputable def ep1002 := @ep927 84844576197 1099511627776 3424092980667 19044640904708096 Bool.false 218523167031 1099511627776 3434450280469 19044640904708096 Bool.false ep928 957126712327 549755813888 28217438789059 4761160226177024 Bool.false 7506444478116928684032 3413535741 549755813888 56427159219271 9522320452354048 (ep929 (BSN.head_sum_c_succ qz145 21 22 rfl rfl) (ep993 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep994 ep1001) rfl rfl

noncomputable abbrev qz213 := (@HMul.hMul Real Real Real qz268 qz433 qz421)

noncomputable def ep1003 := @Enclosure.Complex.IsNear.of_eq qz206 (Complex.mk (@HMul.hMul Real Real Real qz0 qz135 (Real.cos qz213)) (@HMul.hMul Real Real Real qz0 qz135 (@Neg.neg Real Real.instNeg (Real.sin qz213)))) Bool.true 161210512689 1099511627776 3355170411551 19044640904708096 Bool.false 163012131009 1099511627776 3355313136591 19044640904708096 (BSN.cpow_neg_s_mk qz148 115476 1000 23 qz149 rfl)

noncomputable def ep1004 := @Enclosure.Real.IsNear.mulLit_ff qz148 qz138 115476 1000 0 1 3530250507853047 1125899906842624 31250000017321 4330250000000000000 101914801911209613843 281474976710656000 902156250500039949 1082562500000000000000 qz150 (BSN.isNear_log_sfrac 23 1 3530250507853047 1125899906842624 31250000017321 4330250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz422 Bool.false 59227775304360265777152 18889465931478580854784 1000000000554272 138568000000000000000 3530250507853047 1125899906842624 31250000017321 4330250000000000000 (BSN.log_rat_reduce_isNear 23 1 4 46 32 190266 524288 24973259072661432 36028797018963968 138568 1000000000000000 rfl rfl rfl rfl (ep514 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1005 := nat_lit 297478912027657555435710933531157629158872237220778727909933514566589231190625

noncomputable def ep1006 := nat_lit 69287126479598172329268995542575191595351048189207424175833824497250390625

noncomputable def ep1007 := nat_lit 892298161830013469962474262602387737093426009565957768881448876050773192790625

noncomputable def ep1008 := BSN.cos_dyadic_bound_f 1698562645 2147483648 3 2 1048576 277407 ep1005 ep155 ep1006 ep1007 ep158 ep1006 737323 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1698562645) qz288 0 2 ep1005 ep155 ep1006 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1698562645) qz289 0 2 ep1007 ep158 ep1006 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz484 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 189831111) qz26)

noncomputable def ep1009 := @Enclosure.Real.IsNear.cos_image qz213 qz484 Bool.false 189831111 524288 875 1048576 Bool.true 737323 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz213 Bool.false 101914801911209613843 281474976710656000 902156250500039949 1082562500000000000000 189831111 524288 875 1048576 (ep1004 rfl) rfl) (Enclosure.sfrac_false_div 189831111 524288) (BSN.cos_reduce2 qz484 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 59762860152489972334592) qz302) 226375608064910080 72057594037927936 Bool.false 737323 1048576 57 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q2 189831111 524288 226375608064910080 72057594037927936 57 59762860152489972334592 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 737323 1048576 59762860152489972334592 75557863725914323419136 1698562645 2147483648 277407 277136 (ep1008 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1010 := nat_lit 8323888903607386105084593394285800625

noncomputable def ep1011 := BSN.sin_dyadic_bound_f 1698562645 2147483648 2 1 1048576 277407 ep1010 ep67 ep1010 ep1010 ep68 ep1010 745563 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1698562645) qz292 0 1 ep1010 ep67 ep1010 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1698562645) qz293 0 1 ep1010 ep68 ep1010 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1012 := @Enclosure.Real.IsNear.sin_image qz213 qz484 Bool.false 189831111 524288 875 1048576 Bool.true 745563 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz213 Bool.false 101914801911209613843 281474976710656000 902156250500039949 1082562500000000000000 189831111 524288 875 1048576 (ep1004 rfl) rfl) (Enclosure.sfrac_false_div 189831111 524288) (BSN.sin_reduce2 qz484 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 59762860152489972334592) qz302) 226375608064910080 72057594037927936 Bool.false 745563 1048576 57 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q2 189831111 524288 226375608064910080 72057594037927936 57 59762860152489972334592 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 745563 1048576 59762860152489972334592 75557863725914323419136 1698562645 2147483648 277407 277136 (ep1011 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1013 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz135 (Real.cos qz213)) (@HMul.hMul Real Real Real qz0 qz135 (@Neg.neg Real Real.instNeg (Real.sin qz213))) Bool.true 161210512689 1099511627776 3355170411551 19044640904708096 Bool.false 163012131009 1099511627776 3355313136591 19044640904708096 (@Enclosure.Real.IsNear.mulLit_ft qz135 (Real.cos qz213) 218643 1048576 1 1048576 737323 1048576 15286947 18162384896 161210512689 1099511627776 3355170411551 19044640904708096 qz424 (@Enclosure.Real.IsNear.recentre' (Real.cos qz213) Bool.true 737323 1048576 122295576 145299079168 737323 1048576 15286947 18162384896 (ep1009 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz135 (@Neg.neg Real Real.instNeg (Real.sin qz213)) 218643 1048576 1 1048576 745563 1048576 15286947 18162384896 163012131009 1099511627776 3355313136591 19044640904708096 qz424 (@Enclosure.Real.IsNear.neg (Real.sin qz213) Bool.true 745563 1048576 15286947 18162384896 (@Enclosure.Real.IsNear.recentre' (Real.sin qz213) Bool.true 745563 1048576 122295576 145299079168 745563 1048576 15286947 18162384896 (ep1012 rfl rfl) rfl)) rfl)

noncomputable def ep1014 := @ep925 161210512689 1099511627776 3355170411551 19044640904708096 Bool.false 163012131009 1099511627776 3355313136591 19044640904708096 Bool.false 963745532847908108369920 1753042911965 1099511627776 116224925567787 19044640904708096 Bool.false 93370088995528541995008 169839202491 1099511627776 116209631575133 19044640904708096 (ep926 (BSN.head_sum_c_succ qz145 22 23 rfl rfl) (ep1002 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1003 ep1013) rfl rfl

noncomputable def ep1015 := @Enclosure.Complex.IsNear.mul qz203 (@HAdd.hAdd Complex Complex Complex qz4 qz204 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz69 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz69 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz112 (@HMul.hMul Nat Nat Nat qz69 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz113 qz205 (@HSub.hSub Nat Nat Nat qz112 (@HMul.hMul Nat Nat Nat qz69 2 k) 1))))) Bool.true ep917 ep795 ep918 ep797 Bool.true

noncomputable abbrev qz214 := (Complex.re qz470)

noncomputable abbrev qz215 := (Complex.im qz470)

noncomputable def ep1016 := @Enclosure.Real.IsNear.subLit_tt_n (@HMul.hMul Real Real Real qz0 qz214 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz204 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz69 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz69 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz112 (@HMul.hMul Nat Nat Nat qz69 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz113 qz205 (@HSub.hSub Nat Nat Nat qz112 (@HMul.hMul Nat Nat Nat qz69 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz215 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz204 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz69 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz69 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz112 (@HMul.hMul Nat Nat Nat qz69 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz113 qz205 (@HSub.hSub Nat Nat Nat qz112 (@HMul.hMul Nat Nat Nat qz69 2 k) 1))))))) 22605123207768071248075 263914916601600638189568 395176037163458682922685

noncomputable def ep1017 := nat_lit 4571270270456324654081507328

noncomputable def ep1018 := nat_lit 1832742476400004431872000

noncomputable def ep1019 := nat_lit 31744932433724476764454912000

noncomputable def ep1020 := nat_lit 31019586208906102882136150388215802210233090048

noncomputable def ep1021 := @Enclosure.Real.IsNear.mulLit_tf qz214 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz204 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz69 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz69 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz112 (@HMul.hMul Nat Nat Nat qz69 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz113 qz205 (@HSub.hSub Nat Nat Nat qz112 (@HMul.hMul Nat Nat Nat qz69 2 k) 1)))))) 188038612475 1099511627776 3287235067405 19044640904708096 120215326577

noncomputable abbrev qz485 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) qz569 (Real.log (Enclosure.sfrac Bool.false 24 1)))

noncomputable abbrev qz216 := (Real.cos qz485)

noncomputable abbrev qz217 := (Real.sin qz485)

noncomputable abbrev qz486 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 24)))

noncomputable abbrev qz487 := (@Neg.neg Real Real.instNeg qz217)

noncomputable def ep1022 := @Enclosure.Complex.IsNear.of_eq qz203 (Complex.mk (@HMul.hMul Real Real Real qz0 qz486 qz216) (@HMul.hMul Real Real Real qz0 qz486 qz487)) Bool.true 188038612475 1099511627776 3287235067405 19044640904708096 Bool.true 61263740853 549755813888 1640966805807 9522320452354048 (BSN.cpow_neg_s_mk qz148 115476 1000 24 qz149 rfl)

noncomputable abbrev qz488 := (Real.sqrt (@Nat.cast Real Real.instNatCast 24))

noncomputable abbrev qz489 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 24) qz15)

noncomputable def ep1023 := @Enclosure.Real.IsNear.inv_image qz488 5136953 1048576 1 1048576 107019 107020 524288 (@Enclosure.Real.IsNear.of_eq qz488 (Real.sqrt qz489) Bool.false 5136953 1048576 1 1048576 (BSN.sqrt_natCast_div_one 24) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz489) Bool.false 5136953 1048576 1 1048576 5136953 1048576 1 1048576 (BSN.sqrt_enclosure 24 1 2568476 2568477 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep1024 := BSN.log_dyadic_bound 8 40 4 3 430080000000 524288 138568 5875957760 3932160 212580 48 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 8) (BSN.artanhQ 40) 0 3 5875957760 430080000000 3932160 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz490 := (Real.log (Enclosure.sfrac Bool.false 24 1))

noncomputable def ep1025 := @Enclosure.Real.IsNear.mulLit_ff qz148 qz490 115476 1000 0 1 3578169457974519 1125899906842624 31250000017321 4330250000000000000 103298174082266389011 281474976710656000 902156250500039949 1082562500000000000000 qz150 (BSN.isNear_log_sfrac 24 1 3578169457974519 1125899906842624 31250000017321 4330250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz489) Bool.false 60031721881041427759104 18889465931478580854784 1000000000554272 138568000000000000000 3578169457974519 1125899906842624 31250000017321 4330250000000000000 (BSN.log_rat_reduce_isNear 24 1 4 48 32 212580 524288 24973259072661432 36028797018963968 138568 1000000000000000 rfl rfl rfl rfl (ep1024 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1026 := nat_lit 1331885300635997379892938939761889451221406516873168562842263137071236720265345

noncomputable def ep1027 := nat_lit 428599438042109413486201489191816797291608122172360622964643156034110523521

noncomputable def ep1028 := nat_lit 3487577102575544008288243373155780859336640178660495747387794031981564755085441

noncomputable def ep1029 := BSN.sin_dyadic_bound_f 2133076591 2147483648 3 2 1048576 277407 ep1026 ep187 ep1027 ep1028 ep189 ep1027 878525 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2133076591) qz292 0 2 ep1026 ep187 ep1027 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2133076591) qz293 0 2 ep1028 ep189 ep1027 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz218 := qz485

noncomputable abbrev qz491 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 384815685) qz16)

noncomputable def ep1030 := @Enclosure.Real.IsNear.cos_image qz218 qz491 Bool.false 384815685 1048576 875 1048576 Bool.true 878525 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 103298174082266389011 281474976710656000 902156250500039949 1082562500000000000000 384815685 1048576 875 1048576 (ep1025 rfl) rfl) (Enclosure.sfrac_false_div 384815685 1048576) (BSN.cos_reduce1 qz491 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 150101920985130918215680) qz19) 226375608064910080 72057594037927936 Bool.false 878525 1048576 58 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q1 384815685 1048576 226375608064910080 72057594037927936 58 150101920985130918215680 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 878525 1048576 150101920985130918215680 151115727451828646838272 2133076591 2147483648 277407 277136 (ep1029 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1031 := nat_lit 740126766770239481902071056085134947032911001872725806300352695331146671491201

noncomputable def ep1032 := nat_lit 2219523101434634226879240765277021207504149789373832697655128799681371793426561

noncomputable def ep1033 := BSN.cos_dyadic_bound_f 2133076591 2147483648 3 2 1048576 277407 ep1031 ep155 ep1027 ep1032 ep158 ep1027 572454 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2133076591) qz288 0 2 ep1031 ep155 ep1027 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2133076591) qz289 0 2 ep1032 ep158 ep1027 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1034 := @Enclosure.Real.IsNear.sin_image qz218 qz491 Bool.false 384815685 1048576 875 1048576 Bool.false 572454 1048576 1 138568 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 103298174082266389011 281474976710656000 902156250500039949 1082562500000000000000 384815685 1048576 875 1048576 (ep1025 rfl) rfl) (Enclosure.sfrac_false_div 384815685 1048576) (BSN.sin_reduce1 qz491 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 150101920985130918215680) qz19) 226375608064910080 72057594037927936 Bool.false 572454 1048576 58 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q1 384815685 1048576 226375608064910080 72057594037927936 58 150101920985130918215680 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 572454 1048576 150101920985130918215680 151115727451828646838272 2133076591 2147483648 277407 277136 (ep1033 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1035 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz486 qz216) (@HMul.hMul Real Real Real qz0 qz486 qz487) Bool.true 188038612475 1099511627776 3287235067405 19044640904708096 Bool.true 61263740853 549755813888 1640966805807 9522320452354048 (@Enclosure.Real.IsNear.mulLit_ft qz486 qz216 214039 1048576 1 1048576 878525 1048576 15286947 18162384896 188038612475 1099511627776 3287235067405 19044640904708096 (@Enclosure.Real.IsNear.recentre' qz486 Bool.false 214039 1048576 1 1048576 214039 1048576 1 1048576 (ep1023 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' qz216 Bool.true 878525 1048576 122295576 145299079168 878525 1048576 15286947 18162384896 (ep1030 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz486 qz487 214039 1048576 1 1048576 286227 524288 15286947 18162384896 61263740853 549755813888 1640966805807 9522320452354048 (@Enclosure.Real.IsNear.recentre' qz486 Bool.false 214039 1048576 1 1048576 214039 1048576 1 1048576 (ep1023 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg qz217 Bool.false 286227 524288 15286947 18162384896 (@Enclosure.Real.IsNear.recentre' qz217 Bool.false 572454 1048576 122295576 145299079168 286227 524288 15286947 18162384896 (ep1034 rfl rfl) rfl)) rfl)

noncomputable def ep1036 := @ep1021 240029218368 0 1 22605123207768071248075 263914916601600638189568 395176037163458682922685 ep1017 (@Enclosure.Complex.IsNear.re_isNear qz203 Bool.true 188038612475 1099511627776 3287235067405 19044640904708096 Bool.true 61263740853 549755813888 1640966805807 9522320452354048 (ep1022 ep1035))

noncomputable def ep1037 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz204 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz69 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz69 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz112 (@HMul.hMul Nat Nat Nat qz69 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz113 qz205 (@HSub.hSub Nat Nat Nat qz112 (@HMul.hMul Nat Nat Nat qz69 2 k) 1))))) Bool.false 120215326577 240029218368 0 1 Bool.false

noncomputable def ep1038 := @Enclosure.Complex.IsNear.addLitP qz204 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz69 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz69 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz112 (@HMul.hMul Nat Nat Nat qz69 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz113 qz205 (@HSub.hSub Nat Nat Nat qz112 (@HMul.hMul Nat Nat Nat qz69 2 k) 1)))) Bool.false 415967393 833434786 0 1 Bool.true 86607000

noncomputable def ep1039 := @ep1038 416717393 0 1 Bool.false 1 576 0 1 Bool.false 9623 24000 0 1 Bool.false 240430653154 120215326577 240029218368 0 1 Bool.false 1931503472839 1931503472839 10001217432000 0 1

noncomputable abbrev qz219 := (@HDiv.hDiv Complex Complex Complex qz363 qz471 (@HSub.hSub Complex Complex Complex qz355 qz426 (1 : Complex)))

noncomputable def ep1040 := @Enclosure.Complex.IsNear.addLitP qz219 qz88 Bool.true 48000000 53339826304 0 1 Bool.true 11085696000 53339826304 0 1

noncomputable def ep1041 := @Enclosure.Complex.IsNear.of_eq qz219 (Complex.mk (Enclosure.sfrac Bool.true 48000000 53339826304) (Enclosure.sfrac Bool.true 11085696000 53339826304)) Bool.true 48000000 53339826304 0 1 Bool.true 11085696000 53339826304 0 1

noncomputable def ep1042 := @ep1040 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 53243826304 415967393 833434786 0 1 Bool.true 11085696000 86607000 416717393 0 1 (ep1041 (BSN.N_div_s_sub_one_mk qz148 115476 1000 24 qz149 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 48000000 53339826304) (Enclosure.sfrac Bool.true 11085696000 53339826304) Bool.true 48000000 53339826304 0 1 Bool.true 11085696000 53339826304 0 1 (Enclosure.Real.IsNear.const Bool.true 48000000 53339826304) (Enclosure.Real.IsNear.const Bool.true 11085696000 53339826304))) qz89 rfl

noncomputable abbrev qz220 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz392 qz471 1))

noncomputable def ep1043 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz69 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz69 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz112 (@HMul.hMul Nat Nat Nat qz69 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz113 qz205 (@HSub.hSub Nat Nat Nat qz112 (@HMul.hMul Nat Nat Nat qz69 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz69 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz69 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz112 (@HMul.hMul Nat Nat Nat qz69 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz113 qz205 (@HSub.hSub Nat Nat Nat qz112 (@HMul.hMul Nat Nat Nat qz69 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz90)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1))) qz220)) Bool.false 1 576 0 1

noncomputable def ep1044 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz69 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz69 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz112 (@HMul.hMul Nat Nat Nat qz69 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz113 qz205 (@HSub.hSub Nat Nat Nat qz112 (@HMul.hMul Nat Nat Nat qz69 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz90)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1))) qz220) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1045 := @ep1044 0 1 0 1 Bool.false 1 576 0 1 Bool.false 9623 24000 0 1 Bool.false 1 1 576 0 1 Bool.false 9623 9623 24000 0

noncomputable def ep1046 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz69 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz69 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz112 (@HMul.hMul Nat Nat Nat qz69 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz113 qz205 (@HSub.hSub Nat Nat Nat qz112 (@HMul.hMul Nat Nat Nat qz69 2 k) 1)))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1047 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz90)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1))) qz220 Bool.false 1 576 0 1 Bool.false 9623 24000 0 1

noncomputable def ep1048 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz90)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz220)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz90)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz220)) 1 576 0 1 0 1 0

noncomputable def ep1049 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz90)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz220) 1 24 0 1 1 24 0 1 1

noncomputable def ep1050 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz90)) ↑qz141)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz90)) ↑qz141)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep1051 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz90)) ↑qz141)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep1052 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1)) qz145 Bool.false 1 2 0 1 Bool.false 115476 1000 0 1 (BSN.ascPochhammer_one_eval qz145)

noncomputable def ep1053 := ep1052 (@Enclosure.Complex.IsNear.of_eq qz145 (Complex.mk qz83 qz148) Bool.false 1 2 0 1 Bool.false 115476 1000 0 1 (BSN.s_crit_mk qz148 Bool.false 115476 1000 qz149) (@Enclosure.Complex.IsNear.mk qz83 qz148 Bool.false 1 2 0 1 Bool.false 115476 1000 0 1 qz372 qz150))

noncomputable def ep1054 := @ep1051 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz90)) ↑qz141) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep538) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 115476 1000 0 1 ep1053)

noncomputable def ep1055 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz90)) ↑qz141)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 115476 1000 0 1 0 1 0

noncomputable def ep1056 := @ep1055 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz90)) ↑qz141) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep538) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 115476 1000 0 1 ep1053)

noncomputable def ep1057 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz90)) ↑qz141)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz90)) ↑qz141)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1)))) 9623 1000 0 1 0 1 0 1 9623

noncomputable def ep1058 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz90)) ↑qz141)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 115476 1000 0 1 9623 1000 0

noncomputable def ep1059 := @ep1058 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz90)) ↑qz141) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep538) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 115476 1000 0 1 ep1053)

noncomputable def ep1060 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz90)) ↑qz141)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep1061 := @ep1060 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz90)) ↑qz141) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep538) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 115476 1000 0 1 ep1053)

noncomputable def ep1062 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz90)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 9623 1000 0 1 (@ep1050 1 24 0 1 (ep1054 rfl) (ep1056 rfl) rfl rfl) (@ep1057 9623 1000 0 1 (ep1059 rfl) (ep1061 rfl) rfl rfl)

noncomputable def ep1063 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz90)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 9623 1000 0 1 ep1062

noncomputable abbrev qz221 := (@Enclosure.Complex.IsNear.of_eq (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz392 qz471 1)) (Complex.mk (Enclosure.sfrac Bool.false 1 24) qz284) Bool.false 1 24 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 24 1 24 EMRow36.d13 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 24) qz284 Bool.false 1 24 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 24) qz295))

noncomputable def ep1064 := @ep1049 576 0 1 ep1063 (@Enclosure.Complex.IsNear.re_isNear qz220 Bool.false 1 24 0 1 Bool.false 0 1 0 1 qz221)

noncomputable def ep1065 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz90)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz220) 9623 1000 0 1 0 1 0 1 0

noncomputable def ep1066 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz90)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 9623 1000 0 1 ep1062

noncomputable def ep1067 := @ep1065 1 0 1 ep1066 (@Enclosure.Complex.IsNear.im_isNear qz220 Bool.false 1 24 0 1 Bool.false 0 1 0 1 qz221)

noncomputable def ep1068 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz90)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz220)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz90)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz220)) 0 1 0 1 9623 24000 0

noncomputable def ep1069 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz90)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz220) 1 24 0 1 0 1 0 1 0

noncomputable def ep1070 := @ep1069 1 0 1 ep1063 (@Enclosure.Complex.IsNear.im_isNear qz220 Bool.false 1 24 0 1 Bool.false 0 1 0 1 qz221)

noncomputable def ep1071 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz90)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz220) 9623 1000 0 1 1 24 0 1 9623

noncomputable def ep1072 := @ep1071 24000 0 1 ep1066 (@Enclosure.Complex.IsNear.re_isNear qz220 Bool.false 1 24 0 1 Bool.false 0 1 0 1 qz221)

noncomputable def ep1073 := @ep1045 1 (@ep1046 0 1 0 1 (BSN.bern_sum_base qz145 24) qz104) (ep1047 (@ep1048 1 1 1 576 0 1 (ep1064 rfl) (ep1067 rfl) rfl rfl) (@ep1068 1 9623 9623 24000 0 1 (ep1070 rfl) (ep1072 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep1074 := ep1039 (ep1042 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep1043 Bool.false 9623 24000 0 1 (BSN.bern_sum_succ qz145 24 0 1 1 rfl rfl) (ep1073 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep1075 := @Enclosure.Real.IsNear.mulLit_tf qz215 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz204 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz69 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz69 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz112 (@HMul.hMul Nat Nat Nat qz69 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz113 qz205 (@HSub.hSub Nat Nat Nat qz112 (@HMul.hMul Nat Nat Nat qz69 2 k) 1)))))) 61263740853 549755813888 1640966805807 9522320452354048 1931503472839

noncomputable def ep1076 := @ep1075 10001217432000 0 1 39443709405559340063889 ep1018 1056511028076580470658691 ep1019 (@Enclosure.Complex.IsNear.im_isNear qz203 Bool.true 188038612475 1099511627776 3287235067405 19044640904708096 Bool.true 61263740853 549755813888 1640966805807 9522320452354048 (ep1022 ep1035))

noncomputable def ep1077 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz204 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz69 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz69 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz112 (@HMul.hMul Nat Nat Nat qz69 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz113 qz205 (@HSub.hSub Nat Nat Nat qz112 (@HMul.hMul Nat Nat Nat qz69 2 k) 1))))) Bool.false 120215326577 240029218368 0 1 Bool.false

noncomputable def ep1078 := nat_lit 1269861189746180350342559

noncomputable def ep1079 := @Enclosure.Real.IsNear.addLit_tt (@HMul.hMul Real Real Real qz0 qz214 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz204 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz69 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz69 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz112 (@HMul.hMul Nat Nat Nat qz69 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz113 qz205 (@HSub.hSub Nat Nat Nat qz112 (@HMul.hMul Nat Nat Nat qz69 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz215 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz204 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz69 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz69 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz112 (@HMul.hMul Nat Nat Nat qz69 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz113 qz205 (@HSub.hSub Nat Nat Nat qz112 (@HMul.hMul Nat Nat Nat qz69 2 k) 1))))))) 14527889320931576362661 439858194336001063649280 ep1078

noncomputable def ep1080 := nat_lit 761878378409387442346917888

noncomputable def ep1081 := nat_lit 572949871477742265314096538260266718546886656

noncomputable def ep1082 := @Enclosure.Real.IsNear.mulLit_tf qz214 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz204 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz69 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz69 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz112 (@HMul.hMul Nat Nat Nat qz69 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz113 qz205 (@HSub.hSub Nat Nat Nat qz112 (@HMul.hMul Nat Nat Nat qz69 2 k) 1)))))) 188038612475 1099511627776 3287235067405 19044640904708096 1931503472839

noncomputable def ep1083 := @ep1082 10001217432000 0 1 14527889320931576362661 439858194336001063649280 ep1078 ep914 (@Enclosure.Complex.IsNear.re_isNear qz203 Bool.true 188038612475 1099511627776 3287235067405 19044640904708096 Bool.true 61263740853 549755813888 1640966805807 9522320452354048 (ep1022 ep1035))

noncomputable def ep1084 := @Enclosure.Real.IsNear.mulLit_tf qz215 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz204 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz69 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz69 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz112 (@HMul.hMul Nat Nat Nat qz69 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz113 qz205 (@HSub.hSub Nat Nat Nat qz112 (@HMul.hMul Nat Nat Nat qz69 2 k) 1)))))) 61263740853 549755813888 1640966805807 9522320452354048 120215326577

noncomputable def ep1085 := @ep1084 240029218368 0 1 818315623774676838909 14661939811200035454976 65756453487368348344213 ep1080 (@Enclosure.Complex.IsNear.im_isNear qz203 Bool.true 188038612475 1099511627776 3287235067405 19044640904708096 Bool.true 61263740853 549755813888 1640966805807 9522320452354048 (ep1022 ep1035))

noncomputable abbrev qz492 := (ep1074 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep1086 := @ep1015 39077358034171881529931 439858194336001063649280 ep919 ep914 (@ep1016 ep1017 39443709405559340063889 ep1018 1056511028076580470658691 ep1019 ep1020 ep917 ep795 ep918 ep797 (ep1036 (@ep1037 1931503472839 10001217432000 0 1 qz492) rfl) (ep1076 (@ep1077 1931503472839 10001217432000 0 1 qz492) rfl) rfl rfl) (@ep1079 ep914 818315623774676838909 14661939811200035454976 65756453487368348344213 ep1080 ep1081 39077358034171881529931 439858194336001063649280 ep919 ep914 (ep1083 (@ep1077 1931503472839 10001217432000 0 1 qz492) rfl) (ep1085 (@ep1037 1931503472839 10001217432000 0 1 qz492) rfl) rfl rfl)

noncomputable def ep1087 := @ep922 ep913 ep914 (@ep923 19044640904708096 (BSN.head_sum_c_eq qz145 24) (ep924 (BSN.head_sum_c_succ qz145 23 24 rfl rfl) (ep1014 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep1086 rfl rfl rfl

noncomputable def ep1088 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz145 1 24) Bool.false ep794 ep795 ep796 ep797 Bool.false 28866593669426799394549 439858194336001063649280 ep913 ep914 (@ep915 ep797 Bool.false 28866593669426799394549 439858194336001063649280 ep913 ep914 (BSN.zetaApproximant_eq_folded' qz145 1 24 rfl) (ep1087 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep1089 := @Enclosure.Real.IsNear.mulLit_ff (Real.sin (@HSub.hSub Real Real Real qz358 (Complex.im (@HSub.hSub Complex Complex Complex qz62 qz173 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz174 (@Nat.cast Complex Complex.instNatCast j))))) qz175)) (Complex.im (zetaApproximant qz145 1 24)) 55 262144 6280027

noncomputable def ep1090 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz358 (Complex.im (@HSub.hSub Complex Complex Complex qz62 qz173 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz174 (@Nat.cast Complex Complex.instNatCast j))))) qz175)) Bool.false 220 1048576 50240216

noncomputable def ep1091 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz358 (Complex.im (@HSub.hSub Complex Complex Complex qz62 qz173 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz174 (@Nat.cast Complex Complex.instNatCast j))))) qz175) qz453 Bool.false 28824183 262144 355

noncomputable def ep1092 := nat_lit 4640499176291679666443864970583904983643075061696619213832543383402782570643456

noncomputable def ep1093 := nat_lit 13888003943180182773598856792082140533895855085487266027850154100327212573065216

noncomputable def ep1094 := BSN.cos_dyadic_bound_f 3372806732 2147483648 3 2 1048576 277407 ep1092 ep155 ep909 ep1093 ep158 ep909 220 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3372806732) qz288 0 2 ep1092 ep155 ep909 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3372806732) qz289 0 2 ep1093 ep158 ep909 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1095 := @ep1091 1048576 Bool.false 220 1048576 1 138568 (@ep800 28824183 262144 355 1048576 ep907 rfl) (Enclosure.sfrac_false_div 28824183 262144) (BSN.sin_reduce1 qz453 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 59335043538710163357696) qz319) 226375608064910080 72057594037927936 Bool.false 220 1048576 17 1000000000000000 277136 138568 (BSN.sin_reduce_arg_pos_rat_q1 28824183 262144 226375608064910080 72057594037927936 17 59335043538710163357696 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 220 1048576 59335043538710163357696 37778931862957161709568 3372806732 2147483648 277407 277136 (ep1094 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1096 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz145 1 24) Bool.false ep794 ep795 ep796 ep797 Bool.false 28866593669426799394549 439858194336001063649280 ep913 ep914 (@ep915 ep797 Bool.false 28866593669426799394549 439858194336001063649280 ep913 ep914 (BSN.zetaApproximant_eq_folded' qz145 1 24 rfl) (ep1087 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow36.d14 : Enclosure.Real.IsNear (hardyZApproximantEM 1 24 qz148) Bool.true ep779 ep780 ep781 ep782 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 24 qz148) ep783 Bool.true ep779 ep780 ep781 ep782 (@Eq.refl Real ep783) (@ep784 Bool.true ep779 ep780 ep781 ep782 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz358 (Complex.im (@HSub.hSub Complex Complex Complex qz62 qz173 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz174 (@Nat.cast Complex Complex.instNatCast j))))) qz175) (zetaApproximant qz145 1 24)) (@ep786 ep780 ep787 ep788 317532530363694793340039 ep789 ep790 ep791 ep792 ep779 ep780 ep781 ep782 (@ep793 18162384896 ep794 ep795 ep796 ep797 ep785 ep780 ep787 ep788 (@ep798 145299079168 1048575 1048576 6280027 18162384896 (ep912 rfl rfl) rfl) ep1088 rfl) (@ep1089 18162384896 28866593669426799394549 439858194336001063649280 ep913 ep914 317532530363694793340039 ep789 ep790 ep791 (@ep1090 145299079168 55 262144 6280027 18162384896 (ep1095 rfl rfl) rfl) ep1096 rfl) rfl rfl))

theorem EMRow36.d15 : @Eq Nat (Nat.mul (BSN.factNat (Nat.succ (Nat.mul 2 1))) (Nat.pow 4 (Nat.mul 2 1))) 96 := @Eq.refl Nat 96

theorem EMRow36.d16 : @Eq Nat (Nat.mul (Nat.mul 2 1) (Nat.pow (Nat.succ (Nat.mul 4 2)) (Nat.mul 2 1))) 162 := @Eq.refl Nat 162

theorem EMRow36.d17 : @Eq Nat (BSN.factNat (Nat.mul 2 2)) 24 := @Eq.refl Nat 24

theorem EMRow36.d18 : @Eq Nat (Nat.pow 23 (Nat.succ (Nat.mul 2 3))) 3404825447 := @Eq.refl Nat 3404825447

noncomputable abbrev qz573 := (@HAdd.hAdd Complex Complex Complex qz578 qz577 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz493 := qz573

noncomputable abbrev qz222 := (@HDiv.hDiv Real Real Real qz271 (@Norm.norm Complex Complex.instNorm qz493) (@HAdd.hAdd Real Real Real qz382 (Complex.re qz273) qz296))

noncomputable abbrev qz223 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)

noncomputable abbrev qz224 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)))

noncomputable abbrev qz494 := (@HPow.hPow Complex Complex Complex qz532 (@Nat.cast Complex Complex.instNatCast 23) (@HSub.hSub Complex Complex Complex qz553 qz533 qz534))

noncomputable abbrev qz225 := qz494

noncomputable def ep1097 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 23))) (@HMul.hMul Real Real Real qz0 qz222 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))) 50729252315 1855425871872 174323857 1855425871872 565943546169960101 504403158265495552 129695283691

noncomputable def ep1098 := nat_lit 1075654292666862908309296381952

noncomputable def ep1099 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 23)) 26561 1769472 1 1769472 1909915 1048576 6491 1048576 50729252315 1855425871872

noncomputable abbrev qz226 := qz272

noncomputable abbrev qz574 := (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid)))

noncomputable abbrev qz495 := (@Inv.inv Real Real.instInv (@HPow.hPow Real Nat Real qz574 qz226 2))

noncomputable def ep1100 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 96 162) qz495 96 162 0 1 26561 1048576 1 1048576 26561 1769472 1 1769472

noncomputable def ep1101 := nat_lit 781950621441006189802102638025

noncomputable def ep1102 := nat_lit 19807040628566084398385987584

noncomputable def ep1103 := nat_lit 26986075409044041160201671

noncomputable def ep1104 := nat_lit 1073741824000000000000000000000000000000

noncomputable abbrev qz496 := (@HPow.hPow Real Nat Real qz574 qz226 1)

noncomputable def ep1105 := @Enclosure.Real.IsNear.mulLit_ff qz496 qz226 884279719003555 140737488355328 1 500000000000000 884279719003555 140737488355328 1 500000000000000 ep1101 ep1102 ep1103 ep1104

noncomputable def ep1106 := ep1105 (@Enclosure.Real.IsNear.of_eq qz496 qz226 Bool.false 884279719003555 140737488355328 1 500000000000000 (BSN.pow_one_r qz226) (@Enclosure.Real.IsNear.of_eq qz226 qz269 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz270)) (@Enclosure.Real.IsNear.of_eq qz226 qz269 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz270) rfl

noncomputable abbrev qz497 := (@HPow.hPow Real Nat Real qz574 qz226 2)

noncomputable def ep1107 := @Enclosure.Real.IsNear.inv_image qz497 ep1101 ep1102 ep1103 ep1104 13280 13281 524288 (@Enclosure.Real.IsNear.of_eq qz497 (@HMul.hMul Real Real Real qz0 qz496 qz226) Bool.false ep1101 ep1102 ep1103 ep1104 (BSN.pow_succ_r qz226 1 2 rfl) ep1106) rfl rfl rfl

noncomputable def ep1108 := ep1100 (Enclosure.Real.IsNear.const Bool.false 96 162) (@Enclosure.Real.IsNear.recentre' qz495 Bool.false 26561 1048576 1 1048576 26561 1048576 1 1048576 (ep1107 rfl rfl rfl) rfl)

noncomputable def ep1109 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 23)) (Real.sqrt (@HAdd.hAdd Real Real Real qz382 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 23)) (Complex.re (zetaApproximant qz5 1 23))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 23)) (Complex.im (zetaApproximant qz5 1 23))))) Bool.false 1909915 1048576 6491 1048576

noncomputable def ep1110 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz382 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 23)) (Complex.re (zetaApproximant qz5 1 23))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 23)) (Complex.im (zetaApproximant qz5 1 23))))) Bool.false 1909915 1048576 6491 1048576

noncomputable def ep1111 := nat_lit 17434984293606461860613947397952525461418037

noncomputable def ep1112 := nat_lit 5255183678211618902664090950511110389760000

noncomputable def ep1113 := nat_lit 20539625023201941141296872972738126283770940605137029064029587

noncomputable def ep1114 := nat_lit 910959224761365096150311767817122690554630721780109751091200000

noncomputable def ep1115 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz382 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 23)) (Complex.re (zetaApproximant qz5 1 23))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 23)) (Complex.im (zetaApproximant qz5 1 23)))) ep1111 ep1112 ep1113 ep1114 951712 958203

noncomputable def ep1116 := nat_lit 5587756764241452106839183655579145181416275177886931481

noncomputable def ep1117 := nat_lit 1686865707740775920625699405997561115860138983424000000

noncomputable def ep1118 := nat_lit 19730106673833453511328908519914452328742724982357797521159031

noncomputable def ep1119 := nat_lit 2178276604078215806312712103489044139735273808196361

noncomputable def ep1120 := nat_lit 421716426935193980156424851499390278965034745856000000

noncomputable def ep1121 := nat_lit 202379587342121907491991113205918488757053905694807885717639

noncomputable def ep1122 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 23)) (Complex.re (zetaApproximant qz5 1 23))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 23)) (Complex.im (zetaApproximant qz5 1 23))) ep1116 ep1117 ep1118 ep1114 ep1119 ep1120 ep1121

noncomputable def ep1123 := nat_lit 227739806190341274037577941954280672638657680445027437772800000

noncomputable def ep1124 := nat_lit 2360123277304259845489517717432645600942230953051830958812494001526399283069543852333776656980036812800000000

noncomputable def ep1125 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz5 1 23)) (Complex.re (zetaApproximant qz5 1 23)) ep264 ep265 ep266 ep267 ep264 ep265 ep266 ep267 ep1116

noncomputable def ep1126 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (zetaApproximant qz5 1 23)) (Complex.im (zetaApproximant qz5 1 23)) ep397 ep398 ep399 ep400 ep397 ep398 ep399 ep400 ep1119

noncomputable def ep1127 := @ep1097 504403158265495552 ep1098 15652830081917096807 13618885273168379904 1283044461403081 13618885273168379904 (@ep1099 174323857 1855425871872 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) qz495) Bool.false 26561 1769472 1 1769472 (BSN.theta_err_eq 1 2 96 162 EMRow36.d15 EMRow36.d16 rfl) (ep1108 rfl)) (ep1109 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz5 1 23)) (@ep1110 1909915 1048576 6491 1048576 (@ep1115 524288 (@ep1122 ep1123 ep1124 ep1111 ep1112 ep1113 ep1114 (@ep1125 ep1117 ep1118 ep1114 ep577 ep577 rfl) (@ep1126 ep1120 ep1121 ep1123 ep583 ep583 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz227 := (@Norm.norm Complex Complex.instNorm qz493)

noncomputable abbrev qz575 := (Enclosure.sfrac Bool.false 2 7)

noncomputable def ep1128 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz222 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz227 qz575) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))) Bool.false 565943546169960101 504403158265495552 129695283691 504403158265495552 (BSN.zrb_shape_eq qz227 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) qz13 3)

noncomputable def ep1129 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz227 qz575) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) 118871863 3670016 1 3670016 4760954627 137438953472 1051 137438953472

noncomputable def ep1130 := @Enclosure.Real.IsNear.mulLit_ff qz227 qz575 118871863 1048576 1 1048576 2 7 0 1 118871863 3670016

noncomputable abbrev qz498 := (Complex.re qz573)

noncomputable abbrev qz499 := (Complex.im qz573)

noncomputable abbrev qz228 := (@HAdd.hAdd Real Real Real qz382 (@HMul.hMul Real Real Real qz268 qz498 qz498) (@HMul.hMul Real Real Real qz268 qz499 qz499))

noncomputable abbrev qz229 := qz493

noncomputable def ep1131 := @Enclosure.Real.IsNear.of_eq qz227 (Real.sqrt qz228) Bool.false 118871863 1048576 1 1048576 (BSN.norm_eq_sqrt_mul_add qz229)

noncomputable def ep1132 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz228) Bool.false 118871863 1048576 1 1048576 118871863

noncomputable def ep1133 := @Enclosure.Real.IsNear.sqrt_image qz228 12851632721 1000000 0 1 59435931 59435932 524288

noncomputable abbrev qz230 := (@HMul.hMul Real Real Real qz268 qz498 qz498)

noncomputable abbrev qz231 := (@HMul.hMul Real Real Real qz268 qz499 qz499)

noncomputable def ep1134 := @Enclosure.Real.IsNear.addLit_ff qz230 qz231 49 4 0 1 12839382721 1000000 0 1

noncomputable abbrev qz232 := qz498

noncomputable def ep1135 := @Enclosure.Real.IsNear.mulLit_ff qz232 qz232 7 2 0 1 7 2 0 1 49 4

noncomputable abbrev qz500 := (Enclosure.sfrac Bool.false 7 2)

noncomputable def ep1136 := @Enclosure.Complex.IsNear.of_eq qz229 (Complex.mk qz500 qz13) Bool.false 7 2 0 1 Bool.false 113311 1000 0 1 (BSN.s_add_nat_mk qz13 Bool.false 113311 1000 3 qz14)

noncomputable abbrev qz501 := (ep1136 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz13 Bool.false 7 2 0 1 Bool.false 113311 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz18))

noncomputable def ep1137 := @ep1135 0 1 (@Enclosure.Complex.IsNear.re_isNear qz229 Bool.false 7 2 0 1 Bool.false 113311 1000 0 1 qz501)

noncomputable def ep1138 := ep1137 (@Enclosure.Complex.IsNear.re_isNear qz229 Bool.false 7 2 0 1 Bool.false 113311 1000 0 1 qz501)

noncomputable abbrev qz233 := qz499

noncomputable def ep1139 := @Enclosure.Real.IsNear.mulLit_ff qz233 qz233 113311 1000 0 1 113311 1000 0 1 12839382721 1000000

noncomputable def ep1140 := @ep1139 0 1 (@Enclosure.Complex.IsNear.im_isNear qz229 Bool.false 7 2 0 1 Bool.false 113311 1000 0 1 qz501)

noncomputable def ep1141 := ep1140 (@Enclosure.Complex.IsNear.im_isNear qz229 Bool.false 7 2 0 1 Bool.false 113311 1000 0 1 qz501)

noncomputable def ep1142 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Real.sqrt (@HAdd.hAdd Real Real Real qz382 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.re (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.im (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))))) Bool.false 4760954627 137438953472

noncomputable def ep1143 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz382 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.re (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.im (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))))) Bool.false 9521909254 274877906944

noncomputable def ep1144 := nat_lit 5682150369110643389622698250030811662740587201183441496772715121

noncomputable def ep1145 := nat_lit 4735265304952125454979938858000756983685221439242240000000000000000

noncomputable def ep1146 := nat_lit 36824276099561670735206139110781884483173465218866378644720237689231529069961423

noncomputable def ep1147 := nat_lit 69533316674395549307118852316543998256270509123667243090327869220454400000000000000000000

noncomputable def ep1148 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz382 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.re (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.im (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)))) ep1144 ep1145 ep1146 ep1147

noncomputable def ep1149 := nat_lit 23273410553647851923474526708811875028626189022617596127759241

noncomputable def ep1150 := nat_lit 189410612198085018199197554320030279347408857569689600000000000000

noncomputable def ep1151 := nat_lit 1263673808219894801063319747657338907023414114847665256286559990718664121763893

noncomputable def ep1152 := nat_lit 23177772224798516435706284105514666085423503041222414363442623073484800000000000000000000

noncomputable def ep1153 := nat_lit 318769694079340443220989692644407174189058279726125099598670881

noncomputable def ep1154 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.re (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.im (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))) ep1149 ep1150 ep1151 ep1152 ep1153

noncomputable def ep1155 := nat_lit 295954081559507840936246178625047311480326339952640000000000000000

noncomputable def ep1156 := nat_lit 2064578417181374145751011241738116735131451429645211429741284857317221044041859

noncomputable def ep1157 := nat_lit 4345832292149721831694928269783999891016906820229202693145491826278400000000000000000000

noncomputable def ep1158 := nat_lit 67266223750926357463628038828759733778870379762043534639474999803694334890354800458022008618040076305817254074777600000000000000

noncomputable def ep1159 := nat_lit 4824252331050672967428572815171

noncomputable def ep1160 := nat_lit 435213295061266502894223360000000

noncomputable def ep1161 := nat_lit 216162625243454356924994708788917859

noncomputable def ep1162 := nat_lit 87897235877659081321594653549527040000000000

noncomputable def ep1163 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.re (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) ep1159 ep1160 ep1161 ep1162 ep1159 ep1160 ep1161

noncomputable def ep1164 := nat_lit 17854122607379519259225104350609

noncomputable def ep1165 := nat_lit 544016618826583128617779200000000

noncomputable def ep1166 := nat_lit 477131964429454918538658346349261797

noncomputable def ep1167 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225) Bool.true ep1159 ep1160 ep1161 ep1162 Bool.true ep1164 ep1165 ep1166

noncomputable def ep1168 := nat_lit 65922926908244310991195990162145280000000000

noncomputable def ep1169 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225 Bool.true ep1159 ep1160 ep1161 ep1162 Bool.true ep1164 ep1165 ep1166 ep1168

noncomputable def ep1170 := nat_lit 239244645727550585012676391

noncomputable def ep1171 := nat_lit 181338872942194376205926400000

noncomputable def ep1172 := nat_lit 6243403940529304244107485916453

noncomputable def ep1173 := nat_lit 21974308969414770330398663387381760000000

noncomputable def ep1174 := nat_lit 4250065181304551563398149476771

noncomputable def ep1175 := nat_lit 63729669827112379982854921707701953

noncomputable abbrev qz234 := (Complex.re qz494)

noncomputable abbrev qz235 := (Complex.im qz494)

noncomputable def ep1176 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz234) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz235) ep1170 ep1171 ep1172 ep1173 ep1174 ep1160 ep1175

noncomputable def ep1177 := nat_lit 29299078625886360440531551183175680000000000

noncomputable def ep1178 := nat_lit 874824480501483026468665291024279417032486935262029414400000

noncomputable def ep1179 := nat_lit 45779810352947438188330548723712

noncomputable def ep1180 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz234 38516898163 480000000 0 1 155285509177743925 9444732965739290427392 162095190378721261831 ep1179 ep1170

noncomputable def ep1181 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) 38516898163 480000000 0 1 0 1 0 1 38516898163

noncomputable def ep1182 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 115550694489 2000000 0 1 38516898163 480000000 0

noncomputable def ep1183 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (Complex.mk (Enclosure.sfrac Bool.true 1 720) qz10) Bool.true 1 720 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 2 1 30 24 Bool.true BSN.bern_real_2 EMRow36.d17 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 1 720) qz10 Bool.true 1 720 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.true 1 720) qz20)

noncomputable abbrev qz502 := (@HAdd.hAdd Complex Complex Complex qz531 qz530 qz535)

noncomputable abbrev qz236 := qz502

noncomputable def ep1184 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz61 (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) qz236) Bool.true 115550694489 2000000 0 1 Bool.true 1454191757249231 1000000000 0 1

noncomputable abbrev qz237 := (Complex.re qz502)

noncomputable abbrev qz238 := (Complex.im qz502)

noncomputable def ep1185 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz237) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz238) 12838632721 400000 0 1 12839382721 500000 0 1

noncomputable def ep1186 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz237 12838632721 1000000 0 1 5 2 0 1 12838632721 400000

noncomputable abbrev qz503 := (@HAdd.hAdd Complex Complex Complex qz531 qz530 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz239 := qz503

noncomputable def ep1187 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz61 (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz239) Bool.true 12838632721 1000000 0 1 Bool.false 113311 500 0 1

noncomputable abbrev qz240 := (Complex.re qz503)

noncomputable abbrev qz241 := (Complex.im qz503)

noncomputable def ep1188 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz240) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz241) 3 4 0 1 12839382721 1000000 0 1

noncomputable def ep1189 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz240 1 2 0 1 3 2 0 1 3 4

noncomputable def ep1190 := @ep1189 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 113311 1000 0 1 ep540)

noncomputable abbrev qz504 := (Enclosure.sfrac Bool.false 3 2)

noncomputable def ep1191 := @Enclosure.Complex.IsNear.of_eq qz239 (Complex.mk qz504 qz13) Bool.false 3 2 0 1 Bool.false 113311 1000 0 1 (BSN.s_add_nat_mk qz13 Bool.false 113311 1000 1 qz14)

noncomputable abbrev qz505 := (ep1191 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz13 Bool.false 3 2 0 1 Bool.false 113311 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz18))

noncomputable def ep1192 := ep1190 (@Enclosure.Complex.IsNear.re_isNear qz239 Bool.false 3 2 0 1 Bool.false 113311 1000 0 1 qz505)

noncomputable def ep1193 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz241 113311 1000 0 1 113311 1000 0 1 12839382721 1000000

noncomputable def ep1194 := @ep1193 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 113311 1000 0 1 ep540)

noncomputable def ep1195 := ep1194 (@Enclosure.Complex.IsNear.im_isNear qz239 Bool.false 3 2 0 1 Bool.false 113311 1000 0 1 qz505)

noncomputable def ep1196 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz239 Bool.true 12838632721 1000000 0 1 Bool.false 113311 500 0 1 (@ep1188 51354530884 12838632721 1000000 0 1 (ep1192 rfl) (ep1195 rfl) rfl rfl)

noncomputable def ep1197 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz241) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz240) 113311 2000 0 1 339933 2000 0 1

noncomputable def ep1198 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz241 1 2 0 1 113311 1000 0 1 113311 2000

noncomputable def ep1199 := @ep1198 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 113311 1000 0 1 ep540)

noncomputable def ep1200 := ep1199 (@Enclosure.Complex.IsNear.im_isNear qz239 Bool.false 3 2 0 1 Bool.false 113311 1000 0 1 qz505)

noncomputable def ep1201 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz240 113311 1000 0 1 3 2 0 1 339933 2000

noncomputable def ep1202 := @ep1201 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 113311 1000 0 1 ep540)

noncomputable def ep1203 := ep1202 (@Enclosure.Complex.IsNear.re_isNear qz239 Bool.false 3 2 0 1 Bool.false 113311 1000 0 1 qz505)

noncomputable abbrev qz242 := (ep1187 (BSN.ascPochhammer_succ_eval_c 1 2 qz273 rfl) (ep1196 (@ep1197 906488000 113311 500 0 1 (ep1200 rfl) (ep1203 rfl) rfl rfl)))

noncomputable def ep1204 := @ep1186 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 12838632721 1000000 0 1 Bool.false 113311 500 0 1 qz242)

noncomputable abbrev qz506 := (Enclosure.sfrac Bool.false 5 2)

noncomputable def ep1205 := @Enclosure.Complex.IsNear.of_eq qz236 (Complex.mk qz506 qz13) Bool.false 5 2 0 1 Bool.false 113311 1000 0 1 (BSN.s_add_nat_mk qz13 Bool.false 113311 1000 2 qz14)

noncomputable abbrev qz507 := (ep1205 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz13 Bool.false 5 2 0 1 Bool.false 113311 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz18))

noncomputable def ep1206 := ep1204 (@Enclosure.Complex.IsNear.re_isNear qz236 Bool.false 5 2 0 1 Bool.false 113311 1000 0 1 qz507)

noncomputable def ep1207 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz238 113311 500 0 1 113311 1000 0 1 12839382721 500000

noncomputable def ep1208 := @ep1207 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 12838632721 1000000 0 1 Bool.false 113311 500 0 1 qz242)

noncomputable def ep1209 := ep1208 (@Enclosure.Complex.IsNear.im_isNear qz236 Bool.false 5 2 0 1 Bool.false 113311 1000 0 1 qz507)

noncomputable def ep1210 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) qz236 Bool.true 115550694489 2000000 0 1 Bool.true 1454191757249231 1000000000 0 1 (@ep1185 11555069448900000 115550694489 2000000 0 1 (ep1206 rfl) (ep1209 rfl) rfl rfl)

noncomputable def ep1211 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz238) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz237) 1454758312249231 1000000000 0 1 113311 200 0 1

noncomputable def ep1212 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz238 12838632721 1000000 0 1 113311 1000 0 1 1454758312249231 1000000000

noncomputable def ep1213 := @ep1212 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 12838632721 1000000 0 1 Bool.false 113311 500 0 1 qz242)

noncomputable def ep1214 := ep1213 (@Enclosure.Complex.IsNear.im_isNear qz236 Bool.false 5 2 0 1 Bool.false 113311 1000 0 1 qz507)

noncomputable def ep1215 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz237 113311 500 0 1 5 2 0 1 113311 200

noncomputable def ep1216 := @ep1215 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 12838632721 1000000 0 1 Bool.false 113311 500 0 1 qz242)

noncomputable def ep1217 := ep1216 (@Enclosure.Complex.IsNear.re_isNear qz236 Bool.false 5 2 0 1 Bool.false 113311 1000 0 1 qz507)

noncomputable abbrev qz243 := (ep1184 (BSN.ascPochhammer_succ_eval_c 2 3 qz273 rfl) (ep1210 (@ep1211 290838351449846200 1454191757249231 1000000000 0 1 (ep1214 rfl) (ep1217 rfl) rfl rfl)))

noncomputable def ep1218 := @ep1182 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1183) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 115550694489 2000000 0 1 Bool.true 1454191757249231 1000000000 0 1 qz243)

noncomputable def ep1219 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 1454191757249231 1000000000 0 1 0 1 0

noncomputable def ep1220 := @ep1219 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1183) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 115550694489 2000000 0 1 Bool.true 1454191757249231 1000000000 0 1 qz243)

noncomputable def ep1221 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) 1454191757249231 720000000000 0 1 0 1 0 1 1454191757249231

noncomputable def ep1222 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 1454191757249231 1000000000 0 1 1454191757249231 720000000000 0

noncomputable def ep1223 := @ep1222 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1183) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 115550694489 2000000 0 1 Bool.true 1454191757249231 1000000000 0 1 qz243)

noncomputable def ep1224 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 115550694489 2000000 0 1 0 1 0

noncomputable def ep1225 := @ep1224 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1183) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 115550694489 2000000 0 1 Bool.true 1454191757249231 1000000000 0 1 qz243)

noncomputable def ep1226 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 38516898163 480000000 0 1 Bool.false 1454191757249231 720000000000 0 1 (@ep1181 38516898163 480000000 0 1 (ep1218 rfl) (ep1220 rfl) rfl rfl) (@ep1221 1454191757249231 720000000000 0 1 (ep1223 rfl) (ep1225 rfl) rfl rfl)

noncomputable def ep1227 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 38516898163 480000000 0 1 Bool.false 1454191757249231 720000000000 0 1 ep1226

noncomputable def ep1228 := nat_lit 366238482823579505506644389789696

noncomputable def ep1229 := @Enclosure.Complex.IsNear.re_isNear qz225 Bool.true 155285509177743925 9444732965739290427392 162095190378721261831 ep1179 Bool.false 365328812389917625 75557863725914323419136 394423242728991016167 ep1228

noncomputable abbrev qz508 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 3404825447)))

noncomputable def ep1230 := @Enclosure.Complex.IsNear.of_eq qz225 (Complex.mk (@HMul.hMul Real Real Real qz0 qz508 qz136) (@HMul.hMul Real Real Real qz0 qz508 qz419)) Bool.true 155285509177743925 9444732965739290427392 162095190378721261831 ep1179 Bool.false 365328812389917625 75557863725914323419136 394423242728991016167

noncomputable abbrev qz509 := (Real.sqrt (@Nat.cast Real Real.instNatCast 3404825447))

noncomputable abbrev qz510 := (@Nat.cast Real Real.instNatCast 3404825447)

noncomputable def ep1231 := @Enclosure.Real.IsNear.inv_image qz509 16039368352118837 274877906944 1 274877906944 2355387 2355388 137438953472 (@Enclosure.Real.IsNear.of_eq qz509 (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz510 qz15)) Bool.false 16039368352118837 274877906944 1 274877906944 (BSN.sqrt_natCast_div_one 3404825447) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz510 qz15)) Bool.false 16039368352118837 274877906944 1 274877906944 16039368352118837 274877906944 1 274877906944 (BSN.sqrt_enclosure 3404825447 1 8019684176059418 8019684176059419 137438953472 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep1232 := nat_lit 1211781490250000000000000000

noncomputable def ep1233 := nat_lit 1211781490250000000000000

noncomputable def ep1234 := nat_lit 15526215331353001189665931264

noncomputable def ep1235 := nat_lit 4951760157141521099596496896

noncomputable def ep1236 := nat_lit 38777007688000000000000000

noncomputable def ep1237 := nat_lit 38173642625234895562091333025

noncomputable def ep1238 := nat_lit 418040252652648286100516895

noncomputable def ep1239 := BSN.log_dyadic_bound 7 39 8 7 ep1237 137438953472 38777007688 ep1238 91651674949449615 49877351261 46 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 7) (BSN.artanhQ 39) 0 7 ep1238 ep1237 91651674949449615 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1240 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz138 113311 1000 0 1 3530252645612791 1125899906842624 31254847125961 ep1233 400016457527030961001 1125899906842624000 3541517982689766871 ep1232 qz18 (BSN.isNear_log_sfrac 23 1 3530252645612791 1125899906842624 31254847125961 ep1233 Bool.false (@Enclosure.Real.IsNear.recentre' qz422 Bool.false ep1234 ep1235 1000155108030752 ep1236 3530252645612791 1125899906842624 31254847125961 ep1233 (BSN.log_rat_reduce_isNear 23 1 4 46 32 49877351261 137438953472 24973259072661432 36028797018963968 38777007688 1000000000000000 rfl rfl rfl rfl (ep1239 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1241 := nat_lit 11330231146421318627151052800

noncomputable def ep1242 := nat_lit 39614081257132168796771975168

noncomputable def ep1243 := nat_lit 113403390555090091013977863844996653977976059381478762265753891196547003653590523567039475911687091505875745030500000000

noncomputable def ep1244 := nat_lit 406704355798688102870807269590474370206928662370602703270828848655152000467652488154169143141621708451154749585707730206720

noncomputable def ep1245 := nat_lit 451722533386888031692663767114952267242309546841148552455049287626006009970505240090211134612865443789062500000000

noncomputable def ep1246 := nat_lit 340209268220203499265870206207455732029393693525342604500156763491065758948751629690638247312792048786739656966500000000

noncomputable def ep1247 := nat_lit 18301696010940964629186327131571346659311789806677121647187298189481840021044361966937611441372976880301963731356847859302400

noncomputable def ep1248 := BSN.cos_dyadic_bound_f 161012268711450 562949953421312 3 2 274877906944 77629751720 ep1243 ep1244 ep1245 ep1246 ep1247 ep1245 263711188376 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 161012268711450) (BSN.cosEvenQ 562949953421312) 0 2 ep1243 ep1244 ep1245 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 161012268711450) (BSN.cosOddQ 562949953421312) 0 2 ep1246 ep1247 ep1245 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz511 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 97660267950935) (@Nat.cast Real Real.instNatCast 274877906944))

noncomputable def ep1249 := @Enclosure.Real.IsNear.cos_image qz139 qz511 Bool.false 97660267950935 274877906944 201 68719476736 Bool.true 263711188376 274877906944 1 38777007688 (@Enclosure.Real.IsNear.recentre' qz139 Bool.false 400016457527030961001 1125899906842624000 3541517982689766871 ep1232 97660267950935 274877906944 201 68719476736 (ep1240 rfl) rfl) (Enclosure.sfrac_false_div 97660267950935 274877906944) (BSN.cos_reduce2 qz511 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1241) (@Nat.cast Real Real.instNatCast ep1242)) 226375608064910080 72057594037927936 Bool.false 263711188376 274877906944 56 1000000000000000 77554015376 38777007688 (BSN.sin_reduce_arg_pos_rat_q2 97660267950935 274877906944 226375608064910080 72057594037927936 56 ep1241 ep1242 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 263711188376 274877906944 ep1241 ep1242 161012268711450 562949953421312 77629751720 77554015376 (ep1248 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1250 := nat_lit 204125741621135454314734800789980285198543113039024299159515040114354505771654966016478984472129074418221309804900000000

noncomputable def ep1251 := nat_lit 3660339202188192925837265426314269331862357961335424329437459637896368004208872393387522288274595376060392746271369571860480

noncomputable def ep1252 := nat_lit 534614306218872134910349356803849227502037379934368754986787796886367549201746863510865765656596297884623010054500000000

noncomputable def ep1253 := nat_lit 67106218706783536973683199482428271084143229291149446039686760028100080077162660545437908618367581894440533681641775484108800

noncomputable def ep1254 := BSN.sin_dyadic_bound_f 161012268711450 562949953421312 3 2 274877906944 77629751720 ep1250 ep1251 ep1245 ep1252 ep1253 ep1245 77551743055 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 161012268711450) (BSN.sinEvenQ 562949953421312) 0 2 ep1250 ep1251 ep1245 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 161012268711450) (BSN.sinOddQ 562949953421312) 0 2 ep1252 ep1253 ep1245 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1255 := @Enclosure.Real.IsNear.sin_image qz139 qz511 Bool.false 97660267950935 274877906944 201 68719476736 Bool.true 77551743055 274877906944 1 38777007688 (@Enclosure.Real.IsNear.recentre' qz139 Bool.false 400016457527030961001 1125899906842624000 3541517982689766871 ep1232 97660267950935 274877906944 201 68719476736 (ep1240 rfl) rfl) (Enclosure.sfrac_false_div 97660267950935 274877906944) (BSN.sin_reduce2 qz511 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1241) (@Nat.cast Real Real.instNatCast ep1242)) 226375608064910080 72057594037927936 Bool.false 77551743055 274877906944 56 1000000000000000 77554015376 38777007688 (BSN.sin_reduce_arg_pos_rat_q2 97660267950935 274877906944 226375608064910080 72057594037927936 56 ep1241 ep1242 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 77551743055 274877906944 ep1241 ep1242 161012268711450 562949953421312 77629751720 77554015376 (ep1254 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1256 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz508 qz136) (@HMul.hMul Real Real Real qz0 qz508 qz419) Bool.true 155285509177743925 9444732965739290427392 162095190378721261831 ep1179 Bool.false 365328812389917625 75557863725914323419136 394423242728991016167 ep1228 (@Enclosure.Real.IsNear.mulLit_ft qz508 qz136 4710775 274877906944 1 274877906944 32963898547 34359738368 982862252753 333091959713401143296 155285509177743925 9444732965739290427392 162095190378721261831 ep1179 (@Enclosure.Real.IsNear.recentre' qz508 Bool.false 4710775 274877906944 1 274877906944 4710775 274877906944 1 274877906944 (ep1231 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' qz136 Bool.true 263711188376 274877906944 7862898022024 2664735677707209146368 32963898547 34359738368 982862252753 333091959713401143296 (ep1249 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz508 qz419 4710775 274877906944 1 274877906944 77551743055 274877906944 982862252753 333091959713401143296 365328812389917625 75557863725914323419136 394423242728991016167 ep1228 (@Enclosure.Real.IsNear.recentre' qz508 Bool.false 4710775 274877906944 1 274877906944 4710775 274877906944 1 274877906944 (ep1231 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg qz137 Bool.true 77551743055 274877906944 982862252753 333091959713401143296 (@Enclosure.Real.IsNear.recentre' qz137 Bool.true 77551743055 274877906944 7862898022024 2664735677707209146368 77551743055 274877906944 982862252753 333091959713401143296 (ep1255 rfl rfl) rfl)) rfl)

noncomputable def ep1257 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz235 1454191757249231 720000000000 0 1 365328812389917625 75557863725914323419136 394423242728991016167 ep1228 ep1174

noncomputable def ep1258 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 38516898163 480000000 0 1 Bool.false 1454191757249231 720000000000 0 1 ep1226

noncomputable def ep1259 := @Enclosure.Complex.IsNear.im_isNear qz225 Bool.true 155285509177743925 9444732965739290427392 162095190378721261831 ep1179 Bool.false 365328812389917625 75557863725914323419136 394423242728991016167 ep1228

noncomputable def ep1260 := nat_lit 112570661302657518480670583

noncomputable def ep1261 := nat_lit 290142196707511001929482240000

noncomputable def ep1262 := nat_lit 5063986624437592392482075200407

noncomputable def ep1263 := nat_lit 58598157251772720881063102366351360000000

noncomputable def ep1264 := nat_lit 9032596298661001053188180846867

noncomputable def ep1265 := nat_lit 272008309413291564308889600000000

noncomputable def ep1266 := nat_lit 235717489738481313548558005874401961

noncomputable def ep1267 := @Enclosure.Real.IsNear.addLit_ft_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz235) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz234) ep1260 ep1261 ep1262 ep1263 ep1264 ep1265 ep1266

noncomputable def ep1268 := nat_lit 32961463454122155495597995081072640000000000

noncomputable def ep1269 := nat_lit 2590117176795163848907384283474868675990259602823399342080000

noncomputable def ep1270 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz235 38516898163 480000000 0 1 365328812389917625 75557863725914323419136 394423242728991016167 ep1228 ep1260

noncomputable def ep1271 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz234 1454191757249231 720000000000 0 1 155285509177743925 9444732965739290427392 162095190378721261831 ep1179 ep1264

noncomputable abbrev qz512 := (@ep1230 ep1228 (BSN.cpow_neg_s_sub_mk qz13 113311 1000 23 3 3404825447 qz14 rfl EMRow36.d18) ep1256)

noncomputable def ep1272 := ep1169 (@ep1176 ep1177 ep1178 ep1159 ep1160 ep1161 ep1162 (@ep1180 ep1171 ep1172 ep1173 ep1227 (ep1229 qz512) rfl) (@ep1257 ep1160 ep1175 ep1177 ep1258 (ep1259 qz512) rfl) rfl rfl) (@ep1267 ep1268 ep1269 ep1164 ep1165 ep1166 ep1168 (@ep1270 ep1261 ep1262 ep1263 ep1227 (ep1259 qz512) rfl) (@ep1271 ep1265 ep1266 ep1268 ep1258 (ep1229 qz512) rfl) rfl rfl)

noncomputable def ep1273 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.im (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) ep1164 ep1165 ep1166 ep1168 ep1164 ep1165 ep1166

noncomputable def ep1274 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225) Bool.true ep1159 ep1160 ep1161 ep1162 Bool.true ep1164 ep1165 ep1166

noncomputable def ep1275 := @ep1129 565943546169960101 504403158265495552 129695283691 504403158265495552 (@ep1130 1 3670016 (ep1131 (@ep1132 1048576 1 1048576 (ep1133 (@ep1134 51406530884 12851632721 1000000 0 1 (ep1138 rfl) (ep1141 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep1142 1051 137438953472 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (@ep1143 2102 274877906944 4760954627 137438953472 1051 137438953472 (@ep1148 4760953576 4760955678 137438953472 (@ep1154 ep1155 ep1156 ep1157 ep1158 ep1144 ep1145 ep1146 ep1147 (@ep1163 ep1162 ep1149 ep1150 ep1151 ep1152 (@ep1167 ep1168 ep1272) (@ep1167 ep1168 ep1272) rfl) (@ep1273 ep1168 ep1153 ep1155 ep1156 ep1157 (@ep1274 ep1168 ep1272) (@ep1274 ep1168 ep1272) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow36.d19 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz382 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 23))) (@HMul.hMul Real Real Real qz0 qz222 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)))) Bool.false 15652830081917096807 13618885273168379904 1283044461403081 13618885273168379904 := ep1127 (ep1128 ep1275) rfl rfl

theorem EMRow36.d20 : @Eq Nat (Nat.pow 24 (Nat.succ (Nat.mul 2 3))) 4586471424 := @Eq.refl Nat 4586471424

noncomputable abbrev qz576 := (@HAdd.hAdd Complex Complex Complex qz578 qz584 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz513 := qz576

noncomputable abbrev qz244 := (@HDiv.hDiv Real Real Real qz271 (@Norm.norm Complex Complex.instNorm qz513) (@HAdd.hAdd Real Real Real qz382 (Complex.re qz426) qz296))

noncomputable abbrev qz514 := (@HPow.hPow Complex Complex Complex qz532 (@Nat.cast Complex Complex.instNatCast 24) (@HSub.hSub Complex Complex Complex qz553 qz568 qz534))

noncomputable abbrev qz245 := qz514

noncomputable def ep1276 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz145 1 24))) (@HMul.hMul Real Real Real qz0 qz244 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))) 21329093903 927712935936 91459129 927712935936 262976381793602325 252201579132747776 10018701789

noncomputable def ep1277 := nat_lit 249345822399376533124104060928

noncomputable def ep1278 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz145 1 24)) 26561 1769472 1 1769472 803023 524288 3413 524288 21329093903 927712935936

noncomputable def ep1279 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz145 1 24)) (Real.sqrt (@HAdd.hAdd Real Real Real qz382 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz145 1 24)) (Complex.re (zetaApproximant qz145 1 24))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz145 1 24)) (Complex.im (zetaApproximant qz145 1 24))))) Bool.false 803023 524288 3413 524288

noncomputable def ep1280 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz382 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz145 1 24)) (Complex.re (zetaApproximant qz145 1 24))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz145 1 24)) (Complex.im (zetaApproximant qz145 1 24))))) Bool.false 1606046 1048576 6826 1048576

noncomputable def ep1281 := nat_lit 3063374890419918341882119448815989907667389

noncomputable def ep1282 := nat_lit 1305798837961469417023015536040083456000000

noncomputable def ep1283 := nat_lit 3254957870990372554427033148718512995275416987811513321543

noncomputable def ep1284 := nat_lit 163253999105920621480858510941169409707052909910294528000000

noncomputable def ep1285 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz382 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz145 1 24)) (Complex.re (zetaApproximant qz145 1 24))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz145 1 24)) (Complex.im (zetaApproximant qz145 1 24)))) ep1281 ep1282 ep1283 ep1284 799610 806436

noncomputable def ep1286 := nat_lit 2548435994940721766942335421952458911739468722513129

noncomputable def ep1287 := nat_lit 1088298175075465939822121710354242242573500416000000

noncomputable def ep1288 := nat_lit 6230647183178854516581340513629916690616947600878643317611

noncomputable def ep1289 := nat_lit 326507998211841242961717021882338819414105819820589056000000

noncomputable def ep1290 := nat_lit 833280230075791370962424550743749392970913401

noncomputable def ep1291 := nat_lit 193475231124527278190599415174087509790844518400

noncomputable def ep1292 := nat_lit 413731198225023099663297457492013777679831666287975297

noncomputable def ep1293 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz145 1 24)) (Complex.re (zetaApproximant qz145 1 24))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz145 1 24)) (Complex.im (zetaApproximant qz145 1 24))) ep1286 ep1287 ep1288 ep1289 ep1290 ep1291 ep1292

noncomputable def ep1294 := nat_lit 483715552906431471054395587973835288020897510845317120000

noncomputable def ep1295 := nat_lit 493966100480938721395213790715790956851441655530250339164293757466654184355872746886793216498073600

noncomputable def ep1296 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz145 1 24)) (Complex.re (zetaApproximant qz145 1 24)) ep794 ep795 ep796 ep797 ep794 ep795 ep796 ep797 ep1286

noncomputable def ep1297 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (zetaApproximant qz145 1 24)) (Complex.im (zetaApproximant qz145 1 24)) 28866593669426799394549 439858194336001063649280 ep913 ep914 28866593669426799394549 439858194336001063649280 ep913 ep914 ep1290

noncomputable def ep1298 := @ep1276 36028797018963968 ep1277 7256918540206287671 6809442636584189952 96172352598607 972777519512027136 (@ep1278 91459129 927712935936 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) qz495) Bool.false 26561 1769472 1 1769472 (BSN.theta_err_eq 1 2 96 162 EMRow36.d15 EMRow36.d16 rfl) (ep1108 rfl)) (ep1279 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz145 1 24)) (@ep1280 803023 524288 3413 524288 (@ep1285 524288 (@ep1293 ep1294 ep1295 ep1281 ep1282 ep1283 ep1284 (@ep1296 ep1287 ep1288 ep1289 ep1088 ep1088 rfl) (@ep1297 ep1291 ep1292 ep1294 ep1096 ep1096 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz246 := (@Norm.norm Complex Complex.instNorm qz513)

noncomputable def ep1299 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz244 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz246 qz575) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))) Bool.false 262976381793602325 252201579132747776 10018701789 36028797018963968 (BSN.zrb_shape_eq qz246 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) qz148 3)

noncomputable def ep1300 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz246 qz575) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) 121140967 3670016 1 3670016 2170829475 68719476736 561 68719476736

noncomputable def ep1301 := @Enclosure.Real.IsNear.mulLit_ff qz246 qz575 121140967 1048576 1 1048576 2 7 0 1 121140967 3670016

noncomputable abbrev qz515 := (Complex.re qz576)

noncomputable abbrev qz516 := (Complex.im qz576)

noncomputable abbrev qz247 := (@HAdd.hAdd Real Real Real qz382 (@HMul.hMul Real Real Real qz268 qz515 qz515) (@HMul.hMul Real Real Real qz268 qz516 qz516))

noncomputable abbrev qz248 := qz513

noncomputable def ep1302 := @Enclosure.Real.IsNear.of_eq qz246 (Real.sqrt qz247) Bool.false 121140967 1048576 1 1048576 (BSN.norm_eq_sqrt_mul_add qz248)

noncomputable def ep1303 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz247) Bool.false 121140967 1048576 1 1048576 121140967

noncomputable def ep1304 := @Enclosure.Real.IsNear.sqrt_image qz247 417092393 31250 0 1 60570483 60570484 524288

noncomputable abbrev qz249 := (@HMul.hMul Real Real Real qz268 qz515 qz515)

noncomputable abbrev qz250 := (@HMul.hMul Real Real Real qz268 qz516 qz516)

noncomputable def ep1305 := @Enclosure.Real.IsNear.addLit_ff qz249 qz250 49 4 0 1 833419161 62500 0 1

noncomputable abbrev qz251 := qz515

noncomputable def ep1306 := @Enclosure.Real.IsNear.mulLit_ff qz251 qz251 7 2 0 1 7 2 0 1 49 4

noncomputable def ep1307 := @Enclosure.Complex.IsNear.of_eq qz248 (Complex.mk qz500 qz148) Bool.false 7 2 0 1 Bool.false 115476 1000 0 1 (BSN.s_add_nat_mk qz148 Bool.false 115476 1000 3 qz149)

noncomputable abbrev qz517 := (ep1307 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz148 Bool.false 7 2 0 1 Bool.false 115476 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz150))

noncomputable def ep1308 := @ep1306 0 1 (@Enclosure.Complex.IsNear.re_isNear qz248 Bool.false 7 2 0 1 Bool.false 115476 1000 0 1 qz517)

noncomputable def ep1309 := ep1308 (@Enclosure.Complex.IsNear.re_isNear qz248 Bool.false 7 2 0 1 Bool.false 115476 1000 0 1 qz517)

noncomputable abbrev qz252 := qz516

noncomputable def ep1310 := @Enclosure.Real.IsNear.mulLit_ff qz252 qz252 115476 1000 0 1 115476 1000 0 1 833419161 62500

noncomputable def ep1311 := @ep1310 0 1 (@Enclosure.Complex.IsNear.im_isNear qz248 Bool.false 7 2 0 1 Bool.false 115476 1000 0 1 qz517)

noncomputable def ep1312 := ep1311 (@Enclosure.Complex.IsNear.im_isNear qz248 Bool.false 7 2 0 1 Bool.false 115476 1000 0 1 qz517)

noncomputable def ep1313 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Real.sqrt (@HAdd.hAdd Real Real Real qz382 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.re (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.im (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))))) Bool.false 2170829475 68719476736

noncomputable def ep1314 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz382 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.re (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.im (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))))) Bool.false 8683317900 274877906944

noncomputable def ep1315 := nat_lit 200287394371375538312799869382547958013695845402429423958009

noncomputable def ep1316 := nat_lit 200706706786775608273821464453835253553823744000000000000000000

noncomputable def ep1317 := nat_lit 39768843097925713636402458891552665209938302145182600131382537221

noncomputable def ep1318 := nat_lit 77162783434115261465978169331135249323985146364506931200000000000000000000

noncomputable def ep1319 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz382 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.re (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.im (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)))) ep1315 ep1316 ep1317 ep1318

noncomputable def ep1320 := nat_lit 20572762689990636258215668685054352226394636303060659005289

noncomputable def ep1321 := nat_lit 78401057338584221981961509552279395919462400000000000000000000

noncomputable def ep1322 := nat_lit 1466266321288950460709399652009662081211141583588529626703560593793

noncomputable def ep1323 := nat_lit 9876836279566753467645205674385311913470098734656887193600000000000000000000

noncomputable def ep1324 := nat_lit 3690528047124987737294193938720220407853139411664853422611729

noncomputable def ep1325 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.re (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.im (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))) ep1320 ep1321 ep1322 ep1323 ep1324

noncomputable def ep1326 := nat_lit 5017667669669390206845536611345881338845593600000000000000000000

noncomputable def ep1327 := nat_lit 724829119049108176950023017221815813132192218198968638022680834099

noncomputable def ep1328 := nat_lit 1975367255913350693529041134877062382694019746931377438720000000000000000000

noncomputable def ep1329 := nat_lit 392568587257646108592349746208933163657195395120013496144399267116698254875888473826385997690086359040000000000000000000000

noncomputable def ep1330 := nat_lit 143432083893355730112806101267

noncomputable def ep1331 := nat_lit 8854437155380584775680000000000

noncomputable def ep1332 := nat_lit 455395281544744386036114201097

noncomputable def ep1333 := nat_lit 99382273467488926566910525440000000000

noncomputable def ep1334 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.re (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) ep1330 ep1331 ep1332 ep1333 ep1330 ep1331 ep1332

noncomputable def ep1335 := nat_lit 1921074711489635880708454821527

noncomputable def ep1336 := nat_lit 70835497243044678205440000000000

noncomputable def ep1337 := nat_lit 134463170335451519348526359861

noncomputable def ep1338 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz245) Bool.false ep1330 ep1331 ep1332 ep1333 Bool.true ep1335 ep1336 ep1337

noncomputable def ep1339 := nat_lit 19876454693497785313382105088000000000

noncomputable def ep1340 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz245 Bool.false ep1330 ep1331 ep1332 ep1333 Bool.true ep1335 ep1336 ep1337 ep1339

noncomputable def ep1341 := nat_lit 389534181486183917978796473

noncomputable def ep1342 := nat_lit 377789318629571617095680000000

noncomputable def ep1343 := nat_lit 81781692649347090302028817

noncomputable def ep1344 := nat_lit 318023275095964565014113681408000000

noncomputable def ep1345 := nat_lit 2440988660351010651046946297647

noncomputable def ep1346 := nat_lit 141670994486089356410880000000000

noncomputable def ep1347 := nat_lit 859677005183646840633460391569

noncomputable abbrev qz253 := (Complex.re qz514)

noncomputable abbrev qz254 := (Complex.im qz514)

noncomputable def ep1348 := @Enclosure.Real.IsNear.subLit_tt_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3)))) qz254) ep1341 ep1342 ep1343 ep1344 ep1345 ep1346 ep1347

noncomputable def ep1349 := nat_lit 198764546934977853133821050880000000000

noncomputable def ep1350 := nat_lit 866993747899046640173636550626401147925187624131624960000000

noncomputable def ep1351 := nat_lit 106007758365321521671371227136

noncomputable def ep1352 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253 1250089679 15000000 0 1 934814968949561061 75557863725914323419136 327103303159689115 ep1351 ep1341

noncomputable def ep1353 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3)))) 1250089679 15000000 0 1 0 1 0 1 1250089679

noncomputable def ep1354 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 3750269037 62500 0 1 1250089679 15000000 0

noncomputable abbrev qz518 := (@HAdd.hAdd Complex Complex Complex qz531 qz567 qz535)

noncomputable abbrev qz255 := qz518

noncomputable def ep1355 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz61 (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 2)) qz255) Bool.true 3750269037 62500 0 1 Bool.true 12024801481017 7812500 0 1

noncomputable abbrev qz256 := (Complex.re qz518)

noncomputable abbrev qz257 := (Complex.im qz518)

noncomputable def ep1356 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 2))) qz256) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 2))) qz257) 416686143 12500 0 1 833419161 31250 0 1

noncomputable def ep1357 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 2))) qz256 416686143 31250 0 1 5 2 0 1 416686143 12500

noncomputable abbrev qz519 := (@HAdd.hAdd Complex Complex Complex qz531 qz567 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz258 := qz519

noncomputable def ep1358 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz61 (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1)) qz258) Bool.true 416686143 31250 0 1 Bool.false 28869 125 0 1

noncomputable abbrev qz259 := (Complex.re qz519)

noncomputable abbrev qz260 := (Complex.im qz519)

noncomputable def ep1359 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1))) qz259) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1))) qz260) 3 4 0 1 833419161 62500 0 1

noncomputable def ep1360 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1))) qz259 1 2 0 1 3 2 0 1 3 4

noncomputable def ep1361 := @ep1360 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 115476 1000 0 1 ep1053)

noncomputable def ep1362 := @Enclosure.Complex.IsNear.of_eq qz258 (Complex.mk qz504 qz148) Bool.false 3 2 0 1 Bool.false 115476 1000 0 1 (BSN.s_add_nat_mk qz148 Bool.false 115476 1000 1 qz149)

noncomputable abbrev qz520 := (ep1362 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz148 Bool.false 3 2 0 1 Bool.false 115476 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz150))

noncomputable def ep1363 := ep1361 (@Enclosure.Complex.IsNear.re_isNear qz258 Bool.false 3 2 0 1 Bool.false 115476 1000 0 1 qz520)

noncomputable def ep1364 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1))) qz260 115476 1000 0 1 115476 1000 0 1 833419161 62500

noncomputable def ep1365 := @ep1364 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 115476 1000 0 1 ep1053)

noncomputable def ep1366 := ep1365 (@Enclosure.Complex.IsNear.im_isNear qz258 Bool.false 3 2 0 1 Bool.false 115476 1000 0 1 qz520)

noncomputable def ep1367 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1)) qz258 Bool.true 416686143 31250 0 1 Bool.false 28869 125 0 1 (@ep1359 3333489144 416686143 31250 0 1 (ep1363 rfl) (ep1366 rfl) rfl rfl)

noncomputable def ep1368 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1))) qz260) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1))) qz259) 28869 500 0 1 86607 500 0 1

noncomputable def ep1369 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1))) qz260 1 2 0 1 115476 1000 0 1 28869 500

noncomputable def ep1370 := @ep1369 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 115476 1000 0 1 ep1053)

noncomputable def ep1371 := ep1370 (@Enclosure.Complex.IsNear.im_isNear qz258 Bool.false 3 2 0 1 Bool.false 115476 1000 0 1 qz520)

noncomputable def ep1372 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1))) qz259 115476 1000 0 1 3 2 0 1 86607 500

noncomputable def ep1373 := @ep1372 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 115476 1000 0 1 ep1053)

noncomputable def ep1374 := ep1373 (@Enclosure.Complex.IsNear.re_isNear qz258 Bool.false 3 2 0 1 Bool.false 115476 1000 0 1 qz520)

noncomputable abbrev qz261 := (ep1358 (BSN.ascPochhammer_succ_eval_c 1 2 qz426 rfl) (ep1367 (@ep1368 57738000 28869 125 0 1 (ep1371 rfl) (ep1374 rfl) rfl rfl)))

noncomputable def ep1375 := @ep1357 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 416686143 31250 0 1 Bool.false 28869 125 0 1 qz261)

noncomputable def ep1376 := @Enclosure.Complex.IsNear.of_eq qz255 (Complex.mk qz506 qz148) Bool.false 5 2 0 1 Bool.false 115476 1000 0 1 (BSN.s_add_nat_mk qz148 Bool.false 115476 1000 2 qz149)

noncomputable abbrev qz521 := (ep1376 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz148 Bool.false 5 2 0 1 Bool.false 115476 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz150))

noncomputable def ep1377 := ep1375 (@Enclosure.Complex.IsNear.re_isNear qz255 Bool.false 5 2 0 1 Bool.false 115476 1000 0 1 qz521)

noncomputable def ep1378 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 2))) qz257 28869 125 0 1 115476 1000 0 1 833419161 31250

noncomputable def ep1379 := @ep1378 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 416686143 31250 0 1 Bool.false 28869 125 0 1 qz261)

noncomputable def ep1380 := ep1379 (@Enclosure.Complex.IsNear.im_isNear qz255 Bool.false 5 2 0 1 Bool.false 115476 1000 0 1 qz521)

noncomputable def ep1381 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 2)) qz255 Bool.true 3750269037 62500 0 1 Bool.true 12024801481017 7812500 0 1 (@ep1356 23439181481250 3750269037 62500 0 1 (ep1377 rfl) (ep1380 rfl) rfl rfl)

noncomputable def ep1382 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 2))) qz257) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 2))) qz256) 12029312262267 7812500 0 1 28869 50 0 1

noncomputable def ep1383 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 2))) qz257 416686143 31250 0 1 115476 1000 0 1 12029312262267 7812500

noncomputable def ep1384 := @ep1383 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 416686143 31250 0 1 Bool.false 28869 125 0 1 qz261)

noncomputable def ep1385 := ep1384 (@Enclosure.Complex.IsNear.im_isNear qz255 Bool.false 5 2 0 1 Bool.false 115476 1000 0 1 qz521)

noncomputable def ep1386 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 2))) qz256 28869 125 0 1 5 2 0 1 28869 50

noncomputable def ep1387 := @ep1386 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 416686143 31250 0 1 Bool.false 28869 125 0 1 qz261)

noncomputable def ep1388 := ep1387 (@Enclosure.Complex.IsNear.re_isNear qz255 Bool.false 5 2 0 1 Bool.false 115476 1000 0 1 qz521)

noncomputable abbrev qz262 := (ep1355 (BSN.ascPochhammer_succ_eval_c 2 3 qz426 rfl) (ep1381 (@ep1382 601240074050850 12024801481017 7812500 0 1 (ep1385 rfl) (ep1388 rfl) rfl rfl)))

noncomputable def ep1389 := @ep1354 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1183) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 3750269037 62500 0 1 Bool.true 12024801481017 7812500 0 1 qz262)

noncomputable def ep1390 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 12024801481017 7812500 0 1 0 1 0

noncomputable def ep1391 := @ep1390 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1183) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 3750269037 62500 0 1 Bool.true 12024801481017 7812500 0 1 qz262)

noncomputable def ep1392 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3)))) 4008267160339 1875000000 0 1 0 1 0 1 4008267160339

noncomputable def ep1393 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 12024801481017 7812500 0 1 4008267160339 1875000000 0

noncomputable def ep1394 := @ep1393 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1183) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 3750269037 62500 0 1 Bool.true 12024801481017 7812500 0 1 qz262)

noncomputable def ep1395 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 3750269037 62500 0 1 0 1 0

noncomputable def ep1396 := @ep1395 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1183) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 3750269037 62500 0 1 Bool.true 12024801481017 7812500 0 1 qz262)

noncomputable def ep1397 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 1250089679 15000000 0 1 Bool.false 4008267160339 1875000000 0 1 (@ep1353 1250089679 15000000 0 1 (ep1389 rfl) (ep1391 rfl) rfl rfl) (@ep1392 4008267160339 1875000000 0 1 (ep1394 rfl) (ep1396 rfl) rfl rfl)

noncomputable def ep1398 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 1250089679 15000000 0 1 Bool.false 4008267160339 1875000000 0 1 ep1397

noncomputable def ep1399 := @Enclosure.Complex.IsNear.re_isNear qz245 Bool.true 934814968949561061 75557863725914323419136 327103303159689115 ep1351 Bool.true 608988513665981173 75557863725914323419136 214475974478442571 ep1351

noncomputable abbrev qz522 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 4586471424)))

noncomputable def ep1400 := @Enclosure.Complex.IsNear.of_eq qz245 (Complex.mk (@HMul.hMul Real Real Real qz0 qz522 qz216) (@HMul.hMul Real Real Real qz0 qz522 qz487)) Bool.true 934814968949561061 75557863725914323419136 327103303159689115 ep1351 Bool.true 608988513665981173 75557863725914323419136 214475974478442571

noncomputable abbrev qz523 := (Real.sqrt (@Nat.cast Real Real.instNatCast 4586471424))

noncomputable abbrev qz524 := (@Nat.cast Real Real.instNatCast 4586471424)

noncomputable def ep1401 := @Enclosure.Real.IsNear.inv_image qz523 18615691844177917 274877906944 1 274877906944 2029413 2029414 137438953472 (@Enclosure.Real.IsNear.of_eq qz523 (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz524 qz15)) Bool.false 18615691844177917 274877906944 1 274877906944 (BSN.sqrt_natCast_div_one 4586471424) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz524 qz15)) Bool.false 18615691844177917 274877906944 1 274877906944 18615691844177917 274877906944 1 274877906944 (BSN.sqrt_enclosure 4586471424 1 9307845922088958 9307845922088959 137438953472 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep1402 := nat_lit 15736960334339222256381591552

noncomputable def ep1403 := nat_lit 45973536768000000000000000

noncomputable def ep1404 := nat_lit 54412538019840000000000000000

noncomputable def ep1405 := nat_lit 743426006773320438031319040

noncomputable def ep1406 := BSN.log_dyadic_bound 8 40 8 7 ep1404 137438953472 45973536768 ep1405 594330015278039040 55726700127 48 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 8) (BSN.artanhQ 40) 0 7 ep1405 ep1404 594330015278039040 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1407 := @Enclosure.Real.IsNear.mulLit_ff qz148 qz490 115476 1000 0 1 3578170511523063 1125899906842624 30523190129 1403001000000000000000 103298204497159305747 281474976710656000 293724658611367 116916750000000000000000 qz150 (BSN.isNear_log_sfrac 24 1 3578170511523063 1125899906842624 30523190129 1403001000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz489) Bool.false ep1402 ep1235 1000183894147072 ep1403 3578170511523063 1125899906842624 30523190129 1403001000000000000000 (BSN.log_rat_reduce_isNear 24 1 4 48 32 55726700127 137438953472 24973259072661432 36028797018963968 45973536768 1000000000000000 rfl rfl rfl rfl (ep1406 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1408 := nat_lit 39352627107768698558107090944

noncomputable def ep1409 := nat_lit 51212141532959616176419733979111293923945231804588577784902548764655340930020615635610574790681694633476156982765298455336850793780126485756556904363931572505761969262583444015053861841

noncomputable def ep1410 := nat_lit 6308378847008246063796460162423931949098252867933419242910272974037146636290687601591899635669002301462775740831203986644333398331477415382602044345464892932073894033779958631686261964800

noncomputable def ep1411 := nat_lit 935679592969318072487872981708380218537234051986805272688106858472932698211603137401030145989131821359617066765652280125258451909219630606427234710147165315350399028530202866641

noncomputable def ep1412 := nat_lit 256009743372379379948975915855196364047599415843944369983351961688385157175791497340785786234458483911689531175350493220011362644305158874536708099640814806214232283251159795431757902801

noncomputable def ep1413 := nat_lit 220793259645288612232876105684837618218438850377669673501859554091300132270174066055716487248415080551197150929092139532551668941601709538391071552091271252622586291182298552109019168768000

noncomputable def ep1414 := BSN.sin_dyadic_bound_f 559234466490021 562949953421312 4 3 274877906944 92036865601 ep1409 ep1410 ep1411 ep1412 ep1413 ep1411 230316534543 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 559234466490021) (BSN.sinEvenQ 562949953421312) 0 3 ep1409 ep1410 ep1411 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 559234466490021) (BSN.sinOddQ 562949953421312) 0 3 ep1412 ep1413 ep1411 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz525 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 100877152829257) (@Nat.cast Real Real.instNatCast 274877906944))

noncomputable def ep1415 := @Enclosure.Real.IsNear.cos_image qz218 qz525 Bool.false 100877152829257 274877906944 691 274877906944 Bool.true 230316534543 274877906944 1 45973536768 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 103298204497159305747 281474976710656000 293724658611367 116916750000000000000000 100877152829257 274877906944 691 274877906944 (ep1407 rfl) rfl) (Enclosure.sfrac_false_div 100877152829257 274877906944) (BSN.cos_reduce1 qz525 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1408) (@Nat.cast Real Real.instNatCast ep1242)) 226375608064910080 72057594037927936 Bool.false 230316534543 274877906944 58 1000000000000000 91947073536 45973536768 (BSN.sin_reduce_arg_pos_rat_q1 100877152829257 274877906944 226375608064910080 72057594037927936 58 ep1408 ep1242 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 230316534543 274877906944 ep1408 ep1242 559234466490021 562949953421312 92036865601 91947073536 (ep1414 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1416 := nat_lit 19702051084377372208378486228643825466626169878349461646103651316707906018947405527618666888118962963570173534131862229419662319569307063915218494422515823479522212269219047298129261521

noncomputable def ep1417 := nat_lit 485259911308326620292035397109533226853711759071801480223867151849011279714668277045530741205307869343290441602400306664948722948575185798661695718881914840928761079521535279360481689600

noncomputable def ep1418 := nat_lit 119479607575109743835690632693535515062845045904924816313607323782603369516495797003715395487307821421873994444607664772787218142341385624522256055619987684627437683389290425797804618705

noncomputable def ep1419 := nat_lit 44158651929057722446575221136967523643687770075533934700371910818260026454034813211143297449683016110239430185818427906510333788320341907678214310418254250524517258236459710421803833753600

noncomputable def ep1420 := BSN.cos_dyadic_bound_f 559234466490021 562949953421312 4 3 274877906944 92036865601 ep1416 ep1417 ep1411 ep1418 ep1419 ep1411 150040519999 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 559234466490021) (BSN.cosEvenQ 562949953421312) 0 3 ep1416 ep1417 ep1411 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 559234466490021) (BSN.cosOddQ 562949953421312) 0 3 ep1418 ep1419 ep1411 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1421 := @Enclosure.Real.IsNear.sin_image qz218 qz525 Bool.false 100877152829257 274877906944 691 274877906944 Bool.false 150040519999 274877906944 1 45973536768 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 103298204497159305747 281474976710656000 293724658611367 116916750000000000000000 100877152829257 274877906944 691 274877906944 (ep1407 rfl) rfl) (Enclosure.sfrac_false_div 100877152829257 274877906944) (BSN.sin_reduce1 qz525 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1408) (@Nat.cast Real Real.instNatCast ep1242)) 226375608064910080 72057594037927936 Bool.false 150040519999 274877906944 58 1000000000000000 91947073536 45973536768 (BSN.sin_reduce_arg_pos_rat_q1 100877152829257 274877906944 226375608064910080 72057594037927936 58 ep1408 ep1242 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 150040519999 274877906944 ep1408 ep1242 559234466490021 562949953421312 92036865601 91947073536 (ep1420 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1422 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz522 qz216) (@HMul.hMul Real Real Real qz0 qz522 qz487) Bool.true 934814968949561061 75557863725914323419136 327103303159689115 ep1351 Bool.true 608988513665981173 75557863725914323419136 214475974478442571 ep1351 (@Enclosure.Real.IsNear.mulLit_ft qz522 qz216 4058827 274877906944 1 274877906944 230316534543 274877906944 977862299 385653978320338944 934814968949561061 75557863725914323419136 327103303159689115 ep1351 (@Enclosure.Real.IsNear.recentre' qz522 Bool.false 4058827 274877906944 1 274877906944 4058827 274877906944 1 274877906944 (ep1401 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' qz216 Bool.true 230316534543 274877906944 32042591813632 12637109561600866516992 230316534543 274877906944 977862299 385653978320338944 (ep1415 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz522 qz487 4058827 274877906944 1 274877906944 150040519999 274877906944 977862299 385653978320338944 608988513665981173 75557863725914323419136 214475974478442571 ep1351 (@Enclosure.Real.IsNear.recentre' qz522 Bool.false 4058827 274877906944 1 274877906944 4058827 274877906944 1 274877906944 (ep1401 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg qz217 Bool.false 150040519999 274877906944 977862299 385653978320338944 (@Enclosure.Real.IsNear.recentre' qz217 Bool.false 150040519999 274877906944 32042591813632 12637109561600866516992 150040519999 274877906944 977862299 385653978320338944 (ep1421 rfl rfl) rfl)) rfl)

noncomputable def ep1423 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3)))) qz254 4008267160339 1875000000 0 1 608988513665981173 75557863725914323419136 214475974478442571 ep1351 ep1345

noncomputable def ep1424 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 1250089679 15000000 0 1 Bool.false 4008267160339 1875000000 0 1 ep1397

noncomputable def ep1425 := @Enclosure.Complex.IsNear.im_isNear qz245 Bool.true 934814968949561061 75557863725914323419136 327103303159689115 ep1351 Bool.true 608988513665981173 75557863725914323419136 214475974478442571 ep1351

noncomputable def ep1426 := nat_lit 761290255563393517775613467

noncomputable def ep1427 := nat_lit 1133367955888714851287040000000

noncomputable def ep1428 := nat_lit 268114202088968466001324709

noncomputable def ep1429 := nat_lit 1590116375479822825070568407040000000

noncomputable def ep1430 := nat_lit 1248996047011282523898319319893

noncomputable def ep1431 := nat_lit 47223664828696452136960000000000

noncomputable def ep1432 := nat_lit 262223485618678827047019601997

noncomputable def ep1433 := @Enclosure.Real.IsNear.addLit_tt (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3)))) qz254) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253) ep1426 ep1427 ep1428 ep1429 ep1430 ep1431 ep1432

noncomputable def ep1434 := nat_lit 39752909386995570626764210176000000000

noncomputable def ep1435 := nat_lit 1451523012580340832230646944825332834424769512965406720000000

noncomputable def ep1436 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3)))) qz254 1250089679 15000000 0 1 608988513665981173 75557863725914323419136 214475974478442571 ep1351 ep1426

noncomputable def ep1437 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253 4008267160339 1875000000 0 1 934814968949561061 75557863725914323419136 327103303159689115 ep1351 ep1430

noncomputable abbrev qz526 := (@ep1400 ep1351 (BSN.cpow_neg_s_sub_mk qz148 115476 1000 24 3 4586471424 qz149 rfl EMRow36.d20) ep1422)

noncomputable def ep1438 := ep1340 (@ep1348 ep1349 ep1350 ep1330 ep1331 ep1332 ep1333 (@ep1352 ep1342 ep1343 ep1344 ep1398 (ep1399 qz526) rfl) (@ep1423 ep1346 ep1347 ep1349 ep1424 (ep1425 qz526) rfl) rfl rfl) (@ep1433 ep1434 ep1435 ep1335 ep1336 ep1337 ep1339 (@ep1436 ep1427 ep1428 ep1429 ep1398 (ep1425 qz526) rfl) (@ep1437 ep1431 ep1432 ep1434 ep1424 (ep1399 qz526) rfl) rfl rfl)

noncomputable def ep1439 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.im (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) ep1335 ep1336 ep1337 ep1339 ep1335 ep1336 ep1337

noncomputable def ep1440 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz245) Bool.false ep1330 ep1331 ep1332 ep1333 Bool.true ep1335 ep1336 ep1337

noncomputable def ep1441 := @ep1300 262976381793602325 252201579132747776 10018701789 36028797018963968 (@ep1301 1 3670016 (ep1302 (@ep1303 1048576 1 1048576 (ep1304 (@ep1305 3336739144 417092393 31250 0 1 (ep1309 rfl) (ep1312 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep1313 561 68719476736 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (@ep1314 2244 274877906944 2170829475 68719476736 561 68719476736 (@ep1319 4341657828 4341660072 137438953472 (@ep1325 ep1326 ep1327 ep1328 ep1329 ep1315 ep1316 ep1317 ep1318 (@ep1334 ep1333 ep1320 ep1321 ep1322 ep1323 (@ep1338 ep1339 ep1438) (@ep1338 ep1339 ep1438) rfl) (@ep1439 ep1339 ep1324 ep1326 ep1327 ep1328 (@ep1440 ep1339 ep1438) (@ep1440 ep1339 ep1438) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow36.d21 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz382 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz145 1 24))) (@HMul.hMul Real Real Real qz0 qz244 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)))) Bool.false 7256918540206287671 6809442636584189952 96172352598607 972777519512027136 := ep1298 (ep1299 ep1441) rfl rfl

noncomputable def EMRow36.d22 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J))

noncomputable abbrev qz527 := (EMRow36.d3 qz537 qz569 (@Enclosure.dec_le_dec qz537 qz569 113311 1000 115476 1000 (@Eq.refl Real qz537) (@Eq.refl Real qz569) rfl rfl rfl) 23 24 1 1)

noncomputable abbrev qz263 := qz527

noncomputable def ep1442 := @Zeta.Certificates.ZIntervalEM.Certificate.mk qz263 (@Enclosure.dec_nonneg qz13 113311 1000 qz14) (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 23 rfl)

noncomputable abbrev qz264 := (Zeta.Certificates.ZIntervalEM.fstVal qz527)

noncomputable def ep1443 := @Enclosure.Real.IsNear.pos_val qz264 ep247 ep248

noncomputable def ep1444 := @Enclosure.Real.IsNear.of_eq qz264 (hardyZApproximantEM 1 23 qz13) Bool.false

noncomputable abbrev qz265 := (Zeta.Certificates.ZIntervalEM.sndVal qz527)

noncomputable def ep1445 := BSN.mul_neg_of_pos_neg_r qz264 qz265 (@ep1443 ep249 ep250 (@ep1444 ep247 ep248 ep249 ep250 (@Eq.refl Real (hardyZApproximantEM 1 23 qz13)) EMRow36.d10) rfl rfl rfl)

noncomputable def ep1446 := @Enclosure.Real.IsNear.neg_val qz265 ep779 ep780

noncomputable def ep1447 := @Enclosure.Real.IsNear.of_eq qz265 (hardyZApproximantEM 1 24 qz148) Bool.true

noncomputable def ep1448 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz264) (BSN.hardyZErrorBoundStrong 1 23 qz13)

noncomputable def ep1449 := @Enclosure.norm_gt_of_isNear qz264 (BSN.hardyZErrorBoundStrong 1 23 qz13) Bool.false

noncomputable def ep1450 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 23 qz13) (@HAdd.hAdd Real Real Real qz382 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 23))) (@HMul.hMul Real Real Real qz0 qz222 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)))) Bool.false 15652830081917096807 13618885273168379904 1283044461403081 13618885273168379904 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz382 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 23))) (@HMul.hMul Real Real Real qz0 qz222 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)))))

noncomputable def ep1451 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz265) (BSN.hardyZErrorBoundStrong 1 24 qz148)

noncomputable def ep1452 := @Enclosure.norm_gt_of_isNear qz265 (BSN.hardyZErrorBoundStrong 1 24 qz148) Bool.true

noncomputable def ep1453 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 24 qz148) (@HAdd.hAdd Real Real Real qz382 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz145 1 24))) (@HMul.hMul Real Real Real qz0 qz244 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)))) Bool.false 7256918540206287671 6809442636584189952 96172352598607 972777519512027136 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz382 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz145 1 24))) (@HMul.hMul Real Real Real qz0 qz244 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz61 (@HMul.hMul Complex Complex Complex qz61 (@HDiv.hDiv Complex Complex Complex qz68 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)))))

noncomputable def ep1454 := @List.cons EMRow36.d0 (@PSigma.mk Zeta.Certificates.ZIntervalEM Zeta.Certificates.ZIntervalEM.Certificate qz263 (ep1442 (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 24 rfl) (ep1445 (@ep1446 ep781 ep782 (@ep1447 ep779 ep780 ep781 ep782 (@Eq.refl Real (hardyZApproximantEM 1 24 qz148)) EMRow36.d14) rfl rfl rfl)) (ep1448 (hardyZErrorBoundEM 1 23 qz13) (BSN.hardyZErrorBoundEM_le_strong 1 23 qz13 rfl) (@ep1449 Bool.false ep247 ep248 ep249 ep250 15652830081917096807 13618885273168379904 1283044461403081 13618885273168379904 (@ep1444 ep247 ep248 ep249 ep250 (@Eq.refl Real (hardyZApproximantEM 1 23 qz13)) EMRow36.d10) (ep1450 EMRow36.d19) rfl rfl rfl rfl rfl)) (ep1451 (hardyZErrorBoundEM 1 24 qz148) (BSN.hardyZErrorBoundEM_le_strong 1 24 qz148 rfl) (@ep1452 Bool.false ep779 ep780 ep781 ep782 7256918540206287671 6809442636584189952 96172352598607 972777519512027136 (@ep1447 ep779 ep780 ep781 ep782 (@Eq.refl Real (hardyZApproximantEM 1 24 qz148)) EMRow36.d14) (ep1453 EMRow36.d21) rfl rfl rfl rfl rfl)))) (@List.nil EMRow36.d0)

noncomputable abbrev qz528 := (@Enclosure.dec_le_dec qz537 qz569 113311 1000 115476 1000 (@Eq.refl Real qz537) (@Eq.refl Real qz569) rfl rfl rfl)

noncomputable abbrev qz266 := (Zeta.Certificates.CertifiedZeroIntervals.intervals (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1454 (@List.IsChain.singleton EMRow36.d1 EMRow36.d22 (EMRow36.d2 qz285 qz433 qz528))))

noncomputable abbrev qz529 := (@NonemptyInterval Real Real.instLE)

noncomputable def ep1455 := And (@Eq (Option Real) (@Option.map qz529 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz529 qz266)) (@Option.some Real qz13))

noncomputable def ep1456 := ep1455 (@Eq (Option Real) (@Option.map qz529 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz529 qz266)) (@Option.some Real qz148))

noncomputable def ep1457 := @And.intro (@Eq Nat (@List.length qz529 qz266) 1) ep1456

noncomputable def ep1458 := @And.intro (@Eq (Option Real) (@Option.map qz529 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz529 qz266)) (@Option.some Real qz13))

noncomputable def ep1459 := @ep1458 (@Eq (Option Real) (@Option.map qz529 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz529 qz266)) (@Option.some Real qz148))

noncomputable abbrev qz267 := (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1454 (@List.IsChain.singleton EMRow36.d1 EMRow36.d22 (EMRow36.d2 qz285 qz433 qz528)))

theorem EMRow36.d23 : Zeta.Certificates.BatchSpec 1 113311 1000 115476 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz529 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 1) (And (@Eq (Option Real) (@Option.map qz529 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz529 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz13)) (@Eq (Option Real) (@Option.map qz529 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz529 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz148)))) qz267 (ep1457 (@Eq.refl Nat 1) (ep1459 (@Eq.refl (Option Real) (@Option.some Real qz13)) (@Eq.refl (Option Real) (@Option.some Real qz148))))

theorem solution : Zeta.Certificates.BatchSpec 1 113311 1000 115476 1000 := EMRow36.d23
#print axioms solution
#check solution
