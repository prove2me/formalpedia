-- Prove2me | solution 1 for RHHeight1000.em_main_0038_0038
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T09:42:04.042865+00:00
-- url     : https://prove2.me/submissions/126c1065-656c-4394-b5e0-7e618f2cde0e

import Definitions.Def_RHT1000_Support_20261118_S005
/- Copyright (c) 2026 Salvatore Mercuri, Bhavik Mehta.
Apache 2.0 license; see the source project LICENSE. -/
set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def EMRow38.d0 := @PSigma Zeta.Certificates.ZIntervalEM fun (I : Zeta.Certificates.ZIntervalEM) => Zeta.Certificates.ZIntervalEM.Certificate I

noncomputable def EMRow38.d1 := @NonemptyInterval Real Real.instLE

noncomputable def EMRow38.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h

noncomputable def EMRow38.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) (fc sc fb sb : Nat) => Zeta.Certificates.ZIntervalEM.mk (EMRow38.d2 a b h) fc sc fb sb

noncomputable def ep0 := nat_lit 26986075409044028275299783

noncomputable def ep1 := nat_lit 4294967296000000000000000

noncomputable def ep2 := nat_lit 26986075409044045455168967

noncomputable abbrev qz267 := (@instHMul Real Real.instMul)

noncomputable abbrev qz0 := qz267

noncomputable abbrev qz268 := (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 2 1) Real.pi)

noncomputable def ep3 := @BSN.isNear_log_image_fff qz268 884279719003555 140737488355328 1 500000000000000 ep0 ep1 ep2 ep1 4138529546116343 2251799813685248 125000000070159 35079500000000000000 4138529546116343 2251799813685248 125000000070159 35079500000000000000 963576 524288

noncomputable abbrev qz269 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 2 1) Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) BSN.pi_near_15 rfl)

noncomputable def ep4 := @ep3 3 524288 qz269 rfl rfl rfl rfl

noncomputable def ep5 := nat_lit 53972150818088056550599566

noncomputable def ep6 := nat_lit 34359738368000000000000000

noncomputable def ep7 := nat_lit 9806206225044028275299783

noncomputable def ep8 := nat_lit 44165944593044028275299783

noncomputable def ep9 := nat_lit 13681445815609410487519367394620474863599256634174726093703677122907123617368241606644861540940610176751640793056574796245399519365549113997355475306157239709119582688278313060810592403844863400465080549957745

noncomputable def ep10 := nat_lit 231714499556395493334623298703961145503103241611736774613091488581016477543539392410113701224645713379230392133956226737605624599560350113120270717249177907454870984269546186598262646369758174842349131395304

noncomputable def ep11 := nat_lit 8978369550011295664474073352761810093897501552430546263638635096022803738134167562509900960712119243631997923545019968443113540909076206607473711060286601587364321108377403290080403445693385008949995305

noncomputable def ep12 := BSN.log_dyadic_bound ep7 ep8 5 4 ep9 1048576 280636 ep10 ep11 473518 ep5 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep7) (BSN.artanhQ ep8) 0 4 ep10 ep9 ep11 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz270 := (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))

noncomputable abbrev qz1 := qz270

noncomputable def ep13 := ep4 rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep1 4138529546116343 2251799813685248 125000000070159 35079500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep0) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 69433004117575847641088 37778931862957161709568 1000000000561272 280636000000000000000 4138529546116343 2251799813685248 125000000070159 35079500000000000000 (BSN.log_rat_reduce_isNear ep0 ep1 2 ep5 ep6 473518 1048576 24973259072661432 36028797018963968 280636 1000000000000000 rfl rfl rfl rfl (ep12 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep14 := nat_lit 53972150818088090910337934

noncomputable def ep15 := nat_lit 9806206225044045455168967

noncomputable def ep16 := nat_lit 44165944593044045455168967

noncomputable def ep17 := nat_lit 13681445815609453062485491347592146866046743284321690683909457683007658987562290830600045658905080811372395010565947827677605470036294121079488508864180301737865471494204890974265645509835068840465080549957745

noncomputable def ep18 := nat_lit 231714499556396865510889920206523150079811393376960301632499817942333196803513131357563499488546302200815366867712007119763002650772307103678175657719139104636874731038771518520299266622696414842349131395304

noncomputable def ep19 := nat_lit 8978369550011421500876706511871067098718760264493934208903156435737864998391937547068187824077011975074541700434630537294838404525415248443919841847024664017658842168336182958576672102333385008949995305

noncomputable def ep20 := BSN.log_dyadic_bound ep15 ep16 5 4 ep17 1048576 280636 ep18 ep19 473518 ep14 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep15) (BSN.artanhQ ep16) 0 4 ep18 ep17 ep19 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep21 := ep13 (BSN.isNear_log_sfrac ep2 ep1 4138529546116343 2251799813685248 125000000070159 35079500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep2) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 69433004117575847641088 37778931862957161709568 1000000000561272 280636000000000000000 4138529546116343 2251799813685248 125000000070159 35079500000000000000 (BSN.log_rat_reduce_isNear ep2 ep1 2 ep14 ep6 473518 1048576 24973259072661432 36028797018963968 280636 1000000000000000 rfl rfl rfl rfl (ep20 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable abbrev qz271 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)

noncomputable abbrev qz2 := (Real.log qz271)

theorem EMRow38.d4 : Enclosure.Real.IsNear qz2 Bool.false 120447 65536 3 524288 := @Enclosure.Real.IsNear.of_eq qz2 (Real.log qz268) Bool.false 120447 65536 3 524288 BSN.log_two_pi_eq (@Enclosure.Real.IsNear.recentre' (Real.log qz268) Bool.false 963576 524288 3 524288 120447 65536 3 524288 (ep21 rfl rfl rfl rfl rfl rfl rfl rfl) rfl)

noncomputable def ep22 := nat_lit 8589934592000000000000000

noncomputable def ep23 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 ep0 ep22 ep2 ep22 1200336 1048576 1 280636 1200336 1048576 1 280636 600168 524288 2 524288 BSN.pi_near_15 rfl rfl rfl

noncomputable def ep24 := nat_lit 17179869184000000000000000

noncomputable def ep25 := nat_lit 18396140817044028275299783

noncomputable def ep26 := nat_lit 35576010001044028275299783

noncomputable def ep27 := nat_lit 145019262663961446558303139663424756232419223153299357158415217874016130572233056993847515999529612750616182853355499335896178729185698845314776375864537073527142908641610750276034469165612529925303649396973267518946591078603565291376312767403717761600170009932259137778521478520425507632472584532570900560707662248426541531715360699177249902784721815296292248142738824858695953661559845440650653128788875447728828657762006237171740033404723254477174341920697506370253193455781322964835857351124092897592956162654178130575

noncomputable def ep28 := nat_lit 15500762873619990602332184736899274490522931101512051618692838888825382235673431503644115344741331161500627469184702974962114537943617674254904297224139410345221262767191485292268260077615645253784097850065864022184521411511133693085443040736512010941548648374196772723338837137976260321103066698629790037694560548409922339907589559883712609967105556007429010014773911317423638534096849366294542840133852248768895750397896505791271178551667935288585787166713880920071720072716082683081155281219708172458141800988558163320

noncomputable def ep29 := nat_lit 12900190794487083783367107939442176642390171280542213571554777169279725287102813254708993369099729304728646904879886535518616983985412662170766446331701281703998252143668221340329975389245922410714088123244705567402747658401492589451585970559635763980329972215329212888079422466283203384882259392047898400615815810081169907384366653346471604103896809335921621947903075223769953790093549808584241881353287841076643853121427928248525828402335494512605306631304432120211393210317325496757155861061354331245840675149075

noncomputable def ep30 := BSN.log_dyadic_bound ep25 ep26 11 10 ep27 1048576 280636 ep28 ep29 1200336 ep5 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep25) (BSN.artanhQ ep26) 0 10 ep28 ep27 ep29 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep31 := nat_lit 18396140817044045455168967

noncomputable def ep32 := nat_lit 35576010001044045455168967

noncomputable def ep33 := nat_lit 145019262663962847171784895425483977818796535899227200426399035286881207006285364467913811844950531107314785650583974625982406238691319033447632878979985852280879486690814033867010958364699188952871572448188560932645032521756218245629809291975913196623825614492380080480004685076434733043183791438169545293975334857826316990371107134320667652578346815517853870648072772035977941843998949310557583393428557296298890786965786350523173236912472938174255438182435383147950274229549088258679583524155427309880956162654178130575

noncomputable def ep34 := nat_lit 15500762873620157189619721156942591192100275120160672416764593300158228469749443299607348495591439275767946573253526107895503597951484257520435868240203420954375895980141891044871083424251900562230440202302413072793440172565998181227591194192658878334739610458454844032013325963992941389843551995646587189684848765634635122388286241104146031552341815777883628509454807838726994150833304950745987647656768534710890974432620160470644835720379148964170536679305861738540146791997074363921127776563807649880221800988558163320

noncomputable def ep35 := nat_lit 12900190794487324729109480814509220959173684627296055849229843377126536688487849343376525559792931631054411655715865486295286288812423905434305314401904993536755333953308594664509631000767632482919425633906965368325056855874260596615770736441041599390097968820060635361729170158825410327022636428624381203910573184452046894301676992229743752846881064485858738985580654099214803581683226335297196686880535448467637789069028262446657986458573827723305156755787640135484017403116612632808333639900906331245840675149075

noncomputable def ep36 := BSN.log_dyadic_bound ep31 ep32 11 10 ep33 1048576 280636 ep34 ep35 1200336 ep14 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep31) (BSN.artanhQ ep32) 0 10 ep34 ep33 ep35 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep37 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 600168 524288 2 524288 75021 65536 1 262144 (ep23 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep22 1200336 1048576 1 280636 Bool.false (BSN.logfrac_isNear ep5 ep24 1 ep0 ep22 1200336 1048576 280636 rfl rfl rfl (ep30 rfl))) (BSN.isNear_log_sfrac ep2 ep22 1200336 1048576 1 280636 Bool.false (BSN.logfrac_isNear ep14 ep24 1 ep2 ep22 1200336 1048576 280636 rfl rfl rfl (ep36 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl

theorem EMRow38.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 75021 65536 1 262144 := ep37

noncomputable abbrev qz578 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 117628 1000)))

noncomputable abbrev qz529 := qz578

noncomputable abbrev qz272 := qz529

noncomputable abbrev qz3 := (BSN.headSumC qz272 9)

noncomputable abbrev qz579 := (@instHAdd Complex Complex.instAdd)

noncomputable abbrev qz530 := qz579

noncomputable abbrev qz273 := qz530

noncomputable abbrev qz4 := qz273

noncomputable abbrev qz5 := qz272

noncomputable abbrev qz531 := (@instHPow Complex Complex Complex.instPow)

noncomputable abbrev qz274 := qz531

noncomputable abbrev qz6 := qz274

noncomputable abbrev qz532 := (@Neg.neg Complex Complex.instNeg qz578)

noncomputable abbrev qz275 := qz532

noncomputable abbrev qz7 := qz275

noncomputable abbrev qz276 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 8) qz7)

noncomputable def ep38 := @Enclosure.Complex.IsNear.of_eq qz3 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 8) qz276) Bool.false 1694563523977 1099511627776 220581376071445 77140636293136384 Bool.false 35777219993 137438953472 55079102012371 19285159073284096

noncomputable def ep39 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 8) qz276 Bool.false 335866536975 274877906944 12339490413557 4821289768321024 Bool.false 29836901403 274877906944 12325108941101 4821289768321024 Bool.false

noncomputable abbrev qz277 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 7) qz7)

noncomputable def ep40 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 8) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 7) qz277) Bool.false 335866536975 274877906944 12339490413557 4821289768321024 Bool.false 29836901403 274877906944 12325108941101 4821289768321024

noncomputable def ep41 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 7) qz277 Bool.false 859469452175 549755813888 86344227231365 38570318146568192 Bool.false 297460420187 1099511627776 172493288331459 77140636293136384 Bool.true

noncomputable abbrev qz278 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 6) qz7)

noncomputable def ep42 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 7) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 6) qz278) Bool.false 859469452175 549755813888 86344227231365 38570318146568192 Bool.false 297460420187 1099511627776 172493288331459 77140636293136384

noncomputable def ep43 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 6) qz278 Bool.false 2151035425765 1099511627776 145963574859875 77140636293136384 Bool.false 87944062291 549755813888 72909650682807 38570318146568192 Bool.true

noncomputable def ep44 := nat_lit 1889993312769362467225600

noncomputable abbrev qz279 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 5) qz7)

noncomputable def ep45 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 6) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 5) qz279) Bool.false 2151035425765 1099511627776 145963574859875 77140636293136384 Bool.false 87944062291 549755813888 72909650682807 38570318146568192

noncomputable def ep46 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 5) qz279 Bool.false 907641314973 549755813888 58357644378419 38570318146568192 Bool.false 267564752897 549755813888 58283750534213 38570318146568192 Bool.false

noncomputable abbrev qz280 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 4) qz7)

noncomputable def ep47 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 5) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 4) qz280) Bool.false 907641314973 549755813888 58357644378419 38570318146568192 Bool.false 267564752897 549755813888 58283750534213 38570318146568192

noncomputable def ep48 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 4) qz280 Bool.false 1289420147511 1099511627776 84000541845139 77140636293136384 Bool.false 93705616025 274877906944 20975418007091 19285159073284096 Bool.false

noncomputable def ep49 := nat_lit 1995924359325424702980096

noncomputable abbrev qz533 := (@Nat.cast Complex Complex.instNatCast 3)

noncomputable abbrev qz281 := qz533

noncomputable abbrev qz8 := qz281

noncomputable def ep50 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 4) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz7)) Bool.false 1289420147511 1099511627776 84000541845139 77140636293136384 Bool.false 93705616025 274877906944 20975418007091 19285159073284096

noncomputable def ep51 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz7) Bool.false 1868476832641 1099511627776 46238932716225 77140636293136384 Bool.false 57346354065 549755813888 23088511610961 38570318146568192 Bool.true

noncomputable abbrev qz534 := (@Nat.cast Complex Complex.instNatCast 2)

noncomputable abbrev qz282 := qz534

noncomputable abbrev qz9 := qz282

noncomputable def ep52 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 3) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz7)) Bool.false 1868476832641 1099511627776 46238932716225 77140636293136384 Bool.false 57346354065 549755813888 23088511610961 38570318146568192

noncomputable def ep53 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz7) Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz283 := (Enclosure.sfrac Bool.false 0 1)

noncomputable abbrev qz10 := qz283

noncomputable def ep54 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz10) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz5)

noncomputable abbrev qz535 := (@Nat.cast Real Real.instNatCast 2)

noncomputable abbrev qz11 := (@Inv.inv Real Real.instInv (Real.sqrt qz535))

noncomputable abbrev qz580 := (Enclosure.sfrac Bool.false 117628 1000)

noncomputable abbrev qz536 := qz580

noncomputable abbrev qz284 := qz536

noncomputable abbrev qz285 := (Enclosure.sfrac Bool.false 2 1)

noncomputable abbrev qz12 := (@HMul.hMul Real Real Real qz267 qz284 (Real.log qz285))

noncomputable abbrev qz13 := qz284

noncomputable abbrev qz286 := (@Eq.refl Real qz536)

noncomputable abbrev qz14 := qz286

noncomputable def ep55 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz9 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz11 (Real.cos qz12)) (@HMul.hMul Real Real Real qz0 qz11 (@Neg.neg Real Real.instNeg (Real.sin qz12)))) Bool.false 768965204865 1099511627776 46238932716225 77140636293136384 Bool.false 57346354065 549755813888 23088511610961 38570318146568192 (BSN.cpow_neg_s_mk qz13 117628 1000 2 qz14 rfl)

noncomputable abbrev qz15 := (@Nat.cast Real Real.instNatCast 1)

noncomputable def ep56 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz535) 1482911 1048576 1 1048576 370727 370728 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz535) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz535 qz15)) Bool.false 1482911 1048576 1 1048576 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz535 qz15)) Bool.false 1482911 1048576 1 1048576 1482911 1048576 1 1048576 (BSN.sqrt_enclosure 2 1 741455 741456 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep57 := BSN.log_dyadic_bound 1 3 6 5 613814355 524288 140318 24381081 945 363408 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 1) (BSN.artanhQ 3) 0 5 24381081 613814355 945 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep58 := nat_lit 5611840512509130786006779313723074877066502190125173888789155748986191099709985

noncomputable def ep59 := nat_lit 164135286493895707012911871249815109382010203263545499525931125331216861264609280

noncomputable def ep60 := nat_lit 7593326366135418614004590674756041876214807393779914577198041336155397933601

noncomputable def ep61 := nat_lit 14685383575788266142737938389134638705469824619309335561322801561371963188300321

noncomputable def ep62 := nat_lit 3009146919054754628570050972913277005336853726498334157975403964405642456517836800

noncomputable abbrev qz287 := (BSN.sinEvenQ 2147483648)

noncomputable abbrev qz288 := (BSN.sinOddQ 2147483648)

noncomputable def ep63 := BSN.sin_dyadic_bound_f 3055301043 2147483648 3 2 1048576 280911 ep58 ep59 ep60 ep61 ep62 ep60 1037103 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3055301043) qz287 0 2 ep58 ep59 ep60 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3055301043) qz288 0 2 ep61 ep62 ep60 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz16 := (Real.log qz285)

noncomputable abbrev qz17 := (Enclosure.Real.IsNear.const Bool.false 117628 1000)

noncomputable abbrev qz289 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 10686739) (@Nat.cast Real Real.instNatCast 131072))

noncomputable abbrev qz290 := (BSN.isNear_log_sfrac 2 1 363408 524288 1 140318 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 363408 524288 140318 rfl rfl rfl (ep57 rfl)))

noncomputable abbrev qz291 := (@Nat.cast Real Real.instNatCast 18889465931478580854784)

noncomputable def ep64 := @Enclosure.Real.IsNear.cos_image qz12 qz289 Bool.false 10686739 131072 55 65536 Bool.false 1037103 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz12 Bool.false 667921191 8192000 29407 35079500 10686739 131072 55 65536 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz16 117628 1000 0 1 363408 524288 1 140318 667921191 8192000 29407 35079500 qz17 qz290 rfl) rfl) (Enclosure.sfrac_false_div 10686739 131072) (BSN.cos_reduce3 qz289 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26874712188105311387648) qz291) 226375608064910080 72057594037927936 Bool.false 1037103 1048576 12 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q3 10686739 131072 226375608064910080 72057594037927936 12 26874712188105311387648 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1037103 1048576 26874712188105311387648 18889465931478580854784 3055301043 2147483648 280911 280636 (ep63 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep65 := nat_lit 3121063985334466178276657214590488728093041131133443233583841212252841898920481

noncomputable def ep66 := nat_lit 18237254054877300779212430138868345486890022584838388836214569481246317918289920

noncomputable def ep67 := nat_lit 9348005303271127697601962462421954100526693778612769871597127554086214900894241

noncomputable def ep68 := nat_lit 820676432469478535064559356249075546910051016317727497629655626656084306323046400

noncomputable abbrev qz292 := (BSN.cosEvenQ 2147483648)

noncomputable abbrev qz293 := (BSN.cosOddQ 2147483648)

noncomputable def ep69 := BSN.cos_dyadic_bound_f 3055301043 2147483648 3 2 1048576 280911 ep65 ep66 ep60 ep67 ep68 ep60 154686 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3055301043) qz292 0 2 ep65 ep66 ep60 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3055301043) qz293 0 2 ep67 ep68 ep60 rfl rfl rfl rfl) rfl rfl

noncomputable def ep70 := @Enclosure.Real.IsNear.sin_image qz12 qz289 Bool.false 10686739 131072 55 65536 Bool.true 154686 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz12 Bool.false 667921191 8192000 29407 35079500 10686739 131072 55 65536 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz16 117628 1000 0 1 363408 524288 1 140318 667921191 8192000 29407 35079500 qz17 qz290 rfl) rfl) (Enclosure.sfrac_false_div 10686739 131072) (BSN.sin_reduce3 qz289 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26874712188105311387648) qz291) 226375608064910080 72057594037927936 Bool.false 154686 1048576 12 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q3 10686739 131072 226375608064910080 72057594037927936 12 26874712188105311387648 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 154686 1048576 26874712188105311387648 18889465931478580854784 3055301043 2147483648 280911 280636 (ep69 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz294 := (@Enclosure.Real.IsNear.recentre' qz11 Bool.false 741455 1048576 1 1048576 741455 1048576 1 1048576 (ep56 rfl rfl) rfl)

noncomputable def ep71 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz11 (Real.cos qz12)) (@HMul.hMul Real Real Real qz0 qz11 (@Neg.neg Real Real.instNeg (Real.sin qz12))) Bool.false 768965204865 1099511627776 46238932716225 77140636293136384 Bool.false 57346354065 549755813888 23088511610961 38570318146568192 (@Enclosure.Real.IsNear.mulLit_ff qz11 (Real.cos qz12) 741455 1048576 1 1048576 1037103 1048576 3891513 4597940224 768965204865 1099511627776 46238932716225 77140636293136384 qz294 (@Enclosure.Real.IsNear.recentre' (Real.cos qz12) Bool.false 1037103 1048576 7783026 9195880448 1037103 1048576 3891513 4597940224 (ep64 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz11 (@Neg.neg Real Real.instNeg (Real.sin qz12)) 741455 1048576 1 1048576 77343 524288 3891513 4597940224 57346354065 549755813888 23088511610961 38570318146568192 qz294 (@Enclosure.Real.IsNear.neg (Real.sin qz12) Bool.true 77343 524288 3891513 4597940224 (@Enclosure.Real.IsNear.recentre' (Real.sin qz12) Bool.true 154686 1048576 7783026 9195880448 77343 524288 3891513 4597940224 (ep70 rfl rfl) rfl)) rfl)

noncomputable abbrev qz295 := (Enclosure.Real.IsNear.const Bool.false 0 1)

noncomputable abbrev qz18 := qz295

noncomputable def ep72 := @ep53 768965204865 1099511627776 46238932716225 77140636293136384 Bool.false 57346354065 549755813888 23088511610961 38570318146568192 Bool.false 1868476832641 1868476832641 1099511627776 46238932716225 77140636293136384 Bool.false 57346354065 57346354065 549755813888 23088511610961 38570318146568192 (ep54 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz10 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz18)) (ep55 ep71) rfl rfl

noncomputable abbrev qz296 := (@Nat.cast Real Real.instNatCast 3)

noncomputable abbrev qz19 := (@Inv.inv Real Real.instInv (Real.sqrt qz296))

noncomputable abbrev qz20 := (@HMul.hMul Real Real Real qz267 qz284 (Real.log (Enclosure.sfrac Bool.false 3 1)))

noncomputable def ep73 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz8 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz19 (Real.cos qz20)) (@HMul.hMul Real Real Real qz0 qz19 (@Neg.neg Real Real.instNeg (Real.sin qz20)))) Bool.true 289528342565 549755813888 18880804564457 38570318146568192 Bool.false 130064877985 549755813888 18862324403221 38570318146568192 (BSN.cpow_neg_s_mk qz13 117628 1000 3 qz14 rfl)

noncomputable def ep74 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz296) 1816187 1048576 1 1048576 302697 302698 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz296) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz296 qz15)) Bool.false 1816187 1048576 1 1048576 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz296 qz15)) Bool.false 1816187 1048576 1 1048576 1816187 1048576 1 1048576 (BSN.sqrt_enclosure 3 1 908093 908094 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep75 := BSN.log_dyadic_bound 1 2 10 9 171633298636800 524288 140318 16925142283965 34459425 575989 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP 1) (BSN.artanhQ 2) 0 9 16925142283965 171633298636800 34459425 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep76 := nat_lit 675846673515707463003856959759689281

noncomputable def ep77 := nat_lit 510423550381407695195061911147652317184

noncomputable def ep78 := nat_lit 7656353255721115427925928667214784757760

noncomputable def ep79 := BSN.cos_dyadic_bound_f 906696721 2147483648 2 1 1048576 280911 ep76 ep77 ep76 ep76 ep78 ep76 956494 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 906696721) qz292 0 1 ep76 ep77 ep76 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 906696721) qz293 0 1 ep76 ep78 ep76 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz21 := (Real.log (Enclosure.sfrac Bool.false 3 1))

noncomputable abbrev qz537 := (@Nat.cast Real Real.instNatCast 262144)

noncomputable abbrev qz297 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 33876217) qz537)

noncomputable abbrev qz298 := (BSN.isNear_log_sfrac 3 1 575989 524288 1 140318 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 575989 524288 140318 rfl rfl rfl (ep75 rfl)))

noncomputable abbrev qz299 := (@Nat.cast Real Real.instNatCast 37778931862957161709568)

noncomputable def ep80 := @Enclosure.Real.IsNear.cos_image qz20 qz297 Bool.false 33876217 262144 55 65536 Bool.true 956494 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz20 Bool.false 16938108523 131072000 29407 35079500 33876217 262144 55 65536 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz21 117628 1000 0 1 575989 524288 1 140318 16938108523 131072000 29407 35079500 qz17 qz298 rfl) rfl) (Enclosure.sfrac_false_div 33876217 262144) (BSN.cos_reduce2 qz297 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 15950777406947363651584) qz299) 226375608064910080 72057594037927936 Bool.false 956494 1048576 20 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q2 33876217 262144 226375608064910080 72057594037927936 20 15950777406947363651584 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 956494 1048576 15950777406947363651584 37778931862957161709568 906696721 2147483648 280911 280636 (ep79 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep81 := nat_lit 2552117751907038475975309555738261585920

noncomputable def ep82 := nat_lit 17864824263349269331827166890167831101440

noncomputable def ep83 := BSN.sin_dyadic_bound_f 906696721 2147483648 2 1 1048576 280911 ep76 ep81 ep76 ep76 ep82 ep76 429686 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 906696721) qz287 0 1 ep76 ep81 ep76 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 906696721) qz288 0 1 ep76 ep82 ep76 rfl rfl rfl rfl) rfl rfl

noncomputable def ep84 := @Enclosure.Real.IsNear.sin_image qz20 qz297 Bool.false 33876217 262144 55 65536 Bool.true 429686 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz20 Bool.false 16938108523 131072000 29407 35079500 33876217 262144 55 65536 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz21 117628 1000 0 1 575989 524288 1 140318 16938108523 131072000 29407 35079500 qz17 qz298 rfl) rfl) (Enclosure.sfrac_false_div 33876217 262144) (BSN.sin_reduce2 qz297 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 15950777406947363651584) qz299) 226375608064910080 72057594037927936 Bool.false 429686 1048576 20 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q2 33876217 262144 226375608064910080 72057594037927936 20 15950777406947363651584 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 429686 1048576 15950777406947363651584 37778931862957161709568 906696721 2147483648 280911 280636 (ep83 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz300 := (@Enclosure.Real.IsNear.recentre' qz19 Bool.false 605395 1048576 1 1048576 605395 1048576 1 1048576 (ep74 rfl rfl) rfl)

noncomputable def ep85 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz19 (Real.cos qz20)) (@HMul.hMul Real Real Real qz0 qz19 (@Neg.neg Real Real.instNeg (Real.sin qz20))) Bool.true 289528342565 549755813888 18880804564457 38570318146568192 Bool.false 130064877985 549755813888 18862324403221 38570318146568192 (@Enclosure.Real.IsNear.mulLit_ft qz19 (Real.cos qz20) 605395 1048576 1 1048576 478247 524288 3891513 4597940224 289528342565 549755813888 18880804564457 38570318146568192 qz300 (@Enclosure.Real.IsNear.recentre' (Real.cos qz20) Bool.true 956494 1048576 7783026 9195880448 478247 524288 3891513 4597940224 (ep80 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 (@Neg.neg Real Real.instNeg (Real.sin qz20)) 605395 1048576 1 1048576 214843 524288 3891513 4597940224 130064877985 549755813888 18862324403221 38570318146568192 qz300 (@Enclosure.Real.IsNear.neg (Real.sin qz20) Bool.true 214843 524288 3891513 4597940224 (@Enclosure.Real.IsNear.recentre' (Real.sin qz20) Bool.true 429686 1048576 7783026 9195880448 214843 524288 3891513 4597940224 (ep84 rfl rfl) rfl)) rfl)

noncomputable def ep86 := @ep51 289528342565 549755813888 18880804564457 38570318146568192 Bool.false 130064877985 549755813888 18862324403221 38570318146568192 Bool.false 708866222638494822432768 1289420147511 1099511627776 84000541845139 77140636293136384 Bool.false 103030414407400580710400 93705616025 274877906944 20975418007091 19285159073284096 (ep52 (BSN.head_sum_c_succ qz5 2 3 rfl rfl) (ep72 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep73 ep85) rfl rfl

noncomputable abbrev qz538 := (@Nat.cast Real Real.instNatCast 4)

noncomputable abbrev qz22 := (@Inv.inv Real Real.instInv (Real.sqrt qz538))

noncomputable abbrev qz23 := (@HMul.hMul Real Real Real qz267 qz284 (Real.log (Enclosure.sfrac Bool.false 4 1)))

noncomputable def ep87 := @Enclosure.Complex.IsNear.of_eq qz280 (Complex.mk (@HMul.hMul Real Real Real qz0 qz22 (Real.cos qz23)) (@HMul.hMul Real Real Real qz0 qz22 (@Neg.neg Real Real.instNeg (Real.sin qz23)))) Bool.false 525862482435 1099511627776 32714746911699 77140636293136384 Bool.false 80153520847 549755813888 16332914520031 38570318146568192 (BSN.cpow_neg_s_mk qz13 117628 1000 4 qz14 rfl)

noncomputable def ep88 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz538) 2097153 1048576 1 1048576 262143 262144 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz538) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz538 qz15)) Bool.false 2097153 1048576 1 1048576 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz538 qz15)) Bool.false 2097153 1048576 1 1048576 2097153 1048576 1 1048576 (BSN.sqrt_enclosure 4 1 1048576 1048577 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep89 := nat_lit 318077276165597140789031982421875

noncomputable def ep90 := nat_lit 49379992292270016474244603430625

noncomputable def ep91 := nat_lit 20095619060363156210525625

noncomputable def ep92 := BSN.log_dyadic_bound 3 5 14 13 ep89 524288 140318 ep90 ep91 726817 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base13 (BSN.artanhP 3) (BSN.artanhQ 5) 0 13 ep90 ep89 ep91 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep93 := nat_lit 3616628146058619022994476357313694712486707796861503173855332535927719103365120

noncomputable def ep94 := nat_lit 3156797563425149658432307262779978477792889737672012446890682571560226717696

noncomputable def ep95 := nat_lit 9467010329336551960776642914538985234215427170300086958992809822313881094127616

noncomputable def ep96 := BSN.sin_dyadic_bound_f 2737825988 2147483648 3 2 1048576 280911 ep93 ep59 ep94 ep95 ep62 ep94 1003005 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2737825988) qz287 0 2 ep93 ep59 ep94 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2737825988) qz288 0 2 ep95 ep62 ep94 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz24 := (Real.log (Enclosure.sfrac Bool.false 4 1))

noncomputable abbrev qz301 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 42747015) qz537)

noncomputable abbrev qz302 := (BSN.isNear_log_sfrac 4 1 726817 524288 1 140318 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 726817 524288 140318 rfl rfl rfl (ep92 rfl)))

noncomputable def ep97 := @Enclosure.Real.IsNear.cos_image qz23 qz301 Bool.false 42747015 262144 55 65536 Bool.false 1003005 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz23 Bool.false 21373507519 131072000 29407 35079500 42747015 262144 55 65536 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz24 117628 1000 0 1 726817 524288 1 140318 21373507519 131072000 29407 35079500 qz17 qz302 rfl) rfl) (Enclosure.sfrac_false_div 42747015 262144) (BSN.cos_reduce3 qz301 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 48164344147949933035520) qz299) 226375608064910080 72057594037927936 Bool.false 1003005 1048576 25 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q3 42747015 262144 226375608064910080 72057594037927936 25 48164344147949933035520 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1003005 1048576 48164344147949933035520 37778931862957161709568 2737825988 2147483648 280911 280636 (ep96 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep98 := nat_lit 2010640880060755079289567890624399275149412282584244879896025045547204047077376

noncomputable def ep99 := nat_lit 6025609045055414938551839057347637868492651068277390614794293771498491687796736

noncomputable def ep100 := BSN.cos_dyadic_bound_f 2737825988 2147483648 3 2 1048576 280911 ep98 ep66 ep94 ep99 ep68 ep94 305762 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2737825988) qz292 0 2 ep98 ep66 ep94 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2737825988) qz293 0 2 ep99 ep68 ep94 rfl rfl rfl rfl) rfl rfl

noncomputable def ep101 := @Enclosure.Real.IsNear.sin_image qz23 qz301 Bool.false 42747015 262144 55 65536 Bool.true 305762 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz23 Bool.false 21373507519 131072000 29407 35079500 42747015 262144 55 65536 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz24 117628 1000 0 1 726817 524288 1 140318 21373507519 131072000 29407 35079500 qz17 qz302 rfl) rfl) (Enclosure.sfrac_false_div 42747015 262144) (BSN.sin_reduce3 qz301 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 48164344147949933035520) qz299) 226375608064910080 72057594037927936 Bool.false 305762 1048576 25 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q3 42747015 262144 226375608064910080 72057594037927936 25 48164344147949933035520 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 305762 1048576 48164344147949933035520 37778931862957161709568 2737825988 2147483648 280911 280636 (ep100 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz303 := (@Enclosure.Real.IsNear.recentre' qz22 Bool.false 524287 1048576 1 1048576 524287 1048576 1 1048576 (ep88 rfl rfl) rfl)

noncomputable def ep102 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz22 (Real.cos qz23)) (@HMul.hMul Real Real Real qz0 qz22 (@Neg.neg Real Real.instNeg (Real.sin qz23))) Bool.false 525862482435 1099511627776 32714746911699 77140636293136384 Bool.false 80153520847 549755813888 16332914520031 38570318146568192 (@Enclosure.Real.IsNear.mulLit_ff qz22 (Real.cos qz23) 524287 1048576 1 1048576 1003005 1048576 3891513 4597940224 525862482435 1099511627776 32714746911699 77140636293136384 qz303 (@Enclosure.Real.IsNear.recentre' (Real.cos qz23) Bool.false 1003005 1048576 7783026 9195880448 1003005 1048576 3891513 4597940224 (ep97 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz22 (@Neg.neg Real Real.instNeg (Real.sin qz23)) 524287 1048576 1 1048576 152881 524288 3891513 4597940224 80153520847 549755813888 16332914520031 38570318146568192 qz303 (@Enclosure.Real.IsNear.neg (Real.sin qz23) Bool.true 152881 524288 3891513 4597940224 (@Enclosure.Real.IsNear.recentre' (Real.sin qz23) Bool.true 305762 1048576 7783026 9195880448 152881 524288 3891513 4597940224 (ep101 rfl rfl) rfl)) rfl)

noncomputable def ep103 := @ep48 525862482435 1099511627776 32714746911699 77140636293136384 Bool.false 80153520847 549755813888 16332914520031 38570318146568192 Bool.false ep49 907641314973 549755813888 58357644378419 38570318146568192 Bool.false 73547639248315920416768 267564752897 549755813888 58283750534213 38570318146568192 (ep50 (BSN.head_sum_c_succ qz5 3 4 rfl rfl) (ep86 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep87 ep102) rfl rfl

noncomputable abbrev qz539 := (@Nat.cast Real Real.instNatCast 5)

noncomputable abbrev qz25 := (@Inv.inv Real Real.instInv (Real.sqrt qz539))

noncomputable abbrev qz26 := (@HMul.hMul Real Real Real qz267 qz284 (Real.log (Enclosure.sfrac Bool.false 5 1)))

noncomputable def ep104 := @Enclosure.Complex.IsNear.of_eq qz279 (Complex.mk (@HMul.hMul Real Real Real qz0 qz25 (Real.cos qz26)) (@HMul.hMul Real Real Real qz0 qz25 (@Neg.neg Real Real.instNeg (Real.sin qz26)))) Bool.false 335752795819 1099511627776 29248286103037 77140636293136384 Bool.true 89810345303 274877906944 7312950074297 19285159073284096 (BSN.cpow_neg_s_mk qz13 117628 1000 5 qz14 rfl)

noncomputable def ep105 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz539) 2344687 1048576 1 1048576 234468 234469 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz539) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz539 qz15)) Bool.false 2344687 1048576 1 1048576 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz539 qz15)) Bool.false 2344687 1048576 1 1048576 2344687 1048576 1 1048576 (BSN.sqrt_enclosure 5 1 1172343 1172344 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep106 := nat_lit 11734546589655452485523914939250625

noncomputable def ep107 := nat_lit 2429970938528035899633153341031900

noncomputable def ep108 := nat_lit 824199001261152424427520000

noncomputable def ep109 := BSN.log_dyadic_bound 2 3 17 16 ep106 524288 140318 ep107 ep108 843808 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base16 (BSN.artanhP 2) (BSN.artanhQ 3) 0 16 ep107 ep106 ep108 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep110 := nat_lit 342283555474465007473602640371042073577069883846997855404508898752859478163456

noncomputable def ep111 := nat_lit 91723747248727315263647205404381176335939029494140721149547579350320152576

noncomputable def ep112 := nat_lit 1026667218928897567790280626702317458378537773482005284771227601099877794185216

noncomputable def ep113 := BSN.cos_dyadic_bound_f 1759179776 2147483648 3 2 1048576 280911 ep110 ep66 ep111 ep112 ep68 ep111 715987 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1759179776) qz292 0 2 ep110 ep66 ep111 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1759179776) qz293 0 2 ep112 ep68 ep111 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz27 := (@Nat.cast Real Real.instNatCast 524288)

noncomputable abbrev qz28 := (Real.log (Enclosure.sfrac Bool.false 5 1))

noncomputable abbrev qz29 := (@Nat.cast Real Real.instNatCast 75557863725914323419136)

noncomputable abbrev qz304 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 99255447) qz27)

noncomputable abbrev qz305 := (BSN.isNear_log_sfrac 5 1 843808 524288 1 140318 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 843808 524288 140318 rfl rfl rfl (ep109 rfl)))

noncomputable def ep114 := @Enclosure.Real.IsNear.cos_image qz26 qz304 Bool.false 99255447 524288 55 65536 Bool.false 715987 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz26 Bool.false 775433183 4096000 29407 35079500 99255447 524288 55 65536 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz28 117628 1000 0 1 843808 524288 1 140318 775433183 4096000 29407 35079500 qz17 qz305 rfl) rfl) (Enclosure.sfrac_false_div 99255447 524288) (BSN.cos_reduce0 qz304 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 61895635821875360169984) qz29) 226375608064910080 72057594037927936 Bool.false 715987 1048576 30 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q0 99255447 524288 226375608064910080 72057594037927936 30 61895635821875360169984 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 715987 1048576 61895635821875360169984 75557863725914323419136 1759179776 2147483648 280911 280636 (ep113 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep115 := nat_lit 9577251549830322550294630977268350976

noncomputable def ep116 := BSN.sin_dyadic_bound_f 1759179776 2147483648 2 1 1048576 280911 ep115 ep81 ep115 ep115 ep82 ep115 766076 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1759179776) qz287 0 1 ep115 ep81 ep115 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1759179776) qz288 0 1 ep115 ep82 ep115 rfl rfl rfl rfl) rfl rfl

noncomputable def ep117 := @Enclosure.Real.IsNear.sin_image qz26 qz304 Bool.false 99255447 524288 55 65536 Bool.false 766076 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz26 Bool.false 775433183 4096000 29407 35079500 99255447 524288 55 65536 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz28 117628 1000 0 1 843808 524288 1 140318 775433183 4096000 29407 35079500 qz17 qz305 rfl) rfl) (Enclosure.sfrac_false_div 99255447 524288) (BSN.sin_reduce0 qz304 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 61895635821875360169984) qz29) 226375608064910080 72057594037927936 Bool.false 766076 1048576 30 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q0 99255447 524288 226375608064910080 72057594037927936 30 61895635821875360169984 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 766076 1048576 61895635821875360169984 75557863725914323419136 1759179776 2147483648 280911 280636 (ep116 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz306 := (@Enclosure.Real.IsNear.recentre' qz25 Bool.false 468937 1048576 1 1048576 468937 1048576 1 1048576 (ep105 rfl rfl) rfl)

noncomputable def ep118 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz25 (Real.cos qz26)) (@HMul.hMul Real Real Real qz0 qz25 (@Neg.neg Real Real.instNeg (Real.sin qz26))) Bool.false 335752795819 1099511627776 29248286103037 77140636293136384 Bool.true 89810345303 274877906944 7312950074297 19285159073284096 (@Enclosure.Real.IsNear.mulLit_ff qz25 (Real.cos qz26) 468937 1048576 1 1048576 715987 1048576 3891513 4597940224 335752795819 1099511627776 29248286103037 77140636293136384 qz306 (@Enclosure.Real.IsNear.recentre' (Real.cos qz26) Bool.false 715987 1048576 7783026 9195880448 715987 1048576 3891513 4597940224 (ep114 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz25 (@Neg.neg Real Real.instNeg (Real.sin qz26)) 468937 1048576 1 1048576 191519 262144 3891513 4597940224 89810345303 274877906944 7312950074297 19285159073284096 qz306 (@Enclosure.Real.IsNear.neg (Real.sin qz26) Bool.false 191519 262144 3891513 4597940224 (@Enclosure.Real.IsNear.recentre' (Real.sin qz26) Bool.false 766076 1048576 7783026 9195880448 191519 262144 3891513 4597940224 (ep117 rfl rfl) rfl)) rfl)

noncomputable def ep119 := @ep46 335752795819 1099511627776 29248286103037 77140636293136384 Bool.true 89810345303 274877906944 7312950074297 19285159073284096 Bool.false 1182544231193358180024320 2151035425765 1099511627776 145963574859875 77140636293136384 Bool.false 24173879770702837448704 87944062291 549755813888 72909650682807 38570318146568192 (ep47 (BSN.head_sum_c_succ qz5 4 5 rfl rfl) (ep103 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep104 ep118) rfl rfl

noncomputable abbrev qz307 := (@Nat.cast Real Real.instNatCast 6)

noncomputable abbrev qz30 := (@Inv.inv Real Real.instInv (Real.sqrt qz307))

noncomputable abbrev qz540 := (Real.log (Enclosure.sfrac Bool.false 6 1))

noncomputable abbrev qz31 := (@HMul.hMul Real Real Real qz267 qz284 qz540)

noncomputable def ep120 := @Enclosure.Complex.IsNear.of_eq qz278 (Complex.mk (@HMul.hMul Real Real Real qz0 qz30 (Real.cos qz31)) (@HMul.hMul Real Real Real qz0 qz30 (@Neg.neg Real Real.instNeg (Real.sin qz31)))) Bool.true 432096521415 1099511627776 26724879602855 77140636293136384 Bool.false 121572295605 1099511627776 26673986965845 77140636293136384 (BSN.cpow_neg_s_mk qz13 117628 1000 6 qz14 rfl)

noncomputable abbrev qz308 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6) qz15)

noncomputable def ep121 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz307) 2568477 1048576 1 1048576 214039 214040 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz307) (Real.sqrt qz308) Bool.false 2568477 1048576 1 1048576 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz308) Bool.false 2568477 1048576 1 1048576 2568477 1048576 1 1048576 (BSN.sqrt_enclosure 6 1 1284238 1284239 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep122 := BSN.log_dyadic_bound 2 10 4 3 105000000 524288 140318 1434560 960 212580 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 2) (BSN.artanhQ 10) 0 3 1434560 105000000 960 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep123 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz540 117628 1000 0 1 4034681531866359 2251799813685248 250000000070159 35079500000000000000 118647879807594019113 562949953421312000 7351750002063165713 8769875000000000000000 qz17 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 250000000070159 35079500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz308) Bool.false 33845361775666394038272 18889465931478580854784 1000000000280636 140318000000000000000 4034681531866359 2251799813685248 250000000070159 35079500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 212580 524288 24973259072661432 36028797018963968 140318 1000000000000000 rfl rfl rfl rfl (ep122 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep124 := nat_lit 120336162045468456990026525818045456

noncomputable def ep125 := BSN.cos_dyadic_bound_f 588977954 2147483648 2 1 1048576 280911 ep124 ep77 ep124 ep124 ep78 ep124 1009385 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 588977954) qz292 0 1 ep124 ep77 ep124 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 588977954) qz293 0 1 ep124 ep78 ep124 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz32 := (@Nat.cast Real Real.instNatCast 1048576)

noncomputable abbrev qz33 := (@Nat.cast Real Real.instNatCast 151115727451828646838272)

noncomputable abbrev qz309 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 220998897) qz32)

noncomputable def ep126 := @Enclosure.Real.IsNear.cos_image qz31 qz309 Bool.false 220998897 1048576 55 65536 Bool.true 1009385 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz31 Bool.false 118647879807594019113 562949953421312000 7351750002063165713 8769875000000000000000 220998897 1048576 55 65536 (ep123 rfl) rfl) (Enclosure.sfrac_false_div 220998897 1048576) (BSN.cos_reduce2 qz309 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 41445639007365668798464) qz33) 226375608064910080 72057594037927936 Bool.false 1009385 1048576 33 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q2 220998897 1048576 226375608064910080 72057594037927936 33 41445639007365668798464 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1009385 1048576 41445639007365668798464 151115727451828646838272 588977954 2147483648 280911 280636 (ep125 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep127 := BSN.sin_dyadic_bound_f 588977954 2147483648 2 1 1048576 280911 ep124 ep81 ep124 ep124 ep82 ep124 283995 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 588977954) qz287 0 1 ep124 ep81 ep124 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 588977954) qz288 0 1 ep124 ep82 ep124 rfl rfl rfl rfl) rfl rfl

noncomputable def ep128 := @Enclosure.Real.IsNear.sin_image qz31 qz309 Bool.false 220998897 1048576 55 65536 Bool.true 283995 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz31 Bool.false 118647879807594019113 562949953421312000 7351750002063165713 8769875000000000000000 220998897 1048576 55 65536 (ep123 rfl) rfl) (Enclosure.sfrac_false_div 220998897 1048576) (BSN.sin_reduce2 qz309 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 41445639007365668798464) qz33) 226375608064910080 72057594037927936 Bool.false 283995 1048576 33 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q2 220998897 1048576 226375608064910080 72057594037927936 33 41445639007365668798464 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 283995 1048576 41445639007365668798464 151115727451828646838272 588977954 2147483648 280911 280636 (ep127 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz310 := (@Enclosure.Real.IsNear.recentre' qz30 Bool.false 428079 1048576 1 1048576 428079 1048576 1 1048576 (ep121 rfl rfl) rfl)

noncomputable def ep129 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz30 (Real.cos qz31)) (@HMul.hMul Real Real Real qz0 qz30 (@Neg.neg Real Real.instNeg (Real.sin qz31))) Bool.true 432096521415 1099511627776 26724879602855 77140636293136384 Bool.false 121572295605 1099511627776 26673986965845 77140636293136384 (@Enclosure.Real.IsNear.mulLit_ft qz30 (Real.cos qz31) 428079 1048576 1 1048576 1009385 1048576 3891513 4597940224 432096521415 1099511627776 26724879602855 77140636293136384 qz310 (@Enclosure.Real.IsNear.recentre' (Real.cos qz31) Bool.true 1009385 1048576 7783026 9195880448 1009385 1048576 3891513 4597940224 (ep126 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz30 (@Neg.neg Real Real.instNeg (Real.sin qz31)) 428079 1048576 1 1048576 283995 1048576 3891513 4597940224 121572295605 1099511627776 26673986965845 77140636293136384 qz310 (@Enclosure.Real.IsNear.neg (Real.sin qz31) Bool.true 283995 1048576 3891513 4597940224 (@Enclosure.Real.IsNear.recentre' (Real.sin qz31) Bool.true 283995 1048576 7783026 9195880448 283995 1048576 3891513 4597940224 (ep128 rfl rfl) rfl)) rfl)

noncomputable def ep130 := @ep43 432096521415 1099511627776 26724879602855 77140636293136384 Bool.false 121572295605 1099511627776 26673986965845 77140636293136384 Bool.false ep44 859469452175 549755813888 86344227231365 38570318146568192 Bool.false 163530595399370650157056 297460420187 1099511627776 172493288331459 77140636293136384 (ep45 (BSN.head_sum_c_succ qz5 5 6 rfl rfl) (ep119 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep120 ep129) rfl rfl

noncomputable abbrev qz311 := (@Nat.cast Real Real.instNatCast 7)

noncomputable abbrev qz34 := (@Inv.inv Real Real.instInv (Real.sqrt qz311))

noncomputable abbrev qz541 := (Real.log (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz35 := (@HMul.hMul Real Real Real qz267 qz284 qz541)

noncomputable def ep131 := @Enclosure.Complex.IsNear.of_eq qz277 (Complex.mk (@HMul.hMul Real Real Real qz0 qz34 (Real.cos qz35)) (@HMul.hMul Real Real Real qz0 qz34 (@Neg.neg Real Real.instNeg (Real.sin qz35)))) Bool.true 187736378225 549755813888 12371696077091 38570318146568192 Bool.true 178112814575 1099511627776 24708454726157 77140636293136384 (BSN.cpow_neg_s_mk qz13 117628 1000 7 qz14 rfl)

noncomputable abbrev qz312 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 7) qz15)

noncomputable def ep132 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz311) 2774271 1048576 1 1048576 198162 198163 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz311) (Real.sqrt qz312) Bool.false 2774271 1048576 1 1048576 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz312) Bool.false 2774271 1048576 1 1048576 2774271 1048576 1 1048576 (BSN.sqrt_enclosure 7 1 1387135 1387136 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep133 := BSN.log_dyadic_bound 3 11 5 4 202569142545 524288 140318 5259111624 688905 293399 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 3) (BSN.artanhQ 11) 0 4 5259111624 202569142545 688905 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep134 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz541 117628 1000 0 1 4381796493761783 2251799813685248 250000000070159 35079500000000000000 128855489492052752681 562949953421312000 7351750002063165713 8769875000000000000000 qz17 (BSN.isNear_log_sfrac 7 1 4381796493761783 2251799813685248 250000000070159 35079500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz312) Bool.false 36757173121942042968064 18889465931478580854784 1000000000280636 140318000000000000000 4381796493761783 2251799813685248 250000000070159 35079500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 293399 524288 24973259072661432 36028797018963968 140318 1000000000000000 rfl rfl rfl rfl (ep133 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep135 := nat_lit 2214508057874179634664890225019771927401944656537363358482266940924982695525985

noncomputable def ep136 := nat_lit 1184369911567356000331204168774066225386322678583318047273899256791580245601

noncomputable def ep137 := nat_lit 5797984505051742371550366734969006559783039101832531042996065198863958786932321

noncomputable def ep138 := BSN.sin_dyadic_bound_f 2422065707 2147483648 3 2 1048576 280911 ep135 ep59 ep136 ep137 ep62 ep136 947386 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2422065707) qz287 0 2 ep135 ep59 ep136 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2422065707) qz288 0 2 ep137 ep62 ep136 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz313 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 60003013) qz537)

noncomputable def ep139 := @Enclosure.Real.IsNear.cos_image qz35 qz313 Bool.false 60003013 262144 55 65536 Bool.true 947386 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz35 Bool.false 128855489492052752681 562949953421312000 7351750002063165713 8769875000000000000000 60003013 262144 55 65536 (ep134 rfl) rfl) (Enclosure.sfrac_false_div 60003013 262144) (BSN.cos_reduce1 qz313 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 42609430530695612071936) qz299) 226375608064910080 72057594037927936 Bool.false 947386 1048576 36 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q1 60003013 262144 226375608064910080 72057594037927936 36 42609430530695612071936 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 947386 1048576 42609430530695612071936 37778931862957161709568 2422065707 2147483648 280911 280636 (ep138 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep140 := nat_lit 1230808641001907510813975104641550655767918730377905562733381144628008866512481

noncomputable def ep141 := nat_lit 3690057183182587820441262905587103834852983545776550052105595635370443439046241

noncomputable def ep142 := BSN.cos_dyadic_bound_f 2422065707 2147483648 3 2 1048576 280911 ep140 ep66 ep136 ep141 ep68 ep136 449411 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2422065707) qz292 0 2 ep140 ep66 ep136 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2422065707) qz293 0 2 ep141 ep68 ep136 rfl rfl rfl rfl) rfl rfl

noncomputable def ep143 := @Enclosure.Real.IsNear.sin_image qz35 qz313 Bool.false 60003013 262144 55 65536 Bool.false 449411 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz35 Bool.false 128855489492052752681 562949953421312000 7351750002063165713 8769875000000000000000 60003013 262144 55 65536 (ep134 rfl) rfl) (Enclosure.sfrac_false_div 60003013 262144) (BSN.sin_reduce1 qz313 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 42609430530695612071936) qz299) 226375608064910080 72057594037927936 Bool.false 449411 1048576 36 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q1 60003013 262144 226375608064910080 72057594037927936 36 42609430530695612071936 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 449411 1048576 42609430530695612071936 37778931862957161709568 2422065707 2147483648 280911 280636 (ep142 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz314 := (@Enclosure.Real.IsNear.recentre' qz34 Bool.false 396325 1048576 1 1048576 396325 1048576 1 1048576 (ep132 rfl rfl) rfl)

noncomputable def ep144 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz34 (Real.cos qz35)) (@HMul.hMul Real Real Real qz0 qz34 (@Neg.neg Real Real.instNeg (Real.sin qz35))) Bool.true 187736378225 549755813888 12371696077091 38570318146568192 Bool.true 178112814575 1099511627776 24708454726157 77140636293136384 (@Enclosure.Real.IsNear.mulLit_ft qz34 (Real.cos qz35) 396325 1048576 1 1048576 473693 524288 3891513 4597940224 187736378225 549755813888 12371696077091 38570318146568192 qz314 (@Enclosure.Real.IsNear.recentre' (Real.cos qz35) Bool.true 947386 1048576 7783026 9195880448 473693 524288 3891513 4597940224 (ep139 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz34 (@Neg.neg Real Real.instNeg (Real.sin qz35)) 396325 1048576 1 1048576 449411 1048576 3891513 4597940224 178112814575 1099511627776 24708454726157 77140636293136384 qz314 (@Enclosure.Real.IsNear.neg (Real.sin qz35) Bool.false 449411 1048576 3891513 4597940224 (@Enclosure.Real.IsNear.recentre' (Real.sin qz35) Bool.false 449411 1048576 7783026 9195880448 449411 1048576 3891513 4597940224 (ep143 rfl rfl) rfl)) rfl)

noncomputable def ep145 := @ep41 187736378225 549755813888 12371696077091 38570318146568192 Bool.true 178112814575 1099511627776 24708454726157 77140636293136384 Bool.false 369289162784870341017600 335866536975 274877906944 12339490413557 4821289768321024 Bool.false 131224080117618192678912 29836901403 274877906944 12325108941101 4821289768321024 (ep42 (BSN.head_sum_c_succ qz5 6 7 rfl rfl) (ep130 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep131 ep144) rfl rfl

noncomputable abbrev qz315 := (@Nat.cast Real Real.instNatCast 8)

noncomputable abbrev qz36 := (@Inv.inv Real Real.instInv (Real.sqrt qz315))

noncomputable abbrev qz542 := (Real.log (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz37 := (@HMul.hMul Real Real Real qz267 qz284 qz542)

noncomputable def ep146 := @Enclosure.Complex.IsNear.of_eq qz276 (Complex.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz37)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz37)))) Bool.false 351097376077 1099511627776 23149529454533 77140636293136384 Bool.false 41717538583 274877906944 5778666247967 19285159073284096 (BSN.cpow_neg_s_mk qz13 117628 1000 8 qz14 rfl)

noncomputable abbrev qz316 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8) qz15)

noncomputable def ep147 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz315) 2965821 1048576 1 1048576 185363 185364 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz315) (Real.sqrt qz316) Bool.false 2965821 1048576 1 1048576 (BSN.sqrt_natCast_div_one 8) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz316) Bool.false 2965821 1048576 1 1048576 2965821 1048576 1 1048576 (BSN.sqrt_enclosure 8 1 1482910 1482911 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep148 := BSN.log_dyadic_bound 0 16 1 0 1 524288 140318 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl

noncomputable def ep149 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz542 117628 1000 0 1 9364972152248037 4503599627370496 500000000210477 70159000000000000000 275395736081158024059 1125899906842624000 14703500006189497139 17539750000000000000000 qz17 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 500000000210477 70159000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz316) Bool.false 39279540158062550581248 18889465931478580854784 1000000000420954 140318000000000000000 9364972152248037 4503599627370496 500000000210477 70159000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 524288 24973259072661432 36028797018963968 140318 1000000000000000 rfl rfl rfl rfl (ep148 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep150 := nat_lit 2208666345090588449981795366010295327288599840675200494698363338050662160977505

noncomputable def ep151 := nat_lit 1178132910629295728606107635148579408621436524467397838737056625625139039841

noncomputable def ep152 := nat_lit 5782694879096236604486958927189104347665707733109720746756805888929293529828961

noncomputable def ep153 := BSN.sin_dyadic_bound_f 2420467669 2147483648 3 2 1048576 280911 ep150 ep59 ep151 ep152 ep62 ep151 947051 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2420467669) qz287 0 2 ep150 ep59 ep151 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2420467669) qz288 0 2 ep152 ep62 ep151 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz317 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 256482265) qz32)

noncomputable def ep154 := @Enclosure.Real.IsNear.cos_image qz37 qz317 Bool.false 256482265 1048576 55 65536 Bool.false 947051 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz37 Bool.false 275395736081158024059 1125899906842624000 14703500006189497139 17539750000000000000000 256482265 1048576 55 65536 (ep149 rfl) rfl) (Enclosure.sfrac_false_div 256482265 1048576) (BSN.cos_reduce3 qz317 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 170325270244477296967680) qz33) 226375608064910080 72057594037927936 Bool.false 947051 1048576 38 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q3 256482265 1048576 226375608064910080 72057594037927936 38 170325270244477296967680 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 947051 1048576 170325270244477296967680 151115727451828646838272 2420467669 2147483648 280911 280636 (ep153 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep155 := nat_lit 1227560473010606603647044584510230106008609438830430229427418324083979040116321

noncomputable def ep156 := nat_lit 3680325153210561219483921538260393159208585443442355892604780859000686842269281

noncomputable def ep157 := BSN.cos_dyadic_bound_f 2420467669 2147483648 3 2 1048576 280911 ep155 ep66 ep151 ep156 ep68 ep151 450116 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2420467669) qz292 0 2 ep155 ep66 ep151 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2420467669) qz293 0 2 ep156 ep68 ep151 rfl rfl rfl rfl) rfl rfl

noncomputable def ep158 := @Enclosure.Real.IsNear.sin_image qz37 qz317 Bool.false 256482265 1048576 55 65536 Bool.true 450116 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz37 Bool.false 275395736081158024059 1125899906842624000 14703500006189497139 17539750000000000000000 256482265 1048576 55 65536 (ep149 rfl) rfl) (Enclosure.sfrac_false_div 256482265 1048576) (BSN.sin_reduce3 qz317 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 170325270244477296967680) qz33) 226375608064910080 72057594037927936 Bool.false 450116 1048576 38 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q3 256482265 1048576 226375608064910080 72057594037927936 38 170325270244477296967680 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 450116 1048576 170325270244477296967680 151115727451828646838272 2420467669 2147483648 280911 280636 (ep157 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz318 := (@Enclosure.Real.IsNear.recentre' qz36 Bool.false 370727 1048576 1 1048576 370727 1048576 1 1048576 (ep147 rfl rfl) rfl)

noncomputable def ep159 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz37)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz37))) Bool.false 351097376077 1099511627776 23149529454533 77140636293136384 Bool.false 41717538583 274877906944 5778666247967 19285159073284096 (@Enclosure.Real.IsNear.mulLit_ff qz36 (Real.cos qz37) 370727 1048576 1 1048576 947051 1048576 3891513 4597940224 351097376077 1099511627776 23149529454533 77140636293136384 qz318 (@Enclosure.Real.IsNear.recentre' (Real.cos qz37) Bool.false 947051 1048576 7783026 9195880448 947051 1048576 3891513 4597940224 (ep154 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz36 (@Neg.neg Real Real.instNeg (Real.sin qz37)) 370727 1048576 1 1048576 112529 262144 3891513 4597940224 41717538583 274877906944 5778666247967 19285159073284096 qz318 (@Enclosure.Real.IsNear.neg (Real.sin qz37) Bool.true 112529 262144 3891513 4597940224 (@Enclosure.Real.IsNear.recentre' (Real.sin qz37) Bool.true 450116 1048576 7783026 9195880448 112529 262144 3891513 4597940224 (ep158 rfl rfl) rfl)) rfl)

noncomputable def ep160 := @ep39 351097376077 1099511627776 23149529454533 77140636293136384 Bool.false 41717538583 274877906944 5778666247967 19285159073284096 Bool.false 465798074654446518796288 1694563523977 1099511627776 220581376071445 77140636293136384 Bool.false 19668734695901740662784 35777219993 137438953472 55079102012371 19285159073284096 (ep40 (BSN.head_sum_c_succ qz5 7 8 rfl rfl) (ep145 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep146 ep159) rfl rfl

theorem EMRow38.d6 : Enclosure.Complex.IsNear qz3 Bool.false 1694563523977 1099511627776 220581376071445 77140636293136384 Bool.false 35777219993 137438953472 55079102012371 19285159073284096 := ep38 (BSN.head_sum_c_succ qz5 8 9 rfl rfl) (ep160 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz38 := (BSN.headSumC qz272 17)

noncomputable abbrev qz39 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 16) qz275)

noncomputable def ep161 := @Enclosure.Complex.IsNear.of_eq qz38 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 16) qz39) Bool.false 2347483159709 1099511627776 370715408847401 77140636293136384 Bool.false 268061722897 1099511627776 370311660079289 77140636293136384

noncomputable def ep162 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 16) qz39 Bool.false 132457331273 68719476736 88583038705979 19285159073284096 Bool.false 114772555075 1099511627776 353948445781451 77140636293136384 Bool.false

noncomputable abbrev qz40 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 15) qz275)

noncomputable def ep163 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 16) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 15) qz40) Bool.false 132457331273 68719476736 88583038705979 19285159073284096 Bool.false 114772555075 1099511627776 353948445781451 77140636293136384

noncomputable def ep164 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 15) qz40 Bool.false 2211134507921 1099511627776 337450825389433 77140636293136384 Bool.true 38465452301 274877906944 168510648243147 38570318146568192 Bool.true

noncomputable def ep165 := nat_lit 2330214014701457603821568

noncomputable abbrev qz41 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 14) qz275)

noncomputable def ep166 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 15) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 14) qz41) Bool.false 2211134507921 1099511627776 337450825389433 77140636293136384 Bool.true 38465452301 274877906944 168510648243147 38570318146568192

noncomputable def ep167 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 14) qz41 Bool.false 2455176277667 1099511627776 319940558681983 77140636293136384 Bool.false 4914904277 549755813888 9985348296459 2410644884160512 Bool.true

noncomputable def ep168 := nat_lit 1215584051017951737806848

noncomputable abbrev qz42 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 13) qz275)

noncomputable def ep169 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 14) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 13) qz42) Bool.false 2455176277667 1099511627776 319940558681983 77140636293136384 Bool.false 4914904277 549755813888 9985348296459 2410644884160512

noncomputable def ep170 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 13) qz42 Bool.false 2152302735839 1099511627776 301759566546267 77140636293136384 Bool.false 2834687581 68719476736 150707324628405 38570318146568192 Bool.false

noncomputable abbrev qz43 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 12) qz275)

noncomputable def ep171 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 13) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 12) qz43) Bool.false 2152302735839 1099511627776 301759566546267 77140636293136384 Bool.false 2834687581 68719476736 150707324628405 38570318146568192

noncomputable def ep172 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 12) qz43 Bool.false 2467172392997 1099511627776 282839334939057 77140636293136384 Bool.false 2675585585 549755813888 35319765743813 9642579536642048 Bool.true

noncomputable abbrev qz44 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 11) qz275)

noncomputable def ep173 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 12) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 11) qz44) Bool.false 2467172392997 1099511627776 282839334939057 77140636293136384 Bool.false 2675585585 549755813888 35319765743813 9642579536642048

noncomputable def ep174 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 11) qz44 Bool.false 1105096988207 549755813888 65774245224493 19285159073284096 Bool.true 204086085009 1099511627776 262826321858567 77140636293136384 Bool.false

noncomputable def ep175 := nat_lit 1356342366914070326542336

noncomputable abbrev qz45 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 10) qz275)

noncomputable def ep176 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 11) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 10) qz45) Bool.false 1105096988207 549755813888 65774245224493 19285159073284096 Bool.true 204086085009 1099511627776 262826321858567 77140636293136384

noncomputable def ep177 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 10) qz45 Bool.false 1937965044427 1099511627776 14258423107115 4537684487831552 Bool.false 12210082869 1099511627776 14243198133637 4537684487831552 Bool.false

noncomputable def ep178 := nat_lit 2430133976707667291275264

noncomputable abbrev qz319 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 9) qz7)

noncomputable def ep179 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 10) (@HAdd.hAdd Complex Complex Complex qz4 qz3 qz319) Bool.false 1937965044427 1099511627776 14258423107115 4537684487831552 Bool.false 12210082869 1099511627776 14243198133637 4537684487831552

noncomputable def ep180 := @Enclosure.Complex.IsNear.addLitP qz3 qz319 Bool.false 1694563523977 1099511627776 220581376071445 77140636293136384 Bool.false 35777219993 137438953472 55079102012371 19285159073284096 Bool.false

noncomputable abbrev qz320 := (@Nat.cast Real Real.instNatCast 9)

noncomputable abbrev qz46 := (@Inv.inv Real Real.instInv (Real.sqrt qz320))

noncomputable abbrev qz543 := (Real.log (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz47 := (@HMul.hMul Real Real Real qz267 qz284 qz543)

noncomputable def ep181 := @Enclosure.Complex.IsNear.of_eq qz319 (Complex.mk (@HMul.hMul Real Real Real qz0 qz46 (Real.cos qz47)) (@HMul.hMul Real Real Real qz0 qz46 (@Neg.neg Real Real.instNeg (Real.sin qz47)))) Bool.false 121700760225 549755813888 10905908374755 38570318146568192 Bool.true 274007677075 1099511627776 21817960222345 77140636293136384 (BSN.cpow_neg_s_mk qz13 117628 1000 9 qz14 rfl)

noncomputable abbrev qz321 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9) qz15)

noncomputable def ep182 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz320) 3145729 1048576 1 1048576 174762 174763 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz320) (Real.sqrt qz321) Bool.false 3145729 1048576 1 1048576 (BSN.sqrt_natCast_div_one 9) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz321) Bool.false 3145729 1048576 1 1048576 3145729 1048576 1 1048576 (BSN.sqrt_enclosure 9 1 1572864 1572865 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep183 := BSN.log_dyadic_bound 1 17 2 1 867 524288 140318 1 1 61752 18 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1) (BSN.artanhQ 17) 0 1 1 867 1 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep184 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz543 117628 1000 0 1 9895417793173221 4503599627370496 500000000210477 70159000000000000000 290994551043844909947 1125899906842624000 14703500006189497139 17539750000000000000000 qz17 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 500000000210477 70159000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz321) Bool.false 41504390431577613533184 18889465931478580854784 1000000000420954 140318000000000000000 9895417793173221 4503599627370496 500000000210477 70159000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 61752 524288 24973259072661432 36028797018963968 140318 1000000000000000 rfl rfl rfl rfl (ep183 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep185 := nat_lit 386582462836165732691705015311557286401824990395722713311828816832886971597056

noncomputable def ep186 := nat_lit 116994084187912106383938982345914121070775863816300702697171243640391762176

noncomputable def ep187 := nat_lit 1159513400340121373862347167969980030963333419459535538530092108011380131266816

noncomputable def ep188 := BSN.cos_dyadic_bound_f 1813512226 2147483648 3 2 1048576 280911 ep185 ep66 ep186 ep187 ep68 ep186 696378 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1813512226) qz292 0 2 ep185 ep66 ep186 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1813512226) qz293 0 2 ep187 ep68 ep186 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz322 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 135504897) qz27)

noncomputable def ep189 := @Enclosure.Real.IsNear.cos_image qz47 qz322 Bool.false 135504897 524288 55 65536 Bool.false 696378 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz47 Bool.false 290994551043844909947 1125899906842624000 14703500006189497139 17539750000000000000000 135504897 524288 55 65536 (ep184 rfl) rfl) (Enclosure.sfrac_false_div 135504897 524288) (BSN.cos_reduce0 qz322 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 63807288968243654426624) qz29) 226375608064910080 72057594037927936 Bool.false 696378 1048576 41 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q0 135504897 524288 226375608064910080 72057594037927936 41 63807288968243654426624 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 696378 1048576 63807288968243654426624 75557863725914323419136 1813512226 2147483648 280911 280636 (ep188 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep190 := nat_lit 10816380364424695396176001941049205776

noncomputable def ep191 := BSN.sin_dyadic_bound_f 1813512226 2147483648 2 1 1048576 280911 ep190 ep81 ep190 ep190 ep82 ep190 783943 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1813512226) qz287 0 1 ep190 ep81 ep190 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1813512226) qz288 0 1 ep190 ep82 ep190 rfl rfl rfl rfl) rfl rfl

noncomputable def ep192 := @Enclosure.Real.IsNear.sin_image qz47 qz322 Bool.false 135504897 524288 55 65536 Bool.false 783943 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz47 Bool.false 290994551043844909947 1125899906842624000 14703500006189497139 17539750000000000000000 135504897 524288 55 65536 (ep184 rfl) rfl) (Enclosure.sfrac_false_div 135504897 524288) (BSN.sin_reduce0 qz322 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 63807288968243654426624) qz29) 226375608064910080 72057594037927936 Bool.false 783943 1048576 41 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q0 135504897 524288 226375608064910080 72057594037927936 41 63807288968243654426624 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 783943 1048576 63807288968243654426624 75557863725914323419136 1813512226 2147483648 280911 280636 (ep191 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz323 := (@Enclosure.Real.IsNear.recentre' qz46 Bool.false 349525 1048576 1 1048576 349525 1048576 1 1048576 (ep182 rfl rfl) rfl)

noncomputable def ep193 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz46 (Real.cos qz47)) (@HMul.hMul Real Real Real qz0 qz46 (@Neg.neg Real Real.instNeg (Real.sin qz47))) Bool.false 121700760225 549755813888 10905908374755 38570318146568192 Bool.true 274007677075 1099511627776 21817960222345 77140636293136384 (@Enclosure.Real.IsNear.mulLit_ff qz46 (Real.cos qz47) 349525 1048576 1 1048576 348189 524288 3891513 4597940224 121700760225 549755813888 10905908374755 38570318146568192 qz323 (@Enclosure.Real.IsNear.recentre' (Real.cos qz47) Bool.false 696378 1048576 7783026 9195880448 348189 524288 3891513 4597940224 (ep189 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz46 (@Neg.neg Real Real.instNeg (Real.sin qz47)) 349525 1048576 1 1048576 783943 1048576 3891513 4597940224 274007677075 1099511627776 21817960222345 77140636293136384 qz323 (@Enclosure.Real.IsNear.neg (Real.sin qz47) Bool.false 783943 1048576 3891513 4597940224 (@Enclosure.Real.IsNear.recentre' (Real.sin qz47) Bool.false 783943 1048576 7783026 9195880448 783943 1048576 3891513 4597940224 (ep192 rfl rfl) rfl)) rfl)

noncomputable def ep194 := @ep180 121700760225 549755813888 10905908374755 38570318146568192 Bool.true 274007677075 1099511627776 21817960222345 77140636293136384 Bool.false 1065407550285459463602176 1937965044427 1099511627776 14258423107115 4537684487831552 Bool.false 1678141011321755271168 12210082869 1099511627776 14243198133637 4537684487831552 EMRow38.d6 (ep181 ep193) rfl rfl

noncomputable abbrev qz324 := (@Nat.cast Real Real.instNatCast 10)

noncomputable abbrev qz48 := (@Inv.inv Real Real.instInv (Real.sqrt qz324))

noncomputable abbrev qz544 := (Real.log (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz49 := (@HMul.hMul Real Real Real qz267 qz284 qz544)

noncomputable def ep195 := @Enclosure.Complex.IsNear.of_eq qz45 (Complex.mk (@HMul.hMul Real Real Real qz0 qz48 (Real.cos qz49)) (@HMul.hMul Real Real Real qz0 qz48 (@Neg.neg Real Real.instNeg (Real.sin qz49)))) Bool.false 272228931987 1099511627776 20703788077017 77140636293136384 Bool.true 108148083939 549755813888 10345976793369 38570318146568192 (BSN.cpow_neg_s_mk qz13 117628 1000 10 qz14 rfl)

noncomputable abbrev qz325 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 10) qz15)

noncomputable def ep196 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz324) 3315889 1048576 1 1048576 165794 165795 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz324) (Real.sqrt qz325) Bool.false 3315889 1048576 1 1048576 (BSN.sqrt_natCast_div_one 10) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz325) Bool.false 3315889 1048576 1 1048576 3315889 1048576 1 1048576 (BSN.sqrt_enclosure 10 1 1657944 1657945 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep197 := BSN.log_dyadic_bound 2 18 3 2 1574640 524288 140318 6528 48 116991 20 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 2) (BSN.artanhQ 18) 0 2 6528 1574640 48 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep198 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz544 117628 1000 0 1 10369917190100709 4503599627370496 500000000210477 70159000000000000000 304948154809291549563 1125899906842624000 14703500006189497139 17539750000000000000000 qz17 (BSN.isNear_log_sfrac 10 1 10369917190100709 4503599627370496 500000000210477 70159000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz325) Bool.false 43494585150108164161536 18889465931478580854784 1000000000420954 140318000000000000000 10369917190100709 4503599627370496 500000000210477 70159000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 116991 524288 24973259072661432 36028797018963968 140318 1000000000000000 rfl rfl rfl rfl (ep197 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep199 := nat_lit 154429290230438993291612295108829161543288906857485002293932726978485779690625

noncomputable def ep200 := nat_lit 18676556665953308282315475092970669315863191476677898358684517749062890625

noncomputable def ep201 := nat_lit 463250517577985073258272254376301543291234994189501651085080811899959213290625

noncomputable def ep202 := BSN.cos_dyadic_bound_f 1441823505 2147483648 3 2 1048576 280911 ep199 ep66 ep200 ep201 ep68 ep200 820983 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1441823505) qz292 0 2 ep199 ep66 ep200 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1441823505) qz293 0 2 ep201 ep68 ep200 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz326 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 71001275) qz537)

noncomputable def ep203 := @Enclosure.Real.IsNear.cos_image qz49 qz326 Bool.false 71001275 262144 55 65536 Bool.false 820983 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz49 Bool.false 304948154809291549563 1125899906842624000 14703500006189497139 17539750000000000000000 71001275 262144 55 65536 (ep198 rfl) rfl) (Enclosure.sfrac_false_div 71001275 262144) (BSN.cos_reduce0 qz326 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 25364827352904090255360) qz299) 226375608064910080 72057594037927936 Bool.false 820983 1048576 43 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q0 71001275 262144 226375608064910080 72057594037927936 43 25364827352904090255360 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 820983 1048576 25364827352904090255360 37778931862957161709568 1441823505 2147483648 280911 280636 (ep202 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep204 := nat_lit 4321638192393401676296634113749250625

noncomputable def ep205 := BSN.sin_dyadic_bound_f 1441823505 2147483648 2 1 1048576 280911 ep204 ep81 ep204 ep204 ep82 ep204 652302 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1441823505) qz287 0 1 ep204 ep81 ep204 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1441823505) qz288 0 1 ep204 ep82 ep204 rfl rfl rfl rfl) rfl rfl

noncomputable def ep206 := @Enclosure.Real.IsNear.sin_image qz49 qz326 Bool.false 71001275 262144 55 65536 Bool.false 652302 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz49 Bool.false 304948154809291549563 1125899906842624000 14703500006189497139 17539750000000000000000 71001275 262144 55 65536 (ep198 rfl) rfl) (Enclosure.sfrac_false_div 71001275 262144) (BSN.sin_reduce0 qz326 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 25364827352904090255360) qz299) 226375608064910080 72057594037927936 Bool.false 652302 1048576 43 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q0 71001275 262144 226375608064910080 72057594037927936 43 25364827352904090255360 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 652302 1048576 25364827352904090255360 37778931862957161709568 1441823505 2147483648 280911 280636 (ep205 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz327 := (@Enclosure.Real.IsNear.recentre' qz48 Bool.false 331589 1048576 1 1048576 331589 1048576 1 1048576 (ep196 rfl rfl) rfl)

noncomputable def ep207 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz48 (Real.cos qz49)) (@HMul.hMul Real Real Real qz0 qz48 (@Neg.neg Real Real.instNeg (Real.sin qz49))) Bool.false 272228931987 1099511627776 20703788077017 77140636293136384 Bool.true 108148083939 549755813888 10345976793369 38570318146568192 (@Enclosure.Real.IsNear.mulLit_ff qz48 (Real.cos qz49) 331589 1048576 1 1048576 820983 1048576 3891513 4597940224 272228931987 1099511627776 20703788077017 77140636293136384 qz327 (@Enclosure.Real.IsNear.recentre' (Real.cos qz49) Bool.false 820983 1048576 7783026 9195880448 820983 1048576 3891513 4597940224 (ep203 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz48 (@Neg.neg Real Real.instNeg (Real.sin qz49)) 331589 1048576 1 1048576 326151 524288 3891513 4597940224 108148083939 549755813888 10345976793369 38570318146568192 qz327 (@Enclosure.Real.IsNear.neg (Real.sin qz49) Bool.false 326151 524288 3891513 4597940224 (@Enclosure.Real.IsNear.recentre' (Real.sin qz49) Bool.false 652302 1048576 7783026 9195880448 326151 524288 3891513 4597940224 (ep206 rfl rfl) rfl)) rfl)

noncomputable def ep208 := @ep177 272228931987 1099511627776 20703788077017 77140636293136384 Bool.true 108148083939 549755813888 10345976793369 38570318146568192 Bool.false ep178 1105096988207 549755813888 65774245224493 19285159073284096 Bool.true 112197511767338350804992 204086085009 1099511627776 262826321858567 77140636293136384 (ep179 (BSN.head_sum_c_succ qz5 9 10 rfl rfl) (ep194 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep195 ep207) rfl rfl

noncomputable abbrev qz328 := (@Nat.cast Real Real.instNatCast 11)

noncomputable abbrev qz50 := (@Inv.inv Real Real.instInv (Real.sqrt qz328))

noncomputable abbrev qz545 := (Real.log (Enclosure.sfrac Bool.false 11 1))

noncomputable abbrev qz51 := (@HMul.hMul Real Real Real qz267 qz284 qz545)

noncomputable def ep209 := @Enclosure.Complex.IsNear.of_eq qz44 (Complex.mk (@HMul.hMul Real Real Real qz0 qz50 (Real.cos qz51)) (@HMul.hMul Real Real Real qz0 qz50 (@Neg.neg Real Real.instNeg (Real.sin qz51)))) Bool.false 256978416583 1099511627776 19742354041085 77140636293136384 Bool.false 209437256179 1099511627776 19731804091937 77140636293136384 (BSN.cpow_neg_s_mk qz13 117628 1000 11 qz14 rfl)

noncomputable abbrev qz329 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11) qz15)

noncomputable def ep210 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz328) 3477733 1048576 1 1048576 158078 158079 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz328) (Real.sqrt qz329) Bool.false 3477733 1048576 1 1048576 (BSN.sqrt_natCast_div_one 11) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz329) Bool.false 3477733 1048576 1 1048576 3477733 1048576 1 1048576 (BSN.sqrt_enclosure 11 1 1738866 1738867 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep211 := BSN.log_dyadic_bound 3 19 4 3 4939817505 524288 140318 41676111 10935 166961 22 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 3) (BSN.artanhQ 19) 0 3 41676111 4939817505 10935 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep212 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz545 117628 1000 0 1 10799156221662949 4503599627370496 500000000210477 70159000000000000000 317570787010442341243 1125899906842624000 14703500006189497139 17539750000000000000000 qz17 (BSN.isNear_log_sfrac 11 1 10799156221662949 4503599627370496 500000000210477 70159000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz329) Bool.false 45294944137145793642496 18889465931478580854784 1000000000420954 140318000000000000000 10799156221662949 4503599627370496 500000000210477 70159000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 166961 524288 24973259072661432 36028797018963968 140318 1000000000000000 rfl rfl rfl rfl (ep211 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep213 := nat_lit 846754842054485324231889591575480476895676895906260693897219826705912056152320

noncomputable def ep214 := nat_lit 173274685140527284573163396358494496063121566233611472674544128001147044096

noncomputable def ep215 := nat_lit 2217410713033424519289449522913106543637908721028209303536959808022529718518016

noncomputable def ep216 := BSN.sin_dyadic_bound_f 1904767138 2147483648 3 2 1048576 280911 ep213 ep59 ep214 ep215 ep62 ep214 812819 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1904767138) qz287 0 2 ep213 ep59 ep214 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1904767138) qz288 0 2 ep215 ep62 ep214 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz330 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 147880421) qz27)

noncomputable def ep217 := @Enclosure.Real.IsNear.cos_image qz51 qz330 Bool.false 147880421 524288 55 65536 Bool.false 812819 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz51 Bool.false 317570787010442341243 1125899906842624000 14703500006189497139 17539750000000000000000 147880421 524288 55 65536 (ep212 rfl) rfl) (Enclosure.sfrac_false_div 147880421 524288) (BSN.cos_reduce3 qz330 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 67018035748478178557952) qz29) 226375608064910080 72057594037927936 Bool.false 812819 1048576 44 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q3 147880421 524288 226375608064910080 72057594037927936 44 67018035748478178557952 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 812819 1048576 67018035748478178557952 75557863725914323419136 1904767138 2147483648 280911 280636 (ep216 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep218 := nat_lit 470496367668109858921971179051426262495848551755137546152977478893507207659776

noncomputable def ep219 := nat_lit 1411142553634048522196767210361561798495419412132945415513583348424519328891136

noncomputable def ep220 := BSN.cos_dyadic_bound_f 1904767138 2147483648 3 2 1048576 280911 ep218 ep66 ep214 ep219 ep68 ep214 662447 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1904767138) qz292 0 2 ep218 ep66 ep214 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1904767138) qz293 0 2 ep219 ep68 ep214 rfl rfl rfl rfl) rfl rfl

noncomputable def ep221 := @Enclosure.Real.IsNear.sin_image qz51 qz330 Bool.false 147880421 524288 55 65536 Bool.true 662447 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz51 Bool.false 317570787010442341243 1125899906842624000 14703500006189497139 17539750000000000000000 147880421 524288 55 65536 (ep212 rfl) rfl) (Enclosure.sfrac_false_div 147880421 524288) (BSN.sin_reduce3 qz330 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 67018035748478178557952) qz29) 226375608064910080 72057594037927936 Bool.false 662447 1048576 44 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q3 147880421 524288 226375608064910080 72057594037927936 44 67018035748478178557952 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 662447 1048576 67018035748478178557952 75557863725914323419136 1904767138 2147483648 280911 280636 (ep220 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz331 := (@Enclosure.Real.IsNear.recentre' qz50 Bool.false 316157 1048576 1 1048576 316157 1048576 1 1048576 (ep210 rfl rfl) rfl)

noncomputable def ep222 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz50 (Real.cos qz51)) (@HMul.hMul Real Real Real qz0 qz50 (@Neg.neg Real Real.instNeg (Real.sin qz51))) Bool.false 256978416583 1099511627776 19742354041085 77140636293136384 Bool.false 209437256179 1099511627776 19731804091937 77140636293136384 (@Enclosure.Real.IsNear.mulLit_ff qz50 (Real.cos qz51) 316157 1048576 1 1048576 812819 1048576 3891513 4597940224 256978416583 1099511627776 19742354041085 77140636293136384 qz331 (@Enclosure.Real.IsNear.recentre' (Real.cos qz51) Bool.false 812819 1048576 7783026 9195880448 812819 1048576 3891513 4597940224 (ep217 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz50 (@Neg.neg Real Real.instNeg (Real.sin qz51)) 316157 1048576 1 1048576 662447 1048576 3891513 4597940224 209437256179 1099511627776 19731804091937 77140636293136384 qz331 (@Enclosure.Real.IsNear.neg (Real.sin qz51) Bool.true 662447 1048576 3891513 4597940224 (@Enclosure.Real.IsNear.recentre' (Real.sin qz51) Bool.true 662447 1048576 7783026 9195880448 662447 1048576 3891513 4597940224 (ep221 rfl rfl) rfl)) rfl)

noncomputable def ep223 := @ep174 256978416583 1099511627776 19742354041085 77140636293136384 Bool.false 209437256179 1099511627776 19731804091937 77140636293136384 Bool.false ep175 2467172392997 1099511627776 282839334939057 77140636293136384 Bool.false 5883674923634702417920 2675585585 549755813888 35319765743813 9642579536642048 (ep176 (BSN.head_sum_c_succ qz5 10 11 rfl rfl) (ep208 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep209 ep222) rfl rfl

noncomputable abbrev qz332 := (@Nat.cast Real Real.instNatCast 12)

noncomputable abbrev qz52 := (@Inv.inv Real Real.instInv (Real.sqrt qz332))

noncomputable abbrev qz546 := (Real.log (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz53 := (@HMul.hMul Real Real Real qz267 qz284 qz546)

noncomputable def ep224 := @Enclosure.Complex.IsNear.of_eq qz43 (Complex.mk (@HMul.hMul Real Real Real qz0 qz52 (Real.cos qz53)) (@HMul.hMul Real Real Real qz0 qz52 (@Neg.neg Real Real.instNeg (Real.sin qz53)))) Bool.true 157434828579 549755813888 9460115803605 38570318146568192 Bool.false 20001915063 549755813888 9428261653153 38570318146568192 (BSN.cpow_neg_s_mk qz13 117628 1000 12 qz14 rfl)

noncomputable abbrev qz333 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 12) qz15)

noncomputable def ep225 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz332) 3632373 1048576 1 1048576 151348 151349 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz332) (Real.sqrt qz333) Bool.false 3632373 1048576 1 1048576 (BSN.sqrt_natCast_div_one 12) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz333) Bool.false 3632373 1048576 1 1048576 3632373 1048576 1 1048576 (BSN.sqrt_enclosure 12 1 1816186 1816187 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep226 := BSN.log_dyadic_bound 4 20 4 3 6720000000 524288 140318 91811840 61440 212580 24 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 4) (BSN.artanhQ 20) 0 3 91811840 6720000000 61440 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep227 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz546 117628 1000 0 1 11191020447815397 4503599627370496 500000000210477 70159000000000000000 329094338308907379579 1125899906842624000 14703500006189497139 17539750000000000000000 qz17 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 500000000210477 70159000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz333) Bool.false 46938541828353910898688 18889465931478580854784 1000000000420954 140318000000000000000 11191020447815397 4503599627370496 500000000210477 70159000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 212580 524288 24973259072661432 36028797018963968 140318 1000000000000000 rfl rfl rfl rfl (ep226 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep228 := nat_lit 5424061235544103658381323694015121

noncomputable def ep229 := BSN.cos_dyadic_bound_f 271382067 2147483648 2 1 1048576 280911 ep228 ep77 ep228 ep228 ep78 ep228 1040214 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 271382067) qz292 0 1 ep228 ep77 ep228 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 271382067) qz293 0 1 ep228 ep78 ep228 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz334 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 153246493) qz27)

noncomputable def ep230 := @Enclosure.Real.IsNear.cos_image qz53 qz334 Bool.false 153246493 524288 55 65536 Bool.true 1040214 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz53 Bool.false 329094338308907379579 1125899906842624000 14703500006189497139 17539750000000000000000 153246493 524288 55 65536 (ep227 rfl) rfl) (Enclosure.sfrac_false_div 153246493 524288) (BSN.cos_reduce2 qz334 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9548407649113217171456) qz29) 226375608064910080 72057594037927936 Bool.false 1040214 1048576 46 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q2 153246493 524288 226375608064910080 72057594037927936 46 9548407649113217171456 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1040214 1048576 9548407649113217171456 75557863725914323419136 271382067 2147483648 280911 280636 (ep229 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep231 := BSN.sin_dyadic_bound_f 271382067 2147483648 1 0 1048576 280911 0 1 1 0 1 1 132158 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 271382067) qz287 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 271382067) qz288 0 0 rfl) rfl rfl

noncomputable def ep232 := @Enclosure.Real.IsNear.sin_image qz53 qz334 Bool.false 153246493 524288 55 65536 Bool.true 132158 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz53 Bool.false 329094338308907379579 1125899906842624000 14703500006189497139 17539750000000000000000 153246493 524288 55 65536 (ep227 rfl) rfl) (Enclosure.sfrac_false_div 153246493 524288) (BSN.sin_reduce2 qz334 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9548407649113217171456) qz29) 226375608064910080 72057594037927936 Bool.false 132158 1048576 46 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q2 153246493 524288 226375608064910080 72057594037927936 46 9548407649113217171456 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 132158 1048576 9548407649113217171456 75557863725914323419136 271382067 2147483648 280911 280636 (ep231 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz335 := (@Enclosure.Real.IsNear.recentre' qz52 Bool.false 302697 1048576 1 1048576 302697 1048576 1 1048576 (ep225 rfl rfl) rfl)

noncomputable def ep233 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz52 (Real.cos qz53)) (@HMul.hMul Real Real Real qz0 qz52 (@Neg.neg Real Real.instNeg (Real.sin qz53))) Bool.true 157434828579 549755813888 9460115803605 38570318146568192 Bool.false 20001915063 549755813888 9428261653153 38570318146568192 (@Enclosure.Real.IsNear.mulLit_ft qz52 (Real.cos qz53) 302697 1048576 1 1048576 520107 524288 3891513 4597940224 157434828579 549755813888 9460115803605 38570318146568192 qz335 (@Enclosure.Real.IsNear.recentre' (Real.cos qz53) Bool.true 1040214 1048576 7783026 9195880448 520107 524288 3891513 4597940224 (ep230 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz52 (@Neg.neg Real Real.instNeg (Real.sin qz53)) 302697 1048576 1 1048576 66079 524288 3891513 4597940224 20001915063 549755813888 9428261653153 38570318146568192 qz335 (@Enclosure.Real.IsNear.neg (Real.sin qz53) Bool.true 66079 524288 3891513 4597940224 (@Enclosure.Real.IsNear.recentre' (Real.sin qz53) Bool.true 132158 1048576 7783026 9195880448 66079 524288 3891513 4597940224 (ep232 rfl rfl) rfl)) rfl)

noncomputable def ep234 := @ep172 157434828579 549755813888 9460115803605 38570318146568192 Bool.false 20001915063 549755813888 9428261653153 38570318146568192 Bool.false 1183240942274538511532032 2152302735839 1099511627776 301759566546267 77140636293136384 Bool.false 12467087825686887399424 2834687581 68719476736 150707324628405 38570318146568192 (ep173 (BSN.head_sum_c_succ qz5 11 12 rfl rfl) (ep223 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep224 ep233) rfl rfl

noncomputable abbrev qz336 := (@Nat.cast Real Real.instNatCast 13)

noncomputable abbrev qz54 := (@Inv.inv Real Real.instInv (Real.sqrt qz336))

noncomputable abbrev qz547 := (Real.log (Enclosure.sfrac Bool.false 13 1))

noncomputable abbrev qz55 := (@HMul.hMul Real Real Real qz267 qz284 qz547)

noncomputable def ep235 := @Enclosure.Complex.IsNear.of_eq qz42 (Complex.mk (@HMul.hMul Real Real Real qz0 qz54 (Real.cos qz55)) (@HMul.hMul Real Real Real qz0 qz54 (@Neg.neg Real Real.instNeg (Real.sin qz55)))) Bool.false 75718385457 274877906944 4545248033929 19285159073284096 Bool.true 17762596371 549755813888 9058248114939 38570318146568192 (BSN.cpow_neg_s_mk qz13 117628 1000 13 qz14 rfl)

noncomputable abbrev qz337 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13) qz15)

noncomputable def ep236 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz336) 3780695 1048576 1 1048576 145411 145412 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz336) (Real.sqrt qz337) Bool.false 3780695 1048576 1 1048576 (BSN.sqrt_natCast_div_one 13) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz337) Bool.false 3780695 1048576 1 1048576 3780695 1048576 1 1048576 (BSN.sqrt_enclosure 13 1 1890347 1890348 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep237 := BSN.log_dyadic_bound 5 21 5 4 35742602096145 524288 140318 699352521000 41015625 254545 26 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 5) (BSN.artanhQ 21) 0 4 699352521000 35742602096145 41015625 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep238 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz547 117628 1000 0 1 11551497052968677 4503599627370496 500000000210477 70159000000000000000 339694873836649884539 1125899906842624000 14703500006189497139 17539750000000000000000 qz17 (BSN.isNear_log_sfrac 13 1 11551497052968677 4503599627370496 500000000210477 70159000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz337) Bool.false 48450490295254733815808 18889465931478580854784 1000000000420954 140318000000000000000 11551497052968677 4503599627370496 500000000210477 70159000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 254545 524288 24973259072661432 36028797018963968 140318 1000000000000000 rfl rfl rfl rfl (ep237 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep239 := nat_lit 3952855454123718048263098785327376

noncomputable def ep240 := BSN.cos_dyadic_bound_f 250742374 2147483648 2 1 1048576 280911 ep239 ep77 ep239 ep239 ep78 ep239 1041436 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 250742374) qz292 0 1 ep239 ep77 ep239 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 250742374) qz293 0 1 ep239 ep78 ep239 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz338 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4943211) (@Nat.cast Real Real.instNatCast 16384))

noncomputable def ep241 := @Enclosure.Real.IsNear.cos_image qz55 qz338 Bool.false 4943211 16384 55 65536 Bool.false 1041436 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz55 Bool.false 339694873836649884539 1125899906842624000 14703500006189497139 17539750000000000000000 4943211 16384 55 65536 (ep238 rfl) rfl) (Enclosure.sfrac_false_div 4943211 16384) (BSN.cos_reduce0 qz338 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 275694156826124746752) (@Nat.cast Real Real.instNatCast 2361183241434822606848)) 226375608064910080 72057594037927936 Bool.false 1041436 1048576 48 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q0 4943211 16384 226375608064910080 72057594037927936 48 275694156826124746752 2361183241434822606848 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1041436 1048576 275694156826124746752 2361183241434822606848 250742374 2147483648 280911 280636 (ep240 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep242 := BSN.sin_dyadic_bound_f 250742374 2147483648 1 0 1048576 280911 0 1 1 0 1 1 122154 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 250742374) qz287 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 250742374) qz288 0 0 rfl) rfl rfl

noncomputable def ep243 := @Enclosure.Real.IsNear.sin_image qz55 qz338 Bool.false 4943211 16384 55 65536 Bool.false 122154 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz55 Bool.false 339694873836649884539 1125899906842624000 14703500006189497139 17539750000000000000000 4943211 16384 55 65536 (ep238 rfl) rfl) (Enclosure.sfrac_false_div 4943211 16384) (BSN.sin_reduce0 qz338 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 275694156826124746752) (@Nat.cast Real Real.instNatCast 2361183241434822606848)) 226375608064910080 72057594037927936 Bool.false 122154 1048576 48 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q0 4943211 16384 226375608064910080 72057594037927936 48 275694156826124746752 2361183241434822606848 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 122154 1048576 275694156826124746752 2361183241434822606848 250742374 2147483648 280911 280636 (ep242 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz339 := (@Enclosure.Real.IsNear.recentre' qz54 Bool.false 290823 1048576 1 1048576 290823 1048576 1 1048576 (ep236 rfl rfl) rfl)

noncomputable def ep244 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz54 (Real.cos qz55)) (@HMul.hMul Real Real Real qz0 qz54 (@Neg.neg Real Real.instNeg (Real.sin qz55))) Bool.false 75718385457 274877906944 4545248033929 19285159073284096 Bool.true 17762596371 549755813888 9058248114939 38570318146568192 (@Enclosure.Real.IsNear.mulLit_ff qz54 (Real.cos qz55) 290823 1048576 1 1048576 260359 262144 3891513 4597940224 75718385457 274877906944 4545248033929 19285159073284096 qz339 (@Enclosure.Real.IsNear.recentre' (Real.cos qz55) Bool.false 1041436 1048576 7783026 9195880448 260359 262144 3891513 4597940224 (ep241 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz54 (@Neg.neg Real Real.instNeg (Real.sin qz55)) 290823 1048576 1 1048576 61077 524288 3891513 4597940224 17762596371 549755813888 9058248114939 38570318146568192 qz339 (@Enclosure.Real.IsNear.neg (Real.sin qz55) Bool.false 61077 524288 3891513 4597940224 (@Enclosure.Real.IsNear.recentre' (Real.sin qz55) Bool.false 122154 1048576 7783026 9195880448 61077 524288 3891513 4597940224 (ep243 rfl rfl) rfl)) rfl)

noncomputable def ep245 := @ep170 75718385457 274877906944 4545248033929 19285159073284096 Bool.true 17762596371 549755813888 9058248114939 38570318146568192 Bool.false 674873716383665931419648 2455176277667 1099511627776 319940558681983 77140636293136384 Bool.false 337749650122968399872 4914904277 549755813888 9985348296459 2410644884160512 (ep171 (BSN.head_sum_c_succ qz5 12 13 rfl rfl) (ep234 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep235 ep244) rfl rfl

noncomputable abbrev qz340 := (@Nat.cast Real Real.instNatCast 14)

noncomputable abbrev qz56 := (@Inv.inv Real Real.instInv (Real.sqrt qz340))

noncomputable abbrev qz548 := (Real.log (Enclosure.sfrac Bool.false 14 1))

noncomputable abbrev qz57 := (@HMul.hMul Real Real Real qz267 qz284 qz548)

noncomputable def ep246 := @Enclosure.Complex.IsNear.of_eq qz41 (Complex.mk (@HMul.hMul Real Real Real qz0 qz56 (Real.cos qz57)) (@HMul.hMul Real Real Real qz0 qz56 (@Neg.neg Real Real.instNeg (Real.sin qz57)))) Bool.true 122020884873 549755813888 8755133353725 38570318146568192 Bool.true 81845808879 549755813888 8745075499803 38570318146568192 (BSN.cpow_neg_s_mk qz13 117628 1000 14 qz14 rfl)

noncomputable abbrev qz341 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14) qz15)

noncomputable def ep247 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz340) 3923413 1048576 1 1048576 140121 140122 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz340) (Real.sqrt qz341) Bool.false 3923413 1048576 1 1048576 (BSN.sqrt_natCast_div_one 14) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz341) Bool.false 3923413 1048576 1 1048576 3923413 1048576 1 1048576 (BSN.sqrt_enclosure 14 1 1961706 1961707 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep248 := BSN.log_dyadic_bound 6 22 5 4 51857700491520 524288 140318 1346332575744 176359680 293399 28 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 6) (BSN.artanhQ 22) 0 4 1346332575744 51857700491520 176359680 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep249 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz548 117628 1000 0 1 11885250371606245 4503599627370496 500000000210477 70159000000000000000 69901911535564969343 225179981368524800 14703500006189497139 17539750000000000000000 qz17 (BSN.isNear_log_sfrac 14 1 11885250371606245 4503599627370496 500000000210477 70159000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz341) Bool.false 49850353174629559828480 18889465931478580854784 1000000000420954 140318000000000000000 11885250371606245 4503599627370496 500000000210477 70159000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 293399 524288 24973259072661432 36028797018963968 140318 1000000000000000 rfl rfl rfl rfl (ep248 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep250 := nat_lit 1261840572538153685312162804802064048626574365258430855401688546290455715840000

noncomputable def ep251 := nat_lit 384717210962403766547790714588780321258527374300688478298047352857600000000

noncomputable def ep252 := nat_lit 3304197671639320522100301399038928768739942864689879697087177925522757427200000

noncomputable def ep253 := BSN.sin_dyadic_bound_f 2104469820 2147483648 3 2 1048576 280911 ep250 ep59 ep251 ep252 ep62 ep251 870822 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2104469820) qz287 0 2 ep250 ep59 ep251 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2104469820) qz288 0 2 ep252 ep62 ep251 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz342 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 325506141) qz32)

noncomputable def ep254 := @Enclosure.Real.IsNear.cos_image qz57 qz342 Bool.false 325506141 1048576 55 65536 Bool.true 870822 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz57 Bool.false 69901911535564969343 225179981368524800 14703500006189497139 17539750000000000000000 325506141 1048576 55 65536 (ep249 rfl) rfl) (Enclosure.sfrac_false_div 325506141 1048576) (BSN.cos_reduce1 qz342 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 148088898413643213832192) qz33) 226375608064910080 72057594037927936 Bool.false 870822 1048576 49 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q1 325506141 1048576 226375608064910080 72057594037927936 49 148088898413643213832192 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 870822 1048576 148088898413643213832192 151115727451828646838272 2104469820 2147483648 280911 280636 (ep253 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep255 := nat_lit 701193525726068671291889465207630596046433992865484114546848324540412108800000

noncomputable def ep256 := nat_lit 2102811142756281206342572814193714227496784923847850966683948878915521126400000

noncomputable def ep257 := BSN.cos_dyadic_bound_f 2104469820 2147483648 3 2 1048576 280911 ep255 ep66 ep251 ep256 ep68 ep251 584106 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2104469820) qz292 0 2 ep255 ep66 ep251 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2104469820) qz293 0 2 ep256 ep68 ep251 rfl rfl rfl rfl) rfl rfl

noncomputable def ep258 := @Enclosure.Real.IsNear.sin_image qz57 qz342 Bool.false 325506141 1048576 55 65536 Bool.false 584106 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz57 Bool.false 69901911535564969343 225179981368524800 14703500006189497139 17539750000000000000000 325506141 1048576 55 65536 (ep249 rfl) rfl) (Enclosure.sfrac_false_div 325506141 1048576) (BSN.sin_reduce1 qz342 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 148088898413643213832192) qz33) 226375608064910080 72057594037927936 Bool.false 584106 1048576 49 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q1 325506141 1048576 226375608064910080 72057594037927936 49 148088898413643213832192 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 584106 1048576 148088898413643213832192 151115727451828646838272 2104469820 2147483648 280911 280636 (ep257 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz343 := (@Enclosure.Real.IsNear.recentre' qz56 Bool.false 280243 1048576 1 1048576 280243 1048576 1 1048576 (ep247 rfl rfl) rfl)

noncomputable def ep259 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz56 (Real.cos qz57)) (@HMul.hMul Real Real Real qz0 qz56 (@Neg.neg Real Real.instNeg (Real.sin qz57))) Bool.true 122020884873 549755813888 8755133353725 38570318146568192 Bool.true 81845808879 549755813888 8745075499803 38570318146568192 (@Enclosure.Real.IsNear.mulLit_ft qz56 (Real.cos qz57) 280243 1048576 1 1048576 435411 524288 3891513 4597940224 122020884873 549755813888 8755133353725 38570318146568192 qz343 (@Enclosure.Real.IsNear.recentre' (Real.cos qz57) Bool.true 870822 1048576 7783026 9195880448 435411 524288 3891513 4597940224 (ep254 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz56 (@Neg.neg Real Real.instNeg (Real.sin qz57)) 280243 1048576 1 1048576 292053 524288 3891513 4597940224 81845808879 549755813888 8745075499803 38570318146568192 qz343 (@Enclosure.Real.IsNear.neg (Real.sin qz57) Bool.false 292053 524288 3891513 4597940224 (@Enclosure.Real.IsNear.recentre' (Real.sin qz57) Bool.false 584106 1048576 7783026 9195880448 292053 524288 3891513 4597940224 (ep258 rfl rfl) rfl)) rfl)

noncomputable def ep260 := @ep167 122020884873 549755813888 8755133353725 38570318146568192 Bool.true 81845808879 549755813888 8745075499803 38570318146568192 Bool.false ep168 2211134507921 1099511627776 337450825389433 77140636293136384 Bool.true 42293212072612594712576 38465452301 274877906944 168510648243147 38570318146568192 (ep169 (BSN.head_sum_c_succ qz5 13 14 rfl rfl) (ep245 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep246 ep259) rfl rfl

noncomputable abbrev qz344 := (@Nat.cast Real Real.instNatCast 15)

noncomputable abbrev qz58 := (@Inv.inv Real Real.instInv (Real.sqrt qz344))

noncomputable abbrev qz549 := (Real.log (Enclosure.sfrac Bool.false 15 1))

noncomputable abbrev qz59 := (@HMul.hMul Real Real Real qz267 qz284 qz549)

noncomputable def ep261 := @Enclosure.Complex.IsNear.of_eq qz40 (Complex.mk (@HMul.hMul Real Real Real qz0 qz58 (Real.cos qz59)) (@HMul.hMul Real Real Real qz0 qz58 (@Neg.neg Real Real.instNeg (Real.sin qz59)))) Bool.true 91817207553 1099511627776 993019378499 4537684487831552 Bool.false 268634364279 1099511627776 995714664421 4537684487831552 (BSN.cpow_neg_s_mk qz13 117628 1000 15 qz14 rfl)

noncomputable abbrev qz345 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 15) qz15)

noncomputable def ep262 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz344) 4061117 1048576 1 1048576 135370 135371 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz344) (Real.sqrt qz345) Bool.false 4061117 1048576 1 1048576 (BSN.sqrt_natCast_div_one 15) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz345) Bool.false 4061117 1048576 1 1048576 4061117 1048576 1 1048576 (BSN.sqrt_enclosure 15 1 2030558 2030559 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep263 := BSN.log_dyadic_bound 7 23 6 5 430628584065881355 524288 140318 14087658153505881 266939110305 329571 30 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 7) (BSN.artanhQ 23) 0 5 14087658153505881 430628584065881355 266939110305 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep264 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz549 117628 1000 0 1 12195965485668069 4503599627370496 500000000210477 70159000000000000000 358646757037040905083 1125899906842624000 14703500006189497139 17539750000000000000000 qz17 (BSN.isNear_log_sfrac 15 1 12195965485668069 4503599627370496 500000000210477 70159000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz345) Bool.false 51153586820399524478976 18889465931478580854784 1000000000420954 140318000000000000000 12195965485668069 4503599627370496 500000000210477 70159000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 329571 524288 24973259072661432 36028797018963968 140318 1000000000000000 rfl rfl rfl rfl (ep263 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep265 := nat_lit 1807511990962888835261858729359813451208765450952007701004312322221565299571841

noncomputable def ep266 := nat_lit 2551982428467859978270984612688831401420219232909258190724108472798400658561

noncomputable def ep267 := nat_lit 5417432008031730785829034218854062690823455914390204586631488749719099097398401

noncomputable def ep268 := BSN.cos_dyadic_bound_f 2665997329 2147483648 3 2 1048576 280911 ep265 ep66 ep266 ep267 ep68 ep266 339133 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2665997329) qz292 0 2 ep265 ep66 ep266 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2665997329) qz293 0 2 ep267 ep68 ep266 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz346 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 334015821) qz32)

noncomputable def ep269 := @Enclosure.Real.IsNear.cos_image qz59 qz346 Bool.false 334015821 1048576 55 65536 Bool.true 339133 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz59 Bool.false 358646757037040905083 1125899906842624000 14703500006189497139 17539750000000000000000 334015821 1048576 55 65536 (ep264 rfl) rfl) (Enclosure.sfrac_false_div 334015821 1048576) (BSN.cos_reduce2 qz346 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 187602884067636650442752) qz33) 226375608064910080 72057594037927936 Bool.false 339133 1048576 50 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q2 334015821 1048576 226375608064910080 72057594037927936 50 187602884067636650442752 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 339133 1048576 187602884067636650442752 151115727451828646838272 2665997329 2147483648 280911 280636 (ep268 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep270 := nat_lit 3251479997790425615488728925157513147054641636327286455255182893220578818702465

noncomputable def ep271 := nat_lit 8511649165519309600600898924134847753350333454480087631454782830431270924106881

noncomputable def ep272 := BSN.sin_dyadic_bound_f 2665997329 2147483648 3 2 1048576 280911 ep270 ep59 ep266 ep271 ep62 ep266 992219 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2665997329) qz287 0 2 ep270 ep59 ep266 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2665997329) qz288 0 2 ep271 ep62 ep266 rfl rfl rfl rfl) rfl rfl

noncomputable def ep273 := @Enclosure.Real.IsNear.sin_image qz59 qz346 Bool.false 334015821 1048576 55 65536 Bool.true 992219 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz59 Bool.false 358646757037040905083 1125899906842624000 14703500006189497139 17539750000000000000000 334015821 1048576 55 65536 (ep264 rfl) rfl) (Enclosure.sfrac_false_div 334015821 1048576) (BSN.sin_reduce2 qz346 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 187602884067636650442752) qz33) 226375608064910080 72057594037927936 Bool.false 992219 1048576 50 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q2 334015821 1048576 226375608064910080 72057594037927936 50 187602884067636650442752 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 992219 1048576 187602884067636650442752 151115727451828646838272 2665997329 2147483648 280911 280636 (ep272 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz347 := (@Enclosure.Real.IsNear.recentre' qz58 Bool.false 270741 1048576 1 1048576 270741 1048576 1 1048576 (ep262 rfl rfl) rfl)

noncomputable def ep274 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz58 (Real.cos qz59)) (@HMul.hMul Real Real Real qz0 qz58 (@Neg.neg Real Real.instNeg (Real.sin qz59))) Bool.true 91817207553 1099511627776 993019378499 4537684487831552 Bool.false 268634364279 1099511627776 995714664421 4537684487831552 (@Enclosure.Real.IsNear.mulLit_ft qz58 (Real.cos qz59) 270741 1048576 1 1048576 339133 1048576 3891513 4597940224 91817207553 1099511627776 993019378499 4537684487831552 qz347 (@Enclosure.Real.IsNear.recentre' (Real.cos qz59) Bool.true 339133 1048576 7783026 9195880448 339133 1048576 3891513 4597940224 (ep269 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz58 (@Neg.neg Real Real.instNeg (Real.sin qz59)) 270741 1048576 1 1048576 992219 1048576 3891513 4597940224 268634364279 1099511627776 995714664421 4537684487831552 qz347 (@Enclosure.Real.IsNear.neg (Real.sin qz59) Bool.true 992219 1048576 3891513 4597940224 (@Enclosure.Real.IsNear.recentre' (Real.sin qz59) Bool.true 992219 1048576 7783026 9195880448 992219 1048576 3891513 4597940224 (ep273 rfl rfl) rfl)) rfl)

noncomputable def ep275 := @ep164 91817207553 1099511627776 993019378499 4537684487831552 Bool.false 268634364279 1099511627776 995714664421 4537684487831552 Bool.false ep165 132457331273 68719476736 88583038705979 19285159073284096 Bool.false 31548439713630964940800 114772555075 1099511627776 353948445781451 77140636293136384 (ep166 (BSN.head_sum_c_succ qz5 14 15 rfl rfl) (ep260 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep261 ep274) rfl rfl

noncomputable abbrev qz348 := (@Nat.cast Real Real.instNatCast 16)

noncomputable abbrev qz60 := (@Inv.inv Real Real.instInv (Real.sqrt qz348))

noncomputable abbrev qz550 := (Real.log (Enclosure.sfrac Bool.false 16 1))

noncomputable abbrev qz61 := (@HMul.hMul Real Real Real qz267 qz284 qz550)

noncomputable def ep276 := @Enclosure.Complex.IsNear.of_eq qz39 (Complex.mk (@HMul.hMul Real Real Real qz0 qz60 (Real.cos qz61)) (@HMul.hMul Real Real Real qz0 qz60 (@Neg.neg Real Real.instNeg (Real.sin qz61)))) Bool.false 228165859341 1099511627776 16383254023485 77140636293136384 Bool.false 76644583911 549755813888 8181607148919 38570318146568192 (BSN.cpow_neg_s_mk qz13 117628 1000 16 qz14 rfl)

noncomputable abbrev qz349 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16) qz15)

noncomputable def ep277 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz348) 4194305 1048576 1 1048576 131071 131072 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz348) (Real.sqrt qz349) Bool.false 4194305 1048576 1 1048576 (BSN.sqrt_natCast_div_one 16) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz349) Bool.false 4194305 1048576 1 1048576 4194305 1048576 1 1048576 (BSN.sqrt_enclosure 16 1 2097152 2097153 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep278 := BSN.log_dyadic_bound 0 32 1 0 1 524288 140318 0 1 0 32 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 32) 0 0 rfl) rfl rfl rfl

noncomputable def ep279 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz550 117628 1000 0 1 3121657384082679 1125899906842624 125000000070159 17539750000000000000 91798578693719341353 281474976710656000 3675875002063165713 4384937500000000000000 qz17 (BSN.isNear_log_sfrac 16 1 3121657384082679 1125899906842624 125000000070159 17539750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz349) Bool.false 52372720210750067441664 18889465931478580854784 1000000000561272 140318000000000000000 3121657384082679 1125899906842624 125000000070159 17539750000000000000 (BSN.log_rat_reduce_isNear 16 1 4 32 32 0 524288 24973259072661432 36028797018963968 140318 1000000000000000 rfl rfl rfl rfl (ep278 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep280 := nat_lit 1258011036497526700433422916025260975479154280894506368677952782522170021781760

noncomputable def ep281 := nat_lit 382386319878410965347708978587979298014994495468557365330182007094126059776

noncomputable def ep282 := nat_lit 3294171708213719169096020870291302969296236935064377110803151278594197662474496

noncomputable def ep283 := BSN.sin_dyadic_bound_f 2102871782 2147483648 3 2 1048576 280911 ep280 ep59 ep281 ep282 ep62 ep281 870387 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2102871782) qz287 0 2 ep280 ep59 ep281 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2102871782) qz288 0 2 ep282 ep62 ep281 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz350 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 170988177) qz27)

noncomputable def ep284 := @Enclosure.Real.IsNear.cos_image qz61 qz350 Bool.false 170988177 524288 55 65536 Bool.false 870387 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz61 Bool.false 91798578693719341353 281474976710656000 3675875002063165713 4384937500000000000000 170988177 524288 55 65536 (ep279 rfl) rfl) (Enclosure.sfrac_false_div 170988177 524288) (BSN.cos_reduce3 qz350 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 73988223267669031256064) qz29) 226375608064910080 72057594037927936 Bool.false 870387 1048576 51 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q3 170988177 524288 226375608064910080 72057594037927936 51 73988223267669031256064 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 870387 1048576 73988223267669031256064 75557863725914323419136 2102871782 2147483648 280911 280636 (ep283 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep285 := nat_lit 699064969751905238447611712893406310509759042494934008094564960071025179238656

noncomputable def ep286 := nat_lit 2096430136615958893412139720723042972933247138493864909553034516198887285596416

noncomputable def ep287 := BSN.cos_dyadic_bound_f 2102871782 2147483648 3 2 1048576 280911 ep285 ep66 ep281 ep286 ep68 ep281 584754 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2102871782) qz292 0 2 ep285 ep66 ep281 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2102871782) qz293 0 2 ep286 ep68 ep281 rfl rfl rfl rfl) rfl rfl

noncomputable def ep288 := @Enclosure.Real.IsNear.sin_image qz61 qz350 Bool.false 170988177 524288 55 65536 Bool.true 584754 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz61 Bool.false 91798578693719341353 281474976710656000 3675875002063165713 4384937500000000000000 170988177 524288 55 65536 (ep279 rfl) rfl) (Enclosure.sfrac_false_div 170988177 524288) (BSN.sin_reduce3 qz350 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 73988223267669031256064) qz29) 226375608064910080 72057594037927936 Bool.false 584754 1048576 51 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q3 170988177 524288 226375608064910080 72057594037927936 51 73988223267669031256064 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 584754 1048576 73988223267669031256064 75557863725914323419136 2102871782 2147483648 280911 280636 (ep287 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz351 := (@Enclosure.Real.IsNear.recentre' qz60 Bool.false 262143 1048576 1 1048576 262143 1048576 1 1048576 (ep277 rfl rfl) rfl)

noncomputable def ep289 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz60 (Real.cos qz61)) (@HMul.hMul Real Real Real qz0 qz60 (@Neg.neg Real Real.instNeg (Real.sin qz61))) Bool.false 228165859341 1099511627776 16383254023485 77140636293136384 Bool.false 76644583911 549755813888 8181607148919 38570318146568192 (@Enclosure.Real.IsNear.mulLit_ff qz60 (Real.cos qz61) 262143 1048576 1 1048576 870387 1048576 3891513 4597940224 228165859341 1099511627776 16383254023485 77140636293136384 qz351 (@Enclosure.Real.IsNear.recentre' (Real.cos qz61) Bool.false 870387 1048576 7783026 9195880448 870387 1048576 3891513 4597940224 (ep284 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz60 (@Neg.neg Real Real.instNeg (Real.sin qz61)) 262143 1048576 1 1048576 292377 524288 3891513 4597940224 76644583911 549755813888 8181607148919 38570318146568192 qz351 (@Enclosure.Real.IsNear.neg (Real.sin qz61) Bool.true 292377 524288 3891513 4597940224 (@Enclosure.Real.IsNear.recentre' (Real.sin qz61) Bool.true 584754 1048576 7783026 9195880448 292377 524288 3891513 4597940224 (ep288 rfl rfl) rfl)) rfl)

noncomputable def ep290 := @ep162 228165859341 1099511627776 16383254023485 77140636293136384 Bool.false 76644583911 549755813888 8181607148919 38570318146568192 Bool.false 161317814381774398029824 2347483159709 1099511627776 370715408847401 77140636293136384 Bool.false 147368490643459760193536 268061722897 1099511627776 370311660079289 77140636293136384 (ep163 (BSN.head_sum_c_succ qz5 15 16 rfl rfl) (ep275 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep276 ep289) rfl rfl

theorem EMRow38.d7 : Enclosure.Complex.IsNear qz38 Bool.false 2347483159709 1099511627776 370715408847401 77140636293136384 Bool.false 268061722897 1099511627776 370311660079289 77140636293136384 := ep161 (BSN.head_sum_c_succ qz5 16 17 rfl rfl) (ep290 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

theorem EMRow38.d8 : @Eq Nat (BSN.factNat (Nat.mul 2 1)) 2 := @Eq.refl Nat 2

theorem EMRow38.d9 : @Eq Nat (Nat.pow 24 1) 24 := @Eq.refl Nat 24

noncomputable def ep291 := nat_lit 11141233668273411513963161202811

noncomputable def ep292 := nat_lit 3589314642377761097196660326400

noncomputable def ep293 := nat_lit 163117084025766498287693396258368509251

noncomputable def ep294 := nat_lit 22084538291317290363081914358744219648000

noncomputable abbrev qz581 := (@instHMul Complex Complex.instMul)

noncomputable abbrev qz551 := qz581

noncomputable abbrev qz352 := qz551

noncomputable abbrev qz62 := qz352

noncomputable abbrev qz552 := (@instHSub Complex Complex.instSub)

noncomputable abbrev qz353 := qz552

noncomputable abbrev qz63 := qz353

noncomputable abbrev qz582 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (4 : Complex))

noncomputable abbrev qz583 := (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid))

noncomputable abbrev qz553 := (@HAdd.hAdd Complex Complex Complex qz579 (@HAdd.hAdd Complex Complex Complex qz579 qz582 (@HMul.hMul Complex Complex Complex qz581 Complex.I (@HDiv.hDiv Complex Complex Complex qz583 (↑qz580) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz354 := qz553

noncomputable abbrev qz64 := (Complex.Stirling.logGammaStirling 1 qz354)

noncomputable abbrev qz554 := (@HAdd.hAdd Complex Complex Complex qz579 qz582 (@HMul.hMul Complex Complex Complex qz581 Complex.I (@HDiv.hDiv Complex Complex Complex qz583 (↑qz580) (2 : Complex))))

noncomputable abbrev qz355 := qz554

noncomputable abbrev qz65 := qz355

noncomputable abbrev qz66 := (@HMul.hMul Real Real Real qz267 (@HDiv.hDiv Real Real Real qz270 qz284 (2 : Real)) (Real.log Real.pi))

noncomputable abbrev qz356 := (@instHSub Real Real.instSub)

noncomputable def ep295 := Complex.re (@HMul.hMul Complex Complex Complex qz62 (Complex.exp (@HMul.hMul Complex Complex Complex qz62 Complex.I ↑(@HSub.hSub Real Real Real qz356 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))))) qz66))) (zetaApproximant qz5 1 24))

noncomputable def ep296 := @Enclosure.Real.IsNear.of_eq ep295 (@HSub.hSub Real Real Real qz356 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz356 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))))) qz66)) (Complex.re (zetaApproximant qz5 1 24))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz356 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))))) qz66)) (Complex.im (zetaApproximant qz5 1 24))))

noncomputable def ep297 := nat_lit 371379578742686661698092942807

noncomputable def ep298 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz356 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))))) qz66)) (Complex.re (zetaApproximant qz5 1 24))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz356 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))))) qz66)) (Complex.im (zetaApproximant qz5 1 24))) ep297

noncomputable def ep299 := nat_lit 119643821412592036573222010880

noncomputable def ep300 := nat_lit 8661665572312826872029007483594453411

noncomputable def ep301 := nat_lit 1177842042203588819364368765799691714560

noncomputable def ep302 := nat_lit 153694007188336979627081399

noncomputable def ep303 := nat_lit 2843418179603977748598023763890031179

noncomputable def ep304 := nat_lit 88338153165269161452327657434976878592000

noncomputable def ep305 := nat_lit 1332979771322861715367023287766810896166707876112920928583680

noncomputable def ep306 := @Enclosure.Real.IsNear.mulLit_ff (Real.cos (@HSub.hSub Real Real Real qz356 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))))) qz66)) (Complex.re (zetaApproximant qz5 1 24)) 1048575 1048576 3222691

noncomputable def ep307 := nat_lit 26563162773956559738079747

noncomputable def ep308 := nat_lit 8557592969841387503616000

noncomputable def ep309 := nat_lit 578578787067720062676772333

noncomputable def ep310 := nat_lit 92368025410938754748645376000

noncomputable def ep311 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz356 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))))) qz66)) Bool.false 1048575 1048576 6445382

noncomputable abbrev qz357 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 118591747) qz32)

noncomputable def ep312 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz356 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))))) qz66) qz357 Bool.false 118591747 1048576 45

noncomputable def ep313 := nat_lit 9449025838796525585381213

noncomputable def ep314 := nat_lit 27587641344000000000000000000

noncomputable def ep315 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz356 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))))) qz66) Bool.false 101869535062122567031 900719925474099200 ep313 ep314

noncomputable def ep316 := nat_lit 3259528699796525585381213

noncomputable def ep317 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))))) qz66 812557598180345408339 4503599627370496000 ep316 ep314 2206142547 32768000

noncomputable def ep318 := nat_lit 16690304624578161382359040000

noncomputable def ep319 := nat_lit 2014967580366124667527461

noncomputable def ep320 := nat_lit 9195880448000000000000000000

noncomputable def ep321 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz63 qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 416513275324499133049 4503599627370496000 ep319 ep320 Bool.false 812557598180345408339 4503599627370496000

noncomputable def ep322 := nat_lit 1982199580264969982599461

noncomputable def ep323 := nat_lit 3062920699768937944037213

noncomputable def ep324 := @Enclosure.Complex.IsNear.subLitP qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 379813467069302304049 4503599627370496000 ep322 ep320 Bool.false 826591230553874544339 4503599627370496000 ep323

noncomputable def ep325 := nat_lit 1875809031546279102015925403521122304

noncomputable def ep326 := nat_lit 228714631023879299976381771372560384

noncomputable abbrev qz584 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex))

noncomputable abbrev qz555 := qz584

noncomputable abbrev qz358 := (@HSub.hSub Complex Complex Complex qz552 qz553 qz555)

noncomputable abbrev qz359 := (Complex.log qz553)

noncomputable abbrev qz67 := (@HSub.hSub Complex Complex Complex qz353 (@HMul.hMul Complex Complex Complex qz352 qz358 qz359) qz354)

noncomputable abbrev qz360 := qz555

noncomputable abbrev qz68 := (@HMul.hMul Complex Complex Complex qz352 qz360 ↑(Real.log qz271))

noncomputable abbrev qz556 := qz583

noncomputable abbrev qz361 := qz556

noncomputable abbrev qz69 := qz361

noncomputable abbrev qz70 := (@instHMul Nat instMulNat)

noncomputable abbrev qz557 := (@instHPow Complex Int (@ZPow.toPow Complex (@DivInvMonoid.toZPow Complex Complex.instDivInvMonoid)))

noncomputable abbrev qz362 := qz557

noncomputable abbrev qz71 := qz362

noncomputable abbrev qz72 := qz354

noncomputable abbrev qz363 := (@OfNat.ofNat Int 1 (@instOfNat 1))

noncomputable abbrev qz73 := qz363

noncomputable abbrev qz364 := (@OfNat.ofNat Int 2 (@instOfNat 2))

noncomputable abbrev qz74 := qz364

noncomputable abbrev qz365 := (@instHSub Int Int.instSub)

noncomputable abbrev qz366 := (@instHMul Int Int.instMul)

noncomputable def ep327 := @Enclosure.Complex.IsNear.of_eq qz64 (@HAdd.hAdd Complex Complex Complex qz4 (@HAdd.hAdd Complex Complex Complex qz4 qz67 qz68) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz63 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz71 qz72 (@HSub.hSub Int Int Int qz365 qz73 (@HMul.hMul Int Int Int qz366 qz74 (@Nat.cast Int instNatCastInt k)))))) Bool.true 379813467069302304049

noncomputable def ep328 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz4 qz67 qz68) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz63 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz71 qz72 (@HSub.hSub Int Int Int qz365 qz73 (@HMul.hMul Int Int Int qz366 qz74 (@Nat.cast Int instNatCastInt k))))) Bool.true 379813710830585376049 4503599627370496000

noncomputable def ep329 := nat_lit 13050291357144210891423227052032

noncomputable def ep330 := nat_lit 3550182302389287134022906937344000

noncomputable def ep331 := @ep328 60491906047330737477 280636000000000000000000 Bool.false 826597602365475698387 4503599627370496000 30426757901391453 274058593750000000000 Bool.false 1859751 34359738368 3 34359738368 Bool.true 6076633073 4294967296000 29407 12884901888000 Bool.true ep329 379813467069302304049 4503599627370496000 ep322 ep320 Bool.false ep330

noncomputable def ep332 := @Enclosure.Complex.IsNear.addLitP qz67 qz68 Bool.true 383952238237795872049 4503599627370496000 1865281250342305761 8769875000000000000000

noncomputable def ep333 := nat_lit 49782942705986486409494528

noncomputable def ep334 := @ep332 Bool.false 826597602365475698387 4503599627370496000 30426757901391453 274058593750000000000 Bool.false 120447 131072 3 1048576 Bool.false 0 1 0 1 Bool.true ep333 379813710830585376049 4503599627370496000 60491906047330737477 280636000000000000000000 Bool.false 826597602365475698387 826597602365475698387 4503599627370496000

noncomputable abbrev qz75 := (@HMul.hMul Complex Complex Complex qz352 qz358 qz359)

noncomputable def ep335 := @Enclosure.Complex.IsNear.subLitP qz75 qz72 Bool.true 373819139076212256049 4503599627370496000 1865281250342305761 8769875000000000000000 Bool.false 1091472310849644050131

noncomputable def ep336 := nat_lit 1535808952951183488196000

noncomputable def ep337 := nat_lit 3306390409461902793548000

noncomputable def ep338 := @ep335 4503599627370496000 30426757901391453 274058593750000000000 Bool.false 9000 4000 0 1 Bool.false 235256 4000 0 1 Bool.true ep336 383952238237795872049 4503599627370496000 1865281250342305761 8769875000000000000000 Bool.false ep337 826597602365475698387 4503599627370496000 30426757901391453 274058593750000000000

noncomputable abbrev qz76 := qz358

noncomputable abbrev qz77 := qz359

noncomputable def ep339 := @Enclosure.Complex.IsNear.mul qz76 qz77 Bool.true 373819139076212256049 4503599627370496000 1865281250342305761 8769875000000000000000 Bool.false 1091472310849644050131 4503599627370496000 30426757901391453

noncomputable abbrev qz78 := (Complex.re qz358)

noncomputable abbrev qz79 := (Complex.re qz359)

noncomputable abbrev qz80 := (Complex.im qz358)

noncomputable abbrev qz81 := (Complex.im qz359)

noncomputable def ep340 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz78 qz79) (@HMul.hMul Real Real Real qz0 qz80 qz81) 256937336114361931 36028797018963968 1750000005402243 561272000000000000000 25371019130656718589 281474976710656000

noncomputable def ep341 := nat_lit 841765867723794568333142614870065152

noncomputable def ep342 := @Enclosure.Real.IsNear.mulLit_ff qz78 qz79 7000 4000 0 1 36705333730623133 9007199254740992 250000000771749 140318000000000000000

noncomputable def ep343 := @Enclosure.Complex.IsNear.re_isNear qz76 Bool.false 7000 4000 0 1 Bool.false 235256 4000 0 1

noncomputable abbrev qz367 := (Enclosure.sfrac Bool.false 235256 4000)

noncomputable abbrev qz82 := qz367

noncomputable def ep344 := @Enclosure.Complex.IsNear.of_eq qz76 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz82) Bool.false 7000 4000 0 1 Bool.false 235256 4000 0

noncomputable abbrev qz368 := (Enclosure.sfrac Bool.false 9000 4000)

noncomputable abbrev qz83 := qz368

noncomputable abbrev qz369 := (Complex.log (Complex.mk qz83 qz82))

noncomputable def ep345 := @Enclosure.Complex.IsNear.of_eq qz77 qz369 Bool.false 36705333730623133 9007199254740992 250000000771749 140318000000000000000 Bool.false 862754416657827 562949953421312 500000000070159 140318000000000000000

noncomputable def ep346 := nat_lit 3459069744877859312544299509956199251601190753377157706484904115121392246381543698643025920

noncomputable def ep347 := nat_lit 79268541920322697702960323428826131945514254282386758290362393410129489196050729626763264

noncomputable def ep348 := nat_lit 7294927767333368300395402106415150053400352765210863431456816887969193315854587002880

noncomputable def ep349 := BSN.log_dyadic_bound 22658385536 88194385536 5 4 ep346 1048576 280636 ep347 ep348 551134 110852771072 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 22658385536) (BSN.artanhQ 88194385536) 0 4 ep347 ep346 ep348 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz84 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz370 := (Enclosure.Real.IsNear.const Bool.false 1 2)

noncomputable abbrev qz371 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable abbrev qz558 := (Real.log (Enclosure.sfrac Bool.false 55426385536 16000000))

noncomputable def ep350 := @Enclosure.Real.IsNear.mulLit_ff qz84 qz558 1 2 0 1 36705333730623133 4503599627370496 250000000771749 70159000000000000000 36705333730623133 9007199254740992 250000000771749 140318000000000000000 qz370 (BSN.isNear_log_sfrac 55426385536 16000000 36705333730623133 4503599627370496 250000000771749 70159000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 55426385536) qz371)) Bool.false 307906656175375058468864 37778931862957161709568 1000000003086996 280636000000000000000 36705333730623133 4503599627370496 250000000771749 70159000000000000000 (BSN.log_rat_reduce_isNear 55426385536 16000000 11 110852771072 65536000000 551134 1048576 24973259072661432 36028797018963968 280636 1000000000000000 rfl rfl rfl rfl (ep349 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep351 := BSN.arctan_dyadic_bound_f 9000 235256 1 0 1048576 280636 0 1 1 0 1 1 40094 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 235256) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 235256) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz85 := (@HMul.hMul Real Real Real qz267 (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz86 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 2) Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 qz370 BSN.pi_near_15 rfl)

noncomputable abbrev qz372 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 235256)))

noncomputable def ep352 := @Enclosure.Real.IsNear.subLit_ff_p qz85 qz372 884279719003555 562949953421312 1 2000000000000000 40094 1048576 1 280636 904663575201397604352 862754416657827 562949953421312 500000000070159 140318000000000000000 qz86 (ep351 rfl) rfl rfl

noncomputable abbrev qz373 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 235256) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep353 := @Enclosure.Complex.IsNear.re_isNear qz77 Bool.false 36705333730623133 9007199254740992 250000000771749 140318000000000000000 Bool.false 862754416657827 562949953421312 500000000070159 140318000000000000000 (ep345 (@congrArg Complex Complex qz72 (Complex.mk qz83 qz82) Complex.log (BSN.w_shift_mk qz13 Bool.false 117628 1000 2 qz14 rfl)) (@Enclosure.Complex.IsNear.of_parts qz369 Bool.false 36705333730623133 9007199254740992 250000000771749 140318000000000000000 Bool.false 862754416657827 562949953421312 500000000070159 140318000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz369) (@HMul.hMul Real Real Real qz0 qz84 qz558) Bool.false 36705333730623133 9007199254740992 250000000771749 140318000000000000000 (Enclosure.clog_re_eq 9000 235256 4000 55426385536 16000000 rfl rfl rfl) (ep350 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz369) qz373 Bool.false 862754416657827 562949953421312 500000000070159 140318000000000000000 (Enclosure.clog_im_eq 9000 235256 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz373 (@HSub.hSub Real Real Real qz356 qz85 qz372) Bool.false 862754416657827 562949953421312 500000000070159 140318000000000000000 (BSN.arctan_recip 235256 9000 rfl rfl) ep352))))

noncomputable def ep354 := @Enclosure.Real.IsNear.mulLit_ff qz80 qz81 235256 4000 0 1 862754416657827 562949953421312 500000000070159 140318000000000000000

noncomputable def ep355 := @Enclosure.Complex.IsNear.im_isNear qz76 Bool.false 7000 4000 0 1 Bool.false 235256 4000 0 1

noncomputable def ep356 := @Enclosure.Complex.IsNear.im_isNear qz77 Bool.false 36705333730623133 9007199254740992 250000000771749 140318000000000000000 Bool.false 862754416657827 562949953421312 500000000070159 140318000000000000000 (ep345 (@congrArg Complex Complex qz72 (Complex.mk qz83 qz82) Complex.log (BSN.w_shift_mk qz13 Bool.false 117628 1000 2 qz14 rfl)) (@Enclosure.Complex.IsNear.of_parts qz369 Bool.false 36705333730623133 9007199254740992 250000000771749 140318000000000000000 Bool.false 862754416657827 562949953421312 500000000070159 140318000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz369) (@HMul.hMul Real Real Real qz0 qz84 qz558) Bool.false 36705333730623133 9007199254740992 250000000771749 140318000000000000000 (Enclosure.clog_re_eq 9000 235256 4000 55426385536 16000000 rfl rfl rfl) (ep350 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz369) qz373 Bool.false 862754416657827 562949953421312 500000000070159 140318000000000000000 (Enclosure.clog_im_eq 9000 235256 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz373 (@HSub.hSub Real Real Real qz356 qz85 qz372) Bool.false 862754416657827 562949953421312 500000000070159 140318000000000000000 (BSN.arctan_recip 235256 9000 rfl rfl) ep352))))

noncomputable abbrev qz374 := (Enclosure.Real.IsNear.const Bool.false 235256 4000)

noncomputable abbrev qz87 := (@ep344 1 (BSN.w_sub_half_mk qz284 Bool.false 117628 1000 2 qz286 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz367 Bool.false 7000 4000 0 1 Bool.false 235256 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) qz374))

noncomputable def ep357 := @ep340 14703500002063165713 70159000000000000000000 ep341 373819139076212256049 4503599627370496000 1865281250342305761 8769875000000000000000 (@ep342 256937336114361931 36028797018963968 1750000005402243 561272000000000000000 (ep343 qz87) ep353 rfl) (@ep354 25371019130656718589 281474976710656000 14703500002063165713 70159000000000000000000 (ep355 qz87) ep356 rfl) rfl

noncomputable def ep358 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz78 qz81) (@HMul.hMul Real Real Real qz0 qz80 qz79) 6039280916604789 2251799813685248 3500000000491113 561272000000000000000 1079393749016434472131 4503599627370496000

noncomputable def ep359 := nat_lit 2457777146213835561266645311567167488

noncomputable def ep360 := @Enclosure.Real.IsNear.mulLit_ff qz78 qz81 7000 4000 0 1 862754416657827 562949953421312 500000000070159 140318000000000000000

noncomputable def ep361 := @Enclosure.Real.IsNear.mulLit_ff qz80 qz79 235256 4000 0 1 36705333730623133 9007199254740992 250000000771749 140318000000000000000

noncomputable def ep362 := @ep358 7351750022694822843 70159000000000000000000 ep359 1091472310849644050131 4503599627370496000 30426757901391453 274058593750000000000 (@ep360 6039280916604789 2251799813685248 3500000000491113 561272000000000000000 (ep343 qz87) ep356 rfl) (@ep361 1079393749016434472131 4503599627370496000 7351750022694822843 70159000000000000000000 (ep355 qz87) ep353 rfl) rfl

noncomputable def ep363 := @Enclosure.Complex.IsNear.of_eq qz72 (Complex.mk qz83 qz82) Bool.false 9000 4000 0 1 Bool.false 235256 4000 0 1 (BSN.w_shift_mk qz13 Bool.false 117628 1000 2 qz14 rfl)

noncomputable abbrev qz375 := (ep363 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9000 4000) (Enclosure.sfrac Bool.false 235256 4000) Bool.false 9000 4000 0 1 Bool.false 235256 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 235256 4000)))

noncomputable abbrev qz88 := qz375

noncomputable def ep364 := ep338 (@ep339 274058593750000000000 (ep357 rfl) (ep362 rfl)) qz88 rfl rfl rfl rfl rfl rfl

noncomputable abbrev qz89 := qz360

noncomputable def ep365 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re qz89) (Complex.re ↑qz2)) (@HMul.hMul Real Real Real qz0 (Complex.im qz89) (Complex.im ↑qz2)) 120447 131072 3 1048576 0 1 0 1 120447 120447

noncomputable def ep366 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz89) (Complex.re ↑qz2) 1 2 0 1 120447 65536 3 524288 120447 131072 3 1048576

noncomputable abbrev qz90 := (@Enclosure.Complex.IsNear.of_eq qz360 (Complex.mk (Enclosure.sfrac Bool.false 1 2) qz283) Bool.false 1 2 0 1 Bool.false 0 1 0 1 BSN.half_c_mk (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 2) qz283 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz370 qz295))

noncomputable def ep367 := ep366 (@Enclosure.Complex.IsNear.re_isNear qz89 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz90) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz2) qz2 Bool.false 120447 65536 3 524288 (Complex.ofReal_re qz2) EMRow38.d4)

noncomputable def ep368 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz89) (Complex.im ↑qz2) 0 1 0 1 0 1 0 1 0 1 0 1

noncomputable def ep369 := ep368 (@Enclosure.Complex.IsNear.im_isNear qz89 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz90) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz2) qz10 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz2) (0 : Real) qz10 (Complex.ofReal_im qz2) Enclosure.sfrac_zero_eq) qz18)

noncomputable def ep370 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re qz89) (Complex.im ↑qz2)) (@HMul.hMul Real Real Real qz0 (Complex.im qz89) (Complex.re ↑qz2)) 0 1 0 1 0 1 0 1 0 0

noncomputable def ep371 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz89) (Complex.im ↑qz2) 1 2 0 1 0 1 0 1 0 1 0 1

noncomputable def ep372 := ep371 (@Enclosure.Complex.IsNear.re_isNear qz89 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz90) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz2) qz10 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz2) (0 : Real) qz10 (Complex.ofReal_im qz2) Enclosure.sfrac_zero_eq) qz18)

noncomputable def ep373 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz89) (Complex.re ↑qz2) 0 1 0 1 120447 65536 3 524288 0 1 0 1

noncomputable def ep374 := ep373 (@Enclosure.Complex.IsNear.im_isNear qz89 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz90) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz2) qz2 Bool.false 120447 65536 3 524288 (Complex.ofReal_re qz2) EMRow38.d4)

noncomputable def ep375 := @ep334 30426757901391453 274058593750000000000 (ep364 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz89 (↑qz2) Bool.false 120447 131072 3 1048576 Bool.false 0 1 0 1 (@ep365 131072 3 1048576 (ep367 rfl) (ep369 rfl) rfl rfl) (@ep370 1 0 1 (ep372 rfl) (ep374 rfl) rfl rfl))

noncomputable abbrev qz91 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)

noncomputable abbrev qz376 := (@Nat.cast Complex Complex.instNatCast 1)

noncomputable abbrev qz92 := (@HMul.hMul Complex Complex Complex qz352 (@HMul.hMul Complex Complex Complex qz352 (2 : Complex) qz376) (@HSub.hSub Complex Complex Complex qz353 (@HMul.hMul Complex Complex Complex qz352 (2 : Complex) qz376) (1 : Complex)))

noncomputable abbrev qz377 := (@HPow.hPow Complex Int Complex qz557 qz553 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz93 := qz377

noncomputable def ep376 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz63 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz71 qz72 (@HSub.hSub Int Int Int qz365 qz73 (@HMul.hMul Int Int Int qz366 qz74 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz63 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz71 qz72 (@HSub.hSub Int Int Int qz365 qz73 (@HMul.hMul Int Int Int qz366 qz74 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92) qz93)) Bool.false 1859751 34359738368 3 34359738368

noncomputable def ep377 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz63 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz71 qz72 (@HSub.hSub Int Int Int qz365 qz73 (@HMul.hMul Int Int Int qz366 qz74 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92) qz93) Bool.false 0 1 0 1 Bool.false

noncomputable def ep378 := @ep377 0 1 0 1 Bool.false 1859751 34359738368 3 34359738368 Bool.true 6076633073 4294967296000 29407 12884901888000 Bool.false 1859751 1859751 34359738368 3 34359738368 Bool.true 6076633073 6076633073 4294967296000 29407

noncomputable def ep379 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz63 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz71 qz72 (@HSub.hSub Int Int Int qz365 qz73 (@HMul.hMul Int Int Int qz366 qz74 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep380 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92) qz93 Bool.false 1859751 34359738368 3 34359738368 Bool.true 6076633073 4294967296000 29407 12884901888000

noncomputable abbrev qz94 := (Complex.re qz377)

noncomputable abbrev qz95 := (Complex.im qz377)

noncomputable def ep381 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz94) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz95) 1859751 34359738368 3 34359738368 0 1 0

noncomputable def ep382 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz94 1 12 0 1 5579253 8589934592 9 8589934592 1859751

noncomputable def ep383 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz10) Bool.false 1 12 0 1 Bool.false 0 1 0 1

noncomputable abbrev qz378 := (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 12) qz10 Bool.false 1 12 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 12) qz18)

noncomputable def ep384 := @Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep383 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz378)

noncomputable def ep385 := @Enclosure.Complex.IsNear.re_isNear qz93 Bool.false 5579253 8589934592 9 8589934592 Bool.true 18229899219 1073741824000 29407 1073741824000

noncomputable abbrev qz559 := (@instHPow Complex Nat (@NPow.toPow Complex (@Monoid.toNPow Complex (@Semiring.toMonoid Complex Complex.instSemiring))))

noncomputable abbrev qz379 := (@HPow.hPow Complex Nat Complex qz559 qz553 1)

noncomputable abbrev qz96 := (@Inv.inv Complex Complex.instInv qz379)

noncomputable def ep386 := @Enclosure.Complex.IsNear.of_eq qz93 qz96 Bool.false 5579253 8589934592 9 8589934592 Bool.true 18229899219 1073741824000 29407

noncomputable def ep387 := @Enclosure.Complex.IsNear.of_parts qz96 Bool.false 5579253 8589934592 9 8589934592 Bool.true 18229899219 1073741824000 29407

noncomputable abbrev qz97 := (Complex.re qz379)

noncomputable abbrev qz98 := (@MonoidWithZeroHom Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz99 := (@MonoidWithZeroHom.funLike Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz100 := qz379

noncomputable def ep388 := @Enclosure.Real.IsNear.mulLit_ff qz97 (@Inv.inv Real Real.instInv (@DFunLike.coe qz98 Complex (fun (x : Complex) => Real) qz99 Complex.normSq qz100)) 9000 4000 0 1 619917 2147483648 1 2147483648

noncomputable def ep389 := @Enclosure.Complex.IsNear.re_isNear qz100 Bool.false 9000 4000 0 1 Bool.false 235256 4000 0 1

noncomputable def ep390 := @Enclosure.Complex.IsNear.of_eq qz100 qz72 Bool.false 9000 4000 0 1 Bool.false 235256 4000 0

noncomputable def ep391 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz98 Complex (fun (x : Complex) => Real) qz99 Complex.normSq qz100)) Bool.false 619917 2147483648 1 2147483648 619917 2147483648 1

noncomputable abbrev qz101 := (Complex.im qz379)

noncomputable abbrev qz380 := (@instHAdd Real Real.instAdd)

noncomputable def ep392 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz98 Complex (fun (x : Complex) => Real) qz99 Complex.normSq qz100) (@HAdd.hAdd Real Real Real qz380 (@HMul.hMul Real Real Real qz0 qz97 qz97) (@HMul.hMul Real Real Real qz0 qz101 qz101)) Bool.false 433018637 125000 0 1

noncomputable def ep393 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz97 qz97) (@HMul.hMul Real Real Real qz0 qz101 qz101) 81 16 0 1 864771649 250000

noncomputable def ep394 := @Enclosure.Real.IsNear.mulLit_ff qz97 qz97 9000 4000 0 1 9000 4000 0 1

noncomputable def ep395 := @Enclosure.Real.IsNear.mulLit_ff qz101 qz101 235256 4000 0 1 235256 4000 0 1

noncomputable def ep396 := @Enclosure.Complex.IsNear.im_isNear qz100 Bool.false 9000 4000 0 1 Bool.false 235256 4000 0 1

noncomputable abbrev qz102 := (ep389 (@ep390 1 (BSN.pow_one_c qz354) qz375))

noncomputable abbrev qz103 := (ep396 (@ep390 1 (BSN.pow_one_c qz354) qz375))

noncomputable def ep397 := @ep393 0 1 13856596384 433018637 125000 0 1 (@ep394 81 16 0 1 qz102 qz102 rfl) (@ep395 864771649 250000 0 1 qz103 qz103 rfl)

noncomputable def ep398 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz98 Complex (fun (x : Complex) => Real) qz99 Complex.normSq qz100) 433018637 125000 0 1 309958 309959 1073741824 (ep392 (Enclosure.Complex.normSq_eq_mul_add_mul qz100) (ep397 rfl rfl)) rfl

noncomputable def ep399 := @Enclosure.Real.IsNear.of_eq (Complex.re qz96) (@HMul.hMul Real Real Real qz0 qz97 (@Inv.inv Real Real.instInv (@DFunLike.coe qz98 Complex (fun (x : Complex) => Real) qz99 Complex.normSq qz100))) Bool.false 5579253 8589934592 9 8589934592 (Enclosure.Complex.inv_re_eq_mul qz100) (@ep388 5579253 8589934592 9 8589934592 qz102 (@ep391 2147483648 (ep398 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep400 := @Enclosure.Real.IsNear.of_eq (Complex.im qz96) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz101) (@Inv.inv Real Real.instInv (@DFunLike.coe qz98 Complex (fun (x : Complex) => Real) qz99 Complex.normSq qz100))) Bool.true 18229899219 1073741824000 29407 1073741824000 (Enclosure.Complex.inv_im_eq_mul qz100)

noncomputable def ep401 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz101) (@Inv.inv Real Real.instInv (@DFunLike.coe qz98 Complex (fun (x : Complex) => Real) qz99 Complex.normSq qz100)) 235256 4000 0 1 619917 2147483648 1

noncomputable def ep402 := @ep401 2147483648 18229899219 1073741824000 29407 1073741824000 (@Enclosure.Real.IsNear.neg qz101 Bool.false 235256 4000 0 1 qz103) (@ep391 2147483648 (ep398 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep403 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz95 0 1 0 1 18229899219 1073741824000 29407 1073741824000 0

noncomputable def ep404 := @Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep383 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz378)

noncomputable def ep405 := @Enclosure.Complex.IsNear.im_isNear qz93 Bool.false 5579253 8589934592 9 8589934592 Bool.true 18229899219 1073741824000 29407 1073741824000

noncomputable abbrev qz104 := (@ep386 1073741824000 (BSN.zpow_one_sub_two_mul qz354 1 1 rfl rfl) (@ep387 1073741824000 ep399 (ep400 ep402)))

noncomputable def ep406 := @ep381 1 1859751 1859751 34359738368 3 34359738368 (@ep382 34359738368 3 34359738368 ep384 (ep385 qz104) rfl) (@ep403 1 0 1 ep404 (ep405 qz104) rfl) rfl

noncomputable def ep407 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz95) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz94) 6076633073 4294967296000 29407 12884901888000 0 1 0

noncomputable def ep408 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz95 1 12 0 1 18229899219 1073741824000 29407 1073741824000 6076633073

noncomputable def ep409 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz94 0 1 0 1 5579253 8589934592 9 8589934592 0

noncomputable def ep410 := @ep407 1 6076633073 6076633073 4294967296000 29407 12884901888000 (@ep408 4294967296000 29407 12884901888000 ep384 (ep405 qz104) rfl) (@ep409 1 0 1 ep404 (ep385 qz104) rfl) rfl

noncomputable abbrev qz105 := (@Enclosure.Complex.IsNear.mk qz283 qz283 Bool.false 0 1 0 1 Bool.false 0 1 0 1 qz295 qz295)

noncomputable def ep411 := @ep378 12884901888000 (@ep379 0 1 0 1 (BSN.stirling_sum_base qz72) qz105) (ep380 (ep406 rfl) (ep410 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep412 := @ep331 826591230553874544339 4503599627370496000 ep323 ep314 (ep375 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep376 Bool.true 6076633073 4294967296000 29407 12884901888000 (BSN.stirling_sum_succ qz72 0 1 rfl) (ep411 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep413 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz13 2) Bool.false 36699808255196829 4503599627370496 250000000771749 70159000000000000000 Bool.false 877102023345571 281474976710656

noncomputable abbrev qz106 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz273 qz355 qz376))

noncomputable def ep414 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz13 2) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz13 1) qz106) Bool.false 36699808255196829 4503599627370496 250000000771749 70159000000000000000 Bool.false 877102023345571 281474976710656 500000000070159 70159000000000000000

noncomputable def ep415 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz13 1) qz106 Bool.false 36698831150136989 9007199254740992 250000000771749 140318000000000000000 Bool.false 881886885348771 562949953421312 500000000070159 140318000000000000000 Bool.false

noncomputable def ep416 := nat_lit 661124971130692368221200749428736

noncomputable def ep417 := nat_lit 987529086376255409735864418304

noncomputable abbrev qz107 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz273 qz355 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep418 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz13 1) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz13 0) qz107) Bool.false 36698831150136989 9007199254740992 250000000771749 140318000000000000000 Bool.false 881886885348771 562949953421312 500000000070159 140318000000000000000

noncomputable def ep419 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz13 0) qz107 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz381 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz82))

noncomputable def ep420 := @Enclosure.Complex.IsNear.of_eq qz107 qz381 Bool.false 36698831150136989 9007199254740992 250000000771749 140318000000000000000 Bool.false 881886885348771 562949953421312 500000000070159 140318000000000000000

noncomputable def ep421 := nat_lit 3434047868927634366734288422094270501264396036086285904230386109039076766754157637843025920

noncomputable def ep422 := nat_lit 78265180379036896710466750235418681157781778557439018633817879515419908247627418266763264

noncomputable def ep423 := nat_lit 7091406406465432244377964502050732669527078537342508802235242906230393117403387002880

noncomputable def ep424 := BSN.log_dyadic_bound 22578385536 88114385536 5 4 ep421 1048576 280636 ep422 ep423 549620 110692771072 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 22578385536) (BSN.artanhQ 88114385536) 0 4 ep422 ep421 ep423 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep425 := @Enclosure.Real.IsNear.mulLit_ff qz84 (Real.log (Enclosure.sfrac Bool.false 55346385536 16000000)) 1 2 0 1 36698831150136989 4503599627370496 250000000771749 70159000000000000000 36698831150136989 9007199254740992 250000000771749 140318000000000000000 qz370 (BSN.isNear_log_sfrac 55346385536 16000000 36698831150136989 4503599627370496 250000000771749 70159000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 55346385536) qz371)) Bool.false 307852108576688347021312 37778931862957161709568 1000000003086996 280636000000000000000 36698831150136989 4503599627370496 250000000771749 70159000000000000000 (BSN.log_rat_reduce_isNear 55346385536 16000000 11 110692771072 65536000000 549620 1048576 24973259072661432 36028797018963968 280636 1000000000000000 rfl rfl rfl rfl (ep424 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep426 := BSN.arctan_dyadic_bound_f 1000 235256 1 0 1048576 280636 0 1 1 0 1 1 4457 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 235256) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 235256) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz382 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable abbrev qz383 := (@Nat.cast Real Real.instNatCast 235256)

noncomputable def ep427 := @Enclosure.Real.IsNear.subLit_ff_p qz85 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz382 qz383)) 884279719003555 562949953421312 1 2000000000000000 4457 1048576 1 280636 924725422691472900096 881886885348771 562949953421312 500000000070159 140318000000000000000 qz86 (ep426 rfl) rfl rfl

noncomputable abbrev qz108 := (@HAdd.hAdd Complex Complex Complex qz273 qz355 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz384 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz82)

noncomputable def ep428 := @ep419 36698831150136989 9007199254740992 250000000771749 140318000000000000000 Bool.false 881886885348771 562949953421312 500000000070159 140318000000000000000 Bool.false 36698831150136989 36698831150136989 9007199254740992 250000000771749 140318000000000000000 Bool.false 881886885348771 881886885348771 562949953421312 500000000070159 140318000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz13 0) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz13) qz105) (ep420 (@congrArg Complex Complex qz108 qz384 Complex.log (BSN.w_shift_mk qz13 Bool.false 117628 1000 0 qz14 rfl)) (@Enclosure.Complex.IsNear.of_parts qz381 Bool.false 36698831150136989 9007199254740992 250000000771749 140318000000000000000 Bool.false 881886885348771 562949953421312 500000000070159 140318000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz381) (@HMul.hMul Real Real Real qz0 qz84 (Real.log (Enclosure.sfrac Bool.false 55346385536 16000000))) Bool.false 36698831150136989 9007199254740992 250000000771749 140318000000000000000 (Enclosure.clog_re_eq 1000 235256 4000 55346385536 16000000 rfl rfl rfl) (ep425 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz381) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz383 qz382)) Bool.false 881886885348771 562949953421312 500000000070159 140318000000000000000 (Enclosure.clog_im_eq 1000 235256 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz383 qz382)) (@HSub.hSub Real Real Real qz356 qz85 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz382 qz383))) Bool.false 881886885348771 562949953421312 500000000070159 140318000000000000000 (BSN.arctan_recip 235256 1000 rfl rfl) ep427)))) rfl rfl

noncomputable abbrev qz385 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz82))

noncomputable def ep429 := @Enclosure.Complex.IsNear.of_eq qz106 qz385 Bool.false 36700785360256669 9007199254740992 250000000771749 140318000000000000000 Bool.false 872317161342371 562949953421312 500000000070159 140318000000000000000

noncomputable def ep430 := nat_lit 3441537747903049393054523366380760521800662044986296192938283755434779992929733456083025920

noncomputable def ep431 := nat_lit 78565093187082140254608459747981724708543953489730588535979805404222694174266411674763264

noncomputable def ep432 := nat_lit 7151934484702835858936466975333836827311408436692508443855543599021176216938747002880

noncomputable def ep433 := BSN.log_dyadic_bound 22602385536 88138385536 5 4 ep430 1048576 280636 ep431 ep432 550075 110740771072 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 22602385536) (BSN.artanhQ 88138385536) 0 4 ep431 ep430 ep432 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep434 := @Enclosure.Real.IsNear.mulLit_ff qz84 (Real.log (Enclosure.sfrac Bool.false 55370385536 16000000)) 1 2 0 1 36700785360256669 4503599627370496 250000000771749 70159000000000000000 36700785360256669 9007199254740992 250000000771749 140318000000000000000 qz370 (BSN.isNear_log_sfrac 55370385536 16000000 36700785360256669 4503599627370496 250000000771749 70159000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 55370385536) qz371)) Bool.false 307868501679331975626752 37778931862957161709568 1000000003086996 280636000000000000000 36700785360256669 4503599627370496 250000000771749 70159000000000000000 (BSN.log_rat_reduce_isNear 55370385536 16000000 11 110740771072 65536000000 550075 1048576 24973259072661432 36028797018963968 280636 1000000000000000 rfl rfl rfl rfl (ep433 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep435 := BSN.arctan_dyadic_bound_f 5000 235256 1 0 1048576 280636 0 1 1 0 1 1 22282 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 235256) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 235256) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz386 := (@Nat.cast Real Real.instNatCast 5000)

noncomputable def ep436 := @Enclosure.Real.IsNear.subLit_ff_p qz85 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz386 qz383)) 884279719003555 562949953421312 1 2000000000000000 22282 1048576 1 280636 914690839771738013696 872317161342371 562949953421312 500000000070159 140318000000000000000 qz86 (ep435 rfl) rfl rfl

noncomputable abbrev qz109 := (@HAdd.hAdd Complex Complex Complex qz273 qz355 qz376)

noncomputable abbrev qz387 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz82)

noncomputable def ep437 := @ep415 36700785360256669 9007199254740992 250000000771749 140318000000000000000 Bool.false 872317161342371 562949953421312 500000000070159 140318000000000000000 Bool.false ep416 36699808255196829 4503599627370496 250000000771749 70159000000000000000 Bool.false ep417 877102023345571 281474976710656 500000000070159 70159000000000000000 (ep418 (BSN.log_sum_c_succ qz13 0 1 rfl) (ep428 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep429 (@congrArg Complex Complex qz109 qz387 Complex.log (BSN.w_shift_mk qz13 Bool.false 117628 1000 1 qz14 rfl)) (@Enclosure.Complex.IsNear.of_parts qz385 Bool.false 36700785360256669 9007199254740992 250000000771749 140318000000000000000 Bool.false 872317161342371 562949953421312 500000000070159 140318000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz385) (@HMul.hMul Real Real Real qz0 qz84 (Real.log (Enclosure.sfrac Bool.false 55370385536 16000000))) Bool.false 36700785360256669 9007199254740992 250000000771749 140318000000000000000 (Enclosure.clog_re_eq 5000 235256 4000 55370385536 16000000 rfl rfl rfl) (ep434 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz385) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz383 qz386)) Bool.false 872317161342371 562949953421312 500000000070159 140318000000000000000 (Enclosure.clog_im_eq 5000 235256 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz383 qz386)) (@HSub.hSub Real Real Real qz356 qz85 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz386 qz383))) Bool.false 872317161342371 562949953421312 500000000070159 140318000000000000000 (BSN.arctan_recip 235256 5000 rfl rfl) ep436)))) rfl rfl

noncomputable def ep438 := @ep324 ep314 Bool.false 36699808255196829 4503599627370496 250000000771749 70159000000000000000 Bool.false 877102023345571 281474976710656 500000000070159 70159000000000000000 Bool.true ep325 416513275324499133049 4503599627370496000 ep319 ep320 Bool.false ep326 812557598180345408339 4503599627370496000 ep316 ep314 (@ep327 4503599627370496000 ep322 ep320 Bool.false 826591230553874544339 4503599627370496000 ep323 ep314 (BSN.logGammaStirling_unfold 1 qz72) (ep412 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep413 500000000070159 70159000000000000000 (BSN.log_sum_c_eq qz13 2) (ep414 (BSN.log_sum_c_succ qz13 1 2 rfl) (ep437 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz110 := (@HDiv.hDiv Real Real Real qz270 qz284 (2 : Real))

noncomputable def ep439 := @Enclosure.Real.IsNear.mulLit_ff qz110 (Real.log Real.pi) 117628 2000 0 1 75021 65536 1 262144 2206142547 32768000 29407 131072000 (@Enclosure.Real.IsNear.of_eq qz110 (Enclosure.sfrac Bool.false 117628 2000) Bool.false 117628 2000 0 1 (BSN.t_half_eq qz13 Bool.false 117628 1000 qz14) (Enclosure.Real.IsNear.const Bool.false 117628 2000)) EMRow38.d5 rfl

noncomputable def ep440 := @ep317 29407 131072000 ep318 101869535062122567031 900719925474099200 ep313 ep314 (@ep321 ep316 ep314 (ep438 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep439 rfl rfl

noncomputable def ep441 := BSN.cos_dyadic_bound_f 1219174 2147483648 1 0 1048576 280911 0 1 1 0 1 1 1048575 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 1219174) qz292 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 1219174) qz293 0 0 rfl) rfl rfl

noncomputable def ep442 := @ep312 131072 Bool.false 1048575 1048576 1 140318 (@ep315 118591747 1048576 45 131072 ep440 rfl) (Enclosure.sfrac_false_div 118591747 1048576) (BSN.cos_reduce0 qz357 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 85791785793433370624) qz33) 226375608064910080 72057594037927936 Bool.false 1048575 1048576 18 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q0 118591747 1048576 226375608064910080 72057594037927936 18 85791785793433370624 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1048575 1048576 85791785793433370624 151115727451828646838272 1219174 2147483648 280911 280636 (ep441 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep443 := nat_lit 1291546278893588064093121

noncomputable def ep444 := nat_lit 17115185939682775007232000

noncomputable def ep445 := nat_lit 7512072890517162071975243639

noncomputable def ep446 := nat_lit 1200784330342203811732389888000

noncomputable abbrev qz560 := (@Nat.cast Complex Complex.instNatCast 24)

noncomputable abbrev qz388 := (@HPow.hPow Complex Complex Complex qz531 qz560 qz532)

noncomputable abbrev qz111 := qz388

noncomputable abbrev qz389 := qz560

noncomputable abbrev qz112 := (@HAdd.hAdd Complex Complex Complex qz273 (@HDiv.hDiv Complex Complex Complex qz361 qz389 (@HSub.hSub Complex Complex Complex qz353 qz272 (1 : Complex))) qz360)

noncomputable abbrev qz113 := (@instHSub Nat instSubNat)

noncomputable abbrev qz390 := qz559

noncomputable abbrev qz114 := qz390

noncomputable abbrev qz115 := qz389

noncomputable def ep447 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz5 1 24) (@HAdd.hAdd Complex Complex Complex qz4 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 24, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz7) (@HMul.hMul Complex Complex Complex qz62 qz111 (@HAdd.hAdd Complex Complex Complex qz4 qz112 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))))) Bool.false ep307 ep308 ep309

noncomputable def ep448 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 24, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz7) (@HMul.hMul Complex Complex Complex qz62 qz111 (@HAdd.hAdd Complex Complex Complex qz4 qz112 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))))) Bool.false 3524334641735 1099511627776 473760497877339 77140636293136384

noncomputable def ep449 := nat_lit 11299026237867597806776333

noncomputable def ep450 := nat_lit 146555223026403282229667639

noncomputable def ep451 := nat_lit 29206506340471824537529046836468252672

noncomputable def ep452 := nat_lit 710035075727162342320116043977064448

noncomputable def ep453 := @ep448 Bool.false 65627308659 549755813888 236587330939209 38570318146568192 Bool.true 867034953451435785430253 ep308 ep449 ep310 Bool.true 751585529892647336282879 ep444 ep450 ep446 Bool.false ep451 ep307 ep308 ep309 ep310 Bool.false ep452 ep443 ep444

noncomputable def ep454 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 24, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz7) (BSN.headSumC qz5 24) Bool.false 3524334641735 1099511627776 473760497877339 77140636293136384 Bool.false 65627308659 549755813888 236587330939209

noncomputable abbrev qz116 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 23) qz275)

noncomputable def ep455 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 24) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 23) qz116) Bool.false 3524334641735 1099511627776 473760497877339 77140636293136384 Bool.false 65627308659 549755813888 236587330939209 38570318146568192

noncomputable def ep456 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 23) qz116 Bool.false 898865403677 274877906944 230061989444469 38570318146568192 Bool.true 43348298115 549755813888 229745514683771 38570318146568192 Bool.true

noncomputable abbrev qz117 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 22) qz275)

noncomputable def ep457 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 23) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 22) qz117) Bool.false 898865403677 274877906944 230061989444469 38570318146568192 Bool.true 43348298115 549755813888 229745514683771 38570318146568192

noncomputable def ep458 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 22) qz117 Bool.false 429694518973 137438953472 223077380765043 38570318146568192 Bool.true 259950364989 1099511627776 445516995242545 77140636293136384 Bool.false

noncomputable abbrev qz118 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 21) qz275)

noncomputable def ep459 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 22) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 21) qz118) Bool.false 429694518973 137438953472 223077380765043 38570318146568192 Bool.true 259950364989 1099511627776 445516995242545 77140636293136384

noncomputable def ep460 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 21) qz118 Bool.false 1598837057515 549755813888 53970045332409 9642579536642048 Bool.true 264894664333 1099511627776 431266667176641 77140636293136384 Bool.false

noncomputable abbrev qz119 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 20) qz275)

noncomputable def ep461 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 21) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 20) qz119) Bool.false 1598837057515 549755813888 53970045332409 9642579536642048 Bool.true 264894664333 1099511627776 431266667176641 77140636293136384

noncomputable def ep462 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 20) qz119 Bool.false 1492371718685 549755813888 104274389903813 19285159073284096 Bool.true 141984607719 1099511627776 416630800558127 77140636293136384 Bool.false

noncomputable abbrev qz120 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 19) qz275)

noncomputable def ep463 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 20) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 19) qz120) Bool.false 1492371718685 549755813888 104274389903813 19285159073284096 Bool.true 141984607719 1099511627776 416630800558127 77140636293136384

noncomputable def ep464 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 19) qz120 Bool.false 2804229647683 1099511627776 402066634916285 77140636293136384 Bool.false 17101243897 549755813888 200800568869467 38570318146568192 Bool.false

noncomputable def ep465 := nat_lit 3281760115316422208389120

noncomputable abbrev qz121 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 18) qz275)

noncomputable def ep466 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 19) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 18) qz121) Bool.false 2804229647683 1099511627776 402066634916285 77140636293136384 Bool.false 17101243897 549755813888 200800568869467 38570318146568192

noncomputable def ep467 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 18) qz121 Bool.false 325680978555 137438953472 193310741494041 38570318146568192 Bool.false 100239380183 549755813888 193082606596285 38570318146568192 Bool.false

noncomputable abbrev qz122 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 17) qz275)

noncomputable def ep468 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 18) (@HAdd.hAdd Complex Complex Complex qz4 qz38 qz122) Bool.false 325680978555 137438953472 193310741494041 38570318146568192 Bool.false 100239380183 549755813888 193082606596285 38570318146568192

noncomputable def ep469 := @Enclosure.Complex.IsNear.addLitP qz38 qz122 Bool.false 2347483159709 1099511627776 370715408847401 77140636293136384 Bool.false 268061722897 1099511627776 370311660079289 77140636293136384 Bool.false

noncomputable def ep470 := nat_lit 2864720182933508786749440

noncomputable abbrev qz391 := (@Nat.cast Real Real.instNatCast 17)

noncomputable abbrev qz123 := (@Inv.inv Real Real.instInv (Real.sqrt qz391))

noncomputable abbrev qz561 := (Real.log (Enclosure.sfrac Bool.false 17 1))

noncomputable abbrev qz124 := (@HMul.hMul Real Real Real qz267 qz284 qz561)

noncomputable def ep471 := @Enclosure.Complex.IsNear.of_eq qz122 (Complex.mk (@HMul.hMul Real Real Real qz0 qz123 (Real.cos qz124)) (@HMul.hMul Real Real Real qz0 qz123 (@Neg.neg Real Real.instNeg (Real.sin qz124)))) Bool.false 257964668731 1099511627776 15906074140681 77140636293136384 Bool.true 67582962531 1099511627776 15853553113281 77140636293136384 (BSN.cpow_neg_s_mk qz13 117628 1000 17 qz14 rfl)

noncomputable abbrev qz392 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 17) qz15)

noncomputable def ep472 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz391) 4323389 1048576 1 1048576 127158 127159 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz391) (Real.sqrt qz392) Bool.false 4323389 1048576 1 1048576 (BSN.sqrt_natCast_div_one 17) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz392) Bool.false 4323389 1048576 1 1048576 4323389 1048576 1 1048576 (BSN.sqrt_enclosure 17 1 2161694 2161695 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep473 := BSN.log_dyadic_bound 1 33 2 1 3267 524288 140318 1 1 31784 34 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1) (BSN.artanhQ 33) 0 1 1 3267 1 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep474 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz561 117628 1000 0 1 3189913004350711 1125899906842624 125000000070159 17539750000000000000 93805771718941358377 281474976710656000 3675875002063165713 4384937500000000000000 qz17 (BSN.isNear_log_sfrac 17 1 3189913004350711 1125899906842624 125000000070159 17539750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz392) Bool.false 53517859495200818200576 18889465931478580854784 1000000000561272 140318000000000000000 3189913004350711 1125899906842624 125000000070159 17539750000000000000 (BSN.log_rat_reduce_isNear 17 1 4 34 32 31784 524288 24973259072661432 36028797018963968 140318 1000000000000000 rfl rfl rfl rfl (ep473 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep475 := nat_lit 91667905777236539018894861684982016

noncomputable def ep476 := BSN.cos_dyadic_bound_f 550242748 2147483648 2 1 1048576 280911 ep475 ep77 ep475 ep475 ep78 ep475 1014343 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 550242748) qz292 0 1 ep475 ep77 ep475 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 550242748) qz293 0 1 ep475 ep78 ep475 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz393 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 349453731) qz32)

noncomputable def ep477 := @Enclosure.Real.IsNear.cos_image qz124 qz393 Bool.false 349453731 1048576 55 65536 Bool.false 1014343 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz124 Bool.false 93805771718941358377 281474976710656000 3675875002063165713 4384937500000000000000 349453731 1048576 55 65536 (ep474 rfl) rfl) (Enclosure.sfrac_false_div 349453731 1048576) (BSN.cos_reduce0 qz393 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 38719891193061254889472) qz33) 226375608064910080 72057594037927936 Bool.false 1014343 1048576 53 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q0 349453731 1048576 226375608064910080 72057594037927936 53 38719891193061254889472 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1014343 1048576 38719891193061254889472 151115727451828646838272 550242748 2147483648 280911 280636 (ep476 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep478 := BSN.sin_dyadic_bound_f 550242748 2147483648 2 1 1048576 280911 ep475 ep81 ep475 ep475 ep82 ep475 265743 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 550242748) qz287 0 1 ep475 ep81 ep475 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 550242748) qz288 0 1 ep475 ep82 ep475 rfl rfl rfl rfl) rfl rfl

noncomputable def ep479 := @Enclosure.Real.IsNear.sin_image qz124 qz393 Bool.false 349453731 1048576 55 65536 Bool.false 265743 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz124 Bool.false 93805771718941358377 281474976710656000 3675875002063165713 4384937500000000000000 349453731 1048576 55 65536 (ep474 rfl) rfl) (Enclosure.sfrac_false_div 349453731 1048576) (BSN.sin_reduce0 qz393 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 38719891193061254889472) qz33) 226375608064910080 72057594037927936 Bool.false 265743 1048576 53 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q0 349453731 1048576 226375608064910080 72057594037927936 53 38719891193061254889472 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 265743 1048576 38719891193061254889472 151115727451828646838272 550242748 2147483648 280911 280636 (ep478 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz394 := (@Enclosure.Real.IsNear.recentre' qz123 Bool.false 254317 1048576 1 1048576 254317 1048576 1 1048576 (ep472 rfl rfl) rfl)

noncomputable def ep480 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz123 (Real.cos qz124)) (@HMul.hMul Real Real Real qz0 qz123 (@Neg.neg Real Real.instNeg (Real.sin qz124))) Bool.false 257964668731 1099511627776 15906074140681 77140636293136384 Bool.true 67582962531 1099511627776 15853553113281 77140636293136384 (@Enclosure.Real.IsNear.mulLit_ff qz123 (Real.cos qz124) 254317 1048576 1 1048576 1014343 1048576 3891513 4597940224 257964668731 1099511627776 15906074140681 77140636293136384 qz394 (@Enclosure.Real.IsNear.recentre' (Real.cos qz124) Bool.false 1014343 1048576 7783026 9195880448 1014343 1048576 3891513 4597940224 (ep477 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz123 (@Neg.neg Real Real.instNeg (Real.sin qz124)) 254317 1048576 1 1048576 265743 1048576 3891513 4597940224 67582962531 1099511627776 15853553113281 77140636293136384 qz394 (@Enclosure.Real.IsNear.neg (Real.sin qz124) Bool.false 265743 1048576 3891513 4597940224 (@Enclosure.Real.IsNear.recentre' (Real.sin qz124) Bool.false 265743 1048576 7783026 9195880448 265743 1048576 3891513 4597940224 (ep479 rfl rfl) rfl)) rfl)

noncomputable def ep481 := @ep469 257964668731 1099511627776 15906074140681 77140636293136384 Bool.true 67582962531 1099511627776 15853553113281 77140636293136384 Bool.false ep470 325680978555 137438953472 193310741494041 38570318146568192 Bool.false 220428728144535293526016 100239380183 549755813888 193082606596285 38570318146568192 EMRow38.d7 (ep471 ep480) rfl rfl

noncomputable abbrev qz395 := (@Nat.cast Real Real.instNatCast 18)

noncomputable abbrev qz125 := (@Inv.inv Real Real.instInv (Real.sqrt qz395))

noncomputable abbrev qz562 := (Real.log (Enclosure.sfrac Bool.false 18 1))

noncomputable abbrev qz126 := (@HMul.hMul Real Real Real qz267 qz284 qz562)

noncomputable def ep482 := @Enclosure.Complex.IsNear.of_eq qz121 (Complex.mk (@HMul.hMul Real Real Real qz0 qz125 (Real.cos qz126)) (@HMul.hMul Real Real Real qz0 qz125 (@Neg.neg Real Real.instNeg (Real.sin qz126)))) Bool.false 198781819243 1099511627776 15445151928203 77140636293136384 Bool.true 41569068143 274877906944 3858981136591 19285159073284096 (BSN.cpow_neg_s_mk qz13 117628 1000 18 qz14 rfl)

noncomputable abbrev qz396 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 18) qz15)

noncomputable def ep483 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz395) 4448731 1048576 1 1048576 123575 123576 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz395) (Real.sqrt qz396) Bool.false 4448731 1048576 1 1048576 (BSN.sqrt_natCast_div_one 18) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz396) Bool.false 4448731 1048576 1 1048576 4448731 1048576 1 1048576 (BSN.sqrt_enclosure 18 1 2224365 2224366 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep484 := BSN.log_dyadic_bound 2 34 2 1 3468 524288 140318 4 4 61752 36 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 2) (BSN.artanhQ 34) 0 1 4 3468 4 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep485 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz562 117628 1000 0 1 3254268794313975 1125899906842624 125000000070159 17539750000000000000 3827931297375642513 11258999068426240 3675875002063165713 4384937500000000000000 qz17 (BSN.isNear_log_sfrac 18 1 3254268794313975 1125899906842624 125000000070159 17539750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz396) Bool.false 54597570484265130393600 18889465931478580854784 1000000000561272 140318000000000000000 3254268794313975 1125899906842624 125000000070159 17539750000000000000 (BSN.log_rat_reduce_isNear 18 1 4 36 32 61752 524288 24973259072661432 36028797018963968 140318 1000000000000000 rfl rfl rfl rfl (ep484 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep486 := nat_lit 178944695974050158508175327567072831035176508149395406497830186832921656176161

noncomputable def ep487 := nat_lit 25076010669082282704048592895810595727599092314690169756732910064579522081

noncomputable def ep488 := nat_lit 536783935900812310959117885515426871914074326263556839153977094678635809484321

noncomputable def ep489 := BSN.cos_dyadic_bound_f 1495916339 2147483648 3 2 1048576 280911 ep486 ep66 ep487 ep488 ep68 ep487 804293 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1495916339) qz292 0 2 ep486 ep66 ep487 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1495916339) qz293 0 2 ep488 ep68 ep487 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz397 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 356503883) qz32)

noncomputable def ep490 := @Enclosure.Real.IsNear.cos_image qz126 qz397 Bool.false 356503883 1048576 55 65536 Bool.false 804293 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz126 Bool.false 3827931297375642513 11258999068426240 3675875002063165713 4384937500000000000000 356503883 1048576 55 65536 (ep485 rfl) rfl) (Enclosure.sfrac_false_div 356503883 1048576) (BSN.cos_reduce0 qz397 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 105265754227348074397696) qz33) 226375608064910080 72057594037927936 Bool.false 804293 1048576 54 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q0 356503883 1048576 226375608064910080 72057594037927936 54 105265754227348074397696 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 804293 1048576 105265754227348074397696 151115727451828646838272 1495916339 2147483648 280911 280636 (ep489 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep491 := nat_lit 5007595298052976914913401049197252241

noncomputable def ep492 := BSN.sin_dyadic_bound_f 1495916339 2147483648 2 1 1048576 280911 ep491 ep81 ep491 ep491 ep82 ep491 672772 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1495916339) qz287 0 1 ep491 ep81 ep491 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1495916339) qz288 0 1 ep491 ep82 ep491 rfl rfl rfl rfl) rfl rfl

noncomputable def ep493 := @Enclosure.Real.IsNear.sin_image qz126 qz397 Bool.false 356503883 1048576 55 65536 Bool.false 672772 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz126 Bool.false 3827931297375642513 11258999068426240 3675875002063165713 4384937500000000000000 356503883 1048576 55 65536 (ep485 rfl) rfl) (Enclosure.sfrac_false_div 356503883 1048576) (BSN.sin_reduce0 qz397 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 105265754227348074397696) qz33) 226375608064910080 72057594037927936 Bool.false 672772 1048576 54 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q0 356503883 1048576 226375608064910080 72057594037927936 54 105265754227348074397696 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 672772 1048576 105265754227348074397696 151115727451828646838272 1495916339 2147483648 280911 280636 (ep492 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz398 := (@Enclosure.Real.IsNear.recentre' qz125 Bool.false 247151 1048576 1 1048576 247151 1048576 1 1048576 (ep483 rfl rfl) rfl)

noncomputable def ep494 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz125 (Real.cos qz126)) (@HMul.hMul Real Real Real qz0 qz125 (@Neg.neg Real Real.instNeg (Real.sin qz126))) Bool.false 198781819243 1099511627776 15445151928203 77140636293136384 Bool.true 41569068143 274877906944 3858981136591 19285159073284096 (@Enclosure.Real.IsNear.mulLit_ff qz125 (Real.cos qz126) 247151 1048576 1 1048576 804293 1048576 3891513 4597940224 198781819243 1099511627776 15445151928203 77140636293136384 qz398 (@Enclosure.Real.IsNear.recentre' (Real.cos qz126) Bool.false 804293 1048576 7783026 9195880448 804293 1048576 3891513 4597940224 (ep490 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz125 (@Neg.neg Real Real.instNeg (Real.sin qz126)) 247151 1048576 1 1048576 168193 262144 3891513 4597940224 41569068143 274877906944 3858981136591 19285159073284096 qz398 (@Enclosure.Real.IsNear.neg (Real.sin qz126) Bool.false 168193 262144 3891513 4597940224 (@Enclosure.Real.IsNear.recentre' (Real.sin qz126) Bool.false 672772 1048576 7783026 9195880448 168193 262144 3891513 4597940224 (ep493 rfl rfl) rfl)) rfl)

noncomputable def ep495 := @ep467 198781819243 1099511627776 15445151928203 77140636293136384 Bool.true 41569068143 274877906944 3858981136591 19285159073284096 Bool.false 385410388072706789605376 2804229647683 1099511627776 402066634916285 77140636293136384 Bool.false 4700754128546213920768 17101243897 549755813888 200800568869467 38570318146568192 (ep468 (BSN.head_sum_c_succ qz5 17 18 rfl rfl) (ep481 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep482 ep494) rfl rfl

noncomputable abbrev qz399 := (@Nat.cast Real Real.instNatCast 19)

noncomputable abbrev qz127 := (@Inv.inv Real Real.instInv (Real.sqrt qz399))

noncomputable abbrev qz563 := (Real.log (Enclosure.sfrac Bool.false 19 1))

noncomputable abbrev qz128 := (@HMul.hMul Real Real Real qz267 qz284 qz563)

noncomputable def ep496 := @Enclosure.Complex.IsNear.of_eq qz120 (Complex.mk (@HMul.hMul Real Real Real qz0 qz127 (Real.cos qz128)) (@HMul.hMul Real Real Real qz0 qz127 (@Neg.neg Real Real.instNeg (Real.sin qz128)))) Bool.false 180513789687 1099511627776 15030924698967 77140636293136384 Bool.true 176187095513 1099511627776 15029662819193 77140636293136384 (BSN.cpow_neg_s_mk qz13 117628 1000 19 qz14 rfl)

noncomputable abbrev qz400 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 19) qz15)

noncomputable def ep497 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz399) 4570637 1048576 1 1048576 120279 120280 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz399) (Real.sqrt qz400) Bool.false 4570637 1048576 1 1048576 (BSN.sqrt_natCast_div_one 19) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz400) Bool.false 4570637 1048576 1 1048576 4570637 1048576 1 1048576 (BSN.sqrt_enclosure 19 1 2285318 2285319 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep498 := BSN.log_dyadic_bound 3 35 3 2 22509375 524288 140318 55368 243 90099 38 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 3) (BSN.artanhQ 35) 0 2 55368 22509375 243 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep499 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz563 117628 1000 0 1 3315143513283831 1125899906842624 125000000070159 17539750000000000000 97488425295137618217 281474976710656000 3675875002063165713 4384937500000000000000 qz17 (BSN.isNear_log_sfrac 19 1 3315143513283831 1125899906842624 125000000070159 17539750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz400) Bool.false 55618878793361701994496 18889465931478580854784 1000000000561272 140318000000000000000 3315143513283831 1125899906842624 125000000070159 17539750000000000000 (BSN.log_rat_reduce_isNear 19 1 4 38 32 90099 524288 24973259072661432 36028797018963968 140318 1000000000000000 rfl rfl rfl rfl (ep498 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep500 := nat_lit 271746274083503513882471644858630505439021585630309278754322214989894464551521

noncomputable def ep501 := nat_lit 57820903589652561971814675868956886534147844632866096727124859019560467041

noncomputable def ep502 := nat_lit 815123180443331236523471305224153602543996461201662104069512395251644272720481

noncomputable def ep503 := BSN.cos_dyadic_bound_f 1660583083 2147483648 3 2 1048576 280911 ep500 ep66 ep501 ep502 ep68 ep501 750393 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1660583083) qz292 0 2 ep500 ep66 ep501 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1660583083) qz293 0 2 ep502 ep68 ep501 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz401 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 90793171) qz537)

noncomputable def ep504 := @Enclosure.Real.IsNear.cos_image qz128 qz401 Bool.false 90793171 262144 55 65536 Bool.false 750393 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz128 Bool.false 97488425295137618217 281474976710656000 3675875002063165713 4384937500000000000000 90793171 262144 55 65536 (ep499 rfl) rfl) (Enclosure.sfrac_false_div 90793171 262144) (BSN.cos_reduce0 qz401 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 29213286543429795315712) qz299) 226375608064910080 72057594037927936 Bool.false 750393 1048576 55 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q0 90793171 262144 226375608064910080 72057594037927936 55 29213286543429795315712 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 750393 1048576 29213286543429795315712 37778931862957161709568 1660583083 2147483648 280911 280636 (ep503 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep505 := nat_lit 7604005759443673775669600295060742321

noncomputable def ep506 := BSN.sin_dyadic_bound_f 1660583083 2147483648 2 1 1048576 280911 ep505 ep81 ep505 ep505 ep82 ep505 732407 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1660583083) qz287 0 1 ep505 ep81 ep505 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1660583083) qz288 0 1 ep505 ep82 ep505 rfl rfl rfl rfl) rfl rfl

noncomputable def ep507 := @Enclosure.Real.IsNear.sin_image qz128 qz401 Bool.false 90793171 262144 55 65536 Bool.false 732407 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz128 Bool.false 97488425295137618217 281474976710656000 3675875002063165713 4384937500000000000000 90793171 262144 55 65536 (ep499 rfl) rfl) (Enclosure.sfrac_false_div 90793171 262144) (BSN.sin_reduce0 qz401 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 29213286543429795315712) qz299) 226375608064910080 72057594037927936 Bool.false 732407 1048576 55 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q0 90793171 262144 226375608064910080 72057594037927936 55 29213286543429795315712 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 732407 1048576 29213286543429795315712 37778931862957161709568 1660583083 2147483648 280911 280636 (ep506 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz402 := (@Enclosure.Real.IsNear.recentre' qz127 Bool.false 240559 1048576 1 1048576 240559 1048576 1 1048576 (ep497 rfl rfl) rfl)

noncomputable def ep508 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz127 (Real.cos qz128)) (@HMul.hMul Real Real Real qz0 qz127 (@Neg.neg Real Real.instNeg (Real.sin qz128))) Bool.false 180513789687 1099511627776 15030924698967 77140636293136384 Bool.true 176187095513 1099511627776 15029662819193 77140636293136384 (@Enclosure.Real.IsNear.mulLit_ff qz127 (Real.cos qz128) 240559 1048576 1 1048576 750393 1048576 3891513 4597940224 180513789687 1099511627776 15030924698967 77140636293136384 qz402 (@Enclosure.Real.IsNear.recentre' (Real.cos qz128) Bool.false 750393 1048576 7783026 9195880448 750393 1048576 3891513 4597940224 (ep504 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz127 (@Neg.neg Real Real.instNeg (Real.sin qz128)) 240559 1048576 1 1048576 732407 1048576 3891513 4597940224 176187095513 1099511627776 15029662819193 77140636293136384 qz402 (@Enclosure.Real.IsNear.neg (Real.sin qz128) Bool.false 732407 1048576 3891513 4597940224 (@Enclosure.Real.IsNear.recentre' (Real.sin qz128) Bool.false 732407 1048576 7783026 9195880448 732407 1048576 3891513 4597940224 (ep507 rfl rfl) rfl)) rfl)

noncomputable def ep509 := @ep464 180513789687 1099511627776 15030924698967 77140636293136384 Bool.true 176187095513 1099511627776 15029662819193 77140636293136384 Bool.false ep465 1492371718685 549755813888 104274389903813 19285159073284096 Bool.true 78056863576127252201472 141984607719 1099511627776 416630800558127 77140636293136384 (ep466 (BSN.head_sum_c_succ qz5 18 19 rfl rfl) (ep495 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep496 ep508) rfl rfl

noncomputable abbrev qz403 := (@Nat.cast Real Real.instNatCast 20)

noncomputable abbrev qz129 := (@Inv.inv Real Real.instInv (Real.sqrt qz403))

noncomputable abbrev qz564 := (Real.log (Enclosure.sfrac Bool.false 20 1))

noncomputable abbrev qz130 := (@HMul.hMul Real Real Real qz267 qz284 qz564)

noncomputable def ep510 := @Enclosure.Complex.IsNear.of_eq qz119 (Complex.mk (@HMul.hMul Real Real Real qz0 qz129 (Real.cos qz130)) (@HMul.hMul Real Real Real qz0 qz129 (@Neg.neg Real Real.instNeg (Real.sin qz130)))) Bool.false 53232669415 274877906944 3665700761005 19285159073284096 Bool.true 61455028307 549755813888 7317933309257 38570318146568192 (BSN.cpow_neg_s_mk qz13 117628 1000 20 qz14 rfl)

noncomputable abbrev qz404 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 20) qz15)

noncomputable def ep511 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz403) 4689375 1048576 1 1048576 117234 117235 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz403) (Real.sqrt qz404) Bool.false 4689375 1048576 1 1048576 (BSN.sqrt_natCast_div_one 20) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz404) Bool.false 4689375 1048576 1 1048576 4689375 1048576 1 1048576 (BSN.sqrt_enclosure 20 1 2344687 2344688 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep512 := BSN.log_dyadic_bound 4 36 3 2 25194240 524288 140318 104448 768 116991 40 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 4) (BSN.artanhQ 36) 0 2 104448 25194240 768 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep513 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz564 117628 1000 0 1 3372893643545847 1125899906842624 125000000070159 17539750000000000000 99186683375752722729 281474976710656000 3675875002063165713 4384937500000000000000 qz17 (BSN.isNear_log_sfrac 20 1 3372893643545847 1125899906842624 125000000070159 17539750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz404) Bool.false 56587765202795681021952 18889465931478580854784 1000000000561272 140318000000000000000 3372893643545847 1125899906842624 125000000070159 17539750000000000000 (BSN.log_rat_reduce_isNear 20 1 4 40 32 116991 524288 24973259072661432 36028797018963968 140318 1000000000000000 rfl rfl rfl rfl (ep512 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep514 := nat_lit 1597412211925920084298729158874997776

noncomputable def ep515 := BSN.cos_dyadic_bound_f 1124227618 2147483648 2 1 1048576 280911 ep514 ep77 ep514 ep514 ep78 ep514 908140 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1124227618) qz292 0 1 ep514 ep77 ep514 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1124227618) qz293 0 1 ep514 ep78 ep514 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz405 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 369499189) qz32)

noncomputable def ep516 := @Enclosure.Real.IsNear.cos_image qz130 qz405 Bool.false 369499189 1048576 55 65536 Bool.false 908140 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz130 Bool.false 99186683375752722729 281474976710656000 3675875002063165713 4384937500000000000000 369499189 1048576 55 65536 (ep513 rfl) rfl) (Enclosure.sfrac_false_div 369499189 1048576) (BSN.cos_reduce0 qz405 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 79110485702477126565888) qz33) 226375608064910080 72057594037927936 Bool.false 908140 1048576 56 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q0 369499189 1048576 226375608064910080 72057594037927936 56 79110485702477126565888 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 908140 1048576 79110485702477126565888 151115727451828646838272 1124227618 2147483648 280911 280636 (ep515 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep517 := BSN.sin_dyadic_bound_f 1124227618 2147483648 2 1 1048576 280911 ep514 ep81 ep514 ep514 ep82 ep514 524206 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1124227618) qz287 0 1 ep514 ep81 ep514 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1124227618) qz288 0 1 ep514 ep82 ep514 rfl rfl rfl rfl) rfl rfl

noncomputable def ep518 := @Enclosure.Real.IsNear.sin_image qz130 qz405 Bool.false 369499189 1048576 55 65536 Bool.false 524206 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz130 Bool.false 99186683375752722729 281474976710656000 3675875002063165713 4384937500000000000000 369499189 1048576 55 65536 (ep513 rfl) rfl) (Enclosure.sfrac_false_div 369499189 1048576) (BSN.sin_reduce0 qz405 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 79110485702477126565888) qz33) 226375608064910080 72057594037927936 Bool.false 524206 1048576 56 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q0 369499189 1048576 226375608064910080 72057594037927936 56 79110485702477126565888 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 524206 1048576 79110485702477126565888 151115727451828646838272 1124227618 2147483648 280911 280636 (ep517 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz406 := (@Enclosure.Real.IsNear.recentre' qz129 Bool.false 234469 1048576 1 1048576 234469 1048576 1 1048576 (ep511 rfl rfl) rfl)

noncomputable def ep519 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz129 (Real.cos qz130)) (@HMul.hMul Real Real Real qz0 qz129 (@Neg.neg Real Real.instNeg (Real.sin qz130))) Bool.false 53232669415 274877906944 3665700761005 19285159073284096 Bool.true 61455028307 549755813888 7317933309257 38570318146568192 (@Enclosure.Real.IsNear.mulLit_ff qz129 (Real.cos qz130) 234469 1048576 1 1048576 227035 262144 3891513 4597940224 53232669415 274877906944 3665700761005 19285159073284096 qz406 (@Enclosure.Real.IsNear.recentre' (Real.cos qz130) Bool.false 908140 1048576 7783026 9195880448 227035 262144 3891513 4597940224 (ep516 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz129 (@Neg.neg Real Real.instNeg (Real.sin qz130)) 234469 1048576 1 1048576 262103 524288 3891513 4597940224 61455028307 549755813888 7317933309257 38570318146568192 qz406 (@Enclosure.Real.IsNear.neg (Real.sin qz130) Bool.false 262103 524288 3891513 4597940224 (@Enclosure.Real.IsNear.recentre' (Real.sin qz130) Bool.false 524206 1048576 7783026 9195880448 262103 524288 3891513 4597940224 (ep518 rfl rfl) rfl)) rfl)

noncomputable def ep520 := @ep462 53232669415 274877906944 3665700761005 19285159073284096 Bool.true 61455028307 549755813888 7317933309257 38570318146568192 Bool.false 439484983914226945884160 1598837057515 549755813888 53970045332409 9642579536642048 Bool.true 145627381784976979656704 264894664333 1099511627776 431266667176641 77140636293136384 (ep463 (BSN.head_sum_c_succ qz5 19 20 rfl rfl) (ep509 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep510 ep519) rfl rfl

noncomputable abbrev qz407 := (@Nat.cast Real Real.instNatCast 21)

noncomputable abbrev qz131 := (@Inv.inv Real Real.instInv (Real.sqrt qz407))

noncomputable abbrev qz565 := (Real.log (Enclosure.sfrac Bool.false 21 1))

noncomputable abbrev qz132 := (@HMul.hMul Real Real Real qz267 qz284 qz565)

noncomputable def ep521 := @Enclosure.Complex.IsNear.of_eq qz118 (Complex.mk (@HMul.hMul Real Real Real qz0 qz131 (Real.cos qz132)) (@HMul.hMul Real Real Real qz0 qz131 (@Neg.neg Real Real.instNeg (Real.sin qz132)))) Bool.false 119941018377 549755813888 423364672671 2268842243915776 Bool.false 309018709 68719476736 52390912007 283605280489472 (BSN.cpow_neg_s_mk qz13 117628 1000 21 qz14 rfl)

noncomputable abbrev qz408 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 21) qz15)

noncomputable def ep522 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz407) 4805179 1048576 1 1048576 114408 114410 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz407) (Real.sqrt qz408) Bool.false 4805179 1048576 1 1048576 (BSN.sqrt_natCast_div_one 21) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz408) Bool.false 4805179 1048576 1 1048576 4805179 1048576 1 1048576 (BSN.sqrt_enclosure 21 1 2402589 2402590 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep523 := BSN.log_dyadic_bound 5 37 3 2 28112415 524288 140318 173000 1875 142571 42 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 5) (BSN.artanhQ 37) 0 2 173000 28112415 1875 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep524 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz565 117628 1000 0 1 3427826275261687 1125899906842624 125000000070159 17539750000000000000 100802087276620429609 281474976710656000 3675875002063165713 4384937500000000000000 qz17 (BSN.isNear_log_sfrac 21 1 3427826275261687 1125899906842624 125000000070159 17539750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz408) Bool.false 57509381830540779323392 18889465931478580854784 1000000000561272 140318000000000000000 3427826275261687 1125899906842624 125000000070159 17539750000000000000 (BSN.log_rat_reduce_isNear 21 1 4 42 32 142571 524288 24973259072661432 36028797018963968 140318 1000000000000000 rfl rfl rfl rfl (ep523 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep525 := nat_lit 7913818001284369362447312289298858253083571839962648794813624305435354379386880

noncomputable def ep526 := nat_lit 15083860056560414348089130265547078450048289327720068446939187026856698249216

noncomputable def ep527 := nat_lit 20702244706129393373655578356305171583442609969562057208931114497144350625038336

noncomputable def ep528 := BSN.sin_dyadic_bound_f 3329002044 2147483648 3 2 1048576 280911 ep525 ep59 ep526 ep527 ep62 ep526 1048353 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3329002044) qz287 0 2 ep525 ep59 ep526 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3329002044) qz288 0 2 ep527 ep62 ep526 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz409 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 375517037) qz32)

noncomputable def ep529 := @Enclosure.Real.IsNear.cos_image qz132 qz409 Bool.false 375517037 1048576 55 65536 Bool.false 1048353 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz132 Bool.false 100802087276620429609 281474976710656000 3675875002063165713 4384937500000000000000 375517037 1048576 55 65536 (ep524 rfl) rfl) (Enclosure.sfrac_false_div 375517037 1048576) (BSN.cos_reduce3 qz409 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 234257693227576778031104) qz33) 226375608064910080 72057594037927936 Bool.false 1048353 1048576 56 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q3 375517037 1048576 226375608064910080 72057594037927936 56 234257693227576778031104 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1048353 1048576 234257693227576778031104 151115727451828646838272 3329002044 2147483648 280911 280636 (ep528 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep530 := nat_lit 4403269494072009829958768663061831064357561373013791583095097586142688743325696

noncomputable def ep531 := nat_lit 13179640762102908661180127728654399036172587540385934612391414384374352833478656

noncomputable def ep532 := BSN.cos_dyadic_bound_f 3329002044 2147483648 3 2 1048576 280911 ep530 ep66 ep526 ep531 ep68 ep526 21608 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3329002044) qz292 0 2 ep530 ep66 ep526 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3329002044) qz293 0 2 ep531 ep68 ep526 rfl rfl rfl rfl) rfl rfl

noncomputable def ep533 := @Enclosure.Real.IsNear.sin_image qz132 qz409 Bool.false 375517037 1048576 55 65536 Bool.true 21608 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz132 Bool.false 100802087276620429609 281474976710656000 3675875002063165713 4384937500000000000000 375517037 1048576 55 65536 (ep524 rfl) rfl) (Enclosure.sfrac_false_div 375517037 1048576) (BSN.sin_reduce3 qz409 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 234257693227576778031104) qz33) 226375608064910080 72057594037927936 Bool.false 21608 1048576 56 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q3 375517037 1048576 226375608064910080 72057594037927936 56 234257693227576778031104 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 21608 1048576 234257693227576778031104 151115727451828646838272 3329002044 2147483648 280911 280636 (ep532 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz410 := (@Enclosure.Real.IsNear.recentre' qz131 Bool.false 228818 1048576 2 1048576 114409 524288 1 524288 (ep522 rfl rfl) rfl)

noncomputable def ep534 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz131 (Real.cos qz132)) (@HMul.hMul Real Real Real qz0 qz131 (@Neg.neg Real Real.instNeg (Real.sin qz132))) Bool.false 119941018377 549755813888 423364672671 2268842243915776 Bool.false 309018709 68719476736 52390912007 283605280489472 (@Enclosure.Real.IsNear.mulLit_ff qz131 (Real.cos qz132) 114409 524288 1 524288 1048353 1048576 3891513 4597940224 119941018377 549755813888 423364672671 2268842243915776 qz410 (@Enclosure.Real.IsNear.recentre' (Real.cos qz132) Bool.false 1048353 1048576 7783026 9195880448 1048353 1048576 3891513 4597940224 (ep529 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz131 (@Neg.neg Real Real.instNeg (Real.sin qz132)) 114409 524288 1 524288 2701 131072 3891513 4597940224 309018709 68719476736 52390912007 283605280489472 qz410 (@Enclosure.Real.IsNear.neg (Real.sin qz132) Bool.true 2701 131072 3891513 4597940224 (@Enclosure.Real.IsNear.recentre' (Real.sin qz132) Bool.true 21608 1048576 7783026 9195880448 2701 131072 3891513 4597940224 (ep533 rfl rfl) rfl)) rfl)

noncomputable def ep535 := @ep460 119941018377 549755813888 423364672671 2268842243915776 Bool.false 309018709 68719476736 52390912007 283605280489472 Bool.false 944908240004857091588096 429694518973 137438953472 223077380765043 38570318146568192 Bool.true 17863653059376294395904 259950364989 1099511627776 445516995242545 77140636293136384 (ep461 (BSN.head_sum_c_succ qz5 20 21 rfl rfl) (ep520 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep521 ep534) rfl rfl

noncomputable abbrev qz411 := (@Nat.cast Real Real.instNatCast 22)

noncomputable abbrev qz133 := (@Inv.inv Real Real.instInv (Real.sqrt qz411))

noncomputable abbrev qz566 := (Real.log (Enclosure.sfrac Bool.false 22 1))

noncomputable abbrev qz134 := (@HMul.hMul Real Real Real qz267 qz284 qz566)

noncomputable def ep536 := @Enclosure.Complex.IsNear.of_eq qz117 (Complex.mk (@HMul.hMul Real Real Real qz0 qz133 (Real.cos qz134)) (@HMul.hMul Real Real Real qz0 qz133 (@Neg.neg Real Real.instNeg (Real.sin qz134)))) Bool.false 39476365731 274877906944 3492304339713 19285159073284096 Bool.false 173253768759 1099511627776 13974034124997 77140636293136384 (BSN.cpow_neg_s_mk qz13 117628 1000 22 qz14 rfl)

noncomputable abbrev qz412 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 22) qz15)

noncomputable def ep537 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz411) 4918257 1048576 1 1048576 111778 111779 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz411) (Real.sqrt qz412) Bool.false 4918257 1048576 1 1048576 (BSN.sqrt_natCast_div_one 22) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz412) Bool.false 4918257 1048576 1 1048576 4918257 1048576 1 1048576 (BSN.sqrt_enclosure 22 1 2459128 2459129 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep538 := BSN.log_dyadic_bound 6 38 4 3 316148320320 524288 140318 2667271104 699840 166961 44 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 6) (BSN.artanhQ 38) 0 3 2667271104 316148320320 699840 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep539 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz566 117628 1000 0 1 3480203401436407 1125899906842624 125000000070159 17539750000000000000 102342341426040420649 281474976710656000 3675875002063165713 4384937500000000000000 qz17 (BSN.isNear_log_sfrac 22 1 3480203401436407 1125899906842624 125000000070159 17539750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz412) Bool.false 58388124189833310502912 18889465931478580854784 1000000000561272 140318000000000000000 3480203401436407 1125899906842624 125000000070159 17539750000000000000 (BSN.log_rat_reduce_isNear 22 1 4 44 32 166961 524288 24973259072661432 36028797018963968 140318 1000000000000000 rfl rfl rfl rfl (ep538 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep540 := nat_lit 6345928190718815998808025979026810001

noncomputable def ep541 := BSN.sin_dyadic_bound_f 1587171251 2147483648 2 1 1048576 280911 ep540 ep81 ep540 ep540 ep82 ep540 706332 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1587171251) qz287 0 1 ep540 ep81 ep540 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1587171251) qz288 0 1 ep540 ep82 ep540 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz413 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 381254931) qz32)

noncomputable def ep542 := @Enclosure.Real.IsNear.cos_image qz134 qz413 Bool.false 381254931 1048576 55 65536 Bool.false 706332 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz134 Bool.false 102342341426040420649 281474976710656000 3675875002063165713 4384937500000000000000 381254931 1048576 55 65536 (ep539 rfl) rfl) (Enclosure.sfrac_false_div 381254931 1048576) (BSN.cos_reduce3 qz413 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 111687247787817122660352) qz33) 226375608064910080 72057594037927936 Bool.false 706332 1048576 57 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q3 381254931 1048576 226375608064910080 72057594037927936 57 111687247787817122660352 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 706332 1048576 111687247787817122660352 151115727451828646838272 1587171251 2147483648 280911 280636 (ep541 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep543 := nat_lit 226778054634653026915788523511384288497917804836635704053432152254249028622881

noncomputable def ep544 := nat_lit 40270804601759785521034413357259544707940729362032626791610750734153620001

noncomputable def ep545 := nat_lit 680253622294755561176323501707438346404337533051183046906713235261278778628641

noncomputable def ep546 := BSN.cos_dyadic_bound_f 1587171251 2147483648 3 2 1048576 280911 ep543 ep66 ep544 ep545 ep68 ep544 774987 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1587171251) qz292 0 2 ep543 ep66 ep544 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1587171251) qz293 0 2 ep545 ep68 ep544 rfl rfl rfl rfl) rfl rfl

noncomputable def ep547 := @Enclosure.Real.IsNear.sin_image qz134 qz413 Bool.false 381254931 1048576 55 65536 Bool.true 774987 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz134 Bool.false 102342341426040420649 281474976710656000 3675875002063165713 4384937500000000000000 381254931 1048576 55 65536 (ep539 rfl) rfl) (Enclosure.sfrac_false_div 381254931 1048576) (BSN.sin_reduce3 qz413 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 111687247787817122660352) qz33) 226375608064910080 72057594037927936 Bool.false 774987 1048576 57 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q3 381254931 1048576 226375608064910080 72057594037927936 57 111687247787817122660352 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 774987 1048576 111687247787817122660352 151115727451828646838272 1587171251 2147483648 280911 280636 (ep546 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz414 := (@Enclosure.Real.IsNear.recentre' qz133 Bool.false 223557 1048576 1 1048576 223557 1048576 1 1048576 (ep537 rfl rfl) rfl)

noncomputable def ep548 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz133 (Real.cos qz134)) (@HMul.hMul Real Real Real qz0 qz133 (@Neg.neg Real Real.instNeg (Real.sin qz134))) Bool.false 39476365731 274877906944 3492304339713 19285159073284096 Bool.false 173253768759 1099511627776 13974034124997 77140636293136384 (@Enclosure.Real.IsNear.mulLit_ff qz133 (Real.cos qz134) 223557 1048576 1 1048576 176583 262144 3891513 4597940224 39476365731 274877906944 3492304339713 19285159073284096 qz414 (@Enclosure.Real.IsNear.recentre' (Real.cos qz134) Bool.false 706332 1048576 7783026 9195880448 176583 262144 3891513 4597940224 (ep542 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz133 (@Neg.neg Real Real.instNeg (Real.sin qz134)) 223557 1048576 1 1048576 774987 1048576 3891513 4597940224 173253768759 1099511627776 13974034124997 77140636293136384 qz414 (@Enclosure.Real.IsNear.neg (Real.sin qz134) Bool.true 774987 1048576 3891513 4597940224 (@Enclosure.Real.IsNear.recentre' (Real.sin qz134) Bool.true 774987 1048576 7783026 9195880448 774987 1048576 3891513 4597940224 (ep547 rfl rfl) rfl)) rfl)

noncomputable def ep549 := @ep458 39476365731 274877906944 3492304339713 19285159073284096 Bool.false 173253768759 1099511627776 13974034124997 77140636293136384 Bool.false 123539120393553700716544 898865403677 274877906944 230061989444469 38570318146568192 Bool.true 95323915643485924884480 43348298115 549755813888 229745514683771 38570318146568192 (ep459 (BSN.head_sum_c_succ qz5 21 22 rfl rfl) (ep535 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep536 ep548) rfl rfl

noncomputable abbrev qz415 := (@Nat.cast Real Real.instNatCast 23)

noncomputable abbrev qz135 := (@Inv.inv Real Real.instInv (Real.sqrt qz415))

noncomputable abbrev qz567 := (Real.log (Enclosure.sfrac Bool.false 23 1))

noncomputable abbrev qz136 := (@HMul.hMul Real Real Real qz267 qz284 qz567)

noncomputable def ep550 := @Enclosure.Complex.IsNear.of_eq qz116 (Complex.mk (@HMul.hMul Real Real Real qz0 qz135 (Real.cos qz136)) (@HMul.hMul Real Real Real qz0 qz135 (@Neg.neg Real Real.instNeg (Real.sin qz136)))) Bool.true 71126972973 1099511627776 13636518988401 77140636293136384 Bool.false 54487803387 274877906944 3420908127719 19285159073284096 (BSN.cpow_neg_s_mk qz13 117628 1000 23 qz14 rfl)

noncomputable abbrev qz416 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 23) qz15)

noncomputable def ep551 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz415) 5028793 1048576 1 1048576 109321 109322 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz415) (Real.sqrt qz416) Bool.false 5028793 1048576 1 1048576 (BSN.sqrt_natCast_div_one 23) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz416) Bool.false 5028793 1048576 1 1048576 5028793 1048576 1 1048576 (BSN.sqrt_enclosure 23 1 2514396 2514397 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep552 := BSN.log_dyadic_bound 7 39 4 3 369468094905 524288 140318 4046006391 1764735 190266 46 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 7) (BSN.artanhQ 39) 0 3 4046006391 369468094905 1764735 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep553 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz567 117628 1000 0 1 3530250507853047 1125899906842624 125000000070159 17539750000000000000 103814076684434553129 281474976710656000 3675875002063165713 4384937500000000000000 qz17 (BSN.isNear_log_sfrac 23 1 3530250507853047 1125899906842624 125000000070159 17539750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz416) Bool.false 59227775304360265777152 18889465931478580854784 1000000000561272 140318000000000000000 3530250507853047 1125899906842624 125000000070159 17539750000000000000 (BSN.log_rat_reduce_isNear 23 1 4 46 32 190266 524288 24973259072661432 36028797018963968 140318 1000000000000000 rfl rfl rfl rfl (ep552 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep554 := nat_lit 1889939234348551494449251180981700019574654796900778578295799205124371837306401

noncomputable def ep555 := nat_lit 2789684872023212454529055894750282457004662366954991198079071921842688050721

noncomputable def ep556 := nat_lit 5664238333301608058438695431155599493809955065968425752491239471529430135817761

noncomputable def ep557 := BSN.cos_dyadic_bound_f 2695841741 2147483648 3 2 1048576 280911 ep554 ep66 ep555 ep556 ep68 ep555 325311 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2695841741) qz292 0 2 ep554 ep66 ep555 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2695841741) qz293 0 2 ep556 ep68 ep555 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz417 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 96684393) qz537)

noncomputable def ep558 := @Enclosure.Real.IsNear.cos_image qz136 qz417 Bool.false 96684393 262144 55 65536 Bool.true 325311 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz136 Bool.false 103814076684434553129 281474976710656000 3675875002063165713 4384937500000000000000 96684393 262144 55 65536 (ep553 rfl) rfl) (Enclosure.sfrac_false_div 96684393 262144) (BSN.cos_reduce2 qz417 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 47425749462100545110016) qz299) 226375608064910080 72057594037927936 Bool.false 325311 1048576 58 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q2 96684393 262144 226375608064910080 72057594037927936 58 47425749462100545110016 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 325311 1048576 47425749462100545110016 37778931862957161709568 2695841741 2147483648 280911 280636 (ep557 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep559 := nat_lit 3399658873929774120045028881051259809268774904527837447973975311686395156710945

noncomputable def ep560 := nat_lit 8899351846689942256143933359876084757440212439454980473230188271305194391684641

noncomputable def ep561 := BSN.sin_dyadic_bound_f 2695841741 2147483648 3 2 1048576 280911 ep559 ep59 ep555 ep560 ep62 ep555 996836 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2695841741) qz287 0 2 ep559 ep59 ep555 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2695841741) qz288 0 2 ep560 ep62 ep555 rfl rfl rfl rfl) rfl rfl

noncomputable def ep562 := @Enclosure.Real.IsNear.sin_image qz136 qz417 Bool.false 96684393 262144 55 65536 Bool.true 996836 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz136 Bool.false 103814076684434553129 281474976710656000 3675875002063165713 4384937500000000000000 96684393 262144 55 65536 (ep553 rfl) rfl) (Enclosure.sfrac_false_div 96684393 262144) (BSN.sin_reduce2 qz417 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 47425749462100545110016) qz299) 226375608064910080 72057594037927936 Bool.false 996836 1048576 58 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q2 96684393 262144 226375608064910080 72057594037927936 58 47425749462100545110016 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 996836 1048576 47425749462100545110016 37778931862957161709568 2695841741 2147483648 280911 280636 (ep561 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz418 := (@Enclosure.Real.IsNear.recentre' qz135 Bool.false 218643 1048576 1 1048576 218643 1048576 1 1048576 (ep551 rfl rfl) rfl)

noncomputable def ep563 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz135 (Real.cos qz136)) (@HMul.hMul Real Real Real qz0 qz135 (@Neg.neg Real Real.instNeg (Real.sin qz136))) Bool.true 71126972973 1099511627776 13636518988401 77140636293136384 Bool.false 54487803387 274877906944 3420908127719 19285159073284096 (@Enclosure.Real.IsNear.mulLit_ft qz135 (Real.cos qz136) 218643 1048576 1 1048576 325311 1048576 3891513 4597940224 71126972973 1099511627776 13636518988401 77140636293136384 qz418 (@Enclosure.Real.IsNear.recentre' (Real.cos qz136) Bool.true 325311 1048576 7783026 9195880448 325311 1048576 3891513 4597940224 (ep558 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz135 (@Neg.neg Real Real.instNeg (Real.sin qz136)) 218643 1048576 1 1048576 249209 262144 3891513 4597940224 54487803387 274877906944 3420908127719 19285159073284096 qz418 (@Enclosure.Real.IsNear.neg (Real.sin qz136) Bool.true 249209 262144 3891513 4597940224 (@Enclosure.Real.IsNear.recentre' (Real.sin qz136) Bool.true 996836 1048576 7783026 9195880448 249209 262144 3891513 4597940224 (ep562 rfl rfl) rfl)) rfl)

noncomputable def ep564 := @ep456 71126972973 1099511627776 13636518988401 77140636293136384 Bool.false 54487803387 274877906944 3420908127719 19285159073284096 Bool.false 968761729690348908707840 3524334641735 1099511627776 473760497877339 77140636293136384 Bool.false 18039497242553767428096 65627308659 549755813888 236587330939209 38570318146568192 (ep457 (BSN.head_sum_c_succ qz5 22 23 rfl rfl) (ep549 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep550 ep563) rfl rfl

noncomputable def ep565 := @Enclosure.Complex.IsNear.mul qz111 (@HAdd.hAdd Complex Complex Complex qz4 qz112 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))) Bool.true 867034953451435785430253 ep308 ep449 ep310 Bool.true

noncomputable def ep566 := nat_lit 1671665685322634233186831

noncomputable abbrev qz137 := (Complex.re qz388)

noncomputable abbrev qz138 := (Complex.im qz388)

noncomputable def ep567 := @Enclosure.Real.IsNear.subLit_tt_n (@HMul.hMul Real Real Real qz0 qz137 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz112 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz138 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz112 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))))) 2153151630238222905907 21064844233455723085824 ep566

noncomputable def ep568 := nat_lit 19212549285475260987718238208

noncomputable def ep569 := nat_lit 3803374653262838890496000

noncomputable def ep570 := nat_lit 28272157173076087942610261

noncomputable def ep571 := nat_lit 800522886894802541154926592000

noncomputable def ep572 := nat_lit 8117313884184901508797531931662491127415570432

noncomputable def ep573 := @Enclosure.Real.IsNear.mulLit_tf qz137 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz112 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))))) 224384146987 1099511627776 13400581075267 77140636293136384 124745761093

noncomputable abbrev qz419 := (@Nat.cast Real Real.instNatCast 24)

noncomputable abbrev qz139 := (@Inv.inv Real Real.instInv (Real.sqrt qz419))

noncomputable abbrev qz420 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) qz536 (Real.log (Enclosure.sfrac Bool.false 24 1)))

noncomputable abbrev qz140 := (Real.cos qz420)

noncomputable abbrev qz141 := (Real.sin qz420)

noncomputable abbrev qz421 := (@Neg.neg Real Real.instNeg qz141)

noncomputable def ep574 := @Enclosure.Complex.IsNear.of_eq qz111 (Complex.mk (@HMul.hMul Real Real Real qz0 qz139 qz140) (@HMul.hMul Real Real Real qz0 qz139 qz421)) Bool.true 224384146987 1099511627776 13400581075267 77140636293136384 Bool.true 4829361957 1099511627776 13328614077837 77140636293136384 (BSN.cpow_neg_s_mk qz13 117628 1000 24 qz14 rfl)

noncomputable abbrev qz422 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 24) qz15)

noncomputable def ep575 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz419) 5136953 1048576 1 1048576 107019 107020 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz419) (Real.sqrt qz422) Bool.false 5136953 1048576 1 1048576 (BSN.sqrt_natCast_div_one 24) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz422) Bool.false 5136953 1048576 1 1048576 5136953 1048576 1 1048576 (BSN.sqrt_enclosure 24 1 2568476 2568477 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep576 := BSN.log_dyadic_bound 8 40 4 3 430080000000 524288 140318 5875957760 3932160 212580 48 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 8) (BSN.artanhQ 40) 0 3 5875957760 430080000000 3932160 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz423 := (Real.log (Enclosure.sfrac Bool.false 24 1))

noncomputable abbrev qz142 := qz423

noncomputable abbrev qz424 := (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 24) qz15))

noncomputable def ep577 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz142 117628 1000 0 1 3578169457974519 1125899906842624 125000000070159 17539750000000000000 105223229250656680233 281474976710656000 3675875002063165713 4384937500000000000000 qz17 (BSN.isNear_log_sfrac 24 1 3578169457974519 1125899906842624 125000000070159 17539750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz424 Bool.false 60031721881041427759104 18889465931478580854784 1000000000561272 140318000000000000000 3578169457974519 1125899906842624 125000000070159 17539750000000000000 (BSN.log_rat_reduce_isNear 24 1 4 48 32 212580 524288 24973259072661432 36028797018963968 140318 1000000000000000 rfl rfl rfl rfl (ep576 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep578 := nat_lit 7895195413444471549324195897393064085201240996571885394010716372136106978766785

noncomputable def ep579 := nat_lit 15013088115918029551985777101937539547801571258815252237345280657083884171201

noncomputable def ep580 := nat_lit 20653585844928796295622059901673935635306809589935903718786650520245001512873921

noncomputable def ep581 := BSN.sin_dyadic_bound_f 3327045607 2147483648 3 2 1048576 280911 ep578 ep59 ep579 ep580 ep62 ep579 1048333 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3327045607) qz287 0 2 ep578 ep59 ep579 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3327045607) qz288 0 2 ep580 ep62 ep579 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz143 := qz420

noncomputable abbrev qz425 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 391987075) qz32)

noncomputable def ep582 := @Enclosure.Real.IsNear.cos_image qz143 qz425 Bool.false 391987075 1048576 55 65536 Bool.true 1048333 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz143 Bool.false 105223229250656680233 281474976710656000 3675875002063165713 4384937500000000000000 391987075 1048576 55 65536 (ep577 rfl) rfl) (Enclosure.sfrac_false_div 391987075 1048576) (BSN.cos_reduce1 qz425 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 234120021191358351933440) qz33) 226375608064910080 72057594037927936 Bool.false 1048333 1048576 59 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q1 391987075 1048576 226375608064910080 72057594037927936 59 234120021191358351933440 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1048333 1048576 234120021191358351933440 151115727451828646838272 3327045607 2147483648 280911 280636 (ep581 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep583 := nat_lit 4392892157742892207203213621708118953799712363099409775444773664812096714502081

noncomputable def ep584 := nat_lit 13148650296996840562505669310920481782303533946780598821859630433122122375163841

noncomputable def ep585 := BSN.cos_dyadic_bound_f 3327045607 2147483648 3 2 1048576 280911 ep583 ep66 ep579 ep584 ep68 ep579 22563 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3327045607) qz292 0 2 ep583 ep66 ep579 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3327045607) qz293 0 2 ep584 ep68 ep579 rfl rfl rfl rfl) rfl rfl

noncomputable def ep586 := @Enclosure.Real.IsNear.sin_image qz143 qz425 Bool.false 391987075 1048576 55 65536 Bool.false 22563 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz143 Bool.false 105223229250656680233 281474976710656000 3675875002063165713 4384937500000000000000 391987075 1048576 55 65536 (ep577 rfl) rfl) (Enclosure.sfrac_false_div 391987075 1048576) (BSN.sin_reduce1 qz425 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 234120021191358351933440) qz33) 226375608064910080 72057594037927936 Bool.false 22563 1048576 59 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q1 391987075 1048576 226375608064910080 72057594037927936 59 234120021191358351933440 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 22563 1048576 234120021191358351933440 151115727451828646838272 3327045607 2147483648 280911 280636 (ep585 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz426 := (@Enclosure.Real.IsNear.recentre' qz139 Bool.false 214039 1048576 1 1048576 214039 1048576 1 1048576 (ep575 rfl rfl) rfl)

noncomputable def ep587 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz139 qz140) (@HMul.hMul Real Real Real qz0 qz139 qz421) Bool.true 224384146987 1099511627776 13400581075267 77140636293136384 Bool.true 4829361957 1099511627776 13328614077837 77140636293136384 (@Enclosure.Real.IsNear.mulLit_ft qz139 qz140 214039 1048576 1 1048576 1048333 1048576 3891513 4597940224 224384146987 1099511627776 13400581075267 77140636293136384 qz426 (@Enclosure.Real.IsNear.recentre' qz140 Bool.true 1048333 1048576 7783026 9195880448 1048333 1048576 3891513 4597940224 (ep582 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz139 qz421 214039 1048576 1 1048576 22563 1048576 3891513 4597940224 4829361957 1099511627776 13328614077837 77140636293136384 qz426 (@Enclosure.Real.IsNear.neg qz141 Bool.false 22563 1048576 3891513 4597940224 (@Enclosure.Real.IsNear.recentre' qz141 Bool.false 22563 1048576 7783026 9195880448 22563 1048576 3891513 4597940224 (ep586 rfl rfl) rfl)) rfl)

noncomputable def ep588 := @ep573 249058734912 0 1 2153151630238222905907 21064844233455723085824 ep566 ep568 (@Enclosure.Complex.IsNear.re_isNear qz111 Bool.true 224384146987 1099511627776 13400581075267 77140636293136384 Bool.true 4829361957 1099511627776 13328614077837 77140636293136384 (ep574 ep587))

noncomputable def ep589 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz112 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))) Bool.false 124745761093 249058734912 0 1 Bool.false

noncomputable def ep590 := @Enclosure.Complex.IsNear.addLitP qz112 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) Bool.false 431643637 864787274 0 1 Bool.true 88221000

noncomputable def ep591 := @ep590 432393637 0 1 Bool.false 1 576 0 1 Bool.false 29407 72000 0 1 Bool.false 249491522186 124745761093 249058734912 0 1 Bool.false 6363487683259 6363487683259 31132341864000 0 1

noncomputable abbrev qz144 := (@HDiv.hDiv Complex Complex Complex qz361 qz389 (@HSub.hSub Complex Complex Complex qz353 qz272 (1 : Complex)))

noncomputable def ep592 := @Enclosure.Complex.IsNear.addLitP qz144 qz89 Bool.true 48000000 55346385536 0 1 Bool.true 11292288000 55346385536 0 1

noncomputable def ep593 := @Enclosure.Complex.IsNear.of_eq qz144 (Complex.mk (Enclosure.sfrac Bool.true 48000000 55346385536) (Enclosure.sfrac Bool.true 11292288000 55346385536)) Bool.true 48000000 55346385536 0 1 Bool.true 11292288000 55346385536 0 1

noncomputable def ep594 := @ep592 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 55250385536 431643637 864787274 0 1 Bool.true 11292288000 88221000 432393637 0 1 (ep593 (BSN.N_div_s_sub_one_mk qz13 117628 1000 24 qz14 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 48000000 55346385536) (Enclosure.sfrac Bool.true 11292288000 55346385536) Bool.true 48000000 55346385536 0 1 Bool.true 11292288000 55346385536 0 1 (Enclosure.Real.IsNear.const Bool.true 48000000 55346385536) (Enclosure.Real.IsNear.const Bool.true 11292288000 55346385536))) qz90 rfl

noncomputable abbrev qz145 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)))

noncomputable abbrev qz427 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz559 qz560 1))

noncomputable abbrev qz146 := qz427

noncomputable def ep595 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz146)) Bool.false 1 576 0 1

noncomputable def ep596 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz146) Bool.false 0 1 0 1 Bool.false

noncomputable def ep597 := @ep596 0 1 0 1 Bool.false 1 576 0 1 Bool.false 29407 72000 0 1 Bool.false 1 1 576 0 1 Bool.false 29407 29407 72000 0

noncomputable def ep598 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep599 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz146 Bool.false 1 576 0 1 Bool.false 29407 72000 0 1

noncomputable abbrev qz147 := (Complex.re qz427)

noncomputable abbrev qz148 := (Complex.im qz427)

noncomputable def ep600 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz147) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz148) 1 576 0 1 0 1 0

noncomputable def ep601 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz147 1 24 0 1 1 24 0 1 1

noncomputable def ep602 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep603 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep604 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz10) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 1 1 6 2 Bool.false BSN.bern_real_1 EMRow38.d8 rfl) qz378

noncomputable def ep605 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz5 Bool.false 1 2 0 1 Bool.false 117628 1000 0 1 (BSN.ascPochhammer_one_eval qz5)

noncomputable def ep606 := ep605 (@Enclosure.Complex.IsNear.of_eq qz5 (Complex.mk qz84 qz13) Bool.false 1 2 0 1 Bool.false 117628 1000 0 1 (BSN.s_crit_mk qz13 Bool.false 117628 1000 qz14) (@Enclosure.Complex.IsNear.mk qz84 qz13 Bool.false 1 2 0 1 Bool.false 117628 1000 0 1 qz370 qz17))

noncomputable def ep607 := @ep603 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep604) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 117628 1000 0 1 ep606)

noncomputable def ep608 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 117628 1000 0 1 0 1 0

noncomputable def ep609 := @ep608 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep604) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 117628 1000 0 1 ep606)

noncomputable def ep610 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) 29407 3000 0 1 0 1 0 1 29407

noncomputable def ep611 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 117628 1000 0 1 29407 3000 0

noncomputable def ep612 := @ep611 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep604) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 117628 1000 0 1 ep606)

noncomputable def ep613 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep614 := @ep613 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep604) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 117628 1000 0 1 ep606)

noncomputable def ep615 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 29407 3000 0 1 (@ep602 1 24 0 1 (ep607 rfl) (ep609 rfl) rfl rfl) (@ep610 29407 3000 0 1 (ep612 rfl) (ep614 rfl) rfl rfl)

noncomputable def ep616 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 29407 3000 0 1 ep615

noncomputable abbrev qz149 := (@Enclosure.Complex.IsNear.re_isNear qz427 Bool.false 1 24 0 1 Bool.false 0 1 0 1 (@Enclosure.Complex.IsNear.of_eq qz427 (Complex.mk (Enclosure.sfrac Bool.false 1 24) qz283) Bool.false 1 24 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 24 1 24 EMRow38.d9 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 24) qz283 Bool.false 1 24 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 24) qz295)))

noncomputable def ep617 := @ep601 576 0 1 ep616 qz149

noncomputable def ep618 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz148 29407 3000 0 1 0 1 0 1 0

noncomputable def ep619 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 29407 3000 0 1 ep615

noncomputable abbrev qz150 := (@Enclosure.Complex.IsNear.im_isNear qz427 Bool.false 1 24 0 1 Bool.false 0 1 0 1 (@Enclosure.Complex.IsNear.of_eq qz427 (Complex.mk (Enclosure.sfrac Bool.false 1 24) qz283) Bool.false 1 24 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 24 1 24 EMRow38.d9 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 24) qz283 Bool.false 1 24 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 24) qz295)))

noncomputable def ep620 := @ep618 1 0 1 ep619 qz150

noncomputable def ep621 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz148) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz147) 0 1 0 1 29407 72000 0

noncomputable def ep622 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz148 1 24 0 1 0 1 0 1 0

noncomputable def ep623 := @ep622 1 0 1 ep616 qz150

noncomputable def ep624 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz147 29407 3000 0 1 1 24 0 1 29407

noncomputable def ep625 := @ep624 72000 0 1 ep619 qz149

noncomputable def ep626 := @ep597 1 (@ep598 0 1 0 1 (BSN.bern_sum_base qz5 24) qz105) (ep599 (@ep600 1 1 1 576 0 1 (ep617 rfl) (ep620 rfl) rfl rfl) (@ep621 1 29407 29407 72000 0 1 (ep623 rfl) (ep625 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep627 := ep591 (ep594 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep595 Bool.false 29407 72000 0 1 (BSN.bern_sum_succ qz5 24 0 1 1 rfl rfl) (ep626 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep628 := @Enclosure.Real.IsNear.mulLit_tf qz138 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz112 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))))) 4829361957 1099511627776 13328614077837 77140636293136384 6363487683259

noncomputable def ep629 := @ep628 31132341864000 0 1 3414620592374342264207 ep569 ep570 ep571 (@Enclosure.Complex.IsNear.im_isNear qz111 Bool.true 224384146987 1099511627776 13400581075267 77140636293136384 Bool.true 4829361957 1099511627776 13328614077837 77140636293136384 (ep574 ep587))

noncomputable def ep630 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz112 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))) Bool.false 124745761093 249058734912 0 1 Bool.false

noncomputable def ep631 := nat_lit 2633105529181965385728000

noncomputable def ep632 := nat_lit 85274432620975200934855153

noncomputable def ep633 := @Enclosure.Real.IsNear.addLit_tt (@HMul.hMul Real Real Real qz0 qz137 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz112 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz138 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz112 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))))) 109835827359257811937741 ep631 ep632

noncomputable def ep634 := nat_lit 2401568660684407623464779776000

noncomputable def ep635 := nat_lit 6404183095158420329239412736

noncomputable def ep636 := nat_lit 3518229358957310272832124177628047656813068288

noncomputable def ep637 := @Enclosure.Real.IsNear.mulLit_tf qz137 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz112 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))))) 224384146987 1099511627776 13400581075267 77140636293136384 6363487683259

noncomputable def ep638 := @ep637 31132341864000 0 1 109835827359257811937741 ep631 ep632 ep634 (@Enclosure.Complex.IsNear.re_isNear qz111 Bool.true 224384146987 1099511627776 13400581075267 77140636293136384 Bool.true 4829361957 1099511627776 13328614077837 77140636293136384 (ep574 ep587))

noncomputable def ep639 := @Enclosure.Real.IsNear.mulLit_tf qz138 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz112 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))))) 4829361957 1099511627776 13328614077837 77140636293136384 124745761093

noncomputable def ep640 := @ep639 249058734912 0 1 66938048102171659889 30426997226102711123968 554229369151550302731947 ep635 (@Enclosure.Complex.IsNear.im_isNear qz111 Bool.true 224384146987 1099511627776 13400581075267 77140636293136384 Bool.true 4829361957 1099511627776 13328614077837 77140636293136384 (ep574 ep587))

noncomputable abbrev qz428 := (ep627 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep641 := @ep565 751585529892647336282879 ep444 ep450 ep446 (@ep567 ep568 3414620592374342264207 ep569 ep570 ep571 ep572 867034953451435785430253 ep308 ep449 ep310 (ep588 (@ep589 6363487683259 31132341864000 0 1 qz428) rfl) (ep629 (@ep630 6363487683259 31132341864000 0 1 qz428) rfl) rfl rfl) (@ep633 ep634 66938048102171659889 30426997226102711123968 554229369151550302731947 ep635 ep636 751585529892647336282879 ep444 ep450 ep446 (ep638 (@ep630 6363487683259 31132341864000 0 1 qz428) rfl) (ep640 (@ep589 6363487683259 31132341864000 0 1 qz428) rfl) rfl rfl)

noncomputable def ep642 := @ep453 ep445 ep446 (@ep454 38570318146568192 (BSN.head_sum_c_eq qz5 24) (ep455 (BSN.head_sum_c_succ qz5 23 24 rfl rfl) (ep564 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep641 rfl rfl rfl

noncomputable def ep643 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz5 1 24) Bool.false ep307 ep308 ep309 ep310 Bool.false ep443 ep444 ep445 ep446 (@ep447 ep310 Bool.false ep443 ep444 ep445 ep446 (BSN.zetaApproximant_eq_folded' qz5 1 24 rfl) (ep642 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep644 := @Enclosure.Real.IsNear.mulLit_ff (Real.sin (@HSub.hSub Real Real Real qz356 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))))) qz66)) (Complex.im (zetaApproximant qz5 1 24)) 595 1048576 3222691

noncomputable def ep645 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz356 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))))) qz66)) Bool.false 595 1048576 6445382

noncomputable def ep646 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz356 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))))) qz66) qz357 Bool.false 118591747 1048576 45

noncomputable def ep647 := BSN.sin_dyadic_bound_f 1219174 2147483648 1 0 1048576 280911 0 1 1 0 1 1 595 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 1219174) qz287 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 1219174) qz288 0 0 rfl) rfl rfl

noncomputable def ep648 := @ep646 131072 Bool.false 595 1048576 1 140318 (@ep315 118591747 1048576 45 131072 ep440 rfl) (Enclosure.sfrac_false_div 118591747 1048576) (BSN.sin_reduce0 qz357 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 85791785793433370624) qz33) 226375608064910080 72057594037927936 Bool.false 595 1048576 18 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q0 118591747 1048576 226375608064910080 72057594037927936 18 85791785793433370624 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 595 1048576 85791785793433370624 151115727451828646838272 1219174 2147483648 280911 280636 (ep647 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep649 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz5 1 24) Bool.false ep307 ep308 ep309 ep310 Bool.false ep443 ep444 ep445 ep446 (@ep447 ep310 Bool.false ep443 ep444 ep445 ep446 (BSN.zetaApproximant_eq_folded' qz5 1 24 rfl) (ep642 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow38.d10 : Enclosure.Real.IsNear (hardyZApproximantEM 1 24 qz13) Bool.false ep291 ep292 ep293 ep294 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 24 qz13) ep295 Bool.false ep291 ep292 ep293 ep294 (@Eq.refl Real ep295) (@ep296 Bool.false ep291 ep292 ep293 ep294 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz356 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))))) qz66) (zetaApproximant qz5 1 24)) (@ep298 ep299 ep300 ep301 ep302 ep292 ep303 ep304 ep305 ep291 ep292 ep293 ep294 (@ep306 9195880448 ep307 ep308 ep309 ep310 ep297 ep299 ep300 ep301 (@ep311 18391760896 1048575 1048576 3222691 9195880448 (ep442 rfl rfl) rfl) ep643 rfl) (@ep644 9195880448 ep443 ep444 ep445 ep446 ep302 ep292 ep303 ep304 (@ep645 18391760896 595 1048576 3222691 9195880448 (ep648 rfl rfl) rfl) ep649 rfl) rfl rfl))

noncomputable abbrev qz585 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 119766 1000)))

noncomputable abbrev qz568 := qz585

noncomputable abbrev qz429 := qz568

noncomputable abbrev qz151 := (BSN.headSumC qz429 9)

noncomputable abbrev qz152 := qz429

noncomputable abbrev qz569 := (@Neg.neg Complex Complex.instNeg qz585)

noncomputable abbrev qz430 := qz569

noncomputable abbrev qz153 := qz430

noncomputable abbrev qz431 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 8) qz153)

noncomputable def ep650 := @Enclosure.Complex.IsNear.of_eq qz151 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz152 8) qz431) Bool.false 380215730853 274877906944 112210358352851 38570318146568192 Bool.true 634474951203 1099511627776 224439733232493 77140636293136384

noncomputable def ep651 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz152 8) qz431 Bool.false 443579648239 274877906944 100436753583199 38570318146568192 Bool.true 929220711099 1099511627776 200884709664405 77140636293136384 Bool.true

noncomputable abbrev qz432 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 7) qz153)

noncomputable def ep652 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz152 8) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz152 7) qz432) Bool.false 443579648239 274877906944 100436753583199 38570318146568192 Bool.true 929220711099 1099511627776 200884709664405 77140636293136384

noncomputable def ep653 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz152 7) qz432 Bool.false 1425756700331 1099511627776 175689985505131 77140636293136384 Bool.true 702927855249 1099511627776 175722832545751 77140636293136384 Bool.false

noncomputable def ep654 := nat_lit 1950883924334273527545856

noncomputable abbrev qz433 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 6) qz153)

noncomputable def ep655 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz152 7) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz152 6) qz433) Bool.false 1425756700331 1099511627776 175689985505131 77140636293136384 Bool.true 702927855249 1099511627776 175722832545751 77140636293136384

noncomputable def ep656 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz152 6) qz433 Bool.false 1169589945941 1099511627776 148513400861781 77140636293136384 Bool.true 5223879561 17179869184 74263910495923 38570318146568192 Bool.false

noncomputable abbrev qz434 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 5) qz153)

noncomputable def ep657 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz152 6) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz152 5) qz434) Bool.false 1169589945941 1099511627776 148513400861781 77140636293136384 Bool.true 5223879561 17179869184 74263910495923 38570318146568192

noncomputable def ep658 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz152 5) qz434 Bool.false 692228674139 549755813888 59378398614223 38570318146568192 Bool.true 388306863223 549755813888 29684298174769 19285159073284096 Bool.true

noncomputable abbrev qz435 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 4) qz153)

noncomputable def ep659 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz152 5) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz152 4) qz435) Bool.false 692228674139 549755813888 59378398614223 38570318146568192 Bool.true 388306863223 549755813888 29684298174769 19285159073284096

noncomputable def ep660 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz152 4) qz435 Bool.false 936851551173 549755813888 42729206971397 38570318146568192 Bool.true 525877138705 1099511627776 85470726215863 77140636293136384 Bool.true

noncomputable def ep661 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz152 4) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz152 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz153)) Bool.false 936851551173 549755813888 42729206971397 38570318146568192 Bool.true 525877138705 1099511627776 85470726215863 77140636293136384

noncomputable def ep662 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz152 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz153) Bool.false 640992593093 549755813888 23507876930565 38570318146568192 Bool.true 377877350565 549755813888 23534999838693 38570318146568192 Bool.false

noncomputable def ep663 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz152 3) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz152 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz153)) Bool.false 640992593093 549755813888 23507876930565 38570318146568192 Bool.true 377877350565 549755813888 23534999838693 38570318146568192

noncomputable def ep664 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz152 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz153) Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable def ep665 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz152 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz10) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz152)

noncomputable abbrev qz586 := (Enclosure.sfrac Bool.false 119766 1000)

noncomputable abbrev qz570 := qz586

noncomputable abbrev qz436 := qz570

noncomputable abbrev qz154 := (@HMul.hMul Real Real Real qz267 qz436 (Real.log qz285))

noncomputable abbrev qz155 := qz436

noncomputable abbrev qz437 := (@Eq.refl Real qz570)

noncomputable abbrev qz156 := qz437

noncomputable def ep666 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz9 qz153) (Complex.mk (@HMul.hMul Real Real Real qz0 qz11 (Real.cos qz154)) (@HMul.hMul Real Real Real qz0 qz11 (@Neg.neg Real Real.instNeg (Real.sin qz154)))) Bool.false 91236779205 549755813888 23507876930565 38570318146568192 Bool.true 377877350565 549755813888 23534999838693 38570318146568192 (BSN.cpow_neg_s_mk qz155 119766 1000 2 qz156 rfl)

noncomputable def ep667 := nat_lit 2410124434840263456239342546413950980796525091760448981081467838017233152382081

noncomputable def ep668 := nat_lit 4533005515154609706593226751364091784788032119413216079145871072239342851201

noncomputable def ep669 := nat_lit 7221307293490481149304841185739124758819999211042520511086111771907220771443841

noncomputable def ep670 := BSN.cos_dyadic_bound_f 2864496401 2147483648 3 2 1048576 280911 ep667 ep66 ep668 ep669 ep68 ep668 246102 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2864496401) qz292 0 2 ep667 ep66 ep668 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2864496401) qz293 0 2 ep669 ep68 ep668 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz157 := (Enclosure.Real.IsNear.const Bool.false 119766 1000)

noncomputable abbrev qz438 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 87047845) qz32)

noncomputable def ep671 := @Enclosure.Real.IsNear.cos_image qz154 qz438 Bool.false 87047845 1048576 7 8192 Bool.false 246102 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz154 Bool.false 1360122579 16384000 59883 70159000 87047845 1048576 7 8192 (@Enclosure.Real.IsNear.mulLit_ff qz155 qz16 119766 1000 0 1 363408 524288 1 140318 1360122579 16384000 59883 70159000 qz157 qz290 rfl) rfl) (Enclosure.sfrac_false_div 87047845 1048576) (BSN.cos_reduce0 qz438 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 201571014454850281799680) qz33) 226375608064910080 72057594037927936 Bool.false 246102 1048576 13 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q0 87047845 1048576 226375608064910080 72057594037927936 13 201571014454850281799680 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 246102 1048576 201571014454850281799680 151115727451828646838272 2864496401 2147483648 280911 280636 (ep670 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep672 := nat_lit 4334597578300350533465542002144020492005914739473277593083325411573228200006785

noncomputable def ep673 := nat_lit 11345178315190667743360982876589273711411548456141438965375806572384353016353921

noncomputable def ep674 := BSN.sin_dyadic_bound_f 2864496401 2147483648 3 2 1048576 280911 ep672 ep59 ep668 ep673 ep62 ep668 1019286 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2864496401) qz287 0 2 ep672 ep59 ep668 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2864496401) qz288 0 2 ep673 ep62 ep668 rfl rfl rfl rfl) rfl rfl

noncomputable def ep675 := @Enclosure.Real.IsNear.sin_image qz154 qz438 Bool.false 87047845 1048576 7 8192 Bool.false 1019286 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz154 Bool.false 1360122579 16384000 59883 70159000 87047845 1048576 7 8192 (@Enclosure.Real.IsNear.mulLit_ff qz155 qz16 119766 1000 0 1 363408 524288 1 140318 1360122579 16384000 59883 70159000 qz157 qz290 rfl) rfl) (Enclosure.sfrac_false_div 87047845 1048576) (BSN.sin_reduce0 qz438 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 201571014454850281799680) qz33) 226375608064910080 72057594037927936 Bool.false 1019286 1048576 13 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q0 87047845 1048576 226375608064910080 72057594037927936 13 201571014454850281799680 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1019286 1048576 201571014454850281799680 151115727451828646838272 2864496401 2147483648 280911 280636 (ep674 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep676 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz11 (Real.cos qz154)) (@HMul.hMul Real Real Real qz0 qz11 (@Neg.neg Real Real.instNeg (Real.sin qz154))) Bool.false 91236779205 549755813888 23507876930565 38570318146568192 Bool.true 377877350565 549755813888 23534999838693 38570318146568192 (@Enclosure.Real.IsNear.mulLit_ff qz11 (Real.cos qz154) 741455 1048576 1 1048576 123051 524288 495209 574742528 91236779205 549755813888 23507876930565 38570318146568192 qz294 (@Enclosure.Real.IsNear.recentre' (Real.cos qz154) Bool.false 246102 1048576 990418 1149485056 123051 524288 495209 574742528 (ep671 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz11 (@Neg.neg Real Real.instNeg (Real.sin qz154)) 741455 1048576 1 1048576 509643 524288 495209 574742528 377877350565 549755813888 23534999838693 38570318146568192 qz294 (@Enclosure.Real.IsNear.neg (Real.sin qz154) Bool.false 509643 524288 495209 574742528 (@Enclosure.Real.IsNear.recentre' (Real.sin qz154) Bool.false 1019286 1048576 990418 1149485056 509643 524288 495209 574742528 (ep675 rfl rfl) rfl)) rfl)

noncomputable def ep677 := @ep664 91236779205 549755813888 23507876930565 38570318146568192 Bool.true 377877350565 549755813888 23534999838693 38570318146568192 Bool.false 640992593093 640992593093 549755813888 23507876930565 38570318146568192 Bool.true 377877350565 377877350565 549755813888 23534999838693 38570318146568192 (ep665 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz10 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz18)) (ep666 ep676) rfl rfl

noncomputable abbrev qz158 := (@HMul.hMul Real Real Real qz267 qz436 (Real.log (Enclosure.sfrac Bool.false 3 1)))

noncomputable def ep678 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz8 qz153) (Complex.mk (@HMul.hMul Real Real Real qz0 qz19 (Real.cos qz158)) (@HMul.hMul Real Real Real qz0 qz19 (@Neg.neg Real Real.instNeg (Real.sin qz158)))) Bool.false 1155699055 2147483648 9385415059 18833163157504 Bool.false 229877562425 1099511627776 38400726538477 77140636293136384 (BSN.cpow_neg_s_mk qz155 119766 1000 3 qz156 rfl)

noncomputable def ep679 := nat_lit 2840564137745873457131751192636695164592912460328512651790442496412744320495745

noncomputable def ep680 := nat_lit 1948098027216651042601214476250424076336746311516265517721998305658964488321

noncomputable def ep681 := nat_lit 7436418678242746381276089252515510458762606473498887753374847112395644420698241

noncomputable def ep682 := BSN.sin_dyadic_bound_f 2577515887 2147483648 3 2 1048576 280911 ep679 ep59 ep680 ep681 ep62 ep680 977408 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2577515887) qz287 0 2 ep679 ep59 ep680 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2577515887) qz288 0 2 ep681 ep62 ep680 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz439 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 137967797) qz32)

noncomputable def ep683 := @Enclosure.Real.IsNear.cos_image qz158 qz439 Bool.false 137967797 1048576 7 8192 Bool.false 977408 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz158 Bool.false 34491949287 262144000 59883 70159000 137967797 1048576 7 8192 (@Enclosure.Real.IsNear.mulLit_ff qz155 qz21 119766 1000 0 1 575989 524288 1 140318 34491949287 262144000 59883 70159000 qz157 qz298 rfl) rfl) (Enclosure.sfrac_false_div 137967797 1048576) (BSN.cos_reduce3 qz439 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 181376556077997929529344) qz33) 226375608064910080 72057594037927936 Bool.false 977408 1048576 20 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q3 137967797 1048576 226375608064910080 72057594037927936 20 181376556077997929529344 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 977408 1048576 181376556077997929529344 151115727451828646838272 2577515887 2147483648 280911 280636 (ep682 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep684 := nat_lit 1578957008982025987758795646787608613252212142987625369002566719476261940048001

noncomputable def ep685 := nat_lit 4732974830891644661191184511410324991603962936339843575972256161817467891167361

noncomputable def ep686 := BSN.cos_dyadic_bound_f 2577515887 2147483648 3 2 1048576 280911 ep684 ep66 ep680 ep685 ep68 ep680 379715 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2577515887) qz292 0 2 ep684 ep66 ep680 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2577515887) qz293 0 2 ep685 ep68 ep680 rfl rfl rfl rfl) rfl rfl

noncomputable def ep687 := @Enclosure.Real.IsNear.sin_image qz158 qz439 Bool.false 137967797 1048576 7 8192 Bool.true 379715 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz158 Bool.false 34491949287 262144000 59883 70159000 137967797 1048576 7 8192 (@Enclosure.Real.IsNear.mulLit_ff qz155 qz21 119766 1000 0 1 575989 524288 1 140318 34491949287 262144000 59883 70159000 qz157 qz298 rfl) rfl) (Enclosure.sfrac_false_div 137967797 1048576) (BSN.sin_reduce3 qz439 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 181376556077997929529344) qz33) 226375608064910080 72057594037927936 Bool.false 379715 1048576 20 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q3 137967797 1048576 226375608064910080 72057594037927936 20 181376556077997929529344 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 379715 1048576 181376556077997929529344 151115727451828646838272 2577515887 2147483648 280911 280636 (ep686 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep688 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz19 (Real.cos qz158)) (@HMul.hMul Real Real Real qz0 qz19 (@Neg.neg Real Real.instNeg (Real.sin qz158))) Bool.false 1155699055 2147483648 9385415059 18833163157504 Bool.false 229877562425 1099511627776 38400726538477 77140636293136384 (@Enclosure.Real.IsNear.mulLit_ff qz19 (Real.cos qz158) 605395 1048576 1 1048576 1909 2048 495209 574742528 1155699055 2147483648 9385415059 18833163157504 qz300 (@Enclosure.Real.IsNear.recentre' (Real.cos qz158) Bool.false 977408 1048576 990418 1149485056 1909 2048 495209 574742528 (ep683 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 (@Neg.neg Real Real.instNeg (Real.sin qz158)) 605395 1048576 1 1048576 379715 1048576 495209 574742528 229877562425 1099511627776 38400726538477 77140636293136384 qz300 (@Enclosure.Real.IsNear.neg (Real.sin qz158) Bool.true 379715 1048576 495209 574742528 (@Enclosure.Real.IsNear.recentre' (Real.sin qz158) Bool.true 379715 1048576 990418 1149485056 379715 1048576 495209 574742528 (ep687 rfl rfl) rfl)) rfl)

noncomputable def ep689 := @ep662 1155699055 2147483648 9385415059 18833163157504 Bool.false 229877562425 1099511627776 38400726538477 77140636293136384 Bool.false 2011873386747452719104 936851551173 549755813888 42729206971397 38570318146568192 Bool.true 289104014393859941335040 525877138705 1099511627776 85470726215863 77140636293136384 (ep663 (BSN.head_sum_c_succ qz152 2 3 rfl rfl) (ep677 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep678 ep688) rfl rfl

noncomputable abbrev qz159 := (@HMul.hMul Real Real Real qz267 qz436 (Real.log (Enclosure.sfrac Bool.false 4 1)))

noncomputable def ep690 := @Enclosure.Complex.IsNear.of_eq qz435 (Complex.mk (@HMul.hMul Real Real Real qz0 qz22 (Real.cos qz159)) (@HMul.hMul Real Real Real qz0 qz22 (@Neg.neg Real Real.instNeg (Real.sin qz159)))) Bool.true 122311438517 274877906944 8324595821413 19285159073284096 Bool.true 250736587741 1099511627776 33266466483213 77140636293136384 (BSN.cpow_neg_s_mk qz155 119766 1000 4 qz156 rfl)

noncomputable def ep691 := nat_lit 1983237783782690596269827462876102175535663977908998593578484579833776963584000

noncomputable def ep692 := nat_lit 950015965288777139353683010162812132865481105249727203314616227601219321856

noncomputable def ep693 := nat_lit 5192656074534674493909642154087623049616385353686496758185902616148537692389376

noncomputable def ep694 := BSN.sin_dyadic_bound_f 2356222848 2147483648 3 2 1048576 280911 ep691 ep59 ep692 ep693 ep62 ep692 933164 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2356222848) qz287 0 2 ep691 ep59 ep692 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2356222848) qz288 0 2 ep693 ep62 ep692 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz440 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 174095929) qz32)

noncomputable def ep695 := @Enclosure.Real.IsNear.cos_image qz159 qz440 Bool.false 174095929 1048576 7 8192 Bool.true 933164 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz159 Bool.false 43523982411 262144000 59883 70159000 174095929 1048576 7 8192 (@Enclosure.Real.IsNear.mulLit_ff qz155 qz24 119766 1000 0 1 726817 524288 1 140318 43523982411 262144000 59883 70159000 qz157 qz302 rfl) rfl) (Enclosure.sfrac_false_div 174095929 1048576) (BSN.cos_reduce1 qz440 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 165804442837379541106688) qz33) 226375608064910080 72057594037927936 Bool.false 933164 1048576 26 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q1 174095929 1048576 226375608064910080 72057594037927936 26 165804442837379541106688 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 933164 1048576 165804442837379541106688 151115727451828646838272 2356222848 2147483648 280911 280636 (ep694 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep696 := nat_lit 1102220998086067565545172449602351347356642423773999097411742373786587743911936

noncomputable def ep697 := nat_lit 3304762962327625142356809982786728417804196309111497837828597888904560793092096

noncomputable def ep698 := BSN.cos_dyadic_bound_f 2356222848 2147483648 3 2 1048576 280911 ep696 ep66 ep692 ep697 ep68 ep692 478243 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2356222848) qz292 0 2 ep696 ep66 ep692 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2356222848) qz293 0 2 ep697 ep68 ep692 rfl rfl rfl rfl) rfl rfl

noncomputable def ep699 := @Enclosure.Real.IsNear.sin_image qz159 qz440 Bool.false 174095929 1048576 7 8192 Bool.false 478243 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz159 Bool.false 43523982411 262144000 59883 70159000 174095929 1048576 7 8192 (@Enclosure.Real.IsNear.mulLit_ff qz155 qz24 119766 1000 0 1 726817 524288 1 140318 43523982411 262144000 59883 70159000 qz157 qz302 rfl) rfl) (Enclosure.sfrac_false_div 174095929 1048576) (BSN.sin_reduce1 qz440 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 165804442837379541106688) qz33) 226375608064910080 72057594037927936 Bool.false 478243 1048576 26 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q1 174095929 1048576 226375608064910080 72057594037927936 26 165804442837379541106688 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 478243 1048576 165804442837379541106688 151115727451828646838272 2356222848 2147483648 280911 280636 (ep698 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep700 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz22 (Real.cos qz159)) (@HMul.hMul Real Real Real qz0 qz22 (@Neg.neg Real Real.instNeg (Real.sin qz159))) Bool.true 122311438517 274877906944 8324595821413 19285159073284096 Bool.true 250736587741 1099511627776 33266466483213 77140636293136384 (@Enclosure.Real.IsNear.mulLit_ft qz22 (Real.cos qz159) 524287 1048576 1 1048576 233291 262144 495209 574742528 122311438517 274877906944 8324595821413 19285159073284096 qz303 (@Enclosure.Real.IsNear.recentre' (Real.cos qz159) Bool.true 933164 1048576 990418 1149485056 233291 262144 495209 574742528 (ep695 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz22 (@Neg.neg Real Real.instNeg (Real.sin qz159)) 524287 1048576 1 1048576 478243 1048576 495209 574742528 250736587741 1099511627776 33266466483213 77140636293136384 qz303 (@Enclosure.Real.IsNear.neg (Real.sin qz159) Bool.false 478243 1048576 495209 574742528 (@Enclosure.Real.IsNear.recentre' (Real.sin qz159) Bool.false 478243 1048576 990418 1149485056 478243 1048576 495209 574742528 (ep699 rfl rfl) rfl)) rfl)

noncomputable def ep701 := @ep660 122311438517 274877906944 8324595821413 19285159073284096 Bool.true 250736587741 1099511627776 33266466483213 77140636293136384 Bool.false 190278369073948541321216 692228674139 549755813888 59378398614223 38570318146568192 Bool.true 853895822517826639364096 388306863223 549755813888 29684298174769 19285159073284096 (ep661 (BSN.head_sum_c_succ qz152 3 4 rfl rfl) (ep689 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep690 ep700) rfl rfl

noncomputable abbrev qz160 := (@HMul.hMul Real Real Real qz267 qz436 (Real.log (Enclosure.sfrac Bool.false 5 1)))

noncomputable def ep702 := @Enclosure.Complex.IsNear.of_eq qz434 (Complex.mk (@HMul.hMul Real Real Real qz0 qz25 (Real.cos qz160)) (@HMul.hMul Real Real Real qz0 qz25 (@Neg.neg Real Real.instNeg (Real.sin qz160)))) Bool.true 214867402337 1099511627776 29756603633335 77140636293136384 Bool.false 221142717271 549755813888 14895314146385 38570318146568192 (BSN.cpow_neg_s_mk qz155 119766 1000 5 qz156 rfl)

noncomputable def ep703 := nat_lit 1190680606580739054926145945791735995372462403350106455055575618968423896252416

noncomputable def ep704 := nat_lit 1108470342438664503413390912507253051179981813953153517961948627059972571136

noncomputable def ep705 := nat_lit 3569824879057339835771611055550193480015027246422413058130802959651151743614976

noncomputable def ep706 := BSN.cos_dyadic_bound_f 2402096828 2147483648 3 2 1048576 280911 ep703 ep66 ep704 ep705 ep68 ep704 458201 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2402096828) qz292 0 2 ep703 ep66 ep704 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2402096828) qz293 0 2 ep705 ep68 ep704 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz441 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 202119017) qz32)

noncomputable def ep707 := @Enclosure.Real.IsNear.cos_image qz160 qz441 Bool.false 202119017 1048576 7 8192 Bool.true 458201 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz160 Bool.false 1579054827 8192000 59883 70159000 202119017 1048576 7 8192 (@Enclosure.Real.IsNear.mulLit_ff qz155 qz28 119766 1000 0 1 843808 524288 1 140318 1579054827 8192000 59883 70159000 qz157 qz305 rfl) rfl) (Enclosure.sfrac_false_div 202119017 1048576) (BSN.cos_reduce2 qz441 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 169032537185029732696064) qz33) 226375608064910080 72057594037927936 Bool.false 458201 1048576 30 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q2 202119017 1048576 226375608064910080 72057594037927936 30 169032537185029732696064 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 458201 1048576 169032537185029732696064 151115727451828646838272 2402096828 2147483648 280911 280636 (ep706 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep708 := nat_lit 2142338315571379367264331989695118989229488340579029096285666555241515035197440

noncomputable def ep709 := nat_lit 5609091398322997647924866863914585609708654254770104432195283537379204184211456

noncomputable def ep710 := BSN.sin_dyadic_bound_f 2402096828 2147483648 3 2 1048576 280911 ep708 ep59 ep704 ep709 ep62 ep704 943166 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2402096828) qz287 0 2 ep708 ep59 ep704 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2402096828) qz288 0 2 ep709 ep62 ep704 rfl rfl rfl rfl) rfl rfl

noncomputable def ep711 := @Enclosure.Real.IsNear.sin_image qz160 qz441 Bool.false 202119017 1048576 7 8192 Bool.true 943166 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz160 Bool.false 1579054827 8192000 59883 70159000 202119017 1048576 7 8192 (@Enclosure.Real.IsNear.mulLit_ff qz155 qz28 119766 1000 0 1 843808 524288 1 140318 1579054827 8192000 59883 70159000 qz157 qz305 rfl) rfl) (Enclosure.sfrac_false_div 202119017 1048576) (BSN.sin_reduce2 qz441 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 169032537185029732696064) qz33) 226375608064910080 72057594037927936 Bool.false 943166 1048576 30 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q2 202119017 1048576 226375608064910080 72057594037927936 30 169032537185029732696064 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 943166 1048576 169032537185029732696064 151115727451828646838272 2402096828 2147483648 280911 280636 (ep710 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep712 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz25 (Real.cos qz160)) (@HMul.hMul Real Real Real qz0 qz25 (@Neg.neg Real Real.instNeg (Real.sin qz160))) Bool.true 214867402337 1099511627776 29756603633335 77140636293136384 Bool.false 221142717271 549755813888 14895314146385 38570318146568192 (@Enclosure.Real.IsNear.mulLit_ft qz25 (Real.cos qz160) 468937 1048576 1 1048576 458201 1048576 495209 574742528 214867402337 1099511627776 29756603633335 77140636293136384 qz306 (@Enclosure.Real.IsNear.recentre' (Real.cos qz160) Bool.true 458201 1048576 990418 1149485056 458201 1048576 495209 574742528 (ep707 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz25 (@Neg.neg Real Real.instNeg (Real.sin qz160)) 468937 1048576 1 1048576 471583 524288 495209 574742528 221142717271 549755813888 14895314146385 38570318146568192 qz306 (@Enclosure.Real.IsNear.neg (Real.sin qz160) Bool.true 471583 524288 495209 574742528 (@Enclosure.Real.IsNear.recentre' (Real.sin qz160) Bool.true 943166 1048576 990418 1149485056 471583 524288 495209 574742528 (ep711 rfl rfl) rfl)) rfl)

noncomputable def ep713 := @ep658 214867402337 1099511627776 29756603633335 77140636293136384 Bool.false 221142717271 549755813888 14895314146385 38570318146568192 Bool.false 642988872646016377028608 1169589945941 1099511627776 148513400861781 77140636293136384 Bool.true 91899461110734180581376 5223879561 17179869184 74263910495923 38570318146568192 (ep659 (BSN.head_sum_c_succ qz152 4 5 rfl rfl) (ep701 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep702 ep712) rfl rfl

noncomputable abbrev qz161 := (@HMul.hMul Real Real Real qz267 qz436 qz540)

noncomputable def ep714 := @Enclosure.Complex.IsNear.of_eq qz433 (Complex.mk (@HMul.hMul Real Real Real qz0 qz30 (Real.cos qz161)) (@HMul.hMul Real Real Real qz0 qz30 (@Neg.neg Real Real.instNeg (Real.sin qz161)))) Bool.false 128083377195 549755813888 13588292321675 38570318146568192 Bool.true 368599563345 1099511627776 27195011553905 77140636293136384 (BSN.cpow_neg_s_mk qz155 119766 1000 6 qz156 rfl)

noncomputable def ep715 := @Enclosure.Real.IsNear.mulLit_ff qz155 qz540 119766 1000 0 1 4034681531866359 2251799813685248 250000000070159 35079500000000000000 241608834172753175997 1125899906842624000 14970750004201331397 17539750000000000000000 qz157 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 250000000070159 35079500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz308) Bool.false 33845361775666394038272 18889465931478580854784 1000000000280636 140318000000000000000 4034681531866359 2251799813685248 250000000070159 35079500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 212580 524288 24973259072661432 36028797018963968 140318 1000000000000000 rfl rfl rfl rfl (ep122 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep716 := nat_lit 655074224291249160528785473383563131295065394508426576625294699317534668390656

noncomputable def ep717 := nat_lit 335798051853093622575080103834042912055716171073515135725826258122711531776

noncomputable def ep718 := nat_lit 1964551076770041294341206259943021308061084751183132699604432445436358582108416

noncomputable def ep719 := BSN.cos_dyadic_bound_f 2068996574 2147483648 3 2 1048576 280911 ep716 ep66 ep717 ep718 ep68 ep717 598410 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2068996574) qz292 0 2 ep716 ep66 ep717 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2068996574) qz293 0 2 ep718 ep68 ep717 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz442 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 225015761) qz32)

noncomputable def ep720 := @Enclosure.Real.IsNear.cos_image qz161 qz442 Bool.false 225015761 1048576 7 8192 Bool.false 598410 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz161 Bool.false 241608834172753175997 1125899906842624000 14970750004201331397 17539750000000000000000 225015761 1048576 7 8192 (ep715 rfl) rfl) (Enclosure.sfrac_false_div 225015761 1048576) (BSN.cos_reduce0 qz442 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 145592690637958086131712) qz33) 226375608064910080 72057594037927936 Bool.false 598410 1048576 34 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q0 225015761 1048576 226375608064910080 72057594037927936 34 145592690637958086131712 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 598410 1048576 145592690637958086131712 151115727451828646838272 2068996574 2147483648 280911 280636 (ep719 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep721 := nat_lit 1178864965282766014053753788007346402001473137178309025816949797765064233877760

noncomputable def ep722 := nat_lit 3086959807466148837608995505565414031003387056904309376443693370681064793866496

noncomputable def ep723 := BSN.sin_dyadic_bound_f 2068996574 2147483648 3 2 1048576 280911 ep721 ep59 ep717 ep722 ep62 ep717 861055 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2068996574) qz287 0 2 ep721 ep59 ep717 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2068996574) qz288 0 2 ep722 ep62 ep717 rfl rfl rfl rfl) rfl rfl

noncomputable def ep724 := @Enclosure.Real.IsNear.sin_image qz161 qz442 Bool.false 225015761 1048576 7 8192 Bool.false 861055 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz161 Bool.false 241608834172753175997 1125899906842624000 14970750004201331397 17539750000000000000000 225015761 1048576 7 8192 (ep715 rfl) rfl) (Enclosure.sfrac_false_div 225015761 1048576) (BSN.sin_reduce0 qz442 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 145592690637958086131712) qz33) 226375608064910080 72057594037927936 Bool.false 861055 1048576 34 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q0 225015761 1048576 226375608064910080 72057594037927936 34 145592690637958086131712 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 861055 1048576 145592690637958086131712 151115727451828646838272 2068996574 2147483648 280911 280636 (ep723 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep725 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz30 (Real.cos qz161)) (@HMul.hMul Real Real Real qz0 qz30 (@Neg.neg Real Real.instNeg (Real.sin qz161))) Bool.false 128083377195 549755813888 13588292321675 38570318146568192 Bool.true 368599563345 1099511627776 27195011553905 77140636293136384 (@Enclosure.Real.IsNear.mulLit_ff qz30 (Real.cos qz161) 428079 1048576 1 1048576 299205 524288 495209 574742528 128083377195 549755813888 13588292321675 38570318146568192 qz310 (@Enclosure.Real.IsNear.recentre' (Real.cos qz161) Bool.false 598410 1048576 990418 1149485056 299205 524288 495209 574742528 (ep720 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz30 (@Neg.neg Real Real.instNeg (Real.sin qz161)) 428079 1048576 1 1048576 861055 1048576 495209 574742528 368599563345 1099511627776 27195011553905 77140636293136384 qz310 (@Enclosure.Real.IsNear.neg (Real.sin qz161) Bool.false 861055 1048576 495209 574742528 (@Enclosure.Real.IsNear.recentre' (Real.sin qz161) Bool.false 861055 1048576 990418 1149485056 861055 1048576 495209 574742528 (ep724 rfl rfl) rfl)) rfl)

noncomputable def ep726 := @ep656 128083377195 549755813888 13588292321675 38570318146568192 Bool.true 368599563345 1099511627776 27195011553905 77140636293136384 Bool.false 783818035196738223996928 1425756700331 1099511627776 175689985505131 77140636293136384 Bool.true 12076208598967507746816 702927855249 1099511627776 175722832545751 77140636293136384 (ep657 (BSN.head_sum_c_succ qz152 5 6 rfl rfl) (ep713 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep714 ep725) rfl rfl

noncomputable abbrev qz162 := (@HMul.hMul Real Real Real qz267 qz436 qz541)

noncomputable def ep727 := @Enclosure.Complex.IsNear.of_eq qz432 (Complex.mk (@HMul.hMul Real Real Real qz0 qz34 (Real.cos qz162)) (@HMul.hMul Real Real Real qz0 qz34 (@Neg.neg Real Real.instNeg (Real.sin qz162)))) Bool.false 348561892625 1099511627776 25183521661267 77140636293136384 Bool.true 113146427925 549755813888 12580938559327 38570318146568192 (BSN.cpow_neg_s_mk qz155 119766 1000 7 qz156 rfl)

noncomputable def ep728 := @Enclosure.Real.IsNear.mulLit_ff qz155 qz541 119766 1000 0 1 4381796493761783 2251799813685248 250000000070159 35079500000000000000 262395119435936851389 1125899906842624000 14970750004201331397 17539750000000000000000 qz157 (BSN.isNear_log_sfrac 7 1 4381796493761783 2251799813685248 250000000070159 35079500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz312) Bool.false 36757173121942042968064 18889465931478580854784 1000000000280636 140318000000000000000 4381796493761783 2251799813685248 250000000070159 35079500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 293399 524288 24973259072661432 36028797018963968 140318 1000000000000000 rfl rfl rfl rfl (ep133 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep729 := nat_lit 2338214920682833972996521559432642816

noncomputable def ep730 := BSN.cos_dyadic_bound_f 1236576836 2147483648 2 1 1048576 280911 ep729 ep77 ep729 ep729 ep78 ep729 879485 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1236576836) qz292 0 1 ep729 ep77 ep729 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1236576836) qz293 0 1 ep729 ep78 ep729 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz443 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 122187249) qz27)

noncomputable def ep731 := @Enclosure.Real.IsNear.cos_image qz162 qz443 Bool.false 122187249 524288 7 8192 Bool.false 879485 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz162 Bool.false 262395119435936851389 1125899906842624000 14970750004201331397 17539750000000000000000 122187249 524288 7 8192 (ep728 rfl) rfl) (Enclosure.sfrac_false_div 122187249 524288) (BSN.cos_reduce0 qz443 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 43508179538367068766208) qz29) 226375608064910080 72057594037927936 Bool.false 879485 1048576 37 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q0 122187249 524288 226375608064910080 72057594037927936 37 43508179538367068766208 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 879485 1048576 43508179538367068766208 75557863725914323419136 1236576836 2147483648 280911 280636 (ep730 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep732 := BSN.sin_dyadic_bound_f 1236576836 2147483648 2 1 1048576 280911 ep729 ep81 ep729 ep729 ep82 ep729 570978 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1236576836) qz287 0 1 ep729 ep81 ep729 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1236576836) qz288 0 1 ep729 ep82 ep729 rfl rfl rfl rfl) rfl rfl

noncomputable def ep733 := @Enclosure.Real.IsNear.sin_image qz162 qz443 Bool.false 122187249 524288 7 8192 Bool.false 570978 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz162 Bool.false 262395119435936851389 1125899906842624000 14970750004201331397 17539750000000000000000 122187249 524288 7 8192 (ep728 rfl) rfl) (Enclosure.sfrac_false_div 122187249 524288) (BSN.sin_reduce0 qz443 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 43508179538367068766208) qz29) 226375608064910080 72057594037927936 Bool.false 570978 1048576 37 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q0 122187249 524288 226375608064910080 72057594037927936 37 43508179538367068766208 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 570978 1048576 43508179538367068766208 75557863725914323419136 1236576836 2147483648 280911 280636 (ep732 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep734 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz34 (Real.cos qz162)) (@HMul.hMul Real Real Real qz0 qz34 (@Neg.neg Real Real.instNeg (Real.sin qz162))) Bool.false 348561892625 1099511627776 25183521661267 77140636293136384 Bool.true 113146427925 549755813888 12580938559327 38570318146568192 (@Enclosure.Real.IsNear.mulLit_ff qz34 (Real.cos qz162) 396325 1048576 1 1048576 879485 1048576 495209 574742528 348561892625 1099511627776 25183521661267 77140636293136384 qz314 (@Enclosure.Real.IsNear.recentre' (Real.cos qz162) Bool.false 879485 1048576 990418 1149485056 879485 1048576 495209 574742528 (ep731 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz34 (@Neg.neg Real Real.instNeg (Real.sin qz162)) 396325 1048576 1 1048576 285489 524288 495209 574742528 113146427925 549755813888 12580938559327 38570318146568192 qz314 (@Enclosure.Real.IsNear.neg (Real.sin qz162) Bool.false 285489 524288 495209 574742528 (@Enclosure.Real.IsNear.recentre' (Real.sin qz162) Bool.false 570978 1048576 990418 1149485056 285489 524288 495209 574742528 (ep733 rfl rfl) rfl)) rfl)

noncomputable def ep735 := @ep653 348561892625 1099511627776 25183521661267 77140636293136384 Bool.true 113146427925 549755813888 12580938559327 38570318146568192 Bool.false ep654 443579648239 274877906944 100436753583199 38570318146568192 Bool.true 510844488311816859942912 929220711099 1099511627776 200884709664405 77140636293136384 (ep655 (BSN.head_sum_c_succ qz152 6 7 rfl rfl) (ep726 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep727 ep734) rfl rfl

noncomputable abbrev qz163 := (@HMul.hMul Real Real Real qz267 qz436 qz542)

noncomputable def ep736 := @Enclosure.Complex.IsNear.of_eq qz431 (Complex.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz163)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz163)))) Bool.true 31681958693 137438953472 2943401192413 9642579536642048 Bool.false 36843219987 137438953472 2944377946011 9642579536642048 (BSN.cpow_neg_s_mk qz155 119766 1000 8 qz156 rfl)

noncomputable def ep737 := @Enclosure.Real.IsNear.mulLit_ff qz155 qz542 119766 1000 0 1 9364972152248037 4503599627370496 500000000210477 70159000000000000000 560802627393069199671 2251799813685248000 29941500012603994191 35079500000000000000000 qz157 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 500000000210477 70159000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz316) Bool.false 39279540158062550581248 18889465931478580854784 1000000000420954 140318000000000000000 9364972152248037 4503599627370496 500000000210477 70159000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 524288 24973259072661432 36028797018963968 140318 1000000000000000 rfl rfl rfl rfl (ep148 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep738 := nat_lit 416913750606024052842951795650346173121376843219825943578505263742527462890625

noncomputable def ep739 := nat_lit 136066566499118832107123614008580066054790254827053299435476123199462890625

noncomputable def ep740 := nat_lit 1250469118685073920864641139723021359232020949149823724136644838981183462890625

noncomputable def ep741 := BSN.cos_dyadic_bound_f 1848072175 2147483648 3 2 1048576 280911 ep738 ep66 ep739 ep740 ep68 ep739 683672 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1848072175) qz292 0 2 ep738 ep66 ep739 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1848072175) qz293 0 2 ep740 ep68 ep739 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz444 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 261144073) qz32)

noncomputable def ep742 := @Enclosure.Real.IsNear.cos_image qz163 qz444 Bool.false 261144073 1048576 7 8192 Bool.true 683672 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz163 Bool.false 560802627393069199671 2251799813685248000 29941500012603994191 35079500000000000000000 261144073 1048576 7 8192 (ep737 rfl) rfl) (Enclosure.sfrac_false_div 261144073 1048576) (BSN.cos_reduce2 qz444 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 130046518131193351766016) qz33) 226375608064910080 72057594037927936 Bool.false 683672 1048576 39 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q2 261144073 1048576 226375608064910080 72057594037927936 39 130046518131193351766016 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 683672 1048576 130046518131193351766016 151115727451828646838272 1848072175 2147483648 280911 280636 (ep741 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep743 := nat_lit 11664757455648995709516980204437890625

noncomputable def ep744 := BSN.sin_dyadic_bound_f 1848072175 2147483648 2 1 1048576 280911 ep743 ep81 ep743 ep743 ep82 ep743 795048 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1848072175) qz287 0 1 ep743 ep81 ep743 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1848072175) qz288 0 1 ep743 ep82 ep743 rfl rfl rfl rfl) rfl rfl

noncomputable def ep745 := @Enclosure.Real.IsNear.sin_image qz163 qz444 Bool.false 261144073 1048576 7 8192 Bool.true 795048 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz163 Bool.false 560802627393069199671 2251799813685248000 29941500012603994191 35079500000000000000000 261144073 1048576 7 8192 (ep737 rfl) rfl) (Enclosure.sfrac_false_div 261144073 1048576) (BSN.sin_reduce2 qz444 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 130046518131193351766016) qz33) 226375608064910080 72057594037927936 Bool.false 795048 1048576 39 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q2 261144073 1048576 226375608064910080 72057594037927936 39 130046518131193351766016 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 795048 1048576 130046518131193351766016 151115727451828646838272 1848072175 2147483648 280911 280636 (ep744 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep746 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz163)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz163))) Bool.true 31681958693 137438953472 2943401192413 9642579536642048 Bool.false 36843219987 137438953472 2944377946011 9642579536642048 (@Enclosure.Real.IsNear.mulLit_ft qz36 (Real.cos qz163) 370727 1048576 1 1048576 85459 131072 495209 574742528 31681958693 137438953472 2943401192413 9642579536642048 qz318 (@Enclosure.Real.IsNear.recentre' (Real.cos qz163) Bool.true 683672 1048576 990418 1149485056 85459 131072 495209 574742528 (ep742 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz36 (@Neg.neg Real Real.instNeg (Real.sin qz163)) 370727 1048576 1 1048576 99381 131072 495209 574742528 36843219987 137438953472 2944377946011 9642579536642048 qz318 (@Enclosure.Real.IsNear.neg (Real.sin qz163) Bool.true 99381 131072 495209 574742528 (@Enclosure.Real.IsNear.recentre' (Real.sin qz163) Bool.true 795048 1048576 990418 1149485056 99381 131072 495209 574742528 (ep745 rfl rfl) rfl)) rfl)

noncomputable def ep747 := @ep651 31681958693 137438953472 2943401192413 9642579536642048 Bool.false 36843219987 137438953472 2944377946011 9642579536642048 Bool.false 52256452142027941871616 380215730853 274877906944 112210358352851 38570318146568192 Bool.true 87201573297538587426816 634474951203 1099511627776 224439733232493 77140636293136384 (ep652 (BSN.head_sum_c_succ qz152 7 8 rfl rfl) (ep735 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep736 ep746) rfl rfl

theorem EMRow38.d11 : Enclosure.Complex.IsNear qz151 Bool.false 380215730853 274877906944 112210358352851 38570318146568192 Bool.true 634474951203 1099511627776 224439733232493 77140636293136384 := ep650 (BSN.head_sum_c_succ qz152 8 9 rfl rfl) (ep747 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz164 := (BSN.headSumC qz429 17)

noncomputable abbrev qz165 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 16) qz430)

noncomputable def ep748 := @Enclosure.Complex.IsNear.of_eq qz164 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz152 16) qz165) Bool.false 1851874704749 1099511627776 377155765664893 77140636293136384 Bool.false 247731199751 1099511627776 377264647662081 77140636293136384

noncomputable def ep749 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz152 16) qz165 Bool.false 422826259847 274877906944 90124083666703 19285159073284096 Bool.false 6157354721 274877906944 180294240397911 38570318146568192 Bool.false

noncomputable abbrev qz166 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 15) qz430)

noncomputable def ep750 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz152 16) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz152 15) qz166) Bool.false 422826259847 274877906944 90124083666703 19285159073284096 Bool.false 6157354721 274877906944 180294240397911 38570318146568192

noncomputable def ep751 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz152 15) qz166 Bool.false 949699098217 549755813888 171640477014237 38570318146568192 Bool.true 84241007093 549755813888 85844245618977 19285159073284096 Bool.true

noncomputable abbrev qz445 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 14) qz153)

noncomputable def ep752 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz152 15) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz152 14) qz445) Bool.false 949699098217 549755813888 171640477014237 38570318146568192 Bool.true 84241007093 549755813888 85844245618977 19285159073284096

noncomputable def ep753 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz152 14) qz445 Bool.false 499285477615 274877906944 40686590863081 9642579536642048 Bool.false 108641600981 1099511627776 325543847488249 77140636293136384 Bool.true

noncomputable abbrev qz446 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 13) qz153)

noncomputable def ep754 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz152 14) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz152 13) qz446) Bool.false 499285477615 274877906944 40686590863081 9642579536642048 Bool.false 108641600981 1099511627776 325543847488249 77140636293136384

noncomputable def ep755 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz152 13) qz446 Bool.false 1760514067333 1099511627776 307001253340809 77140636293136384 Bool.true 5232286465 68719476736 76765763416927 19285159073284096 Bool.false

noncomputable def ep756 := nat_lit 2195880752869545040936960

noncomputable abbrev qz447 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 12) qz153)

noncomputable def ep757 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz152 13) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz152 12) qz447) Bool.false 1760514067333 1099511627776 307001253340809 77140636293136384 Bool.true 5232286465 68719476736 76765763416927 19285159073284096

noncomputable def ep758 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz152 12) qz447 Bool.false 985699868783 549755813888 143882665640181 38570318146568192 Bool.false 153497066459 1099511627776 287821029317759 77140636293136384 Bool.true

noncomputable abbrev qz448 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 11) qz153)

noncomputable def ep759 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz152 12) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz152 11) qz448) Bool.false 985699868783 549755813888 143882665640181 38570318146568192 Bool.false 153497066459 1099511627776 287821029317759 77140636293136384

noncomputable def ep760 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz152 11) qz448 Bool.false 2059668558867 1099511627776 267705514639859 77140636293136384 Bool.true 41512521263 274877906944 133854944631993 38570318146568192 Bool.true

noncomputable def ep761 := nat_lit 2167576934448371876233216

noncomputable abbrev qz449 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 10) qz153)

noncomputable def ep762 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz152 11) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz152 10) qz449) Bool.false 2059668558867 1099511627776 267705514639859 77140636293136384 Bool.true 41512521263 274877906944 133854944631993 38570318146568192

noncomputable def ep763 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz152 10) qz449 Bool.false 1791257211037 1099511627776 14507665290497 4537684487831552 Bool.true 193532713789 549755813888 1813564064775 567210560978944 Bool.false

noncomputable abbrev qz450 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 9) qz153)

noncomputable def ep764 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz152 10) (@HAdd.hAdd Complex Complex Complex qz4 qz151 qz450) Bool.false 1791257211037 1099511627776 14507665290497 4537684487831552 Bool.true 193532713789 549755813888 1813564064775 567210560978944

noncomputable def ep765 := @Enclosure.Complex.IsNear.addLitP qz151 qz450 Bool.false 380215730853 274877906944 112210358352851 38570318146568192 Bool.true 634474951203 1099511627776 224439733232493 77140636293136384 Bool.false

noncomputable abbrev qz167 := (@HMul.hMul Real Real Real qz267 qz436 qz543)

noncomputable def ep766 := @Enclosure.Complex.IsNear.of_eq qz450 (Complex.mk (@HMul.hMul Real Real Real qz0 qz46 (Real.cos qz167)) (@HMul.hMul Real Real Real qz0 qz46 (@Neg.neg Real Real.instNeg (Real.sin qz167)))) Bool.false 270394287625 1099511627776 22209593232747 77140636293136384 Bool.false 247409523625 1099511627776 22204979576907 77140636293136384 (BSN.cpow_neg_s_mk qz155 119766 1000 9 qz156 rfl)

noncomputable def ep767 := @Enclosure.Real.IsNear.mulLit_ff qz155 qz543 119766 1000 0 1 9895417793173221 4503599627370496 500000000210477 70159000000000000000 592567303708591993143 2251799813685248000 29941500012603994191 35079500000000000000000 qz157 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 500000000210477 70159000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz321) Bool.false 41504390431577613533184 18889465931478580854784 1000000000420954 140318000000000000000 9895417793173221 4503599627370496 500000000210477 70159000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 61752 524288 24973259072661432 36028797018963968 140318 1000000000000000 rfl rfl rfl rfl (ep183 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep768 := nat_lit 10081535006845056849163792526553760000

noncomputable def ep769 := BSN.sin_dyadic_bound_f 1781893180 2147483648 2 1 1048576 280911 ep768 ep81 ep768 ep768 ep82 ep768 773605 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1781893180) qz287 0 1 ep768 ep81 ep768 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1781893180) qz288 0 1 ep768 ep82 ep768 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz451 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 275935653) qz32)

noncomputable def ep770 := @Enclosure.Real.IsNear.cos_image qz167 qz451 Bool.false 275935653 1048576 7 8192 Bool.false 773605 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz167 Bool.false 592567303708591993143 2251799813685248000 29941500012603994191 35079500000000000000000 275935653 1048576 7 8192 (ep767 rfl) rfl) (Enclosure.sfrac_false_div 275935653 1048576) (BSN.cos_reduce3 qz451 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 125389585349821182509056) qz33) 226375608064910080 72057594037927936 Bool.false 773605 1048576 41 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q3 275935653 1048576 226375608064910080 72057594037927936 41 125389585349821182509056 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 773605 1048576 125389585349821182509056 151115727451828646838272 1781893180 2147483648 280911 280636 (ep769 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep771 := nat_lit 360311339752275469712827758544587141783259327858388861983585818146484428800000

noncomputable def ep772 := nat_lit 101637348094242360450523793446664468755630486501159344174702170137600000000

noncomputable def ep773 := nat_lit 1080730744560637924417582228046868096412266722602164267262408050099178086400000

noncomputable def ep774 := BSN.cos_dyadic_bound_f 1781893180 2147483648 3 2 1048576 280911 ep771 ep66 ep772 ep773 ep68 ep772 707845 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1781893180) qz292 0 2 ep771 ep66 ep772 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1781893180) qz293 0 2 ep773 ep68 ep772 rfl rfl rfl rfl) rfl rfl

noncomputable def ep775 := @Enclosure.Real.IsNear.sin_image qz167 qz451 Bool.false 275935653 1048576 7 8192 Bool.true 707845 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz167 Bool.false 592567303708591993143 2251799813685248000 29941500012603994191 35079500000000000000000 275935653 1048576 7 8192 (ep767 rfl) rfl) (Enclosure.sfrac_false_div 275935653 1048576) (BSN.sin_reduce3 qz451 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 125389585349821182509056) qz33) 226375608064910080 72057594037927936 Bool.false 707845 1048576 41 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q3 275935653 1048576 226375608064910080 72057594037927936 41 125389585349821182509056 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 707845 1048576 125389585349821182509056 151115727451828646838272 1781893180 2147483648 280911 280636 (ep774 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep776 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz46 (Real.cos qz167)) (@HMul.hMul Real Real Real qz0 qz46 (@Neg.neg Real Real.instNeg (Real.sin qz167))) Bool.false 270394287625 1099511627776 22209593232747 77140636293136384 Bool.false 247409523625 1099511627776 22204979576907 77140636293136384 (@Enclosure.Real.IsNear.mulLit_ff qz46 (Real.cos qz167) 349525 1048576 1 1048576 773605 1048576 495209 574742528 270394287625 1099511627776 22209593232747 77140636293136384 qz323 (@Enclosure.Real.IsNear.recentre' (Real.cos qz167) Bool.false 773605 1048576 990418 1149485056 773605 1048576 495209 574742528 (ep770 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz46 (@Neg.neg Real Real.instNeg (Real.sin qz167)) 349525 1048576 1 1048576 707845 1048576 495209 574742528 247409523625 1099511627776 22204979576907 77140636293136384 qz323 (@Enclosure.Real.IsNear.neg (Real.sin qz167) Bool.true 707845 1048576 495209 574742528 (@Enclosure.Real.IsNear.recentre' (Real.sin qz167) Bool.true 707845 1048576 990418 1149485056 707845 1048576 495209 574742528 (ep775 rfl rfl) rfl)) rfl)

noncomputable def ep777 := @ep765 270394287625 1099511627776 22209593232747 77140636293136384 Bool.false 247409523625 1099511627776 22204979576907 77140636293136384 Bool.false 492377032968197455740928 1791257211037 1099511627776 14507665290497 4537684487831552 Bool.true 425582938332100221206528 193532713789 549755813888 1813564064775 567210560978944 EMRow38.d11 (ep766 ep776) rfl rfl

noncomputable abbrev qz168 := (@HMul.hMul Real Real Real qz267 qz436 qz544)

noncomputable def ep778 := @Enclosure.Complex.IsNear.of_eq qz449 (Complex.mk (@HMul.hMul Real Real Real qz0 qz48 (Real.cos qz168)) (@HMul.hMul Real Real Real qz0 qz48 (@Neg.neg Real Real.instNeg (Real.sin qz168)))) Bool.false 134205673915 549755813888 10537602350705 38570318146568192 Bool.false 110507671263 549755813888 10532588227293 38570318146568192 (BSN.cpow_neg_s_mk qz155 119766 1000 10 qz156 rfl)

noncomputable def ep779 := @Enclosure.Real.IsNear.mulLit_ff qz155 qz544 119766 1000 0 1 10369917190100709 4503599627370496 500000000210477 70159000000000000000 620981751094800757047 2251799813685248000 29941500012603994191 35079500000000000000000 qz157 (BSN.isNear_log_sfrac 10 1 10369917190100709 4503599627370496 500000000210477 70159000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz325) Bool.false 43494585150108164161536 18889465931478580854784 1000000000420954 140318000000000000000 10369917190100709 4503599627370496 500000000210477 70159000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 116991 524288 24973259072661432 36028797018963968 140318 1000000000000000 rfl rfl rfl rfl (ep197 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep780 := nat_lit 12866798841920259556514729134620200625

noncomputable def ep781 := BSN.sin_dyadic_bound_f 1893946155 2147483648 2 1 1048576 280911 ep780 ep81 ep780 ep780 ep82 ep780 809470 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1893946155) qz287 0 1 ep780 ep81 ep780 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1893946155) qz288 0 1 ep780 ep82 ep780 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz452 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 289167161) qz32)

noncomputable def ep782 := @Enclosure.Real.IsNear.cos_image qz168 qz452 Bool.false 289167161 1048576 7 8192 Bool.false 809470 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz168 Bool.false 620981751094800757047 2251799813685248000 29941500012603994191 35079500000000000000000 289167161 1048576 7 8192 (ep779 rfl) rfl) (Enclosure.sfrac_false_div 289167161 1048576) (BSN.cos_reduce3 qz452 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 133274612478843543355392) qz33) 226375608064910080 72057594037927936 Bool.false 809470 1048576 43 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q3 289167161 1048576 226375608064910080 72057594037927936 43 133274612478843543355392 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 809470 1048576 133274612478843543355392 151115727451828646838272 1893946155 2147483648 280911 280636 (ep781 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep783 := nat_lit 459891754797981105873980225771653759544548375857196148656425354780250303190625

noncomputable def ep784 := nat_lit 165554512438440532472212659308876946699911597443613705617609666315250390625

noncomputable def ep785 := nat_lit 1379344155369066436556996251996343524740245304376701218558040845008120408790625

noncomputable def ep786 := BSN.cos_dyadic_bound_f 1893946155 2147483648 3 2 1048576 280911 ep783 ep66 ep784 ep785 ep68 ep784 666534 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1893946155) qz292 0 2 ep783 ep66 ep784 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1893946155) qz293 0 2 ep785 ep68 ep784 rfl rfl rfl rfl) rfl rfl

noncomputable def ep787 := @Enclosure.Real.IsNear.sin_image qz168 qz452 Bool.false 289167161 1048576 7 8192 Bool.true 666534 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz168 Bool.false 620981751094800757047 2251799813685248000 29941500012603994191 35079500000000000000000 289167161 1048576 7 8192 (ep779 rfl) rfl) (Enclosure.sfrac_false_div 289167161 1048576) (BSN.sin_reduce3 qz452 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 133274612478843543355392) qz33) 226375608064910080 72057594037927936 Bool.false 666534 1048576 43 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q3 289167161 1048576 226375608064910080 72057594037927936 43 133274612478843543355392 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 666534 1048576 133274612478843543355392 151115727451828646838272 1893946155 2147483648 280911 280636 (ep786 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep788 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz48 (Real.cos qz168)) (@HMul.hMul Real Real Real qz0 qz48 (@Neg.neg Real Real.instNeg (Real.sin qz168))) Bool.false 134205673915 549755813888 10537602350705 38570318146568192 Bool.false 110507671263 549755813888 10532588227293 38570318146568192 (@Enclosure.Real.IsNear.mulLit_ff qz48 (Real.cos qz168) 331589 1048576 1 1048576 404735 524288 495209 574742528 134205673915 549755813888 10537602350705 38570318146568192 qz327 (@Enclosure.Real.IsNear.recentre' (Real.cos qz168) Bool.false 809470 1048576 990418 1149485056 404735 524288 495209 574742528 (ep782 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz48 (@Neg.neg Real Real.instNeg (Real.sin qz168)) 331589 1048576 1 1048576 333267 524288 495209 574742528 110507671263 549755813888 10532588227293 38570318146568192 qz327 (@Enclosure.Real.IsNear.neg (Real.sin qz168) Bool.true 333267 524288 495209 574742528 (@Enclosure.Real.IsNear.recentre' (Real.sin qz168) Bool.true 666534 1048576 990418 1149485056 333267 524288 495209 574742528 (ep787 rfl rfl) rfl)) rfl)

noncomputable def ep789 := @ep763 134205673915 549755813888 10537602350705 38570318146568192 Bool.false 110507671263 549755813888 10532588227293 38570318146568192 Bool.false 1132314764919451624144896 2059668558867 1099511627776 267705514639859 77140636293136384 Bool.true 45643499826966941401088 41512521263 274877906944 133854944631993 38570318146568192 (ep764 (BSN.head_sum_c_succ qz152 9 10 rfl rfl) (ep777 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep778 ep788) rfl rfl

noncomputable abbrev qz169 := (@HMul.hMul Real Real Real qz267 qz436 qz545)

noncomputable def ep790 := @Enclosure.Complex.IsNear.of_eq qz448 (Complex.mk (@HMul.hMul Real Real Real qz0 qz50 (Real.cos qz169)) (@HMul.hMul Real Real Real qz0 qz50 (@Neg.neg Real Real.instNeg (Real.sin qz169)))) Bool.true 88268821301 1099511627776 20059816640503 77140636293136384 Bool.false 319547151511 1099511627776 20111140053773 77140636293136384 (BSN.cpow_neg_s_mk qz155 119766 1000 11 qz156 rfl)

noncomputable def ep791 := @Enclosure.Real.IsNear.mulLit_ff qz155 qz545 119766 1000 0 1 10799156221662949 4503599627370496 500000000210477 70159000000000000000 646685872021842374967 2251799813685248000 29941500012603994191 35079500000000000000000 qz157 (BSN.isNear_log_sfrac 11 1 10799156221662949 4503599627370496 500000000210477 70159000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz329) Bool.false 45294944137145793642496 18889465931478580854784 1000000000420954 140318000000000000000 10799156221662949 4503599627370496 500000000210477 70159000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 166961 524288 24973259072661432 36028797018963968 140318 1000000000000000 rfl rfl rfl rfl (ep211 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep792 := nat_lit 2182627540504812719467968937310080984004157700855317144499687552676957163421696

noncomputable def ep793 := nat_lit 3718951661292584519643014470223645290036933045491049381839002819948634505216

noncomputable def ep794 := nat_lit 6540444718191852989364620782989795661432399236474969334735384652390974221254656

noncomputable def ep795 := BSN.cos_dyadic_bound_f 2794490044 2147483648 3 2 1048576 280911 ep792 ep66 ep793 ep794 ep68 ep793 279193 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2794490044) qz292 0 2 ep792 ep66 ep793 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2794490044) qz293 0 2 ep794 ep68 ep793 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz453 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 301136575) qz32)

noncomputable def ep796 := @Enclosure.Real.IsNear.cos_image qz169 qz453 Bool.false 301136575 1048576 7 8192 Bool.true 279193 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz169 Bool.false 646685872021842374967 2251799813685248000 29941500012603994191 35079500000000000000000 301136575 1048576 7 8192 (ep791 rfl) rfl) (Enclosure.sfrac_false_div 301136575 1048576) (BSN.cos_reduce2 qz453 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 196644755030727815331840) qz33) 226375608064910080 72057594037927936 Bool.false 279193 1048576 45 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q2 301136575 1048576 226375608064910080 72057594037927936 45 196644755030727815331840 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 279193 1048576 196644755030727815331840 151115727451828646838272 2794490044 2147483648 280911 280636 (ep795 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep797 := nat_lit 3925754411579628827426629675581966854975454315103178020593966392562563986554880

noncomputable def ep798 := nat_lit 10275716584780744649276036650715265384942320552720385497794553595002988842254336

noncomputable def ep799 := BSN.sin_dyadic_bound_f 2794490044 2147483648 3 2 1048576 280911 ep797 ep59 ep793 ep798 ep62 ep793 1010723 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2794490044) qz287 0 2 ep797 ep59 ep793 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2794490044) qz288 0 2 ep798 ep62 ep793 rfl rfl rfl rfl) rfl rfl

noncomputable def ep800 := @Enclosure.Real.IsNear.sin_image qz169 qz453 Bool.false 301136575 1048576 7 8192 Bool.true 1010723 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz169 Bool.false 646685872021842374967 2251799813685248000 29941500012603994191 35079500000000000000000 301136575 1048576 7 8192 (ep791 rfl) rfl) (Enclosure.sfrac_false_div 301136575 1048576) (BSN.sin_reduce2 qz453 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 196644755030727815331840) qz33) 226375608064910080 72057594037927936 Bool.false 1010723 1048576 45 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q2 301136575 1048576 226375608064910080 72057594037927936 45 196644755030727815331840 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1010723 1048576 196644755030727815331840 151115727451828646838272 2794490044 2147483648 280911 280636 (ep799 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep801 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz50 (Real.cos qz169)) (@HMul.hMul Real Real Real qz0 qz50 (@Neg.neg Real Real.instNeg (Real.sin qz169))) Bool.true 88268821301 1099511627776 20059816640503 77140636293136384 Bool.false 319547151511 1099511627776 20111140053773 77140636293136384 (@Enclosure.Real.IsNear.mulLit_ft qz50 (Real.cos qz169) 316157 1048576 1 1048576 279193 1048576 495209 574742528 88268821301 1099511627776 20059816640503 77140636293136384 qz331 (@Enclosure.Real.IsNear.recentre' (Real.cos qz169) Bool.true 279193 1048576 990418 1149485056 279193 1048576 495209 574742528 (ep796 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz50 (@Neg.neg Real Real.instNeg (Real.sin qz169)) 316157 1048576 1 1048576 1010723 1048576 495209 574742528 319547151511 1099511627776 20111140053773 77140636293136384 qz331 (@Enclosure.Real.IsNear.neg (Real.sin qz169) Bool.true 1010723 1048576 495209 574742528 (@Enclosure.Real.IsNear.recentre' (Real.sin qz169) Bool.true 1010723 1048576 990418 1149485056 1010723 1048576 495209 574742528 (ep800 rfl rfl) rfl)) rfl)

noncomputable def ep802 := @ep760 88268821301 1099511627776 20059816640503 77140636293136384 Bool.false 319547151511 1099511627776 20111140053773 77140636293136384 Bool.false ep761 985699868783 549755813888 143882665640181 38570318146568192 Bool.false 42192952350293985591296 153497066459 1099511627776 287821029317759 77140636293136384 (ep762 (BSN.head_sum_c_succ qz152 10 11 rfl rfl) (ep789 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep790 ep801) rfl rfl

noncomputable abbrev qz170 := (@HMul.hMul Real Real Real qz267 qz436 qz546)

noncomputable def ep803 := @Enclosure.Complex.IsNear.of_eq qz447 (Complex.mk (@HMul.hMul Real Real Real qz0 qz52 (Real.cos qz170)) (@HMul.hMul Real Real Real qz0 qz52 (@Neg.neg Real Real.instNeg (Real.sin qz170)))) Bool.true 210885670233 1099511627776 19235922060447 77140636293136384 Bool.true 237213649899 1099511627776 19242024349949 77140636293136384 (BSN.cpow_neg_s_mk qz155 119766 1000 12 qz156 rfl)

noncomputable def ep804 := @Enclosure.Real.IsNear.mulLit_ff qz155 qz546 119766 1000 0 1 11191020447815397 4503599627370496 500000000210477 70159000000000000000 670151877476529418551 2251799813685248000 29941500012603994191 35079500000000000000000 qz157 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 500000000210477 70159000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz333) Bool.false 46938541828353910898688 18889465931478580854784 1000000000420954 140318000000000000000 11191020447815397 4503599627370496 500000000210477 70159000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 212580 524288 24973259072661432 36028797018963968 140318 1000000000000000 rfl rfl rfl rfl (ep226 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep805 := nat_lit 5931527759974425186797433787165654161

noncomputable def ep806 := BSN.sin_dyadic_bound_f 1560600141 2147483648 2 1 1048576 280911 ep805 ep81 ep805 ep805 ep82 ep805 696689 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1560600141) qz287 0 1 ep805 ep81 ep805 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1560600141) qz288 0 1 ep805 ep82 ep805 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz454 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 312063785) qz32)

noncomputable def ep807 := @Enclosure.Real.IsNear.cos_image qz170 qz454 Bool.false 312063785 1048576 7 8192 Bool.true 696689 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz170 Bool.false 670151877476529418551 2251799813685248000 29941500012603994191 35079500000000000000000 312063785 1048576 7 8192 (ep804 rfl) rfl) (Enclosure.sfrac_false_div 312063785 1048576) (BSN.cos_reduce1 qz454 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 109817472109202794086400) qz33) 226375608064910080 72057594037927936 Bool.false 696689 1048576 47 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q1 312063785 1048576 226375608064910080 72057594037927936 47 109817472109202794086400 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 696689 1048576 109817472109202794086400 151115727451828646838272 1560600141 2147483648 280911 280636 (ep806 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep808 := nat_lit 211966585111809051370206388622796645935982527463043528389381727643872554797601

noncomputable def ep809 := nat_lit 35183021567347222171064982081740364904129764980201555710904516715056613921

noncomputable def ep810 := nat_lit 635829389292292459666277035904226457078139322859170182056723373898187551164961

noncomputable def ep811 := BSN.cos_dyadic_bound_f 1560600141 2147483648 3 2 1048576 280911 ep808 ep66 ep809 ep810 ep68 ep809 783667 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1560600141) qz292 0 2 ep808 ep66 ep809 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1560600141) qz293 0 2 ep810 ep68 ep809 rfl rfl rfl rfl) rfl rfl

noncomputable def ep812 := @Enclosure.Real.IsNear.sin_image qz170 qz454 Bool.false 312063785 1048576 7 8192 Bool.false 783667 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz170 Bool.false 670151877476529418551 2251799813685248000 29941500012603994191 35079500000000000000000 312063785 1048576 7 8192 (ep804 rfl) rfl) (Enclosure.sfrac_false_div 312063785 1048576) (BSN.sin_reduce1 qz454 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 109817472109202794086400) qz33) 226375608064910080 72057594037927936 Bool.false 783667 1048576 47 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q1 312063785 1048576 226375608064910080 72057594037927936 47 109817472109202794086400 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 783667 1048576 109817472109202794086400 151115727451828646838272 1560600141 2147483648 280911 280636 (ep811 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep813 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz52 (Real.cos qz170)) (@HMul.hMul Real Real Real qz0 qz52 (@Neg.neg Real Real.instNeg (Real.sin qz170))) Bool.true 210885670233 1099511627776 19235922060447 77140636293136384 Bool.true 237213649899 1099511627776 19242024349949 77140636293136384 (@Enclosure.Real.IsNear.mulLit_ft qz52 (Real.cos qz170) 302697 1048576 1 1048576 696689 1048576 495209 574742528 210885670233 1099511627776 19235922060447 77140636293136384 qz335 (@Enclosure.Real.IsNear.recentre' (Real.cos qz170) Bool.true 696689 1048576 990418 1149485056 696689 1048576 495209 574742528 (ep807 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz52 (@Neg.neg Real Real.instNeg (Real.sin qz170)) 302697 1048576 1 1048576 783667 1048576 495209 574742528 237213649899 1099511627776 19242024349949 77140636293136384 qz335 (@Enclosure.Real.IsNear.neg (Real.sin qz170) Bool.false 783667 1048576 495209 574742528 (@Enclosure.Real.IsNear.recentre' (Real.sin qz170) Bool.false 783667 1048576 990418 1149485056 783667 1048576 495209 574742528 (ep812 rfl rfl) rfl)) rfl)

noncomputable def ep814 := @ep758 210885670233 1099511627776 19235922060447 77140636293136384 Bool.true 237213649899 1099511627776 19242024349949 77140636293136384 Bool.false 967852843947926648520704 1760514067333 1099511627776 307001253340809 77140636293136384 Bool.true 92047356929959725629440 5232286465 68719476736 76765763416927 19285159073284096 (ep759 (BSN.head_sum_c_succ qz152 11 12 rfl rfl) (ep802 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep803 ep813) rfl rfl

noncomputable abbrev qz171 := (@HMul.hMul Real Real Real qz267 qz436 qz547)

noncomputable def ep815 := @Enclosure.Complex.IsNear.of_eq qz446 (Complex.mk (@HMul.hMul Real Real Real qz0 qz54 (Real.cos qz171)) (@HMul.hMul Real Real Real qz0 qz54 (@Neg.neg Real Real.instNeg (Real.sin qz171)))) Bool.false 236627843127 1099511627776 18491473563839 77140636293136384 Bool.false 192358184421 1099511627776 18480793820541 77140636293136384 (BSN.cpow_neg_s_mk qz155 119766 1000 13 qz156 rfl)

noncomputable def ep816 := @Enclosure.Real.IsNear.mulLit_ff qz155 qz547 119766 1000 0 1 11551497052968677 4503599627370496 500000000210477 70159000000000000000 691738298022923284791 2251799813685248000 29941500012603994191 35079500000000000000000 qz157 (BSN.isNear_log_sfrac 13 1 11551497052968677 4503599627370496 500000000210477 70159000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz337) Bool.false 48450490295254733815808 18889465931478580854784 1000000000420954 140318000000000000000 11551497052968677 4503599627370496 500000000210477 70159000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 254545 524288 24973259072661432 36028797018963968 140318 1000000000000000 rfl rfl rfl rfl (ep237 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep817 := nat_lit 851553873234568383650712746044375714535869397735863226925398343285957218795520

noncomputable def ep818 := nat_lit 175243932775191297540113227615091141815009498501992179374705669527878762496

noncomputable def ep819 := nat_lit 2229976415913662123651087484890559580983386026310638559371341375617319007420416

noncomputable def ep820 := BSN.sin_dyadic_bound_f 1907459712 2147483648 3 2 1048576 280911 ep817 ep59 ep818 ep819 ep62 ep818 813649 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1907459712) qz287 0 2 ep817 ep59 ep818 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1907459712) qz288 0 2 ep819 ep62 ep818 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz455 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 161057873) qz27)

noncomputable def ep821 := @Enclosure.Real.IsNear.cos_image qz171 qz455 Bool.false 161057873 524288 7 8192 Bool.false 813649 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz171 Bool.false 691738298022923284791 2251799813685248000 29941500012603994191 35079500000000000000000 161057873 524288 7 8192 (ep816 rfl) rfl) (Enclosure.sfrac_false_div 161057873 524288) (BSN.cos_reduce3 qz455 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 67112772270872074387456) qz29) 226375608064910080 72057594037927936 Bool.false 813649 1048576 48 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q3 161057873 524288 226375608064910080 72057594037927936 48 67112772270872074387456 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 813649 1048576 67112772270872074387456 75557863725914323419136 1907459712 2147483648 280911 280636 (ep820 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep822 := nat_lit 473163371322660298160413798125815437471845225185924900371610059900877512114176

noncomputable def ep823 := nat_lit 1419139626102430511886161167922216130131905656560770716756080768363576778817536

noncomputable def ep824 := BSN.cos_dyadic_bound_f 1907459712 2147483648 3 2 1048576 280911 ep822 ep66 ep818 ep823 ep68 ep818 661427 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1907459712) qz292 0 2 ep822 ep66 ep818 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1907459712) qz293 0 2 ep823 ep68 ep818 rfl rfl rfl rfl) rfl rfl

noncomputable def ep825 := @Enclosure.Real.IsNear.sin_image qz171 qz455 Bool.false 161057873 524288 7 8192 Bool.true 661427 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz171 Bool.false 691738298022923284791 2251799813685248000 29941500012603994191 35079500000000000000000 161057873 524288 7 8192 (ep816 rfl) rfl) (Enclosure.sfrac_false_div 161057873 524288) (BSN.sin_reduce3 qz455 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 67112772270872074387456) qz29) 226375608064910080 72057594037927936 Bool.false 661427 1048576 48 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q3 161057873 524288 226375608064910080 72057594037927936 48 67112772270872074387456 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 661427 1048576 67112772270872074387456 75557863725914323419136 1907459712 2147483648 280911 280636 (ep824 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep826 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz54 (Real.cos qz171)) (@HMul.hMul Real Real Real qz0 qz54 (@Neg.neg Real Real.instNeg (Real.sin qz171))) Bool.false 236627843127 1099511627776 18491473563839 77140636293136384 Bool.false 192358184421 1099511627776 18480793820541 77140636293136384 (@Enclosure.Real.IsNear.mulLit_ff qz54 (Real.cos qz171) 290823 1048576 1 1048576 813649 1048576 495209 574742528 236627843127 1099511627776 18491473563839 77140636293136384 qz339 (@Enclosure.Real.IsNear.recentre' (Real.cos qz171) Bool.false 813649 1048576 990418 1149485056 813649 1048576 495209 574742528 (ep821 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz54 (@Neg.neg Real Real.instNeg (Real.sin qz171)) 290823 1048576 1 1048576 661427 1048576 495209 574742528 192358184421 1099511627776 18480793820541 77140636293136384 qz339 (@Enclosure.Real.IsNear.neg (Real.sin qz171) Bool.true 661427 1048576 495209 574742528 (@Enclosure.Real.IsNear.recentre' (Real.sin qz171) Bool.true 661427 1048576 990418 1149485056 661427 1048576 495209 574742528 (ep825 rfl rfl) rfl)) rfl)

noncomputable def ep827 := @ep755 236627843127 1099511627776 18491473563839 77140636293136384 Bool.false 192358184421 1099511627776 18480793820541 77140636293136384 Bool.false ep756 499285477615 274877906944 40686590863081 9642579536642048 Bool.false 7465793971175624278016 108641600981 1099511627776 325543847488249 77140636293136384 (ep757 (BSN.head_sum_c_succ qz152 12 13 rfl rfl) (ep814 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep815 ep826) rfl rfl

noncomputable abbrev qz172 := (@HMul.hMul Real Real Real qz267 qz436 qz548)

noncomputable def ep828 := @Enclosure.Complex.IsNear.of_eq qz445 (Complex.mk (@HMul.hMul Real Real Real qz0 qz56 (Real.cos qz172)) (@HMul.hMul Real Real Real qz0 qz56 (@Neg.neg Real Real.instNeg (Real.sin qz172)))) Bool.true 48871857013 549755813888 8894113561913 38570318146568192 Bool.true 277123615167 1099511627776 17833134987659 77140636293136384 (BSN.cpow_neg_s_mk qz155 119766 1000 14 qz156 rfl)

noncomputable def ep829 := @Enclosure.Real.IsNear.mulLit_ff qz155 qz548 119766 1000 0 1 11885250371606245 4503599627370496 500000000210477 70159000000000000000 142344889600579353867 450359962737049600 29941500012603994191 35079500000000000000000 qz157 (BSN.isNear_log_sfrac 14 1 11885250371606245 4503599627370496 500000000210477 70159000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz341) Bool.false 49850353174629559828480 18889465931478580854784 1000000000420954 140318000000000000000 11885250371606245 4503599627370496 500000000210477 70159000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 293399 524288 24973259072661432 36028797018963968 140318 1000000000000000 rfl rfl rfl rfl (ep248 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep830 := nat_lit 281161562132588107816236588796123281

noncomputable def ep831 := BSN.sin_dyadic_bound_f 728180403 2147483648 2 1 1048576 280911 ep830 ep81 ep830 ep830 ep82 ep830 348782 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 728180403) qz287 0 1 ep830 ep81 ep830 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 728180403) qz288 0 1 ep830 ep82 ep830 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz456 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 165711261) qz27)

noncomputable def ep832 := @Enclosure.Real.IsNear.cos_image qz172 qz456 Bool.false 165711261 524288 7 8192 Bool.true 348782 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz172 Bool.false 142344889600579353867 450359962737049600 29941500012603994191 35079500000000000000000 165711261 524288 7 8192 (ep829 rfl) rfl) (Enclosure.sfrac_false_div 165711261 524288) (BSN.cos_reduce1 qz456 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 25620570273989422743552) qz29) 226375608064910080 72057594037927936 Bool.false 348782 1048576 50 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q1 165711261 524288 226375608064910080 72057594037927936 50 25620570273989422743552 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 348782 1048576 25620570273989422743552 75557863725914323419136 728180403 2147483648 280911 280636 (ep831 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep833 := BSN.cos_dyadic_bound_f 728180403 2147483648 2 1 1048576 280911 ep830 ep77 ep830 ep830 ep78 ep830 988869 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 728180403) qz292 0 1 ep830 ep77 ep830 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 728180403) qz293 0 1 ep830 ep78 ep830 rfl rfl rfl rfl) rfl rfl

noncomputable def ep834 := @Enclosure.Real.IsNear.sin_image qz172 qz456 Bool.false 165711261 524288 7 8192 Bool.false 988869 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz172 Bool.false 142344889600579353867 450359962737049600 29941500012603994191 35079500000000000000000 165711261 524288 7 8192 (ep829 rfl) rfl) (Enclosure.sfrac_false_div 165711261 524288) (BSN.sin_reduce1 qz456 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 25620570273989422743552) qz29) 226375608064910080 72057594037927936 Bool.false 988869 1048576 50 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q1 165711261 524288 226375608064910080 72057594037927936 50 25620570273989422743552 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 988869 1048576 25620570273989422743552 75557863725914323419136 728180403 2147483648 280911 280636 (ep833 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep835 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz56 (Real.cos qz172)) (@HMul.hMul Real Real Real qz0 qz56 (@Neg.neg Real Real.instNeg (Real.sin qz172))) Bool.true 48871857013 549755813888 8894113561913 38570318146568192 Bool.true 277123615167 1099511627776 17833134987659 77140636293136384 (@Enclosure.Real.IsNear.mulLit_ft qz56 (Real.cos qz172) 280243 1048576 1 1048576 174391 524288 495209 574742528 48871857013 549755813888 8894113561913 38570318146568192 qz343 (@Enclosure.Real.IsNear.recentre' (Real.cos qz172) Bool.true 348782 1048576 990418 1149485056 174391 524288 495209 574742528 (ep832 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz56 (@Neg.neg Real Real.instNeg (Real.sin qz172)) 280243 1048576 1 1048576 988869 1048576 495209 574742528 277123615167 1099511627776 17833134987659 77140636293136384 qz343 (@Enclosure.Real.IsNear.neg (Real.sin qz172) Bool.false 988869 1048576 495209 574742528 (@Enclosure.Real.IsNear.recentre' (Real.sin qz172) Bool.false 988869 1048576 990418 1149485056 988869 1048576 495209 574742528 (ep834 rfl rfl) rfl)) rfl)

noncomputable def ep836 := @ep753 48871857013 549755813888 8894113561913 38570318146568192 Bool.true 277123615167 1099511627776 17833134987659 77140636293136384 Bool.false 261051300344493242318848 949699098217 549755813888 171640477014237 38570318146568192 Bool.true 185247933668627983630336 84241007093 549755813888 85844245618977 19285159073284096 (ep754 (BSN.head_sum_c_succ qz152 13 14 rfl rfl) (ep827 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep828 ep835) rfl rfl

noncomputable abbrev qz173 := (@HMul.hMul Real Real Real qz267 qz436 qz549)

noncomputable def ep837 := @Enclosure.Complex.IsNear.of_eq qz166 (Complex.mk (@HMul.hMul Real Real Real qz0 qz58 (Real.cos qz173)) (@HMul.hMul Real Real Real qz0 qz58 (@Neg.neg Real Real.instNeg (Real.sin qz173)))) Bool.true 104046578523 549755813888 506334724657 2268842243915776 Bool.false 96555716535 549755813888 506220538821 2268842243915776 (BSN.cpow_neg_s_mk qz155 119766 1000 15 qz156 rfl)

noncomputable def ep838 := @Enclosure.Real.IsNear.mulLit_ff qz155 qz549 119766 1000 0 1 12195965485668069 4503599627370496 500000000210477 70159000000000000000 730331001178260975927 2251799813685248000 29941500012603994191 35079500000000000000000 qz157 (BSN.isNear_log_sfrac 15 1 12195965485668069 4503599627370496 500000000210477 70159000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz345) Bool.false 51153586820399524478976 18889465931478580854784 1000000000420954 140318000000000000000 12195965485668069 4503599627370496 500000000210477 70159000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 329571 524288 24973259072661432 36028797018963968 140318 1000000000000000 rfl rfl rfl rfl (ep263 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep839 := nat_lit 238016378553721266975109537492663472389570267565647433571920990725965514048321

noncomputable def ep840 := nat_lit 44360282145422260759726731182902601251725280627144890339745475518715691841

noncomputable def ep841 := nat_lit 713960415096872956403809159015624611966207352135688010935083481226859110761281

noncomputable def ep842 := BSN.cos_dyadic_bound_f 1606476169 2147483648 3 2 1048576 280911 ep839 ep66 ep840 ep841 ep68 ep840 768606 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1606476169) qz292 0 2 ep839 ep66 ep840 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1606476169) qz293 0 2 ep841 ep68 ep840 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz457 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 170043437) qz27)

noncomputable def ep843 := @Enclosure.Real.IsNear.cos_image qz173 qz457 Bool.false 170043437 524288 7 8192 Bool.true 768606 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz173 Bool.false 730331001178260975927 2251799813685248000 29941500012603994191 35079500000000000000000 170043437 524288 7 8192 (ep838 rfl) rfl) (Enclosure.sfrac_false_div 170043437 524288) (BSN.cos_reduce2 qz457 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 56522855286020530765824) qz29) 226375608064910080 72057594037927936 Bool.false 768606 1048576 51 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q2 170043437 524288 226375608064910080 72057594037927936 51 56522855286020530765824 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 768606 1048576 56522855286020530765824 75557863725914323419136 1606476169 2147483648 280911 280636 (ep842 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep844 := nat_lit 6660351503143228307833816802892066721

noncomputable def ep845 := BSN.sin_dyadic_bound_f 1606476169 2147483648 2 1 1048576 280911 ep844 ep81 ep844 ep844 ep82 ep844 713270 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1606476169) qz287 0 1 ep844 ep81 ep844 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1606476169) qz288 0 1 ep844 ep82 ep844 rfl rfl rfl rfl) rfl rfl

noncomputable def ep846 := @Enclosure.Real.IsNear.sin_image qz173 qz457 Bool.false 170043437 524288 7 8192 Bool.true 713270 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz173 Bool.false 730331001178260975927 2251799813685248000 29941500012603994191 35079500000000000000000 170043437 524288 7 8192 (ep838 rfl) rfl) (Enclosure.sfrac_false_div 170043437 524288) (BSN.sin_reduce2 qz457 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 56522855286020530765824) qz29) 226375608064910080 72057594037927936 Bool.false 713270 1048576 51 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q2 170043437 524288 226375608064910080 72057594037927936 51 56522855286020530765824 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 713270 1048576 56522855286020530765824 75557863725914323419136 1606476169 2147483648 280911 280636 (ep845 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep847 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz58 (Real.cos qz173)) (@HMul.hMul Real Real Real qz0 qz58 (@Neg.neg Real Real.instNeg (Real.sin qz173))) Bool.true 104046578523 549755813888 506334724657 2268842243915776 Bool.false 96555716535 549755813888 506220538821 2268842243915776 (@Enclosure.Real.IsNear.mulLit_ft qz58 (Real.cos qz173) 270741 1048576 1 1048576 384303 524288 495209 574742528 104046578523 549755813888 506334724657 2268842243915776 qz347 (@Enclosure.Real.IsNear.recentre' (Real.cos qz173) Bool.true 768606 1048576 990418 1149485056 384303 524288 495209 574742528 (ep843 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz58 (@Neg.neg Real Real.instNeg (Real.sin qz173)) 270741 1048576 1 1048576 356635 524288 495209 574742528 96555716535 549755813888 506220538821 2268842243915776 qz347 (@Enclosure.Real.IsNear.neg (Real.sin qz173) Bool.true 356635 524288 495209 574742528 (@Enclosure.Real.IsNear.recentre' (Real.sin qz173) Bool.true 713270 1048576 990418 1149485056 356635 524288 495209 574742528 (ep846 rfl rfl) rfl)) rfl)

noncomputable def ep848 := @ep751 104046578523 549755813888 506334724657 2268842243915776 Bool.false 96555716535 549755813888 506220538821 2268842243915776 Bool.false 464902389230812918710272 422826259847 274877906944 90124083666703 19285159073284096 Bool.false 6770083112080948330496 6157354721 274877906944 180294240397911 38570318146568192 (ep752 (BSN.head_sum_c_succ qz152 14 15 rfl rfl) (ep836 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep837 ep847) rfl rfl

noncomputable abbrev qz174 := (@HMul.hMul Real Real Real qz267 qz436 qz550)

noncomputable def ep849 := @Enclosure.Complex.IsNear.of_eq qz165 (Complex.mk (@HMul.hMul Real Real Real qz0 qz60 (Real.cos qz174)) (@HMul.hMul Real Real Real qz0 qz60 (@Neg.neg Real Real.instNeg (Real.sin qz174)))) Bool.false 160569665361 1099511627776 16659430998081 77140636293136384 Bool.false 223101780867 1099511627776 16676166866259 77140636293136384 (BSN.cpow_neg_s_mk qz155 119766 1000 16 qz156 rfl)

noncomputable def ep850 := @Enclosure.Real.IsNear.mulLit_ff qz155 qz550 119766 1000 0 1 3121657384082679 1125899906842624 125000000070159 17539750000000000000 186934209131023066557 562949953421312000 7485375004201331397 8769875000000000000000 qz157 (BSN.isNear_log_sfrac 16 1 3121657384082679 1125899906842624 125000000070159 17539750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz349) Bool.false 52372720210750067441664 18889465931478580854784 1000000000561272 140318000000000000000 3121657384082679 1125899906842624 125000000070159 17539750000000000000 (BSN.log_rat_reduce_isNear 16 1 4 32 32 0 524288 24973259072661432 36028797018963968 140318 1000000000000000 rfl rfl rfl rfl (ep278 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep851 := nat_lit 3221059698705265956255734259766318096

noncomputable def ep852 := BSN.sin_dyadic_bound_f 1339675742 2147483648 2 1 1048576 280911 ep851 ep81 ep851 ep851 ep82 ep851 612527 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1339675742) qz287 0 1 ep851 ep81 ep851 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1339675742) qz288 0 1 ep851 ep82 ep851 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz458 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 348192097) qz32)

noncomputable def ep853 := @Enclosure.Real.IsNear.cos_image qz174 qz458 Bool.false 348192097 1048576 7 8192 Bool.false 612527 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz174 Bool.false 186934209131023066557 562949953421312000 7485375004201331397 8769875000000000000000 348192097 1048576 7 8192 (ep850 rfl) rfl) (Enclosure.sfrac_false_div 348192097 1048576) (BSN.cos_reduce3 qz458 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 94271299602438059720704) qz33) 226375608064910080 72057594037927936 Bool.false 612527 1048576 52 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q3 348192097 1048576 226375608064910080 72057594037927936 52 94271299602438059720704 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 612527 1048576 94271299602438059720704 151115727451828646838272 1339675742 2147483648 280911 280636 (ep852 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep854 := BSN.cos_dyadic_bound_f 1339675742 2147483648 2 1 1048576 280911 ep851 ep77 ep851 ep851 ep78 ep851 851069 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1339675742) qz292 0 1 ep851 ep77 ep851 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1339675742) qz293 0 1 ep851 ep78 ep851 rfl rfl rfl rfl) rfl rfl

noncomputable def ep855 := @Enclosure.Real.IsNear.sin_image qz174 qz458 Bool.false 348192097 1048576 7 8192 Bool.true 851069 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz174 Bool.false 186934209131023066557 562949953421312000 7485375004201331397 8769875000000000000000 348192097 1048576 7 8192 (ep850 rfl) rfl) (Enclosure.sfrac_false_div 348192097 1048576) (BSN.sin_reduce3 qz458 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 94271299602438059720704) qz33) 226375608064910080 72057594037927936 Bool.false 851069 1048576 52 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q3 348192097 1048576 226375608064910080 72057594037927936 52 94271299602438059720704 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 851069 1048576 94271299602438059720704 151115727451828646838272 1339675742 2147483648 280911 280636 (ep854 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep856 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz60 (Real.cos qz174)) (@HMul.hMul Real Real Real qz0 qz60 (@Neg.neg Real Real.instNeg (Real.sin qz174))) Bool.false 160569665361 1099511627776 16659430998081 77140636293136384 Bool.false 223101780867 1099511627776 16676166866259 77140636293136384 (@Enclosure.Real.IsNear.mulLit_ff qz60 (Real.cos qz174) 262143 1048576 1 1048576 612527 1048576 495209 574742528 160569665361 1099511627776 16659430998081 77140636293136384 qz351 (@Enclosure.Real.IsNear.recentre' (Real.cos qz174) Bool.false 612527 1048576 990418 1149485056 612527 1048576 495209 574742528 (ep853 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz60 (@Neg.neg Real Real.instNeg (Real.sin qz174)) 262143 1048576 1 1048576 851069 1048576 495209 574742528 223101780867 1099511627776 16676166866259 77140636293136384 qz351 (@Enclosure.Real.IsNear.neg (Real.sin qz174) Bool.true 851069 1048576 495209 574742528 (@Enclosure.Real.IsNear.recentre' (Real.sin qz174) Bool.true 851069 1048576 990418 1149485056 851069 1048576 495209 574742528 (ep855 rfl rfl) rfl)) rfl)

noncomputable def ep857 := @ep749 160569665361 1099511627776 16659430998081 77140636293136384 Bool.false 223101780867 1099511627776 16676166866259 77140636293136384 Bool.false 509039442763943096877056 1851874704749 1099511627776 377155765664893 77140636293136384 Bool.false 68095833672280853970944 247731199751 1099511627776 377264647662081 77140636293136384 (ep750 (BSN.head_sum_c_succ qz152 15 16 rfl rfl) (ep848 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep849 ep856) rfl rfl

theorem EMRow38.d12 : Enclosure.Complex.IsNear qz164 Bool.false 1851874704749 1099511627776 377155765664893 77140636293136384 Bool.false 247731199751 1099511627776 377264647662081 77140636293136384 := ep748 (BSN.head_sum_c_succ qz152 16 17 rfl rfl) (ep857 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep858 := nat_lit 412887530242297288357194196832929

noncomputable def ep859 := nat_lit 148839056589473405032363720704000

noncomputable def ep860 := nat_lit 10838183447884839169043778230482528640693

noncomputable def ep861 := nat_lit 1465256594976582002263510542119388315648000

noncomputable abbrev qz571 := (@HAdd.hAdd Complex Complex Complex qz579 (@HAdd.hAdd Complex Complex Complex qz579 qz582 (@HMul.hMul Complex Complex Complex qz581 Complex.I (@HDiv.hDiv Complex Complex Complex qz583 (↑qz586) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz459 := qz571

noncomputable abbrev qz175 := (Complex.Stirling.logGammaStirling 1 qz459)

noncomputable abbrev qz572 := (@HAdd.hAdd Complex Complex Complex qz579 qz582 (@HMul.hMul Complex Complex Complex qz581 Complex.I (@HDiv.hDiv Complex Complex Complex qz583 (↑qz586) (2 : Complex))))

noncomputable abbrev qz460 := qz572

noncomputable abbrev qz176 := qz460

noncomputable abbrev qz177 := (@HMul.hMul Real Real Real qz267 (@HDiv.hDiv Real Real Real qz270 qz436 (2 : Real)) (Real.log Real.pi))

noncomputable def ep862 := Complex.re (@HMul.hMul Complex Complex Complex qz62 (Complex.exp (@HMul.hMul Complex Complex Complex qz62 Complex.I ↑(@HSub.hSub Real Real Real qz356 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz175 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz176 (@Nat.cast Complex Complex.instNatCast j))))) qz177))) (zetaApproximant qz152 1 24))

noncomputable def ep863 := @Enclosure.Real.IsNear.of_eq ep862 (@HSub.hSub Real Real Real qz356 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz356 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz175 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz176 (@Nat.cast Complex Complex.instNatCast j))))) qz177)) (Complex.re (zetaApproximant qz152 1 24))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz356 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz175 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz176 (@Nat.cast Complex Complex.instNatCast j))))) qz177)) (Complex.im (zetaApproximant qz152 1 24))))

noncomputable def ep864 := nat_lit 2202089786588105738174631104357

noncomputable def ep865 := @Enclosure.Real.IsNear.subLit_tt_n (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz356 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz175 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz176 (@Nat.cast Complex Complex.instNatCast j))))) qz177)) (Complex.re (zetaApproximant qz152 1 24))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz356 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz175 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz176 (@Nat.cast Complex Complex.instNatCast j))))) qz177)) (Complex.im (zetaApproximant qz152 1 24))) ep864

noncomputable def ep866 := nat_lit 793808301810524826839273177088

noncomputable def ep867 := nat_lit 719776145698350060423141556400193437639

noncomputable def ep868 := nat_lit 97683772998438800150900702807959221043200

noncomputable def ep869 := nat_lit 8609485945075101098270468017

noncomputable def ep870 := nat_lit 297678113178946810064727441408000

noncomputable def ep871 := nat_lit 10385315602397065674163721119906769027

noncomputable def ep872 := nat_lit 366314148744145500565877635529847078912000

noncomputable def ep873 := nat_lit 655507098440759445522929166574928260438396349105445498733461504

noncomputable def ep874 := @Enclosure.Real.IsNear.mulLit_tf (Real.cos (@HSub.hSub Real Real Real qz356 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz175 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz176 (@Nat.cast Complex Complex.instNatCast j))))) qz177)) (Complex.re (zetaApproximant qz152 1 24)) 1048575 1048576 26272641

noncomputable def ep875 := nat_lit 157505885601037532234792297

noncomputable def ep876 := nat_lit 56777594219006883633561600

noncomputable def ep877 := nat_lit 8465467909358652450161303813

noncomputable def ep878 := nat_lit 1327819744270434649615682764800

noncomputable def ep879 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz356 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz175 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz176 (@Nat.cast Complex Complex.instNatCast j))))) qz177)) Bool.true 1048575 1048576 52545282

noncomputable abbrev qz461 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 121885817) qz32)

noncomputable def ep880 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz356 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz175 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz176 (@Nat.cast Complex Complex.instNatCast j))))) qz177) qz461 Bool.false 121885817 1048576 367

noncomputable def ep881 := nat_lit 6409380285244976203520299

noncomputable def ep882 := nat_lit 18391760896000000000000000000

noncomputable def ep883 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz356 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz175 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz176 (@Nat.cast Complex Complex.instNatCast j))))) qz177) Bool.false 209398240314421494387 1801439850948198400 ep881 ep882

noncomputable def ep884 := nat_lit 2208048888244976203520299

noncomputable def ep885 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz175 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz176 (@Nat.cast Complex Complex.instNatCast j))))) qz177 1664433300773256711231 9007199254740992000 ep884 ep882 4492482543 65536000

noncomputable def ep886 := nat_lit 68615615386229635280732160000

noncomputable def ep887 := nat_lit 2049996572371039865626917

noncomputable def ep888 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz63 qz175 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz176 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 424095897480856522673 4503599627370496000 ep887 ep320 Bool.false 1664433300773256711231 9007199254740992000

noncomputable def ep889 := nat_lit 540934144000000000000000000

noncomputable def ep890 := nat_lit 2076976888226584442624299

noncomputable def ep891 := @Enclosure.Complex.IsNear.subLitP qz175 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz176 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 387233883343275309673 4503599627370496000 118660504251169716511701 ep889 Bool.false 1692504671509049959231 9007199254740992000 ep890

noncomputable def ep892 := nat_lit 1909958125864141508783707261195255808

noncomputable def ep893 := nat_lit 468496324571592726029904176832577536

noncomputable abbrev qz462 := (@HSub.hSub Complex Complex Complex qz552 qz571 qz555)

noncomputable abbrev qz463 := (Complex.log qz571)

noncomputable abbrev qz178 := (@HSub.hSub Complex Complex Complex qz353 (@HMul.hMul Complex Complex Complex qz352 qz462 qz463) qz459)

noncomputable abbrev qz179 := qz459

noncomputable def ep894 := @Enclosure.Complex.IsNear.of_eq qz175 (@HAdd.hAdd Complex Complex Complex qz4 (@HAdd.hAdd Complex Complex Complex qz4 qz178 qz68) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz63 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz71 qz179 (@HSub.hSub Int Int Int qz365 qz73 (@HMul.hMul Int Int Int qz366 qz74 (@Nat.cast Int instNatCastInt k)))))) Bool.true 387233883343275309673

noncomputable def ep895 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz4 qz178 qz68) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz63 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz71 qz179 (@HSub.hSub Int Int Int qz365 qz73 (@HMul.hMul Int Int Int qz366 qz74 (@Nat.cast Int instNatCastInt k))))) Bool.true 387234118491555117673 4503599627370496000

noncomputable def ep896 := nat_lit 13305254918899572772558459633664

noncomputable def ep897 := nat_lit 14538504424917185085854556618752000

noncomputable def ep898 := @ep895 3621229767498866907 16508000000000000000000 Bool.false 1692517188295218619199 9007199254740992000 15845750046337423617 140318000000000000000000 Bool.false 1794039 34359738368 3 34359738368 Bool.true 11936937493 8589934592000 19961 8589934592000 Bool.true ep896 387233883343275309673 4503599627370496000 118660504251169716511701 ep889 Bool.false ep897

noncomputable def ep899 := @Enclosure.Complex.IsNear.addLitP qz178 qz68 Bool.true 391372645898765613673 4503599627370496000 1787000000326581891 8254000000000000000000

noncomputable def ep900 := nat_lit 50755550378925112383635456

noncomputable def ep901 := @ep899 Bool.false 1692517188295218619199 9007199254740992000 15845750046337423617 140318000000000000000000 Bool.false 120447 131072 3 1048576 Bool.false 0 1 0 1 Bool.true ep900 387234118491555117673 4503599627370496000 3621229767498866907 16508000000000000000000 Bool.false 1692517188295218619199 1692517188295218619199 9007199254740992000

noncomputable abbrev qz180 := (@HMul.hMul Complex Complex Complex qz352 qz462 qz463)

noncomputable def ep902 := @Enclosure.Complex.IsNear.subLitP qz180 qz179 Bool.true 381239546737181997673 4503599627370496000 1787000000326581891 8254000000000000000000 Bool.false 446379060253374688627

noncomputable def ep903 := nat_lit 1565490583595062454692000

noncomputable def ep904 := nat_lit 1354013750636174895359200

noncomputable def ep905 := @ep902 1801439850948198400 15845750046337423617 140318000000000000000000 Bool.false 9000 4000 0 1 Bool.false 239532 4000 0 1 Bool.true ep903 391372645898765613673 4503599627370496000 1787000000326581891 8254000000000000000000 Bool.false ep904 1692517188295218619199 9007199254740992000 15845750046337423617 140318000000000000000000

noncomputable abbrev qz181 := qz462

noncomputable abbrev qz182 := qz463

noncomputable def ep906 := @Enclosure.Complex.IsNear.mul qz181 qz182 Bool.true 381239546737181997673 4503599627370496000 1787000000326581891 8254000000000000000000 Bool.false 446379060253374688627 1801439850948198400 15845750046337423617

noncomputable abbrev qz183 := (Complex.re qz462)

noncomputable abbrev qz184 := (Complex.re qz463)

noncomputable abbrev qz185 := (Complex.im qz462)

noncomputable abbrev qz186 := (Complex.im qz463)

noncomputable def ep907 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz183 qz184) (@HMul.hMul Real Real Real qz0 qz185 qz186) 258071439408739915 36028797018963968 1750000005402243 561272000000000000000 51687309582909310881 562949953421312000

noncomputable def ep908 := nat_lit 1716950280624469638859176649380855808

noncomputable def ep909 := @Enclosure.Real.IsNear.mulLit_ff qz183 qz184 7000 4000 0 1 36867348486962845 9007199254740992 250000000771749 140318000000000000000

noncomputable def ep910 := @Enclosure.Complex.IsNear.re_isNear qz181 Bool.false 7000 4000 0 1 Bool.false 239532 4000 0 1

noncomputable abbrev qz187 := (Enclosure.sfrac Bool.false 239532 4000)

noncomputable def ep911 := @Enclosure.Complex.IsNear.of_eq qz181 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz187) Bool.false 7000 4000 0 1 Bool.false 239532 4000 0

noncomputable abbrev qz464 := (Complex.log (Complex.mk qz83 qz187))

noncomputable def ep912 := @Enclosure.Complex.IsNear.of_eq qz182 qz464 Bool.false 36867348486962845 9007199254740992 250000000771749 140318000000000000000 Bool.false 863138279359907 562949953421312 500000000070159 140318000000000000000

noncomputable def ep913 := nat_lit 371597802807114879789914766876751923558251699039857990058449156807334373210086528375635986897916129606473634283520

noncomputable def ep914 := nat_lit 9714909696409618477010097632727502773108969610381313931995066846055269022436495219105274547570468917409956757504

noncomputable def ep915 := nat_lit 79504690717676269950680768970409259684065340878012105811023377699323546363078778685076336699326056439480320

noncomputable def ep916 := BSN.log_dyadic_bound 24688579024 90224579024 6 5 ep913 1048576 280636 ep914 ep915 588856 114913158048 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 24688579024) (BSN.artanhQ 90224579024) 0 5 ep914 ep913 ep915 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz573 := (Real.log (Enclosure.sfrac Bool.false 57456579024 16000000))

noncomputable def ep917 := @Enclosure.Real.IsNear.mulLit_ff qz84 qz573 1 2 0 1 36867348486962845 4503599627370496 250000000771749 70159000000000000000 36867348486962845 9007199254740992 250000000771749 140318000000000000000 qz370 (BSN.isNear_log_sfrac 57456579024 16000000 36867348486962845 4503599627370496 250000000771749 70159000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 57456579024) qz371)) Bool.false 309265734456524417269760 37778931862957161709568 1000000003086996 280636000000000000000 36867348486962845 4503599627370496 250000000771749 70159000000000000000 (BSN.log_rat_reduce_isNear 57456579024 16000000 11 114913158048 65536000000 588856 1048576 24973259072661432 36028797018963968 280636 1000000000000000 rfl rfl rfl rfl (ep916 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep918 := BSN.arctan_dyadic_bound_f 9000 239532 1 0 1048576 280636 0 1 1 0 1 1 39379 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 239532) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 239532) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz465 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 239532)))

noncomputable def ep919 := @Enclosure.Real.IsNear.subLit_ff_p qz85 qz465 884279719003555 562949953421312 1 2000000000000000 39379 1048576 1 280636 905066084418093842432 863138279359907 562949953421312 500000000070159 140318000000000000000 qz86 (ep918 rfl) rfl rfl

noncomputable abbrev qz466 := (Complex.mk qz83 qz187)

noncomputable abbrev qz467 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 239532) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep920 := @Enclosure.Complex.IsNear.re_isNear qz182 Bool.false 36867348486962845 9007199254740992 250000000771749 140318000000000000000 Bool.false 863138279359907 562949953421312 500000000070159 140318000000000000000 (ep912 (@congrArg Complex Complex qz179 qz466 Complex.log (BSN.w_shift_mk qz155 Bool.false 119766 1000 2 qz156 rfl)) (@Enclosure.Complex.IsNear.of_parts qz464 Bool.false 36867348486962845 9007199254740992 250000000771749 140318000000000000000 Bool.false 863138279359907 562949953421312 500000000070159 140318000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz464) (@HMul.hMul Real Real Real qz0 qz84 qz573) Bool.false 36867348486962845 9007199254740992 250000000771749 140318000000000000000 (Enclosure.clog_re_eq 9000 239532 4000 57456579024 16000000 rfl rfl rfl) (ep917 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz464) qz467 Bool.false 863138279359907 562949953421312 500000000070159 140318000000000000000 (Enclosure.clog_im_eq 9000 239532 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz467 (@HSub.hSub Real Real Real qz356 qz85 qz465) Bool.false 863138279359907 562949953421312 500000000070159 140318000000000000000 (BSN.arctan_recip 239532 9000 rfl rfl) ep919))))

noncomputable def ep921 := @Enclosure.Real.IsNear.mulLit_ff qz185 qz186 239532 4000 0 1 863138279359907 562949953421312 500000000070159 140318000000000000000

noncomputable def ep922 := @Enclosure.Complex.IsNear.im_isNear qz181 Bool.false 7000 4000 0 1 Bool.false 239532 4000 0 1

noncomputable def ep923 := @Enclosure.Complex.IsNear.im_isNear qz182 Bool.false 36867348486962845 9007199254740992 250000000771749 140318000000000000000 Bool.false 863138279359907 562949953421312 500000000070159 140318000000000000000 (ep912 (@congrArg Complex Complex qz179 qz466 Complex.log (BSN.w_shift_mk qz155 Bool.false 119766 1000 2 qz156 rfl)) (@Enclosure.Complex.IsNear.of_parts qz464 Bool.false 36867348486962845 9007199254740992 250000000771749 140318000000000000000 Bool.false 863138279359907 562949953421312 500000000070159 140318000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz464) (@HMul.hMul Real Real Real qz0 qz84 qz573) Bool.false 36867348486962845 9007199254740992 250000000771749 140318000000000000000 (Enclosure.clog_re_eq 9000 239532 4000 57456579024 16000000 rfl rfl rfl) (ep917 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz464) qz467 Bool.false 863138279359907 562949953421312 500000000070159 140318000000000000000 (Enclosure.clog_im_eq 9000 239532 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz467 (@HSub.hSub Real Real Real qz356 qz85 qz465) Bool.false 863138279359907 562949953421312 500000000070159 140318000000000000000 (BSN.arctan_recip 239532 9000 rfl rfl) ep919))))

noncomputable abbrev qz468 := (Enclosure.Real.IsNear.const Bool.false 239532 4000)

noncomputable abbrev qz188 := (@ep911 1 (BSN.w_sub_half_mk qz436 Bool.false 119766 1000 2 qz437 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) (Enclosure.sfrac Bool.false 239532 4000) Bool.false 7000 4000 0 1 Bool.false 239532 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) qz468))

noncomputable def ep924 := @ep907 29941500004201331397 140318000000000000000000 ep908 381239546737181997673 4503599627370496000 1787000000326581891 8254000000000000000000 (@ep909 258071439408739915 36028797018963968 1750000005402243 561272000000000000000 (ep910 qz188) ep920 rfl) (@ep921 51687309582909310881 562949953421312000 29941500004201331397 140318000000000000000000 (ep922 qz188) ep923 rfl) rfl

noncomputable def ep925 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz183 qz186) (@HMul.hMul Real Real Real qz0 qz185 qz184) 6041967955519349 2251799813685248 3500000000491113 561272000000000000000 441545485888959209427 1801439850948198400

noncomputable def ep926 := nat_lit 1005156284711545214749716325383274496

noncomputable def ep927 := @Enclosure.Real.IsNear.mulLit_ff qz183 qz186 7000 4000 0 1 863138279359907 562949953421312 500000000070159 140318000000000000000

noncomputable def ep928 := @Enclosure.Real.IsNear.mulLit_ff qz185 qz184 239532 4000 0 1 36867348486962845 9007199254740992 250000000771749 140318000000000000000

noncomputable def ep929 := @ep925 14970750046214645367 140318000000000000000000 ep926 446379060253374688627 1801439850948198400 15845750046337423617 140318000000000000000000 (@ep927 6041967955519349 2251799813685248 3500000000491113 561272000000000000000 (ep910 qz188) ep923 rfl) (@ep928 441545485888959209427 1801439850948198400 14970750046214645367 140318000000000000000000 (ep922 qz188) ep920 rfl) rfl

noncomputable def ep930 := @Enclosure.Complex.IsNear.of_eq qz179 qz466 Bool.false 9000 4000 0 1 Bool.false 239532 4000 0 1 (BSN.w_shift_mk qz155 Bool.false 119766 1000 2 qz156 rfl)

noncomputable abbrev qz469 := (ep930 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9000 4000) (Enclosure.sfrac Bool.false 239532 4000) Bool.false 9000 4000 0 1 Bool.false 239532 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 239532 4000)))

noncomputable abbrev qz189 := qz469

noncomputable def ep931 := ep905 (@ep906 140318000000000000000000 (ep924 rfl) (ep929 rfl)) qz189 rfl rfl rfl rfl rfl rfl

noncomputable def ep932 := @ep901 15845750046337423617 140318000000000000000000 (ep931 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz89 (↑qz2) Bool.false 120447 131072 3 1048576 Bool.false 0 1 0 1 (@ep365 131072 3 1048576 (ep367 rfl) (ep369 rfl) rfl rfl) (@ep370 1 0 1 (ep372 rfl) (ep374 rfl) rfl rfl))

noncomputable abbrev qz470 := (@HPow.hPow Complex Int Complex qz557 qz571 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz190 := qz470

noncomputable def ep933 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz63 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz71 qz179 (@HSub.hSub Int Int Int qz365 qz73 (@HMul.hMul Int Int Int qz366 qz74 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz63 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz71 qz179 (@HSub.hSub Int Int Int qz365 qz73 (@HMul.hMul Int Int Int qz366 qz74 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92) qz190)) Bool.false 1794039 34359738368 3 34359738368

noncomputable def ep934 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz63 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz71 qz179 (@HSub.hSub Int Int Int qz365 qz73 (@HMul.hMul Int Int Int qz366 qz74 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92) qz190) Bool.false 0 1 0 1 Bool.false

noncomputable def ep935 := @ep934 0 1 0 1 Bool.false 1794039 34359738368 3 34359738368 Bool.true 11936937493 8589934592000 19961 8589934592000 Bool.false 1794039 1794039 34359738368 3 34359738368 Bool.true 11936937493 11936937493 8589934592000 19961

noncomputable def ep936 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz63 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz71 qz179 (@HSub.hSub Int Int Int qz365 qz73 (@HMul.hMul Int Int Int qz366 qz74 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep937 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92) qz190 Bool.false 1794039 34359738368 3 34359738368 Bool.true 11936937493 8589934592000 19961 8589934592000

noncomputable abbrev qz191 := (Complex.re qz470)

noncomputable abbrev qz192 := (Complex.im qz470)

noncomputable def ep938 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz191) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz192) 1794039 34359738368 3 34359738368 0 1 0

noncomputable def ep939 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz191 1 12 0 1 5382117 8589934592 9 8589934592 1794039

noncomputable def ep940 := @Enclosure.Complex.IsNear.re_isNear qz190 Bool.false 5382117 8589934592 9 8589934592 Bool.true 35810812479 2147483648000 59883 2147483648000

noncomputable abbrev qz471 := (@HPow.hPow Complex Nat Complex qz559 qz571 1)

noncomputable abbrev qz193 := (@Inv.inv Complex Complex.instInv qz471)

noncomputable def ep941 := @Enclosure.Complex.IsNear.of_eq qz190 qz193 Bool.false 5382117 8589934592 9 8589934592 Bool.true 35810812479 2147483648000 59883

noncomputable def ep942 := @Enclosure.Complex.IsNear.of_parts qz193 Bool.false 5382117 8589934592 9 8589934592 Bool.true 35810812479 2147483648000 59883

noncomputable abbrev qz194 := (Complex.re qz471)

noncomputable abbrev qz195 := qz471

noncomputable def ep943 := @Enclosure.Real.IsNear.mulLit_ff qz194 (@Inv.inv Real Real.instInv (@DFunLike.coe qz98 Complex (fun (x : Complex) => Real) qz99 Complex.normSq qz195)) 9000 4000 0 1 598013 2147483648 1 2147483648

noncomputable def ep944 := @Enclosure.Complex.IsNear.re_isNear qz195 Bool.false 9000 4000 0 1 Bool.false 239532 4000 0 1

noncomputable def ep945 := @Enclosure.Complex.IsNear.of_eq qz195 qz179 Bool.false 9000 4000 0 1 Bool.false 239532 4000 0

noncomputable def ep946 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz98 Complex (fun (x : Complex) => Real) qz99 Complex.normSq qz195)) Bool.false 598013 2147483648 1 2147483648 598013 2147483648 1

noncomputable abbrev qz196 := (Complex.im qz471)

noncomputable def ep947 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz98 Complex (fun (x : Complex) => Real) qz99 Complex.normSq qz195) (@HAdd.hAdd Real Real Real qz380 (@HMul.hMul Real Real Real qz0 qz194 qz194) (@HMul.hMul Real Real Real qz0 qz196 qz196)) Bool.false 3591036189 1000000 0 1

noncomputable def ep948 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz194 qz194) (@HMul.hMul Real Real Real qz0 qz196 qz196) 81 16 0 1 3585973689 1000000

noncomputable def ep949 := @Enclosure.Real.IsNear.mulLit_ff qz194 qz194 9000 4000 0 1 9000 4000 0 1

noncomputable def ep950 := @Enclosure.Real.IsNear.mulLit_ff qz196 qz196 239532 4000 0 1 239532 4000 0 1

noncomputable def ep951 := @Enclosure.Complex.IsNear.im_isNear qz195 Bool.false 9000 4000 0 1 Bool.false 239532 4000 0 1

noncomputable abbrev qz197 := (ep944 (@ep945 1 (BSN.pow_one_c qz459) qz469))

noncomputable abbrev qz198 := (ep951 (@ep945 1 (BSN.pow_one_c qz459) qz469))

noncomputable def ep952 := @ep948 0 1 57456579024 3591036189 1000000 0 1 (@ep949 81 16 0 1 qz197 qz197 rfl) (@ep950 3585973689 1000000 0 1 qz198 qz198 rfl)

noncomputable def ep953 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz98 Complex (fun (x : Complex) => Real) qz99 Complex.normSq qz195) 3591036189 1000000 0 1 299006 299007 1073741824 (ep947 (Enclosure.Complex.normSq_eq_mul_add_mul qz195) (ep952 rfl rfl)) rfl

noncomputable def ep954 := @Enclosure.Real.IsNear.of_eq (Complex.re qz193) (@HMul.hMul Real Real Real qz0 qz194 (@Inv.inv Real Real.instInv (@DFunLike.coe qz98 Complex (fun (x : Complex) => Real) qz99 Complex.normSq qz195))) Bool.false 5382117 8589934592 9 8589934592 (Enclosure.Complex.inv_re_eq_mul qz195) (@ep943 5382117 8589934592 9 8589934592 qz197 (@ep946 2147483648 (ep953 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep955 := @Enclosure.Real.IsNear.of_eq (Complex.im qz193) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz196) (@Inv.inv Real Real.instInv (@DFunLike.coe qz98 Complex (fun (x : Complex) => Real) qz99 Complex.normSq qz195))) Bool.true 35810812479 2147483648000 59883 2147483648000 (Enclosure.Complex.inv_im_eq_mul qz195)

noncomputable def ep956 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz196) (@Inv.inv Real Real.instInv (@DFunLike.coe qz98 Complex (fun (x : Complex) => Real) qz99 Complex.normSq qz195)) 239532 4000 0 1 598013 2147483648 1

noncomputable def ep957 := @ep956 2147483648 35810812479 2147483648000 59883 2147483648000 (@Enclosure.Real.IsNear.neg qz196 Bool.false 239532 4000 0 1 qz198) (@ep946 2147483648 (ep953 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep958 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz192 0 1 0 1 35810812479 2147483648000 59883 2147483648000 0

noncomputable def ep959 := @Enclosure.Complex.IsNear.im_isNear qz190 Bool.false 5382117 8589934592 9 8589934592 Bool.true 35810812479 2147483648000 59883 2147483648000

noncomputable abbrev qz199 := (@ep941 2147483648000 (BSN.zpow_one_sub_two_mul qz459 1 1 rfl rfl) (@ep942 2147483648000 ep954 (ep955 ep957)))

noncomputable def ep960 := @ep938 1 1794039 1794039 34359738368 3 34359738368 (@ep939 34359738368 3 34359738368 ep384 (ep940 qz199) rfl) (@ep958 1 0 1 ep404 (ep959 qz199) rfl) rfl

noncomputable def ep961 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz192) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz191) 11936937493 8589934592000 19961 8589934592000 0 1 0

noncomputable def ep962 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz192 1 12 0 1 35810812479 2147483648000 59883 2147483648000 11936937493

noncomputable def ep963 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz191 0 1 0 1 5382117 8589934592 9 8589934592 0

noncomputable def ep964 := @ep961 1 11936937493 11936937493 8589934592000 19961 8589934592000 (@ep962 8589934592000 19961 8589934592000 ep384 (ep959 qz199) rfl) (@ep963 1 0 1 ep404 (ep940 qz199) rfl) rfl

noncomputable def ep965 := @ep935 8589934592000 (@ep936 0 1 0 1 (BSN.stirling_sum_base qz179) qz105) (ep937 (ep960 rfl) (ep964 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep966 := @ep898 1692504671509049959231 9007199254740992000 ep890 ep882 (ep932 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep933 Bool.true 11936937493 8589934592000 19961 8589934592000 (BSN.stirling_sum_succ qz179 0 1 rfl) (ep965 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep967 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz176 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz155 2) Bool.false 36862014137581213 4503599627370496 250000000771749 70159000000000000000 Bool.false 877230335493539 281474976710656

noncomputable abbrev qz200 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz273 qz460 qz376))

noncomputable def ep968 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz155 2) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz155 1) qz200) Bool.false 36862014137581213 4503599627370496 250000000771749 70159000000000000000 Bool.false 877230335493539 281474976710656 500000000070159 70159000000000000000

noncomputable def ep969 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz155 1) qz200 Bool.false 36861073539743389 9007199254740992 250000000771749 140318000000000000000 Bool.false 881929835021731 562949953421312 500000000070159 140318000000000000000 Bool.false

noncomputable def ep970 := nat_lit 664047012536546825355699360366592

noncomputable def ep971 := nat_lit 987673553011699357922241806336

noncomputable abbrev qz201 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz273 qz460 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep972 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz155 1) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz155 0) qz201) Bool.false 36861073539743389 9007199254740992 250000000771749 140318000000000000000 Bool.false 881929835021731 562949953421312 500000000070159 140318000000000000000

noncomputable def ep973 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz155 0) qz201 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz472 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz187))

noncomputable def ep974 := @Enclosure.Complex.IsNear.of_eq qz201 qz472 Bool.false 36861073539743389 9007199254740992 250000000771749 140318000000000000000 Bool.false 881929835021731 562949953421312 500000000070159 140318000000000000000

noncomputable def ep975 := nat_lit 368316048626703791933615093043796859193534317180072500210906894555977821157504985964557618740620178127689634283520

noncomputable def ep976 := nat_lit 9581637881863152349782852315105332581727859255637912651674836435361589350379443833289057306961969038293156757504

noncomputable def ep977 := nat_lit 76965691847254715455887912781467403108436102770818493612015575018277027145313778419036594484100712439480320

noncomputable def ep978 := BSN.log_dyadic_bound 24608579024 90144579024 6 5 ep975 1048576 280636 ep976 ep977 587395 114753158048 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 24608579024) (BSN.artanhQ 90144579024) 0 5 ep976 ep975 ep977 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep979 := @Enclosure.Real.IsNear.mulLit_ff qz84 (Real.log (Enclosure.sfrac Bool.false 57376579024 16000000)) 1 2 0 1 36861073539743389 4503599627370496 250000000771749 70159000000000000000 36861073539743389 9007199254740992 250000000771749 140318000000000000000 qz370 (BSN.isNear_log_sfrac 57376579024 16000000 36861073539743389 4503599627370496 250000000771749 70159000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 57376579024) qz371)) Bool.false 309213096384079710912512 37778931862957161709568 1000000003086996 280636000000000000000 36861073539743389 4503599627370496 250000000771749 70159000000000000000 (BSN.log_rat_reduce_isNear 57376579024 16000000 11 114753158048 65536000000 587395 1048576 24973259072661432 36028797018963968 280636 1000000000000000 rfl rfl rfl rfl (ep978 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep980 := BSN.arctan_dyadic_bound_f 1000 239532 1 0 1048576 280636 0 1 1 0 1 1 4377 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 239532) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 239532) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz473 := (@Nat.cast Real Real.instNatCast 239532)

noncomputable def ep981 := @Enclosure.Real.IsNear.subLit_ff_p qz85 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz382 qz473)) 884279719003555 562949953421312 1 2000000000000000 4377 1048576 1 280636 924770458687746605056 881929835021731 562949953421312 500000000070159 140318000000000000000 qz86 (ep980 rfl) rfl rfl

noncomputable abbrev qz202 := (@HAdd.hAdd Complex Complex Complex qz273 qz460 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz474 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz187)

noncomputable def ep982 := @ep973 36861073539743389 9007199254740992 250000000771749 140318000000000000000 Bool.false 881929835021731 562949953421312 500000000070159 140318000000000000000 Bool.false 36861073539743389 36861073539743389 9007199254740992 250000000771749 140318000000000000000 Bool.false 881929835021731 881929835021731 562949953421312 500000000070159 140318000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz155 0) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz155) qz105) (ep974 (@congrArg Complex Complex qz202 qz474 Complex.log (BSN.w_shift_mk qz155 Bool.false 119766 1000 0 qz156 rfl)) (@Enclosure.Complex.IsNear.of_parts qz472 Bool.false 36861073539743389 9007199254740992 250000000771749 140318000000000000000 Bool.false 881929835021731 562949953421312 500000000070159 140318000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz472) (@HMul.hMul Real Real Real qz0 qz84 (Real.log (Enclosure.sfrac Bool.false 57376579024 16000000))) Bool.false 36861073539743389 9007199254740992 250000000771749 140318000000000000000 (Enclosure.clog_re_eq 1000 239532 4000 57376579024 16000000 rfl rfl rfl) (ep979 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz472) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz473 qz382)) Bool.false 881929835021731 562949953421312 500000000070159 140318000000000000000 (Enclosure.clog_im_eq 1000 239532 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz473 qz382)) (@HSub.hSub Real Real Real qz356 qz85 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz382 qz473))) Bool.false 881929835021731 562949953421312 500000000070159 140318000000000000000 (BSN.arctan_recip 239532 1000 rfl rfl) ep981)))) rfl rfl

noncomputable abbrev qz475 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz187))

noncomputable def ep983 := @Enclosure.Complex.IsNear.of_eq qz200 qz475 Bool.false 36862954735419037 9007199254740992 250000000771749 140318000000000000000 Bool.false 872530835965347 562949953421312 500000000070159 140318000000000000000

noncomputable def ep984 := nat_lit 369297825154431267436734504090460416147556038263072640329756819737479728026186238590112620501892393971324834283520

noncomputable def ep985 := nat_lit 9621453757908525450691663500109953708869008761523550207915772593899832641477370600366214366725621082028196757504

noncomputable def ep986 := nat_lit 77719617724303764116333637208597567715181168691169366818530432599259047324090244549807542915068315639480320

noncomputable def ep987 := BSN.log_dyadic_bound 24632579024 90168579024 6 5 ep984 1048576 280636 ep985 ep986 587833 114801158048 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 24632579024) (BSN.artanhQ 90168579024) 0 5 ep985 ep984 ep986 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep988 := @Enclosure.Real.IsNear.mulLit_ff qz84 (Real.log (Enclosure.sfrac Bool.false 57400579024 16000000)) 1 2 0 1 36862954735419037 4503599627370496 250000000771749 70159000000000000000 36862954735419037 9007199254740992 250000000771749 140318000000000000000 qz370 (BSN.isNear_log_sfrac 57400579024 16000000 36862954735419037 4503599627370496 250000000771749 70159000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 57400579024) qz371)) Bool.false 309228876997174017130496 37778931862957161709568 1000000003086996 280636000000000000000 36862954735419037 4503599627370496 250000000771749 70159000000000000000 (BSN.log_rat_reduce_isNear 57400579024 16000000 11 114801158048 65536000000 587833 1048576 24973259072661432 36028797018963968 280636 1000000000000000 rfl rfl rfl rfl (ep987 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep989 := BSN.arctan_dyadic_bound_f 5000 239532 1 0 1048576 280636 0 1 1 0 1 1 21884 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 239532) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 239532) 0 0 rfl) rfl rfl rfl

noncomputable def ep990 := @Enclosure.Real.IsNear.subLit_ff_p qz85 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz386 qz473)) 884279719003555 562949953421312 1 2000000000000000 21884 1048576 1 280636 914914893853199695872 872530835965347 562949953421312 500000000070159 140318000000000000000 qz86 (ep989 rfl) rfl rfl

noncomputable abbrev qz203 := (@HAdd.hAdd Complex Complex Complex qz273 qz460 qz376)

noncomputable abbrev qz476 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz187)

noncomputable def ep991 := @ep969 36862954735419037 9007199254740992 250000000771749 140318000000000000000 Bool.false 872530835965347 562949953421312 500000000070159 140318000000000000000 Bool.false ep970 36862014137581213 4503599627370496 250000000771749 70159000000000000000 Bool.false ep971 877230335493539 281474976710656 500000000070159 70159000000000000000 (ep972 (BSN.log_sum_c_succ qz155 0 1 rfl) (ep982 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep983 (@congrArg Complex Complex qz203 qz476 Complex.log (BSN.w_shift_mk qz155 Bool.false 119766 1000 1 qz156 rfl)) (@Enclosure.Complex.IsNear.of_parts qz475 Bool.false 36862954735419037 9007199254740992 250000000771749 140318000000000000000 Bool.false 872530835965347 562949953421312 500000000070159 140318000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz475) (@HMul.hMul Real Real Real qz0 qz84 (Real.log (Enclosure.sfrac Bool.false 57400579024 16000000))) Bool.false 36862954735419037 9007199254740992 250000000771749 140318000000000000000 (Enclosure.clog_re_eq 5000 239532 4000 57400579024 16000000 rfl rfl rfl) (ep988 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz475) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz473 qz386)) Bool.false 872530835965347 562949953421312 500000000070159 140318000000000000000 (Enclosure.clog_im_eq 5000 239532 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz473 qz386)) (@HSub.hSub Real Real Real qz356 qz85 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz386 qz473))) Bool.false 872530835965347 562949953421312 500000000070159 140318000000000000000 (BSN.arctan_recip 239532 5000 rfl rfl) ep990)))) rfl rfl

noncomputable def ep992 := @ep891 ep882 Bool.false 36862014137581213 4503599627370496 250000000771749 70159000000000000000 Bool.false 877230335493539 281474976710656 500000000070159 70159000000000000000 Bool.true ep892 424095897480856522673 4503599627370496000 ep887 ep320 Bool.false ep893 1664433300773256711231 9007199254740992000 ep884 ep882 (@ep894 4503599627370496000 118660504251169716511701 ep889 Bool.false 1692504671509049959231 9007199254740992000 ep890 ep882 (BSN.logGammaStirling_unfold 1 qz179) (ep966 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep967 500000000070159 70159000000000000000 (BSN.log_sum_c_eq qz155 2) (ep968 (BSN.log_sum_c_succ qz155 1 2 rfl) (ep991 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz204 := (@HDiv.hDiv Real Real Real qz270 qz436 (2 : Real))

noncomputable def ep993 := @Enclosure.Real.IsNear.mulLit_ff qz204 (Real.log Real.pi) 119766 2000 0 1 75021 65536 1 262144 4492482543 65536000 59883 262144000 (@Enclosure.Real.IsNear.of_eq qz204 (Enclosure.sfrac Bool.false 119766 2000) Bool.false 119766 2000 0 1 (BSN.t_half_eq qz155 Bool.false 119766 1000 qz156) (Enclosure.Real.IsNear.const Bool.false 119766 2000)) EMRow38.d5 rfl

noncomputable def ep994 := @ep885 59883 262144000 ep886 209398240314421494387 1801439850948198400 ep881 ep882 (@ep888 ep884 ep882 (ep992 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep993 rfl rfl

noncomputable def ep995 := BSN.cos_dyadic_bound_f 955682 2147483648 1 0 1048576 280911 0 1 1 0 1 1 1048575 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 955682) qz292 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 955682) qz293 0 0 rfl) rfl rfl

noncomputable def ep996 := @ep880 1048576 Bool.true 1048575 1048576 1 140318 (@ep883 121885817 1048576 367 1048576 ep994 rfl) (Enclosure.sfrac_false_div 121885817 1048576) (BSN.cos_reduce2 qz461 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 67250166285681557504) qz33) 226375608064910080 72057594037927936 Bool.false 1048575 1048576 18 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q2 121885817 1048576 226375608064910080 72057594037927936 18 67250166285681557504 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1048575 1048576 67250166285681557504 151115727451828646838272 955682 2147483648 280911 280636 (ep995 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep997 := nat_lit 36950583455257944627770249

noncomputable def ep998 := nat_lit 567775942190068836335616000

noncomputable def ep999 := nat_lit 253921305497675816135399045791

noncomputable def ep1000 := nat_lit 39834592328113039488470482944000

noncomputable abbrev qz477 := (@HPow.hPow Complex Complex Complex qz531 qz560 qz569)

noncomputable abbrev qz205 := qz477

noncomputable abbrev qz206 := (@HAdd.hAdd Complex Complex Complex qz273 (@HDiv.hDiv Complex Complex Complex qz361 qz389 (@HSub.hSub Complex Complex Complex qz353 qz429 (1 : Complex))) qz360)

noncomputable def ep1001 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz152 1 24) (@HAdd.hAdd Complex Complex Complex qz4 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 24, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz153) (@HMul.hMul Complex Complex Complex qz62 qz205 (@HAdd.hAdd Complex Complex Complex qz4 qz206 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))))) Bool.false ep875 ep876 ep877

noncomputable def ep1002 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 24, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz153) (@HMul.hMul Complex Complex Complex qz62 qz205 (@HAdd.hAdd Complex Complex Complex qz4 qz206 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))))) Bool.false 3172089839603 1099511627776 482048271379935 77140636293136384

noncomputable def ep1003 := nat_lit 6297411416850580623932503

noncomputable def ep1004 := nat_lit 167983688494621033516271813

noncomputable def ep1005 := nat_lit 5285687194344108743258249

noncomputable def ep1006 := nat_lit 5035045942252994444631365791

noncomputable def ep1007 := nat_lit 173179552661497217181946549495736041472

noncomputable def ep1008 := nat_lit 20313798081081798581817870445667418112

noncomputable def ep1009 := @ep1002 Bool.false 30659912691 549755813888 120493541571745 19285159073284096 Bool.true ep1003 ep876 ep1004 ep878 Bool.false ep1005 ep998 ep1006 ep1000 Bool.false ep1007 ep875 ep876 ep877 ep878 Bool.false ep1008 ep997 ep998

noncomputable def ep1010 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 24, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz153) (BSN.headSumC qz152 24) Bool.false 3172089839603 1099511627776 482048271379935 77140636293136384 Bool.false 30659912691 549755813888 120493541571745

noncomputable abbrev qz478 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 23) qz153)

noncomputable def ep1011 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz152 24) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz152 23) qz478) Bool.false 3172089839603 1099511627776 482048271379935 77140636293136384 Bool.false 30659912691 549755813888 120493541571745 19285159073284096

noncomputable def ep1012 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz152 23) qz478 Bool.false 3148050041753 1099511627776 468181424393597 77140636293136384 Bool.true 166680001803 1099511627776 468041871828287 77140636293136384 Bool.false

noncomputable def ep1013 := nat_lit 1743874831496802639806464

noncomputable abbrev qz479 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 22) qz153)

noncomputable def ep1014 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz152 23) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz152 22) qz479) Bool.false 3148050041753 1099511627776 468181424393597 77140636293136384 Bool.true 166680001803 1099511627776 468041871828287 77140636293136384

noncomputable def ep1015 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz152 22) qz479 Bool.false 2943036647789 1099511627776 453946469438713 77140636293136384 Bool.true 140174338119 549755813888 226917791815163 38570318146568192 Bool.false

noncomputable abbrev qz480 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 21) qz153)

noncomputable def ep1016 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz152 22) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz152 21) qz480) Bool.false 2943036647789 1099511627776 453946469438713 77140636293136384 Bool.true 140174338119 549755813888 226917791815163 38570318146568192

noncomputable def ep1017 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz152 21) qz480 Bool.false 2708146962159 1099511627776 439298271507943 77140636293136384 Bool.true 115707058197 549755813888 219650709455421 38570318146568192 Bool.false

noncomputable def ep1018 := nat_lit 1617951507607452890693632

noncomputable abbrev qz481 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 20) qz153)

noncomputable def ep1019 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz152 21) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz152 20) qz481) Bool.false 2708146962159 1099511627776 439298271507943 77140636293136384 Bool.true 115707058197 549755813888 219650709455421 38570318146568192

noncomputable def ep1020 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz152 20) qz481 Bool.false 627927736045 274877906944 212188600593867 38570318146568192 Bool.true 83565702471 1099511627776 424394887219249 77140636293136384 Bool.false

noncomputable abbrev qz482 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 19) qz153)

noncomputable def ep1021 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz152 20) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz152 19) qz482) Bool.false 627927736045 274877906944 212188600593867 38570318146568192 Bool.true 83565702471 1099511627776 424394887219249 77140636293136384

noncomputable def ep1022 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz152 19) qz482 Bool.false 2333328988351 1099511627776 409076859053185 77140636293136384 Bool.false 94779447831 1099511627776 409094555819027 77140636293136384 Bool.false

noncomputable def ep1023 := nat_lit 2761655388738145673543680

noncomputable abbrev qz483 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 18) qz153)

noncomputable def ep1024 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz152 19) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz152 18) qz483) Bool.false 2333328988351 1099511627776 409076859053185 77140636293136384 Bool.false 94779447831 1099511627776 409094555819027 77140636293136384

noncomputable def ep1025 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz152 18) qz483 Bool.false 1059210777481 549755813888 98337422634045 19285159073284096 Bool.false 119806573397 549755813888 12293352475083 2410644884160512 Bool.false

noncomputable def ep1026 := nat_lit 1282761177059367676018688

noncomputable abbrev qz484 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 17) qz153)

noncomputable def ep1027 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz152 18) (@HAdd.hAdd Complex Complex Complex qz4 qz164 qz484) Bool.false 1059210777481 549755813888 98337422634045 19285159073284096 Bool.false 119806573397 549755813888 12293352475083 2410644884160512

noncomputable def ep1028 := @Enclosure.Complex.IsNear.addLitP qz164 qz484 Bool.false 1851874704749 1099511627776 377155765664893 77140636293136384 Bool.false 247731199751 1099511627776 377264647662081 77140636293136384 Bool.false

noncomputable def ep1029 := nat_lit 2329229132212033669824512

noncomputable abbrev qz207 := (@HMul.hMul Real Real Real qz267 qz436 qz561)

noncomputable def ep1030 := @Enclosure.Complex.IsNear.of_eq qz484 (Complex.mk (@HMul.hMul Real Real Real qz0 qz123 (Real.cos qz207)) (@HMul.hMul Real Real Real qz0 qz123 (@Neg.neg Real Real.instNeg (Real.sin qz207)))) Bool.false 266546850213 1099511627776 16193924871287 77140636293136384 Bool.true 8118052957 1099511627776 16122631540575 77140636293136384 (BSN.cpow_neg_s_mk qz155 119766 1000 17 qz156 rfl)

noncomputable def ep1031 := @Enclosure.Real.IsNear.mulLit_ff qz155 qz561 119766 1000 0 1 3189913004350711 1125899906842624 125000000070159 17539750000000000000 191021560439533626813 562949953421312000 7485375004201331397 8769875000000000000000 qz157 (BSN.isNear_log_sfrac 17 1 3189913004350711 1125899906842624 125000000070159 17539750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz392) Bool.false 53517859495200818200576 18889465931478580854784 1000000000561272 140318000000000000000 3189913004350711 1125899906842624 125000000070159 17539750000000000000 (BSN.log_rat_reduce_isNear 17 1 4 34 32 31784 524288 24973259072661432 36028797018963968 140318 1000000000000000 rfl rfl rfl rfl (ep473 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1032 := BSN.cos_dyadic_bound_f 65386291 2147483648 1 0 1048576 280911 0 1 1 0 1 1 1048089 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 65386291) qz292 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 65386291) qz293 0 0 rfl) rfl rfl

noncomputable abbrev qz485 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 177902691) qz27)

noncomputable def ep1033 := @Enclosure.Real.IsNear.cos_image qz207 qz485 Bool.false 177902691 524288 7 8192 Bool.false 1048089 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz207 Bool.false 191021560439533626813 562949953421312000 7485375004201331397 8769875000000000000000 177902691 524288 7 8192 (ep1031 rfl) rfl) (Enclosure.sfrac_false_div 177902691 524288) (BSN.cos_reduce0 qz485 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2300575620587335974912) qz29) 226375608064910080 72057594037927936 Bool.false 1048089 1048576 54 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q0 177902691 524288 226375608064910080 72057594037927936 54 2300575620587335974912 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1048089 1048576 2300575620587335974912 75557863725914323419136 65386291 2147483648 280911 280636 (ep1032 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1034 := BSN.sin_dyadic_bound_f 65386291 2147483648 1 0 1048576 280911 0 1 1 0 1 1 31921 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 65386291) qz287 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 65386291) qz288 0 0 rfl) rfl rfl

noncomputable def ep1035 := @Enclosure.Real.IsNear.sin_image qz207 qz485 Bool.false 177902691 524288 7 8192 Bool.false 31921 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz207 Bool.false 191021560439533626813 562949953421312000 7485375004201331397 8769875000000000000000 177902691 524288 7 8192 (ep1031 rfl) rfl) (Enclosure.sfrac_false_div 177902691 524288) (BSN.sin_reduce0 qz485 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2300575620587335974912) qz29) 226375608064910080 72057594037927936 Bool.false 31921 1048576 54 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q0 177902691 524288 226375608064910080 72057594037927936 54 2300575620587335974912 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 31921 1048576 2300575620587335974912 75557863725914323419136 65386291 2147483648 280911 280636 (ep1034 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1036 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz123 (Real.cos qz207)) (@HMul.hMul Real Real Real qz0 qz123 (@Neg.neg Real Real.instNeg (Real.sin qz207))) Bool.false 266546850213 1099511627776 16193924871287 77140636293136384 Bool.true 8118052957 1099511627776 16122631540575 77140636293136384 (@Enclosure.Real.IsNear.mulLit_ff qz123 (Real.cos qz207) 254317 1048576 1 1048576 1048089 1048576 495209 574742528 266546850213 1099511627776 16193924871287 77140636293136384 qz394 (@Enclosure.Real.IsNear.recentre' (Real.cos qz207) Bool.false 1048089 1048576 990418 1149485056 1048089 1048576 495209 574742528 (ep1033 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz123 (@Neg.neg Real Real.instNeg (Real.sin qz207)) 254317 1048576 1 1048576 31921 1048576 495209 574742528 8118052957 1099511627776 16122631540575 77140636293136384 qz394 (@Enclosure.Real.IsNear.neg (Real.sin qz207) Bool.false 31921 1048576 495209 574742528 (@Enclosure.Real.IsNear.recentre' (Real.sin qz207) Bool.false 31921 1048576 990418 1149485056 31921 1048576 495209 574742528 (ep1035 rfl rfl) rfl)) rfl)

noncomputable def ep1037 := @ep1028 266546850213 1099511627776 16193924871287 77140636293136384 Bool.true 8118052957 1099511627776 16122631540575 77140636293136384 Bool.false ep1029 1059210777481 549755813888 98337422634045 19285159073284096 Bool.false 263457441068000575750144 119806573397 549755813888 12293352475083 2410644884160512 EMRow38.d12 (ep1030 ep1036) rfl rfl

noncomputable abbrev qz208 := (@HMul.hMul Real Real Real qz267 qz436 qz562)

noncomputable def ep1038 := @Enclosure.Complex.IsNear.of_eq qz483 (Complex.mk (@HMul.hMul Real Real Real qz0 qz125 (Real.cos qz208)) (@HMul.hMul Real Real Real qz0 qz125 (@Neg.neg Real Real.instNeg (Real.sin qz208)))) Bool.false 214907433389 1099511627776 15727168517005 77140636293136384 Bool.true 144833698963 1099511627776 15707276616371 77140636293136384 (BSN.cpow_neg_s_mk qz155 119766 1000 18 qz156 rfl)

noncomputable def ep1039 := @Enclosure.Real.IsNear.mulLit_ff qz155 qz562 119766 1000 0 1 3254268794313975 1125899906842624 125000000070159 17539750000000000000 7795015128396150597 22517998136852480 7485375004201331397 8769875000000000000000 qz157 (BSN.isNear_log_sfrac 18 1 3254268794313975 1125899906842624 125000000070159 17539750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz396) Bool.false 54597570484265130393600 18889465931478580854784 1000000000561272 140318000000000000000 3254268794313975 1125899906842624 125000000070159 17539750000000000000 (BSN.log_rat_reduce_isNear 18 1 4 36 32 61752 524288 24973259072661432 36028797018963968 140318 1000000000000000 rfl rfl rfl rfl (ep484 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1040 := nat_lit 2630215663676502021182269217876476081

noncomputable def ep1041 := BSN.cos_dyadic_bound_f 1273496747 2147483648 2 1 1048576 280911 ep1040 ep77 ep1040 ep1040 ep78 ep1040 869539 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1273496747) qz292 0 1 ep1040 ep77 ep1040 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1273496747) qz293 0 1 ep1040 ep78 ep1040 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz486 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 362983677) qz32)

noncomputable def ep1042 := @Enclosure.Real.IsNear.cos_image qz208 qz486 Bool.false 362983677 1048576 7 8192 Bool.false 869539 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz208 Bool.false 7795015128396150597 22517998136852480 7485375004201331397 8769875000000000000000 362983677 1048576 7 8192 (ep1039 rfl) rfl) (Enclosure.sfrac_false_div 362983677 1048576) (BSN.cos_reduce0 qz486 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 89614366821065890463744) qz33) 226375608064910080 72057594037927936 Bool.false 869539 1048576 55 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q0 362983677 1048576 226375608064910080 72057594037927936 55 89614366821065890463744 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 869539 1048576 89614366821065890463744 151115727451828646838272 1273496747 2147483648 280911 280636 (ep1041 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1043 := BSN.sin_dyadic_bound_f 1273496747 2147483648 2 1 1048576 280911 ep1040 ep81 ep1040 ep1040 ep82 ep1040 586013 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1273496747) qz287 0 1 ep1040 ep81 ep1040 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1273496747) qz288 0 1 ep1040 ep82 ep1040 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1044 := @Enclosure.Real.IsNear.sin_image qz208 qz486 Bool.false 362983677 1048576 7 8192 Bool.false 586013 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz208 Bool.false 7795015128396150597 22517998136852480 7485375004201331397 8769875000000000000000 362983677 1048576 7 8192 (ep1039 rfl) rfl) (Enclosure.sfrac_false_div 362983677 1048576) (BSN.sin_reduce0 qz486 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 89614366821065890463744) qz33) 226375608064910080 72057594037927936 Bool.false 586013 1048576 55 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q0 362983677 1048576 226375608064910080 72057594037927936 55 89614366821065890463744 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 586013 1048576 89614366821065890463744 151115727451828646838272 1273496747 2147483648 280911 280636 (ep1043 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1045 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz125 (Real.cos qz208)) (@HMul.hMul Real Real Real qz0 qz125 (@Neg.neg Real Real.instNeg (Real.sin qz208))) Bool.false 214907433389 1099511627776 15727168517005 77140636293136384 Bool.true 144833698963 1099511627776 15707276616371 77140636293136384 (@Enclosure.Real.IsNear.mulLit_ff qz125 (Real.cos qz208) 247151 1048576 1 1048576 869539 1048576 495209 574742528 214907433389 1099511627776 15727168517005 77140636293136384 qz398 (@Enclosure.Real.IsNear.recentre' (Real.cos qz208) Bool.false 869539 1048576 990418 1149485056 869539 1048576 495209 574742528 (ep1042 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz125 (@Neg.neg Real Real.instNeg (Real.sin qz208)) 247151 1048576 1 1048576 586013 1048576 495209 574742528 144833698963 1099511627776 15707276616371 77140636293136384 qz398 (@Enclosure.Real.IsNear.neg (Real.sin qz208) Bool.false 586013 1048576 495209 574742528 (@Enclosure.Real.IsNear.recentre' (Real.sin qz208) Bool.false 586013 1048576 990418 1149485056 586013 1048576 495209 574742528 (ep1044 rfl rfl) rfl)) rfl)

noncomputable def ep1046 := @ep1025 214907433389 1099511627776 15727168517005 77140636293136384 Bool.true 144833698963 1099511627776 15707276616371 77140636293136384 Bool.false ep1026 2333328988351 1099511627776 409076859053185 77140636293136384 Bool.false 52105552482186641276928 94779447831 1099511627776 409094555819027 77140636293136384 (ep1027 (BSN.head_sum_c_succ qz152 17 18 rfl rfl) (ep1037 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1038 ep1045) rfl rfl

noncomputable abbrev qz209 := (@HMul.hMul Real Real Real qz267 qz436 qz563)

noncomputable def ep1047 := @Enclosure.Complex.IsNear.of_eq qz482 (Complex.mk (@HMul.hMul Real Real Real qz0 qz127 (Real.cos qz209)) (@HMul.hMul Real Real Real qz0 qz127 (@Neg.neg Real Real.instNeg (Real.sin qz209)))) Bool.false 178381955829 1099511627776 15300342134549 77140636293136384 Bool.true 89172575151 549755813888 7650165700111 38570318146568192 (BSN.cpow_neg_s_mk qz155 119766 1000 19 qz156 rfl)

noncomputable def ep1048 := @Enclosure.Real.IsNear.mulLit_ff qz155 qz563 119766 1000 0 1 3315143513283831 1125899906842624 125000000070159 17539750000000000000 198520739005975651773 562949953421312000 7485375004201331397 8769875000000000000000 qz157 (BSN.isNear_log_sfrac 19 1 3315143513283831 1125899906842624 125000000070159 17539750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz400) Bool.false 55618878793361701994496 18889465931478580854784 1000000000561272 140318000000000000000 3315143513283831 1125899906842624 125000000070159 17539750000000000000 (BSN.log_rat_reduce_isNear 19 1 4 38 32 90099 524288 24973259072661432 36028797018963968 140318 1000000000000000 rfl rfl rfl rfl (ep498 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1049 := nat_lit 289052922803984641674812941190621395515188316903635885852086635480671865569536

noncomputable def ep1050 := nat_lit 65418508876246946984543686722189837800525990414239400657873113556648755456

noncomputable def ep1051 := nat_lit 867027931394201431130469736198419806869963898730079178754944160214902299197696

noncomputable def ep1052 := BSN.cos_dyadic_bound_f 1686407714 2147483648 3 2 1048576 280911 ep1049 ep66 ep1050 ep1051 ep68 ep1050 741531 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1686407714) qz292 0 2 ep1049 ep66 ep1050 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1686407714) qz293 0 2 ep1051 ep68 ep1050 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz487 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 369773691) qz32)

noncomputable def ep1053 := @Enclosure.Real.IsNear.cos_image qz209 qz487 Bool.false 369773691 1048576 7 8192 Bool.false 741531 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz209 Bool.false 198520739005975651773 562949953421312000 7485375004201331397 8769875000000000000000 369773691 1048576 7 8192 (ep1048 rfl) rfl) (Enclosure.sfrac_false_div 369773691 1048576) (BSN.cos_reduce0 qz487 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 118670393059675715141632) qz33) 226375608064910080 72057594037927936 Bool.false 741531 1048576 56 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q0 369773691 1048576 226375608064910080 72057594037927936 56 118670393059675715141632 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 741531 1048576 118670393059675715141632 151115727451828646838272 1686407714 2147483648 280911 280636 (ep1052 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1054 := nat_lit 8088170922788844413834792796243993616

noncomputable def ep1055 := BSN.sin_dyadic_bound_f 1686407714 2147483648 2 1 1048576 280911 ep1054 ep81 ep1054 ep1054 ep82 ep1054 741378 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1686407714) qz287 0 1 ep1054 ep81 ep1054 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1686407714) qz288 0 1 ep1054 ep82 ep1054 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1056 := @Enclosure.Real.IsNear.sin_image qz209 qz487 Bool.false 369773691 1048576 7 8192 Bool.false 741378 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz209 Bool.false 198520739005975651773 562949953421312000 7485375004201331397 8769875000000000000000 369773691 1048576 7 8192 (ep1048 rfl) rfl) (Enclosure.sfrac_false_div 369773691 1048576) (BSN.sin_reduce0 qz487 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 118670393059675715141632) qz33) 226375608064910080 72057594037927936 Bool.false 741378 1048576 56 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q0 369773691 1048576 226375608064910080 72057594037927936 56 118670393059675715141632 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 741378 1048576 118670393059675715141632 151115727451828646838272 1686407714 2147483648 280911 280636 (ep1055 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1057 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz127 (Real.cos qz209)) (@HMul.hMul Real Real Real qz0 qz127 (@Neg.neg Real Real.instNeg (Real.sin qz209))) Bool.false 178381955829 1099511627776 15300342134549 77140636293136384 Bool.true 89172575151 549755813888 7650165700111 38570318146568192 (@Enclosure.Real.IsNear.mulLit_ff qz127 (Real.cos qz209) 240559 1048576 1 1048576 741531 1048576 495209 574742528 178381955829 1099511627776 15300342134549 77140636293136384 qz402 (@Enclosure.Real.IsNear.recentre' (Real.cos qz209) Bool.false 741531 1048576 990418 1149485056 741531 1048576 495209 574742528 (ep1053 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz127 (@Neg.neg Real Real.instNeg (Real.sin qz209)) 240559 1048576 1 1048576 370689 524288 495209 574742528 89172575151 549755813888 7650165700111 38570318146568192 qz402 (@Enclosure.Real.IsNear.neg (Real.sin qz209) Bool.false 370689 524288 495209 574742528 (@Enclosure.Real.IsNear.recentre' (Real.sin qz209) Bool.false 741378 1048576 990418 1149485056 370689 524288 495209 574742528 (ep1056 rfl rfl) rfl)) rfl)

noncomputable def ep1058 := @ep1022 178381955829 1099511627776 15300342134549 77140636293136384 Bool.true 89172575151 549755813888 7650165700111 38570318146568192 Bool.false ep1023 627927736045 274877906944 212188600593867 38570318146568192 Bool.true 45940730775067057717248 83565702471 1099511627776 424394887219249 77140636293136384 (ep1024 (BSN.head_sum_c_succ qz152 18 19 rfl rfl) (ep1046 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1047 ep1057) rfl rfl

noncomputable abbrev qz210 := (@HMul.hMul Real Real Real qz267 qz436 qz564)

noncomputable def ep1059 := @Enclosure.Complex.IsNear.of_eq qz481 (Complex.mk (@HMul.hMul Real Real Real qz0 qz129 (Real.cos qz210)) (@HMul.hMul Real Real Real qz0 qz129 (@Neg.neg Real Real.instNeg (Real.sin qz210)))) Bool.false 196436017979 1099511627776 14921070320209 77140636293136384 Bool.true 147848413923 1099511627776 14906531691593 77140636293136384 (BSN.cpow_neg_s_mk qz155 119766 1000 20 qz156 rfl)

noncomputable def ep1060 := @Enclosure.Real.IsNear.mulLit_ff qz155 qz564 119766 1000 0 1 3372893643545847 1125899906842624 125000000070159 17539750000000000000 201978990056455955901 562949953421312000 7485375004201331397 8769875000000000000000 qz157 (BSN.isNear_log_sfrac 20 1 3372893643545847 1125899906842624 125000000070159 17539750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz404) Bool.false 56587765202795681021952 18889465931478580854784 1000000000561272 140318000000000000000 3372893643545847 1125899906842624 125000000070159 17539750000000000000 (BSN.log_rat_reduce_isNear 20 1 4 40 32 116991 524288 24973259072661432 36028797018963968 140318 1000000000000000 rfl rfl rfl rfl (ep512 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1061 := nat_lit 3685454296884579714557913647662410000

noncomputable def ep1062 := BSN.cos_dyadic_bound_f 1385551770 2147483648 2 1 1048576 280911 ep1061 ep77 ep1061 ep1061 ep78 ep1061 837791 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1385551770) qz292 0 1 ep1061 ep77 ep1061 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1385551770) qz293 0 1 ep1061 ep78 ep1061 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz488 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 188107593) qz27)

noncomputable def ep1063 := @Enclosure.Real.IsNear.cos_image qz210 qz488 Bool.false 188107593 524288 7 8192 Bool.false 837791 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz210 Bool.false 201978990056455955901 562949953421312000 7485375004201331397 8769875000000000000000 188107593 524288 7 8192 (ep1060 rfl) rfl) (Enclosure.sfrac_false_div 188107593 524288) (BSN.cos_reduce0 qz488 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 48749769032638163582976) qz29) 226375608064910080 72057594037927936 Bool.false 837791 1048576 57 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q0 188107593 524288 226375608064910080 72057594037927936 57 48749769032638163582976 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 837791 1048576 48749769032638163582976 75557863725914323419136 1385551770 2147483648 280911 280636 (ep1062 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1064 := BSN.sin_dyadic_bound_f 1385551770 2147483648 2 1 1048576 280911 ep1061 ep81 ep1061 ep1061 ep82 ep1061 630567 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1385551770) qz287 0 1 ep1061 ep81 ep1061 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1385551770) qz288 0 1 ep1061 ep82 ep1061 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1065 := @Enclosure.Real.IsNear.sin_image qz210 qz488 Bool.false 188107593 524288 7 8192 Bool.false 630567 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz210 Bool.false 201978990056455955901 562949953421312000 7485375004201331397 8769875000000000000000 188107593 524288 7 8192 (ep1060 rfl) rfl) (Enclosure.sfrac_false_div 188107593 524288) (BSN.sin_reduce0 qz488 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 48749769032638163582976) qz29) 226375608064910080 72057594037927936 Bool.false 630567 1048576 57 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q0 188107593 524288 226375608064910080 72057594037927936 57 48749769032638163582976 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 630567 1048576 48749769032638163582976 75557863725914323419136 1385551770 2147483648 280911 280636 (ep1064 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1066 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz129 (Real.cos qz210)) (@HMul.hMul Real Real Real qz0 qz129 (@Neg.neg Real Real.instNeg (Real.sin qz210))) Bool.false 196436017979 1099511627776 14921070320209 77140636293136384 Bool.true 147848413923 1099511627776 14906531691593 77140636293136384 (@Enclosure.Real.IsNear.mulLit_ff qz129 (Real.cos qz210) 234469 1048576 1 1048576 837791 1048576 495209 574742528 196436017979 1099511627776 14921070320209 77140636293136384 qz406 (@Enclosure.Real.IsNear.recentre' (Real.cos qz210) Bool.false 837791 1048576 990418 1149485056 837791 1048576 495209 574742528 (ep1063 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz129 (@Neg.neg Real Real.instNeg (Real.sin qz210)) 234469 1048576 1 1048576 630567 1048576 495209 574742528 147848413923 1099511627776 14906531691593 77140636293136384 qz406 (@Enclosure.Real.IsNear.neg (Real.sin qz210) Bool.false 630567 1048576 495209 574742528 (@Enclosure.Real.IsNear.recentre' (Real.sin qz210) Bool.false 630567 1048576 990418 1149485056 630567 1048576 495209 574742528 (ep1065 rfl rfl) rfl)) rfl)

noncomputable def ep1067 := @ep1020 196436017979 1099511627776 14921070320209 77140636293136384 Bool.true 147848413923 1099511627776 14906531691593 77140636293136384 Bool.false 744409768655017891332096 2708146962159 1099511627776 439298271507943 77140636293136384 Bool.true 254442511806711667359744 115707058197 549755813888 219650709455421 38570318146568192 (ep1021 (BSN.head_sum_c_succ qz152 19 20 rfl rfl) (ep1058 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1059 ep1066) rfl rfl

noncomputable abbrev qz211 := (@HMul.hMul Real Real Real qz267 qz436 qz565)

noncomputable def ep1068 := @Enclosure.Complex.IsNear.of_eq qz480 (Complex.mk (@HMul.hMul Real Real Real qz0 qz131 (Real.cos qz211)) (@HMul.hMul Real Real Real qz0 qz131 (@Neg.neg Real Real.instNeg (Real.sin qz211)))) Bool.false 117444842815 549755813888 430829350905 2268842243915776 Bool.true 12233639961 274877906944 213737716463 1134421121957888 (BSN.cpow_neg_s_mk qz155 119766 1000 21 qz156 rfl)

noncomputable def ep1069 := @Enclosure.Real.IsNear.mulLit_ff qz155 qz565 119766 1000 0 1 3427826275261687 1125899906842624 125000000070159 17539750000000000000 205268520841495602621 562949953421312000 7485375004201331397 8769875000000000000000 qz157 (BSN.isNear_log_sfrac 21 1 3427826275261687 1125899906842624 125000000070159 17539750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz408) Bool.false 57509381830540779323392 18889465931478580854784 1000000000561272 140318000000000000000 3427826275261687 1125899906842624 125000000070159 17539750000000000000 (BSN.log_rat_reduce_isNear 21 1 4 42 32 142571 524288 24973259072661432 36028797018963968 140318 1000000000000000 rfl rfl rfl rfl (ep523 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1070 := nat_lit 37849285334738490314664559674538561

noncomputable def ep1071 := BSN.cos_dyadic_bound_f 441077009 2147483648 2 1 1048576 280911 ep1070 ep77 ep1070 ep1070 ep78 ep1070 1026535 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 441077009) qz292 0 1 ep1070 ep77 ep1070 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 441077009) qz293 0 1 ep1070 ep78 ep1070 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz489 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 191171207) qz27)

noncomputable def ep1072 := @Enclosure.Real.IsNear.cos_image qz211 qz489 Bool.false 191171207 524288 7 8192 Bool.false 1026535 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz211 Bool.false 205268520841495602621 562949953421312000 7485375004201331397 8769875000000000000000 191171207 524288 7 8192 (ep1069 rfl) rfl) (Enclosure.sfrac_false_div 191171207 524288) (BSN.cos_reduce0 qz489 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 15519017629920970932224) qz29) 226375608064910080 72057594037927936 Bool.false 1026535 1048576 58 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q0 191171207 524288 226375608064910080 72057594037927936 58 15519017629920970932224 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1026535 1048576 15519017629920970932224 75557863725914323419136 441077009 2147483648 280911 280636 (ep1071 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1073 := BSN.sin_dyadic_bound_f 441077009 2147483648 2 1 1048576 280911 ep1070 ep81 ep1070 ep1070 ep82 ep1070 213858 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 441077009) qz287 0 1 ep1070 ep81 ep1070 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 441077009) qz288 0 1 ep1070 ep82 ep1070 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1074 := @Enclosure.Real.IsNear.sin_image qz211 qz489 Bool.false 191171207 524288 7 8192 Bool.false 213858 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz211 Bool.false 205268520841495602621 562949953421312000 7485375004201331397 8769875000000000000000 191171207 524288 7 8192 (ep1069 rfl) rfl) (Enclosure.sfrac_false_div 191171207 524288) (BSN.sin_reduce0 qz489 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 15519017629920970932224) qz29) 226375608064910080 72057594037927936 Bool.false 213858 1048576 58 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q0 191171207 524288 226375608064910080 72057594037927936 58 15519017629920970932224 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 213858 1048576 15519017629920970932224 75557863725914323419136 441077009 2147483648 280911 280636 (ep1073 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1075 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz131 (Real.cos qz211)) (@HMul.hMul Real Real Real qz0 qz131 (@Neg.neg Real Real.instNeg (Real.sin qz211))) Bool.false 117444842815 549755813888 430829350905 2268842243915776 Bool.true 12233639961 274877906944 213737716463 1134421121957888 (@Enclosure.Real.IsNear.mulLit_ff qz131 (Real.cos qz211) 114409 524288 1 524288 1026535 1048576 495209 574742528 117444842815 549755813888 430829350905 2268842243915776 qz410 (@Enclosure.Real.IsNear.recentre' (Real.cos qz211) Bool.false 1026535 1048576 990418 1149485056 1026535 1048576 495209 574742528 (ep1072 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz131 (@Neg.neg Real Real.instNeg (Real.sin qz211)) 114409 524288 1 524288 106929 524288 495209 574742528 12233639961 274877906944 213737716463 1134421121957888 qz410 (@Enclosure.Real.IsNear.neg (Real.sin qz211) Bool.false 106929 524288 495209 574742528 (@Enclosure.Real.IsNear.recentre' (Real.sin qz211) Bool.false 213858 1048576 990418 1149485056 106929 524288 495209 574742528 (ep1074 rfl rfl) rfl)) rfl)

noncomputable def ep1076 := @ep1017 117444842815 549755813888 430829350905 2268842243915776 Bool.true 12233639961 274877906944 213737716463 1134421121957888 Bool.false ep1018 2943036647789 1099511627776 453946469438713 77140636293136384 Bool.true 38530828669411273998336 140174338119 549755813888 226917791815163 38570318146568192 (ep1019 (BSN.head_sum_c_succ qz152 20 21 rfl rfl) (ep1067 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1068 ep1075) rfl rfl

noncomputable abbrev qz212 := (@HMul.hMul Real Real Real qz267 qz436 qz566)

noncomputable def ep1077 := @Enclosure.Complex.IsNear.of_eq qz479 (Complex.mk (@HMul.hMul Real Real Real qz0 qz133 (Real.cos qz212)) (@HMul.hMul Real Real Real qz0 qz133 (@Neg.neg Real Real.instNeg (Real.sin qz212)))) Bool.false 51253348491 274877906944 3558738738721 19285159073284096 Bool.false 113668674435 1099511627776 14206288197961 77140636293136384 (BSN.cpow_neg_s_mk qz155 119766 1000 22 qz156 rfl)

noncomputable def ep1078 := @Enclosure.Real.IsNear.mulLit_ff qz155 qz566 119766 1000 0 1 3480203401436407 1125899906842624 125000000070159 17539750000000000000 208405020288216360381 562949953421312000 7485375004201331397 8769875000000000000000 qz157 (BSN.isNear_log_sfrac 22 1 3480203401436407 1125899906842624 125000000070159 17539750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz412) Bool.false 58388124189833310502912 18889465931478580854784 1000000000561272 140318000000000000000 3480203401436407 1125899906842624 125000000070159 17539750000000000000 (BSN.log_rat_reduce_isNear 22 1 4 44 32 166961 524288 24973259072661432 36028797018963968 140318 1000000000000000 rfl rfl rfl rfl (ep538 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1079 := nat_lit 1757370161847636628097485830519487821745970596858994526527324786062772762101345

noncomputable def ep1080 := nat_lit 746028110128582017056581391972147466512710616984433893395299591658476455521

noncomputable def ep1081 := nat_lit 4601428283136935369370561757678322722960330984107963247934639192730291129337441

noncomputable def ep1082 := BSN.sin_dyadic_bound_f 2286095659 2147483648 3 2 1048576 280911 ep1079 ep59 ep1080 ep1081 ep62 ep1080 917052 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2286095659) qz287 0 2 ep1079 ep59 ep1080 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2286095659) qz288 0 2 ep1081 ep62 ep1080 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz490 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 48523075) (@Nat.cast Real Real.instNatCast 131072))

noncomputable def ep1083 := @Enclosure.Real.IsNear.cos_image qz212 qz490 Bool.false 48523075 131072 7 8192 Bool.false 917052 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz212 Bool.false 208405020288216360381 562949953421312000 7485375004201331397 8769875000000000000000 48523075 131072 7 8192 (ep1078 rfl) rfl) (Enclosure.sfrac_false_div 48523075 131072) (BSN.cos_reduce3 qz490 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 20108710077145074892800) qz291) 226375608064910080 72057594037927936 Bool.false 917052 1048576 58 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q3 48523075 131072 226375608064910080 72057594037927936 58 20108710077145074892800 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 917052 1048576 20108710077145074892800 18889465931478580854784 2286095659 2147483648 280911 280636 (ep1082 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1084 := nat_lit 976648324630966385395072830907258633177322647418101152023356125408944190703201

noncomputable def ep1085 := nat_lit 2928452917672641992151105329937831604598942521020334588283277777043515619198561

noncomputable def ep1086 := BSN.cos_dyadic_bound_f 2286095659 2147483648 3 2 1048576 280911 ep1084 ep66 ep1080 ep1085 ep68 ep1080 508455 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2286095659) qz292 0 2 ep1084 ep66 ep1080 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2286095659) qz293 0 2 ep1085 ep68 ep1080 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1087 := @Enclosure.Real.IsNear.sin_image qz212 qz490 Bool.false 48523075 131072 7 8192 Bool.true 508455 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz212 Bool.false 208405020288216360381 562949953421312000 7485375004201331397 8769875000000000000000 48523075 131072 7 8192 (ep1078 rfl) rfl) (Enclosure.sfrac_false_div 48523075 131072) (BSN.sin_reduce3 qz490 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 20108710077145074892800) qz291) 226375608064910080 72057594037927936 Bool.false 508455 1048576 58 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q3 48523075 131072 226375608064910080 72057594037927936 58 20108710077145074892800 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 508455 1048576 20108710077145074892800 18889465931478580854784 2286095659 2147483648 280911 280636 (ep1086 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1088 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz133 (Real.cos qz212)) (@HMul.hMul Real Real Real qz0 qz133 (@Neg.neg Real Real.instNeg (Real.sin qz212))) Bool.false 51253348491 274877906944 3558738738721 19285159073284096 Bool.false 113668674435 1099511627776 14206288197961 77140636293136384 (@Enclosure.Real.IsNear.mulLit_ff qz133 (Real.cos qz212) 223557 1048576 1 1048576 229263 262144 495209 574742528 51253348491 274877906944 3558738738721 19285159073284096 qz414 (@Enclosure.Real.IsNear.recentre' (Real.cos qz212) Bool.false 917052 1048576 990418 1149485056 229263 262144 495209 574742528 (ep1083 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz133 (@Neg.neg Real Real.instNeg (Real.sin qz212)) 223557 1048576 1 1048576 508455 1048576 495209 574742528 113668674435 1099511627776 14206288197961 77140636293136384 qz414 (@Enclosure.Real.IsNear.neg (Real.sin qz212) Bool.true 508455 1048576 495209 574742528 (@Enclosure.Real.IsNear.recentre' (Real.sin qz212) Bool.true 508455 1048576 990418 1149485056 508455 1048576 495209 574742528 (ep1087 rfl rfl) rfl)) rfl)

noncomputable def ep1089 := @ep1015 51253348491 274877906944 3558738738721 19285159073284096 Bool.false 113668674435 1099511627776 14206288197961 77140636293136384 Bool.false 865329406432036448632832 3148050041753 1099511627776 468181424393597 77140636293136384 Bool.true 91633300050061572440064 166680001803 1099511627776 468041871828287 77140636293136384 (ep1016 (BSN.head_sum_c_succ qz152 21 22 rfl rfl) (ep1076 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1077 ep1088) rfl rfl

noncomputable abbrev qz213 := (@HMul.hMul Real Real Real qz267 qz436 qz567)

noncomputable def ep1090 := @Enclosure.Complex.IsNear.of_eq qz478 (Complex.mk (@HMul.hMul Real Real Real qz0 qz135 (Real.cos qz213)) (@HMul.hMul Real Real Real qz0 qz135 (@Neg.neg Real Real.instNeg (Real.sin qz213)))) Bool.false 12019898925 549755813888 6933423493169 38570318146568192 Bool.false 227999827185 1099511627776 13932294458693 77140636293136384 (BSN.cpow_neg_s_mk qz155 119766 1000 23 qz156 rfl)

noncomputable def ep1091 := @Enclosure.Real.IsNear.mulLit_ff qz155 qz567 119766 1000 0 1 3530250507853047 1125899906842624 125000000070159 17539750000000000000 211401991161764013501 562949953421312000 7485375004201331397 8769875000000000000000 qz157 (BSN.isNear_log_sfrac 23 1 3530250507853047 1125899906842624 125000000070159 17539750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz416) Bool.false 59227775304360265777152 18889465931478580854784 1000000000561272 140318000000000000000 3530250507853047 1125899906842624 125000000070159 17539750000000000000 (BSN.log_rat_reduce_isNear 23 1 4 46 32 190266 524288 24973259072661432 36028797018963968 140318 1000000000000000 rfl rfl rfl rfl (ep552 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1092 := BSN.sin_dyadic_bound_f 225594018 2147483648 1 0 1048576 280911 0 1 1 0 1 1 109950 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 225594018) qz287 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 225594018) qz288 0 0 rfl) rfl rfl

noncomputable abbrev qz491 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 393766893) qz32)

noncomputable def ep1093 := @Enclosure.Real.IsNear.cos_image qz213 qz491 Bool.false 393766893 1048576 7 8192 Bool.false 109950 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz213 Bool.false 211401991161764013501 562949953421312000 7485375004201331397 8769875000000000000000 393766893 1048576 7 8192 (ep1091 rfl) rfl) (Enclosure.sfrac_false_div 393766893 1048576) (BSN.cos_reduce3 qz491 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 15874767797609694232576) qz33) 226375608064910080 72057594037927936 Bool.false 109950 1048576 59 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q3 393766893 1048576 226375608064910080 72057594037927936 59 15874767797609694232576 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 109950 1048576 15874767797609694232576 151115727451828646838272 225594018 2147483648 280911 280636 (ep1092 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1094 := nat_lit 2590062939323270697908423840936976

noncomputable def ep1095 := BSN.cos_dyadic_bound_f 225594018 2147483648 2 1 1048576 280911 ep1094 ep77 ep1094 ep1094 ep78 ep1094 1042795 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 225594018) qz292 0 1 ep1094 ep77 ep1094 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 225594018) qz293 0 1 ep1094 ep78 ep1094 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1096 := @Enclosure.Real.IsNear.sin_image qz213 qz491 Bool.false 393766893 1048576 7 8192 Bool.true 1042795 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz213 Bool.false 211401991161764013501 562949953421312000 7485375004201331397 8769875000000000000000 393766893 1048576 7 8192 (ep1091 rfl) rfl) (Enclosure.sfrac_false_div 393766893 1048576) (BSN.sin_reduce3 qz491 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 15874767797609694232576) qz33) 226375608064910080 72057594037927936 Bool.false 1042795 1048576 59 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q3 393766893 1048576 226375608064910080 72057594037927936 59 15874767797609694232576 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1042795 1048576 15874767797609694232576 151115727451828646838272 225594018 2147483648 280911 280636 (ep1095 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1097 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz135 (Real.cos qz213)) (@HMul.hMul Real Real Real qz0 qz135 (@Neg.neg Real Real.instNeg (Real.sin qz213))) Bool.false 12019898925 549755813888 6933423493169 38570318146568192 Bool.false 227999827185 1099511627776 13932294458693 77140636293136384 (@Enclosure.Real.IsNear.mulLit_ff qz135 (Real.cos qz213) 218643 1048576 1 1048576 54975 524288 495209 574742528 12019898925 549755813888 6933423493169 38570318146568192 qz418 (@Enclosure.Real.IsNear.recentre' (Real.cos qz213) Bool.false 109950 1048576 990418 1149485056 54975 524288 495209 574742528 (ep1093 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz135 (@Neg.neg Real Real.instNeg (Real.sin qz213)) 218643 1048576 1 1048576 1042795 1048576 495209 574742528 227999827185 1099511627776 13932294458693 77140636293136384 qz418 (@Enclosure.Real.IsNear.neg (Real.sin qz213) Bool.true 1042795 1048576 495209 574742528 (@Enclosure.Real.IsNear.recentre' (Real.sin qz213) Bool.true 1042795 1048576 990418 1149485056 1042795 1048576 495209 574742528 (ep1096 rfl rfl) rfl)) rfl)

noncomputable def ep1098 := @ep1012 12019898925 549755813888 6933423493169 38570318146568192 Bool.false 227999827185 1099511627776 13932294458693 77140636293136384 Bool.false ep1013 3172089839603 1099511627776 482048271379935 77140636293136384 Bool.false 67421861020702901010432 30659912691 549755813888 120493541571745 19285159073284096 (ep1014 (BSN.head_sum_c_succ qz152 22 23 rfl rfl) (ep1089 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1090 ep1097) rfl rfl

noncomputable def ep1099 := @Enclosure.Complex.IsNear.mul qz205 (@HAdd.hAdd Complex Complex Complex qz4 qz206 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))) Bool.true ep1003 ep876 ep1004 ep878 Bool.false

noncomputable def ep1100 := nat_lit 2271103768760275345342464

noncomputable def ep1101 := nat_lit 1567153726967212373589517

noncomputable abbrev qz214 := (Complex.re qz477)

noncomputable abbrev qz215 := (Complex.im qz477)

noncomputable def ep1102 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 qz214 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz206 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz215 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz206 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))))) 204889452172735826080333 ep1100 ep1101

noncomputable def ep1103 := nat_lit 17704263256939128661542436864

noncomputable def ep1104 := nat_lit 9462932369834480605593600

noncomputable def ep1105 := nat_lit 17943510057708576346157875200

noncomputable def ep1106 := nat_lit 2383679133707223164618424873623703369638825951232

noncomputable def ep1107 := @Enclosure.Real.IsNear.mulLit_tf qz214 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz206 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))))) 198030381073 1099511627776 13632211995993 77140636293136384 1034636458621

noncomputable abbrev qz492 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) qz570 (Real.log (Enclosure.sfrac Bool.false 24 1)))

noncomputable abbrev qz216 := (Real.cos qz492)

noncomputable abbrev qz217 := (Real.sin qz492)

noncomputable abbrev qz493 := (@Neg.neg Real Real.instNeg qz217)

noncomputable def ep1108 := @Enclosure.Complex.IsNear.of_eq qz205 (Complex.mk (@HMul.hMul Real Real Real qz0 qz139 qz216) (@HMul.hMul Real Real Real qz0 qz139 qz493)) Bool.true 198030381073 1099511627776 13632211995993 77140636293136384 Bool.false 26404921235 274877906944 3400480264555 19285159073284096 (BSN.cpow_neg_s_mk qz155 119766 1000 24 qz156 rfl)

noncomputable def ep1109 := @Enclosure.Real.IsNear.mulLit_ff qz155 qz142 119766 1000 0 1 3578169457974519 1125899906842624 125000000070159 17539750000000000000 214271521651888121277 562949953421312000 7485375004201331397 8769875000000000000000 qz157 (BSN.isNear_log_sfrac 24 1 3578169457974519 1125899906842624 125000000070159 17539750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz424 Bool.false 60031721881041427759104 18889465931478580854784 1000000000561272 140318000000000000000 3578169457974519 1125899906842624 125000000070159 17539750000000000000 (BSN.log_rat_reduce_isNear 24 1 4 48 32 212580 524288 24973259072661432 36028797018963968 140318 1000000000000000 rfl rfl rfl rfl (ep576 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1110 := nat_lit 1225752232608515945150537312578519296

noncomputable def ep1111 := BSN.cos_dyadic_bound_f 1052205756 2147483648 2 1 1048576 280911 ep1110 ep77 ep1110 ep1110 ep78 ep1110 925207 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1052205756) qz292 0 1 ep1110 ep77 ep1110 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1052205756) qz293 0 1 ep1110 ep78 ep1110 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz218 := qz492

noncomputable abbrev qz494 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 199555905) qz27)

noncomputable def ep1112 := @Enclosure.Real.IsNear.cos_image qz218 qz494 Bool.false 199555905 524288 7 8192 Bool.true 925207 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 214271521651888121277 562949953421312000 7485375004201331397 8769875000000000000000 199555905 524288 7 8192 (ep1109 rfl) rfl) (Enclosure.sfrac_false_div 199555905 524288) (BSN.cos_reduce2 qz494 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 37021198847817788948480) qz29) 226375608064910080 72057594037927936 Bool.false 925207 1048576 60 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q2 199555905 524288 226375608064910080 72057594037927936 60 37021198847817788948480 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 925207 1048576 37021198847817788948480 75557863725914323419136 1052205756 2147483648 280911 280636 (ep1111 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1113 := BSN.sin_dyadic_bound_f 1052205756 2147483648 2 1 1048576 280911 ep1110 ep81 ep1110 ep1110 ep82 ep1110 493460 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1052205756) qz287 0 1 ep1110 ep81 ep1110 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1052205756) qz288 0 1 ep1110 ep82 ep1110 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1114 := @Enclosure.Real.IsNear.sin_image qz218 qz494 Bool.false 199555905 524288 7 8192 Bool.true 493460 1048576 1 140318 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 214271521651888121277 562949953421312000 7485375004201331397 8769875000000000000000 199555905 524288 7 8192 (ep1109 rfl) rfl) (Enclosure.sfrac_false_div 199555905 524288) (BSN.sin_reduce2 qz494 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 37021198847817788948480) qz29) 226375608064910080 72057594037927936 Bool.false 493460 1048576 60 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q2 199555905 524288 226375608064910080 72057594037927936 60 37021198847817788948480 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 493460 1048576 37021198847817788948480 75557863725914323419136 1052205756 2147483648 280911 280636 (ep1113 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1115 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz139 qz216) (@HMul.hMul Real Real Real qz0 qz139 qz493) Bool.true 198030381073 1099511627776 13632211995993 77140636293136384 Bool.false 26404921235 274877906944 3400480264555 19285159073284096 (@Enclosure.Real.IsNear.mulLit_ft qz139 qz216 214039 1048576 1 1048576 925207 1048576 495209 574742528 198030381073 1099511627776 13632211995993 77140636293136384 qz426 (@Enclosure.Real.IsNear.recentre' qz216 Bool.true 925207 1048576 990418 1149485056 925207 1048576 495209 574742528 (ep1112 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz139 qz493 214039 1048576 1 1048576 123365 262144 495209 574742528 26404921235 274877906944 3400480264555 19285159073284096 qz426 (@Enclosure.Real.IsNear.neg qz217 Bool.true 123365 262144 495209 574742528 (@Enclosure.Real.IsNear.recentre' qz217 Bool.true 493460 1048576 990418 1149485056 123365 262144 495209 574742528 (ep1114 rfl rfl) rfl)) rfl)

noncomputable def ep1116 := @ep1107 2065556844864 0 1 204889452172735826080333 ep1100 ep1101 ep1103 (@Enclosure.Complex.IsNear.re_isNear qz205 Bool.true 198030381073 1099511627776 13632211995993 77140636293136384 Bool.false 26404921235 274877906944 3400480264555 19285159073284096 (ep1108 ep1115))

noncomputable def ep1117 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz206 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))) Bool.false 1034636458621 2065556844864 0 1 Bool.false

noncomputable def ep1118 := @Enclosure.Complex.IsNear.addLitP qz206 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) Bool.false 3580036189 7172072378 0 1 Bool.true 718596000

noncomputable def ep1119 := @ep1118 3586036189 0 1 Bool.false 1 576 0 1 Bool.false 19961 48000 0 1 Bool.false 2069272917242 1034636458621 2065556844864 0 1 Bool.false 37088260368629 37088260368629 172129737072000 0 1

noncomputable abbrev qz219 := (@HDiv.hDiv Complex Complex Complex qz361 qz389 (@HSub.hSub Complex Complex Complex qz353 qz429 (1 : Complex)))

noncomputable def ep1120 := @Enclosure.Complex.IsNear.addLitP qz219 qz89 Bool.true 48000000 57376579024 0 1 Bool.true 11497536000 57376579024 0 1

noncomputable def ep1121 := @Enclosure.Complex.IsNear.of_eq qz219 (Complex.mk (Enclosure.sfrac Bool.true 48000000 57376579024) (Enclosure.sfrac Bool.true 11497536000 57376579024)) Bool.true 48000000 57376579024 0 1 Bool.true 11497536000 57376579024 0 1

noncomputable def ep1122 := @ep1120 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 57280579024 3580036189 7172072378 0 1 Bool.true 11497536000 718596000 3586036189 0 1 (ep1121 (BSN.N_div_s_sub_one_mk qz155 119766 1000 24 qz156 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 48000000 57376579024) (Enclosure.sfrac Bool.true 11497536000 57376579024) Bool.true 48000000 57376579024 0 1 Bool.true 11497536000 57376579024 0 1 (Enclosure.Real.IsNear.const Bool.true 48000000 57376579024) (Enclosure.Real.IsNear.const Bool.true 11497536000 57376579024))) qz90 rfl

noncomputable def ep1123 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1))) qz146)) Bool.false 1 576 0 1

noncomputable def ep1124 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1))) qz146) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1125 := @ep1124 0 1 0 1 Bool.false 1 576 0 1 Bool.false 19961 48000 0 1 Bool.false 1 1 576 0 1 Bool.false 19961 19961 48000 0

noncomputable def ep1126 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1127 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1))) qz146 Bool.false 1 576 0 1 Bool.false 19961 48000 0 1

noncomputable def ep1128 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1)))) qz147) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1)))) qz148) 1 576 0 1 0 1 0

noncomputable def ep1129 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1)))) qz147 1 24 0 1 1 24 0 1 1

noncomputable def ep1130 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep1131 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep1132 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1)) qz152 Bool.false 1 2 0 1 Bool.false 119766 1000 0 1 (BSN.ascPochhammer_one_eval qz152)

noncomputable def ep1133 := ep1132 (@Enclosure.Complex.IsNear.of_eq qz152 (Complex.mk qz84 qz155) Bool.false 1 2 0 1 Bool.false 119766 1000 0 1 (BSN.s_crit_mk qz155 Bool.false 119766 1000 qz156) (@Enclosure.Complex.IsNear.mk qz84 qz155 Bool.false 1 2 0 1 Bool.false 119766 1000 0 1 qz370 qz157))

noncomputable def ep1134 := @ep1131 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep604) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 119766 1000 0 1 ep1133)

noncomputable def ep1135 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 119766 1000 0 1 0 1 0

noncomputable def ep1136 := @ep1135 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep604) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 119766 1000 0 1 ep1133)

noncomputable def ep1137 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1)))) 19961 2000 0 1 0 1 0 1 19961

noncomputable def ep1138 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 119766 1000 0 1 19961 2000 0

noncomputable def ep1139 := @ep1138 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep604) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 119766 1000 0 1 ep1133)

noncomputable def ep1140 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep1141 := @ep1140 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep604) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 119766 1000 0 1 ep1133)

noncomputable def ep1142 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 19961 2000 0 1 (@ep1130 1 24 0 1 (ep1134 rfl) (ep1136 rfl) rfl rfl) (@ep1137 19961 2000 0 1 (ep1139 rfl) (ep1141 rfl) rfl rfl)

noncomputable def ep1143 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 19961 2000 0 1 ep1142

noncomputable def ep1144 := @ep1129 576 0 1 ep1143 qz149

noncomputable def ep1145 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1)))) qz148 19961 2000 0 1 0 1 0 1 0

noncomputable def ep1146 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 19961 2000 0 1 ep1142

noncomputable def ep1147 := @ep1145 1 0 1 ep1146 qz150

noncomputable def ep1148 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1)))) qz148) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1)))) qz147) 0 1 0 1 19961 48000 0

noncomputable def ep1149 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1)))) qz148 1 24 0 1 0 1 0 1 0

noncomputable def ep1150 := @ep1149 1 0 1 ep1143 qz150

noncomputable def ep1151 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1)))) qz147 19961 2000 0 1 1 24 0 1 19961

noncomputable def ep1152 := @ep1151 48000 0 1 ep1146 qz149

noncomputable def ep1153 := @ep1125 1 (@ep1126 0 1 0 1 (BSN.bern_sum_base qz152 24) qz105) (ep1127 (@ep1128 1 1 1 576 0 1 (ep1144 rfl) (ep1147 rfl) rfl rfl) (@ep1148 1 19961 19961 48000 0 1 (ep1150 rfl) (ep1152 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep1154 := ep1119 (ep1122 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep1123 Bool.false 19961 48000 0 1 (BSN.bern_sum_succ qz152 24 0 1 1 rfl rfl) (ep1153 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep1155 := @Enclosure.Real.IsNear.mulLit_ff qz215 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz206 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))))) 26404921235 274877906944 3400480264555 19285159073284096 37088260368629

noncomputable def ep1156 := @ep1155 172129737072000 0 1 195862518755364161987363 ep1104 681718364487568993203487 ep1105 (@Enclosure.Complex.IsNear.im_isNear qz205 Bool.true 198030381073 1099511627776 13632211995993 77140636293136384 Bool.false 26404921235 274877906944 3400480264555 19285159073284096 (ep1108 ep1115))

noncomputable def ep1157 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz206 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))) Bool.false 1034636458621 2065556844864 0 1 Bool.false

noncomputable def ep1158 := nat_lit 7344602334134244324558917

noncomputable def ep1159 := nat_lit 189258647396689612111872000

noncomputable def ep1160 := nat_lit 168531675969245339350301199

noncomputable def ep1161 := @Enclosure.Real.IsNear.addLit_tf_p (@HMul.hMul Real Real Real qz0 qz214 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz206 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz215 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz206 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))))) ep1158 ep1159 ep1160

noncomputable def ep1162 := nat_lit 4426065814234782165385609216000

noncomputable def ep1163 := nat_lit 1076610603462514580769472512

noncomputable def ep1164 := nat_lit 1000362008963569276038980066983689544935174832128

noncomputable def ep1165 := @Enclosure.Real.IsNear.mulLit_tf qz214 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz206 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))))) 198030381073 1099511627776 13632211995993 77140636293136384 37088260368629

noncomputable def ep1166 := @ep1165 172129737072000 0 1 ep1158 ep1159 ep1160 ep1162 (@Enclosure.Complex.IsNear.re_isNear qz205 Bool.true 198030381073 1099511627776 13632211995993 77140636293136384 Bool.false 26404921235 274877906944 3400480264555 19285159073284096 (ep1108 ep1115))

noncomputable def ep1167 := @Enclosure.Real.IsNear.mulLit_ff qz215 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz206 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))))) 26404921235 274877906944 3400480264555 19285159073284096 1034636458621

noncomputable def ep1168 := @ep1167 2065556844864 0 1 27319494196746841716935 567775942190068836335616 95088131311615848391315 ep1163 (@Enclosure.Complex.IsNear.im_isNear qz205 Bool.true 198030381073 1099511627776 13632211995993 77140636293136384 Bool.false 26404921235 274877906944 3400480264555 19285159073284096 (ep1108 ep1115))

noncomputable abbrev qz495 := (ep1154 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep1169 := @ep1099 ep1005 ep998 ep1006 ep1000 (@ep1102 ep1103 195862518755364161987363 ep1104 681718364487568993203487 ep1105 ep1106 ep1003 ep876 ep1004 ep878 (ep1116 (@ep1117 37088260368629 172129737072000 0 1 qz495) rfl) (ep1156 (@ep1157 37088260368629 172129737072000 0 1 qz495) rfl) rfl rfl) (@ep1161 ep1162 27319494196746841716935 567775942190068836335616 95088131311615848391315 ep1163 ep1164 ep1005 ep998 ep1006 ep1000 (ep1166 (@ep1157 37088260368629 172129737072000 0 1 qz495) rfl) (ep1168 (@ep1117 37088260368629 172129737072000 0 1 qz495) rfl) rfl rfl)

noncomputable def ep1170 := @ep1009 ep999 ep1000 (@ep1010 19285159073284096 (BSN.head_sum_c_eq qz152 24) (ep1011 (BSN.head_sum_c_succ qz152 23 24 rfl rfl) (ep1098 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep1169 rfl rfl rfl

noncomputable def ep1171 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz152 1 24) Bool.false ep875 ep876 ep877 ep878 Bool.false ep997 ep998 ep999 ep1000 (@ep1001 ep878 Bool.false ep997 ep998 ep999 ep1000 (BSN.zetaApproximant_eq_folded' qz152 1 24 rfl) (ep1170 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep1172 := @Enclosure.Real.IsNear.mulLit_tf (Real.sin (@HSub.hSub Real Real Real qz356 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz175 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz176 (@Nat.cast Complex Complex.instNatCast j))))) qz177)) (Complex.im (zetaApproximant qz152 1 24)) 233 524288 26272641

noncomputable def ep1173 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz356 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz175 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz176 (@Nat.cast Complex Complex.instNatCast j))))) qz177)) Bool.true 466 1048576 52545282

noncomputable def ep1174 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz356 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz175 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz176 (@Nat.cast Complex Complex.instNatCast j))))) qz177) qz461 Bool.false 121885817 1048576 367

noncomputable def ep1175 := BSN.sin_dyadic_bound_f 955682 2147483648 1 0 1048576 280911 0 1 1 0 1 1 466 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 955682) qz287 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 955682) qz288 0 0 rfl) rfl rfl

noncomputable def ep1176 := @ep1174 1048576 Bool.true 466 1048576 1 140318 (@ep883 121885817 1048576 367 1048576 ep994 rfl) (Enclosure.sfrac_false_div 121885817 1048576) (BSN.sin_reduce2 qz461 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 67250166285681557504) qz33) 226375608064910080 72057594037927936 Bool.false 466 1048576 18 1000000000000000 280636 140318 (BSN.sin_reduce_arg_pos_rat_q2 121885817 1048576 226375608064910080 72057594037927936 18 67250166285681557504 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 466 1048576 67250166285681557504 151115727451828646838272 955682 2147483648 280911 280636 (ep1175 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1177 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz152 1 24) Bool.false ep875 ep876 ep877 ep878 Bool.false ep997 ep998 ep999 ep1000 (@ep1001 ep878 Bool.false ep997 ep998 ep999 ep1000 (BSN.zetaApproximant_eq_folded' qz152 1 24 rfl) (ep1170 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow38.d13 : Enclosure.Real.IsNear (hardyZApproximantEM 1 24 qz155) Bool.true ep858 ep859 ep860 ep861 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 24 qz155) ep862 Bool.true ep858 ep859 ep860 ep861 (@Eq.refl Real ep862) (@ep863 Bool.true ep858 ep859 ep860 ep861 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz356 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz175 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz176 (@Nat.cast Complex Complex.instNatCast j))))) qz177) (zetaApproximant qz152 1 24)) (@ep865 ep866 ep867 ep868 ep869 ep870 ep871 ep872 ep873 ep858 ep859 ep860 ep861 (@ep874 73567043584 ep875 ep876 ep877 ep878 ep864 ep866 ep867 ep868 (@ep879 147134087168 1048575 1048576 26272641 73567043584 (ep996 rfl rfl) rfl) ep1171 rfl) (@ep1172 73567043584 ep997 ep998 ep999 ep1000 ep869 ep870 ep871 ep872 (@ep1173 147134087168 233 524288 26272641 73567043584 (ep1176 rfl rfl) rfl) ep1177 rfl) rfl rfl))

theorem EMRow38.d14 : @Eq Nat (Nat.mul (BSN.factNat (Nat.succ (Nat.mul 2 1))) (Nat.pow 4 (Nat.mul 2 1))) 96 := @Eq.refl Nat 96

theorem EMRow38.d15 : @Eq Nat (Nat.mul (Nat.mul 2 1) (Nat.pow (Nat.succ (Nat.mul 4 2)) (Nat.mul 2 1))) 162 := @Eq.refl Nat 162

theorem EMRow38.d16 : @Eq Nat (BSN.factNat (Nat.mul 2 2)) 24 := @Eq.refl Nat 24

theorem EMRow38.d17 : @Eq Nat (Nat.pow 24 (Nat.succ (Nat.mul 2 3))) 4586471424 := @Eq.refl Nat 4586471424

noncomputable abbrev qz574 := (@HAdd.hAdd Complex Complex Complex qz579 qz578 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz496 := qz574

noncomputable abbrev qz220 := (@HDiv.hDiv Real Real Real qz270 (@Norm.norm Complex Complex.instNorm qz496) (@HAdd.hAdd Real Real Real qz380 (Complex.re qz272) qz296))

noncomputable abbrev qz221 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)

noncomputable abbrev qz222 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)))

noncomputable abbrev qz497 := (@HPow.hPow Complex Complex Complex qz531 qz560 (@HSub.hSub Complex Complex Complex qz552 qz532 qz533))

noncomputable abbrev qz223 := qz497

noncomputable def ep1178 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 24))) (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) 28825617421 618475290624 6750263 68719476736 1132505367249202145 1008806316530991104 291632333011

noncomputable def ep1179 := nat_lit 729506051074900725514857611264

noncomputable def ep1180 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 24)) 26561 1769472 1 1769472 3255783 1048576 6739 1048576 28825617421 618475290624

noncomputable abbrev qz224 := qz271

noncomputable abbrev qz575 := (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid)))

noncomputable abbrev qz498 := (@Inv.inv Real Real.instInv (@HPow.hPow Real Nat Real qz575 qz224 2))

noncomputable def ep1181 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 96 162) qz498 96 162 0 1 26561 1048576 1 1048576 26561 1769472 1 1769472

noncomputable def ep1182 := nat_lit 781950621441006189802102638025

noncomputable def ep1183 := nat_lit 19807040628566084398385987584

noncomputable def ep1184 := nat_lit 26986075409044041160201671

noncomputable def ep1185 := nat_lit 1073741824000000000000000000000000000000

noncomputable abbrev qz499 := (@HPow.hPow Real Nat Real qz575 qz224 1)

noncomputable def ep1186 := @Enclosure.Real.IsNear.mulLit_ff qz499 qz224 884279719003555 140737488355328 1 500000000000000 884279719003555 140737488355328 1 500000000000000 ep1182 ep1183 ep1184 ep1185

noncomputable def ep1187 := ep1186 (@Enclosure.Real.IsNear.of_eq qz499 qz224 Bool.false 884279719003555 140737488355328 1 500000000000000 (BSN.pow_one_r qz224) (@Enclosure.Real.IsNear.of_eq qz224 qz268 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz269)) (@Enclosure.Real.IsNear.of_eq qz224 qz268 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz269) rfl

noncomputable abbrev qz500 := (@HPow.hPow Real Nat Real qz575 qz224 2)

noncomputable def ep1188 := @Enclosure.Real.IsNear.inv_image qz500 ep1182 ep1183 ep1184 ep1185 13280 13281 524288 (@Enclosure.Real.IsNear.of_eq qz500 (@HMul.hMul Real Real Real qz0 qz499 qz224) Bool.false ep1182 ep1183 ep1184 ep1185 (BSN.pow_succ_r qz224 1 2 rfl) ep1187) rfl rfl rfl

noncomputable def ep1189 := ep1181 (Enclosure.Real.IsNear.const Bool.false 96 162) (@Enclosure.Real.IsNear.recentre' qz498 Bool.false 26561 1048576 1 1048576 26561 1048576 1 1048576 (ep1188 rfl rfl rfl) rfl)

noncomputable def ep1190 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 24)) (Real.sqrt (@HAdd.hAdd Real Real Real qz380 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 24)) (Complex.re (zetaApproximant qz5 1 24))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 24)) (Complex.im (zetaApproximant qz5 1 24))))) Bool.false 3255783 1048576 6739 1048576

noncomputable def ep1191 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz380 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 24)) (Complex.re (zetaApproximant qz5 1 24))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 24)) (Complex.im (zetaApproximant qz5 1 24))))) Bool.false 3255783 1048576 6739 1048576

noncomputable def ep1192 := nat_lit 6531258363576173736059470379369910090641921

noncomputable def ep1193 := nat_lit 677460454280262579645735353714737152000000

noncomputable def ep1194 := nat_lit 7193024830930196507918645057972931833461253586476813684909

noncomputable def ep1195 := nat_lit 180235375999421856213268913835735877894915160505581568000000

noncomputable def ep1196 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz380 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 24)) (Complex.re (zetaApproximant qz5 1 24))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 24)) (Complex.im (zetaApproximant qz5 1 24)))) ep1192 ep1193 ep1194 ep1195 1624522 1631261

noncomputable def ep1197 := nat_lit 705601616555711553579336138563832056182858931584009

noncomputable def ep1198 := nat_lit 73232397437478738532005420283049164413075456000000

noncomputable def ep1199 := nat_lit 4317413503198684659676603628574560220333339430772180179193

noncomputable def ep1200 := nat_lit 110914077538105757669703946975837463319947791080357888000000

noncomputable def ep1201 := nat_lit 1668091790523873961287891374196967724224159520641

noncomputable def ep1202 := nat_lit 292929589749914954128021681132196657652301824000000

noncomputable def ep1203 := nat_lit 1417823105858671487553313292314171803356616091776167149763

noncomputable def ep1204 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 24)) (Complex.re (zetaApproximant qz5 1 24))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 24)) (Complex.im (zetaApproximant qz5 1 24))) ep1197 ep1198 ep1199 ep1200 ep1201 ep1202 ep1203

noncomputable def ep1205 := nat_lit 1441883007995374849706151310685887023159321284044652544000000

noncomputable def ep1206 := nat_lit 206813750425507224772765763369076281811293307794747193510695183762284470886517315799182802419712000000

noncomputable def ep1207 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz5 1 24)) (Complex.re (zetaApproximant qz5 1 24)) ep307 ep308 ep309 ep310 ep307 ep308 ep309 ep310 ep1197

noncomputable def ep1208 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (zetaApproximant qz5 1 24)) (Complex.im (zetaApproximant qz5 1 24)) ep443 ep444 ep445 ep446 ep443 ep444 ep445 ep446 ep1201

noncomputable def ep1209 := @ep1178 1008806316530991104 ep1179 10615710213822614249 9079256848778919936 99385925189843 1008806316530991104 (@ep1180 6750263 68719476736 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) qz498) Bool.false 26561 1769472 1 1769472 (BSN.theta_err_eq 1 2 96 162 EMRow38.d14 EMRow38.d15 rfl) (ep1189 rfl)) (ep1190 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz5 1 24)) (@ep1191 3255783 1048576 6739 1048576 (@ep1196 524288 (@ep1204 ep1205 ep1206 ep1192 ep1193 ep1194 ep1195 (@ep1207 ep1198 ep1199 ep1200 ep643 ep643 rfl) (@ep1208 ep1202 ep1203 ep1205 ep649 ep649 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz225 := (@Norm.norm Complex Complex.instNorm qz496)

noncomputable abbrev qz576 := (Enclosure.sfrac Bool.false 2 7)

noncomputable def ep1210 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz225 qz576) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) Bool.false 1132505367249202145 1008806316530991104 291632333011 1008806316530991104 (BSN.zrb_shape_eq qz225 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) qz13 3)

noncomputable def ep1211 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz225 qz576) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) 123396485 3670016 1 3670016 9177776557 274877906944 2289 274877906944

noncomputable def ep1212 := @Enclosure.Real.IsNear.mulLit_ff qz225 qz576 123396485 1048576 1 1048576 2 7 0 1 123396485 3670016

noncomputable abbrev qz501 := (Complex.re qz574)

noncomputable abbrev qz502 := (Complex.im qz574)

noncomputable abbrev qz226 := (@HAdd.hAdd Real Real Real qz380 (@HMul.hMul Real Real Real qz267 qz501 qz501) (@HMul.hMul Real Real Real qz267 qz502 qz502))

noncomputable abbrev qz227 := qz496

noncomputable def ep1213 := @Enclosure.Real.IsNear.of_eq qz225 (Real.sqrt qz226) Bool.false 123396485 1048576 1 1048576 (BSN.norm_eq_sqrt_mul_add qz227)

noncomputable def ep1214 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz226) Bool.false 123396485 1048576 1 1048576 123396485

noncomputable def ep1215 := @Enclosure.Real.IsNear.sqrt_image qz226 432768637 31250 0 1 61698242 61698243 524288

noncomputable abbrev qz228 := (@HMul.hMul Real Real Real qz267 qz501 qz501)

noncomputable abbrev qz229 := (@HMul.hMul Real Real Real qz267 qz502 qz502)

noncomputable def ep1216 := @Enclosure.Real.IsNear.addLit_ff qz228 qz229 49 4 0 1 864771649 62500 0 1

noncomputable abbrev qz230 := qz501

noncomputable def ep1217 := @Enclosure.Real.IsNear.mulLit_ff qz230 qz230 7 2 0 1 7 2 0 1 49 4

noncomputable abbrev qz503 := (Enclosure.sfrac Bool.false 7 2)

noncomputable def ep1218 := @Enclosure.Complex.IsNear.of_eq qz227 (Complex.mk qz503 qz13) Bool.false 7 2 0 1 Bool.false 117628 1000 0 1 (BSN.s_add_nat_mk qz13 Bool.false 117628 1000 3 qz14)

noncomputable abbrev qz504 := (ep1218 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz13 Bool.false 7 2 0 1 Bool.false 117628 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz17))

noncomputable def ep1219 := @ep1217 0 1 (@Enclosure.Complex.IsNear.re_isNear qz227 Bool.false 7 2 0 1 Bool.false 117628 1000 0 1 qz504)

noncomputable def ep1220 := ep1219 (@Enclosure.Complex.IsNear.re_isNear qz227 Bool.false 7 2 0 1 Bool.false 117628 1000 0 1 qz504)

noncomputable abbrev qz231 := qz502

noncomputable def ep1221 := @Enclosure.Real.IsNear.mulLit_ff qz231 qz231 117628 1000 0 1 117628 1000 0 1 864771649 62500

noncomputable def ep1222 := @ep1221 0 1 (@Enclosure.Complex.IsNear.im_isNear qz227 Bool.false 7 2 0 1 Bool.false 117628 1000 0 1 qz504)

noncomputable def ep1223 := ep1222 (@Enclosure.Complex.IsNear.im_isNear qz227 Bool.false 7 2 0 1 Bool.false 117628 1000 0 1 qz504)

noncomputable def ep1224 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Real.sqrt (@HAdd.hAdd Real Real Real qz380 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))))) Bool.false 9177776557 274877906944

noncomputable def ep1225 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz380 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))))) Bool.false 9177776557 274877906944

noncomputable def ep1226 := nat_lit 2517153482446952535968724485330366622263094611454678474977021

noncomputable def ep1227 := nat_lit 2257950451351225593080491475105646602480517120000000000000000000

noncomputable def ep1228 := nat_lit 12663615176969608014928659502753168063746463823501783773865915468357

noncomputable def ep1229 := nat_lit 22787739568757533762510893016198729024258695864637823385600000000000000000000

noncomputable def ep1230 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz380 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)))) ep1226 ep1227 ep1228 ep1229

noncomputable def ep1231 := nat_lit 3569847585043725371780044448088143736806550920703785551969

noncomputable def ep1232 := nat_lit 11289752256756127965402457375528233012402585600000000000000000000

noncomputable def ep1233 := nat_lit 7418720710130575899588929359109685015790707395707260941384883311

noncomputable def ep1234 := nat_lit 11393869784378766881255446508099364512129347932318911692800000000000000000000

noncomputable def ep1235 := nat_lit 87376371976734159406054460987526006719296295183004781870369

noncomputable def ep1236 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) ep1231 ep1232 ep1233 ep1234 ep1235

noncomputable def ep1237 := nat_lit 78401057338584221981961509552279395919462400000000000000000000

noncomputable def ep1238 := nat_lit 2529755547109869372625896328806989738742976481742073850396629140347

noncomputable def ep1239 := nat_lit 4557547913751506752502178603239745804851739172927564677120000000000000000000

noncomputable def ep1240 := nat_lit 986737472536702393561324751025066635028769903951065835552794292664217594058817912198534793065033367552000000000000000000000

noncomputable def ep1241 := nat_lit 59748201521415900872944298063

noncomputable def ep1242 := nat_lit 106253245864567017308160000000000

noncomputable def ep1243 := nat_lit 21849200591157831828415920727

noncomputable def ep1244 := nat_lit 37739021225349046672073687040000000000

noncomputable def ep1245 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) ep1241 ep1242 ep1243 ep1244 ep1241 ep1242 ep1243

noncomputable def ep1246 := nat_lit 295594945790238706182166356463

noncomputable def ep1247 := nat_lit 8854437155380584775680000000000

noncomputable def ep1248 := nat_lit 250993132774251213848098677341

noncomputable def ep1249 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223) Bool.true ep1241 ep1242 ep1243 ep1244 Bool.true ep1246 ep1247 ep1248

noncomputable def ep1250 := nat_lit 30191216980279237337658949632000000000

noncomputable def ep1251 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223 Bool.true ep1241 ep1242 ep1243 ep1244 Bool.true ep1246 ep1247 ep1248 ep1250

noncomputable def ep1252 := nat_lit 241139971669564298570336691

noncomputable def ep1253 := nat_lit 188894659314785808547840000000

noncomputable def ep1254 := nat_lit 12039775944912330461414161

noncomputable def ep1255 := nat_lit 37887017387017082149219074048000000

noncomputable def ep1256 := nat_lit 151786065085428034145740181249

noncomputable def ep1257 := nat_lit 212506491729134034616320000000000

noncomputable def ep1258 := nat_lit 315406560672970085051733081389

noncomputable abbrev qz232 := (Complex.re qz497)

noncomputable abbrev qz233 := (Complex.im qz497)

noncomputable def ep1259 := @Enclosure.Real.IsNear.subLit_tt_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz232) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz233) ep1252 ep1253 ep1254 ep1255 ep1256 ep1257 ep1258

noncomputable def ep1260 := nat_lit 1207648679211169493506357985280000000000

noncomputable def ep1261 := nat_lit 22572232342118047435541607780869817711976188309667840000000

noncomputable def ep1262 := nat_lit 214693098526430132178908086272

noncomputable def ep1263 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz232 1297118411 15000000 0 1 557713088391814443 37778931862957161709568 788964944633376335 ep1262 ep1252

noncomputable def ep1264 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) 1297118411 15000000 0 1 0 1 0 1 1297118411

noncomputable def ep1265 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 3891355233 62500 0 1 1297118411 15000000 0

noncomputable def ep1266 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (Complex.mk (Enclosure.sfrac Bool.true 1 720) qz10) Bool.true 1 720 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 2 1 30 24 Bool.true BSN.bern_real_2 EMRow38.d16 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 1 720) qz10 Bool.true 1 720 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.true 1 720) qz18)

noncomputable abbrev qz505 := (@HAdd.hAdd Complex Complex Complex qz530 qz529 qz534)

noncomputable abbrev qz234 := qz505

noncomputable def ep1267 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz62 (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) qz234) Bool.true 3891355233 62500 0 1 Bool.true 12709885870759 7812500 0 1

noncomputable abbrev qz235 := (Complex.re qz505)

noncomputable abbrev qz236 := (Complex.im qz505)

noncomputable def ep1268 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz235) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz236) 432362387 12500 0 1 864771649 31250 0 1

noncomputable def ep1269 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz235 432362387 31250 0 1 5 2 0 1 432362387 12500

noncomputable abbrev qz506 := (@HAdd.hAdd Complex Complex Complex qz530 qz529 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz237 := qz506

noncomputable def ep1270 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz62 (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz237) Bool.true 432362387 31250 0 1 Bool.false 29407 125 0 1

noncomputable abbrev qz238 := (Complex.re qz506)

noncomputable abbrev qz239 := (Complex.im qz506)

noncomputable def ep1271 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz238) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz239) 3 4 0 1 864771649 62500 0 1

noncomputable def ep1272 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz238 1 2 0 1 3 2 0 1 3 4

noncomputable def ep1273 := @ep1272 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 117628 1000 0 1 ep606)

noncomputable abbrev qz507 := (Enclosure.sfrac Bool.false 3 2)

noncomputable def ep1274 := @Enclosure.Complex.IsNear.of_eq qz237 (Complex.mk qz507 qz13) Bool.false 3 2 0 1 Bool.false 117628 1000 0 1 (BSN.s_add_nat_mk qz13 Bool.false 117628 1000 1 qz14)

noncomputable abbrev qz508 := (ep1274 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz13 Bool.false 3 2 0 1 Bool.false 117628 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz17))

noncomputable def ep1275 := ep1273 (@Enclosure.Complex.IsNear.re_isNear qz237 Bool.false 3 2 0 1 Bool.false 117628 1000 0 1 qz508)

noncomputable def ep1276 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz239 117628 1000 0 1 117628 1000 0 1 864771649 62500

noncomputable def ep1277 := @ep1276 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 117628 1000 0 1 ep606)

noncomputable def ep1278 := ep1277 (@Enclosure.Complex.IsNear.im_isNear qz237 Bool.false 3 2 0 1 Bool.false 117628 1000 0 1 qz508)

noncomputable def ep1279 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz237 Bool.true 432362387 31250 0 1 Bool.false 29407 125 0 1 (@ep1271 3458899096 432362387 31250 0 1 (ep1275 rfl) (ep1278 rfl) rfl rfl)

noncomputable def ep1280 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz239) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz238) 29407 500 0 1 88221 500 0 1

noncomputable def ep1281 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz239 1 2 0 1 117628 1000 0 1 29407 500

noncomputable def ep1282 := @ep1281 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 117628 1000 0 1 ep606)

noncomputable def ep1283 := ep1282 (@Enclosure.Complex.IsNear.im_isNear qz237 Bool.false 3 2 0 1 Bool.false 117628 1000 0 1 qz508)

noncomputable def ep1284 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz238 117628 1000 0 1 3 2 0 1 88221 500

noncomputable def ep1285 := @ep1284 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 117628 1000 0 1 ep606)

noncomputable def ep1286 := ep1285 (@Enclosure.Complex.IsNear.re_isNear qz237 Bool.false 3 2 0 1 Bool.false 117628 1000 0 1 qz508)

noncomputable abbrev qz240 := (ep1270 (BSN.ascPochhammer_succ_eval_c 1 2 qz272 rfl) (ep1279 (@ep1280 58814000 29407 125 0 1 (ep1283 rfl) (ep1286 rfl) rfl rfl)))

noncomputable def ep1287 := @ep1269 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 432362387 31250 0 1 Bool.false 29407 125 0 1 qz240)

noncomputable abbrev qz509 := (Enclosure.sfrac Bool.false 5 2)

noncomputable def ep1288 := @Enclosure.Complex.IsNear.of_eq qz234 (Complex.mk qz509 qz13) Bool.false 5 2 0 1 Bool.false 117628 1000 0 1 (BSN.s_add_nat_mk qz13 Bool.false 117628 1000 2 qz14)

noncomputable abbrev qz510 := (ep1288 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz13 Bool.false 5 2 0 1 Bool.false 117628 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz17))

noncomputable def ep1289 := ep1287 (@Enclosure.Complex.IsNear.re_isNear qz234 Bool.false 5 2 0 1 Bool.false 117628 1000 0 1 qz510)

noncomputable def ep1290 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz236 29407 125 0 1 117628 1000 0 1 864771649 31250

noncomputable def ep1291 := @ep1290 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 432362387 31250 0 1 Bool.false 29407 125 0 1 qz240)

noncomputable def ep1292 := ep1291 (@Enclosure.Complex.IsNear.im_isNear qz234 Bool.false 5 2 0 1 Bool.false 117628 1000 0 1 qz510)

noncomputable def ep1293 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) qz234 Bool.true 3891355233 62500 0 1 Bool.true 12709885870759 7812500 0 1 (@ep1268 24320970206250 3891355233 62500 0 1 (ep1289 rfl) (ep1292 rfl) rfl rfl)

noncomputable def ep1294 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz236) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz235) 12714480714509 7812500 0 1 29407 50 0 1

noncomputable def ep1295 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz236 432362387 31250 0 1 117628 1000 0 1 12714480714509 7812500

noncomputable def ep1296 := @ep1295 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 432362387 31250 0 1 Bool.false 29407 125 0 1 qz240)

noncomputable def ep1297 := ep1296 (@Enclosure.Complex.IsNear.im_isNear qz234 Bool.false 5 2 0 1 Bool.false 117628 1000 0 1 qz510)

noncomputable def ep1298 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz235 29407 125 0 1 5 2 0 1 29407 50

noncomputable def ep1299 := @ep1298 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 432362387 31250 0 1 Bool.false 29407 125 0 1 qz240)

noncomputable def ep1300 := ep1299 (@Enclosure.Complex.IsNear.re_isNear qz234 Bool.false 5 2 0 1 Bool.false 117628 1000 0 1 qz510)

noncomputable abbrev qz241 := (ep1267 (BSN.ascPochhammer_succ_eval_c 2 3 qz272 rfl) (ep1293 (@ep1294 635494293537950 12709885870759 7812500 0 1 (ep1297 rfl) (ep1300 rfl) rfl rfl)))

noncomputable def ep1301 := @ep1265 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1266) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 3891355233 62500 0 1 Bool.true 12709885870759 7812500 0 1 qz241)

noncomputable def ep1302 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 12709885870759 7812500 0 1 0 1 0

noncomputable def ep1303 := @ep1302 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1266) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 3891355233 62500 0 1 Bool.true 12709885870759 7812500 0 1 qz241)

noncomputable def ep1304 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) 12709885870759 5625000000 0 1 0 1 0 1 12709885870759

noncomputable def ep1305 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 12709885870759 7812500 0 1 12709885870759 5625000000 0

noncomputable def ep1306 := @ep1305 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1266) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 3891355233 62500 0 1 Bool.true 12709885870759 7812500 0 1 qz241)

noncomputable def ep1307 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 3891355233 62500 0 1 0 1 0

noncomputable def ep1308 := @ep1307 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1266) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 3891355233 62500 0 1 Bool.true 12709885870759 7812500 0 1 qz241)

noncomputable def ep1309 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 1297118411 15000000 0 1 Bool.false 12709885870759 5625000000 0 1 (@ep1264 1297118411 15000000 0 1 (ep1301 rfl) (ep1303 rfl) rfl rfl) (@ep1304 12709885870759 5625000000 0 1 (ep1306 rfl) (ep1308 rfl) rfl rfl)

noncomputable def ep1310 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 1297118411 15000000 0 1 Bool.false 12709885870759 5625000000 0 1 ep1309

noncomputable def ep1311 := @Enclosure.Complex.IsNear.re_isNear qz223 Bool.true 557713088391814443 37778931862957161709568 788964944633376335 ep1262 Bool.true 11942362553753111 37778931862957161709568 24815845231042571 ep1262

noncomputable abbrev qz511 := (@Nat.cast Real Real.instNatCast 4586471424)

noncomputable abbrev qz242 := (@Inv.inv Real Real.instInv (Real.sqrt qz511))

noncomputable def ep1312 := @Enclosure.Complex.IsNear.of_eq qz223 (Complex.mk (@HMul.hMul Real Real Real qz0 qz242 qz140) (@HMul.hMul Real Real Real qz0 qz242 qz421)) Bool.true 557713088391814443 37778931862957161709568 788964944633376335 ep1262 Bool.true 11942362553753111 37778931862957161709568 24815845231042571

noncomputable def ep1313 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz511) 18615691844177917 274877906944 1 274877906944 2029413 2029414 137438953472 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz511) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz511 qz15)) Bool.false 18615691844177917 274877906944 1 274877906944 (BSN.sqrt_natCast_div_one 4586471424) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz511 qz15)) Bool.false 18615691844177917 274877906944 1 274877906944 18615691844177917 274877906944 1 274877906944 (BSN.sqrt_enclosure 4586471424 1 9307845922088958 9307845922088959 137438953472 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep1314 := nat_lit 15736960334339222256381591552

noncomputable def ep1315 := nat_lit 4951760157141521099596496896

noncomputable def ep1316 := nat_lit 46554144768000000000000000

noncomputable def ep1317 := nat_lit 54412538019840000000000000000

noncomputable def ep1318 := nat_lit 743426006773320438031319040

noncomputable def ep1319 := BSN.log_dyadic_bound 8 40 8 7 ep1317 137438953472 46554144768 ep1318 594330015278039040 55726700127 48 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 8) (BSN.artanhQ 40) 0 7 ep1318 ep1317 594330015278039040 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1320 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz142 117628 1000 0 1 3578170511523063 1125899906842624 7630815251 355179937500000000000 105223260232358713641 281474976710656000 224399384086157 88794984375000000000000 qz17 (BSN.isNear_log_sfrac 24 1 3578170511523063 1125899906842624 7630815251 355179937500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz424 Bool.false ep1314 ep1315 1000186216579072 ep1316 3578170511523063 1125899906842624 7630815251 355179937500000000000 (BSN.log_rat_reduce_isNear 24 1 4 48 32 55726700127 137438953472 24973259072661432 36028797018963968 46554144768 1000000000000000 rfl rfl rfl rfl (ep1319 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1321 := nat_lit 30688761455712430461143744512

noncomputable def ep1322 := nat_lit 1741285869682633512345182075706254993504400427456840532084312608046288426999777428599552199310742430802860716119524867468472493299548813963712183081814688529576852484473815281646844942146091754158889423457963946623840040482000864796316989731914149761

noncomputable def ep1323 := nat_lit 36189711061676687398051995244972293437204064634277911010709893574360646025770957327274520038916625905157259536660301123060201295733050346820418006399790474322883113512225043577386983430344807139857606659932443931695135483567632475872701705235726336000

noncomputable def ep1324 := nat_lit 112220682267176207162479702674185970392635988796576051853473831547636965018422086764180332157431577013049662003975243500844121361078008509948253084976744464331251180313997395542042065556796697973994002058737527701519306865632610839005523841

noncomputable def ep1325 := nat_lit 14162362620981476507973062010740267839751392300091410357073445043591661736142765335465980456383235157893684661228133785805343020392090474260391269629940393164584824782043325376852546309846473174526418180899875142721197660755134684030031631300396347265

noncomputable def ep1326 := nat_lit 2062813530515571181688963728963420725920631684153840927610463933738556823468944567654647642218247676593963793589637164014431473856783869768763826364788057036404337470196827483911058055529654006971883579616149304106622722563355051124743997198436401152000

noncomputable def ep1327 := BSN.sin_dyadic_bound_f 872227060873241 562949953421312 5 4 274877906944 93199215601 ep1322 ep1323 ep1324 ep1325 ep1326 ep1324 274814910018 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.sinEvenP 872227060873241) (BSN.sinEvenQ 562949953421312) 0 4 ep1322 ep1323 ep1324 rfl rfl rfl rfl) (@BSN.binarySplit_of_base4 (BSN.sinOddP 872227060873241) (BSN.sinOddQ 562949953421312) 0 4 ep1325 ep1326 ep1324 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz512 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 51378545035331) (@Nat.cast Real Real.instNatCast 137438953472))

noncomputable def ep1328 := @Enclosure.Real.IsNear.cos_image qz143 qz512 Bool.false 51378545035331 137438953472 87 34359738368 Bool.true 274814910018 274877906944 1 46554144768 (@Enclosure.Real.IsNear.recentre' qz143 Bool.false 105223260232358713641 281474976710656000 224399384086157 88794984375000000000000 51378545035331 137438953472 87 34359738368 (ep1320 rfl) rfl) (Enclosure.sfrac_false_div 51378545035331 137438953472) (BSN.cos_reduce1 qz512 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1321) (@Nat.cast Real Real.instNatCast ep1183)) 226375608064910080 72057594037927936 Bool.false 274814910018 274877906944 59 1000000000000000 93108289536 46554144768 (BSN.sin_reduce_arg_pos_rat_q1 51378545035331 137438953472 226375608064910080 72057594037927936 59 ep1321 ep1183 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 274814910018 274877906944 ep1321 ep1183 872227060873241 562949953421312 93199215601 93108289536 (ep1327 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1329 := nat_lit 512922738257017867965419424027255701233911518352068244766656073549458139275172437753122324805555001943714548818253521694737441335017681695686849419543827048907136639003745491525143360476611420166114429552888677166051377485548409046746124874548277121

noncomputable def ep1330 := nat_lit 2128806533039805141061882073233664319835533213781053588865287857315332119162997489839677649348036817950427031568253007238835370337238255695318706258811204371934300794836767269258057848843812184697506274113673172452655028445154851521923629719748608000

noncomputable def ep1331 := nat_lit 5219881211360771271680885856542541879218200891770193862360805877393228554023567321865502736332297813475731674160151170911950205411656920678758484141118158252437586728336977404423510709501871891491435108140281505422007454545349105514372564969582522241

noncomputable def ep1332 := nat_lit 325707399555090186582467957204750640934836581708501199096389042169245814231938615945470680350249633146415335829942710107541811661597453121383762057598114268905948021610025392196482850873103264258718459939391995385256219352108692282854315347121537024000

noncomputable def ep1333 := BSN.cos_dyadic_bound_f 872227060873241 562949953421312 5 4 274877906944 93199215601 ep1329 ep1330 ep1324 ep1331 ep1332 ep1324 5884637386 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.cosEvenP 872227060873241) (BSN.cosEvenQ 562949953421312) 0 4 ep1329 ep1330 ep1324 rfl rfl rfl rfl) (@BSN.binarySplit_of_base4 (BSN.cosOddP 872227060873241) (BSN.cosOddQ 562949953421312) 0 4 ep1331 ep1332 ep1324 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1334 := @Enclosure.Real.IsNear.sin_image qz143 qz512 Bool.false 51378545035331 137438953472 87 34359738368 Bool.false 5884637386 274877906944 1 46554144768 (@Enclosure.Real.IsNear.recentre' qz143 Bool.false 105223260232358713641 281474976710656000 224399384086157 88794984375000000000000 51378545035331 137438953472 87 34359738368 (ep1320 rfl) rfl) (Enclosure.sfrac_false_div 51378545035331 137438953472) (BSN.sin_reduce1 qz512 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1321) (@Nat.cast Real Real.instNatCast ep1183)) 226375608064910080 72057594037927936 Bool.false 5884637386 274877906944 59 1000000000000000 93108289536 46554144768 (BSN.sin_reduce_arg_pos_rat_q1 51378545035331 137438953472 226375608064910080 72057594037927936 59 ep1321 ep1183 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 5884637386 274877906944 ep1321 ep1183 872227060873241 562949953421312 93199215601 93108289536 (ep1333 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz513 := (@Enclosure.Real.IsNear.recentre' qz242 Bool.false 4058827 274877906944 1 274877906944 4058827 274877906944 1 274877906944 (ep1313 rfl rfl) rfl)

noncomputable def ep1335 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz242 qz140) (@HMul.hMul Real Real Real qz0 qz242 qz421) Bool.true 557713088391814443 37778931862957161709568 788964944633376335 ep1262 Bool.true 11942362553753111 37778931862957161709568 24815845231042571 ep1262 (@Enclosure.Real.IsNear.mulLit_ft qz242 qz140 4058827 274877906944 1 274877906944 137407455009 137438953472 498604777 195262235617001472 557713088391814443 37778931862957161709568 788964944633376335 ep1262 qz513 (@Enclosure.Real.IsNear.recentre' qz140 Bool.true 274814910018 274877906944 4084570333184 1599588234174476058624 137407455009 137438953472 498604777 195262235617001472 (ep1328 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz242 qz421 4058827 274877906944 1 274877906944 2942318693 137438953472 498604777 195262235617001472 11942362553753111 37778931862957161709568 24815845231042571 ep1262 qz513 (@Enclosure.Real.IsNear.neg qz141 Bool.false 2942318693 137438953472 498604777 195262235617001472 (@Enclosure.Real.IsNear.recentre' qz141 Bool.false 5884637386 274877906944 4084570333184 1599588234174476058624 2942318693 137438953472 498604777 195262235617001472 (ep1334 rfl rfl) rfl)) rfl)

noncomputable def ep1336 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz233 12709885870759 5625000000 0 1 11942362553753111 37778931862957161709568 24815845231042571 ep1262 ep1256

noncomputable def ep1337 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 1297118411 15000000 0 1 Bool.false 12709885870759 5625000000 0 1 ep1309

noncomputable def ep1338 := @Enclosure.Complex.IsNear.im_isNear qz223 Bool.true 557713088391814443 37778931862957161709568 788964944633376335 ep1262 Bool.true 11942362553753111 37778931862957161709568 24815845231042571 ep1262

noncomputable def ep1339 := nat_lit 15490658339310137426626621

noncomputable def ep1340 := nat_lit 566683977944357425643520000000

noncomputable def ep1341 := nat_lit 1893475866688933386404393

noncomputable def ep1342 := nat_lit 189435086935085410746095370240000000

noncomputable def ep1343 := nat_lit 787607744676498627426334174693

noncomputable def ep1344 := nat_lit 23611832414348226068480000000000

noncomputable def ep1345 := nat_lit 2005530880463981320717123817653

noncomputable def ep1346 := @Enclosure.Real.IsNear.addLit_tt (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz233) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz232) ep1339 ep1340 ep1341 ep1342 ep1343 ep1344 ep1345

noncomputable def ep1347 := nat_lit 241529735842233898701271597056000000000

noncomputable def ep1348 := nat_lit 446690452641757759568933844204024284971675950629519360000000

noncomputable def ep1349 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz233 1297118411 15000000 0 1 11942362553753111 37778931862957161709568 24815845231042571 ep1262 ep1339

noncomputable def ep1350 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz232 12709885870759 5625000000 0 1 557713088391814443 37778931862957161709568 788964944633376335 ep1262 ep1343

noncomputable abbrev qz514 := (@ep1312 ep1262 (BSN.cpow_neg_s_sub_mk qz13 117628 1000 24 3 4586471424 qz14 rfl EMRow38.d17) ep1335)

noncomputable def ep1351 := ep1251 (@ep1259 ep1260 ep1261 ep1241 ep1242 ep1243 ep1244 (@ep1263 ep1253 ep1254 ep1255 ep1310 (ep1311 qz514) rfl) (@ep1336 ep1257 ep1258 ep1260 ep1337 (ep1338 qz514) rfl) rfl rfl) (@ep1346 ep1347 ep1348 ep1246 ep1247 ep1248 ep1250 (@ep1349 ep1340 ep1341 ep1342 ep1310 (ep1338 qz514) rfl) (@ep1350 ep1344 ep1345 ep1347 ep1337 (ep1311 qz514) rfl) rfl rfl)

noncomputable def ep1352 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) ep1246 ep1247 ep1248 ep1250 ep1246 ep1247 ep1248

noncomputable def ep1353 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223) Bool.true ep1241 ep1242 ep1243 ep1244 Bool.true ep1246 ep1247 ep1248

noncomputable def ep1354 := @ep1211 1132505367249202145 1008806316530991104 291632333011 1008806316530991104 (@ep1212 1 3670016 (ep1213 (@ep1214 1048576 1 1048576 (ep1215 (@ep1216 3462149096 432768637 31250 0 1 (ep1220 rfl) (ep1223 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep1224 2289 274877906944 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (@ep1225 2289 274877906944 9177776557 274877906944 2289 274877906944 (@ep1230 4588887134 4588889423 137438953472 (@ep1236 ep1237 ep1238 ep1239 ep1240 ep1226 ep1227 ep1228 ep1229 (@ep1245 ep1244 ep1231 ep1232 ep1233 ep1234 (@ep1249 ep1250 ep1351) (@ep1249 ep1250 ep1351) rfl) (@ep1352 ep1250 ep1235 ep1237 ep1238 ep1239 (@ep1353 ep1250 ep1351) (@ep1353 ep1250 ep1351) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow38.d18 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz380 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 24))) (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)))) Bool.false 10615710213822614249 9079256848778919936 99385925189843 1008806316530991104 := ep1209 (ep1210 ep1354) rfl rfl

noncomputable abbrev qz577 := (@HAdd.hAdd Complex Complex Complex qz579 qz585 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz515 := qz577

noncomputable abbrev qz243 := (@HDiv.hDiv Real Real Real qz270 (@Norm.norm Complex Complex.instNorm qz515) (@HAdd.hAdd Real Real Real qz380 (Complex.re qz429) qz296))

noncomputable abbrev qz516 := (@HPow.hPow Complex Complex Complex qz531 qz560 (@HSub.hSub Complex Complex Complex qz552 qz569 qz533))

noncomputable abbrev qz244 := qz516

noncomputable def ep1355 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz152 1 24))) (@HMul.hMul Real Real Real qz0 qz243 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) 1207542743 28991029248 11563669 115964116992 152135287145554485 126100789566373888 40409766771

noncomputable def ep1356 := nat_lit 4562830652617093413091672064

noncomputable def ep1357 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz152 1 24)) 26561 1769472 1 1769472 45463 16384 857 131072 1207542743 28991029248

noncomputable def ep1358 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz152 1 24)) (Real.sqrt (@HAdd.hAdd Real Real Real qz380 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz152 1 24)) (Complex.re (zetaApproximant qz152 1 24))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz152 1 24)) (Complex.im (zetaApproximant qz152 1 24))))) Bool.false 45463 16384 857 131072

noncomputable def ep1359 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz380 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz152 1 24)) (Complex.re (zetaApproximant qz152 1 24))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz152 1 24)) (Complex.im (zetaApproximant qz152 1 24))))) Bool.false 2909632 1048576 6856 1048576

noncomputable def ep1360 := nat_lit 692178108276864409759035110242268725172994809

noncomputable def ep1361 := nat_lit 89895780058961471129404312781328482304000000

noncomputable def ep1362 := nat_lit 1556050771599133279523267773110577793450087575096422299065139

noncomputable def ep1363 := nat_lit 42886344485053033066605066664783464208389901068772835328000000

noncomputable def ep1364 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz380 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz152 1 24)) (Complex.re (zetaApproximant qz152 1 24))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz152 1 24)) (Complex.im (zetaApproximant qz152 1 24)))) ep1360 ep1361 ep1362 ep1363 1451388 1458244

noncomputable def ep1365 := nat_lit 24808103998967122226960092215224679498109430730536209

noncomputable def ep1366 := nat_lit 3223695205298203892267225676465191810385900994560000

noncomputable def ep1367 := nat_lit 37461908811571948887486892714102719199229471746845366481501

noncomputable def ep1368 := nat_lit 1057863163964641482309591644397992117140284226363063271424000

noncomputable def ep1369 := nat_lit 1365345617683982146015453527912256122311597529522001

noncomputable def ep1370 := nat_lit 322369520529820389226722567646519181038590099456000000

noncomputable def ep1371 := nat_lit 1381015331810008011130568533937299558809032658299575343158643

noncomputable def ep1372 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz152 1 24)) (Complex.re (zetaApproximant qz152 1 24))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz152 1 24)) (Complex.im (zetaApproximant qz152 1 24))) ep1365 ep1366 ep1367 ep1368 ep1369 ep1370 ep1371

noncomputable def ep1373 := nat_lit 1586794745946962223464387466596988175710426339544594907136000000

noncomputable def ep1374 := nat_lit 8001778049522253772623128310466091128876564262545115720263869036869374386899632667960640830666503618560000

noncomputable def ep1375 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz152 1 24)) (Complex.re (zetaApproximant qz152 1 24)) ep875 ep876 ep877 ep878 ep875 ep876 ep877 ep878 ep1365

noncomputable def ep1376 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (zetaApproximant qz152 1 24)) (Complex.im (zetaApproximant qz152 1 24)) ep997 ep998 ep999 ep1000 ep997 ep998 ep999 ep1000 ep1369

noncomputable def ep1377 := @ep1355 126100789566373888 ep1356 4249467190929775511 3404721318292094976 340601865692449 3404721318292094976 (@ep1357 11563669 115964116992 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) qz498) Bool.false 26561 1769472 1 1769472 (BSN.theta_err_eq 1 2 96 162 EMRow38.d14 EMRow38.d15 rfl) (ep1189 rfl)) (ep1358 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz152 1 24)) (@ep1359 45463 16384 857 131072 (@ep1364 524288 (@ep1372 ep1373 ep1374 ep1360 ep1361 ep1362 ep1363 (@ep1375 ep1366 ep1367 ep1368 ep1171 ep1171 rfl) (@ep1376 ep1370 ep1371 ep1373 ep1177 ep1177 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz245 := (@Norm.norm Complex Complex.instNorm qz515)

noncomputable def ep1378 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz243 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz245 qz576) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) Bool.false 152135287145554485 126100789566373888 40409766771 126100789566373888 (BSN.zrb_shape_eq qz245 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) qz155 3)

noncomputable def ep1379 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz245 qz576) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) 125637367 3670016 1 3670016 1210907955 34359738368 39 4294967296

noncomputable def ep1380 := @Enclosure.Real.IsNear.mulLit_ff qz245 qz576 125637367 1048576 1 1048576 2 7 0 1 125637367 3670016

noncomputable abbrev qz517 := (Complex.re qz577)

noncomputable abbrev qz518 := (Complex.im qz577)

noncomputable abbrev qz246 := (@HAdd.hAdd Real Real Real qz380 (@HMul.hMul Real Real Real qz267 qz517 qz517) (@HMul.hMul Real Real Real qz267 qz518 qz518))

noncomputable abbrev qz247 := qz515

noncomputable def ep1381 := @Enclosure.Real.IsNear.of_eq qz245 (Real.sqrt qz246) Bool.false 125637367 1048576 1 1048576 (BSN.norm_eq_sqrt_mul_add qz247)

noncomputable def ep1382 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz246) Bool.false 125637367 1048576 1 1048576 125637367

noncomputable def ep1383 := @Enclosure.Real.IsNear.sqrt_image qz246 3589036189 250000 0 1 62818683 62818684 524288

noncomputable abbrev qz248 := (@HMul.hMul Real Real Real qz267 qz517 qz517)

noncomputable abbrev qz249 := (@HMul.hMul Real Real Real qz267 qz518 qz518)

noncomputable def ep1384 := @Enclosure.Real.IsNear.addLit_ff qz248 qz249 49 4 0 1 3585973689 250000 0 1

noncomputable abbrev qz250 := qz517

noncomputable def ep1385 := @Enclosure.Real.IsNear.mulLit_ff qz250 qz250 7 2 0 1 7 2 0 1 49 4

noncomputable def ep1386 := @Enclosure.Complex.IsNear.of_eq qz247 (Complex.mk qz503 qz155) Bool.false 7 2 0 1 Bool.false 119766 1000 0 1 (BSN.s_add_nat_mk qz155 Bool.false 119766 1000 3 qz156)

noncomputable abbrev qz519 := (ep1386 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz155 Bool.false 7 2 0 1 Bool.false 119766 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz157))

noncomputable def ep1387 := @ep1385 0 1 (@Enclosure.Complex.IsNear.re_isNear qz247 Bool.false 7 2 0 1 Bool.false 119766 1000 0 1 qz519)

noncomputable def ep1388 := ep1387 (@Enclosure.Complex.IsNear.re_isNear qz247 Bool.false 7 2 0 1 Bool.false 119766 1000 0 1 qz519)

noncomputable abbrev qz251 := qz518

noncomputable def ep1389 := @Enclosure.Real.IsNear.mulLit_ff qz251 qz251 119766 1000 0 1 119766 1000 0 1 3585973689 250000

noncomputable def ep1390 := @ep1389 0 1 (@Enclosure.Complex.IsNear.im_isNear qz247 Bool.false 7 2 0 1 Bool.false 119766 1000 0 1 qz519)

noncomputable def ep1391 := ep1390 (@Enclosure.Complex.IsNear.im_isNear qz247 Bool.false 7 2 0 1 Bool.false 119766 1000 0 1 qz519)

noncomputable def ep1392 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Real.sqrt (@HAdd.hAdd Real Real Real qz380 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))))) Bool.false 1210907955 34359738368

noncomputable def ep1393 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz380 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))))) Bool.false 9687263640 274877906944

noncomputable def ep1394 := nat_lit 6381524169683255327000145056006567887900090314904704362816139349

noncomputable def ep1395 := nat_lit 5138091693741455571809829490018182490977887846400000000000000000000

noncomputable def ep1396 := nat_lit 11797222878135182365196252060129503828266420633404513393664200901297107

noncomputable def ep1397 := nat_lit 18437250621951774477282887465550616115232319656603757943193600000000000000000000

noncomputable def ep1398 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz380 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)))) ep1394 ep1395 ep1396 ep1397

noncomputable def ep1399 := nat_lit 179760226920533794089631355074591091561576954661682507695977161

noncomputable def ep1400 := nat_lit 570899077082383952423314387779798054553098649600000000000000000000

noncomputable def ep1401 := nat_lit 2922802782668848735624953983786771648236360760934474785371401472099063

noncomputable def ep1402 := nat_lit 47636821273984511801934628603352480638458977229495617935523449

noncomputable def ep1403 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) ep1399 ep1400 ep1401 ep1397 ep1402

noncomputable def ep1404 := nat_lit 51380916937414555718098294900181824909778878464000000000000000000

noncomputable def ep1405 := nat_lit 2218605023866583407392824519085683045007514968117509652073199857299511

noncomputable def ep1406 := nat_lit 4609312655487943619320721866387654028808079914150939485798400000000000000000000

noncomputable def ep1407 := nat_lit 36432062588510970321231321503950385129432150838731549919161218724311678142302666606896802229038619730173231104000000000000000000

noncomputable def ep1408 := nat_lit 13407469072145338873604012580131

noncomputable def ep1409 := nat_lit 755578637259143234191360000000000

noncomputable def ep1410 := nat_lit 19180249350435407455318910412059

noncomputable def ep1411 := nat_lit 4293861970528602643578161725440000000000

noncomputable def ep1412 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) ep1408 ep1409 ep1410 ep1411 ep1408 ep1409 ep1410

noncomputable def ep1413 := nat_lit 6901943296926200610231497114357

noncomputable def ep1414 := nat_lit 226673591177742970257408000000000

noncomputable def ep1415 := nat_lit 16969201014646846007777986424251

noncomputable def ep1416 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) qz244) Bool.true ep1408 ep1409 ep1410 ep1411 Bool.true ep1413 ep1414 ep1415

noncomputable def ep1417 := nat_lit 2146930985264301321789080862720000000000

noncomputable def ep1418 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) qz244 Bool.true ep1408 ep1409 ep1410 ep1411 Bool.true ep1413 ep1414 ep1415 ep1417

noncomputable def ep1419 := nat_lit 66183408930253247297722871

noncomputable def ep1420 := nat_lit 56668397794435742564352000000

noncomputable def ep1421 := nat_lit 3750958724065390344740422447

noncomputable def ep1422 := nat_lit 12881585911585807930734485176320000000

noncomputable def ep1423 := nat_lit 37575070859225886728903122900393

noncomputable def ep1424 := nat_lit 2266735911777429702574080000000000

noncomputable def ep1425 := nat_lit 53789789327240832021216308789177

noncomputable abbrev qz252 := (Complex.re qz516)

noncomputable abbrev qz253 := (Complex.im qz516)

noncomputable def ep1426 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3)))) qz252) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253) ep1419 ep1420 ep1421 ep1422 ep1423 ep1424 ep1425

noncomputable def ep1427 := nat_lit 12881585911585807930734485176320000000000

noncomputable def ep1428 := nat_lit 2279339372390779059681872434140816156830631449472270336000000

noncomputable def ep1429 := nat_lit 107346549263215066089454043136

noncomputable def ep1430 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3)))) qz252 10757608567 120000000 0 1 30761208923922565 2361183241434822606848 348679606689893641 ep1429 ep1419

noncomputable def ep1431 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3)))) 10757608567 120000000 0 1 0 1 0 1 10757608567

noncomputable def ep1432 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 32272825701 500000 0 1 10757608567 120000000 0

noncomputable abbrev qz520 := (@HAdd.hAdd Complex Complex Complex qz530 qz568 qz534)

noncomputable abbrev qz254 := qz520

noncomputable def ep1433 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz62 (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 2)) qz254) Bool.true 32272825701 500000 0 1 Bool.true 214652780605887 125000000 0 1

noncomputable abbrev qz255 := (Complex.re qz520)

noncomputable abbrev qz256 := (Complex.im qz520)

noncomputable def ep1434 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 2))) qz255) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 2))) qz256) 3585786189 100000 0 1 3585973689 125000 0 1

noncomputable def ep1435 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 2))) qz255 3585786189 250000 0 1 5 2 0 1 3585786189 100000

noncomputable abbrev qz521 := (@HAdd.hAdd Complex Complex Complex qz530 qz568 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz257 := qz521

noncomputable def ep1436 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz62 (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1)) qz257) Bool.true 3585786189 250000 0 1 Bool.false 59883 250 0 1

noncomputable abbrev qz258 := (Complex.re qz521)

noncomputable abbrev qz259 := (Complex.im qz521)

noncomputable def ep1437 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1))) qz258) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1))) qz259) 3 4 0 1 3585973689 250000 0 1

noncomputable def ep1438 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1))) qz258 1 2 0 1 3 2 0 1 3 4

noncomputable def ep1439 := @ep1438 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 119766 1000 0 1 ep1133)

noncomputable def ep1440 := @Enclosure.Complex.IsNear.of_eq qz257 (Complex.mk qz507 qz155) Bool.false 3 2 0 1 Bool.false 119766 1000 0 1 (BSN.s_add_nat_mk qz155 Bool.false 119766 1000 1 qz156)

noncomputable abbrev qz522 := (ep1440 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz155 Bool.false 3 2 0 1 Bool.false 119766 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz157))

noncomputable def ep1441 := ep1439 (@Enclosure.Complex.IsNear.re_isNear qz257 Bool.false 3 2 0 1 Bool.false 119766 1000 0 1 qz522)

noncomputable def ep1442 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1))) qz259 119766 1000 0 1 119766 1000 0 1 3585973689 250000

noncomputable def ep1443 := @ep1442 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 119766 1000 0 1 ep1133)

noncomputable def ep1444 := ep1443 (@Enclosure.Complex.IsNear.im_isNear qz257 Bool.false 3 2 0 1 Bool.false 119766 1000 0 1 qz522)

noncomputable def ep1445 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1)) qz257 Bool.true 3585786189 250000 0 1 Bool.false 59883 250 0 1 (@ep1437 14343144756 3585786189 250000 0 1 (ep1441 rfl) (ep1444 rfl) rfl rfl)

noncomputable def ep1446 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1))) qz259) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1))) qz258) 59883 1000 0 1 179649 1000 0 1

noncomputable def ep1447 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1))) qz259 1 2 0 1 119766 1000 0 1 59883 1000

noncomputable def ep1448 := @ep1447 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 119766 1000 0 1 ep1133)

noncomputable def ep1449 := ep1448 (@Enclosure.Complex.IsNear.im_isNear qz257 Bool.false 3 2 0 1 Bool.false 119766 1000 0 1 qz522)

noncomputable def ep1450 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1))) qz258 119766 1000 0 1 3 2 0 1 179649 1000

noncomputable def ep1451 := @ep1450 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 119766 1000 0 1 ep1133)

noncomputable def ep1452 := ep1451 (@Enclosure.Complex.IsNear.re_isNear qz257 Bool.false 3 2 0 1 Bool.false 119766 1000 0 1 qz522)

noncomputable abbrev qz260 := (ep1436 (BSN.ascPochhammer_succ_eval_c 1 2 qz429 rfl) (ep1445 (@ep1446 239532000 59883 250 0 1 (ep1449 rfl) (ep1452 rfl) rfl rfl)))

noncomputable def ep1453 := @ep1435 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 3585786189 250000 0 1 Bool.false 59883 250 0 1 qz260)

noncomputable def ep1454 := @Enclosure.Complex.IsNear.of_eq qz254 (Complex.mk qz509 qz155) Bool.false 5 2 0 1 Bool.false 119766 1000 0 1 (BSN.s_add_nat_mk qz155 Bool.false 119766 1000 2 qz156)

noncomputable abbrev qz523 := (ep1454 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz155 Bool.false 5 2 0 1 Bool.false 119766 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz157))

noncomputable def ep1455 := ep1453 (@Enclosure.Complex.IsNear.re_isNear qz254 Bool.false 5 2 0 1 Bool.false 119766 1000 0 1 qz523)

noncomputable def ep1456 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 2))) qz256 59883 250 0 1 119766 1000 0 1 3585973689 125000

noncomputable def ep1457 := @ep1456 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 3585786189 250000 0 1 Bool.false 59883 250 0 1 qz260)

noncomputable def ep1458 := ep1457 (@Enclosure.Complex.IsNear.im_isNear qz254 Bool.false 5 2 0 1 Bool.false 119766 1000 0 1 qz523)

noncomputable def ep1459 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 2)) qz254 Bool.true 32272825701 500000 0 1 Bool.true 214652780605887 125000000 0 1 (@ep1434 806820642525000 32272825701 500000 0 1 (ep1455 rfl) (ep1458 rfl) rfl rfl)

noncomputable def ep1460 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 2))) qz256) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 2))) qz255) 214727634355887 125000000 0 1 59883 100 0 1

noncomputable def ep1461 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 2))) qz256 3585786189 250000 0 1 119766 1000 0 1 214727634355887 125000000

noncomputable def ep1462 := @ep1461 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 3585786189 250000 0 1 Bool.false 59883 250 0 1 qz260)

noncomputable def ep1463 := ep1462 (@Enclosure.Complex.IsNear.im_isNear qz254 Bool.false 5 2 0 1 Bool.false 119766 1000 0 1 qz523)

noncomputable def ep1464 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 2))) qz255 59883 250 0 1 5 2 0 1 59883 100

noncomputable def ep1465 := @ep1464 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 3585786189 250000 0 1 Bool.false 59883 250 0 1 qz260)

noncomputable def ep1466 := ep1465 (@Enclosure.Complex.IsNear.re_isNear qz254 Bool.false 5 2 0 1 Bool.false 119766 1000 0 1 qz523)

noncomputable abbrev qz261 := (ep1433 (BSN.ascPochhammer_succ_eval_c 2 3 qz429 rfl) (ep1459 (@ep1460 21465278060588700 214652780605887 125000000 0 1 (ep1463 rfl) (ep1466 rfl) rfl rfl)))

noncomputable def ep1467 := @ep1432 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1266) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 32272825701 500000 0 1 Bool.true 214652780605887 125000000 0 1 qz261)

noncomputable def ep1468 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 214652780605887 125000000 0 1 0 1 0

noncomputable def ep1469 := @ep1468 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1266) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 32272825701 500000 0 1 Bool.true 214652780605887 125000000 0 1 qz261)

noncomputable def ep1470 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3)))) 71550926868629 30000000000 0 1 0 1 0 1 71550926868629

noncomputable def ep1471 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 214652780605887 125000000 0 1 71550926868629 30000000000 0

noncomputable def ep1472 := @ep1471 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1266) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 32272825701 500000 0 1 Bool.true 214652780605887 125000000 0 1 qz261)

noncomputable def ep1473 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 32272825701 500000 0 1 0 1 0

noncomputable def ep1474 := @ep1473 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1266) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 32272825701 500000 0 1 Bool.true 214652780605887 125000000 0 1 qz261)

noncomputable def ep1475 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 10757608567 120000000 0 1 Bool.false 71550926868629 30000000000 0 1 (@ep1431 10757608567 120000000 0 1 (ep1467 rfl) (ep1469 rfl) rfl rfl) (@ep1470 71550926868629 30000000000 0 1 (ep1472 rfl) (ep1474 rfl) rfl rfl)

noncomputable def ep1476 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 10757608567 120000000 0 1 Bool.false 71550926868629 30000000000 0 1 ep1475

noncomputable def ep1477 := nat_lit 429386197052860264357816172544

noncomputable def ep1478 := @Enclosure.Complex.IsNear.re_isNear qz244 Bool.true 30761208923922565 2361183241434822606848 348679606689893641 ep1429 Bool.false 525151420165605317 75557863725914323419136 751769287713093013 ep1477

noncomputable def ep1479 := @Enclosure.Complex.IsNear.of_eq qz244 (Complex.mk (@HMul.hMul Real Real Real qz0 qz242 qz216) (@HMul.hMul Real Real Real qz0 qz242 qz493)) Bool.true 30761208923922565 2361183241434822606848 348679606689893641 ep1429 Bool.false 525151420165605317 75557863725914323419136 751769287713093013

noncomputable def ep1480 := @Enclosure.Real.IsNear.mulLit_ff qz155 qz142 119766 1000 0 1 3578170511523063 1125899906842624 7630815251 355179937500000000000 214271584741535581629 562949953421312000 152318703225211 59196656250000000000000 qz157 (BSN.isNear_log_sfrac 24 1 3578170511523063 1125899906842624 7630815251 355179937500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz424 Bool.false ep1314 ep1315 1000186216579072 ep1316 3578170511523063 1125899906842624 7630815251 355179937500000000000 (BSN.log_rat_reduce_isNear 24 1 4 48 32 55726700127 137438953472 24973259072661432 36028797018963968 46554144768 1000000000000000 rfl rfl rfl rfl (ep1319 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1481 := nat_lit 19414225829657583281508450304

noncomputable def ep1482 := nat_lit 39614081257132168796771975168

noncomputable def ep1483 := nat_lit 977607333110203234154726376294407266101999924671259914270566325181166246623663923198018015067211827700005570264546631936

noncomputable def ep1484 := nat_lit 406704355798688102870807269590474370206928662370602703270828848655152000467652488154169143141621708451154749585707730206720

noncomputable def ep1485 := nat_lit 33567748488483716207123061035906128797834860142619690560125116660197536370093261306014732366009832925430772587520256

noncomputable def ep1486 := nat_lit 2932754863833632735031764882761149986048404104293494503430578725310178344798251583071442015736903463434165849248464855296

noncomputable def ep1487 := nat_lit 18301696010940964629186327131571346659311789806677121647187298189481840021044361966937611441372976880301963731356847859302400

noncomputable def ep1488 := BSN.cos_dyadic_bound_f 275892742673386 562949953421312 3 2 274877906944 93199215601 ep1483 ep1484 ep1485 ep1486 ep1487 ep1485 242522947040 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 275892742673386) (BSN.cosEvenQ 562949953421312) 0 2 ep1483 ep1484 ep1485 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 275892742673386) (BSN.cosOddQ 562949953421312) 0 2 ep1486 ep1487 ep1485 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz524 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 104624797237077) (@Nat.cast Real Real.instNatCast 274877906944))

noncomputable def ep1489 := @Enclosure.Real.IsNear.cos_image qz218 qz524 Bool.false 104624797237077 274877906944 709 274877906944 Bool.true 242522947040 274877906944 1 46554144768 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 214271584741535581629 562949953421312000 152318703225211 59196656250000000000000 104624797237077 274877906944 709 274877906944 (ep1480 rfl) rfl) (Enclosure.sfrac_false_div 104624797237077 274877906944) (BSN.cos_reduce2 qz524 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1481) (@Nat.cast Real Real.instNatCast ep1482)) 226375608064910080 72057594037927936 Bool.false 242522947040 274877906944 60 1000000000000000 93108289536 46554144768 (BSN.sin_reduce_arg_pos_rat_q2 104624797237077 274877906944 226375608064910080 72057594037927936 60 ep1481 ep1482 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 242522947040 274877906944 ep1481 ep1482 275892742673386 562949953421312 93199215601 93108289536 (ep1488 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1490 := nat_lit 1759666345399575034505541778881104354080561596520153749934571285232771085893498987147387615335088481993669681858113921280

noncomputable def ep1491 := nat_lit 3660339202188192925837265426314269331862357961335424329437459637896368004208872393387522288274595376060392746271369571860480

noncomputable def ep1492 := nat_lit 4608595604453715164354940745446929460288179115398267008424875068277903000376469577248662587739496294063446088377537618176

noncomputable def ep1493 := nat_lit 67106218706783536973683199482428271084143229291149446039686760028100080077162660545437908618367581894440533681641775484108800

noncomputable def ep1494 := BSN.sin_dyadic_bound_f 275892742673386 562949953421312 3 2 274877906944 93199215601 ep1490 ep1491 ep1485 ep1492 ep1493 ep1485 129385021871 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 275892742673386) (BSN.sinEvenQ 562949953421312) 0 2 ep1490 ep1491 ep1485 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 275892742673386) (BSN.sinOddQ 562949953421312) 0 2 ep1492 ep1493 ep1485 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1495 := @Enclosure.Real.IsNear.sin_image qz218 qz524 Bool.false 104624797237077 274877906944 709 274877906944 Bool.true 129385021871 274877906944 1 46554144768 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 214271584741535581629 562949953421312000 152318703225211 59196656250000000000000 104624797237077 274877906944 709 274877906944 (ep1480 rfl) rfl) (Enclosure.sfrac_false_div 104624797237077 274877906944) (BSN.sin_reduce2 qz524 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1481) (@Nat.cast Real Real.instNatCast ep1482)) 226375608064910080 72057594037927936 Bool.false 129385021871 274877906944 60 1000000000000000 93108289536 46554144768 (BSN.sin_reduce_arg_pos_rat_q2 104624797237077 274877906944 226375608064910080 72057594037927936 60 ep1481 ep1482 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 129385021871 274877906944 ep1481 ep1482 275892742673386 562949953421312 93199215601 93108289536 (ep1494 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1496 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz242 qz216) (@HMul.hMul Real Real Real qz0 qz242 qz493) Bool.true 30761208923922565 2361183241434822606848 348679606689893641 ep1429 Bool.false 525151420165605317 75557863725914323419136 751769287713093013 ep1477 (@Enclosure.Real.IsNear.mulLit_ft qz242 qz216 4058827 274877906944 1 274877906944 7578842095 8589934592 4062715643 1562097884936011776 30761208923922565 2361183241434822606848 348679606689893641 ep1429 qz513 (@Enclosure.Real.IsNear.recentre' qz216 Bool.true 242522947040 274877906944 33281766547456 12796705873395808468992 7578842095 8589934592 4062715643 1562097884936011776 (ep1489 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz242 qz493 4058827 274877906944 1 274877906944 129385021871 274877906944 4062715643 1562097884936011776 525151420165605317 75557863725914323419136 751769287713093013 ep1477 qz513 (@Enclosure.Real.IsNear.neg qz217 Bool.true 129385021871 274877906944 4062715643 1562097884936011776 (@Enclosure.Real.IsNear.recentre' qz217 Bool.true 129385021871 274877906944 33281766547456 12796705873395808468992 129385021871 274877906944 4062715643 1562097884936011776 (ep1495 rfl rfl) rfl)) rfl)

noncomputable def ep1497 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253 71550926868629 30000000000 0 1 525151420165605317 75557863725914323419136 751769287713093013 ep1477 ep1423

noncomputable def ep1498 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 10757608567 120000000 0 1 Bool.false 71550926868629 30000000000 0 1 ep1475

noncomputable def ep1499 := @Enclosure.Complex.IsNear.im_isNear qz244 Bool.true 30761208923922565 2361183241434822606848 348679606689893641 ep1429 Bool.false 525151420165605317 75557863725914323419136 751769287713093013 ep1477

noncomputable def ep1500 := nat_lit 5649373416545732316899950739

noncomputable def ep1501 := nat_lit 9066943647109718810296320000000

noncomputable def ep1502 := nat_lit 8087239729909857234716642371

noncomputable def ep1503 := nat_lit 51526343646343231722937940705280000000

noncomputable def ep1504 := nat_lit 440198602021240244884624742677

noncomputable def ep1505 := nat_lit 14167099448608935641088000000000

noncomputable def ep1506 := nat_lit 24948349038850902934497189488189

noncomputable def ep1507 := @Enclosure.Real.IsNear.addLit_ft_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3)))) qz252) ep1500 ep1501 ep1502 ep1503 ep1504 ep1505 ep1506

noncomputable def ep1508 := nat_lit 3220396477896451982683621294080000000000

noncomputable def ep1509 := nat_lit 3911220683048532641128587449177442443294280073756016640000000

noncomputable def ep1510 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253 10757608567 120000000 0 1 525151420165605317 75557863725914323419136 751769287713093013 ep1477 ep1500

noncomputable def ep1511 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3)))) qz252 71550926868629 30000000000 0 1 30761208923922565 2361183241434822606848 348679606689893641 ep1429 ep1504

noncomputable abbrev qz525 := (@ep1479 ep1477 (BSN.cpow_neg_s_sub_mk qz155 119766 1000 24 3 4586471424 qz156 rfl EMRow38.d17) ep1496)

noncomputable def ep1512 := ep1418 (@ep1426 ep1427 ep1428 ep1408 ep1409 ep1410 ep1411 (@ep1430 ep1420 ep1421 ep1422 ep1476 (ep1478 qz525) rfl) (@ep1497 ep1424 ep1425 ep1427 ep1498 (ep1499 qz525) rfl) rfl rfl) (@ep1507 ep1508 ep1509 ep1413 ep1414 ep1415 ep1417 (@ep1510 ep1501 ep1502 ep1503 ep1476 (ep1499 qz525) rfl) (@ep1511 ep1505 ep1506 ep1508 ep1498 (ep1478 qz525) rfl) rfl rfl)

noncomputable def ep1513 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) ep1413 ep1414 ep1415 ep1417 ep1413 ep1414 ep1415

noncomputable def ep1514 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) qz244) Bool.true ep1408 ep1409 ep1410 ep1411 Bool.true ep1413 ep1414 ep1415

noncomputable def ep1515 := @ep1379 152135287145554485 126100789566373888 40409766771 126100789566373888 (@ep1380 1 3670016 (ep1381 (@ep1382 1048576 1 1048576 (ep1383 (@ep1384 14356144756 3589036189 250000 0 1 (ep1388 rfl) (ep1391 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep1392 39 4294967296 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (@ep1393 2496 274877906944 1210907955 34359738368 39 4294967296 (@ep1398 4843630572 4843633068 137438953472 (@ep1403 ep1404 ep1405 ep1406 ep1407 ep1394 ep1395 ep1396 ep1397 (@ep1412 ep1411 ep1399 ep1400 ep1401 ep1397 (@ep1416 ep1417 ep1512) (@ep1416 ep1417 ep1512) rfl) (@ep1513 ep1417 ep1402 ep1404 ep1405 ep1406 (@ep1514 ep1417 ep1512) (@ep1514 ep1417 ep1512) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow38.d19 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz380 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz152 1 24))) (@HMul.hMul Real Real Real qz0 qz243 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)))) Bool.false 4249467190929775511 3404721318292094976 340601865692449 3404721318292094976 := ep1377 (ep1378 ep1515) rfl rfl

noncomputable def EMRow38.d20 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J))

noncomputable abbrev qz526 := (EMRow38.d3 qz536 qz570 (@Enclosure.dec_le_dec qz536 qz570 117628 1000 119766 1000 (@Eq.refl Real qz536) (@Eq.refl Real qz570) rfl rfl rfl) 24 24 1 1)

noncomputable abbrev qz262 := qz526

noncomputable def ep1516 := @Zeta.Certificates.ZIntervalEM.Certificate.mk qz262 (@Enclosure.dec_nonneg qz13 117628 1000 qz14) (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 24 rfl)

noncomputable abbrev qz263 := (Zeta.Certificates.ZIntervalEM.fstVal qz526)

noncomputable def ep1517 := @Enclosure.Real.IsNear.pos_val qz263 ep291 ep292

noncomputable def ep1518 := @Enclosure.Real.IsNear.of_eq qz263 (hardyZApproximantEM 1 24 qz13) Bool.false

noncomputable abbrev qz264 := (Zeta.Certificates.ZIntervalEM.sndVal qz526)

noncomputable def ep1519 := BSN.mul_neg_of_pos_neg_r qz263 qz264 (@ep1517 ep293 ep294 (@ep1518 ep291 ep292 ep293 ep294 (@Eq.refl Real (hardyZApproximantEM 1 24 qz13)) EMRow38.d10) rfl rfl rfl)

noncomputable def ep1520 := @Enclosure.Real.IsNear.neg_val qz264 ep858 ep859

noncomputable def ep1521 := @Enclosure.Real.IsNear.of_eq qz264 (hardyZApproximantEM 1 24 qz155) Bool.true

noncomputable def ep1522 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz263) (BSN.hardyZErrorBoundStrong 1 24 qz13)

noncomputable def ep1523 := @Enclosure.norm_gt_of_isNear qz263 (BSN.hardyZErrorBoundStrong 1 24 qz13) Bool.false

noncomputable def ep1524 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 24 qz13) (@HAdd.hAdd Real Real Real qz380 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 24))) (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)))) Bool.false 10615710213822614249 9079256848778919936 99385925189843 1008806316530991104 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz380 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 24))) (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)))))

noncomputable def ep1525 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz264) (BSN.hardyZErrorBoundStrong 1 24 qz155)

noncomputable def ep1526 := @Enclosure.norm_gt_of_isNear qz264 (BSN.hardyZErrorBoundStrong 1 24 qz155) Bool.true

noncomputable def ep1527 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 24 qz155) (@HAdd.hAdd Real Real Real qz380 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz152 1 24))) (@HMul.hMul Real Real Real qz0 qz243 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)))) Bool.false 4249467190929775511 3404721318292094976 340601865692449 3404721318292094976 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz380 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz152 1 24))) (@HMul.hMul Real Real Real qz0 qz243 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)))))

noncomputable def ep1528 := @List.cons EMRow38.d0 (@PSigma.mk Zeta.Certificates.ZIntervalEM Zeta.Certificates.ZIntervalEM.Certificate qz262 (ep1516 (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 24 rfl) (ep1519 (@ep1520 ep860 ep861 (@ep1521 ep858 ep859 ep860 ep861 (@Eq.refl Real (hardyZApproximantEM 1 24 qz155)) EMRow38.d13) rfl rfl rfl)) (ep1522 (hardyZErrorBoundEM 1 24 qz13) (BSN.hardyZErrorBoundEM_le_strong 1 24 qz13 rfl) (@ep1523 Bool.false ep291 ep292 ep293 ep294 10615710213822614249 9079256848778919936 99385925189843 1008806316530991104 (@ep1518 ep291 ep292 ep293 ep294 (@Eq.refl Real (hardyZApproximantEM 1 24 qz13)) EMRow38.d10) (ep1524 EMRow38.d18) rfl rfl rfl rfl rfl)) (ep1525 (hardyZErrorBoundEM 1 24 qz155) (BSN.hardyZErrorBoundEM_le_strong 1 24 qz155 rfl) (@ep1526 Bool.false ep858 ep859 ep860 ep861 4249467190929775511 3404721318292094976 340601865692449 3404721318292094976 (@ep1521 ep858 ep859 ep860 ep861 (@Eq.refl Real (hardyZApproximantEM 1 24 qz155)) EMRow38.d13) (ep1527 EMRow38.d19) rfl rfl rfl rfl rfl)))) (@List.nil EMRow38.d0)

noncomputable abbrev qz527 := (@Enclosure.dec_le_dec qz536 qz570 117628 1000 119766 1000 (@Eq.refl Real qz536) (@Eq.refl Real qz570) rfl rfl rfl)

noncomputable abbrev qz265 := (Zeta.Certificates.CertifiedZeroIntervals.intervals (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1528 (@List.IsChain.singleton EMRow38.d1 EMRow38.d20 (EMRow38.d2 qz284 qz436 qz527))))

noncomputable abbrev qz528 := (@NonemptyInterval Real Real.instLE)

noncomputable def ep1529 := And (@Eq (Option Real) (@Option.map qz528 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz528 qz265)) (@Option.some Real qz13))

noncomputable def ep1530 := ep1529 (@Eq (Option Real) (@Option.map qz528 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz528 qz265)) (@Option.some Real qz155))

noncomputable def ep1531 := @And.intro (@Eq Nat (@List.length qz528 qz265) 1) ep1530

noncomputable def ep1532 := @And.intro (@Eq (Option Real) (@Option.map qz528 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz528 qz265)) (@Option.some Real qz13))

noncomputable def ep1533 := @ep1532 (@Eq (Option Real) (@Option.map qz528 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz528 qz265)) (@Option.some Real qz155))

noncomputable abbrev qz266 := (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1528 (@List.IsChain.singleton EMRow38.d1 EMRow38.d20 (EMRow38.d2 qz284 qz436 qz527)))

theorem EMRow38.d21 : Zeta.Certificates.BatchSpec 1 117628 1000 119766 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz528 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 1) (And (@Eq (Option Real) (@Option.map qz528 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz528 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz13)) (@Eq (Option Real) (@Option.map qz528 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz528 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz155)))) qz266 (ep1531 (@Eq.refl Nat 1) (ep1533 (@Eq.refl (Option Real) (@Option.some Real qz13)) (@Eq.refl (Option Real) (@Option.some Real qz155))))

theorem solution : Zeta.Certificates.BatchSpec 1 117628 1000 119766 1000 := EMRow38.d21
#print axioms solution
#check solution
