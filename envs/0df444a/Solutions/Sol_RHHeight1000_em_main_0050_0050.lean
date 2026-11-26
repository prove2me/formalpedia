-- Prove2me | solution 1 for RHHeight1000.em_main_0050_0050
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-19T21:59:21.369562+00:00
-- url     : https://prove2.me/submissions/eaa8b6b2-da98-4bb9-822e-97d0587f114b

import Definitions.Def_RHT1000_Support_20261118_S005
/- Copyright (c) 2026 Salvatore Mercuri, Bhavik Mehta.
Apache 2.0 license; see the source project LICENSE. -/
set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def EMRow50.d0 := @PSigma Zeta.Certificates.ZIntervalEM fun (I : Zeta.Certificates.ZIntervalEM) => Zeta.Certificates.ZIntervalEM.Certificate I

noncomputable def EMRow50.d1 := @NonemptyInterval Real Real.instLE

noncomputable def EMRow50.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h

noncomputable def EMRow50.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) (fc sc fb sb : Nat) => Zeta.Certificates.ZIntervalEM.mk (EMRow50.d2 a b h) fc sc fb sb

noncomputable def ep0 := nat_lit 26986075409044028275299783

noncomputable def ep1 := nat_lit 4294967296000000000000000

noncomputable def ep2 := nat_lit 26986075409044045455168967

noncomputable abbrev qz267 := (@instHMul Real Real.instMul)

noncomputable abbrev qz0 := qz267

noncomputable abbrev qz268 := (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 2 1) Real.pi)

noncomputable def ep3 := @BSN.isNear_log_image_fff qz268 884279719003555 140737488355328 1 500000000000000 ep0 ep1 ep2 ep1 4138529546116343 2251799813685248 250000000199203 99601500000000000000 4138529546116343 2251799813685248 250000000199203 99601500000000000000 963576 524288

noncomputable abbrev qz269 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 2 1) Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) BSN.pi_near_15 rfl)

noncomputable def ep4 := @ep3 2 524288 qz269 rfl rfl rfl rfl

noncomputable def ep5 := nat_lit 53972150818088056550599566

noncomputable def ep6 := nat_lit 34359738368000000000000000

noncomputable def ep7 := nat_lit 9806206225044028275299783

noncomputable def ep8 := nat_lit 44165944593044028275299783

noncomputable def ep9 := nat_lit 13681445815609410487519367394620474863599256634174726093703677122907123617368241606644861540940610176751640793056574796245399519365549113997355475306157239709119582688278313060810592403844863400465080549957745

noncomputable def ep10 := nat_lit 231714499556395493334623298703961145503103241611736774613091488581016477543539392410113701224645713379230392133956226737605624599560350113120270717249177907454870984269546186598262646369758174842349131395304

noncomputable def ep11 := nat_lit 8978369550011295664474073352761810093897501552430546263638635096022803738134167562509900960712119243631997923545019968443113540909076206607473711060286601587364321108377403290080403445693385008949995305

noncomputable def ep12 := BSN.log_dyadic_bound ep7 ep8 5 4 ep9 1048576 398406 ep10 ep11 473518 ep5 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep7) (BSN.artanhQ ep8) 0 4 ep10 ep9 ep11 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz270 := (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))

noncomputable abbrev qz1 := qz270

noncomputable def ep13 := ep4 rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep1 4138529546116343 2251799813685248 250000000199203 99601500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep0) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 69433004117575847641088 37778931862957161709568 1000000000796812 398406000000000000000 4138529546116343 2251799813685248 250000000199203 99601500000000000000 (BSN.log_rat_reduce_isNear ep0 ep1 2 ep5 ep6 473518 1048576 24973259072661432 36028797018963968 398406 1000000000000000 rfl rfl rfl rfl (ep12 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep14 := nat_lit 53972150818088090910337934

noncomputable def ep15 := nat_lit 9806206225044045455168967

noncomputable def ep16 := nat_lit 44165944593044045455168967

noncomputable def ep17 := nat_lit 13681445815609453062485491347592146866046743284321690683909457683007658987562290830600045658905080811372395010565947827677605470036294121079488508864180301737865471494204890974265645509835068840465080549957745

noncomputable def ep18 := nat_lit 231714499556396865510889920206523150079811393376960301632499817942333196803513131357563499488546302200815366867712007119763002650772307103678175657719139104636874731038771518520299266622696414842349131395304

noncomputable def ep19 := nat_lit 8978369550011421500876706511871067098718760264493934208903156435737864998391937547068187824077011975074541700434630537294838404525415248443919841847024664017658842168336182958576672102333385008949995305

noncomputable def ep20 := BSN.log_dyadic_bound ep15 ep16 5 4 ep17 1048576 398406 ep18 ep19 473518 ep14 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep15) (BSN.artanhQ ep16) 0 4 ep18 ep17 ep19 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep21 := ep13 (BSN.isNear_log_sfrac ep2 ep1 4138529546116343 2251799813685248 250000000199203 99601500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep2) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 69433004117575847641088 37778931862957161709568 1000000000796812 398406000000000000000 4138529546116343 2251799813685248 250000000199203 99601500000000000000 (BSN.log_rat_reduce_isNear ep2 ep1 2 ep14 ep6 473518 1048576 24973259072661432 36028797018963968 398406 1000000000000000 rfl rfl rfl rfl (ep20 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable abbrev qz2 := (Real.log (@HMul.hMul Real Real Real qz267 (2 : Real) Real.pi))

theorem EMRow50.d4 : Enclosure.Real.IsNear qz2 Bool.false 120447 65536 1 262144 := @Enclosure.Real.IsNear.of_eq qz2 (Real.log qz268) Bool.false 120447 65536 1 262144 BSN.log_two_pi_eq (@Enclosure.Real.IsNear.recentre' (Real.log qz268) Bool.false 963576 524288 2 524288 120447 65536 1 262144 (ep21 rfl rfl rfl rfl rfl rfl rfl rfl) rfl)

noncomputable def ep22 := nat_lit 8589934592000000000000000

noncomputable def ep23 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 ep0 ep22 ep2 ep22 1200336 1048576 1 398406 1200336 1048576 1 398406 600168 524288 2 524288 BSN.pi_near_15 rfl rfl rfl

noncomputable def ep24 := nat_lit 17179869184000000000000000

noncomputable def ep25 := nat_lit 18396140817044028275299783

noncomputable def ep26 := nat_lit 35576010001044028275299783

noncomputable def ep27 := nat_lit 145019262663961446558303139663424756232419223153299357158415217874016130572233056993847515999529612750616182853355499335896178729185698845314776375864537073527142908641610750276034469165612529925303649396973267518946591078603565291376312767403717761600170009932259137778521478520425507632472584532570900560707662248426541531715360699177249902784721815296292248142738824858695953661559845440650653128788875447728828657762006237171740033404723254477174341920697506370253193455781322964835857351124092897592956162654178130575

noncomputable def ep28 := nat_lit 15500762873619990602332184736899274490522931101512051618692838888825382235673431503644115344741331161500627469184702974962114537943617674254904297224139410345221262767191485292268260077615645253784097850065864022184521411511133693085443040736512010941548648374196772723338837137976260321103066698629790037694560548409922339907589559883712609967105556007429010014773911317423638534096849366294542840133852248768895750397896505791271178551667935288585787166713880920071720072716082683081155281219708172458141800988558163320

noncomputable def ep29 := nat_lit 12900190794487083783367107939442176642390171280542213571554777169279725287102813254708993369099729304728646904879886535518616983985412662170766446331701281703998252143668221340329975389245922410714088123244705567402747658401492589451585970559635763980329972215329212888079422466283203384882259392047898400615815810081169907384366653346471604103896809335921621947903075223769953790093549808584241881353287841076643853121427928248525828402335494512605306631304432120211393210317325496757155861061354331245840675149075

noncomputable def ep30 := BSN.log_dyadic_bound ep25 ep26 11 10 ep27 1048576 398406 ep28 ep29 1200336 ep5 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep25) (BSN.artanhQ ep26) 0 10 ep28 ep27 ep29 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep31 := nat_lit 18396140817044045455168967

noncomputable def ep32 := nat_lit 35576010001044045455168967

noncomputable def ep33 := nat_lit 145019262663962847171784895425483977818796535899227200426399035286881207006285364467913811844950531107314785650583974625982406238691319033447632878979985852280879486690814033867010958364699188952871572448188560932645032521756218245629809291975913196623825614492380080480004685076434733043183791438169545293975334857826316990371107134320667652578346815517853870648072772035977941843998949310557583393428557296298890786965786350523173236912472938174255438182435383147950274229549088258679583524155427309880956162654178130575

noncomputable def ep34 := nat_lit 15500762873620157189619721156942591192100275120160672416764593300158228469749443299607348495591439275767946573253526107895503597951484257520435868240203420954375895980141891044871083424251900562230440202302413072793440172565998181227591194192658878334739610458454844032013325963992941389843551995646587189684848765634635122388286241104146031552341815777883628509454807838726994150833304950745987647656768534710890974432620160470644835720379148964170536679305861738540146791997074363921127776563807649880221800988558163320

noncomputable def ep35 := nat_lit 12900190794487324729109480814509220959173684627296055849229843377126536688487849343376525559792931631054411655715865486295286288812423905434305314401904993536755333953308594664509631000767632482919425633906965368325056855874260596615770736441041599390097968820060635361729170158825410327022636428624381203910573184452046894301676992229743752846881064485858738985580654099214803581683226335297196686880535448467637789069028262446657986458573827723305156755787640135484017403116612632808333639900906331245840675149075

noncomputable def ep36 := BSN.log_dyadic_bound ep31 ep32 11 10 ep33 1048576 398406 ep34 ep35 1200336 ep14 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep31) (BSN.artanhQ ep32) 0 10 ep34 ep33 ep35 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep37 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 600168 524288 2 524288 75021 65536 1 262144 (ep23 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep22 1200336 1048576 1 398406 Bool.false (BSN.logfrac_isNear ep5 ep24 1 ep0 ep22 1200336 1048576 398406 rfl rfl rfl (ep30 rfl))) (BSN.isNear_log_sfrac ep2 ep22 1200336 1048576 1 398406 Bool.false (BSN.logfrac_isNear ep14 ep24 1 ep2 ep22 1200336 1048576 398406 rfl rfl rfl (ep36 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl

theorem EMRow50.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 75021 65536 1 262144 := ep37

noncomputable abbrev qz608 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 142522 1000)))

noncomputable abbrev qz534 := qz608

noncomputable abbrev qz271 := qz534

noncomputable abbrev qz3 := (BSN.headSumC qz271 9)

noncomputable abbrev qz609 := (@instHAdd Complex Complex.instAdd)

noncomputable abbrev qz535 := qz609

noncomputable abbrev qz272 := qz535

noncomputable abbrev qz4 := qz272

noncomputable abbrev qz5 := qz271

noncomputable abbrev qz536 := (@instHPow Complex Complex Complex.instPow)

noncomputable abbrev qz273 := qz536

noncomputable abbrev qz6 := qz273

noncomputable abbrev qz537 := (@Neg.neg Complex Complex.instNeg qz608)

noncomputable abbrev qz274 := qz537

noncomputable abbrev qz7 := qz274

noncomputable abbrev qz538 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 8) qz7)

noncomputable def ep38 := @Enclosure.Complex.IsNear.of_eq qz3 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 8) qz538) Bool.false 691151233701 1099511627776 177941061257957 73008671595954176 Bool.false 75251180895 137438953472 88953851129385 36504335797977088

noncomputable def ep39 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 8) qz538 Bool.false 499909486389 1099511627776 159290079919997 73008671595954176 Bool.false 940449462003 1099511627776 159230356204557 73008671595954176 Bool.false

noncomputable abbrev qz539 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 7) qz7)

noncomputable def ep40 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 8) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 7) qz539) Bool.false 499909486389 1099511627776 159290079919997 73008671595954176 Bool.false 940449462003 1099511627776 159230356204557 73008671595954176

noncomputable def ep41 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 7) qz539 Bool.false 58351473091 274877906944 209014882449413 109513007393931264 Bool.false 1259322252553 1099511627776 417824271665695 219026014787862528 Bool.false

noncomputable abbrev qz540 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 6) qz7)

noncomputable def ep42 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 7) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 6) qz540) Bool.false 58351473091 274877906944 209014882449413 109513007393931264 Bool.false 1259322252553 1099511627776 417824271665695 219026014787862528

noncomputable def ep43 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 6) qz540 Bool.false 256916369921 549755813888 29450750515405 18252167898988544 Bool.false 908825722039 1099511627776 117723635535959 73008671595954176 Bool.true

noncomputable abbrev qz541 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 5) qz7)

noncomputable def ep44 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 6) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 5) qz541) Bool.false 256916369921 549755813888 29450750515405 18252167898988544 Bool.false 908825722039 1099511627776 117723635535959 73008671595954176

noncomputable def ep45 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 5) qz541 Bool.false 1005077541869 1099511627776 282554803599745 219026014787862528 Bool.false 887306203109 1099511627776 282516241883005 219026014787862528 Bool.true

noncomputable abbrev qz542 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 4) qz7)

noncomputable def ep46 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 5) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 4) qz542) Bool.false 1005077541869 1099511627776 282554803599745 219026014787862528 Bool.false 887306203109 1099511627776 282516241883005 219026014787862528

noncomputable def ep47 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 4) qz542 Bool.false 1522803614351 1099511627776 203269651279271 219026014787862528 Bool.false 1072210693695 1099511627776 203357545220555 219026014787862528 Bool.true

noncomputable abbrev qz543 := (@Nat.cast Complex Complex.instNatCast 3)

noncomputable abbrev qz275 := qz543

noncomputable abbrev qz8 := qz275

noncomputable def ep48 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 4) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz7)) Bool.false 1522803614351 1099511627776 203269651279271 219026014787862528 Bool.false 1072210693695 1099511627776 203357545220555 219026014787862528

noncomputable def ep49 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz7) Bool.false 483356294273 549755813888 18647291102385 36504335797977088 Bool.false 383023048265 549755813888 18675646321415 36504335797977088 Bool.false

noncomputable abbrev qz544 := (@Nat.cast Complex Complex.instNatCast 2)

noncomputable abbrev qz276 := qz544

noncomputable abbrev qz9 := qz276

noncomputable def ep50 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 3) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz7)) Bool.false 483356294273 549755813888 18647291102385 36504335797977088 Bool.false 383023048265 549755813888 18675646321415 36504335797977088

noncomputable def ep51 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz7) Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.true

noncomputable abbrev qz277 := (Enclosure.sfrac Bool.false 0 1)

noncomputable abbrev qz10 := qz277

noncomputable def ep52 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz10) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz5)

noncomputable abbrev qz545 := (@Nat.cast Real Real.instNatCast 2)

noncomputable abbrev qz11 := (@Inv.inv Real Real.instInv (Real.sqrt qz545))

noncomputable abbrev qz610 := (Enclosure.sfrac Bool.false 142522 1000)

noncomputable abbrev qz546 := qz610

noncomputable abbrev qz278 := qz546

noncomputable abbrev qz279 := (Enclosure.sfrac Bool.false 2 1)

noncomputable abbrev qz12 := (@HMul.hMul Real Real Real qz267 qz278 (Real.log qz279))

noncomputable abbrev qz13 := qz278

noncomputable abbrev qz280 := (@Eq.refl Real qz546)

noncomputable abbrev qz14 := qz280

noncomputable def ep53 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz9 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz11 (Real.cos qz12)) (@HMul.hMul Real Real Real qz0 qz11 (@Neg.neg Real Real.instNeg (Real.sin qz12)))) Bool.true 66399519615 549755813888 18647291102385 36504335797977088 Bool.false 383023048265 549755813888 18675646321415 36504335797977088 (BSN.cpow_neg_s_mk qz13 142522 1000 2 qz14 rfl)

noncomputable abbrev qz15 := (@Nat.cast Real Real.instNatCast 1)

noncomputable def ep54 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz545) 1482911 1048576 1 1048576 370727 370728 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz545) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz545 qz15)) Bool.false 1482911 1048576 1 1048576 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz545 qz15)) Bool.false 1482911 1048576 1 1048576 1482911 1048576 1 1048576 (BSN.sqrt_enclosure 2 1 741455 741456 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep55 := BSN.log_dyadic_bound 1 3 6 5 613814355 524288 199203 24381081 945 363408 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 1) (BSN.artanhQ 3) 0 5 24381081 613814355 945 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep56 := nat_lit 2918700277491429577059148755906639021656608253938817348602000659124018776082401

noncomputable def ep57 := nat_lit 18237254054877300779212430138868345486890022584838388836214569481246317918289920

noncomputable def ep58 := nat_lit 6642666320942172054408356921846787878017842908613917309832757312981149386721

noncomputable def ep59 := nat_lit 8742815499832404387068629553876223489213789075999224211186336462746094029473761

noncomputable def ep60 := nat_lit 820676432469478535064559356249075546910051016317727497629655626656084306323046400

noncomputable abbrev qz281 := (BSN.cosEvenQ 2147483648)

noncomputable abbrev qz282 := (BSN.cosOddQ 2147483648)

noncomputable def ep61 := BSN.cos_dyadic_bound_f 3004642491 2147483648 3 2 1048576 398796 ep56 ep57 ep58 ep59 ep60 ep58 179106 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3004642491) qz281 0 2 ep56 ep57 ep58 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3004642491) qz282 0 2 ep59 ep60 ep58 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz16 := (@Nat.cast Real Real.instNatCast 1048576)

noncomputable abbrev qz17 := (Real.log qz279)

noncomputable abbrev qz18 := (Enclosure.Real.IsNear.const Bool.false 142522 1000)

noncomputable abbrev qz19 := (@Nat.cast Real Real.instNatCast 151115727451828646838272)

noncomputable abbrev qz283 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 103587269) qz16)

noncomputable abbrev qz284 := (BSN.isNear_log_sfrac 2 1 363408 524288 1 199203 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 363408 524288 199203 rfl rfl rfl (ep55 rfl)))

noncomputable def ep62 := @Enclosure.Real.IsNear.cos_image qz12 qz283 Bool.false 103587269 1048576 47 65536 Bool.true 179106 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz12 Bool.false 1618551093 16384000 71261 99601500 103587269 1048576 47 65536 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz17 142522 1000 0 1 363408 524288 1 199203 1618551093 16384000 71261 99601500 qz18 qz284 rfl) rfl) (Enclosure.sfrac_false_div 103587269 1048576) (BSN.cos_reduce2 qz283 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 211432918858463191236608) qz19) 226375608064910080 72057594037927936 Bool.false 179106 1048576 15 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q2 103587269 1048576 226375608064910080 72057594037927936 15 211432918858463191236608 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 179106 1048576 211432918858463191236608 151115727451828646838272 3004642491 2147483648 398796 398406 (ep61 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep63 := nat_lit 5248346366427819501062941075094472808679480582762980093635734980572848877438945

noncomputable def ep64 := nat_lit 164135286493895707012911871249815109382010203263545499525931125331216861264609280

noncomputable def ep65 := nat_lit 13734914261838954224219613094993010175691372637765287236258624294422158532380641

noncomputable def ep66 := nat_lit 3009146919054754628570050972913277005336853726498334157975403964405642456517836800

noncomputable abbrev qz285 := (BSN.sinEvenQ 2147483648)

noncomputable abbrev qz286 := (BSN.sinOddQ 2147483648)

noncomputable def ep67 := BSN.sin_dyadic_bound_f 3004642491 2147483648 3 2 1048576 398796 ep63 ep64 ep58 ep65 ep66 ep58 1033166 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3004642491) qz285 0 2 ep63 ep64 ep58 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3004642491) qz286 0 2 ep65 ep66 ep58 rfl rfl rfl rfl) rfl rfl

noncomputable def ep68 := @Enclosure.Real.IsNear.sin_image qz12 qz283 Bool.false 103587269 1048576 47 65536 Bool.true 1033166 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz12 Bool.false 1618551093 16384000 71261 99601500 103587269 1048576 47 65536 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz17 142522 1000 0 1 363408 524288 1 199203 1618551093 16384000 71261 99601500 qz18 qz284 rfl) rfl) (Enclosure.sfrac_false_div 103587269 1048576) (BSN.sin_reduce2 qz283 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 211432918858463191236608) qz19) 226375608064910080 72057594037927936 Bool.false 1033166 1048576 15 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q2 103587269 1048576 226375608064910080 72057594037927936 15 211432918858463191236608 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1033166 1048576 211432918858463191236608 151115727451828646838272 3004642491 2147483648 398796 398406 (ep67 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz287 := (@Enclosure.Real.IsNear.recentre' qz11 Bool.false 741455 1048576 1 1048576 741455 1048576 1 1048576 (ep54 rfl rfl) rfl)

noncomputable def ep69 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz11 (Real.cos qz12)) (@HMul.hMul Real Real Real qz0 qz11 (@Neg.neg Real Real.instNeg (Real.sin qz12))) Bool.true 66399519615 549755813888 18647291102385 36504335797977088 Bool.false 383023048265 549755813888 18675646321415 36504335797977088 (@Enclosure.Real.IsNear.mulLit_ft qz11 (Real.cos qz12) 741455 1048576 1 1048576 89553 524288 9428077 13054967808 66399519615 549755813888 18647291102385 36504335797977088 qz287 (@Enclosure.Real.IsNear.recentre' (Real.cos qz12) Bool.true 179106 1048576 9428077 13054967808 89553 524288 9428077 13054967808 (ep62 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz11 (@Neg.neg Real Real.instNeg (Real.sin qz12)) 741455 1048576 1 1048576 516583 524288 9428077 13054967808 383023048265 549755813888 18675646321415 36504335797977088 qz287 (@Enclosure.Real.IsNear.neg (Real.sin qz12) Bool.true 516583 524288 9428077 13054967808 (@Enclosure.Real.IsNear.recentre' (Real.sin qz12) Bool.true 1033166 1048576 9428077 13054967808 516583 524288 9428077 13054967808 (ep68 rfl rfl) rfl)) rfl)

noncomputable abbrev qz288 := (Enclosure.Real.IsNear.const Bool.false 0 1)

noncomputable abbrev qz20 := qz288

noncomputable def ep70 := @ep51 66399519615 549755813888 18647291102385 36504335797977088 Bool.false 383023048265 549755813888 18675646321415 36504335797977088 Bool.false 483356294273 483356294273 549755813888 18647291102385 36504335797977088 Bool.false 383023048265 383023048265 549755813888 18675646321415 36504335797977088 (ep52 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz10 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz20)) (ep53 ep69) rfl rfl

noncomputable abbrev qz547 := (@Nat.cast Real Real.instNatCast 3)

noncomputable abbrev qz21 := (@Inv.inv Real Real.instInv (Real.sqrt qz547))

noncomputable abbrev qz22 := (@HMul.hMul Real Real Real qz267 qz278 (Real.log (Enclosure.sfrac Bool.false 3 1)))

noncomputable def ep71 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz8 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz21 (Real.cos qz22)) (@HMul.hMul Real Real Real qz0 qz21 (@Neg.neg Real Real.instNeg (Real.sin qz22)))) Bool.false 556091025805 1099511627776 91385904664961 219026014787862528 Bool.false 306164597165 1099511627776 91303667292065 219026014787862528 (BSN.cpow_neg_s_mk qz13 142522 1000 3 qz14 rfl)

noncomputable def ep72 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz547) 1816187 1048576 1 1048576 302697 302698 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz547) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz547 qz15)) Bool.false 1816187 1048576 1 1048576 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz547 qz15)) Bool.false 1816187 1048576 1 1048576 1816187 1048576 1 1048576 (BSN.sqrt_enclosure 3 1 908093 908094 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep73 := BSN.log_dyadic_bound 1 2 10 9 171633298636800 524288 199203 16925142283965 34459425 575989 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP 1) (BSN.artanhQ 2) 0 9 16925142283965 171633298636800 34459425 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep74 := nat_lit 1777088393721487645262496148804272984446408548933317958797736043466836118508065

noncomputable def ep75 := nat_lit 762856095536686536752092846722041588959060557837977968212589092758584201761

noncomputable def ep76 := nat_lit 4653044026068265387961319858449831653834660101541237927759821636262961650242081

noncomputable def ep77 := BSN.sin_dyadic_bound_f 2292478797 2147483648 3 2 1048576 398796 ep74 ep64 ep75 ep76 ep66 ep75 918559 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2292478797) qz285 0 2 ep74 ep64 ep75 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2292478797) qz286 0 2 ep76 ep66 ep75 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz23 := (Real.log (Enclosure.sfrac Bool.false 3 1))

noncomputable abbrev qz289 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2565347) (@Nat.cast Real Real.instNatCast 16384))

noncomputable abbrev qz290 := (BSN.isNear_log_sfrac 3 1 575989 524288 1 199203 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 575989 524288 199203 rfl rfl rfl (ep73 rfl)))

noncomputable abbrev qz291 := (@Nat.cast Real Real.instNatCast 2361183241434822606848)

noncomputable def ep78 := @Enclosure.Real.IsNear.cos_image qz22 qz289 Bool.false 2565347 16384 751 1048576 Bool.false 918559 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz22 Bool.false 41045552129 262144000 71261 99601500 2565347 16384 751 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz23 142522 1000 0 1 575989 524288 1 199203 41045552129 262144000 71261 99601500 qz18 qz290 rfl) rfl) (Enclosure.sfrac_false_div 2565347 16384) (BSN.cos_reduce3 qz289 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2520607093819445346304) qz291) 226375608064910080 72057594037927936 Bool.false 918559 1048576 24 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q3 2565347 16384 226375608064910080 72057594037927936 24 2520607093819445346304 2361183241434822606848 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 918559 1048576 2520607093819445346304 2361183241434822606848 2292478797 2147483648 398796 398406 (ep77 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep79 := nat_lit 987610376998842774717721012823139232065319887433104633984614508189468325483041

noncomputable def ep80 := nat_lit 2961305418805454951079658852775973613018041541183637946017418346382887808045601

noncomputable def ep81 := BSN.cos_dyadic_bound_f 2292478797 2147483648 3 2 1048576 398796 ep79 ep57 ep75 ep80 ep60 ep75 505727 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2292478797) qz281 0 2 ep79 ep57 ep75 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2292478797) qz282 0 2 ep80 ep60 ep75 rfl rfl rfl rfl) rfl rfl

noncomputable def ep82 := @Enclosure.Real.IsNear.sin_image qz22 qz289 Bool.false 2565347 16384 751 1048576 Bool.true 505727 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz22 Bool.false 41045552129 262144000 71261 99601500 2565347 16384 751 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz23 142522 1000 0 1 575989 524288 1 199203 41045552129 262144000 71261 99601500 qz18 qz290 rfl) rfl) (Enclosure.sfrac_false_div 2565347 16384) (BSN.sin_reduce3 qz289 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2520607093819445346304) qz291) 226375608064910080 72057594037927936 Bool.false 505727 1048576 24 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q3 2565347 16384 226375608064910080 72057594037927936 24 2520607093819445346304 2361183241434822606848 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 505727 1048576 2520607093819445346304 2361183241434822606848 2292478797 2147483648 398796 398406 (ep81 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz292 := (@Enclosure.Real.IsNear.recentre' qz21 Bool.false 605395 1048576 1 1048576 605395 1048576 1 1048576 (ep72 rfl rfl) rfl)

noncomputable def ep83 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz21 (Real.cos qz22)) (@HMul.hMul Real Real Real qz0 qz21 (@Neg.neg Real Real.instNeg (Real.sin qz22))) Bool.false 556091025805 1099511627776 91385904664961 219026014787862528 Bool.false 306164597165 1099511627776 91303667292065 219026014787862528 (@Enclosure.Real.IsNear.mulLit_ff qz21 (Real.cos qz22) 605395 1048576 1 1048576 918559 1048576 150650029 208879484928 556091025805 1099511627776 91385904664961 219026014787862528 qz292 (@Enclosure.Real.IsNear.recentre' (Real.cos qz22) Bool.false 918559 1048576 150650029 208879484928 918559 1048576 150650029 208879484928 (ep78 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz21 (@Neg.neg Real Real.instNeg (Real.sin qz22)) 605395 1048576 1 1048576 505727 1048576 150650029 208879484928 306164597165 1099511627776 91303667292065 219026014787862528 qz292 (@Enclosure.Real.IsNear.neg (Real.sin qz22) Bool.true 505727 1048576 150650029 208879484928 (@Enclosure.Real.IsNear.recentre' (Real.sin qz22) Bool.true 505727 1048576 150650029 208879484928 505727 1048576 150650029 208879484928 (ep82 rfl rfl) rfl)) rfl)

noncomputable def ep84 := @ep49 556091025805 1099511627776 91385904664961 219026014787862528 Bool.false 306164597165 1099511627776 91303667292065 219026014787862528 Bool.false 837170140399122081906688 1522803614351 1099511627776 203269651279271 219026014787862528 Bool.false 589454062571711795036160 1072210693695 1099511627776 203357545220555 219026014787862528 (ep50 (BSN.head_sum_c_succ qz5 2 3 rfl rfl) (ep70 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep71 ep83) rfl rfl

noncomputable abbrev qz548 := (@Nat.cast Real Real.instNatCast 4)

noncomputable abbrev qz24 := (@Inv.inv Real Real.instInv (Real.sqrt qz548))

noncomputable abbrev qz25 := (@HMul.hMul Real Real Real qz267 qz278 (Real.log (Enclosure.sfrac Bool.false 4 1)))

noncomputable def ep85 := @Enclosure.Complex.IsNear.of_eq qz542 (Complex.mk (@HMul.hMul Real Real Real qz0 qz24 (Real.cos qz25)) (@HMul.hMul Real Real Real qz0 qz24 (@Neg.neg Real Real.instNeg (Real.sin qz25)))) Bool.true 258863036241 549755813888 39642576160237 109513007393931264 Bool.true 92452245293 549755813888 39579348331225 109513007393931264 (BSN.cpow_neg_s_mk qz13 142522 1000 4 qz14 rfl)

noncomputable def ep86 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz548) 2097153 1048576 1 1048576 262143 262144 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz548) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz548 qz15)) Bool.false 2097153 1048576 1 1048576 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz548 qz15)) Bool.false 2097153 1048576 1 1048576 2097153 1048576 1 1048576 (BSN.sqrt_enclosure 4 1 1048576 1048577 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep87 := nat_lit 318077276165597140789031982421875

noncomputable def ep88 := nat_lit 49379992292270016474244603430625

noncomputable def ep89 := nat_lit 20095619060363156210525625

noncomputable def ep90 := BSN.log_dyadic_bound 3 5 14 13 ep87 524288 199203 ep88 ep89 726817 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base13 (BSN.artanhP 3) (BSN.artanhQ 5) 0 13 ep88 ep87 ep89 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep91 := nat_lit 3110368828121075664403764917915705345289984912183211611828358688139815484630625

noncomputable def ep92 := nat_lit 2335440743947012768776285479940714977619400907525412281152678389011250390625

noncomputable def ep93 := nat_lit 8142422883874522052765175084716467127700481454248608315857168418212546149590625

noncomputable def ep94 := BSN.sin_dyadic_bound_f 2636611285 2147483648 3 2 1048576 398796 ep91 ep64 ep92 ep93 ep66 ep92 987486 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2636611285) qz285 0 2 ep91 ep64 ep92 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2636611285) qz286 0 2 ep93 ep66 ep92 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz26 := (Real.log (Enclosure.sfrac Bool.false 4 1))

noncomputable abbrev qz293 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 25896853) (@Nat.cast Real Real.instNatCast 131072))

noncomputable abbrev qz294 := (BSN.isNear_log_sfrac 4 1 726817 524288 1 199203 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 726817 524288 199203 rfl rfl rfl (ep90 rfl)))

noncomputable abbrev qz295 := (@Nat.cast Real Real.instNatCast 18889465931478580854784)

noncomputable def ep95 := @Enclosure.Real.IsNear.cos_image qz25 qz293 Bool.false 25896853 131072 47 65536 Bool.true 987486 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz25 Bool.false 51793706237 262144000 71261 99601500 25896853 131072 47 65536 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz26 142522 1000 0 1 726817 524288 1 199203 51793706237 262144000 71261 99601500 qz18 qz294 rfl) rfl) (Enclosure.sfrac_false_div 25896853 131072) (BSN.cos_reduce1 qz293 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 23191878132305615650816) qz295) 226375608064910080 72057594037927936 Bool.false 987486 1048576 31 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q1 25896853 131072 226375608064910080 72057594037927936 31 23191878132305615650816 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 987486 1048576 23191878132305615650816 18889465931478580854784 2636611285 2147483648 398796 398406 (ep94 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep96 := nat_lit 1729020655953462930343769970166476620706711351616239967585156017139458047190625

noncomputable def ep97 := nat_lit 5182391086372494765493757339539548432164895253033669078193162694640351640790625

noncomputable def ep98 := BSN.cos_dyadic_bound_f 2636611285 2147483648 3 2 1048576 398796 ep96 ep57 ep92 ep97 ep60 ep92 352678 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2636611285) qz281 0 2 ep96 ep57 ep92 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2636611285) qz282 0 2 ep97 ep60 ep92 rfl rfl rfl rfl) rfl rfl

noncomputable def ep99 := @Enclosure.Real.IsNear.sin_image qz25 qz293 Bool.false 25896853 131072 47 65536 Bool.false 352678 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz25 Bool.false 51793706237 262144000 71261 99601500 25896853 131072 47 65536 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz26 142522 1000 0 1 726817 524288 1 199203 51793706237 262144000 71261 99601500 qz18 qz294 rfl) rfl) (Enclosure.sfrac_false_div 25896853 131072) (BSN.sin_reduce1 qz293 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 23191878132305615650816) qz295) 226375608064910080 72057594037927936 Bool.false 352678 1048576 31 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q1 25896853 131072 226375608064910080 72057594037927936 31 23191878132305615650816 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 352678 1048576 23191878132305615650816 18889465931478580854784 2636611285 2147483648 398796 398406 (ep98 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz296 := (@Enclosure.Real.IsNear.recentre' qz24 Bool.false 524287 1048576 1 1048576 524287 1048576 1 1048576 (ep86 rfl rfl) rfl)

noncomputable def ep100 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz24 (Real.cos qz25)) (@HMul.hMul Real Real Real qz0 qz24 (@Neg.neg Real Real.instNeg (Real.sin qz25))) Bool.true 258863036241 549755813888 39642576160237 109513007393931264 Bool.true 92452245293 549755813888 39579348331225 109513007393931264 (@Enclosure.Real.IsNear.mulLit_ft qz24 (Real.cos qz25) 524287 1048576 1 1048576 493743 524288 9428077 13054967808 258863036241 549755813888 39642576160237 109513007393931264 qz296 (@Enclosure.Real.IsNear.recentre' (Real.cos qz25) Bool.true 987486 1048576 9428077 13054967808 493743 524288 9428077 13054967808 (ep95 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz24 (@Neg.neg Real Real.instNeg (Real.sin qz25)) 524287 1048576 1 1048576 176339 524288 9428077 13054967808 92452245293 549755813888 39579348331225 109513007393931264 qz296 (@Enclosure.Real.IsNear.neg (Real.sin qz25) Bool.false 176339 524288 9428077 13054967808 (@Enclosure.Real.IsNear.recentre' (Real.sin qz25) Bool.false 352678 1048576 9428077 13054967808 176339 524288 9428077 13054967808 (ep99 rfl rfl) rfl)) rfl)

noncomputable def ep101 := @ep47 258863036241 549755813888 39642576160237 109513007393931264 Bool.true 92452245293 549755813888 39579348331225 109513007393931264 Bool.false 552547222050742491676672 1005077541869 1099511627776 282554803599745 219026014787862528 Bool.false 487801743858059330977792 887306203109 1099511627776 282516241883005 219026014787862528 (ep48 (BSN.head_sum_c_succ qz5 3 4 rfl rfl) (ep84 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep85 ep100) rfl rfl

noncomputable abbrev qz549 := (@Nat.cast Real Real.instNatCast 5)

noncomputable abbrev qz27 := (@Inv.inv Real Real.instInv (Real.sqrt qz549))

noncomputable abbrev qz28 := (@HMul.hMul Real Real Real qz267 qz278 (Real.log (Enclosure.sfrac Bool.false 5 1)))

noncomputable def ep102 := @Enclosure.Complex.IsNear.of_eq qz541 (Complex.mk (@HMul.hMul Real Real Real qz0 qz27 (Real.cos qz28)) (@HMul.hMul Real Real Real qz0 qz27 (@Neg.neg Real Real.instNeg (Real.sin qz28)))) Bool.true 491244802027 1099511627776 70854202585115 219026014787862528 Bool.false 10759759465 549755813888 8831833090609 27378251848482816 (BSN.cpow_neg_s_mk qz13 142522 1000 5 qz14 rfl)

noncomputable def ep103 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz549) 2344687 1048576 1 1048576 234468 234469 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz549) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz549 qz15)) Bool.false 2344687 1048576 1 1048576 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz549 qz15)) Bool.false 2344687 1048576 1 1048576 2344687 1048576 1 1048576 (BSN.sqrt_enclosure 5 1 1172343 1172344 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep104 := nat_lit 3696382175741467532940033205863946875

noncomputable def ep105 := nat_lit 765440954430599474856563326857688500

noncomputable def ep106 := nat_lit 108794268166472120024432640000

noncomputable def ep107 := BSN.log_dyadic_bound 2 3 18 17 ep104 524288 199203 ep105 ep106 843808 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.artanhP 2) (BSN.artanhQ 3) 0 17 8 307084260767580 1483365253795425 132843110400 1663129201793174588340 2491889415829100854875 818968088287641600 ep105 ep104 ep106 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.artanhP 2) (BSN.artanhQ 3) 0 8 307084260767580 1483365253795425 132843110400 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.artanhP 2) (BSN.artanhQ 3) 8 17 1663129201793174588340 2491889415829100854875 818968088287641600 rfl rfl rfl rfl)) rfl rfl

noncomputable def ep108 := BSN.cos_dyadic_bound_f 94013320 2147483648 1 0 1048576 398796 0 1 1 0 1 1 1047571 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 94013320) qz281 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 94013320) qz282 0 0 rfl) rfl rfl

noncomputable abbrev qz29 := (Real.log (Enclosure.sfrac Bool.false 5 1))

noncomputable abbrev qz297 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 240522407) qz16)

noncomputable abbrev qz298 := (BSN.isNear_log_sfrac 5 1 843808 524288 1 199203 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 843808 524288 199203 rfl rfl rfl (ep107 rfl rfl)))

noncomputable def ep109 := @Enclosure.Real.IsNear.cos_image qz28 qz297 Bool.false 240522407 1048576 751 1048576 Bool.true 1047571 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz28 Bool.false 1879081309 8192000 71261 99601500 240522407 1048576 751 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz29 142522 1000 0 1 843808 524288 1 199203 1879081309 8192000 71261 99601500 qz18 qz298 rfl) rfl) (Enclosure.sfrac_false_div 240522407 1048576) (BSN.cos_reduce2 qz297 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6615599330964719796224) qz19) 226375608064910080 72057594037927936 Bool.false 1047571 1048576 36 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q2 240522407 1048576 226375608064910080 72057594037927936 36 6615599330964719796224 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1047571 1048576 6615599330964719796224 151115727451828646838272 94013320 2147483648 398796 398406 (ep108 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep110 := BSN.sin_dyadic_bound_f 94013320 2147483648 1 0 1048576 398796 0 1 1 0 1 1 45890 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 94013320) qz285 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 94013320) qz286 0 0 rfl) rfl rfl

noncomputable def ep111 := @Enclosure.Real.IsNear.sin_image qz28 qz297 Bool.false 240522407 1048576 751 1048576 Bool.true 45890 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz28 Bool.false 1879081309 8192000 71261 99601500 240522407 1048576 751 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz29 142522 1000 0 1 843808 524288 1 199203 1879081309 8192000 71261 99601500 qz18 qz298 rfl) rfl) (Enclosure.sfrac_false_div 240522407 1048576) (BSN.sin_reduce2 qz297 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6615599330964719796224) qz19) 226375608064910080 72057594037927936 Bool.false 45890 1048576 36 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q2 240522407 1048576 226375608064910080 72057594037927936 36 6615599330964719796224 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 45890 1048576 6615599330964719796224 151115727451828646838272 94013320 2147483648 398796 398406 (ep110 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz299 := (@Enclosure.Real.IsNear.recentre' qz27 Bool.false 468937 1048576 1 1048576 468937 1048576 1 1048576 (ep103 rfl rfl) rfl)

noncomputable def ep112 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz27 (Real.cos qz28)) (@HMul.hMul Real Real Real qz0 qz27 (@Neg.neg Real Real.instNeg (Real.sin qz28))) Bool.true 491244802027 1099511627776 70854202585115 219026014787862528 Bool.false 10759759465 549755813888 8831833090609 27378251848482816 (@Enclosure.Real.IsNear.mulLit_ft qz27 (Real.cos qz28) 468937 1048576 1 1048576 1047571 1048576 150650029 208879484928 491244802027 1099511627776 70854202585115 219026014787862528 qz299 (@Enclosure.Real.IsNear.recentre' (Real.cos qz28) Bool.true 1047571 1048576 150650029 208879484928 1047571 1048576 150650029 208879484928 (ep109 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz27 (@Neg.neg Real Real.instNeg (Real.sin qz28)) 468937 1048576 1 1048576 22945 524288 150650029 208879484928 10759759465 549755813888 8831833090609 27378251848482816 qz299 (@Enclosure.Real.IsNear.neg (Real.sin qz28) Bool.true 22945 524288 150650029 208879484928 (@Enclosure.Real.IsNear.recentre' (Real.sin qz28) Bool.true 45890 1048576 150650029 208879484928 22945 524288 150650029 208879484928 (ep111 rfl rfl) rfl)) rfl)

noncomputable def ep113 := @ep45 491244802027 1099511627776 70854202585115 219026014787862528 Bool.false 10759759465 549755813888 8831833090609 27378251848482816 Bool.false 564965072188279349051392 256916369921 549755813888 29450750515405 18252167898988544 Bool.false 499632224501899703877632 908825722039 1099511627776 117723635535959 73008671595954176 (ep46 (BSN.head_sum_c_succ qz5 4 5 rfl rfl) (ep101 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep102 ep112) rfl rfl

noncomputable abbrev qz30 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 6)))

noncomputable abbrev qz550 := (Real.log (Enclosure.sfrac Bool.false 6 1))

noncomputable abbrev qz31 := (@HMul.hMul Real Real Real qz267 qz278 qz550)

noncomputable def ep114 := @Enclosure.Complex.IsNear.of_eq qz540 (Complex.mk (@HMul.hMul Real Real Real qz0 qz30 (Real.cos qz31)) (@HMul.hMul Real Real Real qz0 qz30 (@Neg.neg Real Real.instNeg (Real.sin qz31)))) Bool.true 140213423739 549755813888 32310379356983 109513007393931264 Bool.false 175248265257 549755813888 32326682528909 109513007393931264 (BSN.cpow_neg_s_mk qz13 142522 1000 6 qz14 rfl)

noncomputable abbrev qz300 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6) qz15)

noncomputable def ep115 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 6)) 2568477 1048576 1 1048576 214039 214040 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 6)) (Real.sqrt qz300) Bool.false 2568477 1048576 1 1048576 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz300) Bool.false 2568477 1048576 1 1048576 2568477 1048576 1 1048576 (BSN.sqrt_enclosure 6 1 1284238 1284239 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep116 := BSN.log_dyadic_bound 2 10 4 3 105000000 524288 199203 1434560 960 212580 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 2) (BSN.artanhQ 10) 0 3 1434560 105000000 960 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep117 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz550 142522 1000 0 1 4034681531866359 2251799813685248 500000000199203 99601500000000000000 287515440642328608699 1125899906842624000 35630500014195404983 49800750000000000000000 qz18 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 500000000199203 99601500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz300) Bool.false 33845361775666394038272 18889465931478580854784 1000000000398406 199203000000000000000 4034681531866359 2251799813685248 500000000199203 99601500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 212580 524288 24973259072661432 36028797018963968 199203 1000000000000000 rfl rfl rfl rfl (ep116 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep118 := nat_lit 489953985567437721098584822212125798765154274987913250584930284174529093837056

noncomputable def ep119 := nat_lit 187897038158016306098115758916563204721713108103225421696704522610232402176

noncomputable def ep120 := nat_lit 1469486162625997130683558235118544269886019398747533300911397443478366816706816

noncomputable def ep121 := BSN.cos_dyadic_bound_f 1924154726 2147483648 3 2 1048576 398796 ep118 ep57 ep119 ep120 ep60 ep119 655082 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1924154726) qz281 0 2 ep118 ep57 ep119 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1924154726) qz282 0 2 ep120 ep60 ep119 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz32 := (@Nat.cast Real Real.instNatCast 262144)

noncomputable abbrev qz301 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 66942405) qz32)

noncomputable abbrev qz302 := (@Nat.cast Real Real.instNatCast 37778931862957161709568)

noncomputable def ep122 := @Enclosure.Real.IsNear.cos_image qz31 qz301 Bool.false 66942405 262144 751 1048576 Bool.true 655082 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz31 Bool.false 287515440642328608699 1125899906842624000 35630500014195404983 49800750000000000000000 66942405 262144 751 1048576 (ep117 rfl) rfl) (Enclosure.sfrac_false_div 66942405 262144) (BSN.cos_reduce2 qz301 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 33850087933132847185920) qz302) 226375608064910080 72057594037927936 Bool.false 655082 1048576 40 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q2 66942405 262144 226375608064910080 72057594037927936 40 33850087933132847185920 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 655082 1048576 33850087933132847185920 37778931862957161709568 1924154726 2147483648 398796 398406 (ep121 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep123 := nat_lit 881766856390861484932574187374693187213500324491761270715517147896064182984960

noncomputable def ep124 := nat_lit 2309085171533333767470678303324045816561046647684350486905512151453084864880896

noncomputable def ep125 := BSN.sin_dyadic_bound_f 1924154726 2147483648 3 2 1048576 398796 ep123 ep64 ep119 ep124 ep66 ep119 818766 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1924154726) qz285 0 2 ep123 ep64 ep119 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1924154726) qz286 0 2 ep124 ep66 ep119 rfl rfl rfl rfl) rfl rfl

noncomputable def ep126 := @Enclosure.Real.IsNear.sin_image qz31 qz301 Bool.false 66942405 262144 751 1048576 Bool.true 818766 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz31 Bool.false 287515440642328608699 1125899906842624000 35630500014195404983 49800750000000000000000 66942405 262144 751 1048576 (ep117 rfl) rfl) (Enclosure.sfrac_false_div 66942405 262144) (BSN.sin_reduce2 qz301 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 33850087933132847185920) qz302) 226375608064910080 72057594037927936 Bool.false 818766 1048576 40 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q2 66942405 262144 226375608064910080 72057594037927936 40 33850087933132847185920 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 818766 1048576 33850087933132847185920 37778931862957161709568 1924154726 2147483648 398796 398406 (ep125 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz303 := (@Enclosure.Real.IsNear.recentre' qz30 Bool.false 428079 1048576 1 1048576 428079 1048576 1 1048576 (ep115 rfl rfl) rfl)

noncomputable def ep127 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz30 (Real.cos qz31)) (@HMul.hMul Real Real Real qz0 qz30 (@Neg.neg Real Real.instNeg (Real.sin qz31))) Bool.true 140213423739 549755813888 32310379356983 109513007393931264 Bool.false 175248265257 549755813888 32326682528909 109513007393931264 (@Enclosure.Real.IsNear.mulLit_ft qz30 (Real.cos qz31) 428079 1048576 1 1048576 327541 524288 150650029 208879484928 140213423739 549755813888 32310379356983 109513007393931264 qz303 (@Enclosure.Real.IsNear.recentre' (Real.cos qz31) Bool.true 655082 1048576 150650029 208879484928 327541 524288 150650029 208879484928 (ep122 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz30 (@Neg.neg Real Real.instNeg (Real.sin qz31)) 428079 1048576 1 1048576 409383 524288 150650029 208879484928 175248265257 549755813888 32326682528909 109513007393931264 qz303 (@Enclosure.Real.IsNear.neg (Real.sin qz31) Bool.true 409383 524288 150650029 208879484928 (@Enclosure.Real.IsNear.recentre' (Real.sin qz31) Bool.true 818766 1048576 150650029 208879484928 409383 524288 150650029 208879484928 (ep126 rfl rfl) rfl)) rfl)

noncomputable def ep128 := @ep43 140213423739 549755813888 32310379356983 109513007393931264 Bool.false 175248265257 549755813888 32326682528909 109513007393931264 Bool.false 64158123161412872175616 58351473091 274877906944 209014882449413 109513007393931264 Bool.false 692319729899544000856064 1259322252553 1099511627776 417824271665695 219026014787862528 (ep44 (BSN.head_sum_c_succ qz5 5 6 rfl rfl) (ep113 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep114 ep127) rfl rfl

noncomputable abbrev qz33 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 7)))

noncomputable abbrev qz551 := (Real.log (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz34 := (@HMul.hMul Real Real Real qz267 qz278 qz551)

noncomputable def ep129 := @Enclosure.Complex.IsNear.of_eq qz539 (Complex.mk (@HMul.hMul Real Real Real qz0 qz33 (Real.cos qz34)) (@HMul.hMul Real Real Real qz0 qz33 (@Neg.neg Real Real.instNeg (Real.sin qz34)))) Bool.false 266503594025 1099511627776 59840474861165 219026014787862528 Bool.true 159436395275 549755813888 7483349618497 27378251848482816 (BSN.cpow_neg_s_mk qz13 142522 1000 7 qz14 rfl)

noncomputable abbrev qz304 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 7) qz15)

noncomputable def ep130 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 7)) 2774271 1048576 1 1048576 198162 198163 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 7)) (Real.sqrt qz304) Bool.false 2774271 1048576 1 1048576 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz304) Bool.false 2774271 1048576 1 1048576 2774271 1048576 1 1048576 (BSN.sqrt_enclosure 7 1 1387135 1387136 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep131 := BSN.log_dyadic_bound 3 11 5 4 202569142545 524288 199203 5259111624 688905 293399 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 3) (BSN.artanhQ 11) 0 4 5259111624 202569142545 688905 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep132 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz551 142522 1000 0 1 4381796493761783 2251799813685248 500000000199203 99601500000000000000 312251199941958418363 1125899906842624000 35630500014195404983 49800750000000000000000 qz18 (BSN.isNear_log_sfrac 7 1 4381796493761783 2251799813685248 500000000199203 99601500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz304) Bool.false 36757173121942042968064 18889465931478580854784 1000000000398406 199203000000000000000 4381796493761783 2251799813685248 500000000199203 99601500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 293399 524288 24973259072661432 36028797018963968 199203 1000000000000000 rfl rfl rfl rfl (ep131 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep133 := nat_lit 444819428191104272417398918262865290956714820738385999853998690914469111462721

noncomputable def ep134 := nat_lit 154884341971958287072811758743061808933357993146706674994902705763498130241

noncomputable def ep135 := nat_lit 1334148515889368900678051131271109749252277746228864586212006267331880338127681

noncomputable def ep136 := BSN.cos_dyadic_bound_f 1878239369 2147483648 3 2 1048576 398796 ep133 ep57 ep134 ep135 ep60 ep134 672437 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1878239369) qz281 0 2 ep133 ep57 ep134 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1878239369) qz282 0 2 ep135 ep60 ep134 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz305 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 290806591) qz16)

noncomputable def ep137 := @Enclosure.Real.IsNear.cos_image qz34 qz305 Bool.false 290806591 1048576 751 1048576 Bool.false 672437 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz34 Bool.false 312251199941958418363 1125899906842624000 35630500014195404983 49800750000000000000000 290806591 1048576 751 1048576 (ep132 rfl) rfl) (Enclosure.sfrac_false_div 290806591 1048576) (BSN.cos_reduce0 qz305 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 132169345663772783542272) qz19) 226375608064910080 72057594037927936 Bool.false 672437 1048576 44 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q0 290806591 1048576 226375608064910080 72057594037927936 44 132169345663772783542272 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 672437 1048576 132169345663772783542272 151115727451828646838272 1878239369 2147483648 398796 398406 (ep136 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep138 := nat_lit 800551063270410123721659803466163074274939990934577434397201721481433602128705

noncomputable def ep139 := nat_lit 2096430591059310010615753028135319284934188825220703374518869904261089960983361

noncomputable def ep140 := BSN.sin_dyadic_bound_f 1878239369 2147483648 3 2 1048576 398796 ep138 ep64 ep134 ep139 ep66 ep134 804574 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1878239369) qz285 0 2 ep138 ep64 ep134 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1878239369) qz286 0 2 ep139 ep66 ep134 rfl rfl rfl rfl) rfl rfl

noncomputable def ep141 := @Enclosure.Real.IsNear.sin_image qz34 qz305 Bool.false 290806591 1048576 751 1048576 Bool.false 804574 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz34 Bool.false 312251199941958418363 1125899906842624000 35630500014195404983 49800750000000000000000 290806591 1048576 751 1048576 (ep132 rfl) rfl) (Enclosure.sfrac_false_div 290806591 1048576) (BSN.sin_reduce0 qz305 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 132169345663772783542272) qz19) 226375608064910080 72057594037927936 Bool.false 804574 1048576 44 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q0 290806591 1048576 226375608064910080 72057594037927936 44 132169345663772783542272 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 804574 1048576 132169345663772783542272 151115727451828646838272 1878239369 2147483648 398796 398406 (ep140 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz306 := (@Enclosure.Real.IsNear.recentre' qz33 Bool.false 396325 1048576 1 1048576 396325 1048576 1 1048576 (ep130 rfl rfl) rfl)

noncomputable def ep142 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz33 (Real.cos qz34)) (@HMul.hMul Real Real Real qz0 qz33 (@Neg.neg Real Real.instNeg (Real.sin qz34))) Bool.false 266503594025 1099511627776 59840474861165 219026014787862528 Bool.true 159436395275 549755813888 7483349618497 27378251848482816 (@Enclosure.Real.IsNear.mulLit_ff qz33 (Real.cos qz34) 396325 1048576 1 1048576 672437 1048576 150650029 208879484928 266503594025 1099511627776 59840474861165 219026014787862528 qz306 (@Enclosure.Real.IsNear.recentre' (Real.cos qz34) Bool.false 672437 1048576 150650029 208879484928 672437 1048576 150650029 208879484928 (ep137 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz33 (@Neg.neg Real Real.instNeg (Real.sin qz34)) 396325 1048576 1 1048576 402287 524288 150650029 208879484928 159436395275 549755813888 7483349618497 27378251848482816 qz306 (@Enclosure.Real.IsNear.neg (Real.sin qz34) Bool.false 402287 524288 150650029 208879484928 (@Enclosure.Real.IsNear.recentre' (Real.sin qz34) Bool.false 804574 1048576 150650029 208879484928 402287 524288 150650029 208879484928 (ep141 rfl rfl) rfl)) rfl)

noncomputable def ep143 := @ep41 266503594025 1099511627776 59840474861165 219026014787862528 Bool.true 159436395275 549755813888 7483349618497 27378251848482816 Bool.false 137414073280058376585216 499909486389 1099511627776 159290079919997 73008671595954176 Bool.false 517017559403990995697664 940449462003 1099511627776 159230356204557 73008671595954176 (ep42 (BSN.head_sum_c_succ qz5 6 7 rfl rfl) (ep128 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep129 ep142) rfl rfl

noncomputable abbrev qz35 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 8)))

noncomputable abbrev qz552 := (Real.log (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz36 := (@HMul.hMul Real Real Real qz267 qz278 qz552)

noncomputable def ep144 := @Enclosure.Complex.IsNear.of_eq qz538 (Complex.mk (@HMul.hMul Real Real Real qz0 qz35 (Real.cos qz36)) (@HMul.hMul Real Real Real qz0 qz35 (@Neg.neg Real Real.instNeg (Real.sin qz36)))) Bool.false 11952609207 68719476736 2331372667245 9126083949494272 Bool.true 338440014843 1099511627776 18677346054213 73008671595954176 (BSN.cpow_neg_s_mk qz13 142522 1000 8 qz14 rfl)

noncomputable abbrev qz307 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8) qz15)

noncomputable def ep145 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 8)) 2965821 1048576 1 1048576 185363 185364 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 8)) (Real.sqrt qz307) Bool.false 2965821 1048576 1 1048576 (BSN.sqrt_natCast_div_one 8) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz307) Bool.false 2965821 1048576 1 1048576 2965821 1048576 1 1048576 (BSN.sqrt_enclosure 8 1 1482910 1482911 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep146 := BSN.log_dyadic_bound 0 16 1 0 1 524288 199203 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl

noncomputable def ep147 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz552 142522 1000 0 1 9364972152248037 4503599627370496 1000000000597609 199203000000000000000 667357280541347364657 2251799813685248000 71261000042586214949 99601500000000000000000 qz18 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 1000000000597609 199203000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz307) Bool.false 39279540158062550581248 18889465931478580854784 1000000000597609 199203000000000000000 9364972152248037 4503599627370496 1000000000597609 199203000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 524288 24973259072661432 36028797018963968 199203 1000000000000000 rfl rfl rfl rfl (ep146 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep148 := nat_lit 947280167668717419463008979183900240096777120366783498938419120291305375798401

noncomputable def ep149 := nat_lit 701868254496892736086264278312777968095264104835446720219549518093838062721

noncomputable def ep150 := nat_lit 2840436766497158472916854408995075164354140832890679603374818261837728451269761

noncomputable def ep151 := BSN.cos_dyadic_bound_f 2268725487 2147483648 3 2 1048576 398796 ep148 ep57 ep149 ep150 ep60 ep149 515856 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2268725487) qz281 0 2 ep148 ep57 ep149 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2268725487) qz282 0 2 ep150 ep60 ep149 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz37 := (@Nat.cast Real Real.instNatCast 524288)

noncomputable abbrev qz38 := (@Nat.cast Real Real.instNatCast 75557863725914323419136)

noncomputable abbrev qz308 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 155381225) qz37)

noncomputable def ep152 := @Enclosure.Real.IsNear.cos_image qz36 qz308 Bool.false 155381225 524288 751 1048576 Bool.false 515856 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz36 Bool.false 667357280541347364657 2251799813685248000 71261000042586214949 99601500000000000000000 155381225 524288 751 1048576 (ep147 rfl) rfl) (Enclosure.sfrac_false_div 155381225 524288) (BSN.cos_reduce0 qz308 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 79823681718390022471680) qz38) 226375608064910080 72057594037927936 Bool.false 515856 1048576 47 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q0 155381225 524288 226375608064910080 72057594037927936 47 79823681718390022471680 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 515856 1048576 79823681718390022471680 75557863725914323419136 2268725487 2147483648 398796 398406 (ep151 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep153 := nat_lit 1704542807200093840844547151108370209799722605376341940712978776909874605986945

noncomputable def ep154 := nat_lit 4463142422635822233020150491690367956574738300768304835748874668877519658816641

noncomputable def ep155 := BSN.sin_dyadic_bound_f 2268725487 2147483648 3 2 1048576 398796 ep153 ep64 ep149 ep154 ep66 ep149 912909 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2268725487) qz285 0 2 ep153 ep64 ep149 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2268725487) qz286 0 2 ep154 ep66 ep149 rfl rfl rfl rfl) rfl rfl

noncomputable def ep156 := @Enclosure.Real.IsNear.sin_image qz36 qz308 Bool.false 155381225 524288 751 1048576 Bool.false 912909 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz36 Bool.false 667357280541347364657 2251799813685248000 71261000042586214949 99601500000000000000000 155381225 524288 751 1048576 (ep147 rfl) rfl) (Enclosure.sfrac_false_div 155381225 524288) (BSN.sin_reduce0 qz308 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 79823681718390022471680) qz38) 226375608064910080 72057594037927936 Bool.false 912909 1048576 47 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q0 155381225 524288 226375608064910080 72057594037927936 47 79823681718390022471680 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 912909 1048576 79823681718390022471680 75557863725914323419136 2268725487 2147483648 398796 398406 (ep155 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz309 := (@Enclosure.Real.IsNear.recentre' qz35 Bool.false 370727 1048576 1 1048576 370727 1048576 1 1048576 (ep145 rfl rfl) rfl)

noncomputable def ep157 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz35 (Real.cos qz36)) (@HMul.hMul Real Real Real qz0 qz35 (@Neg.neg Real Real.instNeg (Real.sin qz36))) Bool.false 11952609207 68719476736 2331372667245 9126083949494272 Bool.true 338440014843 1099511627776 18677346054213 73008671595954176 (@Enclosure.Real.IsNear.mulLit_ff qz35 (Real.cos qz36) 370727 1048576 1 1048576 32241 65536 150650029 208879484928 11952609207 68719476736 2331372667245 9126083949494272 qz309 (@Enclosure.Real.IsNear.recentre' (Real.cos qz36) Bool.false 515856 1048576 150650029 208879484928 32241 65536 150650029 208879484928 (ep152 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz35 (@Neg.neg Real Real.instNeg (Real.sin qz36)) 370727 1048576 1 1048576 912909 1048576 150650029 208879484928 338440014843 1099511627776 18677346054213 73008671595954176 qz309 (@Enclosure.Real.IsNear.neg (Real.sin qz36) Bool.false 912909 1048576 150650029 208879484928 (@Enclosure.Real.IsNear.recentre' (Real.sin qz36) Bool.false 912909 1048576 150650029 208879484928 912909 1048576 150650029 208879484928 (ep156 rfl rfl) rfl)) rfl)

noncomputable def ep158 := @ep39 11952609207 68719476736 2331372667245 9126083949494272 Bool.true 338440014843 1099511627776 18677346054213 73008671595954176 Bool.false 47495551125373568679936 691151233701 1099511627776 177941061257957 73008671595954176 Bool.false 661916387183421460316160 75251180895 137438953472 88953851129385 36504335797977088 (ep40 (BSN.head_sum_c_succ qz5 7 8 rfl rfl) (ep143 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep144 ep157) rfl rfl

theorem EMRow50.d6 : Enclosure.Complex.IsNear qz3 Bool.false 691151233701 1099511627776 177941061257957 73008671595954176 Bool.false 75251180895 137438953472 88953851129385 36504335797977088 := ep38 (BSN.head_sum_c_succ qz5 8 9 rfl rfl) (ep158 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz39 := (BSN.headSumC qz271 17)

noncomputable abbrev qz310 := (@Nat.cast Complex Complex.instNatCast 16)

noncomputable def ep159 := @Enclosure.Complex.IsNear.of_eq qz39 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 16) (@HPow.hPow Complex Complex Complex qz6 qz310 qz7)) Bool.false 739981744471 1099511627776 897219928520003 219026014787862528 Bool.false 58066758319 549755813888 448677170670931 109513007393931264

noncomputable def ep160 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 16) (@HPow.hPow Complex Complex Complex qz6 qz310 qz7) Bool.false 527248505683 1099511627776 857514051024847 219026014787862528 Bool.true 57940707511 1099511627776 857677840910725 219026014787862528 Bool.false

noncomputable abbrev qz311 := (@Nat.cast Complex Complex.instNatCast 15)

noncomputable def ep161 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 16) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 15) (@HPow.hPow Complex Complex Complex qz6 qz311 qz7)) Bool.false 527248505683 1099511627776 857514051024847 219026014787862528 Bool.true 57940707511 1099511627776 857677840910725 219026014787862528

noncomputable def ep162 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 15) (@HPow.hPow Complex Complex Complex qz6 qz311 qz7) Bool.false 390851269673 549755813888 34022480888675 9126083949494272 Bool.false 8493521491 137438953472 136132987591245 36504335797977088 Bool.true

noncomputable abbrev qz312 := (@Nat.cast Complex Complex.instNatCast 14)

noncomputable def ep163 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 15) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 14) (@HPow.hPow Complex Complex Complex qz6 qz312 qz7)) Bool.false 390851269673 549755813888 34022480888675 9126083949494272 Bool.false 8493521491 137438953472 136132987591245 36504335797977088

noncomputable def ep164 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 14) (@HPow.hPow Complex Complex Complex qz6 qz312 qz7) Bool.false 591682371981 1099511627776 774129878565427 219026014787862528 Bool.true 156202790407 1099511627776 774364001851327 219026014787862528 Bool.false

noncomputable abbrev qz313 := (@Nat.cast Complex Complex.instNatCast 13)

noncomputable def ep165 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 14) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 13) (@HPow.hPow Complex Complex Complex qz6 qz313 qz7)) Bool.false 591682371981 1099511627776 774129878565427 219026014787862528 Bool.true 156202790407 1099511627776 774364001851327 219026014787862528

noncomputable def ep166 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 13) (@HPow.hPow Complex Complex Complex qz6 qz313 qz7) Bool.false 463427102397 1099511627776 243409794804969 73008671595954176 Bool.false 60232490857 549755813888 121726975104175 36504335797977088 Bool.false

noncomputable abbrev qz314 := (@Nat.cast Complex Complex.instNatCast 12)

noncomputable def ep167 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 13) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 12) (@HPow.hPow Complex Complex Complex qz6 qz314 qz7)) Bool.false 463427102397 1099511627776 243409794804969 73008671595954176 Bool.false 60232490857 549755813888 121726975104175 36504335797977088

noncomputable def ep168 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 12) (@HPow.hPow Complex Complex Complex qz6 qz314 qz7) Bool.false 673801517397 1099511627776 684429177501971 219026014787862528 Bool.false 358132071719 1099511627776 684543682573619 219026014787862528 Bool.true

noncomputable abbrev qz315 := (@Nat.cast Complex Complex.instNatCast 11)

noncomputable def ep169 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 12) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 11) (@HPow.hPow Complex Complex Complex qz6 qz315 qz7)) Bool.false 673801517397 1099511627776 684429177501971 219026014787862528 Bool.false 358132071719 1099511627776 684543682573619 219026014787862528

noncomputable def ep170 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 11) (@HPow.hPow Complex Complex Complex qz6 qz315 qz7) Bool.false 931391065461 1099511627776 636637664590733 219026014787862528 Bool.false 566817190395 1099511627776 636782983179233 219026014787862528 Bool.true

noncomputable abbrev qz316 := (@Nat.cast Complex Complex.instNatCast 10)

noncomputable def ep171 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 11) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 10) (@HPow.hPow Complex Complex Complex qz6 qz316 qz7)) Bool.false 931391065461 1099511627776 636637664590733 219026014787862528 Bool.false 566817190395 1099511627776 636782983179233 219026014787862528

noncomputable def ep172 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 10) (@HPow.hPow Complex Complex Complex qz6 qz316 qz7) Bool.false 221792174619 274877906944 293295500521879 109513007393931264 Bool.false 911689645735 1099511627776 586555703268173 219026014787862528 Bool.false

noncomputable abbrev qz553 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 9) qz7)

noncomputable def ep173 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 10) (@HAdd.hAdd Complex Complex Complex qz4 qz3 qz553) Bool.false 221792174619 274877906944 293295500521879 109513007393931264 Bool.false 911689645735 1099511627776 586555703268173 219026014787862528

noncomputable def ep174 := @Enclosure.Complex.IsNear.addLitP qz3 qz553 Bool.false 691151233701 1099511627776 177941061257957 73008671595954176 Bool.false 75251180895 137438953472 88953851129385 36504335797977088 Bool.false

noncomputable abbrev qz40 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 9)))

noncomputable abbrev qz554 := (Real.log (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz41 := (@HMul.hMul Real Real Real qz267 qz278 qz554)

noncomputable def ep175 := @Enclosure.Complex.IsNear.of_eq qz553 (Complex.mk (@HMul.hMul Real Real Real qz0 qz40 (Real.cos qz41)) (@HMul.hMul Real Real Real qz0 qz40 (@Neg.neg Real Real.instNeg (Real.sin qz41)))) Bool.false 196017464775 1099511627776 52767817269887 219026014787862528 Bool.false 309680198575 1099511627776 52832596491863 219026014787862528 (BSN.cpow_neg_s_mk qz13 142522 1000 9 qz14 rfl)

noncomputable abbrev qz317 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9) qz15)

noncomputable def ep176 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 9)) 3145729 1048576 1 1048576 174762 174763 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 9)) (Real.sqrt qz317) Bool.false 3145729 1048576 1 1048576 (BSN.sqrt_natCast_div_one 9) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz317) Bool.false 3145729 1048576 1 1048576 3145729 1048576 1 1048576 (BSN.sqrt_enclosure 9 1 1572864 1572865 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep177 := BSN.log_dyadic_bound 1 17 3 2 1252815 524288 199203 1448 3 61752 18 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 1) (BSN.artanhQ 17) 0 2 1448 1252815 3 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep178 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz554 142522 1000 0 1 9895417793173221 4503599627370496 1000000000597609 199203000000000000000 705157367359316901681 2251799813685248000 71261000042586214949 99601500000000000000000 qz18 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 1000000000597609 199203000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz317) Bool.false 41504390431577613533184 18889465931478580854784 1000000000597609 199203000000000000000 9895417793173221 4503599627370496 1000000000597609 199203000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 61752 524288 24973259072661432 36028797018963968 199203 1000000000000000 rfl rfl rfl rfl (ep177 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep179 := nat_lit 2156682726563649578431929924798386176

noncomputable def ep180 := nat_lit 2552117751907038475975309555738261585920

noncomputable def ep181 := nat_lit 17864824263349269331827166890167831101440

noncomputable def ep182 := BSN.sin_dyadic_bound_f 1211843576 2147483648 2 1 1048576 398796 ep179 ep180 ep179 ep179 ep181 ep179 560811 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1211843576) qz285 0 1 ep179 ep180 ep179 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1211843576) qz286 0 1 ep179 ep181 ep179 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz318 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 328364487) qz16)

noncomputable def ep183 := @Enclosure.Real.IsNear.cos_image qz41 qz318 Bool.false 328364487 1048576 751 1048576 Bool.false 560811 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz41 Bool.false 705157367359316901681 2251799813685248000 71261000042586214949 99601500000000000000000 328364487 1048576 751 1048576 (ep178 rfl) rfl) (Enclosure.sfrac_false_div 328364487 1048576) (BSN.cos_reduce3 qz318 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 85275910584971238047744) qz19) 226375608064910080 72057594037927936 Bool.false 560811 1048576 49 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q3 328364487 1048576 226375608064910080 72057594037927936 49 85275910584971238047744 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 560811 1048576 85275910584971238047744 151115727451828646838272 1211843576 2147483648 398796 398406 (ep182 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep184 := nat_lit 510423550381407695195061911147652317184

noncomputable def ep185 := nat_lit 7656353255721115427925928667214784757760

noncomputable def ep186 := BSN.cos_dyadic_bound_f 1211843576 2147483648 2 1 1048576 398796 ep179 ep184 ep179 ep179 ep185 ep179 886003 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1211843576) qz281 0 1 ep179 ep184 ep179 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1211843576) qz282 0 1 ep179 ep185 ep179 rfl rfl rfl rfl) rfl rfl

noncomputable def ep187 := @Enclosure.Real.IsNear.sin_image qz41 qz318 Bool.false 328364487 1048576 751 1048576 Bool.true 886003 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz41 Bool.false 705157367359316901681 2251799813685248000 71261000042586214949 99601500000000000000000 328364487 1048576 751 1048576 (ep178 rfl) rfl) (Enclosure.sfrac_false_div 328364487 1048576) (BSN.sin_reduce3 qz318 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 85275910584971238047744) qz19) 226375608064910080 72057594037927936 Bool.false 886003 1048576 49 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q3 328364487 1048576 226375608064910080 72057594037927936 49 85275910584971238047744 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 886003 1048576 85275910584971238047744 151115727451828646838272 1211843576 2147483648 398796 398406 (ep186 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz319 := (@Enclosure.Real.IsNear.recentre' qz40 Bool.false 349525 1048576 1 1048576 349525 1048576 1 1048576 (ep176 rfl rfl) rfl)

noncomputable def ep188 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz40 (Real.cos qz41)) (@HMul.hMul Real Real Real qz0 qz40 (@Neg.neg Real Real.instNeg (Real.sin qz41))) Bool.false 196017464775 1099511627776 52767817269887 219026014787862528 Bool.false 309680198575 1099511627776 52832596491863 219026014787862528 (@Enclosure.Real.IsNear.mulLit_ff qz40 (Real.cos qz41) 349525 1048576 1 1048576 560811 1048576 150650029 208879484928 196017464775 1099511627776 52767817269887 219026014787862528 qz319 (@Enclosure.Real.IsNear.recentre' (Real.cos qz41) Bool.false 560811 1048576 150650029 208879484928 560811 1048576 150650029 208879484928 (ep183 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz40 (@Neg.neg Real Real.instNeg (Real.sin qz41)) 349525 1048576 1 1048576 886003 1048576 150650029 208879484928 309680198575 1099511627776 52832596491863 219026014787862528 qz319 (@Enclosure.Real.IsNear.neg (Real.sin qz41) Bool.true 886003 1048576 150650029 208879484928 (@Enclosure.Real.IsNear.recentre' (Real.sin qz41) Bool.true 886003 1048576 150650029 208879484928 886003 1048576 150650029 208879484928 (ep187 rfl rfl) rfl)) rfl)

noncomputable def ep189 := @ep174 196017464775 1099511627776 52767817269887 219026014787862528 Bool.false 309680198575 1099511627776 52832596491863 219026014787862528 Bool.false 975452299773262090469376 221792174619 274877906944 293295500521879 109513007393931264 Bool.false 125301670801076828241920 911689645735 1099511627776 586555703268173 219026014787862528 EMRow50.d6 (ep175 ep188) rfl rfl

noncomputable abbrev qz320 := (@Nat.cast Real Real.instNatCast 10)

noncomputable abbrev qz42 := (@Inv.inv Real Real.instInv (Real.sqrt qz320))

noncomputable abbrev qz555 := (Real.log (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz43 := (@HMul.hMul Real Real Real qz267 qz278 qz555)

noncomputable def ep190 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz316 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz42 (Real.cos qz43)) (@HMul.hMul Real Real Real qz0 qz42 (@Neg.neg Real Real.instNeg (Real.sin qz43)))) Bool.false 44222366985 1099511627776 16682221182325 73008671595954176 Bool.true 86218113835 274877906944 4185606659255 18252167898988544 (BSN.cpow_neg_s_mk qz13 142522 1000 10 qz14 rfl)

noncomputable abbrev qz321 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 10) qz15)

noncomputable def ep191 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz320) 3315889 1048576 1 1048576 165794 165795 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz320) (Real.sqrt qz321) Bool.false 3315889 1048576 1 1048576 (BSN.sqrt_natCast_div_one 10) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz321) Bool.false 3315889 1048576 1 1048576 3315889 1048576 1 1048576 (BSN.sqrt_enclosure 10 1 1657944 1657945 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep192 := BSN.log_dyadic_bound 2 18 3 2 1574640 524288 199203 6528 48 116991 20 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 2) (BSN.artanhQ 18) 0 2 6528 1574640 48 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep193 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz555 142522 1000 0 1 10369917190100709 4503599627370496 1000000000597609 199203000000000000000 738970668883766624049 2251799813685248000 71261000042586214949 99601500000000000000000 qz18 (BSN.isNear_log_sfrac 10 1 10369917190100709 4503599627370496 1000000000597609 199203000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz321) Bool.false 43494585150108164161536 18889465931478580854784 1000000000597609 199203000000000000000 10369917190100709 4503599627370496 1000000000597609 199203000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 116991 524288 24973259072661432 36028797018963968 199203 1000000000000000 rfl rfl rfl rfl (ep192 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep194 := nat_lit 3305605330638169138815708212949770027611922311802176262451357188585088000000000

noncomputable def ep195 := nat_lit 8515381365515156035067222900583220591492167923901784175792010000000000000000

noncomputable def ep196 := nat_lit 9899785229183477104376990193048143641652782599558725219002487545755264000000000

noncomputable def ep197 := BSN.cos_dyadic_bound_f 3099384900 2147483648 3 2 1048576 398796 ep194 ep57 ep195 ep196 ep60 ep195 133365 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3099384900) qz281 0 2 ep194 ep57 ep195 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3099384900) qz282 0 2 ep196 ep60 ep195 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz322 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 21506877) (@Nat.cast Real Real.instNatCast 65536))

noncomputable abbrev qz556 := (@Nat.cast Real Real.instNatCast 9444732965739290427392)

noncomputable def ep198 := @Enclosure.Real.IsNear.cos_image qz43 qz322 Bool.false 21506877 65536 47 65536 Bool.false 133365 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz43 Bool.false 738970668883766624049 2251799813685248000 71261000042586214949 99601500000000000000000 21506877 65536 47 65536 (ep193 rfl) rfl) (Enclosure.sfrac_false_div 21506877 65536) (BSN.cos_reduce0 qz322 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13631238949773932232704) qz556) 226375608064910080 72057594037927936 Bool.false 133365 1048576 52 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q0 21506877 65536 226375608064910080 72057594037927936 52 13631238949773932232704 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 133365 1048576 13631238949773932232704 9444732965739290427392 3099384900 2147483648 398796 398406 (ep197 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep199 := nat_lit 5943277290056292325040221004989119473228266426904795845071809331453158400000000

noncomputable def ep200 := nat_lit 15551939427936598217715231890275321025116377131921481467474884994758272000000000

noncomputable def ep201 := BSN.sin_dyadic_bound_f 3099384900 2147483648 3 2 1048576 398796 ep199 ep64 ep195 ep200 ep66 ep195 1040060 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3099384900) qz285 0 2 ep199 ep64 ep195 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3099384900) qz286 0 2 ep200 ep66 ep195 rfl rfl rfl rfl) rfl rfl

noncomputable def ep202 := @Enclosure.Real.IsNear.sin_image qz43 qz322 Bool.false 21506877 65536 47 65536 Bool.false 1040060 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz43 Bool.false 738970668883766624049 2251799813685248000 71261000042586214949 99601500000000000000000 21506877 65536 47 65536 (ep193 rfl) rfl) (Enclosure.sfrac_false_div 21506877 65536) (BSN.sin_reduce0 qz322 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13631238949773932232704) qz556) 226375608064910080 72057594037927936 Bool.false 1040060 1048576 52 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q0 21506877 65536 226375608064910080 72057594037927936 52 13631238949773932232704 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1040060 1048576 13631238949773932232704 9444732965739290427392 3099384900 2147483648 398796 398406 (ep201 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz323 := (@Enclosure.Real.IsNear.recentre' qz42 Bool.false 331589 1048576 1 1048576 331589 1048576 1 1048576 (ep191 rfl rfl) rfl)

noncomputable def ep203 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz42 (Real.cos qz43)) (@HMul.hMul Real Real Real qz0 qz42 (@Neg.neg Real Real.instNeg (Real.sin qz43))) Bool.false 44222366985 1099511627776 16682221182325 73008671595954176 Bool.true 86218113835 274877906944 4185606659255 18252167898988544 (@Enclosure.Real.IsNear.mulLit_ff qz42 (Real.cos qz43) 331589 1048576 1 1048576 133365 1048576 9428077 13054967808 44222366985 1099511627776 16682221182325 73008671595954176 qz323 (@Enclosure.Real.IsNear.recentre' (Real.cos qz43) Bool.false 133365 1048576 9428077 13054967808 133365 1048576 9428077 13054967808 (ep198 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz42 (@Neg.neg Real Real.instNeg (Real.sin qz43)) 331589 1048576 1 1048576 260015 262144 9428077 13054967808 86218113835 274877906944 4185606659255 18252167898988544 qz323 (@Enclosure.Real.IsNear.neg (Real.sin qz43) Bool.false 260015 262144 9428077 13054967808 (@Enclosure.Real.IsNear.recentre' (Real.sin qz43) Bool.false 1040060 1048576 9428077 13054967808 260015 262144 9428077 13054967808 (ep202 rfl rfl) rfl)) rfl)

noncomputable def ep204 := @ep172 44222366985 1099511627776 16682221182325 73008671595954176 Bool.true 86218113835 274877906944 4185606659255 18252167898988544 Bool.false 256018826620261770461184 931391065461 1099511627776 636637664590733 219026014787862528 Bool.false 155805522915656340602880 566817190395 1099511627776 636782983179233 219026014787862528 (ep173 (BSN.head_sum_c_succ qz5 9 10 rfl rfl) (ep189 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep190 ep203) rfl rfl

noncomputable abbrev qz324 := (@Nat.cast Real Real.instNatCast 11)

noncomputable abbrev qz44 := (@Inv.inv Real Real.instInv (Real.sqrt qz324))

noncomputable abbrev qz557 := (Real.log (Enclosure.sfrac Bool.false 11 1))

noncomputable abbrev qz45 := (@HMul.hMul Real Real Real qz267 qz278 qz557)

noncomputable def ep205 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz315 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz44 (Real.cos qz45)) (@HMul.hMul Real Real Real qz0 qz44 (@Neg.neg Real Real.instNeg (Real.sin qz45)))) Bool.true 8049673377 34359738368 346315310951 1587145034694656 Bool.true 52171279669 274877906944 346092024597 1587145034694656 (BSN.cpow_neg_s_mk qz13 142522 1000 11 qz14 rfl)

noncomputable abbrev qz325 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11) qz15)

noncomputable def ep206 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz324) 3477733 1048576 1 1048576 158078 158079 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz324) (Real.sqrt qz325) Bool.false 3477733 1048576 1 1048576 (BSN.sqrt_natCast_div_one 11) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz325) Bool.false 3477733 1048576 1 1048576 3477733 1048576 1 1048576 (BSN.sqrt_enclosure 11 1 1738866 1738867 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep207 := BSN.log_dyadic_bound 3 19 4 3 4939817505 524288 199203 41676111 10935 166961 22 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 3) (BSN.artanhQ 19) 0 3 41676111 4939817505 10935 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep208 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz557 142522 1000 0 1 10799156221662949 4503599627370496 1000000000597609 199203000000000000000 769558671511923408689 2251799813685248000 71261000042586214949 99601500000000000000000 qz18 (BSN.isNear_log_sfrac 11 1 10799156221662949 4503599627370496 1000000000597609 199203000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz325) Bool.false 45294944137145793642496 18889465931478580854784 1000000000597609 199203000000000000000 10799156221662949 4503599627370496 1000000000597609 199203000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 166961 524288 24973259072661432 36028797018963968 199203 1000000000000000 rfl rfl rfl rfl (ep207 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep209 := nat_lit 857972445836543086238109130515993249283319811690156664410405129206582920216705

noncomputable def ep210 := nat_lit 177895133476545972556001183269240456767731963939286884674924392370676826241

noncomputable def ep211 := nat_lit 2246782670784365103810909435149927358812023178865937180404444508429593219039361

noncomputable def ep212 := BSN.sin_dyadic_bound_f 1911043217 2147483648 3 2 1048576 398796 ep209 ep64 ep210 ep211 ep66 ep210 814752 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1911043217) qz285 0 2 ep209 ep64 ep210 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1911043217) qz286 0 2 ep211 ep66 ep210 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz326 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 358353681) qz16)

noncomputable def ep213 := @Enclosure.Real.IsNear.cos_image qz45 qz326 Bool.false 358353681 1048576 751 1048576 Bool.true 814752 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz45 Bool.false 769558671511923408689 2251799813685248000 71261000042586214949 99601500000000000000000 358353681 1048576 751 1048576 (ep208 rfl) rfl) (Enclosure.sfrac_false_div 358353681 1048576) (BSN.cos_reduce1 qz326 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 134477711297418962665472) qz19) 226375608064910080 72057594037927936 Bool.false 814752 1048576 54 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q1 358353681 1048576 226375608064910080 72057594037927936 54 134477711297418962665472 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 814752 1048576 134477711297418962665472 151115727451828646838272 1911043217 2147483648 398796 398406 (ep212 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep214 := nat_lit 476730423301846846120085517479227023138185554034060052176747260400266367598721

noncomputable def ep215 := nat_lit 1429835479638587446415144550071142588501021198174301582760891932416057749143681

noncomputable def ep216 := BSN.cos_dyadic_bound_f 1911043217 2147483648 3 2 1048576 398796 ep214 ep57 ep210 ep215 ep60 ep210 660068 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1911043217) qz281 0 2 ep214 ep57 ep210 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1911043217) qz282 0 2 ep215 ep60 ep210 rfl rfl rfl rfl) rfl rfl

noncomputable def ep217 := @Enclosure.Real.IsNear.sin_image qz45 qz326 Bool.false 358353681 1048576 751 1048576 Bool.false 660068 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz45 Bool.false 769558671511923408689 2251799813685248000 71261000042586214949 99601500000000000000000 358353681 1048576 751 1048576 (ep208 rfl) rfl) (Enclosure.sfrac_false_div 358353681 1048576) (BSN.sin_reduce1 qz326 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 134477711297418962665472) qz19) 226375608064910080 72057594037927936 Bool.false 660068 1048576 54 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q1 358353681 1048576 226375608064910080 72057594037927936 54 134477711297418962665472 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 660068 1048576 134477711297418962665472 151115727451828646838272 1911043217 2147483648 398796 398406 (ep216 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz327 := (@Enclosure.Real.IsNear.recentre' qz44 Bool.false 316157 1048576 1 1048576 316157 1048576 1 1048576 (ep206 rfl rfl) rfl)

noncomputable def ep218 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz44 (Real.cos qz45)) (@HMul.hMul Real Real Real qz0 qz44 (@Neg.neg Real Real.instNeg (Real.sin qz45))) Bool.true 8049673377 34359738368 346315310951 1587145034694656 Bool.true 52171279669 274877906944 346092024597 1587145034694656 (@Enclosure.Real.IsNear.mulLit_ft qz44 (Real.cos qz45) 316157 1048576 1 1048576 25461 32768 150650029 208879484928 8049673377 34359738368 346315310951 1587145034694656 qz327 (@Enclosure.Real.IsNear.recentre' (Real.cos qz45) Bool.true 814752 1048576 150650029 208879484928 25461 32768 150650029 208879484928 (ep213 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz44 (@Neg.neg Real Real.instNeg (Real.sin qz45)) 316157 1048576 1 1048576 165017 262144 150650029 208879484928 52171279669 274877906944 346092024597 1587145034694656 qz327 (@Enclosure.Real.IsNear.neg (Real.sin qz45) Bool.false 165017 262144 150650029 208879484928 (@Enclosure.Real.IsNear.recentre' (Real.sin qz45) Bool.false 660068 1048576 150650029 208879484928 165017 262144 150650029 208879484928 (ep217 rfl rfl) rfl)) rfl)

noncomputable def ep219 := @ep170 8049673377 34359738368 346315310951 1587145034694656 Bool.true 52171279669 274877906944 346092024597 1587145034694656 Bool.false 23151643849722320388096 673801517397 1099511627776 684429177501971 219026014787862528 Bool.false 98442594283637216116736 358132071719 1099511627776 684543682573619 219026014787862528 (ep171 (BSN.head_sum_c_succ qz5 10 11 rfl rfl) (ep204 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep205 ep218) rfl rfl

noncomputable abbrev qz328 := (@Nat.cast Real Real.instNatCast 12)

noncomputable abbrev qz46 := (@Inv.inv Real Real.instInv (Real.sqrt qz328))

noncomputable abbrev qz558 := (Real.log (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz47 := (@HMul.hMul Real Real Real qz267 qz278 qz558)

noncomputable def ep220 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz314 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz46 (Real.cos qz47)) (@HMul.hMul Real Real Real qz0 qz46 (@Neg.neg Real Real.instNeg (Real.sin qz47)))) Bool.true 26296801875 137438953472 5725025864117 27378251848482816 Bool.true 237667090005 1099511627776 45818168051431 219026014787862528 (BSN.cpow_neg_s_mk qz13 142522 1000 12 qz14 rfl)

noncomputable abbrev qz329 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 12) qz15)

noncomputable def ep221 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz328) 3632373 1048576 1 1048576 151348 151349 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz328) (Real.sqrt qz329) Bool.false 3632373 1048576 1 1048576 (BSN.sqrt_natCast_div_one 12) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz329) Bool.false 3632373 1048576 1 1048576 3632373 1048576 1 1048576 (BSN.sqrt_enclosure 12 1 1816186 1816187 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep222 := BSN.log_dyadic_bound 4 20 4 3 6720000000 524288 199203 91811840 61440 212580 24 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 4) (BSN.artanhQ 20) 0 3 91811840 6720000000 61440 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep223 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz558 142522 1000 0 1 11191020447815397 4503599627370496 1000000000597609 199203000000000000000 797483308131773005617 2251799813685248000 71261000042586214949 99601500000000000000000 qz18 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 1000000000597609 199203000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz329) Bool.false 46938541828353910898688 18889465931478580854784 1000000000597609 199203000000000000000 11191020447815397 4503599627370496 1000000000597609 199203000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 212580 524288 24973259072661432 36028797018963968 199203 1000000000000000 rfl rfl rfl rfl (ep222 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep224 := nat_lit 5861538843633287481329294482882953216

noncomputable def ep225 := BSN.sin_dyadic_bound_f 1555976064 2147483648 2 1 1048576 398796 ep224 ep180 ep224 ep224 ep181 ep224 695000 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1555976064) qz285 0 1 ep224 ep180 ep224 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1555976064) qz286 0 1 ep224 ep181 ep224 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz330 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 371357103) qz16)

noncomputable def ep226 := @Enclosure.Real.IsNear.cos_image qz47 qz330 Bool.false 371357103 1048576 47 65536 Bool.true 695000 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz47 Bool.false 797483308131773005617 2251799813685248000 71261000042586214949 99601500000000000000000 371357103 1048576 47 65536 (ep223 rfl) rfl) (Enclosure.sfrac_false_div 371357103 1048576) (BSN.cos_reduce1 qz330 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 109492081638971661090816) qz19) 226375608064910080 72057594037927936 Bool.false 695000 1048576 56 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q1 371357103 1048576 226375608064910080 72057594037927936 56 109492081638971661090816 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 695000 1048576 109492081638971661090816 151115727451828646838272 1555976064 2147483648 398796 398406 (ep225 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep227 := nat_lit 209465080346223767909591640357404555866697732222745916269549724524288185204736

noncomputable def ep228 := nat_lit 34357637615421856990595646804416459304524259152460129360565514605644742656

noncomputable def ep229 := nat_lit 628326525763440460014793729778604834681484148149932828549928042543653266128896

noncomputable def ep230 := BSN.cos_dyadic_bound_f 1555976064 2147483648 3 2 1048576 398796 ep227 ep57 ep228 ep229 ep60 ep228 785165 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1555976064) qz281 0 2 ep227 ep57 ep228 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1555976064) qz282 0 2 ep229 ep60 ep228 rfl rfl rfl rfl) rfl rfl

noncomputable def ep231 := @Enclosure.Real.IsNear.sin_image qz47 qz330 Bool.false 371357103 1048576 47 65536 Bool.false 785165 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz47 Bool.false 797483308131773005617 2251799813685248000 71261000042586214949 99601500000000000000000 371357103 1048576 47 65536 (ep223 rfl) rfl) (Enclosure.sfrac_false_div 371357103 1048576) (BSN.sin_reduce1 qz330 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 109492081638971661090816) qz19) 226375608064910080 72057594037927936 Bool.false 785165 1048576 56 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q1 371357103 1048576 226375608064910080 72057594037927936 56 109492081638971661090816 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 785165 1048576 109492081638971661090816 151115727451828646838272 1555976064 2147483648 398796 398406 (ep230 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz331 := (@Enclosure.Real.IsNear.recentre' qz46 Bool.false 302697 1048576 1 1048576 302697 1048576 1 1048576 (ep221 rfl rfl) rfl)

noncomputable def ep232 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz46 (Real.cos qz47)) (@HMul.hMul Real Real Real qz0 qz46 (@Neg.neg Real Real.instNeg (Real.sin qz47))) Bool.true 26296801875 137438953472 5725025864117 27378251848482816 Bool.true 237667090005 1099511627776 45818168051431 219026014787862528 (@Enclosure.Real.IsNear.mulLit_ft qz46 (Real.cos qz47) 302697 1048576 1 1048576 86875 131072 9428077 13054967808 26296801875 137438953472 5725025864117 27378251848482816 qz331 (@Enclosure.Real.IsNear.recentre' (Real.cos qz47) Bool.true 695000 1048576 9428077 13054967808 86875 131072 9428077 13054967808 (ep226 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz46 (@Neg.neg Real Real.instNeg (Real.sin qz47)) 302697 1048576 1 1048576 785165 1048576 9428077 13054967808 237667090005 1099511627776 45818168051431 219026014787862528 qz331 (@Enclosure.Real.IsNear.neg (Real.sin qz47) Bool.false 785165 1048576 9428077 13054967808 (@Enclosure.Real.IsNear.recentre' (Real.sin qz47) Bool.false 785165 1048576 9428077 13054967808 785165 1048576 9428077 13054967808 (ep231 rfl rfl) rfl)) rfl)

noncomputable def ep233 := @ep168 26296801875 137438953472 5725025864117 27378251848482816 Bool.true 237667090005 1099511627776 45818168051431 219026014787862528 Bool.false 63692935964005062672384 463427102397 1099511627776 243409794804969 73008671595954176 Bool.false 132452648134366214488064 60232490857 549755813888 121726975104175 36504335797977088 (ep169 (BSN.head_sum_c_succ qz5 11 12 rfl rfl) (ep219 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep220 ep232) rfl rfl

noncomputable abbrev qz332 := (@Nat.cast Real Real.instNatCast 13)

noncomputable abbrev qz48 := (@Inv.inv Real Real.instInv (Real.sqrt qz332))

noncomputable abbrev qz559 := (Real.log (Enclosure.sfrac Bool.false 13 1))

noncomputable abbrev qz49 := (@HMul.hMul Real Real Real qz267 qz278 qz559)

noncomputable def ep234 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz313 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz48 (Real.cos qz49)) (@HMul.hMul Real Real Real qz0 qz48 (@Neg.neg Real Real.instNeg (Real.sin qz49)))) Bool.false 8015954349 68719476736 5487561768815 27378251848482816 Bool.true 276667772121 1099511627776 44002151226277 219026014787862528 (BSN.cpow_neg_s_mk qz13 142522 1000 13 qz14 rfl)

noncomputable abbrev qz333 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13) qz15)

noncomputable def ep235 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz332) 3780695 1048576 1 1048576 145411 145412 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz332) (Real.sqrt qz333) Bool.false 3780695 1048576 1 1048576 (BSN.sqrt_natCast_div_one 13) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz333) Bool.false 3780695 1048576 1 1048576 3780695 1048576 1 1048576 (BSN.sqrt_enclosure 13 1 1890347 1890348 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep236 := BSN.log_dyadic_bound 5 21 5 4 35742602096145 524288 199203 699352521000 41015625 254545 26 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 5) (BSN.artanhQ 21) 0 4 699352521000 35742602096145 41015625 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep237 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz559 142522 1000 0 1 11551497052968677 4503599627370496 1000000000597609 199203000000000000000 823171231491600891697 2251799813685248000 71261000042586214949 99601500000000000000000 qz18 (BSN.isNear_log_sfrac 13 1 11551497052968677 4503599627370496 1000000000597609 199203000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz333) Bool.false 48450490295254733815808 18889465931478580854784 1000000000597609 199203000000000000000 11551497052968677 4503599627370496 1000000000597609 199203000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 254545 524288 24973259072661432 36028797018963968 199203 1000000000000000 rfl rfl rfl rfl (ep236 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep238 := nat_lit 1269941930985466669236071804269738278250014786168634635784989837982315725571201

noncomputable def ep239 := nat_lit 1260803688597284026030079739410146013190816353137923072268785057609769403521

noncomputable def ep240 := nat_lit 3807304185579205439656155253330394542723662725799628061210431943831727637906561

noncomputable def ep241 := BSN.cos_dyadic_bound_f 2441073937 2147483648 3 2 1048576 398796 ep238 ep57 ep239 ep240 ep60 ep239 441008 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2441073937) qz281 0 2 ep238 ep57 ep239 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2441073937) qz282 0 2 ep240 ep60 ep239 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz334 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 383318975) qz16)

noncomputable def ep242 := @Enclosure.Real.IsNear.cos_image qz49 qz334 Bool.false 383318975 1048576 751 1048576 Bool.false 441008 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz49 Bool.false 823171231491600891697 2251799813685248000 71261000042586214949 99601500000000000000000 383318975 1048576 751 1048576 (ep237 rfl) rfl) (Enclosure.sfrac_false_div 383318975 1048576) (BSN.cos_reduce0 qz334 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 171775307442387828080640) qz19) 226375608064910080 72057594037927936 Bool.false 441008 1048576 58 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q0 383318975 1048576 226375608064910080 72057594037927936 58 171775307442387828080640 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 441008 1048576 171775307442387828080640 151115727451828646838272 2441073937 2147483648 398796 398406 (ep241 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep243 := nat_lit 2284886832822962177404105183894000784039473962021032005955166680322080490505345

noncomputable def ep244 := nat_lit 5982186118088124385730512495382385626558218102626193854432239463131223562765441

noncomputable def ep245 := BSN.sin_dyadic_bound_f 2441073937 2147483648 3 2 1048576 398796 ep243 ep64 ep239 ep244 ep66 ep239 951327 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2441073937) qz285 0 2 ep243 ep64 ep239 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2441073937) qz286 0 2 ep244 ep66 ep239 rfl rfl rfl rfl) rfl rfl

noncomputable def ep246 := @Enclosure.Real.IsNear.sin_image qz49 qz334 Bool.false 383318975 1048576 751 1048576 Bool.false 951327 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz49 Bool.false 823171231491600891697 2251799813685248000 71261000042586214949 99601500000000000000000 383318975 1048576 751 1048576 (ep237 rfl) rfl) (Enclosure.sfrac_false_div 383318975 1048576) (BSN.sin_reduce0 qz334 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 171775307442387828080640) qz19) 226375608064910080 72057594037927936 Bool.false 951327 1048576 58 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q0 383318975 1048576 226375608064910080 72057594037927936 58 171775307442387828080640 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 951327 1048576 171775307442387828080640 151115727451828646838272 2441073937 2147483648 398796 398406 (ep245 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz335 := (@Enclosure.Real.IsNear.recentre' qz48 Bool.false 290823 1048576 1 1048576 290823 1048576 1 1048576 (ep235 rfl rfl) rfl)

noncomputable def ep247 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz48 (Real.cos qz49)) (@HMul.hMul Real Real Real qz0 qz48 (@Neg.neg Real Real.instNeg (Real.sin qz49))) Bool.false 8015954349 68719476736 5487561768815 27378251848482816 Bool.true 276667772121 1099511627776 44002151226277 219026014787862528 (@Enclosure.Real.IsNear.mulLit_ff qz48 (Real.cos qz49) 290823 1048576 1 1048576 27563 65536 150650029 208879484928 8015954349 68719476736 5487561768815 27378251848482816 qz335 (@Enclosure.Real.IsNear.recentre' (Real.cos qz49) Bool.false 441008 1048576 150650029 208879484928 27563 65536 150650029 208879484928 (ep242 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz48 (@Neg.neg Real Real.instNeg (Real.sin qz49)) 290823 1048576 1 1048576 951327 1048576 150650029 208879484928 276667772121 1099511627776 44002151226277 219026014787862528 qz335 (@Enclosure.Real.IsNear.neg (Real.sin qz49) Bool.false 951327 1048576 150650029 208879484928 (@Enclosure.Real.IsNear.recentre' (Real.sin qz49) Bool.false 951327 1048576 150650029 208879484928 951327 1048576 150650029 208879484928 (ep246 rfl rfl) rfl)) rfl)

noncomputable def ep248 := @ep166 8015954349 68719476736 5487561768815 27378251848482816 Bool.true 276667772121 1099511627776 44002151226277 219026014787862528 Bool.false 40660102996449627734016 591682371981 1099511627776 774129878565427 219026014787862528 Bool.true 85873392171776963772416 156202790407 1099511627776 774364001851327 219026014787862528 (ep167 (BSN.head_sum_c_succ qz5 12 13 rfl rfl) (ep233 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep234 ep247) rfl rfl

noncomputable abbrev qz336 := (@Nat.cast Real Real.instNatCast 14)

noncomputable abbrev qz50 := (@Inv.inv Real Real.instInv (Real.sqrt qz336))

noncomputable abbrev qz560 := (Real.log (Enclosure.sfrac Bool.false 14 1))

noncomputable abbrev qz51 := (@HMul.hMul Real Real Real qz267 qz278 qz560)

noncomputable def ep249 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz312 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz50 (Real.cos qz51)) (@HMul.hMul Real Real Real qz0 qz50 (@Neg.neg Real Real.instNeg (Real.sin qz51)))) Bool.false 190020167365 1099511627776 42409662762773 219026014787862528 Bool.false 224150962335 1099511627776 42433923696143 219026014787862528 (BSN.cpow_neg_s_mk qz13 142522 1000 14 qz14 rfl)

noncomputable abbrev qz337 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14) qz15)

noncomputable def ep250 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz336) 3923413 1048576 1 1048576 140121 140122 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz336) (Real.sqrt qz337) Bool.false 3923413 1048576 1 1048576 (BSN.sqrt_natCast_div_one 14) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz337) Bool.false 3923413 1048576 1 1048576 3923413 1048576 1 1048576 (BSN.sqrt_enclosure 14 1 1961706 1961707 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep251 := BSN.log_dyadic_bound 6 22 5 4 51857700491520 524288 199203 1346332575744 176359680 293399 28 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 6) (BSN.artanhQ 22) 0 4 1346332575744 51857700491520 176359680 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep252 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz560 142522 1000 0 1 11885250371606245 4503599627370496 1000000000597609 199203000000000000000 169390965346206524989 450359962737049600 71261000042586214949 99601500000000000000000 qz18 (BSN.isNear_log_sfrac 14 1 11885250371606245 4503599627370496 1000000000597609 199203000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz337) Bool.false 49850353174629559828480 18889465931478580854784 1000000000597609 199203000000000000000 11885250371606245 4503599627370496 1000000000597609 199203000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 293399 524288 24973259072661432 36028797018963968 199203 1000000000000000 rfl rfl rfl rfl (ep251 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep253 := nat_lit 5199692091550974586939504849674286096

noncomputable def ep254 := BSN.sin_dyadic_bound_f 1510060706 2147483648 2 1 1048576 398796 ep253 ep180 ep253 ep253 ep181 ep253 678055 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1510060706) qz285 0 1 ep253 ep180 ep253 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1510060706) qz286 0 1 ep253 ep181 ep253 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz338 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 197197037) qz37)

noncomputable def ep255 := @Enclosure.Real.IsNear.cos_image qz51 qz338 Bool.false 197197037 524288 47 65536 Bool.false 678055 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz51 Bool.false 169390965346206524989 450359962737049600 71261000042586214949 99601500000000000000000 197197037 524288 47 65536 (ep252 rfl) rfl) (Enclosure.sfrac_false_div 197197037 524288) (BSN.cos_reduce3 qz338 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 53130537785106527944704) qz38) 226375608064910080 72057594037927936 Bool.false 678055 1048576 59 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q3 197197037 524288 226375608064910080 72057594037927936 59 53130537785106527944704 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 678055 1048576 53130537785106527944704 75557863725914323419136 1510060706 2147483648 398796 398406 (ep254 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep256 := nat_lit 185810207676017259917837970114008470352192922063125789128562302222221974077696

noncomputable def ep257 := nat_lit 27036797846937748685406243520068216666956166867739815427065220747258921216

noncomputable def ep258 := nat_lit 557376549432357904256143097854985274623244853855641887754832776225171404390656

noncomputable def ep259 := BSN.cos_dyadic_bound_f 1510060706 2147483648 3 2 1048576 398796 ep256 ep57 ep257 ep258 ep60 ep257 799845 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1510060706) qz281 0 2 ep256 ep57 ep257 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1510060706) qz282 0 2 ep258 ep60 ep257 rfl rfl rfl rfl) rfl rfl

noncomputable def ep260 := @Enclosure.Real.IsNear.sin_image qz51 qz338 Bool.false 197197037 524288 47 65536 Bool.true 799845 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz51 Bool.false 169390965346206524989 450359962737049600 71261000042586214949 99601500000000000000000 197197037 524288 47 65536 (ep252 rfl) rfl) (Enclosure.sfrac_false_div 197197037 524288) (BSN.sin_reduce3 qz338 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 53130537785106527944704) qz38) 226375608064910080 72057594037927936 Bool.false 799845 1048576 59 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q3 197197037 524288 226375608064910080 72057594037927936 59 53130537785106527944704 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 799845 1048576 53130537785106527944704 75557863725914323419136 1510060706 2147483648 398796 398406 (ep259 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz339 := (@Enclosure.Real.IsNear.recentre' qz50 Bool.false 280243 1048576 1 1048576 280243 1048576 1 1048576 (ep250 rfl rfl) rfl)

noncomputable def ep261 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz50 (Real.cos qz51)) (@HMul.hMul Real Real Real qz0 qz50 (@Neg.neg Real Real.instNeg (Real.sin qz51))) Bool.false 190020167365 1099511627776 42409662762773 219026014787862528 Bool.false 224150962335 1099511627776 42433923696143 219026014787862528 (@Enclosure.Real.IsNear.mulLit_ff qz50 (Real.cos qz51) 280243 1048576 1 1048576 678055 1048576 9428077 13054967808 190020167365 1099511627776 42409662762773 219026014787862528 qz339 (@Enclosure.Real.IsNear.recentre' (Real.cos qz51) Bool.false 678055 1048576 9428077 13054967808 678055 1048576 9428077 13054967808 (ep255 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz50 (@Neg.neg Real Real.instNeg (Real.sin qz51)) 280243 1048576 1 1048576 799845 1048576 9428077 13054967808 224150962335 1099511627776 42433923696143 219026014787862528 qz339 (@Enclosure.Real.IsNear.neg (Real.sin qz51) Bool.true 799845 1048576 9428077 13054967808 (@Enclosure.Real.IsNear.recentre' (Real.sin qz51) Bool.true 799845 1048576 9428077 13054967808 799845 1048576 9428077 13054967808 (ep260 rfl rfl) rfl)) rfl)

noncomputable def ep262 := @ep164 190020167365 1099511627776 42409662762773 219026014787862528 Bool.false 224150962335 1099511627776 42433923696143 219026014787862528 Bool.false 859491031472953146474496 390851269673 549755813888 34022480888675 9126083949494272 Bool.false 74709805120958788272128 8493521491 137438953472 136132987591245 36504335797977088 (ep165 (BSN.head_sum_c_succ qz5 13 14 rfl rfl) (ep248 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep249 ep261) rfl rfl

noncomputable abbrev qz340 := (@Nat.cast Real Real.instNatCast 15)

noncomputable abbrev qz52 := (@Inv.inv Real Real.instInv (Real.sqrt qz340))

noncomputable abbrev qz561 := (Real.log (Enclosure.sfrac Bool.false 15 1))

noncomputable abbrev qz53 := (@HMul.hMul Real Real Real qz267 qz278 qz561)

noncomputable def ep263 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz311 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz52 (Real.cos qz53)) (@HMul.hMul Real Real Real qz0 qz52 (@Neg.neg Real Real.instNeg (Real.sin qz53)))) Bool.true 254454033663 1099511627776 40974509696647 219026014787862528 Bool.true 125888879439 1099511627776 40879915363255 219026014787862528 (BSN.cpow_neg_s_mk qz13 142522 1000 15 qz14 rfl)

noncomputable abbrev qz341 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 15) qz15)

noncomputable def ep264 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz340) 4061117 1048576 1 1048576 135370 135371 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz340) (Real.sqrt qz341) Bool.false 4061117 1048576 1 1048576 (BSN.sqrt_natCast_div_one 15) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz341) Bool.false 4061117 1048576 1 1048576 4061117 1048576 1 1048576 (BSN.sqrt_enclosure 15 1 2030558 2030559 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep265 := BSN.log_dyadic_bound 7 23 6 5 430628584065881355 524288 199203 14087658153505881 266939110305 329571 30 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 7) (BSN.artanhQ 23) 0 5 14087658153505881 430628584065881355 266939110305 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep266 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz561 142522 1000 0 1 12195965485668069 4503599627370496 1000000000597609 199203000000000000000 869096696474192265009 2251799813685248000 71261000042586214949 99601500000000000000000 qz18 (BSN.isNear_log_sfrac 15 1 12195965485668069 4503599627370496 1000000000597609 199203000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz341) Bool.false 51153586820399524478976 18889465931478580854784 1000000000597609 199203000000000000000 12195965485668069 4503599627370496 1000000000597609 199203000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 329571 524288 24973259072661432 36028797018963968 199203 1000000000000000 rfl rfl rfl rfl (ep265 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep267 := nat_lit 2087690653001958191120956019712504158975276422691350619315388659636279649788160

noncomputable def ep268 := nat_lit 1052668723031396029991538117829589200956331689615214772022754786800212664576

noncomputable def ep269 := nat_lit 5466056913263077764125374704199120129086080379551303179052266791297341595607296

noncomputable def ep270 := BSN.sin_dyadic_bound_f 2386637526 2147483648 3 2 1048576 398796 ep267 ep64 ep268 ep269 ep66 ep268 939843 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2386637526) qz285 0 2 ep267 ep64 ep268 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2386637526) qz286 0 2 ep269 ep66 ep268 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz342 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 202352343) qz37)

noncomputable def ep271 := @Enclosure.Real.IsNear.cos_image qz53 qz342 Bool.false 202352343 524288 751 1048576 Bool.true 939843 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz53 Bool.false 869096696474192265009 2251799813685248000 71261000042586214949 99601500000000000000000 202352343 524288 751 1048576 (ep266 rfl) rfl) (Enclosure.sfrac_false_div 202352343 524288) (BSN.cos_reduce1 qz342 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 83972342756881303863296) qz38) 226375608064910080 72057594037927936 Bool.false 939843 1048576 61 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q1 202352343 524288 226375608064910080 72057594037927936 61 83972342756881303863296 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 939843 1048576 83972342756881303863296 75557863725914323419136 2386637526 2147483648 398796 398406 (ep270 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep272 := nat_lit 1160295993322435171080527361225982127964467493357245995073892701925399899955456

noncomputable def ep273 := nat_lit 3478782642521242721181599007442287205491489816692507555677632596202599274537216

noncomputable def ep274 := BSN.cos_dyadic_bound_f 2386637526 2147483648 3 2 1048576 398796 ep272 ep57 ep268 ep273 ep60 ep268 464979 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2386637526) qz281 0 2 ep272 ep57 ep268 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2386637526) qz282 0 2 ep273 ep60 ep268 rfl rfl rfl rfl) rfl rfl

noncomputable def ep275 := @Enclosure.Real.IsNear.sin_image qz53 qz342 Bool.false 202352343 524288 751 1048576 Bool.false 464979 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz53 Bool.false 869096696474192265009 2251799813685248000 71261000042586214949 99601500000000000000000 202352343 524288 751 1048576 (ep266 rfl) rfl) (Enclosure.sfrac_false_div 202352343 524288) (BSN.sin_reduce1 qz342 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 83972342756881303863296) qz38) 226375608064910080 72057594037927936 Bool.false 464979 1048576 61 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q1 202352343 524288 226375608064910080 72057594037927936 61 83972342756881303863296 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 464979 1048576 83972342756881303863296 75557863725914323419136 2386637526 2147483648 398796 398406 (ep274 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz343 := (@Enclosure.Real.IsNear.recentre' qz52 Bool.false 270741 1048576 1 1048576 270741 1048576 1 1048576 (ep264 rfl rfl) rfl)

noncomputable def ep276 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz52 (Real.cos qz53)) (@HMul.hMul Real Real Real qz0 qz52 (@Neg.neg Real Real.instNeg (Real.sin qz53))) Bool.true 254454033663 1099511627776 40974509696647 219026014787862528 Bool.true 125888879439 1099511627776 40879915363255 219026014787862528 (@Enclosure.Real.IsNear.mulLit_ft qz52 (Real.cos qz53) 270741 1048576 1 1048576 939843 1048576 150650029 208879484928 254454033663 1099511627776 40974509696647 219026014787862528 qz343 (@Enclosure.Real.IsNear.recentre' (Real.cos qz53) Bool.true 939843 1048576 150650029 208879484928 939843 1048576 150650029 208879484928 (ep271 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz52 (@Neg.neg Real Real.instNeg (Real.sin qz53)) 270741 1048576 1 1048576 464979 1048576 150650029 208879484928 125888879439 1099511627776 40879915363255 219026014787862528 qz343 (@Enclosure.Real.IsNear.neg (Real.sin qz53) Bool.false 464979 1048576 150650029 208879484928 (@Enclosure.Real.IsNear.recentre' (Real.sin qz53) Bool.false 464979 1048576 150650029 208879484928 464979 1048576 150650029 208879484928 (ep275 rfl rfl) rfl)) rfl)

noncomputable def ep277 := @ep162 254454033663 1099511627776 40974509696647 219026014787862528 Bool.true 125888879439 1099511627776 40879915363255 219026014787862528 Bool.false 289857931362989458325504 527248505683 1099511627776 857514051024847 219026014787862528 Bool.true 7963310203739089928192 57940707511 1099511627776 857677840910725 219026014787862528 (ep163 (BSN.head_sum_c_succ qz5 14 15 rfl rfl) (ep262 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep263 ep276) rfl rfl

noncomputable abbrev qz344 := (@Nat.cast Real Real.instNatCast 16)

noncomputable abbrev qz54 := (@Inv.inv Real Real.instInv (Real.sqrt qz344))

noncomputable abbrev qz562 := (Real.log (Enclosure.sfrac Bool.false 16 1))

noncomputable abbrev qz55 := (@HMul.hMul Real Real Real qz267 qz278 qz562)

noncomputable def ep278 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz310 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz54 (Real.cos qz55)) (@HMul.hMul Real Real Real qz0 qz54 (@Neg.neg Real Real.instNeg (Real.sin qz55)))) Bool.false 53183309697 274877906944 9926469373789 54756503696965632 Bool.false 174074224149 1099511627776 39676500431137 219026014787862528 (BSN.cpow_neg_s_mk qz13 142522 1000 16 qz14 rfl)

noncomputable abbrev qz345 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16) qz15)

noncomputable def ep279 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz344) 4194305 1048576 1 1048576 131071 131072 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz344) (Real.sqrt qz345) Bool.false 4194305 1048576 1 1048576 (BSN.sqrt_natCast_div_one 16) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz345) Bool.false 4194305 1048576 1 1048576 4194305 1048576 1 1048576 (BSN.sqrt_enclosure 16 1 2097152 2097153 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep280 := BSN.log_dyadic_bound 0 32 1 0 1 524288 199203 0 1 0 32 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 32) 0 0 rfl) rfl rfl rfl

noncomputable def ep281 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz562 142522 1000 0 1 3121657384082679 1125899906842624 250000000199203 49800750000000000000 222452426847115788219 562949953421312000 17815250014195404983 24900375000000000000000 qz18 (BSN.isNear_log_sfrac 16 1 3121657384082679 1125899906842624 250000000199203 49800750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz345) Bool.false 52372720210750067441664 18889465931478580854784 1000000000796812 199203000000000000000 3121657384082679 1125899906842624 250000000199203 49800750000000000000 (BSN.log_rat_reduce_isNear 16 1 4 32 32 0 524288 24973259072661432 36028797018963968 199203 1000000000000000 rfl rfl rfl rfl (ep280 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep282 := nat_lit 839273751852126210210247037190596909242895960850720687968206109650403737890625

noncomputable def ep283 := nat_lit 170227057659024834601810917105718007308458666395570421846998730621337890625

noncomputable def ep284 := nat_lit 2197822315805073081770815498776249314100513821530104211614692289234813337890625

noncomputable def ep285 := BSN.sin_dyadic_bound_f 1900546825 2147483648 3 2 1048576 398796 ep282 ep64 ep283 ep284 ep66 ep283 811516 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1900546825) qz285 0 2 ep282 ep64 ep283 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1900546825) qz286 0 2 ep284 ep66 ep283 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz346 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 414349933) qz16)

noncomputable def ep286 := @Enclosure.Real.IsNear.cos_image qz55 qz346 Bool.false 414349933 1048576 47 65536 Bool.false 811516 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz55 Bool.false 222452426847115788219 562949953421312000 17815250014195404983 24900375000000000000000 414349933 1048576 47 65536 (ep281 rfl) rfl) (Enclosure.sfrac_false_div 414349933 1048576) (BSN.cos_reduce3 qz346 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 133739093343220317290496) qz19) 226375608064910080 72057594037927936 Bool.false 811516 1048576 62 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q3 414349933 1048576 226375608064910080 72057594037927936 62 133739093343220317290496 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 811516 1048576 133739093343220317290496 151115727451828646838272 1900546825 2147483648 398796 398406 (ep285 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep287 := nat_lit 466338851943474127821071381069045268693745959879909524614268727019389337890625

noncomputable def ep288 := nat_lit 1398676101715104333794010521372924370066620962306937432999112183596925337890625

noncomputable def ep289 := BSN.cos_dyadic_bound_f 1900546825 2147483648 3 2 1048576 398796 ep287 ep57 ep283 ep288 ep60 ep283 664043 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1900546825) qz281 0 2 ep287 ep57 ep283 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1900546825) qz282 0 2 ep288 ep60 ep283 rfl rfl rfl rfl) rfl rfl

noncomputable def ep290 := @Enclosure.Real.IsNear.sin_image qz55 qz346 Bool.false 414349933 1048576 47 65536 Bool.true 664043 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz55 Bool.false 222452426847115788219 562949953421312000 17815250014195404983 24900375000000000000000 414349933 1048576 47 65536 (ep281 rfl) rfl) (Enclosure.sfrac_false_div 414349933 1048576) (BSN.sin_reduce3 qz346 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 133739093343220317290496) qz19) 226375608064910080 72057594037927936 Bool.false 664043 1048576 62 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q3 414349933 1048576 226375608064910080 72057594037927936 62 133739093343220317290496 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 664043 1048576 133739093343220317290496 151115727451828646838272 1900546825 2147483648 398796 398406 (ep289 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz347 := (@Enclosure.Real.IsNear.recentre' qz54 Bool.false 262143 1048576 1 1048576 262143 1048576 1 1048576 (ep279 rfl rfl) rfl)

noncomputable def ep291 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz54 (Real.cos qz55)) (@HMul.hMul Real Real Real qz0 qz54 (@Neg.neg Real Real.instNeg (Real.sin qz55))) Bool.false 53183309697 274877906944 9926469373789 54756503696965632 Bool.false 174074224149 1099511627776 39676500431137 219026014787862528 (@Enclosure.Real.IsNear.mulLit_ff qz54 (Real.cos qz55) 262143 1048576 1 1048576 202879 262144 9428077 13054967808 53183309697 274877906944 9926469373789 54756503696965632 qz347 (@Enclosure.Real.IsNear.recentre' (Real.cos qz55) Bool.false 811516 1048576 9428077 13054967808 202879 262144 9428077 13054967808 (ep286 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz54 (@Neg.neg Real Real.instNeg (Real.sin qz55)) 262143 1048576 1 1048576 664043 1048576 9428077 13054967808 174074224149 1099511627776 39676500431137 219026014787862528 qz347 (@Enclosure.Real.IsNear.neg (Real.sin qz55) Bool.true 664043 1048576 9428077 13054967808 (@Enclosure.Real.IsNear.recentre' (Real.sin qz55) Bool.true 664043 1048576 9428077 13054967808 664043 1048576 9428077 13054967808 (ep290 rfl rfl) rfl)) rfl)

noncomputable def ep292 := @ep160 53183309697 274877906944 9926469373789 54756503696965632 Bool.false 174074224149 1099511627776 39676500431137 219026014787862528 Bool.false 203404633096958324506624 739981744471 1099511627776 897219928520003 219026014787862528 Bool.false 127690151917998558937088 58066758319 549755813888 448677170670931 109513007393931264 (ep161 (BSN.head_sum_c_succ qz5 15 16 rfl rfl) (ep277 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep278 ep291) rfl rfl

theorem EMRow50.d7 : Enclosure.Complex.IsNear qz39 Bool.false 739981744471 1099511627776 897219928520003 219026014787862528 Bool.false 58066758319 549755813888 448677170670931 109513007393931264 := ep159 (BSN.head_sum_c_succ qz5 16 17 rfl rfl) (ep292 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz56 := (BSN.headSumC qz271 25)

noncomputable abbrev qz348 := (@Nat.cast Complex Complex.instNatCast 24)

noncomputable def ep293 := @Enclosure.Complex.IsNear.of_eq qz56 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 24) (@HPow.hPow Complex Complex Complex qz6 qz348 qz7)) Bool.false 1525438120315 1099511627776 1179097361398459 219026014787862528 Bool.true 31476199109 137438953472 147373730720309 27378251848482816

noncomputable def ep294 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 24) (@HPow.hPow Complex Complex Complex qz6 qz348 qz7) Bool.false 1334466959501 1099511627776 1146674495095421 219026014787862528 Bool.true 8369057843 68719476736 143329372673443 27378251848482816 Bool.false

noncomputable abbrev qz349 := (@Nat.cast Complex Complex.instNatCast 23)

noncomputable def ep295 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 24) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 23) (@HPow.hPow Complex Complex Complex qz6 qz349 qz7)) Bool.false 1334466959501 1099511627776 1146674495095421 219026014787862528 Bool.true 8369057843 68719476736 143329372673443 27378251848482816

noncomputable def ep296 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 23) (@HPow.hPow Complex Complex Complex qz6 qz349 qz7) Bool.false 1169952532439 1099511627776 1113585883044643 219026014787862528 Bool.false 12886121921 549755813888 556775388251969 109513007393931264 Bool.false

noncomputable abbrev qz350 := (@Nat.cast Complex Complex.instNatCast 22)

noncomputable def ep297 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 23) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 22) (@HPow.hPow Complex Complex Complex qz6 qz350 qz7)) Bool.false 1169952532439 1099511627776 1113585883044643 219026014787862528 Bool.false 12886121921 549755813888 556775388251969 109513007393931264

noncomputable def ep298 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 22) (@HPow.hPow Complex Complex Complex qz6 qz350 qz7) Bool.false 496739100769 549755813888 179958269067947 36504335797977088 Bool.false 45017485975 274877906944 179955711434229 36504335797977088 Bool.false

noncomputable abbrev qz351 := (@Nat.cast Complex Complex.instNatCast 21)

noncomputable def ep299 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 22) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 21) (@HPow.hPow Complex Complex Complex qz6 qz351 qz7)) Bool.false 496739100769 549755813888 179958269067947 36504335797977088 Bool.false 45017485975 274877906944 179955711434229 36504335797977088

noncomputable def ep300 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 21) (@HPow.hPow Complex Complex Complex qz6 qz351 qz7) Bool.false 96238861023 137438953472 261210757340981 54756503696965632 Bool.false 66791120401 274877906944 522532651430083 109513007393931264 Bool.false

noncomputable abbrev qz352 := (@Nat.cast Complex Complex.instNatCast 20)

noncomputable def ep301 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 21) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 20) (@HPow.hPow Complex Complex Complex qz6 qz352 qz7)) Bool.false 96238861023 137438953472 261210757340981 54756503696965632 Bool.false 66791120401 274877906944 522532651430083 109513007393931264

noncomputable def ep302 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 20) (@HPow.hPow Complex Complex Complex qz6 qz352 qz7) Bool.false 267479675491 549755813888 42055021004355 9126083949494272 Bool.false 194748496485 1099511627776 336560288838261 73008671595954176 Bool.false

noncomputable abbrev qz353 := (@Nat.cast Complex Complex.instNatCast 19)

noncomputable def ep303 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 20) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 19) (@HPow.hPow Complex Complex Complex qz6 qz353 qz7)) Bool.false 267479675491 549755813888 42055021004355 9126083949494272 Bool.false 194748496485 1099511627776 336560288838261 73008671595954176

noncomputable def ep304 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 19) (@HPow.hPow Complex Complex Complex qz6 qz353 qz7) Bool.false 118462055935 274877906944 486514763998283 109513007393931264 Bool.true 24990537449 549755813888 243309459739033 54756503696965632 Bool.false

noncomputable abbrev qz354 := (@Nat.cast Complex Complex.instNatCast 18)

noncomputable def ep305 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 19) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 18) (@HPow.hPow Complex Complex Complex qz6 qz354 qz7)) Bool.false 118462055935 274877906944 486514763998283 109513007393931264 Bool.true 24990537449 549755813888 243309459739033 54756503696965632

noncomputable def ep306 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 18) (@HPow.hPow Complex Complex Complex qz6 qz354 qz7) Bool.false 89157677529 137438953472 467776936128413 109513007393931264 Bool.true 37298725207 274877906944 467937591754289 109513007393931264 Bool.true

noncomputable abbrev qz355 := (@Nat.cast Complex Complex.instNatCast 17)

noncomputable def ep307 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 18) (@HAdd.hAdd Complex Complex Complex qz4 qz39 (@HPow.hPow Complex Complex Complex qz6 qz355 qz7)) Bool.false 89157677529 137438953472 467776936128413 109513007393931264 Bool.true 37298725207 274877906944 467937591754289 109513007393931264

noncomputable def ep308 := @Enclosure.Complex.IsNear.addLitP qz39 (@HPow.hPow Complex Complex Complex qz6 qz355 qz7) Bool.false 739981744471 1099511627776 897219928520003 219026014787862528 Bool.false 58066758319 549755813888 448677170670931 109513007393931264 Bool.true

noncomputable abbrev qz356 := (@Nat.cast Real Real.instNatCast 17)

noncomputable abbrev qz57 := (@Inv.inv Real Real.instInv (Real.sqrt qz356))

noncomputable abbrev qz563 := (Real.log (Enclosure.sfrac Bool.false 17 1))

noncomputable abbrev qz58 := (@HMul.hMul Real Real Real qz267 qz278 qz563)

noncomputable def ep309 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz355 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz57 (Real.cos qz58)) (@HMul.hMul Real Real Real qz0 qz57 (@Neg.neg Real Real.instNeg (Real.sin qz58)))) Bool.true 26720324239 1099511627776 38333943736823 219026014787862528 Bool.true 132664208733 549755813888 9630210541679 54756503696965632 (BSN.cpow_neg_s_mk qz13 142522 1000 17 qz14 rfl)

noncomputable abbrev qz357 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 17) qz15)

noncomputable def ep310 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz356) 4323389 1048576 1 1048576 127158 127159 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz356) (Real.sqrt qz357) Bool.false 4323389 1048576 1 1048576 (BSN.sqrt_natCast_div_one 17) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz357) Bool.false 4323389 1048576 1 1048576 4323389 1048576 1 1048576 (BSN.sqrt_enclosure 17 1 2161694 2161695 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep311 := BSN.log_dyadic_bound 1 33 2 1 3267 524288 199203 1 1 31784 34 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1) (BSN.artanhQ 33) 0 1 1 3267 1 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep312 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz563 142522 1000 0 1 3189913004350711 1125899906842624 250000000199203 49800750000000000000 227316390603036016571 562949953421312000 17815250014195404983 24900375000000000000000 qz18 (BSN.isNear_log_sfrac 17 1 3189913004350711 1125899906842624 250000000199203 49800750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz357) Bool.false 53517859495200818200576 18889465931478580854784 1000000000796812 199203000000000000000 3189913004350711 1125899906842624 250000000199203 49800750000000000000 (BSN.log_rat_reduce_isNear 17 1 4 34 32 31784 524288 24973259072661432 36028797018963968 199203 1000000000000000 rfl rfl rfl rfl (ep311 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep313 := BSN.sin_dyadic_bound_f 215540540 2147483648 1 0 1048576 398796 0 1 1 0 1 1 105067 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 215540540) qz285 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 215540540) qz286 0 0 rfl) rfl rfl

noncomputable abbrev qz358 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 105852443) qz32)

noncomputable def ep314 := @Enclosure.Real.IsNear.cos_image qz58 qz358 Bool.false 105852443 262144 751 1048576 Bool.true 105067 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz58 Bool.false 227316390603036016571 562949953421312000 17815250014195404983 24900375000000000000000 105852443 262144 751 1048576 (ep312 rfl) rfl) (Enclosure.sfrac_false_div 105852443 262144) (BSN.cos_reduce1 qz358 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3791829287891848134656) qz302) 226375608064910080 72057594037927936 Bool.false 105067 1048576 64 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q1 105852443 262144 226375608064910080 72057594037927936 64 3791829287891848134656 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 105067 1048576 3791829287891848134656 37778931862957161709568 215540540 2147483648 398796 398406 (ep313 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep315 := nat_lit 2158320154892469965302607270560000

noncomputable def ep316 := BSN.cos_dyadic_bound_f 215540540 2147483648 2 1 1048576 398796 ep315 ep184 ep315 ep315 ep185 ep315 1043298 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 215540540) qz281 0 1 ep315 ep184 ep315 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 215540540) qz282 0 1 ep315 ep185 ep315 rfl rfl rfl rfl) rfl rfl

noncomputable def ep317 := @Enclosure.Real.IsNear.sin_image qz58 qz358 Bool.false 105852443 262144 751 1048576 Bool.false 1043298 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz58 Bool.false 227316390603036016571 562949953421312000 17815250014195404983 24900375000000000000000 105852443 262144 751 1048576 (ep312 rfl) rfl) (Enclosure.sfrac_false_div 105852443 262144) (BSN.sin_reduce1 qz358 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3791829287891848134656) qz302) 226375608064910080 72057594037927936 Bool.false 1043298 1048576 64 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q1 105852443 262144 226375608064910080 72057594037927936 64 3791829287891848134656 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1043298 1048576 3791829287891848134656 37778931862957161709568 215540540 2147483648 398796 398406 (ep316 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz359 := (@Enclosure.Real.IsNear.recentre' qz57 Bool.false 254317 1048576 1 1048576 254317 1048576 1 1048576 (ep310 rfl rfl) rfl)

noncomputable def ep318 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz57 (Real.cos qz58)) (@HMul.hMul Real Real Real qz0 qz57 (@Neg.neg Real Real.instNeg (Real.sin qz58))) Bool.true 26720324239 1099511627776 38333943736823 219026014787862528 Bool.true 132664208733 549755813888 9630210541679 54756503696965632 (@Enclosure.Real.IsNear.mulLit_ft qz57 (Real.cos qz58) 254317 1048576 1 1048576 105067 1048576 150650029 208879484928 26720324239 1099511627776 38333943736823 219026014787862528 qz359 (@Enclosure.Real.IsNear.recentre' (Real.cos qz58) Bool.true 105067 1048576 150650029 208879484928 105067 1048576 150650029 208879484928 (ep314 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz57 (@Neg.neg Real Real.instNeg (Real.sin qz58)) 254317 1048576 1 1048576 521649 524288 150650029 208879484928 132664208733 549755813888 9630210541679 54756503696965632 qz359 (@Enclosure.Real.IsNear.neg (Real.sin qz58) Bool.false 521649 524288 150650029 208879484928 (@Enclosure.Real.IsNear.recentre' (Real.sin qz58) Bool.false 1043298 1048576 150650029 208879484928 521649 524288 150650029 208879484928 (ep317 rfl rfl) rfl)) rfl)

noncomputable def ep319 := @ep308 26720324239 1099511627776 38333943736823 219026014787862528 Bool.true 132664208733 549755813888 9630210541679 54756503696965632 Bool.false 784239225189107899564032 89157677529 137438953472 467776936128413 109513007393931264 Bool.true 41010382066318292549632 37298725207 274877906944 467937591754289 109513007393931264 EMRow50.d7 (ep309 ep318) rfl rfl

noncomputable abbrev qz360 := (@Nat.cast Real Real.instNatCast 18)

noncomputable abbrev qz59 := (@Inv.inv Real Real.instInv (Real.sqrt qz360))

noncomputable abbrev qz564 := (Real.log (Enclosure.sfrac Bool.false 18 1))

noncomputable abbrev qz60 := (@HMul.hMul Real Real Real qz267 qz278 qz564)

noncomputable def ep320 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz354 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz59 (Real.cos qz60)) (@HMul.hMul Real Real Real qz0 qz59 (@Neg.neg Real Real.instNeg (Real.sin qz60)))) Bool.true 59853299123 274877906944 3122971311645 18252167898988544 Bool.false 49606912965 549755813888 6227109241259 36504335797977088 (BSN.cpow_neg_s_mk qz13 142522 1000 18 qz14 rfl)

noncomputable abbrev qz361 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 18) qz15)

noncomputable def ep321 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz360) 4448731 1048576 1 1048576 123575 123576 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz360) (Real.sqrt qz361) Bool.false 4448731 1048576 1 1048576 (BSN.sqrt_natCast_div_one 18) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz361) Bool.false 4448731 1048576 1 1048576 4448731 1048576 1 1048576 (BSN.sqrt_enclosure 18 1 2224365 2224366 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep322 := BSN.log_dyadic_bound 2 34 3 2 20045040 524288 199203 23168 48 61752 36 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 2) (BSN.artanhQ 34) 0 2 23168 20045040 48 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep323 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz564 142522 1000 0 1 3254268794313975 1125899906842624 250000000199203 49800750000000000000 9276097942064326899 22517998136852480 17815250014195404983 24900375000000000000000 qz18 (BSN.isNear_log_sfrac 18 1 3254268794313975 1125899906842624 250000000199203 49800750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz361) Bool.false 54597570484265130393600 18889465931478580854784 1000000000796812 199203000000000000000 3254268794313975 1125899906842624 250000000199203 49800750000000000000 (BSN.log_rat_reduce_isNear 18 1 4 36 32 61752 524288 24973259072661432 36028797018963968 199203 1000000000000000 rfl rfl rfl rfl (ep322 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep324 := nat_lit 506617223925410821035485142473309761

noncomputable def ep325 := BSN.cos_dyadic_bound_f 843664913 2147483648 2 1 1048576 398796 ep324 ep184 ep324 ep324 ep185 ep324 968692 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 843664913) qz281 0 1 ep324 ep184 ep324 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 843664913) qz282 0 1 ep324 ep185 ep324 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz362 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 215975985) qz37)

noncomputable def ep326 := @Enclosure.Real.IsNear.cos_image qz60 qz362 Bool.false 215975985 524288 47 65536 Bool.true 968692 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz60 Bool.false 9276097942064326899 22517998136852480 17815250014195404983 24900375000000000000000 215975985 524288 47 65536 (ep323 rfl) rfl) (Enclosure.sfrac_false_div 215975985 524288) (BSN.cos_reduce2 qz362 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 29683820245705755197440) qz38) 226375608064910080 72057594037927936 Bool.false 968692 1048576 65 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q2 215975985 524288 226375608064910080 72057594037927936 65 29683820245705755197440 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 968692 1048576 29683820245705755197440 75557863725914323419136 843664913 2147483648 398796 398406 (ep325 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep327 := BSN.sin_dyadic_bound_f 843664913 2147483648 2 1 1048576 398796 ep324 ep180 ep324 ep324 ep181 ep324 401430 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 843664913) qz285 0 1 ep324 ep180 ep324 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 843664913) qz286 0 1 ep324 ep181 ep324 rfl rfl rfl rfl) rfl rfl

noncomputable def ep328 := @Enclosure.Real.IsNear.sin_image qz60 qz362 Bool.false 215975985 524288 47 65536 Bool.true 401430 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz60 Bool.false 9276097942064326899 22517998136852480 17815250014195404983 24900375000000000000000 215975985 524288 47 65536 (ep323 rfl) rfl) (Enclosure.sfrac_false_div 215975985 524288) (BSN.sin_reduce2 qz362 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 29683820245705755197440) qz38) 226375608064910080 72057594037927936 Bool.false 401430 1048576 65 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q2 215975985 524288 226375608064910080 72057594037927936 65 29683820245705755197440 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 401430 1048576 29683820245705755197440 75557863725914323419136 843664913 2147483648 398796 398406 (ep327 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz363 := (@Enclosure.Real.IsNear.recentre' qz59 Bool.false 247151 1048576 1 1048576 247151 1048576 1 1048576 (ep321 rfl rfl) rfl)

noncomputable def ep329 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz59 (Real.cos qz60)) (@HMul.hMul Real Real Real qz0 qz59 (@Neg.neg Real Real.instNeg (Real.sin qz60))) Bool.true 59853299123 274877906944 3122971311645 18252167898988544 Bool.false 49606912965 549755813888 6227109241259 36504335797977088 (@Enclosure.Real.IsNear.mulLit_ft qz59 (Real.cos qz60) 247151 1048576 1 1048576 242173 262144 9428077 13054967808 59853299123 274877906944 3122971311645 18252167898988544 qz363 (@Enclosure.Real.IsNear.recentre' (Real.cos qz60) Bool.true 968692 1048576 9428077 13054967808 242173 262144 9428077 13054967808 (ep326 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz59 (@Neg.neg Real Real.instNeg (Real.sin qz60)) 247151 1048576 1 1048576 200715 524288 9428077 13054967808 49606912965 549755813888 6227109241259 36504335797977088 qz363 (@Enclosure.Real.IsNear.neg (Real.sin qz60) Bool.true 200715 524288 9428077 13054967808 (@Enclosure.Real.IsNear.recentre' (Real.sin qz60) Bool.true 401430 1048576 9428077 13054967808 200715 524288 9428077 13054967808 (ep328 rfl rfl) rfl)) rfl)

noncomputable def ep330 := @ep306 59853299123 274877906944 3122971311645 18252167898988544 Bool.false 49606912965 549755813888 6227109241259 36504335797977088 Bool.false 16281300993847926456320 118462055935 274877906944 486514763998283 109513007393931264 Bool.true 6869346627386769145856 24990537449 549755813888 243309459739033 54756503696965632 (ep307 (BSN.head_sum_c_succ qz5 17 18 rfl rfl) (ep319 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep320 ep329) rfl rfl

noncomputable abbrev qz364 := (@Nat.cast Real Real.instNatCast 19)

noncomputable abbrev qz61 := (@Inv.inv Real Real.instInv (Real.sqrt qz364))

noncomputable abbrev qz565 := (Real.log (Enclosure.sfrac Bool.false 19 1))

noncomputable abbrev qz62 := (@HMul.hMul Real Real Real qz267 qz278 qz565)

noncomputable def ep331 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz353 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz61 (Real.cos qz62)) (@HMul.hMul Real Real Real qz0 qz61 (@Neg.neg Real Real.instNeg (Real.sin qz62)))) Bool.false 30555563621 549755813888 18145488053977 109513007393931264 Bool.false 244729571383 1099511627776 36443027558651 219026014787862528 (BSN.cpow_neg_s_mk qz13 142522 1000 19 qz14 rfl)

noncomputable abbrev qz365 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 19) qz15)

noncomputable def ep332 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz364) 4570637 1048576 1 1048576 120279 120280 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz364) (Real.sqrt qz365) Bool.false 4570637 1048576 1 1048576 (BSN.sqrt_natCast_div_one 19) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz365) Bool.false 4570637 1048576 1 1048576 4570637 1048576 1 1048576 (BSN.sqrt_enclosure 19 1 2285318 2285319 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep333 := BSN.log_dyadic_bound 3 35 3 2 22509375 524288 199203 55368 243 90099 38 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 3) (BSN.artanhQ 35) 0 2 55368 22509375 243 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep334 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz565 142522 1000 0 1 3315143513283831 1125899906842624 250000000199203 49800750000000000000 236240441900119080891 562949953421312000 17815250014195404983 24900375000000000000000 qz18 (BSN.isNear_log_sfrac 19 1 3315143513283831 1125899906842624 250000000199203 49800750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz365) Bool.false 55618878793361701994496 18889465931478580854784 1000000000796812 199203000000000000000 3315143513283831 1125899906842624 250000000199203 49800750000000000000 (BSN.log_rat_reduce_isNear 19 1 4 38 32 90099 524288 24973259072661432 36028797018963968 199203 1000000000000000 rfl rfl rfl rfl (ep333 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep335 := nat_lit 76259336138439192949319403579494881

noncomputable def ep336 := BSN.sin_dyadic_bound_f 525500647 2147483648 2 1 1048576 398796 ep335 ep180 ep335 ep335 ep181 ep335 254038 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 525500647) qz285 0 1 ep335 ep180 ep335 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 525500647) qz286 0 1 ep335 ep181 ep335 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz366 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 440032113) qz16)

noncomputable def ep337 := @Enclosure.Real.IsNear.cos_image qz62 qz366 Bool.false 440032113 1048576 751 1048576 Bool.false 254038 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz62 Bool.false 236240441900119080891 562949953421312000 17815250014195404983 24900375000000000000000 440032113 1048576 751 1048576 (ep334 rfl) rfl) (Enclosure.sfrac_false_div 440032113 1048576) (BSN.cos_reduce3 qz366 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 36978820604866043314176) qz19) 226375608064910080 72057594037927936 Bool.false 254038 1048576 66 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q3 440032113 1048576 226375608064910080 72057594037927936 66 36978820604866043314176 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 254038 1048576 36978820604866043314176 151115727451828646838272 525500647 2147483648 398796 398406 (ep336 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep338 := BSN.cos_dyadic_bound_f 525500647 2147483648 2 1 1048576 398796 ep335 ep184 ep335 ep335 ep185 ep335 1017337 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 525500647) qz281 0 1 ep335 ep184 ep335 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 525500647) qz282 0 1 ep335 ep185 ep335 rfl rfl rfl rfl) rfl rfl

noncomputable def ep339 := @Enclosure.Real.IsNear.sin_image qz62 qz366 Bool.false 440032113 1048576 751 1048576 Bool.true 1017337 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz62 Bool.false 236240441900119080891 562949953421312000 17815250014195404983 24900375000000000000000 440032113 1048576 751 1048576 (ep334 rfl) rfl) (Enclosure.sfrac_false_div 440032113 1048576) (BSN.sin_reduce3 qz366 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 36978820604866043314176) qz19) 226375608064910080 72057594037927936 Bool.false 1017337 1048576 66 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q3 440032113 1048576 226375608064910080 72057594037927936 66 36978820604866043314176 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1017337 1048576 36978820604866043314176 151115727451828646838272 525500647 2147483648 398796 398406 (ep338 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz367 := (@Enclosure.Real.IsNear.recentre' qz61 Bool.false 240559 1048576 1 1048576 240559 1048576 1 1048576 (ep332 rfl rfl) rfl)

noncomputable def ep340 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz61 (Real.cos qz62)) (@HMul.hMul Real Real Real qz0 qz61 (@Neg.neg Real Real.instNeg (Real.sin qz62))) Bool.false 30555563621 549755813888 18145488053977 109513007393931264 Bool.false 244729571383 1099511627776 36443027558651 219026014787862528 (@Enclosure.Real.IsNear.mulLit_ff qz61 (Real.cos qz62) 240559 1048576 1 1048576 127019 524288 150650029 208879484928 30555563621 549755813888 18145488053977 109513007393931264 qz367 (@Enclosure.Real.IsNear.recentre' (Real.cos qz62) Bool.false 254038 1048576 150650029 208879484928 127019 524288 150650029 208879484928 (ep337 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz61 (@Neg.neg Real Real.instNeg (Real.sin qz62)) 240559 1048576 1 1048576 1017337 1048576 150650029 208879484928 244729571383 1099511627776 36443027558651 219026014787862528 qz367 (@Enclosure.Real.IsNear.neg (Real.sin qz62) Bool.true 1017337 1048576 150650029 208879484928 (@Enclosure.Real.IsNear.recentre' (Real.sin qz62) Bool.true 1017337 1048576 150650029 208879484928 1017337 1048576 150650029 208879484928 (ep339 rfl rfl) rfl)) rfl)

noncomputable def ep341 := @ep304 30555563621 549755813888 18145488053977 109513007393931264 Bool.false 244729571383 1099511627776 36443027558651 219026014787862528 Bool.false 73524253349026415509504 267479675491 549755813888 42055021004355 9126083949494272 Bool.false 107064118188575482183680 194748496485 1099511627776 336560288838261 73008671595954176 (ep305 (BSN.head_sum_c_succ qz5 18 19 rfl rfl) (ep330 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep331 ep340) rfl rfl

noncomputable abbrev qz368 := (@Nat.cast Real Real.instNatCast 20)

noncomputable abbrev qz63 := (@Inv.inv Real Real.instInv (Real.sqrt qz368))

noncomputable abbrev qz566 := (Real.log (Enclosure.sfrac Bool.false 20 1))

noncomputable abbrev qz64 := (@HMul.hMul Real Real Real qz267 qz278 qz566)

noncomputable def ep342 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz352 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz63 (Real.cos qz64)) (@HMul.hMul Real Real Real qz0 qz63 (@Neg.neg Real Real.instNeg (Real.sin qz64)))) Bool.false 117475768601 549755813888 8880631314851 54756503696965632 Bool.false 72415985119 1099511627776 35384436345383 219026014787862528 (BSN.cpow_neg_s_mk qz13 142522 1000 20 qz14 rfl)

noncomputable abbrev qz369 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 20) qz15)

noncomputable def ep343 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz368) 4689375 1048576 1 1048576 117234 117235 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz368) (Real.sqrt qz369) Bool.false 4689375 1048576 1 1048576 (BSN.sqrt_natCast_div_one 20) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz369) Bool.false 4689375 1048576 1 1048576 4689375 1048576 1 1048576 (BSN.sqrt_enclosure 20 1 2344687 2344688 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep344 := BSN.log_dyadic_bound 4 36 3 2 25194240 524288 199203 104448 768 116991 40 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 4) (BSN.artanhQ 36) 0 2 104448 25194240 768 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep345 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz566 142522 1000 0 1 3372893643545847 1125899906842624 250000000199203 49800750000000000000 240355773932720603067 562949953421312000 17815250014195404983 24900375000000000000000 qz18 (BSN.isNear_log_sfrac 20 1 3372893643545847 1125899906842624 250000000199203 49800750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz369) Bool.false 56587765202795681021952 18889465931478580854784 1000000000796812 199203000000000000000 3372893643545847 1125899906842624 250000000199203 49800750000000000000 (BSN.log_rat_reduce_isNear 20 1 4 40 32 116991 524288 24973259072661432 36028797018963968 199203 1000000000000000 rfl rfl rfl rfl (ep344 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep346 := nat_lit 3581757054968676967215200189421336192137041822172155223134646738513587238764800

noncomputable def ep347 := nat_lit 3096268188274884558578807768029709170488661171194100383876833223093633843456

noncomputable def ep348 := nat_lit 9375779281184566053421158616860022878844794559030854183778750394698195932446976

noncomputable def ep349 := BSN.sin_dyadic_bound_f 2731208286 2147483648 3 2 1048576 398796 ep346 ep64 ep347 ep348 ep66 ep347 1002058 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2731208286) qz285 0 2 ep346 ep64 ep347 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2731208286) qz286 0 2 ep348 ep66 ep347 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz370 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 111924379) qz32)

noncomputable def ep350 := @Enclosure.Real.IsNear.cos_image qz64 qz370 Bool.false 111924379 262144 751 1048576 Bool.false 1002058 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz64 Bool.false 240355773932720603067 562949953421312000 17815250014195404983 24900375000000000000000 111924379 262144 751 1048576 (ep345 rfl) rfl) (Enclosure.sfrac_false_div 111924379 262144) (BSN.cos_reduce3 qz370 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 48047924304502815981568) qz302) 226375608064910080 72057594037927936 Bool.false 1002058 1048576 67 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q3 111924379 262144 226375608064910080 72057594037927936 67 48047924304502815981568 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1002058 1048576 48047924304502815981568 37778931862957161709568 2731208286 2147483648 398796 398406 (ep349 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep351 := nat_lit 1991241149732942708256701797575422199707462639505061390800971225051145636577536

noncomputable def ep352 := nat_lit 5967530912822278355652947777190207180781410596172795971635160008707249642045696

noncomputable def ep353 := BSN.cos_dyadic_bound_f 2731208286 2147483648 3 2 1048576 398796 ep351 ep57 ep347 ep352 ep60 ep347 308851 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2731208286) qz281 0 2 ep351 ep57 ep347 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2731208286) qz282 0 2 ep352 ep60 ep347 rfl rfl rfl rfl) rfl rfl

noncomputable def ep354 := @Enclosure.Real.IsNear.sin_image qz64 qz370 Bool.false 111924379 262144 751 1048576 Bool.true 308851 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz64 Bool.false 240355773932720603067 562949953421312000 17815250014195404983 24900375000000000000000 111924379 262144 751 1048576 (ep345 rfl) rfl) (Enclosure.sfrac_false_div 111924379 262144) (BSN.sin_reduce3 qz370 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 48047924304502815981568) qz302) 226375608064910080 72057594037927936 Bool.false 308851 1048576 67 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q3 111924379 262144 226375608064910080 72057594037927936 67 48047924304502815981568 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 308851 1048576 48047924304502815981568 37778931862957161709568 2731208286 2147483648 398796 398406 (ep353 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz371 := (@Enclosure.Real.IsNear.recentre' qz63 Bool.false 234469 1048576 1 1048576 234469 1048576 1 1048576 (ep343 rfl rfl) rfl)

noncomputable def ep355 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz63 (Real.cos qz64)) (@HMul.hMul Real Real Real qz0 qz63 (@Neg.neg Real Real.instNeg (Real.sin qz64))) Bool.false 117475768601 549755813888 8880631314851 54756503696965632 Bool.false 72415985119 1099511627776 35384436345383 219026014787862528 (@Enclosure.Real.IsNear.mulLit_ff qz63 (Real.cos qz64) 234469 1048576 1 1048576 501029 524288 150650029 208879484928 117475768601 549755813888 8880631314851 54756503696965632 qz371 (@Enclosure.Real.IsNear.recentre' (Real.cos qz64) Bool.false 1002058 1048576 150650029 208879484928 501029 524288 150650029 208879484928 (ep350 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz63 (@Neg.neg Real Real.instNeg (Real.sin qz64)) 234469 1048576 1 1048576 308851 1048576 150650029 208879484928 72415985119 1099511627776 35384436345383 219026014787862528 qz371 (@Enclosure.Real.IsNear.neg (Real.sin qz64) Bool.true 308851 1048576 150650029 208879484928 (@Enclosure.Real.IsNear.recentre' (Real.sin qz64) Bool.true 308851 1048576 150650029 208879484928 308851 1048576 150650029 208879484928 (ep354 rfl rfl) rfl)) rfl)

noncomputable def ep356 := @ep302 117475768601 549755813888 8880631314851 54756503696965632 Bool.false 72415985119 1099511627776 35384436345383 219026014787862528 Bool.false 211631493477413941149696 96238861023 137438953472 261210757340981 54756503696965632 Bool.false 293750454052345247432704 66791120401 274877906944 522532651430083 109513007393931264 (ep303 (BSN.head_sum_c_succ qz5 19 20 rfl rfl) (ep341 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep342 ep355) rfl rfl

noncomputable abbrev qz372 := (@Nat.cast Real Real.instNatCast 21)

noncomputable abbrev qz65 := (@Inv.inv Real Real.instInv (Real.sqrt qz372))

noncomputable abbrev qz567 := (Real.log (Enclosure.sfrac Bool.false 21 1))

noncomputable abbrev qz66 := (@HMul.hMul Real Real Real qz267 qz278 qz567)

noncomputable def ep357 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz351 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz65 (Real.cos qz66)) (@HMul.hMul Real Real Real qz0 qz65 (@Neg.neg Real Real.instNeg (Real.sin qz66)))) Bool.false 111783656677 549755813888 17453292521879 109513007393931264 Bool.true 10886817213 137438953472 4333620718151 27378251848482816 (BSN.cpow_neg_s_mk qz13 142522 1000 21 qz14 rfl)

noncomputable abbrev qz373 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 21) qz15)

noncomputable def ep358 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz372) 4805179 1048576 1 1048576 114408 114410 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz372) (Real.sqrt qz373) Bool.false 4805179 1048576 1 1048576 (BSN.sqrt_natCast_div_one 21) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz373) Bool.false 4805179 1048576 1 1048576 4805179 1048576 1 1048576 (BSN.sqrt_enclosure 21 1 2402589 2402590 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep359 := BSN.log_dyadic_bound 5 37 4 3 269401272945 524288 199203 1658093375 234375 142571 42 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 5) (BSN.artanhQ 37) 0 3 1658093375 269401272945 234375 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep360 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz567 142522 1000 0 1 3427826275261687 1125899906842624 250000000199203 49800750000000000000 244270328201423077307 562949953421312000 17815250014195404983 24900375000000000000000 qz18 (BSN.isNear_log_sfrac 21 1 3427826275261687 1125899906842624 250000000199203 49800750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz373) Bool.false 57509381830540779323392 18889465931478580854784 1000000000796812 199203000000000000000 3427826275261687 1125899906842624 250000000199203 49800750000000000000 (BSN.log_rat_reduce_isNear 21 1 4 42 32 142571 524288 24973259072661432 36028797018963968 199203 1000000000000000 rfl rfl rfl rfl (ep359 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep361 := nat_lit 405010499884378325956314904338900625

noncomputable def ep362 := BSN.cos_dyadic_bound_f 797749555 2147483648 2 1 1048576 398796 ep361 ep184 ep361 ep361 ep185 ep361 977053 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 797749555) qz281 0 1 ep361 ep184 ep361 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 797749555) qz282 0 1 ep361 ep185 ep361 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz374 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 454988941) qz16)

noncomputable def ep363 := @Enclosure.Real.IsNear.cos_image qz66 qz374 Bool.false 454988941 1048576 47 65536 Bool.false 977053 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz66 Bool.false 244270328201423077307 562949953421312000 17815250014195404983 24900375000000000000000 454988941 1048576 47 65536 (ep360 rfl) rfl) (Enclosure.sfrac_false_div 454988941 1048576) (BSN.cos_reduce0 qz374 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 56136634422652905193472) qz19) 226375608064910080 72057594037927936 Bool.false 977053 1048576 69 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q0 454988941 1048576 226375608064910080 72057594037927936 69 56136634422652905193472 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 977053 1048576 56136634422652905193472 151115727451828646838272 797749555 2147483648 398796 398406 (ep362 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep364 := BSN.sin_dyadic_bound_f 797749555 2147483648 2 1 1048576 398796 ep361 ep180 ep361 ep361 ep181 ep361 380628 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 797749555) qz285 0 1 ep361 ep180 ep361 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 797749555) qz286 0 1 ep361 ep181 ep361 rfl rfl rfl rfl) rfl rfl

noncomputable def ep365 := @Enclosure.Real.IsNear.sin_image qz66 qz374 Bool.false 454988941 1048576 47 65536 Bool.false 380628 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz66 Bool.false 244270328201423077307 562949953421312000 17815250014195404983 24900375000000000000000 454988941 1048576 47 65536 (ep360 rfl) rfl) (Enclosure.sfrac_false_div 454988941 1048576) (BSN.sin_reduce0 qz374 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 56136634422652905193472) qz19) 226375608064910080 72057594037927936 Bool.false 380628 1048576 69 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q0 454988941 1048576 226375608064910080 72057594037927936 69 56136634422652905193472 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 380628 1048576 56136634422652905193472 151115727451828646838272 797749555 2147483648 398796 398406 (ep364 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz375 := (@Enclosure.Real.IsNear.recentre' qz65 Bool.false 228818 1048576 2 1048576 114409 524288 1 524288 (ep358 rfl rfl) rfl)

noncomputable def ep366 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz65 (Real.cos qz66)) (@HMul.hMul Real Real Real qz0 qz65 (@Neg.neg Real Real.instNeg (Real.sin qz66))) Bool.false 111783656677 549755813888 17453292521879 109513007393931264 Bool.true 10886817213 137438953472 4333620718151 27378251848482816 (@Enclosure.Real.IsNear.mulLit_ff qz65 (Real.cos qz66) 114409 524288 1 524288 977053 1048576 9428077 13054967808 111783656677 549755813888 17453292521879 109513007393931264 qz375 (@Enclosure.Real.IsNear.recentre' (Real.cos qz66) Bool.false 977053 1048576 9428077 13054967808 977053 1048576 9428077 13054967808 (ep363 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz65 (@Neg.neg Real Real.instNeg (Real.sin qz66)) 114409 524288 1 524288 95157 262144 9428077 13054967808 10886817213 137438953472 4333620718151 27378251848482816 qz375 (@Enclosure.Real.IsNear.neg (Real.sin qz66) Bool.false 95157 262144 9428077 13054967808 (@Enclosure.Real.IsNear.recentre' (Real.sin qz66) Bool.false 380628 1048576 9428077 13054967808 95157 262144 9428077 13054967808 (ep365 rfl rfl) rfl)) rfl)

noncomputable def ep367 := @ep300 111783656677 549755813888 17453292521879 109513007393931264 Bool.true 10886817213 137438953472 4333620718151 27378251848482816 Bool.false 68271302158313710419968 496739100769 549755813888 179958269067947 36504335797977088 Bool.false 6187156160344437555200 45017485975 274877906944 179955711434229 36504335797977088 (ep301 (BSN.head_sum_c_succ qz5 20 21 rfl rfl) (ep356 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep357 ep366) rfl rfl

noncomputable abbrev qz376 := (@Nat.cast Real Real.instNatCast 22)

noncomputable abbrev qz67 := (@Inv.inv Real Real.instInv (Real.sqrt qz376))

noncomputable abbrev qz568 := (Real.log (Enclosure.sfrac Bool.false 22 1))

noncomputable abbrev qz68 := (@HMul.hMul Real Real Real qz267 qz278 qz568)

noncomputable def ep368 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz350 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz67 (Real.cos qz68)) (@HMul.hMul Real Real Real qz0 qz67 (@Neg.neg Real Real.instNeg (Real.sin qz68)))) Bool.false 176474330901 1099511627776 33836268636961 219026014787862528 Bool.true 77148850029 549755813888 8454126974641 54756503696965632 (BSN.cpow_neg_s_mk qz13 142522 1000 22 qz14 rfl)

noncomputable abbrev qz377 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 22) qz15)

noncomputable def ep369 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz376) 4918257 1048576 1 1048576 111778 111779 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz376) (Real.sqrt qz377) Bool.false 4918257 1048576 1 1048576 (BSN.sqrt_natCast_div_one 22) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz377) Bool.false 4918257 1048576 1 1048576 4918257 1048576 1 1048576 (BSN.sqrt_enclosure 22 1 2459128 2459129 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep370 := BSN.log_dyadic_bound 6 38 4 3 316148320320 524288 199203 2667271104 699840 166961 44 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 6) (BSN.artanhQ 38) 0 3 2667271104 316148320320 699840 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep371 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz568 142522 1000 0 1 3480203401436407 1125899906842624 250000000199203 49800750000000000000 248002774589759799227 562949953421312000 17815250014195404983 24900375000000000000000 qz18 (BSN.isNear_log_sfrac 22 1 3480203401436407 1125899906842624 250000000199203 49800750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz377) Bool.false 58388124189833310502912 18889465931478580854784 1000000000796812 199203000000000000000 3480203401436407 1125899906842624 250000000199203 49800750000000000000 (BSN.log_rat_reduce_isNear 22 1 4 44 32 166961 524288 24973259072661432 36028797018963968 199203 1000000000000000 rfl rfl rfl rfl (ep370 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep372 := nat_lit 202493519240612939379880550718483362927083458491092318899739158872961409657441

noncomputable def ep373 := nat_lit 32109018249821462912382914595940460284400505227153885251663832164132760161

noncomputable def ep374 := nat_lit 607416339685339175213816886326258207860681574462822648928714148954555963452001

noncomputable def ep375 := BSN.cos_dyadic_bound_f 1542866603 2147483648 3 2 1048576 398796 ep372 ep57 ep373 ep374 ep60 ep373 789393 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1542866603) qz281 0 2 ep372 ep57 ep373 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1542866603) qz282 0 2 ep374 ep60 ep373 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz378 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 461941165) qz16)

noncomputable def ep376 := @Enclosure.Real.IsNear.cos_image qz68 qz378 Bool.false 461941165 1048576 751 1048576 Bool.false 789393 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz68 Bool.false 248002774589759799227 562949953421312000 17815250014195404983 24900375000000000000000 461941165 1048576 751 1048576 (ep371 rfl) rfl) (Enclosure.sfrac_false_div 461941165 1048576) (BSN.cos_reduce0 qz378 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 108569585319047310868480) qz19) 226375608064910080 72057594037927936 Bool.false 789393 1048576 70 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q0 461941165 1048576 226375608064910080 72057594037927936 70 108569585319047310868480 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 789393 1048576 108569585319047310868480 151115727451828646838272 1542866603 2147483648 398796 398406 (ep375 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep377 := nat_lit 5666481999426228029318164279141832881

noncomputable def ep378 := BSN.sin_dyadic_bound_f 1542866603 2147483648 2 1 1048576 398796 ep377 ep180 ep377 ep377 ep181 ep377 690194 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1542866603) qz285 0 1 ep377 ep180 ep377 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1542866603) qz286 0 1 ep377 ep181 ep377 rfl rfl rfl rfl) rfl rfl

noncomputable def ep379 := @Enclosure.Real.IsNear.sin_image qz68 qz378 Bool.false 461941165 1048576 751 1048576 Bool.false 690194 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz68 Bool.false 248002774589759799227 562949953421312000 17815250014195404983 24900375000000000000000 461941165 1048576 751 1048576 (ep371 rfl) rfl) (Enclosure.sfrac_false_div 461941165 1048576) (BSN.sin_reduce0 qz378 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 108569585319047310868480) qz19) 226375608064910080 72057594037927936 Bool.false 690194 1048576 70 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q0 461941165 1048576 226375608064910080 72057594037927936 70 108569585319047310868480 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 690194 1048576 108569585319047310868480 151115727451828646838272 1542866603 2147483648 398796 398406 (ep378 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz379 := (@Enclosure.Real.IsNear.recentre' qz67 Bool.false 223557 1048576 1 1048576 223557 1048576 1 1048576 (ep369 rfl rfl) rfl)

noncomputable def ep380 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz67 (Real.cos qz68)) (@HMul.hMul Real Real Real qz0 qz67 (@Neg.neg Real Real.instNeg (Real.sin qz68))) Bool.false 176474330901 1099511627776 33836268636961 219026014787862528 Bool.true 77148850029 549755813888 8454126974641 54756503696965632 (@Enclosure.Real.IsNear.mulLit_ff qz67 (Real.cos qz68) 223557 1048576 1 1048576 789393 1048576 150650029 208879484928 176474330901 1099511627776 33836268636961 219026014787862528 qz379 (@Enclosure.Real.IsNear.recentre' (Real.cos qz68) Bool.false 789393 1048576 150650029 208879484928 789393 1048576 150650029 208879484928 (ep376 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz67 (@Neg.neg Real Real.instNeg (Real.sin qz68)) 223557 1048576 1 1048576 345097 524288 150650029 208879484928 77148850029 549755813888 8454126974641 54756503696965632 qz379 (@Enclosure.Real.IsNear.neg (Real.sin qz68) Bool.false 345097 524288 150650029 208879484928 (@Enclosure.Real.IsNear.recentre' (Real.sin qz68) Bool.false 690194 1048576 150650029 208879484928 345097 524288 150650029 208879484928 (ep379 rfl rfl) rfl)) rfl)

noncomputable def ep381 := @ep298 176474330901 1099511627776 33836268636961 219026014787862528 Bool.true 77148850029 549755813888 8454126974641 54756503696965632 Bool.false 643188206681329166712832 1169952532439 1099511627776 1113585883044643 219026014787862528 Bool.false 3542110222269676519424 12886121921 549755813888 556775388251969 109513007393931264 (ep299 (BSN.head_sum_c_succ qz5 21 22 rfl rfl) (ep367 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep368 ep380) rfl rfl

noncomputable abbrev qz380 := (@Nat.cast Real Real.instNatCast 23)

noncomputable abbrev qz69 := (@Inv.inv Real Real.instInv (Real.sqrt qz380))

noncomputable abbrev qz569 := (Real.log (Enclosure.sfrac Bool.false 23 1))

noncomputable abbrev qz70 := (@HMul.hMul Real Real Real qz267 qz278 qz569)

noncomputable def ep382 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz349 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz69 (Real.cos qz70)) (@HMul.hMul Real Real Real qz0 qz69 (@Neg.neg Real Real.instNeg (Real.sin qz70)))) Bool.false 82257213531 549755813888 16544306025389 109513007393931264 Bool.true 79838584665 549755813888 16542102441803 109513007393931264 (BSN.cpow_neg_s_mk qz13 142522 1000 23 qz14 rfl)

noncomputable abbrev qz381 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 23) qz15)

noncomputable def ep383 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz380) 5028793 1048576 1 1048576 109321 109322 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz380) (Real.sqrt qz381) Bool.false 5028793 1048576 1 1048576 (BSN.sqrt_natCast_div_one 23) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz381) Bool.false 5028793 1048576 1 1048576 5028793 1048576 1 1048576 (BSN.sqrt_enclosure 23 1 2514396 2514397 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep384 := BSN.log_dyadic_bound 7 39 4 3 369468094905 524288 199203 4046006391 1764735 190266 46 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 7) (BSN.artanhQ 39) 0 3 4046006391 369468094905 1764735 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep385 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz569 142522 1000 0 1 3530250507853047 1125899906842624 250000000199203 49800750000000000000 251569181440115982267 562949953421312000 17815250014195404983 24900375000000000000000 qz18 (BSN.isNear_log_sfrac 23 1 3530250507853047 1125899906842624 250000000199203 49800750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz381) Bool.false 59227775304360265777152 18889465931478580854784 1000000000796812 199203000000000000000 3530250507853047 1125899906842624 250000000199203 49800750000000000000 (BSN.log_rat_reduce_isNear 23 1 4 46 32 190266 524288 24973259072661432 36028797018963968 199203 1000000000000000 rfl rfl rfl rfl (ep384 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep386 := nat_lit 267844009820855243996625627069548054544388868483173976599858871863205042094336

noncomputable def ep387 := nat_lit 56172558786782713770371423353883878346421702342837898382176221382627328256

noncomputable def ep388 := nat_lit 803419684344992166562336138361936395876473762044836254002812263146849871626496

noncomputable def ep389 := BSN.cos_dyadic_bound_f 1654590498 2147483648 3 2 1048576 398796 ep386 ep57 ep387 ep388 ep60 ep387 752434 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1654590498) qz281 0 2 ep386 ep57 ep387 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1654590498) qz282 0 2 ep388 ep60 ep387 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz382 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 468584115) qz16)

noncomputable def ep390 := @Enclosure.Real.IsNear.cos_image qz70 qz382 Bool.false 468584115 1048576 751 1048576 Bool.false 752434 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz70 Bool.false 251569181440115982267 562949953421312000 17815250014195404983 24900375000000000000000 468584115 1048576 751 1048576 (ep385 rfl) rfl) (Enclosure.sfrac_false_div 468584115 1048576) (BSN.cos_reduce0 qz382 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 116431455538469467586560) qz19) 226375608064910080 72057594037927936 Bool.false 752434 1048576 71 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q0 468584115 1048576 226375608064910080 72057594037927936 71 116431455538469467586560 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 752434 1048576 116431455538469467586560 151115727451828646838272 1654590498 2147483648 398796 398406 (ep389 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep391 := nat_lit 7494835474297131878994141613119104016

noncomputable def ep392 := BSN.sin_dyadic_bound_f 1654590498 2147483648 2 1 1048576 398796 ep391 ep180 ep391 ep391 ep181 ep391 730310 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1654590498) qz285 0 1 ep391 ep180 ep391 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1654590498) qz286 0 1 ep391 ep181 ep391 rfl rfl rfl rfl) rfl rfl

noncomputable def ep393 := @Enclosure.Real.IsNear.sin_image qz70 qz382 Bool.false 468584115 1048576 751 1048576 Bool.false 730310 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz70 Bool.false 251569181440115982267 562949953421312000 17815250014195404983 24900375000000000000000 468584115 1048576 751 1048576 (ep385 rfl) rfl) (Enclosure.sfrac_false_div 468584115 1048576) (BSN.sin_reduce0 qz382 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 116431455538469467586560) qz19) 226375608064910080 72057594037927936 Bool.false 730310 1048576 71 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q0 468584115 1048576 226375608064910080 72057594037927936 71 116431455538469467586560 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 730310 1048576 116431455538469467586560 151115727451828646838272 1654590498 2147483648 398796 398406 (ep392 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz383 := (@Enclosure.Real.IsNear.recentre' qz69 Bool.false 218643 1048576 1 1048576 218643 1048576 1 1048576 (ep383 rfl rfl) rfl)

noncomputable def ep394 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz69 (Real.cos qz70)) (@HMul.hMul Real Real Real qz0 qz69 (@Neg.neg Real Real.instNeg (Real.sin qz70))) Bool.false 82257213531 549755813888 16544306025389 109513007393931264 Bool.true 79838584665 549755813888 16542102441803 109513007393931264 (@Enclosure.Real.IsNear.mulLit_ff qz69 (Real.cos qz70) 218643 1048576 1 1048576 376217 524288 150650029 208879484928 82257213531 549755813888 16544306025389 109513007393931264 qz383 (@Enclosure.Real.IsNear.recentre' (Real.cos qz70) Bool.false 752434 1048576 150650029 208879484928 376217 524288 150650029 208879484928 (ep390 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz69 (@Neg.neg Real Real.instNeg (Real.sin qz70)) 218643 1048576 1 1048576 365155 524288 150650029 208879484928 79838584665 549755813888 16542102441803 109513007393931264 qz383 (@Enclosure.Real.IsNear.neg (Real.sin qz70) Bool.false 365155 524288 150650029 208879484928 (@Enclosure.Real.IsNear.recentre' (Real.sin qz70) Bool.false 730310 1048576 150650029 208879484928 365155 524288 150650029 208879484928 (ep393 rfl rfl) rfl)) rfl)

noncomputable def ep395 := @ep296 82257213531 549755813888 16544306025389 109513007393931264 Bool.true 79838584665 549755813888 16542102441803 109513007393931264 Bool.false 733630969427116989349888 1334466959501 1099511627776 1146674495095421 219026014787862528 Bool.true 36807505647633717788672 8369057843 68719476736 143329372673443 27378251848482816 (ep297 (BSN.head_sum_c_succ qz5 22 23 rfl rfl) (ep381 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep382 ep394) rfl rfl

noncomputable abbrev qz384 := (@Nat.cast Real Real.instNatCast 24)

noncomputable abbrev qz71 := (@Inv.inv Real Real.instInv (Real.sqrt qz384))

noncomputable abbrev qz570 := (Real.log (Enclosure.sfrac Bool.false 24 1))

noncomputable abbrev qz72 := (@HMul.hMul Real Real Real qz267 qz278 qz570)

noncomputable def ep396 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz348 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz71 (Real.cos qz72)) (@HMul.hMul Real Real Real qz0 qz71 (@Neg.neg Real Real.instNeg (Real.sin qz72)))) Bool.false 95485580407 549755813888 16211433151519 109513007393931264 Bool.true 14738083423 137438953472 2022179023433 13689125924241408 (BSN.cpow_neg_s_mk qz13 142522 1000 24 qz14 rfl)

noncomputable abbrev qz385 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 24) qz15)

noncomputable def ep397 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz384) 5136953 1048576 1 1048576 107019 107020 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz384) (Real.sqrt qz385) Bool.false 5136953 1048576 1 1048576 (BSN.sqrt_natCast_div_one 24) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz385) Bool.false 5136953 1048576 1 1048576 5136953 1048576 1 1048576 (BSN.sqrt_enclosure 24 1 2568476 2568477 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep398 := BSN.log_dyadic_bound 8 40 4 3 430080000000 524288 199203 5875957760 3932160 212580 48 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 8) (BSN.artanhQ 40) 0 3 5875957760 430080000000 3932160 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep399 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz570 142522 1000 0 1 3578169457974519 1125899906842624 250000000199203 49800750000000000000 254983933744722198459 562949953421312000 17815250014195404983 24900375000000000000000 qz18 (BSN.isNear_log_sfrac 24 1 3578169457974519 1125899906842624 250000000199203 49800750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz385) Bool.false 60031721881041427759104 18889465931478580854784 1000000000796812 199203000000000000000 3578169457974519 1125899906842624 250000000199203 49800750000000000000 (BSN.log_rat_reduce_isNear 24 1 4 48 32 212580 524288 24973259072661432 36028797018963968 199203 1000000000000000 rfl rfl rfl rfl (ep398 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep400 := nat_lit 1990547196859488391754119191506250000

noncomputable def ep401 := BSN.cos_dyadic_bound_f 1187799450 2147483648 2 1 1048576 398796 ep400 ep184 ep400 ep400 ep185 ep400 892226 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1187799450) qz281 0 1 ep400 ep184 ep400 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1187799450) qz282 0 1 ep400 ep185 ep400 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz386 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 474944587) qz16)

noncomputable def ep402 := @Enclosure.Real.IsNear.cos_image qz72 qz386 Bool.false 474944587 1048576 751 1048576 Bool.false 892226 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz72 Bool.false 254983933744722198459 562949953421312000 17815250014195404983 24900375000000000000000 474944587 1048576 751 1048576 (ep399 rfl) rfl) (Enclosure.sfrac_false_div 474944587 1048576) (BSN.cos_reduce0 qz386 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 83583955660600009293824) qz19) 226375608064910080 72057594037927936 Bool.false 892226 1048576 72 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q0 474944587 1048576 226375608064910080 72057594037927936 72 83583955660600009293824 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 892226 1048576 83583955660600009293824 151115727451828646838272 1187799450 2147483648 398796 398406 (ep401 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep403 := BSN.sin_dyadic_bound_f 1187799450 2147483648 2 1 1048576 398796 ep400 ep180 ep400 ep400 ep181 ep400 550856 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1187799450) qz285 0 1 ep400 ep180 ep400 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1187799450) qz286 0 1 ep400 ep181 ep400 rfl rfl rfl rfl) rfl rfl

noncomputable def ep404 := @Enclosure.Real.IsNear.sin_image qz72 qz386 Bool.false 474944587 1048576 751 1048576 Bool.false 550856 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz72 Bool.false 254983933744722198459 562949953421312000 17815250014195404983 24900375000000000000000 474944587 1048576 751 1048576 (ep399 rfl) rfl) (Enclosure.sfrac_false_div 474944587 1048576) (BSN.sin_reduce0 qz386 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 83583955660600009293824) qz19) 226375608064910080 72057594037927936 Bool.false 550856 1048576 72 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q0 474944587 1048576 226375608064910080 72057594037927936 72 83583955660600009293824 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 550856 1048576 83583955660600009293824 151115727451828646838272 1187799450 2147483648 398796 398406 (ep403 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz387 := (@Enclosure.Real.IsNear.recentre' qz71 Bool.false 214039 1048576 1 1048576 214039 1048576 1 1048576 (ep397 rfl rfl) rfl)

noncomputable def ep405 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz71 (Real.cos qz72)) (@HMul.hMul Real Real Real qz0 qz71 (@Neg.neg Real Real.instNeg (Real.sin qz72))) Bool.false 95485580407 549755813888 16211433151519 109513007393931264 Bool.true 14738083423 137438953472 2022179023433 13689125924241408 (@Enclosure.Real.IsNear.mulLit_ff qz71 (Real.cos qz72) 214039 1048576 1 1048576 446113 524288 150650029 208879484928 95485580407 549755813888 16211433151519 109513007393931264 qz387 (@Enclosure.Real.IsNear.recentre' (Real.cos qz72) Bool.false 892226 1048576 150650029 208879484928 446113 524288 150650029 208879484928 (ep402 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz71 (@Neg.neg Real Real.instNeg (Real.sin qz72)) 214039 1048576 1 1048576 68857 131072 150650029 208879484928 14738083423 137438953472 2022179023433 13689125924241408 qz387 (@Enclosure.Real.IsNear.neg (Real.sin qz72) Bool.false 68857 131072 150650029 208879484928 (@Enclosure.Real.IsNear.recentre' (Real.sin qz72) Bool.false 550856 1048576 150650029 208879484928 68857 131072 150650029 208879484928 (ep404 rfl rfl) rfl)) rfl)

noncomputable def ep406 := @ep294 95485580407 549755813888 16211433151519 109513007393931264 Bool.true 14738083423 137438953472 2022179023433 13689125924241408 Bool.false 838618475369553691934720 1525438120315 1099511627776 1179097361398459 219026014787862528 Bool.true 2163027932408629428224 31476199109 137438953472 147373730720309 27378251848482816 (ep295 (BSN.head_sum_c_succ qz5 23 24 rfl rfl) (ep395 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep396 ep405) rfl rfl

theorem EMRow50.d8 : Enclosure.Complex.IsNear qz56 Bool.false 1525438120315 1099511627776 1179097361398459 219026014787862528 Bool.true 31476199109 137438953472 147373730720309 27378251848482816 := ep293 (BSN.head_sum_c_succ qz5 24 25 rfl rfl) (ep406 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

theorem EMRow50.d9 : @Eq Nat (BSN.factNat (Nat.mul 2 1)) 2 := @Eq.refl Nat 2

theorem EMRow50.d10 : @Eq Nat (Nat.pow 29 1) 29 := @Eq.refl Nat 29

noncomputable def ep407 := nat_lit 26398118555851423038655224156297

noncomputable def ep408 := nat_lit 16978796684131452676838155878400

noncomputable def ep409 := nat_lit 44855661593594206998177027658899374048567

noncomputable def ep410 := nat_lit 6737498120668199304160736327301234425856000

noncomputable abbrev qz611 := (@instHMul Complex Complex.instMul)

noncomputable abbrev qz571 := qz611

noncomputable abbrev qz388 := qz571

noncomputable abbrev qz73 := qz388

noncomputable abbrev qz572 := (@instHSub Complex Complex.instSub)

noncomputable abbrev qz389 := qz572

noncomputable abbrev qz74 := qz389

noncomputable abbrev qz612 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (4 : Complex))

noncomputable abbrev qz613 := (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid))

noncomputable abbrev qz573 := (@HAdd.hAdd Complex Complex Complex qz609 (@HAdd.hAdd Complex Complex Complex qz609 qz612 (@HMul.hMul Complex Complex Complex qz611 Complex.I (@HDiv.hDiv Complex Complex Complex qz613 (↑qz610) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz390 := qz573

noncomputable abbrev qz75 := (Complex.Stirling.logGammaStirling 1 qz390)

noncomputable abbrev qz574 := (@HAdd.hAdd Complex Complex Complex qz609 qz612 (@HMul.hMul Complex Complex Complex qz611 Complex.I (@HDiv.hDiv Complex Complex Complex qz613 (↑qz610) (2 : Complex))))

noncomputable abbrev qz391 := qz574

noncomputable abbrev qz76 := qz391

noncomputable abbrev qz77 := (@HMul.hMul Real Real Real qz267 (@HDiv.hDiv Real Real Real qz270 qz278 (2 : Real)) (Real.log Real.pi))

noncomputable abbrev qz392 := (@instHSub Real Real.instSub)

noncomputable def ep411 := Complex.re (@HMul.hMul Complex Complex Complex qz73 (Complex.exp (@HMul.hMul Complex Complex Complex qz73 Complex.I ↑(@HSub.hSub Real Real Real qz392 (Complex.im (@HSub.hSub Complex Complex Complex qz74 qz75 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz76 (@Nat.cast Complex Complex.instNatCast j))))) qz77))) (zetaApproximant qz5 1 29))

noncomputable def ep412 := @Enclosure.Real.IsNear.of_eq ep411 (@HSub.hSub Real Real Real qz392 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz392 (Complex.im (@HSub.hSub Complex Complex Complex qz74 qz75 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz76 (@Nat.cast Complex Complex.instNatCast j))))) qz77)) (Complex.re (zetaApproximant qz5 1 29))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz392 (Complex.im (@HSub.hSub Complex Complex Complex qz74 qz75 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz76 (@Nat.cast Complex Complex.instNatCast j))))) qz77)) (Complex.im (zetaApproximant qz5 1 29))))

noncomputable def ep413 := nat_lit 4223650937643323020742375640183

noncomputable def ep414 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz392 (Complex.im (@HSub.hSub Complex Complex Complex qz74 qz75 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz76 (@Nat.cast Complex Complex.instNatCast j))))) qz77)) (Complex.re (zetaApproximant qz5 1 29))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz392 (Complex.im (@HSub.hSub Complex Complex Complex qz74 qz75 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz76 (@Nat.cast Complex Complex.instNatCast j))))) qz77)) (Complex.im (zetaApproximant qz5 1 29))) ep413

noncomputable def ep415 := nat_lit 2716607469461032428294104940544

noncomputable def ep416 := nat_lit 1985431417550580539083939044217215996497

noncomputable def ep417 := nat_lit 299444360918586635740477170102277085593600

noncomputable def ep418 := nat_lit 1200782322616636061505620613

noncomputable def ep419 := nat_lit 67915186736525810707352623513600

noncomputable def ep420 := nat_lit 366909397412289737576798328024028254769

noncomputable def ep421 := nat_lit 13474996241336398608321472654602468851712000

noncomputable def ep422 := nat_lit 286853304194175432725157239671896621384145375653274886992822272

noncomputable def ep423 := @Enclosure.Real.IsNear.mulLit_ff (Real.cos (@HSub.hSub Real Real Real qz392 (Complex.im (@HSub.hSub Complex Complex Complex qz74 qz75 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz76 (@Nat.cast Complex Complex.instNatCast j))))) qz77)) (Complex.re (zetaApproximant qz5 1 29)) 1048575 1048576 39368873

noncomputable def ep424 := nat_lit 100699781552185657219139681

noncomputable def ep425 := nat_lit 64768969284559069354393600

noncomputable def ep426 := nat_lit 5197033367558903111986074403

noncomputable def ep427 := nat_lit 860144865892801352840217886720

noncomputable def ep428 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz392 (Complex.im (@HSub.hSub Complex Complex Complex qz74 qz75 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz76 (@Nat.cast Complex Complex.instNatCast j))))) qz77)) Bool.false 1048575 1048576 39368873

noncomputable abbrev qz393 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 79060617) qz37)

noncomputable def ep429 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz392 (Complex.im (@HSub.hSub Complex Complex Complex qz74 qz75 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz76 (@Nat.cast Complex Complex.instNatCast j))))) qz77) qz393 Bool.false 79060617 524288 195

noncomputable def ep430 := nat_lit 12904772068659189671916083

noncomputable def ep431 := nat_lit 34813247488000000000000000000

noncomputable def ep432 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz392 (Complex.im (@HSub.hSub Complex Complex Complex qz74 qz75 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz76 (@Nat.cast Complex Complex.instNatCast j))))) qz77) Bool.false 339562765299461339769 2251799813685248000 ep430 ep431

noncomputable def ep433 := nat_lit 3441168746659189671916083

noncomputable def ep434 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz74 qz75 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz76 (@Nat.cast Complex Complex.instNatCast j))))) qz77 523252382683247622777 2251799813685248000 ep433 ep431 5346071481 65536000

noncomputable def ep435 := nat_lit 22253585386665498363101184000

noncomputable def ep436 := nat_lit 9685685574732985437542401

noncomputable def ep437 := nat_lit 52219871232000000000000000000

noncomputable def ep438 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz74 qz75 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz76 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 126195613783035120191 1125899906842624000 ep436 ep437 Bool.false 523252382683247622777 2251799813685248000

noncomputable def ep439 := nat_lit 9554613574106346982758401

noncomputable def ep440 := nat_lit 9799218239873129273284249

noncomputable def ep441 := @Enclosure.Complex.IsNear.subLitP qz75 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz76 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 116588469899802123191 1125899906842624000 ep439 ep437 Bool.false 530279227618648350777 2251799813685248000 ep440

noncomputable def ep442 := nat_lit 104439742464000000000000000000

noncomputable def ep443 := nat_lit 142083629802266999086061787161821184

noncomputable def ep444 := nat_lit 147282452229562385491359150964211712

noncomputable abbrev qz614 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex))

noncomputable abbrev qz575 := qz614

noncomputable abbrev qz394 := (@HSub.hSub Complex Complex Complex qz572 qz573 qz575)

noncomputable abbrev qz395 := (Complex.log qz573)

noncomputable abbrev qz78 := (@HSub.hSub Complex Complex Complex qz389 (@HMul.hMul Complex Complex Complex qz388 qz394 qz395) qz390)

noncomputable abbrev qz396 := qz575

noncomputable abbrev qz79 := (@HMul.hMul Complex Complex Complex qz388 qz396 ↑(Real.log (@HMul.hMul Real Real Real qz267 (2 : Real) Real.pi)))

noncomputable abbrev qz576 := qz613

noncomputable abbrev qz397 := qz576

noncomputable abbrev qz80 := qz397

noncomputable abbrev qz81 := (@instHMul Nat instMulNat)

noncomputable abbrev qz577 := (@instHPow Complex Int (@ZPow.toPow Complex (@DivInvMonoid.toZPow Complex Complex.instDivInvMonoid)))

noncomputable abbrev qz398 := qz577

noncomputable abbrev qz82 := qz398

noncomputable abbrev qz83 := qz390

noncomputable abbrev qz84 := (@OfNat.ofNat Int 1 (@instOfNat 1))

noncomputable abbrev qz85 := (@OfNat.ofNat Int 2 (@instOfNat 2))

noncomputable abbrev qz399 := (@instHSub Int Int.instSub)

noncomputable abbrev qz400 := (@instHMul Int Int.instMul)

noncomputable def ep445 := @Enclosure.Complex.IsNear.of_eq qz75 (@HAdd.hAdd Complex Complex Complex qz4 (@HAdd.hAdd Complex Complex Complex qz4 qz78 qz79) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz81 2 k))) (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz73 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz82 qz83 (@HSub.hSub Int Int Int qz399 qz84 (@HMul.hMul Int Int Int qz400 qz85 (@Nat.cast Int instNatCastInt k)))))) Bool.true 116588469899802123191

noncomputable def ep446 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz4 qz78 qz79) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz81 2 k))) (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz73 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz82 qz83 (@HSub.hSub Int Int Int qz399 qz84 (@HMul.hMul Int Int Int qz400 qz85 (@Nat.cast Int instNatCastInt k))))) Bool.true 116588511430047243191 1125899906842624000

noncomputable def ep447 := nat_lit 8011898644965288255627330584576

noncomputable def ep448 := nat_lit 1822025552296187701049240951193600

noncomputable def ep449 := @ep446 36447949578891482429 199203000000000000000000 Bool.false 530281858273579458617 2251799813685248000 18690250085346732523 199203000000000000000000 Bool.false 2534805 68719476736 3 68719476736 Bool.true 4014060869 3435973836800 71261 51539607552000 Bool.true ep447 116588469899802123191 1125899906842624000 ep439 ep437 Bool.false ep448

noncomputable def ep450 := @Enclosure.Complex.IsNear.addLitP qz78 qz79 Bool.true 117623143281849867191 1125899906842624000 72136000018378667983 398406000000000000000000

noncomputable def ep451 := nat_lit 15281489370159152259530752

noncomputable def ep452 := @ep450 Bool.false 530281858273579458617 2251799813685248000 18690250085346732523 199203000000000000000000 Bool.false 120447 131072 1 524288 Bool.false 0 1 0 1 Bool.true ep451 116588511430047243191 1125899906842624000 36447949578891482429 199203000000000000000000 Bool.false 530281858273579458617 530281858273579458617 2251799813685248000

noncomputable abbrev qz86 := (@HMul.hMul Complex Complex Complex qz388 qz394 qz395)

noncomputable def ep453 := @Enclosure.Complex.IsNear.subLitP qz86 qz83 Bool.true 115089868491453963191 1125899906842624000 72136000018378667983 398406000000000000000000 Bool.false 138149472959320783269

noncomputable def ep454 := @ep453 450359962737049600 18690250085346732523 199203000000000000000000 Bool.false 9000 4000 0 1 Bool.false 285044 4000 0 1 Bool.true 470492573127399468764000 117623143281849867191 1125899906842624000 72136000018378667983 398406000000000000000000 Bool.false 424225486618863566893600 530281858273579458617 2251799813685248000 18690250085346732523 199203000000000000000000

noncomputable abbrev qz87 := qz394

noncomputable abbrev qz88 := qz395

noncomputable def ep455 := @Enclosure.Complex.IsNear.mul qz87 qz88 Bool.true 115089868491453963191 1125899906842624000 72136000018378667983 398406000000000000000000 Bool.false 138149472959320783269 450359962737049600 18690250085346732523

noncomputable abbrev qz89 := (Complex.re qz394)

noncomputable abbrev qz90 := (Complex.re qz395)

noncomputable abbrev qz91 := (Complex.im qz394)

noncomputable abbrev qz92 := (Complex.im qz395)

noncomputable def ep456 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz89 qz90) (@HMul.hMul Real Real Real qz0 qz91 qz92) 67256598883688515 9007199254740992 875000004183263 398406000000000000000 61748471675957513783 562949953421312000

noncomputable def ep457 := nat_lit 518318688852231457231269057303412736

noncomputable def ep458 := @Enclosure.Real.IsNear.mulLit_ff qz89 qz90 7000 4000 0 1 9608085554812645 2251799813685248 125000000597609 99601500000000000000

noncomputable def ep459 := @Enclosure.Complex.IsNear.re_isNear qz87 Bool.false 7000 4000 0 1 Bool.false 285044 4000 0 1

noncomputable abbrev qz93 := (Enclosure.sfrac Bool.false 285044 4000)

noncomputable def ep460 := @Enclosure.Complex.IsNear.of_eq qz87 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz93) Bool.false 7000 4000 0 1 Bool.false 285044 4000 0

noncomputable abbrev qz578 := (Enclosure.sfrac Bool.false 9000 4000)

noncomputable abbrev qz401 := (Complex.log (Complex.mk qz578 qz93))

noncomputable def ep461 := @Enclosure.Complex.IsNear.of_eq qz88 qz401 Bool.false 9608085554812645 2251799813685248 125000000597609 99601500000000000000 Bool.false 866511439300003 562949953421312 1000000000199203 398406000000000000000

noncomputable def ep462 := nat_lit 6978934516418121119306957590566990474983178240

noncomputable def ep463 := nat_lit 27093568119066231168646105666746753420361728

noncomputable def ep464 := nat_lit 186727716917581015781510750302731412635648

noncomputable def ep465 := BSN.log_dyadic_bound 15795081936 146867081936 3 2 ep462 1048576 398406 ep463 ep464 226417 162662163872 131072000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 15795081936) (BSN.artanhQ 146867081936) 0 2 ep463 ep462 ep464 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz94 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz402 := (Enclosure.Real.IsNear.const Bool.false 1 2)

noncomputable abbrev qz403 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable abbrev qz579 := (Real.log (Enclosure.sfrac Bool.false 81331081936 16000000))

noncomputable def ep466 := @Enclosure.Real.IsNear.mulLit_ff qz94 qz579 1 2 0 1 9608085554812645 1125899906842624 125000000597609 49800750000000000000 9608085554812645 2251799813685248 125000000597609 99601500000000000000 qz402 (BSN.isNear_log_sfrac 81331081936 16000000 9608085554812645 1125899906842624 125000000597609 49800750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 81331081936) qz403)) Bool.false 322393853399143169392640 37778931862957161709568 1000000004780872 398406000000000000000 9608085554812645 1125899906842624 125000000597609 49800750000000000000 (BSN.log_rat_reduce_isNear 81331081936 16000000 12 162662163872 131072000000 226417 1048576 24973259072661432 36028797018963968 398406 1000000000000000 rfl rfl rfl rfl (ep465 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep467 := BSN.arctan_dyadic_bound_f 9000 285044 1 0 1048576 398406 0 1 1 0 1 1 33096 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 285044) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 285044) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz95 := (@HMul.hMul Real Real Real qz267 (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz96 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 2) Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 qz402 BSN.pi_near_15 rfl)

noncomputable abbrev qz404 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 285044)))

noncomputable def ep468 := @Enclosure.Real.IsNear.subLit_ff_p qz95 qz404 884279719003555 562949953421312 1 2000000000000000 33096 1048576 1 398406 908603098975439945728 866511439300003 562949953421312 1000000000199203 398406000000000000000 qz96 (ep467 rfl) rfl rfl

noncomputable abbrev qz405 := (Complex.mk qz578 qz93)

noncomputable abbrev qz406 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 285044) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep469 := @Enclosure.Complex.IsNear.re_isNear qz88 Bool.false 9608085554812645 2251799813685248 125000000597609 99601500000000000000 Bool.false 866511439300003 562949953421312 1000000000199203 398406000000000000000 (ep461 (@congrArg Complex Complex qz83 qz405 Complex.log (BSN.w_shift_mk qz13 Bool.false 142522 1000 2 qz14 rfl)) (@Enclosure.Complex.IsNear.of_parts qz401 Bool.false 9608085554812645 2251799813685248 125000000597609 99601500000000000000 Bool.false 866511439300003 562949953421312 1000000000199203 398406000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz401) (@HMul.hMul Real Real Real qz0 qz94 qz579) Bool.false 9608085554812645 2251799813685248 125000000597609 99601500000000000000 (Enclosure.clog_re_eq 9000 285044 4000 81331081936 16000000 rfl rfl rfl) (ep466 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz401) qz406 Bool.false 866511439300003 562949953421312 1000000000199203 398406000000000000000 (Enclosure.clog_im_eq 9000 285044 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz406 (@HSub.hSub Real Real Real qz392 qz95 qz404) Bool.false 866511439300003 562949953421312 1000000000199203 398406000000000000000 (BSN.arctan_recip 285044 9000 rfl rfl) ep468))))

noncomputable def ep470 := @Enclosure.Real.IsNear.mulLit_ff qz91 qz92 285044 4000 0 1 866511439300003 562949953421312 1000000000199203 398406000000000000000

noncomputable def ep471 := @Enclosure.Complex.IsNear.im_isNear qz87 Bool.false 7000 4000 0 1 Bool.false 285044 4000 0 1

noncomputable def ep472 := @Enclosure.Complex.IsNear.im_isNear qz88 Bool.false 9608085554812645 2251799813685248 125000000597609 99601500000000000000 Bool.false 866511439300003 562949953421312 1000000000199203 398406000000000000000 (ep461 (@congrArg Complex Complex qz83 qz405 Complex.log (BSN.w_shift_mk qz13 Bool.false 142522 1000 2 qz14 rfl)) (@Enclosure.Complex.IsNear.of_parts qz401 Bool.false 9608085554812645 2251799813685248 125000000597609 99601500000000000000 Bool.false 866511439300003 562949953421312 1000000000199203 398406000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz401) (@HMul.hMul Real Real Real qz0 qz94 qz579) Bool.false 9608085554812645 2251799813685248 125000000597609 99601500000000000000 (Enclosure.clog_re_eq 9000 285044 4000 81331081936 16000000 rfl rfl rfl) (ep466 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz401) qz406 Bool.false 866511439300003 562949953421312 1000000000199203 398406000000000000000 (Enclosure.clog_im_eq 9000 285044 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz406 (@HSub.hSub Real Real Real qz392 qz95 qz404) Bool.false 866511439300003 562949953421312 1000000000199203 398406000000000000000 (BSN.arctan_recip 285044 9000 rfl rfl) ep468))))

noncomputable abbrev qz97 := (@ep460 1 (BSN.w_sub_half_mk qz278 Bool.false 142522 1000 2 qz280 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) (Enclosure.sfrac Bool.false 285044 4000) Bool.false 7000 4000 0 1 Bool.false 285044 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) (Enclosure.Real.IsNear.const Bool.false 285044 4000)))

noncomputable def ep473 := @ep456 71261000014195404983 398406000000000000000000 ep457 115089868491453963191 1125899906842624000 72136000018378667983 398406000000000000000000 (@ep458 67256598883688515 9007199254740992 875000004183263 398406000000000000000 (ep459 qz97) ep469 rfl) (@ep470 61748471675957513783 562949953421312000 71261000014195404983 398406000000000000000000 (ep471 qz97) ep472 rfl) rfl

noncomputable def ep474 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz89 qz92) (@HMul.hMul Real Real Real qz0 qz91 qz90) 6065580075100021 2251799813685248 7000000001394421 1593624000000000000000 136936356944300779069 450359962737049600

noncomputable def ep475 := nat_lit 311084957470513746418576376790515712

noncomputable def ep476 := @Enclosure.Real.IsNear.mulLit_ff qz89 qz92 7000 4000 0 1 866511439300003 562949953421312 1000000000199203 398406000000000000000

noncomputable def ep477 := @Enclosure.Real.IsNear.mulLit_ff qz91 qz90 285044 4000 0 1 9608085554812645 2251799813685248 125000000597609 99601500000000000000

noncomputable def ep478 := @ep474 8907625042586214949 99601500000000000000000 ep475 138149472959320783269 450359962737049600 18690250085346732523 199203000000000000000000 (@ep476 6065580075100021 2251799813685248 7000000001394421 1593624000000000000000 (ep459 qz97) ep472 rfl) (@ep477 136936356944300779069 450359962737049600 8907625042586214949 99601500000000000000000 (ep471 qz97) ep469 rfl) rfl

noncomputable def ep479 := @Enclosure.Complex.IsNear.of_eq qz83 qz405 Bool.false 9000 4000 0 1 Bool.false 285044 4000 0 1 (BSN.w_shift_mk qz13 Bool.false 142522 1000 2 qz14 rfl)

noncomputable abbrev qz407 := (ep479 (@Enclosure.Complex.IsNear.mk qz578 (Enclosure.sfrac Bool.false 285044 4000) Bool.false 9000 4000 0 1 Bool.false 285044 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 285044 4000)))

noncomputable abbrev qz98 := qz407

noncomputable def ep480 := ep454 (@ep455 199203000000000000000000 (ep473 rfl) (ep478 rfl)) qz98 rfl rfl rfl rfl rfl rfl

noncomputable abbrev qz99 := qz396

noncomputable def ep481 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re qz99) (Complex.re ↑qz2)) (@HMul.hMul Real Real Real qz0 (Complex.im qz99) (Complex.im ↑qz2)) 120447 131072 1 524288 0 1 0 1 120447 120447

noncomputable def ep482 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz99) (Complex.re ↑qz2) 1 2 0 1 120447 65536 1 262144 120447 131072 1 524288

noncomputable abbrev qz100 := (@Enclosure.Complex.IsNear.of_eq qz396 (Complex.mk (Enclosure.sfrac Bool.false 1 2) qz277) Bool.false 1 2 0 1 Bool.false 0 1 0 1 BSN.half_c_mk (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 2) qz277 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz402 qz288))

noncomputable def ep483 := ep482 (@Enclosure.Complex.IsNear.re_isNear qz99 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz100) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz2) qz2 Bool.false 120447 65536 1 262144 (Complex.ofReal_re qz2) EMRow50.d4)

noncomputable def ep484 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz99) (Complex.im ↑qz2) 0 1 0 1 0 1 0 1 0 1 0 1

noncomputable def ep485 := ep484 (@Enclosure.Complex.IsNear.im_isNear qz99 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz100) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz2) qz10 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz2) (0 : Real) qz10 (Complex.ofReal_im qz2) Enclosure.sfrac_zero_eq) qz20)

noncomputable def ep486 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re qz99) (Complex.im ↑qz2)) (@HMul.hMul Real Real Real qz0 (Complex.im qz99) (Complex.re ↑qz2)) 0 1 0 1 0 1 0 1 0 0

noncomputable def ep487 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz99) (Complex.im ↑qz2) 1 2 0 1 0 1 0 1 0 1 0 1

noncomputable def ep488 := ep487 (@Enclosure.Complex.IsNear.re_isNear qz99 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz100) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz2) qz10 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz2) (0 : Real) qz10 (Complex.ofReal_im qz2) Enclosure.sfrac_zero_eq) qz20)

noncomputable def ep489 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz99) (Complex.re ↑qz2) 0 1 0 1 120447 65536 1 262144 0 1 0 1

noncomputable def ep490 := ep489 (@Enclosure.Complex.IsNear.im_isNear qz99 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz100) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz2) qz2 Bool.false 120447 65536 1 262144 (Complex.ofReal_re qz2) EMRow50.d4)

noncomputable def ep491 := @ep452 18690250085346732523 199203000000000000000000 (ep480 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz99 (↑qz2) Bool.false 120447 131072 1 524288 Bool.false 0 1 0 1 (@ep481 131072 1 524288 (ep483 rfl) (ep485 rfl) rfl rfl) (@ep486 1 0 1 (ep488 rfl) (ep490 rfl) rfl rfl))

noncomputable abbrev qz101 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)

noncomputable abbrev qz408 := (@Nat.cast Complex Complex.instNatCast 1)

noncomputable abbrev qz102 := (@HMul.hMul Complex Complex Complex qz388 (@HMul.hMul Complex Complex Complex qz388 (2 : Complex) qz408) (@HSub.hSub Complex Complex Complex qz389 (@HMul.hMul Complex Complex Complex qz388 (2 : Complex) qz408) (1 : Complex)))

noncomputable abbrev qz409 := (@HPow.hPow Complex Int Complex qz577 qz573 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz103 := qz409

noncomputable def ep492 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz81 2 k))) (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz73 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz82 qz83 (@HSub.hSub Int Int Int qz399 qz84 (@HMul.hMul Int Int Int qz400 qz85 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz81 2 k))) (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz73 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz82 qz83 (@HSub.hSub Int Int Int qz399 qz84 (@HMul.hMul Int Int Int qz400 qz85 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102) qz103)) Bool.false 2534805 68719476736 3 68719476736

noncomputable def ep493 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz81 2 k))) (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz73 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz82 qz83 (@HSub.hSub Int Int Int qz399 qz84 (@HMul.hMul Int Int Int qz400 qz85 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102) qz103) Bool.false 0 1 0 1 Bool.false

noncomputable def ep494 := @ep493 0 1 0 1 Bool.false 2534805 68719476736 3 68719476736 Bool.true 4014060869 3435973836800 71261 51539607552000 Bool.false 2534805 2534805 68719476736 3 68719476736 Bool.true 4014060869 4014060869 3435973836800 71261

noncomputable def ep495 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz81 2 k))) (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz73 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz82 qz83 (@HSub.hSub Int Int Int qz399 qz84 (@HMul.hMul Int Int Int qz400 qz85 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep496 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz80 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102) qz103 Bool.false 2534805 68719476736 3 68719476736 Bool.true 4014060869 3435973836800 71261 51539607552000

noncomputable abbrev qz104 := (Complex.re qz409)

noncomputable abbrev qz105 := (Complex.im qz409)

noncomputable def ep497 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz80 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102)) qz104) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz80 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102)) qz105) 2534805 68719476736 3 68719476736 0 1 0

noncomputable def ep498 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz80 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102)) qz104 1 12 0 1 7604415 17179869184 9 17179869184 2534805

noncomputable def ep499 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz80 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz10) Bool.false 1 12 0 1 Bool.false 0 1 0 1

noncomputable abbrev qz410 := (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 12) qz10 Bool.false 1 12 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 12) qz20)

noncomputable def ep500 := @Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz80 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep499 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz410)

noncomputable def ep501 := @Enclosure.Complex.IsNear.re_isNear qz103 Bool.false 7604415 17179869184 9 17179869184 Bool.true 12042182607 858993459200 71261 4294967296000

noncomputable abbrev qz580 := (@instHPow Complex Nat (@NPow.toPow Complex (@Monoid.toNPow Complex (@Semiring.toMonoid Complex Complex.instSemiring))))

noncomputable abbrev qz411 := (@HPow.hPow Complex Nat Complex qz580 qz573 1)

noncomputable abbrev qz106 := (@Inv.inv Complex Complex.instInv qz411)

noncomputable def ep502 := @Enclosure.Complex.IsNear.of_eq qz103 qz106 Bool.false 7604415 17179869184 9 17179869184 Bool.true 12042182607 858993459200 71261

noncomputable def ep503 := @Enclosure.Complex.IsNear.of_parts qz106 Bool.false 7604415 17179869184 9 17179869184 Bool.true 12042182607 858993459200 71261

noncomputable abbrev qz107 := (Complex.re qz411)

noncomputable abbrev qz108 := (@MonoidWithZeroHom Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz109 := (@MonoidWithZeroHom.funLike Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz110 := qz411

noncomputable def ep504 := @Enclosure.Real.IsNear.mulLit_ff qz107 (@Inv.inv Real Real.instInv (@DFunLike.coe qz108 Complex (fun (x : Complex) => Real) qz109 Complex.normSq qz110)) 9000 4000 0 1 844935 4294967296 1 4294967296

noncomputable def ep505 := @Enclosure.Complex.IsNear.re_isNear qz110 Bool.false 9000 4000 0 1 Bool.false 285044 4000 0 1

noncomputable def ep506 := @Enclosure.Complex.IsNear.of_eq qz110 qz83 Bool.false 9000 4000 0 1 Bool.false 285044 4000 0

noncomputable def ep507 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz108 Complex (fun (x : Complex) => Real) qz109 Complex.normSq qz110)) Bool.false 844935 4294967296 1 4294967296 844935 4294967296 1

noncomputable abbrev qz111 := (Complex.im qz411)

noncomputable abbrev qz412 := (@instHAdd Real Real.instAdd)

noncomputable def ep508 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz108 Complex (fun (x : Complex) => Real) qz109 Complex.normSq qz110) (@HAdd.hAdd Real Real Real qz412 (@HMul.hMul Real Real Real qz0 qz107 qz107) (@HMul.hMul Real Real Real qz0 qz111 qz111)) Bool.false 5083192621 1000000 0 1

noncomputable def ep509 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz107 qz107) (@HMul.hMul Real Real Real qz0 qz111 qz111) 81 16 0 1 5078130121 1000000

noncomputable def ep510 := @Enclosure.Real.IsNear.mulLit_ff qz107 qz107 9000 4000 0 1 9000 4000 0 1

noncomputable def ep511 := @Enclosure.Real.IsNear.mulLit_ff qz111 qz111 285044 4000 0 1 285044 4000 0 1

noncomputable def ep512 := @Enclosure.Complex.IsNear.im_isNear qz110 Bool.false 9000 4000 0 1 Bool.false 285044 4000 0 1

noncomputable abbrev qz112 := (ep505 (@ep506 1 (BSN.pow_one_c qz390) qz407))

noncomputable abbrev qz113 := (ep512 (@ep506 1 (BSN.pow_one_c qz390) qz407))

noncomputable def ep513 := @ep509 0 1 81331081936 5083192621 1000000 0 1 (@ep510 81 16 0 1 qz112 qz112 rfl) (@ep511 5078130121 1000000 0 1 qz113 qz113 rfl)

noncomputable def ep514 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz108 Complex (fun (x : Complex) => Real) qz109 Complex.normSq qz110) 5083192621 1000000 0 1 422467 422468 2147483648 (ep508 (Enclosure.Complex.normSq_eq_mul_add_mul qz110) (ep513 rfl rfl)) rfl

noncomputable def ep515 := @Enclosure.Real.IsNear.of_eq (Complex.re qz106) (@HMul.hMul Real Real Real qz0 qz107 (@Inv.inv Real Real.instInv (@DFunLike.coe qz108 Complex (fun (x : Complex) => Real) qz109 Complex.normSq qz110))) Bool.false 7604415 17179869184 9 17179869184 (Enclosure.Complex.inv_re_eq_mul qz110) (@ep504 7604415 17179869184 9 17179869184 qz112 (@ep507 4294967296 (ep514 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep516 := @Enclosure.Real.IsNear.of_eq (Complex.im qz106) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz111) (@Inv.inv Real Real.instInv (@DFunLike.coe qz108 Complex (fun (x : Complex) => Real) qz109 Complex.normSq qz110))) Bool.true 12042182607 858993459200 71261 4294967296000 (Enclosure.Complex.inv_im_eq_mul qz110)

noncomputable def ep517 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz111) (@Inv.inv Real Real.instInv (@DFunLike.coe qz108 Complex (fun (x : Complex) => Real) qz109 Complex.normSq qz110)) 285044 4000 0 1 844935 4294967296 1

noncomputable def ep518 := @ep517 4294967296 12042182607 858993459200 71261 4294967296000 (@Enclosure.Real.IsNear.neg qz111 Bool.false 285044 4000 0 1 qz113) (@ep507 4294967296 (ep514 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep519 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz80 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102)) qz105 0 1 0 1 12042182607 858993459200 71261 4294967296000 0

noncomputable def ep520 := @Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz80 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep499 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz410)

noncomputable def ep521 := @Enclosure.Complex.IsNear.im_isNear qz103 Bool.false 7604415 17179869184 9 17179869184 Bool.true 12042182607 858993459200 71261 4294967296000

noncomputable abbrev qz114 := (@ep502 4294967296000 (BSN.zpow_one_sub_two_mul qz390 1 1 rfl rfl) (@ep503 4294967296000 ep515 (ep516 ep518)))

noncomputable def ep522 := @ep497 1 2534805 2534805 68719476736 3 68719476736 (@ep498 68719476736 3 68719476736 ep500 (ep501 qz114) rfl) (@ep519 1 0 1 ep520 (ep521 qz114) rfl) rfl

noncomputable def ep523 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz80 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102)) qz105) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz80 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102)) qz104) 4014060869 3435973836800 71261 51539607552000 0 1 0

noncomputable def ep524 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz80 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102)) qz105 1 12 0 1 12042182607 858993459200 71261 4294967296000 4014060869

noncomputable def ep525 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz80 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102)) qz104 0 1 0 1 7604415 17179869184 9 17179869184 0

noncomputable def ep526 := @ep523 1 4014060869 4014060869 3435973836800 71261 51539607552000 (@ep524 3435973836800 71261 51539607552000 ep500 (ep521 qz114) rfl) (@ep525 1 0 1 ep520 (ep501 qz114) rfl) rfl

noncomputable abbrev qz115 := (@Enclosure.Complex.IsNear.mk qz277 qz277 Bool.false 0 1 0 1 Bool.false 0 1 0 1 qz288 qz288)

noncomputable def ep527 := @ep494 51539607552000 (@ep495 0 1 0 1 (BSN.stirling_sum_base qz83) qz115) (ep496 (ep522 rfl) (ep526 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep528 := @ep449 530279227618648350777 2251799813685248000 ep440 ep442 (ep491 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep492 Bool.true 4014060869 3435973836800 71261 51539607552000 (BSN.stirling_sum_succ qz83 0 1 rfl) (ep527 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep529 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz76 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz13 2) Bool.false 9607143883232997 1125899906842624 125000000597609 49800750000000000000 Bool.false 878355616925091 281474976710656

noncomputable abbrev qz116 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz272 qz391 qz408))

noncomputable def ep530 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz13 2) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz13 1) qz116) Bool.false 9607143883232997 1125899906842624 125000000597609 49800750000000000000 Bool.false 878355616925091 281474976710656 1000000000199203 199203000000000000000

noncomputable def ep531 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz13 1) qz116 Bool.false 9606977453250277 2251799813685248 125000000597609 99601500000000000000 Bool.false 882305107789219 562949953421312 1000000000199203 398406000000000000000 Bool.false

noncomputable def ep532 := nat_lit 43266729612622865223454411456512

noncomputable def ep533 := nat_lit 988940507270655489297333878784

noncomputable abbrev qz117 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz272 qz391 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep534 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz13 1) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz13 0) qz117) Bool.false 9606977453250277 2251799813685248 125000000597609 99601500000000000000 Bool.false 882305107789219 562949953421312 1000000000199203 398406000000000000000

noncomputable def ep535 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz13 0) qz117 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz413 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz93))

noncomputable def ep536 := @Enclosure.Complex.IsNear.of_eq qz117 qz413 Bool.false 9606977453250277 2251799813685248 125000000597609 99601500000000000000 Bool.false 882305107789219 562949953421312 1000000000199203 398406000000000000000

noncomputable def ep537 := nat_lit 6963740948466404094206757372125291966183178240

noncomputable def ep538 := nat_lit 26788936044176596336505121553200882060361728

noncomputable def ep539 := nat_lit 182973355909461351163684728523029652635648

noncomputable def ep540 := BSN.log_dyadic_bound 15715081936 146787081936 3 2 ep537 1048576 398406 ep538 ep539 225385 162502163872 131072000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 15715081936) (BSN.artanhQ 146787081936) 0 2 ep538 ep537 ep539 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep541 := @Enclosure.Real.IsNear.mulLit_ff qz94 (Real.log (Enclosure.sfrac Bool.false 81251081936 16000000)) 1 2 0 1 9606977453250277 1125899906842624 125000000597609 49800750000000000000 9606977453250277 2251799813685248 125000000597609 99601500000000000000 qz402 (BSN.isNear_log_sfrac 81251081936 16000000 9606977453250277 1125899906842624 125000000597609 49800750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 81251081936) qz403)) Bool.false 322356671680619598577664 37778931862957161709568 1000000004780872 398406000000000000000 9606977453250277 1125899906842624 125000000597609 49800750000000000000 (BSN.log_rat_reduce_isNear 81251081936 16000000 12 162502163872 131072000000 225385 1048576 24973259072661432 36028797018963968 398406 1000000000000000 rfl rfl rfl rfl (ep540 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep542 := BSN.arctan_dyadic_bound_f 1000 285044 1 0 1048576 398406 0 1 1 0 1 1 3678 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 285044) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 285044) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz414 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable abbrev qz415 := (@Nat.cast Real Real.instNatCast 285044)

noncomputable def ep543 := @Enclosure.Real.IsNear.subLit_ff_p qz95 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz414 qz415)) 884279719003555 562949953421312 1 2000000000000000 3678 1048576 1 398406 925163960705188102144 882305107789219 562949953421312 1000000000199203 398406000000000000000 qz96 (ep542 rfl) rfl rfl

noncomputable abbrev qz118 := (@HAdd.hAdd Complex Complex Complex qz272 qz391 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz416 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz93)

noncomputable def ep544 := @ep535 9606977453250277 2251799813685248 125000000597609 99601500000000000000 Bool.false 882305107789219 562949953421312 1000000000199203 398406000000000000000 Bool.false 9606977453250277 9606977453250277 2251799813685248 125000000597609 99601500000000000000 Bool.false 882305107789219 882305107789219 562949953421312 1000000000199203 398406000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz13 0) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz13) qz115) (ep536 (@congrArg Complex Complex qz118 qz416 Complex.log (BSN.w_shift_mk qz13 Bool.false 142522 1000 0 qz14 rfl)) (@Enclosure.Complex.IsNear.of_parts qz413 Bool.false 9606977453250277 2251799813685248 125000000597609 99601500000000000000 Bool.false 882305107789219 562949953421312 1000000000199203 398406000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz413) (@HMul.hMul Real Real Real qz0 qz94 (Real.log (Enclosure.sfrac Bool.false 81251081936 16000000))) Bool.false 9606977453250277 2251799813685248 125000000597609 99601500000000000000 (Enclosure.clog_re_eq 1000 285044 4000 81251081936 16000000 rfl rfl rfl) (ep541 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz413) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz415 qz414)) Bool.false 882305107789219 562949953421312 1000000000199203 398406000000000000000 (Enclosure.clog_im_eq 1000 285044 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz415 qz414)) (@HSub.hSub Real Real Real qz392 qz95 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz414 qz415))) Bool.false 882305107789219 562949953421312 1000000000199203 398406000000000000000 (BSN.arctan_recip 285044 1000 rfl rfl) ep543)))) rfl rfl

noncomputable abbrev qz417 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz93))

noncomputable def ep545 := @Enclosure.Complex.IsNear.of_eq qz116 qz417 Bool.false 9607310313215717 2251799813685248 125000000597609 99601500000000000000 Bool.false 874406126060963 562949953421312 1000000000199203 398406000000000000000

noncomputable def ep546 := nat_lit 6968296411362420867823797898365641518823178240

noncomputable def ep547 := nat_lit 26880110980773027504535630498112643468361728

noncomputable def ep548 := nat_lit 184093663268677292671652676624940180635648

noncomputable def ep549 := BSN.log_dyadic_bound 15739081936 146811081936 3 2 ep546 1048576 398406 ep547 ep548 225695 162550163872 131072000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 15739081936) (BSN.artanhQ 146811081936) 0 2 ep547 ep546 ep548 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep550 := @Enclosure.Real.IsNear.mulLit_ff qz94 (Real.log (Enclosure.sfrac Bool.false 81275081936 16000000)) 1 2 0 1 9607310313215717 1125899906842624 125000000597609 49800750000000000000 9607310313215717 2251799813685248 125000000597609 99601500000000000000 qz402 (BSN.isNear_log_sfrac 81275081936 16000000 9607310313215717 1125899906842624 125000000597609 49800750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 81275081936) qz403)) Bool.false 322367840607695477407744 37778931862957161709568 1000000004780872 398406000000000000000 9607310313215717 1125899906842624 125000000597609 49800750000000000000 (BSN.log_rat_reduce_isNear 81275081936 16000000 12 162550163872 131072000000 225695 1048576 24973259072661432 36028797018963968 398406 1000000000000000 rfl rfl rfl rfl (ep549 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep551 := BSN.arctan_dyadic_bound_f 5000 285044 1 0 1048576 398406 0 1 1 0 1 1 18391 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 285044) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 285044) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz418 := (@Nat.cast Real Real.instNatCast 5000)

noncomputable def ep552 := @Enclosure.Real.IsNear.subLit_ff_p qz95 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz418 qz415)) 884279719003555 562949953421312 1 2000000000000000 18391 1048576 1 398406 916881278040500338688 874406126060963 562949953421312 1000000000199203 398406000000000000000 qz96 (ep551 rfl) rfl rfl

noncomputable abbrev qz119 := (@HAdd.hAdd Complex Complex Complex qz272 qz391 qz408)

noncomputable abbrev qz419 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz93)

noncomputable def ep553 := @ep531 9607310313215717 2251799813685248 125000000597609 99601500000000000000 Bool.false 874406126060963 562949953421312 1000000000199203 398406000000000000000 Bool.false ep532 9607143883232997 1125899906842624 125000000597609 49800750000000000000 Bool.false ep533 878355616925091 281474976710656 1000000000199203 199203000000000000000 (ep534 (BSN.log_sum_c_succ qz13 0 1 rfl) (ep544 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep545 (@congrArg Complex Complex qz119 qz419 Complex.log (BSN.w_shift_mk qz13 Bool.false 142522 1000 1 qz14 rfl)) (@Enclosure.Complex.IsNear.of_parts qz417 Bool.false 9607310313215717 2251799813685248 125000000597609 99601500000000000000 Bool.false 874406126060963 562949953421312 1000000000199203 398406000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz417) (@HMul.hMul Real Real Real qz0 qz94 (Real.log (Enclosure.sfrac Bool.false 81275081936 16000000))) Bool.false 9607310313215717 2251799813685248 125000000597609 99601500000000000000 (Enclosure.clog_re_eq 5000 285044 4000 81275081936 16000000 rfl rfl rfl) (ep550 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz417) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz415 qz418)) Bool.false 874406126060963 562949953421312 1000000000199203 398406000000000000000 (Enclosure.clog_im_eq 5000 285044 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz415 qz418)) (@HSub.hSub Real Real Real qz392 qz95 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz418 qz415))) Bool.false 874406126060963 562949953421312 1000000000199203 398406000000000000000 (BSN.arctan_recip 285044 5000 rfl rfl) ep552)))) rfl rfl

noncomputable def ep554 := @ep441 ep442 Bool.false 9607143883232997 1125899906842624 125000000597609 49800750000000000000 Bool.false 878355616925091 281474976710656 1000000000199203 199203000000000000000 Bool.true ep443 126195613783035120191 1125899906842624000 ep436 ep437 Bool.false ep444 523252382683247622777 2251799813685248000 ep433 ep431 (@ep445 1125899906842624000 ep439 ep437 Bool.false 530279227618648350777 2251799813685248000 ep440 ep442 (BSN.logGammaStirling_unfold 1 qz83) (ep528 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep529 1000000000199203 199203000000000000000 (BSN.log_sum_c_eq qz13 2) (ep530 (BSN.log_sum_c_succ qz13 1 2 rfl) (ep553 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz120 := (@HDiv.hDiv Real Real Real qz270 qz278 (2 : Real))

noncomputable def ep555 := @Enclosure.Real.IsNear.mulLit_ff qz120 (Real.log Real.pi) 142522 2000 0 1 75021 65536 1 262144 5346071481 65536000 71261 262144000 (@Enclosure.Real.IsNear.of_eq qz120 (Enclosure.sfrac Bool.false 142522 2000) Bool.false 142522 2000 0 1 (BSN.t_half_eq qz13 Bool.false 142522 1000 qz14) (Enclosure.Real.IsNear.const Bool.false 142522 2000)) EMRow50.d5 rfl

noncomputable def ep556 := @ep434 71261 262144000 ep435 339562765299461339769 2251799813685248000 ep430 ep431 (@ep438 ep433 ep431 (ep554 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep555 rfl rfl

noncomputable def ep557 := nat_lit 8337866198797707953301835803494637833778361481594573029426380173510816825753185

noncomputable def ep558 := nat_lit 16740240528573549575895808618059294550247188042465638545505232051421437116001

noncomputable def ep559 := nat_lit 21810165369328687464096214842818622135385784623536080233709701507302218883546721

noncomputable def ep560 := BSN.sin_dyadic_bound_f 3372641749 2147483648 3 2 1048576 398796 ep557 ep64 ep558 ep559 ep66 ep558 1048575 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3372641749) qz285 0 2 ep557 ep64 ep558 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3372641749) qz286 0 2 ep559 ep66 ep558 rfl rfl rfl rfl) rfl rfl

noncomputable def ep561 := @ep429 524288 Bool.false 1048575 1048576 1 199203 (@ep432 79060617 524288 195 524288 ep556 rfl) (Enclosure.sfrac_false_div 79060617 524288) (BSN.cos_reduce3 qz393 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 118664282240328321204224) qz38) 226375608064910080 72057594037927936 Bool.false 1048575 1048576 23 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q3 79060617 524288 226375608064910080 72057594037927936 23 118664282240328321204224 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1048575 1048576 118664282240328321204224 75557863725914323419136 3372641749 2147483648 398796 398406 (ep560 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep562 := nat_lit 3989310041915734423606713

noncomputable def ep563 := nat_lit 389709303283065296653861027051

noncomputable def ep564 := nat_lit 64510864941960101463016341504000

noncomputable abbrev qz581 := (@Nat.cast Complex Complex.instNatCast 29)

noncomputable abbrev qz420 := (@HPow.hPow Complex Complex Complex qz536 qz581 qz537)

noncomputable abbrev qz121 := qz420

noncomputable abbrev qz421 := qz581

noncomputable abbrev qz122 := (@HAdd.hAdd Complex Complex Complex qz272 (@HDiv.hDiv Complex Complex Complex qz397 qz421 (@HSub.hSub Complex Complex Complex qz389 qz271 (1 : Complex))) qz396)

noncomputable abbrev qz123 := (@instHSub Nat instSubNat)

noncomputable abbrev qz422 := qz580

noncomputable abbrev qz124 := qz422

noncomputable abbrev qz125 := qz421

noncomputable def ep565 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz5 1 29) (@HAdd.hAdd Complex Complex Complex qz4 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 29, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz7) (@HMul.hMul Complex Complex Complex qz73 qz121 (@HAdd.hAdd Complex Complex Complex qz4 qz122 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz81 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz81 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz81 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz81 2 k) 1))))))) Bool.false ep424 ep425 ep426

noncomputable def ep566 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 29, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz7) (@HMul.hMul Complex Complex Complex qz73 qz121 (@HAdd.hAdd Complex Complex Complex qz4 qz122 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz81 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz81 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz81 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz81 2 k) 1)))))) Bool.false 109723614389 68719476736 217083087696721 36504335797977088

noncomputable def ep567 := nat_lit 2716102091016950675266719

noncomputable def ep568 := nat_lit 81945001402719180021836163

noncomputable def ep569 := nat_lit 5918941152114812692407687

noncomputable def ep570 := nat_lit 6144971881732896466651387051

noncomputable def ep571 := nat_lit 6920036295695704241223539762413961216

noncomputable def ep572 := nat_lit 1096573194472477986381583532867715072

noncomputable def ep573 := @ep566 Bool.false 42050373501 274877906944 108522503660415 18252167898988544 Bool.true ep567 ep425 ep568 ep427 Bool.true ep569 ep425 ep570 ep564 Bool.false ep571 ep424 ep425 ep426 ep427 Bool.false ep572 ep562 ep425

noncomputable def ep574 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 29, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz7) (BSN.headSumC qz5 29) Bool.false 109723614389 68719476736 217083087696721 36504335797977088 Bool.false 42050373501 274877906944 108522503660415

noncomputable abbrev qz423 := (@Nat.cast Complex Complex.instNatCast 28)

noncomputable def ep575 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 29) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 28) (@HPow.hPow Complex Complex Complex qz6 qz423 qz7)) Bool.false 109723614389 68719476736 217083087696721 36504335797977088 Bool.false 42050373501 274877906944 108522503660415 18252167898988544

noncomputable def ep576 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 28) (@HPow.hPow Complex Complex Complex qz6 qz423 qz7) Bool.false 1934677351461 1099511627776 1272465074361373 219026014787862528 Bool.false 62847144239 1099511627776 1272310724307259 219026014787862528 Bool.true

noncomputable def ep577 := nat_lit 1930278237797048410701824

noncomputable abbrev qz424 := (@Nat.cast Complex Complex.instNatCast 27)

noncomputable def ep578 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 28) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 27) (@HPow.hPow Complex Complex Complex qz6 qz424 qz7)) Bool.false 1934677351461 1099511627776 1272465074361373 219026014787862528 Bool.false 62847144239 1099511627776 1272310724307259 219026014787862528

noncomputable def ep579 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 27) (@HPow.hPow Complex Complex Complex qz6 qz424 qz7) Bool.false 1921785624145 1099511627776 54002224896727 9522870208167936 Bool.true 74180568867 549755813888 26993501243843 4761435104083968 Bool.false

noncomputable abbrev qz425 := (@Nat.cast Complex Complex.instNatCast 26)

noncomputable def ep580 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 27) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 26) (@HPow.hPow Complex Complex Complex qz6 qz425 qz7)) Bool.false 1921785624145 1099511627776 54002224896727 9522870208167936 Bool.true 74180568867 549755813888 26993501243843 4761435104083968

noncomputable def ep581 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 26) (@HPow.hPow Complex Complex Complex qz6 qz425 qz7) Bool.false 1744492568125 1099511627776 1210899157186625 219026014787862528 Bool.true 2117955779 8589934592 302650472284841 54756503696965632 Bool.false

noncomputable abbrev qz426 := (@Nat.cast Complex Complex.instNatCast 25)

noncomputable def ep582 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 26) (@HAdd.hAdd Complex Complex Complex qz4 qz56 (@HPow.hPow Complex Complex Complex qz6 qz426 qz7)) Bool.false 1744492568125 1099511627776 1210899157186625 219026014787862528 Bool.true 2117955779 8589934592 302650472284841 54756503696965632

noncomputable def ep583 := @Enclosure.Complex.IsNear.addLitP qz56 (@HPow.hPow Complex Complex Complex qz6 qz426 qz7) Bool.false 1525438120315 1099511627776 1179097361398459 219026014787862528 Bool.true 31476199109 137438953472 147373730720309 27378251848482816 Bool.false

noncomputable abbrev qz427 := (@Nat.cast Real Real.instNatCast 25)

noncomputable abbrev qz126 := (@Inv.inv Real Real.instInv (Real.sqrt qz427))

noncomputable abbrev qz582 := (Real.log (Enclosure.sfrac Bool.false 25 1))

noncomputable abbrev qz127 := (@HMul.hMul Real Real Real qz267 qz278 qz582)

noncomputable def ep584 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz426 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz126 (Real.cos qz127)) (@HMul.hMul Real Real Real qz0 qz126 (@Neg.neg Real Real.instNeg (Real.sin qz127)))) Bool.false 109527223905 549755813888 15900897894083 109513007393931264 Bool.true 2411093355 137438953472 7903010844223 54756503696965632 (BSN.cpow_neg_s_mk qz13 142522 1000 25 qz14 rfl)

noncomputable abbrev qz428 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 25) qz15)

noncomputable def ep585 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz427) 5242881 1048576 1 1048576 104857 104858 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz427) (Real.sqrt qz428) Bool.false 5242881 1048576 1 1048576 (BSN.sqrt_natCast_div_one 25) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz428) Bool.false 5242881 1048576 1 1048576 5242881 1048576 1 1048576 (BSN.sqrt_enclosure 25 1 2621440 2621441 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep586 := BSN.log_dyadic_bound 9 41 5 4 7545754341519345 524288 199203 124828057765224 4519905705 233982 50 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 9) (BSN.artanhQ 41) 0 4 124828057765224 7545754341519345 4519905705 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep587 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz582 142522 1000 0 1 3624129903009015 1125899906842624 250000000199203 49800750000000000000 51651824203665083583 112589990684262400 17815250014195404983 24900375000000000000000 qz18 (BSN.isNear_log_sfrac 25 1 3624129903009015 1125899906842624 250000000199203 49800750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz428) Bool.false 60802810194841294602240 18889465931478580854784 1000000000796812 199203000000000000000 3624129903009015 1125899906842624 250000000199203 49800750000000000000 (BSN.log_rat_reduce_isNear 25 1 4 50 32 233982 524288 24973259072661432 36028797018963968 199203 1000000000000000 rfl rfl rfl rfl (ep586 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep588 := nat_lit 1265499030621672765733886122287681

noncomputable def ep589 := BSN.cos_dyadic_bound_f 188610321 2147483648 2 1 1048576 398796 ep588 ep184 ep588 ep588 ep185 ep588 1044534 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 188610321) qz281 0 1 ep588 ep184 ep588 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 188610321) qz282 0 1 ep588 ep185 ep588 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz429 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 481045099) qz16)

noncomputable def ep590 := @Enclosure.Real.IsNear.cos_image qz127 qz429 Bool.false 481045099 1048576 751 1048576 Bool.false 1044534 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz127 Bool.false 51651824203665083583 112589990684262400 17815250014195404983 24900375000000000000000 481045099 1048576 751 1048576 (ep587 rfl) rfl) (Enclosure.sfrac_false_div 481045099 1048576) (BSN.cos_reduce0 qz429 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13272271490531058515968) qz19) 226375608064910080 72057594037927936 Bool.false 1044534 1048576 73 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q0 481045099 1048576 226375608064910080 72057594037927936 73 13272271490531058515968 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1044534 1048576 13272271490531058515968 151115727451828646838272 188610321 2147483648 398796 398406 (ep589 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep591 := BSN.sin_dyadic_bound_f 188610321 2147483648 1 0 1048576 398796 0 1 1 0 1 1 91976 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 188610321) qz285 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 188610321) qz286 0 0 rfl) rfl rfl

noncomputable def ep592 := @Enclosure.Real.IsNear.sin_image qz127 qz429 Bool.false 481045099 1048576 751 1048576 Bool.false 91976 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz127 Bool.false 51651824203665083583 112589990684262400 17815250014195404983 24900375000000000000000 481045099 1048576 751 1048576 (ep587 rfl) rfl) (Enclosure.sfrac_false_div 481045099 1048576) (BSN.sin_reduce0 qz429 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13272271490531058515968) qz19) 226375608064910080 72057594037927936 Bool.false 91976 1048576 73 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q0 481045099 1048576 226375608064910080 72057594037927936 73 13272271490531058515968 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 91976 1048576 13272271490531058515968 151115727451828646838272 188610321 2147483648 398796 398406 (ep591 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz430 := (@Enclosure.Real.IsNear.recentre' qz126 Bool.false 209715 1048576 1 1048576 209715 1048576 1 1048576 (ep585 rfl rfl) rfl)

noncomputable def ep593 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz126 (Real.cos qz127)) (@HMul.hMul Real Real Real qz0 qz126 (@Neg.neg Real Real.instNeg (Real.sin qz127))) Bool.false 109527223905 549755813888 15900897894083 109513007393931264 Bool.true 2411093355 137438953472 7903010844223 54756503696965632 (@Enclosure.Real.IsNear.mulLit_ff qz126 (Real.cos qz127) 209715 1048576 1 1048576 522267 524288 150650029 208879484928 109527223905 549755813888 15900897894083 109513007393931264 qz430 (@Enclosure.Real.IsNear.recentre' (Real.cos qz127) Bool.false 1044534 1048576 150650029 208879484928 522267 524288 150650029 208879484928 (ep590 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz126 (@Neg.neg Real Real.instNeg (Real.sin qz127)) 209715 1048576 1 1048576 11497 131072 150650029 208879484928 2411093355 137438953472 7903010844223 54756503696965632 qz430 (@Enclosure.Real.IsNear.neg (Real.sin qz127) Bool.false 11497 131072 150650029 208879484928 (@Enclosure.Real.IsNear.recentre' (Real.sin qz127) Bool.false 91976 1048576 150650029 208879484928 11497 131072 150650029 208879484928 (ep592 rfl rfl) rfl)) rfl)

noncomputable def ep594 := @ep583 109527223905 549755813888 15900897894083 109513007393931264 Bool.true 2411093355 137438953472 7903010844223 54756503696965632 Bool.false 959044931611126661120000 1744492568125 1099511627776 1210899157186625 219026014787862528 Bool.true 4657434012251752235008 2117955779 8589934592 302650472284841 54756503696965632 EMRow50.d8 (ep584 ep593) rfl rfl

noncomputable abbrev qz431 := (@Nat.cast Real Real.instNatCast 26)

noncomputable abbrev qz128 := (@Inv.inv Real Real.instInv (Real.sqrt qz431))

noncomputable abbrev qz583 := (Real.log (Enclosure.sfrac Bool.false 26 1))

noncomputable abbrev qz129 := (@HMul.hMul Real Real Real qz267 qz278 qz583)

noncomputable def ep595 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz425 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz128 (Real.cos qz129)) (@HMul.hMul Real Real Real qz0 qz128 (@Neg.neg Real Real.instNeg (Real.sin qz129)))) Bool.false 44323264005 274877906944 649000321627 4563041974747136 Bool.false 61368600989 549755813888 5183194679569 36504335797977088 (BSN.cpow_neg_s_mk qz13 142522 1000 26 qz14 rfl)

noncomputable abbrev qz432 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26) qz15)

noncomputable def ep596 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz431) 5346709 1048576 1 1048576 102821 102822 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz431) (Real.sqrt qz432) Bool.false 5346709 1048576 1 1048576 (BSN.sqrt_natCast_div_one 26) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz432) Bool.false 5346709 1048576 1 1048576 5346709 1048576 1 1048576 (BSN.sqrt_enclosure 26 1 2673354 2673355 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep597 := BSN.log_dyadic_bound 10 42 5 4 9150106136613120 524288 199203 179034245376000 10500000000 254545 52 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 10) (BSN.artanhQ 42) 0 4 179034245376000 9150106136613120 10500000000 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep598 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz583 142522 1000 0 1 3668288609262839 1125899906842624 250000000199203 49800750000000000000 261405914584679169979 562949953421312000 17815250014195404983 24900375000000000000000 qz18 (BSN.isNear_log_sfrac 26 1 3668288609262839 1125899906842624 250000000199203 49800750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz432) Bool.false 61543670347942250676224 18889465931478580854784 1000000000796812 199203000000000000000 3668288609262839 1125899906842624 250000000199203 49800750000000000000 (BSN.log_rat_reduce_isNear 26 1 4 52 32 254545 524288 24973259072661432 36028797018963968 199203 1000000000000000 rfl rfl rfl rfl (ep597 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep599 := nat_lit 1187778217231761808844591660719432011623062874905380390703519583249704050390625

noncomputable def ep600 := nat_lit 340893635353972242937908654337450115231199676809510729531416821441650390625

noncomputable def ep601 := nat_lit 3110295788768803068104412021205775587397647491942114196375690900324033650390625

noncomputable def ep602 := BSN.sin_dyadic_bound_f 2072895275 2147483648 3 2 1048576 398796 ep599 ep64 ep600 ep601 ep66 ep600 862140 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2072895275) qz285 0 2 ep599 ep64 ep600 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2072895275) qz286 0 2 ep601 ep66 ep600 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz433 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 243453229) qz37)

noncomputable def ep603 := @Enclosure.Real.IsNear.cos_image qz129 qz433 Bool.false 243453229 524288 751 1048576 Bool.false 862140 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz129 Bool.false 261405914584679169979 562949953421312000 17815250014195404983 24900375000000000000000 243453229 524288 751 1048576 (ep598 rfl) rfl) (Enclosure.sfrac_false_div 243453229 524288) (BSN.cos_reduce3 qz433 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 72933518674414050213888) qz38) 226375608064910080 72057594037927936 Bool.false 862140 1048576 73 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q3 243453229 524288 226375608064910080 72057594037927936 73 72933518674414050213888 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 862140 1048576 72933518674414050213888 75557863725914323419136 2072895275 2147483648 398796 398406 (ep602 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep604 := nat_lit 660028295633358325910523326468278873175137685914904444048413731503809650390625

noncomputable def ep605 := nat_lit 1979403099629367033245694162096161719294950658391094310686178360868545650390625

noncomputable def ep606 := BSN.cos_dyadic_bound_f 2072895275 2147483648 3 2 1048576 398796 ep604 ep57 ep600 ep605 ep60 ep600 596846 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2072895275) qz281 0 2 ep604 ep57 ep600 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2072895275) qz282 0 2 ep605 ep60 ep600 rfl rfl rfl rfl) rfl rfl

noncomputable def ep607 := @Enclosure.Real.IsNear.sin_image qz129 qz433 Bool.false 243453229 524288 751 1048576 Bool.true 596846 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz129 Bool.false 261405914584679169979 562949953421312000 17815250014195404983 24900375000000000000000 243453229 524288 751 1048576 (ep598 rfl) rfl) (Enclosure.sfrac_false_div 243453229 524288) (BSN.sin_reduce3 qz433 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 72933518674414050213888) qz38) 226375608064910080 72057594037927936 Bool.false 596846 1048576 73 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q3 243453229 524288 226375608064910080 72057594037927936 73 72933518674414050213888 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 596846 1048576 72933518674414050213888 75557863725914323419136 2072895275 2147483648 398796 398406 (ep606 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz434 := (@Enclosure.Real.IsNear.recentre' qz128 Bool.false 205643 1048576 1 1048576 205643 1048576 1 1048576 (ep596 rfl rfl) rfl)

noncomputable def ep608 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz128 (Real.cos qz129)) (@HMul.hMul Real Real Real qz0 qz128 (@Neg.neg Real Real.instNeg (Real.sin qz129))) Bool.false 44323264005 274877906944 649000321627 4563041974747136 Bool.false 61368600989 549755813888 5183194679569 36504335797977088 (@Enclosure.Real.IsNear.mulLit_ff qz128 (Real.cos qz129) 205643 1048576 1 1048576 215535 262144 150650029 208879484928 44323264005 274877906944 649000321627 4563041974747136 qz434 (@Enclosure.Real.IsNear.recentre' (Real.cos qz129) Bool.false 862140 1048576 150650029 208879484928 215535 262144 150650029 208879484928 (ep603 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz128 (@Neg.neg Real Real.instNeg (Real.sin qz129)) 205643 1048576 1 1048576 298423 524288 150650029 208879484928 61368600989 549755813888 5183194679569 36504335797977088 qz434 (@Enclosure.Real.IsNear.neg (Real.sin qz129) Bool.true 298423 524288 150650029 208879484928 (@Enclosure.Real.IsNear.recentre' (Real.sin qz129) Bool.true 596846 1048576 150650029 208879484928 298423 524288 150650029 208879484928 (ep607 rfl rfl) rfl)) rfl)

noncomputable def ep609 := @ep581 44323264005 274877906944 649000321627 4563041974747136 Bool.false 61368600989 549755813888 5183194679569 36504335797977088 Bool.false 528256409960046269562880 1921785624145 1099511627776 54002224896727 9522870208167936 Bool.true 637206234564881547264 74180568867 549755813888 26993501243843 4761435104083968 (ep582 (BSN.head_sum_c_succ qz5 25 26 rfl rfl) (ep594 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep595 ep608) rfl rfl

noncomputable abbrev qz435 := (@Nat.cast Real Real.instNatCast 27)

noncomputable abbrev qz130 := (@Inv.inv Real Real.instInv (Real.sqrt qz435))

noncomputable abbrev qz584 := (Real.log (Enclosure.sfrac Bool.false 27 1))

noncomputable abbrev qz131 := (@HMul.hMul Real Real Real qz267 qz278 qz584)

noncomputable def ep610 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz424 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz130 (Real.cos qz131)) (@HMul.hMul Real Real Real qz0 qz130 (@Neg.neg Real Real.instNeg (Real.sin qz131)))) Bool.false 3222931829 274877906944 7603475434163 54756503696965632 Bool.false 211208281973 1099511627776 30609667090481 219026014787862528 (BSN.cpow_neg_s_mk qz13 142522 1000 27 qz14 rfl)

noncomputable abbrev qz436 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 27) qz15)

noncomputable def ep611 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz435) 5448561 1048576 1 1048576 100899 100900 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz435) (Real.sqrt qz436) Bool.false 5448561 1048576 1 1048576 (BSN.sqrt_natCast_div_one 27) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz436) Bool.false 5448561 1048576 1 1048576 5448561 1048576 1 1048576 (BSN.sqrt_enclosure 27 1 2724280 2724281 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep612 := BSN.log_dyadic_bound 11 43 5 4 11045349262332945 524288 199203 250863800262504 22507682505 274332 54 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 11) (BSN.artanhQ 43) 0 4 250863800262504 11045349262332945 22507682505 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep613 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz584 142522 1000 0 1 3710780868205815 1125899906842624 250000000199203 49800750000000000000 52886791089842916543 112589990684262400 17815250014195404983 24900375000000000000000 qz18 (BSN.isNear_log_sfrac 27 1 3710780868205815 1125899906842624 250000000199203 49800750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz436) Bool.false 62256572154556490711040 18889465931478580854784 1000000000796812 199203000000000000000 3710780868205815 1125899906842624 250000000199203 49800750000000000000 (BSN.log_rat_reduce_isNear 27 1 4 54 32 274332 524288 24973259072661432 36028797018963968 199203 1000000000000000 rfl rfl rfl rfl (ep612 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep614 := BSN.sin_dyadic_bound_f 130917538 2147483648 1 0 1048576 398796 0 1 1 0 1 1 63884 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 130917538) qz285 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 130917538) qz286 0 0 rfl) rfl rfl

noncomputable abbrev qz437 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 7696041) (@Nat.cast Real Real.instNatCast 16384))

noncomputable def ep615 := @Enclosure.Real.IsNear.cos_image qz131 qz437 Bool.false 7696041 16384 751 1048576 Bool.false 63884 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz131 Bool.false 52886791089842916543 112589990684262400 17815250014195404983 24900375000000000000000 7696041 16384 751 1048576 (ep613 rfl) rfl) (Enclosure.sfrac_false_div 7696041 16384) (BSN.cos_reduce3 qz437 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 143945356387362537472) qz291) 226375608064910080 72057594037927936 Bool.false 63884 1048576 74 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q3 7696041 16384 226375608064910080 72057594037927936 74 143945356387362537472 2361183241434822606848 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 63884 1048576 143945356387362537472 2361183241434822606848 130917538 2147483648 398796 398406 (ep614 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep616 := BSN.cos_dyadic_bound_f 130917538 2147483648 1 0 1048576 398796 0 1 1 0 1 1 1046627 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 130917538) qz281 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 130917538) qz282 0 0 rfl) rfl rfl

noncomputable def ep617 := @Enclosure.Real.IsNear.sin_image qz131 qz437 Bool.false 7696041 16384 751 1048576 Bool.true 1046627 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz131 Bool.false 52886791089842916543 112589990684262400 17815250014195404983 24900375000000000000000 7696041 16384 751 1048576 (ep613 rfl) rfl) (Enclosure.sfrac_false_div 7696041 16384) (BSN.sin_reduce3 qz437 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 143945356387362537472) qz291) 226375608064910080 72057594037927936 Bool.false 1046627 1048576 74 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q3 7696041 16384 226375608064910080 72057594037927936 74 143945356387362537472 2361183241434822606848 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1046627 1048576 143945356387362537472 2361183241434822606848 130917538 2147483648 398796 398406 (ep616 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz438 := (@Enclosure.Real.IsNear.recentre' qz130 Bool.false 201799 1048576 1 1048576 201799 1048576 1 1048576 (ep611 rfl rfl) rfl)

noncomputable def ep618 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz130 (Real.cos qz131)) (@HMul.hMul Real Real Real qz0 qz130 (@Neg.neg Real Real.instNeg (Real.sin qz131))) Bool.false 3222931829 274877906944 7603475434163 54756503696965632 Bool.false 211208281973 1099511627776 30609667090481 219026014787862528 (@Enclosure.Real.IsNear.mulLit_ff qz130 (Real.cos qz131) 201799 1048576 1 1048576 15971 262144 150650029 208879484928 3222931829 274877906944 7603475434163 54756503696965632 qz438 (@Enclosure.Real.IsNear.recentre' (Real.cos qz131) Bool.false 63884 1048576 150650029 208879484928 15971 262144 150650029 208879484928 (ep615 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz130 (@Neg.neg Real Real.instNeg (Real.sin qz131)) 201799 1048576 1 1048576 1046627 1048576 150650029 208879484928 211208281973 1099511627776 30609667090481 219026014787862528 qz438 (@Enclosure.Real.IsNear.neg (Real.sin qz131) Bool.true 1046627 1048576 150650029 208879484928 (@Enclosure.Real.IsNear.recentre' (Real.sin qz131) Bool.true 1046627 1048576 150650029 208879484928 1046627 1048576 150650029 208879484928 (ep617 rfl rfl) rfl)) rfl)

noncomputable def ep619 := @ep579 3222931829 274877906944 7603475434163 54756503696965632 Bool.false 211208281973 1099511627776 30609667090481 219026014787862528 Bool.false 531800060981561140445184 1934677351461 1099511627776 1272465074361373 219026014787862528 Bool.false 34550582931647975391232 62847144239 1099511627776 1272310724307259 219026014787862528 (ep580 (BSN.head_sum_c_succ qz5 26 27 rfl rfl) (ep609 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep610 ep618) rfl rfl

noncomputable abbrev qz132 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 28)))

noncomputable abbrev qz585 := (Real.log (Enclosure.sfrac Bool.false 28 1))

noncomputable abbrev qz133 := (@HMul.hMul Real Real Real qz267 qz278 qz585)

noncomputable def ep620 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz423 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz132 (Real.cos qz133)) (@HMul.hMul Real Real Real qz0 qz132 (@Neg.neg Real Real.instNeg (Real.sin qz133)))) Bool.true 179099521237 1099511627776 30033451818953 219026014787862528 Bool.false 105354349765 1099511627776 29959319617721 219026014787862528 (BSN.cpow_neg_s_mk qz13 142522 1000 28 qz14 rfl)

noncomputable abbrev qz439 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 28) qz15)

noncomputable def ep621 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 28)) 5548543 1048576 1 1048576 99081 99082 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 28)) (Real.sqrt qz439) Bool.false 5548543 1048576 1 1048576 (BSN.sqrt_natCast_div_one 28) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz439) Bool.false 5548543 1048576 1 1048576 5548543 1048576 1 1048576 (BSN.sqrt_enclosure 28 1 2774271 2774272 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep622 := BSN.log_dyadic_bound 12 44 5 4 13275571325829120 524288 199203 344661139390464 45148078080 293399 56 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 12) (BSN.artanhQ 44) 0 4 344661139390464 13275571325829120 45148078080 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep623 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz585 142522 1000 0 1 3751726938922231 1125899906842624 250000000199203 49800750000000000000 267351813394537103291 562949953421312000 17815250014195404983 24900375000000000000000 qz18 (BSN.isNear_log_sfrac 28 1 3751726938922231 1125899906842624 250000000199203 49800750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz439) Bool.false 62943533227317076688896 18889465931478580854784 1000000000796812 199203000000000000000 3751726938922231 1125899906842624 250000000199203 49800750000000000000 (BSN.log_rat_reduce_isNear 28 1 4 56 32 293399 524288 24973259072661432 36028797018963968 199203 1000000000000000 rfl rfl rfl rfl (ep622 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep624 := nat_lit 1700153331244035419173634211048407296

noncomputable def ep625 := BSN.cos_dyadic_bound_f 1141884092 2147483648 2 1 1048576 398796 ep624 ep184 ep624 ep624 ep185 ep624 903799 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1141884092) qz281 0 1 ep624 ep184 ep624 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1141884092) qz282 0 1 ep624 ep185 ep624 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz440 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 248990779) qz37)

noncomputable def ep626 := @Enclosure.Real.IsNear.cos_image qz133 qz440 Bool.false 248990779 524288 751 1048576 Bool.true 903799 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz133 Bool.false 267351813394537103291 562949953421312000 17815250014195404983 24900375000000000000000 248990779 524288 751 1048576 (ep623 rfl) rfl) (Enclosure.sfrac_false_div 248990779 524288) (BSN.cos_reduce2 qz440 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 40176474795920702046208) qz38) 226375608064910080 72057594037927936 Bool.false 903799 1048576 75 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q2 248990779 524288 226375608064910080 72057594037927936 75 40176474795920702046208 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 903799 1048576 40176474795920702046208 75557863725914323419136 1141884092 2147483648 398796 398406 (ep625 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep627 := BSN.sin_dyadic_bound_f 1141884092 2147483648 2 1 1048576 398796 ep624 ep180 ep624 ep624 ep181 ep624 531655 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1141884092) qz285 0 1 ep624 ep180 ep624 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1141884092) qz286 0 1 ep624 ep181 ep624 rfl rfl rfl rfl) rfl rfl

noncomputable def ep628 := @Enclosure.Real.IsNear.sin_image qz133 qz440 Bool.false 248990779 524288 751 1048576 Bool.true 531655 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz133 Bool.false 267351813394537103291 562949953421312000 17815250014195404983 24900375000000000000000 248990779 524288 751 1048576 (ep623 rfl) rfl) (Enclosure.sfrac_false_div 248990779 524288) (BSN.sin_reduce2 qz440 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 40176474795920702046208) qz38) 226375608064910080 72057594037927936 Bool.false 531655 1048576 75 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q2 248990779 524288 226375608064910080 72057594037927936 75 40176474795920702046208 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 531655 1048576 40176474795920702046208 75557863725914323419136 1141884092 2147483648 398796 398406 (ep627 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz441 := (@Enclosure.Real.IsNear.recentre' qz132 Bool.false 198163 1048576 1 1048576 198163 1048576 1 1048576 (ep621 rfl rfl) rfl)

noncomputable def ep629 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz132 (Real.cos qz133)) (@HMul.hMul Real Real Real qz0 qz132 (@Neg.neg Real Real.instNeg (Real.sin qz133))) Bool.true 179099521237 1099511627776 30033451818953 219026014787862528 Bool.false 105354349765 1099511627776 29959319617721 219026014787862528 (@Enclosure.Real.IsNear.mulLit_ft qz132 (Real.cos qz133) 198163 1048576 1 1048576 903799 1048576 150650029 208879484928 179099521237 1099511627776 30033451818953 219026014787862528 qz441 (@Enclosure.Real.IsNear.recentre' (Real.cos qz133) Bool.true 903799 1048576 150650029 208879484928 903799 1048576 150650029 208879484928 (ep626 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz132 (@Neg.neg Real Real.instNeg (Real.sin qz133)) 198163 1048576 1 1048576 531655 1048576 150650029 208879484928 105354349765 1099511627776 29959319617721 219026014787862528 qz441 (@Enclosure.Real.IsNear.neg (Real.sin qz133) Bool.true 531655 1048576 150650029 208879484928 (@Enclosure.Real.IsNear.recentre' (Real.sin qz133) Bool.true 531655 1048576 150650029 208879484928 531655 1048576 150650029 208879484928 (ep628 rfl rfl) rfl)) rfl)

noncomputable def ep630 := @ep576 179099521237 1099511627776 30033451818953 219026014787862528 Bool.false 105354349765 1099511627776 29959319617721 219026014787862528 Bool.false ep577 109723614389 68719476736 217083087696721 36504335797977088 Bool.false 184939498466693143855104 42050373501 274877906944 108522503660415 18252167898988544 (ep578 (BSN.head_sum_c_succ qz5 27 28 rfl rfl) (ep619 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep620 ep629) rfl rfl

noncomputable def ep631 := @Enclosure.Complex.IsNear.mul qz121 (@HAdd.hAdd Complex Complex Complex qz4 qz122 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz81 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz81 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz81 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz81 2 k) 1))))) Bool.true ep567 ep425 ep568 ep427 Bool.true

noncomputable def ep632 := nat_lit 1295379385691181387087872

noncomputable def ep633 := nat_lit 52253358438200158118326127

noncomputable abbrev qz134 := (Complex.re qz420)

noncomputable abbrev qz135 := (Complex.im qz420)

noncomputable def ep634 := @Enclosure.Real.IsNear.subLit_tt_n (@HMul.hMul Real Real Real qz0 qz134 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz122 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz81 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz81 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz81 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz81 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz135 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz122 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz81 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz81 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz81 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz81 2 k) 1))))))) 88116180519086892597165 ep632 ep633

noncomputable def ep635 := nat_lit 774130379303521217556196098048

noncomputable def ep636 := nat_lit 1689706934937393954591531

noncomputable def ep637 := nat_lit 7412807870430035828043593

noncomputable def ep638 := nat_lit 266941510104662488812481413120

noncomputable def ep639 := nat_lit 3518382658136070801043702700371093923096290131968

noncomputable def ep640 := @Enclosure.Real.IsNear.mulLit_tf qz134 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz122 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz81 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz81 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz81 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz81 2 k) 1)))))) 149369186655 1099511627776 29525571065863 219026014787862528 1769766224729

noncomputable abbrev qz442 := (@Nat.cast Real Real.instNatCast 29)

noncomputable abbrev qz136 := (@Inv.inv Real Real.instInv (Real.sqrt qz442))

noncomputable abbrev qz443 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) qz546 (Real.log (Enclosure.sfrac Bool.false 29 1)))

noncomputable abbrev qz137 := (Real.cos qz443)

noncomputable abbrev qz138 := (Real.sin qz443)

noncomputable abbrev qz586 := (@Neg.neg Real Real.instNeg qz138)

noncomputable def ep641 := @Enclosure.Complex.IsNear.of_eq qz121 (Complex.mk (@HMul.hMul Real Real Real qz0 qz136 qz137) (@HMul.hMul Real Real Real qz0 qz136 qz586)) Bool.true 149369186655 1099511627776 29525571065863 219026014787862528 Bool.true 139196106765 1099511627776 29515163505925 219026014787862528 (BSN.cpow_neg_s_mk qz13 142522 1000 29 qz14 rfl)

noncomputable abbrev qz444 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 29) qz15)

noncomputable def ep642 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz442) 5646755 1048576 1 1048576 97357 97358 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz442) (Real.sqrt qz444) Bool.false 5646755 1048576 1 1048576 (BSN.sqrt_natCast_div_one 29) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz444) Bool.false 5646755 1048576 1 1048576 5646755 1048576 1 1048576 (BSN.sqrt_enclosure 29 1 2823377 2823378 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep643 := BSN.log_dyadic_bound 13 45 6 5 353956287581982421875 524288 199203 10371179520995104305 130276274797305 311797 58 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 13) (BSN.artanhQ 45) 0 5 10371179520995104305 353956287581982421875 130276274797305 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz445 := (Real.log (Enclosure.sfrac Bool.false 29 1))

noncomputable abbrev qz139 := qz445

noncomputable abbrev qz446 := (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 29) qz15))

noncomputable def ep644 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz139 142522 1000 0 1 3791236343078135 1125899906842624 250000000199203 49800750000000000000 54033458608818195647 112589990684262400 17815250014195404983 24900375000000000000000 qz18 (BSN.isNear_log_sfrac 29 1 3791236343078135 1125899906842624 250000000199203 49800750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz446 Bool.false 63606391034871975772160 18889465931478580854784 1000000000796812 199203000000000000000 3791236343078135 1125899906842624 250000000199203 49800750000000000000 (BSN.log_rat_reduce_isNear 29 1 4 58 32 311797 524288 24973259072661432 36028797018963968 199203 1000000000000000 rfl rfl rfl rfl (ep643 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep645 := nat_lit 9645540013978539425069575728812153616

noncomputable def ep646 := BSN.sin_dyadic_bound_f 1762307286 2147483648 2 1 1048576 398796 ep645 ep180 ep645 ep645 ep181 ep645 767117 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1762307286) qz285 0 1 ep645 ep180 ep645 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1762307286) qz286 0 1 ep645 ep181 ep645 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz140 := qz443

noncomputable abbrev qz447 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 503225797) qz16)

noncomputable def ep647 := @Enclosure.Real.IsNear.cos_image qz140 qz447 Bool.false 503225797 1048576 47 65536 Bool.true 767117 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz140 Bool.false 54033458608818195647 112589990684262400 17815250014195404983 24900375000000000000000 503225797 1048576 47 65536 (ep644 rfl) rfl) (Enclosure.sfrac_false_div 503225797 1048576) (BSN.cos_reduce1 qz447 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 124011350584766270275584) qz19) 226375608064910080 72057594037927936 Bool.false 767117 1048576 76 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q1 503225797 1048576 226375608064910080 72057594037927936 76 124011350584766270275584 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 767117 1048576 124011350584766270275584 151115727451828646838272 1762307286 2147483648 398796 398406 (ep646 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep648 := nat_lit 344724790991821384318686597543213702063465684883427813643840839106855499489536

noncomputable def ep649 := nat_lit 93036442161261122527570755408798025139997716262864363942821658391981875456

noncomputable def ep650 := nat_lit 1033988300091141630711004651118823510140117059217757712203636874003782534717696

noncomputable def ep651 := BSN.cos_dyadic_bound_f 1762307286 2147483648 3 2 1048576 398796 ep648 ep57 ep649 ep650 ep60 ep649 714871 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1762307286) qz281 0 2 ep648 ep57 ep649 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1762307286) qz282 0 2 ep650 ep60 ep649 rfl rfl rfl rfl) rfl rfl

noncomputable def ep652 := @Enclosure.Real.IsNear.sin_image qz140 qz447 Bool.false 503225797 1048576 47 65536 Bool.false 714871 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz140 Bool.false 54033458608818195647 112589990684262400 17815250014195404983 24900375000000000000000 503225797 1048576 47 65536 (ep644 rfl) rfl) (Enclosure.sfrac_false_div 503225797 1048576) (BSN.sin_reduce1 qz447 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 124011350584766270275584) qz19) 226375608064910080 72057594037927936 Bool.false 714871 1048576 76 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q1 503225797 1048576 226375608064910080 72057594037927936 76 124011350584766270275584 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 714871 1048576 124011350584766270275584 151115727451828646838272 1762307286 2147483648 398796 398406 (ep651 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz448 := (@Enclosure.Real.IsNear.recentre' qz136 Bool.false 194715 1048576 1 1048576 194715 1048576 1 1048576 (ep642 rfl rfl) rfl)

noncomputable def ep653 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz136 qz137) (@HMul.hMul Real Real Real qz0 qz136 qz586) Bool.true 149369186655 1099511627776 29525571065863 219026014787862528 Bool.true 139196106765 1099511627776 29515163505925 219026014787862528 (@Enclosure.Real.IsNear.mulLit_ft qz136 qz137 194715 1048576 1 1048576 767117 1048576 9428077 13054967808 149369186655 1099511627776 29525571065863 219026014787862528 qz448 (@Enclosure.Real.IsNear.recentre' qz137 Bool.true 767117 1048576 9428077 13054967808 767117 1048576 9428077 13054967808 (ep647 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz136 qz586 194715 1048576 1 1048576 714871 1048576 9428077 13054967808 139196106765 1099511627776 29515163505925 219026014787862528 qz448 (@Enclosure.Real.IsNear.neg qz138 Bool.false 714871 1048576 9428077 13054967808 (@Enclosure.Real.IsNear.recentre' qz138 Bool.false 714871 1048576 9428077 13054967808 714871 1048576 9428077 13054967808 (ep652 rfl rfl) rfl)) rfl)

noncomputable def ep654 := @ep640 3534422064216 0 1 88116180519086892597165 ep632 ep633 ep635 (@Enclosure.Complex.IsNear.re_isNear qz121 Bool.true 149369186655 1099511627776 29525571065863 219026014787862528 Bool.true 139196106765 1099511627776 29515163505925 219026014787862528 (ep641 ep653))

noncomputable def ep655 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz122 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz81 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz81 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz81 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz81 2 k) 1))))) Bool.false 1769766224729 3534422064216 0 1 Bool.false

noncomputable def ep656 := @Enclosure.Complex.IsNear.addLitP qz122 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz81 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz81 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz81 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz81 2 k) 1)))) Bool.false 5070942621 10156385242 0 1 Bool.true 1033284500

noncomputable def ep657 := @ep656 5078192621 0 1 Bool.false 1 696 0 1 Bool.false 71261 174000 0 1 Bool.false 3539532449458 1769766224729 3534422064216 0 1 Bool.false 182085581365081 182085581365081 883605516054000 0 1

noncomputable abbrev qz141 := (@HDiv.hDiv Complex Complex Complex qz397 qz421 (@HSub.hSub Complex Complex Complex qz389 qz271 (1 : Complex)))

noncomputable def ep658 := @Enclosure.Complex.IsNear.addLitP qz141 qz99 Bool.true 58000000 81251081936 0 1 Bool.true 16532552000 81251081936 0 1

noncomputable def ep659 := @Enclosure.Complex.IsNear.of_eq qz141 (Complex.mk (Enclosure.sfrac Bool.true 58000000 81251081936) (Enclosure.sfrac Bool.true 16532552000 81251081936)) Bool.true 58000000 81251081936 0 1 Bool.true 16532552000 81251081936 0 1

noncomputable def ep660 := @ep658 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 81135081936 5070942621 10156385242 0 1 Bool.true 16532552000 1033284500 5078192621 0 1 (ep659 (BSN.N_div_s_sub_one_mk qz13 142522 1000 29 qz14 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 58000000 81251081936) (Enclosure.sfrac Bool.true 16532552000 81251081936) Bool.true 58000000 81251081936 0 1 Bool.true 16532552000 81251081936 0 1 (Enclosure.Real.IsNear.const Bool.true 58000000 81251081936) (Enclosure.Real.IsNear.const Bool.true 16532552000 81251081936))) qz100 rfl

noncomputable abbrev qz142 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)))

noncomputable abbrev qz449 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz580 qz581 1))

noncomputable abbrev qz143 := qz449

noncomputable def ep661 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz81 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz81 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz81 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz81 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz81 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz81 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz81 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz81 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz143)) Bool.false 1 696 0 1

noncomputable def ep662 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz81 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz81 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz81 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz81 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz143) Bool.false 0 1 0 1 Bool.false

noncomputable def ep663 := @ep662 0 1 0 1 Bool.false 1 696 0 1 Bool.false 71261 174000 0 1 Bool.false 1 1 696 0 1 Bool.false 71261 71261 174000 0

noncomputable def ep664 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz81 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz81 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz81 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz81 2 k) 1)))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep665 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz143 Bool.false 1 696 0 1 Bool.false 71261 174000 0 1

noncomputable abbrev qz144 := (Complex.re qz449)

noncomputable abbrev qz145 := (Complex.im qz449)

noncomputable def ep666 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz144) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz145) 1 696 0 1 0 1 0

noncomputable def ep667 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz144 1 24 0 1 1 29 0 1 1

noncomputable def ep668 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz142)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz142)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep669 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz142)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep670 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz142) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz10) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 1 1 6 2 Bool.false BSN.bern_real_1 EMRow50.d9 rfl) qz410

noncomputable def ep671 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz5 Bool.false 1 2 0 1 Bool.false 142522 1000 0 1 (BSN.ascPochhammer_one_eval qz5)

noncomputable def ep672 := ep671 (@Enclosure.Complex.IsNear.of_eq qz5 (Complex.mk qz94 qz13) Bool.false 1 2 0 1 Bool.false 142522 1000 0 1 (BSN.s_crit_mk qz13 Bool.false 142522 1000 qz14) (@Enclosure.Complex.IsNear.mk qz94 qz13 Bool.false 1 2 0 1 Bool.false 142522 1000 0 1 qz402 qz18))

noncomputable def ep673 := @ep669 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz142) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep670) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 142522 1000 0 1 ep672)

noncomputable def ep674 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz142)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 142522 1000 0 1 0 1 0

noncomputable def ep675 := @ep674 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz142) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep670) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 142522 1000 0 1 ep672)

noncomputable def ep676 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz142)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz142)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) 71261 6000 0 1 0 1 0 1 71261

noncomputable def ep677 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz142)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 142522 1000 0 1 71261 6000 0

noncomputable def ep678 := @ep677 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz142) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep670) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 142522 1000 0 1 ep672)

noncomputable def ep679 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz142)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep680 := @ep679 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz142) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep670) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 142522 1000 0 1 ep672)

noncomputable def ep681 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 71261 6000 0 1 (@ep668 1 24 0 1 (ep673 rfl) (ep675 rfl) rfl rfl) (@ep676 71261 6000 0 1 (ep678 rfl) (ep680 rfl) rfl rfl)

noncomputable def ep682 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 71261 6000 0 1 ep681

noncomputable abbrev qz146 := (@Enclosure.Complex.IsNear.re_isNear qz449 Bool.false 1 29 0 1 Bool.false 0 1 0 1 (@Enclosure.Complex.IsNear.of_eq qz449 (Complex.mk (Enclosure.sfrac Bool.false 1 29) qz277) Bool.false 1 29 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 29 1 29 EMRow50.d10 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 29) qz277 Bool.false 1 29 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 29) qz288)))

noncomputable def ep683 := @ep667 696 0 1 ep682 qz146

noncomputable def ep684 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz145 71261 6000 0 1 0 1 0 1 0

noncomputable def ep685 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 71261 6000 0 1 ep681

noncomputable abbrev qz147 := (@Enclosure.Complex.IsNear.im_isNear qz449 Bool.false 1 29 0 1 Bool.false 0 1 0 1 (@Enclosure.Complex.IsNear.of_eq qz449 (Complex.mk (Enclosure.sfrac Bool.false 1 29) qz277) Bool.false 1 29 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 29 1 29 EMRow50.d10 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 29) qz277 Bool.false 1 29 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 29) qz288)))

noncomputable def ep686 := @ep684 1 0 1 ep685 qz147

noncomputable def ep687 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz145) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz144) 0 1 0 1 71261 174000 0

noncomputable def ep688 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz145 1 24 0 1 0 1 0 1 0

noncomputable def ep689 := @ep688 1 0 1 ep682 qz147

noncomputable def ep690 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz144 71261 6000 0 1 1 29 0 1 71261

noncomputable def ep691 := @ep690 174000 0 1 ep685 qz146

noncomputable def ep692 := @ep663 1 (@ep664 0 1 0 1 (BSN.bern_sum_base qz5 29) qz115) (ep665 (@ep666 1 1 1 696 0 1 (ep683 rfl) (ep686 rfl) rfl rfl) (@ep687 1 71261 71261 174000 0 1 (ep689 rfl) (ep691 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep693 := ep657 (ep660 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep661 Bool.false 71261 174000 0 1 (BSN.bern_sum_succ qz5 29 0 1 1 rfl rfl) (ep692 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep694 := @Enclosure.Real.IsNear.mulLit_tf qz135 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz122 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz81 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz81 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz81 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz81 2 k) 1)))))) 139196106765 1099511627776 29515163505925 219026014787862528 182085581365081

noncomputable def ep695 := @ep694 883605516054000 0 1 ep636 ep425 ep637 ep638 (@Enclosure.Complex.IsNear.im_isNear qz121 Bool.true 149369186655 1099511627776 29525571065863 219026014787862528 Bool.true 139196106765 1099511627776 29515163505925 219026014787862528 (ep641 ep653))

noncomputable def ep696 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz122 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz81 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz81 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz81 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz81 2 k) 1))))) Bool.false 1769766224729 3534422064216 0 1 Bool.false

noncomputable def ep697 := nat_lit 1813198346006998239212937

noncomputable def ep698 := nat_lit 5376180772663678631699329903

noncomputable def ep699 := @Enclosure.Real.IsNear.addLit_tt (@HMul.hMul Real Real Real qz0 qz134 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz122 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz81 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz81 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz81 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz81 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz135 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz122 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz81 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz81 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz81 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz81 2 k) 1))))))) ep697 ep425 ep698

noncomputable def ep700 := nat_lit 193532594825880304389049024512000

noncomputable def ep701 := nat_lit 1801204810004829071483425

noncomputable def ep702 := nat_lit 26694151010466248881248141312

noncomputable def ep703 := nat_lit 7667274353568739470491467172234677291029117272064

noncomputable def ep704 := @Enclosure.Real.IsNear.mulLit_tf qz134 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz122 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz81 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz81 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz81 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz81 2 k) 1)))))) 149369186655 1099511627776 29525571065863 219026014787862528 182085581365081

noncomputable def ep705 := @ep704 883605516054000 0 1 ep697 ep425 ep698 ep700 (@Enclosure.Complex.IsNear.re_isNear qz121 Bool.true 149369186655 1099511627776 29525571065863 219026014787862528 Bool.true 139196106765 1099511627776 29515163505925 219026014787862528 (ep641 ep653))

noncomputable def ep706 := @Enclosure.Real.IsNear.mulLit_tf qz135 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz122 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz81 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz81 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz81 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz81 2 k) 1)))))) 139196106765 1099511627776 29515163505925 219026014787862528 1769766224729

noncomputable def ep707 := @ep706 3534422064216 0 1 82114856122156289063895 ep632 ep701 ep702 (@Enclosure.Complex.IsNear.im_isNear qz121 Bool.true 149369186655 1099511627776 29525571065863 219026014787862528 Bool.true 139196106765 1099511627776 29515163505925 219026014787862528 (ep641 ep653))

noncomputable abbrev qz587 := (ep693 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep708 := @ep631 ep569 ep425 ep570 ep564 (@ep634 ep635 ep636 ep425 ep637 ep638 ep639 ep567 ep425 ep568 ep427 (ep654 (@ep655 182085581365081 883605516054000 0 1 qz587) rfl) (ep695 (@ep696 182085581365081 883605516054000 0 1 qz587) rfl) rfl rfl) (@ep699 ep700 82114856122156289063895 ep632 ep701 ep702 ep703 ep569 ep425 ep570 ep564 (ep705 (@ep696 182085581365081 883605516054000 0 1 qz587) rfl) (ep707 (@ep655 182085581365081 883605516054000 0 1 qz587) rfl) rfl rfl)

noncomputable def ep709 := @ep573 ep563 ep564 (@ep574 18252167898988544 (BSN.head_sum_c_eq qz5 29) (ep575 (BSN.head_sum_c_succ qz5 28 29 rfl rfl) (ep630 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep708 rfl rfl rfl

noncomputable def ep710 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz5 1 29) Bool.false ep424 ep425 ep426 ep427 Bool.false ep562 ep425 ep563 ep564 (@ep565 ep427 Bool.false ep562 ep425 ep563 ep564 (BSN.zetaApproximant_eq_folded' qz5 1 29 rfl) (ep709 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep711 := @Enclosure.Real.IsNear.mulLit_tf (Real.sin (@HSub.hSub Real Real Real qz392 (Complex.im (@HSub.hSub Complex Complex Complex qz74 qz75 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz76 (@Nat.cast Complex Complex.instNatCast j))))) qz77)) (Complex.im (zetaApproximant qz5 1 29)) 301 1048576 39368873

noncomputable def ep712 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz392 (Complex.im (@HSub.hSub Complex Complex Complex qz74 qz75 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz76 (@Nat.cast Complex Complex.instNatCast j))))) qz77)) Bool.true 301 1048576 39368873

noncomputable def ep713 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz392 (Complex.im (@HSub.hSub Complex Complex Complex qz74 qz75 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz76 (@Nat.cast Complex Complex.instNatCast j))))) qz77) qz393 Bool.false 79060617 524288 195

noncomputable def ep714 := nat_lit 4639587995122537107201418027993936260788088462238080855701546866195529986358881

noncomputable def ep715 := nat_lit 13885283504310464222452462466745690193263771010629311290013630134483747084844641

noncomputable def ep716 := BSN.cos_dyadic_bound_f 3372641749 2147483648 3 2 1048576 398796 ep714 ep57 ep558 ep715 ep60 ep558 301 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3372641749) qz281 0 2 ep714 ep57 ep558 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3372641749) qz282 0 2 ep715 ep60 ep558 rfl rfl rfl rfl) rfl rfl

noncomputable def ep717 := @ep713 524288 Bool.true 301 1048576 1 199203 (@ep432 79060617 524288 195 524288 ep556 rfl) (Enclosure.sfrac_false_div 79060617 524288) (BSN.sin_reduce3 qz393 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 118664282240328321204224) qz38) 226375608064910080 72057594037927936 Bool.false 301 1048576 23 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q3 79060617 524288 226375608064910080 72057594037927936 23 118664282240328321204224 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 301 1048576 118664282240328321204224 75557863725914323419136 3372641749 2147483648 398796 398406 (ep716 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep718 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz5 1 29) Bool.false ep424 ep425 ep426 ep427 Bool.false ep562 ep425 ep563 ep564 (@ep565 ep427 Bool.false ep562 ep425 ep563 ep564 (BSN.zetaApproximant_eq_folded' qz5 1 29 rfl) (ep709 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow50.d11 : Enclosure.Real.IsNear (hardyZApproximantEM 1 29 qz13) Bool.false ep407 ep408 ep409 ep410 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 29 qz13) ep411 Bool.false ep407 ep408 ep409 ep410 (@Eq.refl Real ep411) (@ep412 Bool.false ep407 ep408 ep409 ep410 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz392 (Complex.im (@HSub.hSub Complex Complex Complex qz74 qz75 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz76 (@Nat.cast Complex Complex.instNatCast j))))) qz77) (zetaApproximant qz5 1 29)) (@ep414 ep415 ep416 ep417 ep418 ep419 ep420 ep421 ep422 ep407 ep408 ep409 ep410 (@ep423 104439742464 ep424 ep425 ep426 ep427 ep413 ep415 ep416 ep417 (@ep428 104439742464 1048575 1048576 39368873 104439742464 (ep561 rfl rfl) rfl) ep710 rfl) (@ep711 104439742464 ep562 ep425 ep563 ep564 ep418 ep419 ep420 ep421 (@ep712 104439742464 301 1048576 39368873 104439742464 (ep717 rfl rfl) rfl) ep718 rfl) rfl rfl))

noncomputable abbrev qz615 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 144530 1000)))

noncomputable abbrev qz588 := qz615

noncomputable abbrev qz450 := qz588

noncomputable abbrev qz148 := (BSN.headSumC qz450 9)

noncomputable abbrev qz149 := qz450

noncomputable abbrev qz589 := (@Neg.neg Complex Complex.instNeg qz615)

noncomputable abbrev qz451 := qz589

noncomputable abbrev qz150 := qz451

noncomputable abbrev qz590 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 8) qz150)

noncomputable def ep719 := @Enclosure.Complex.IsNear.of_eq qz148 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz149 8) qz590) Bool.false 1486432300863 549755813888 90162607363671 36504335797977088 Bool.false 60113872579 274877906944 45104736295931 18252167898988544

noncomputable def ep720 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz149 8) qz590 Bool.false 1389924648223 549755813888 80701565958895 36504335797977088 Bool.true 96976147087 1099511627776 161470995931023 73008671595954176 Bool.false

noncomputable abbrev qz591 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 7) qz150)

noncomputable def ep721 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz149 8) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz149 7) qz591) Bool.false 1389924648223 549755813888 80701565958895 36504335797977088 Bool.true 96976147087 1099511627776 161470995931023 73008671595954176

noncomputable def ep722 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz149 7) qz591 Bool.false 2750940954621 1099511627776 423619899683935 219026014787862528 Bool.true 255772984231 549755813888 6619213257493 3422281481060352 Bool.false

noncomputable def ep723 := nat_lit 3056476624907309831684096

noncomputable abbrev qz592 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 6) qz150)

noncomputable def ep724 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz149 7) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz149 6) qz592) Bool.false 2750940954621 1099511627776 423619899683935 219026014787862528 Bool.true 255772984231 549755813888 6619213257493 3422281481060352

noncomputable def ep725 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz149 6) qz592 Bool.false 1326813091815 549755813888 29845527302349 18252167898988544 Bool.true 73348465139 1099511627776 119332483160427 73008671595954176 Bool.false

noncomputable def ep726 := nat_lit 1512345783465499529576448

noncomputable abbrev qz593 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 5) qz150)

noncomputable def ep727 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz149 6) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz149 5) qz593) Bool.false 1326813091815 549755813888 29845527302349 18252167898988544 Bool.true 73348465139 1099511627776 119332483160427 73008671595954176

noncomputable def ep728 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz149 5) qz593 Bool.false 2166313887285 1099511627776 286266243138877 219026014787862528 Bool.true 961046917 137438953472 71574120389167 54756503696965632 Bool.false

noncomputable def ep729 := nat_lit 2917692844672035984506880

noncomputable abbrev qz594 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 4) qz150)

noncomputable def ep730 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz149 5) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz149 4) qz594) Bool.false 2166313887285 1099511627776 286266243138877 219026014787862528 Bool.true 961046917 137438953472 71574120389167 54756503696965632

noncomputable def ep731 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz149 4) qz594 Bool.false 873086414913 549755813888 103039105295707 109513007393931264 Bool.true 362246371965 1099511627776 206133367312475 219026014787862528 Bool.false

noncomputable def ep732 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz149 4) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz149 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz150)) Bool.false 873086414913 549755813888 103039105295707 109513007393931264 Bool.true 362246371965 1099511627776 206133367312475 219026014787862528

noncomputable def ep733 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz149 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz150) Bool.false 114355290531 68719476736 2365025889263 4563041974747136 Bool.false 267038725525 1099511627776 37798938237979 73008671595954176 Bool.true

noncomputable def ep734 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz149 3) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz149 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz150)) Bool.false 114355290531 68719476736 2365025889263 4563041974747136 Bool.false 267038725525 1099511627776 37798938237979 73008671595954176

noncomputable def ep735 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz149 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz150) Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable def ep736 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz149 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz10) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz149)

noncomputable abbrev qz616 := (Enclosure.sfrac Bool.false 144530 1000)

noncomputable abbrev qz595 := qz616

noncomputable abbrev qz452 := qz595

noncomputable abbrev qz151 := (@HMul.hMul Real Real Real qz267 qz452 (Real.log qz279))

noncomputable abbrev qz152 := qz452

noncomputable abbrev qz453 := (@Eq.refl Real qz595)

noncomputable abbrev qz153 := qz453

noncomputable def ep737 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz9 qz150) (Complex.mk (@HMul.hMul Real Real Real qz0 qz11 (Real.cos qz151)) (@HMul.hMul Real Real Real qz0 qz11 (@Neg.neg Real Real.instNeg (Real.sin qz151)))) Bool.false 45635813795 68719476736 2365025889263 4563041974747136 Bool.false 267038725525 1099511627776 37798938237979 73008671595954176 (BSN.cpow_neg_s_mk qz152 144530 1000 2 qz153 rfl)

noncomputable def ep738 := nat_lit 3034197080474803057171176470307619867627614011574410999447150783589846658940865

noncomputable def ep739 := nat_lit 2222534972580474232310297163616401980235403082433510285985041882111372263361

noncomputable def ep740 := nat_lit 7943108249383163429548388369683625478675750806275707886660466746354751408799681

noncomputable def ep741 := BSN.sin_dyadic_bound_f 2620330521 2147483648 3 2 1048576 398796 ep738 ep64 ep739 ep740 ep66 ep739 984784 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2620330521) qz285 0 2 ep738 ep64 ep739 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2620330521) qz286 0 2 ep740 ep66 ep739 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz154 := (Enclosure.Real.IsNear.const Bool.false 144530 1000)

noncomputable abbrev qz454 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26261679) qz32)

noncomputable def ep742 := @Enclosure.Real.IsNear.cos_image qz151 qz454 Bool.false 26261679 262144 381 524288 Bool.false 984784 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz151 Bool.false 328270989 3276800 14453 19920300 26261679 262144 381 524288 (@Enclosure.Real.IsNear.mulLit_ff qz152 qz17 144530 1000 0 1 363408 524288 1 199203 328270989 3276800 14453 19920300 qz154 qz284 rfl) rfl) (Enclosure.sfrac_false_div 26261679 262144) (BSN.cos_reduce3 qz454 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 46097342036983916003328) qz302) 226375608064910080 72057594037927936 Bool.false 984784 1048576 15 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q3 26261679 262144 226375608064910080 72057594037927936 15 46097342036983916003328 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 984784 1048576 46097342036983916003328 37778931862957161709568 2620330521 2147483648 398796 398406 (ep741 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep743 := nat_lit 1686652838029370798087235948910284994006556852244643226486632676164186531528641

noncomputable def ep744 := nat_lit 5055513444142951445797087252403622178059199750569062658887927944728336850059201

noncomputable def ep745 := BSN.cos_dyadic_bound_f 2620330521 2147483648 3 2 1048576 398796 ep743 ep57 ep739 ep744 ep60 ep739 360155 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2620330521) qz281 0 2 ep743 ep57 ep739 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2620330521) qz282 0 2 ep744 ep60 ep739 rfl rfl rfl rfl) rfl rfl

noncomputable def ep746 := @Enclosure.Real.IsNear.sin_image qz151 qz454 Bool.false 26261679 262144 381 524288 Bool.true 360155 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz151 Bool.false 328270989 3276800 14453 19920300 26261679 262144 381 524288 (@Enclosure.Real.IsNear.mulLit_ff qz152 qz17 144530 1000 0 1 363408 524288 1 199203 328270989 3276800 14453 19920300 qz154 qz284 rfl) rfl) (Enclosure.sfrac_false_div 26261679 262144) (BSN.sin_reduce3 qz454 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 46097342036983916003328) qz302) 226375608064910080 72057594037927936 Bool.false 360155 1048576 15 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q3 26261679 262144 226375608064910080 72057594037927936 15 46097342036983916003328 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 360155 1048576 46097342036983916003328 37778931862957161709568 2620330521 2147483648 398796 398406 (ep745 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep747 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz11 (Real.cos qz151)) (@HMul.hMul Real Real Real qz0 qz11 (@Neg.neg Real Real.instNeg (Real.sin qz151))) Bool.false 45635813795 68719476736 2365025889263 4563041974747136 Bool.false 267038725525 1099511627776 37798938237979 73008671595954176 (@Enclosure.Real.IsNear.mulLit_ff qz11 (Real.cos qz151) 741455 1048576 1 1048576 61549 65536 76420631 104439742464 45635813795 68719476736 2365025889263 4563041974747136 qz287 (@Enclosure.Real.IsNear.recentre' (Real.cos qz151) Bool.false 984784 1048576 76420631 104439742464 61549 65536 76420631 104439742464 (ep742 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz11 (@Neg.neg Real Real.instNeg (Real.sin qz151)) 741455 1048576 1 1048576 360155 1048576 76420631 104439742464 267038725525 1099511627776 37798938237979 73008671595954176 qz287 (@Enclosure.Real.IsNear.neg (Real.sin qz151) Bool.true 360155 1048576 76420631 104439742464 (@Enclosure.Real.IsNear.recentre' (Real.sin qz151) Bool.true 360155 1048576 76420631 104439742464 360155 1048576 76420631 104439742464 (ep746 rfl rfl) rfl)) rfl)

noncomputable def ep748 := @ep735 45635813795 68719476736 2365025889263 4563041974747136 Bool.false 267038725525 1099511627776 37798938237979 73008671595954176 Bool.false 114355290531 114355290531 68719476736 2365025889263 4563041974747136 Bool.false 267038725525 267038725525 1099511627776 37798938237979 73008671595954176 (ep736 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz10 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz20)) (ep737 ep747) rfl rfl

noncomputable abbrev qz155 := (@HMul.hMul Real Real Real qz267 qz452 (Real.log (Enclosure.sfrac Bool.false 3 1)))

noncomputable def ep749 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz8 qz150) (Complex.mk (@HMul.hMul Real Real Real qz0 qz21 (Real.cos qz155)) (@HMul.hMul Real Real Real qz0 qz21 (@Neg.neg Real Real.instNeg (Real.sin qz155)))) Bool.true 41755909335 549755813888 46278483953395 109513007393931264 Bool.true 314642548745 549755813888 46368276299269 109513007393931264 (BSN.cpow_neg_s_mk qz152 144530 1000 3 qz153 rfl)

noncomputable def ep750 := BSN.sin_dyadic_bound_f 283336200 2147483648 1 0 1048576 398796 0 1 1 0 1 1 137946 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 283336200) qz285 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 283336200) qz286 0 0 rfl) rfl rfl

noncomputable abbrev qz455 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 41623845) qz32)

noncomputable def ep751 := @Enclosure.Real.IsNear.cos_image qz155 qz455 Bool.false 41623845 262144 381 524288 Bool.true 137946 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz155 Bool.false 8324769017 52428800 14453 19920300 41623845 262144 381 524288 (@Enclosure.Real.IsNear.mulLit_ff qz152 qz23 144530 1000 0 1 575989 524288 1 199203 8324769017 52428800 14453 19920300 qz154 qz290 rfl) rfl) (Enclosure.sfrac_false_div 41623845 262144) (BSN.cos_reduce1 qz455 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4984503157926469304320) qz302) 226375608064910080 72057594037927936 Bool.false 137946 1048576 25 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q1 41623845 262144 226375608064910080 72057594037927936 25 4984503157926469304320 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 137946 1048576 4984503157926469304320 37778931862957161709568 283336200 2147483648 398796 398406 (ep750 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep752 := nat_lit 6444782422476774846862593600000000

noncomputable def ep753 := BSN.cos_dyadic_bound_f 283336200 2147483648 2 1 1048576 398796 ep752 ep184 ep752 ep752 ep185 ep752 1039462 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 283336200) qz281 0 1 ep752 ep184 ep752 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 283336200) qz282 0 1 ep752 ep185 ep752 rfl rfl rfl rfl) rfl rfl

noncomputable def ep754 := @Enclosure.Real.IsNear.sin_image qz155 qz455 Bool.false 41623845 262144 381 524288 Bool.false 1039462 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz155 Bool.false 8324769017 52428800 14453 19920300 41623845 262144 381 524288 (@Enclosure.Real.IsNear.mulLit_ff qz152 qz23 144530 1000 0 1 575989 524288 1 199203 8324769017 52428800 14453 19920300 qz154 qz290 rfl) rfl) (Enclosure.sfrac_false_div 41623845 262144) (BSN.sin_reduce1 qz455 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4984503157926469304320) qz302) 226375608064910080 72057594037927936 Bool.false 1039462 1048576 25 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q1 41623845 262144 226375608064910080 72057594037927936 25 4984503157926469304320 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1039462 1048576 4984503157926469304320 37778931862957161709568 283336200 2147483648 398796 398406 (ep753 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep755 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz21 (Real.cos qz155)) (@HMul.hMul Real Real Real qz0 qz21 (@Neg.neg Real Real.instNeg (Real.sin qz155))) Bool.true 41755909335 549755813888 46278483953395 109513007393931264 Bool.true 314642548745 549755813888 46368276299269 109513007393931264 (@Enclosure.Real.IsNear.mulLit_ft qz21 (Real.cos qz155) 605395 1048576 1 1048576 68973 524288 76420631 104439742464 41755909335 549755813888 46278483953395 109513007393931264 qz292 (@Enclosure.Real.IsNear.recentre' (Real.cos qz155) Bool.true 137946 1048576 76420631 104439742464 68973 524288 76420631 104439742464 (ep751 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz21 (@Neg.neg Real Real.instNeg (Real.sin qz155)) 605395 1048576 1 1048576 519731 524288 76420631 104439742464 314642548745 549755813888 46368276299269 109513007393931264 qz292 (@Enclosure.Real.IsNear.neg (Real.sin qz155) Bool.false 519731 524288 76420631 104439742464 (@Enclosure.Real.IsNear.recentre' (Real.sin qz155) Bool.false 1039462 1048576 76420631 104439742464 519731 524288 76420631 104439742464 (ep754 rfl rfl) rfl)) rfl)

noncomputable def ep756 := @ep733 41755909335 549755813888 46278483953395 109513007393931264 Bool.true 314642548745 549755813888 46368276299269 109513007393931264 Bool.false 59998041578131546963968 873086414913 549755813888 103039105295707 109513007393931264 Bool.true 199147049047593760849920 362246371965 1099511627776 206133367312475 219026014787862528 (ep734 (BSN.head_sum_c_succ qz149 2 3 rfl rfl) (ep748 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep749 ep755) rfl rfl

noncomputable abbrev qz156 := (@HMul.hMul Real Real Real qz267 qz452 (Real.log (Enclosure.sfrac Bool.false 4 1)))

noncomputable def ep757 := @Enclosure.Complex.IsNear.of_eq qz594 (Complex.mk (@HMul.hMul Real Real Real qz0 qz24 (Real.cos qz156)) (@HMul.hMul Real Real Real qz0 qz24 (@Neg.neg Real Real.instNeg (Real.sin qz156)))) Bool.false 420141057459 1099511627776 80188032547463 219026014787862528 Bool.false 354557996629 1099511627776 80163114244193 219026014787862528 (BSN.cpow_neg_s_mk qz152 144530 1000 4 qz153 rfl)

noncomputable def ep758 := nat_lit 783225466739344038802431423941077994339449220137302713966722075938708254140545

noncomputable def ep759 := nat_lit 148254086873298772511209822392974037711112851720273895943876549494357665921

noncomputable def ep760 := nat_lit 2051064763414772855993730818228472789113691870028245712176553446378387896051841

noncomputable def ep761 := BSN.sin_dyadic_bound_f 1867995537 2147483648 3 2 1048576 398796 ep758 ep64 ep759 ep760 ep66 ep759 801357 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1867995537) qz285 0 2 ep758 ep64 ep759 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1867995537) qz286 0 2 ep760 ep66 ep759 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz456 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 105046861) qz37)

noncomputable def ep762 := @Enclosure.Real.IsNear.cos_image qz156 qz456 Bool.false 105046861 524288 761 1048576 Bool.false 801357 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz156 Bool.false 10504686101 52428800 14453 19920300 105046861 524288 761 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz152 qz26 144530 1000 0 1 726817 524288 1 199203 10504686101 52428800 14453 19920300 qz154 qz294 rfl) rfl) (Enclosure.sfrac_false_div 105046861 524288) (BSN.cos_reduce3 qz456 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 65724250049071087091712) qz38) 226375608064910080 72057594037927936 Bool.false 801357 1048576 31 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q3 105046861 524288 226375608064910080 72057594037927936 31 65724250049071087091712 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 801357 1048576 65724250049071087091712 75557863725914323419136 1867995537 2147483648 398796 398406 (ep761 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep763 := nat_lit 435191150004912598789133550999440207538676728010377185046376209543502077929601

noncomputable def ep764 := nat_lit 1305276941840991198822378233353534674540607958327691007347240875531517518456961

noncomputable def ep765 := BSN.cos_dyadic_bound_f 1867995537 2147483648 3 2 1048576 398796 ep763 ep57 ep759 ep764 ep60 ep759 676267 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1867995537) qz281 0 2 ep763 ep57 ep759 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1867995537) qz282 0 2 ep764 ep60 ep759 rfl rfl rfl rfl) rfl rfl

noncomputable def ep766 := @Enclosure.Real.IsNear.sin_image qz156 qz456 Bool.false 105046861 524288 761 1048576 Bool.true 676267 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz156 Bool.false 10504686101 52428800 14453 19920300 105046861 524288 761 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz152 qz26 144530 1000 0 1 726817 524288 1 199203 10504686101 52428800 14453 19920300 qz154 qz294 rfl) rfl) (Enclosure.sfrac_false_div 105046861 524288) (BSN.sin_reduce3 qz456 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 65724250049071087091712) qz38) 226375608064910080 72057594037927936 Bool.false 676267 1048576 31 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q3 105046861 524288 226375608064910080 72057594037927936 31 65724250049071087091712 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 676267 1048576 65724250049071087091712 75557863725914323419136 1867995537 2147483648 398796 398406 (ep765 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep767 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz24 (Real.cos qz156)) (@HMul.hMul Real Real Real qz0 qz24 (@Neg.neg Real Real.instNeg (Real.sin qz156))) Bool.false 420141057459 1099511627776 80188032547463 219026014787862528 Bool.false 354557996629 1099511627776 80163114244193 219026014787862528 (@Enclosure.Real.IsNear.mulLit_ff qz24 (Real.cos qz156) 524287 1048576 1 1048576 801357 1048576 152642059 208879484928 420141057459 1099511627776 80188032547463 219026014787862528 qz296 (@Enclosure.Real.IsNear.recentre' (Real.cos qz156) Bool.false 801357 1048576 152642059 208879484928 801357 1048576 152642059 208879484928 (ep762 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz24 (@Neg.neg Real Real.instNeg (Real.sin qz156)) 524287 1048576 1 1048576 676267 1048576 152642059 208879484928 354557996629 1099511627776 80163114244193 219026014787862528 qz296 (@Enclosure.Real.IsNear.neg (Real.sin qz156) Bool.true 676267 1048576 152642059 208879484928 (@Enclosure.Real.IsNear.recentre' (Real.sin qz156) Bool.true 676267 1048576 152642059 208879484928 676267 1048576 152642059 208879484928 (ep766 rfl rfl) rfl)) rfl)

noncomputable def ep768 := @ep731 420141057459 1099511627776 80188032547463 219026014787862528 Bool.false 354557996629 1099511627776 80163114244193 219026014787862528 Bool.false 1190943654241242269614080 2166313887285 1099511627776 286266243138877 219026014787862528 Bool.true 8453458080638210932736 961046917 137438953472 71574120389167 54756503696965632 (ep732 (BSN.head_sum_c_succ qz149 3 4 rfl rfl) (ep756 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep757 ep767) rfl rfl

noncomputable abbrev qz157 := (@HMul.hMul Real Real Real qz267 qz452 (Real.log (Enclosure.sfrac Bool.false 5 1)))

noncomputable def ep769 := @Enclosure.Complex.IsNear.of_eq qz593 (Complex.mk (@HMul.hMul Real Real Real qz0 qz27 (Real.cos qz157)) (@HMul.hMul Real Real Real qz0 qz27 (@Neg.neg Real Real.instNeg (Real.sin qz157)))) Bool.false 487312296345 1099511627776 71880084489311 219026014787862528 Bool.true 65660089803 1099511627776 71700967924613 219026014787862528 (BSN.cpow_neg_s_mk qz152 144530 1000 5 qz153 rfl)

noncomputable def ep770 := nat_lit 6843436249640776428657350254018816

noncomputable def ep771 := BSN.cos_dyadic_bound_f 287619652 2147483648 2 1 1048576 398796 ep770 ep184 ep770 ep770 ep185 ep770 1039185 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 287619652) qz281 0 1 ep770 ep184 ep770 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 287619652) qz282 0 1 ep770 ep185 ep770 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz457 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 60977785) qz32)

noncomputable def ep772 := @Enclosure.Real.IsNear.cos_image qz157 qz457 Bool.false 60977785 262144 381 524288 Bool.false 1039185 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz157 Bool.false 381111157 1638400 14453 19920300 60977785 262144 381 524288 (@Enclosure.Real.IsNear.mulLit_ff qz152 qz29 144530 1000 0 1 843808 524288 1 199203 381111157 1638400 14453 19920300 qz154 qz298 rfl) rfl) (Enclosure.sfrac_false_div 60977785 262144) (BSN.cos_reduce0 qz457 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 5059858440070428098560) qz302) 226375608064910080 72057594037927936 Bool.false 1039185 1048576 37 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q0 60977785 262144 226375608064910080 72057594037927936 37 5059858440070428098560 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1039185 1048576 5059858440070428098560 37778931862957161709568 287619652 2147483648 398796 398406 (ep771 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep773 := BSN.sin_dyadic_bound_f 287619652 2147483648 1 0 1048576 398796 0 1 1 0 1 1 140019 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 287619652) qz285 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 287619652) qz286 0 0 rfl) rfl rfl

noncomputable def ep774 := @Enclosure.Real.IsNear.sin_image qz157 qz457 Bool.false 60977785 262144 381 524288 Bool.false 140019 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz157 Bool.false 381111157 1638400 14453 19920300 60977785 262144 381 524288 (@Enclosure.Real.IsNear.mulLit_ff qz152 qz29 144530 1000 0 1 843808 524288 1 199203 381111157 1638400 14453 19920300 qz154 qz298 rfl) rfl) (Enclosure.sfrac_false_div 60977785 262144) (BSN.sin_reduce0 qz457 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 5059858440070428098560) qz302) 226375608064910080 72057594037927936 Bool.false 140019 1048576 37 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q0 60977785 262144 226375608064910080 72057594037927936 37 5059858440070428098560 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 140019 1048576 5059858440070428098560 37778931862957161709568 287619652 2147483648 398796 398406 (ep773 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep775 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz27 (Real.cos qz157)) (@HMul.hMul Real Real Real qz0 qz27 (@Neg.neg Real Real.instNeg (Real.sin qz157))) Bool.false 487312296345 1099511627776 71880084489311 219026014787862528 Bool.true 65660089803 1099511627776 71700967924613 219026014787862528 (@Enclosure.Real.IsNear.mulLit_ff qz27 (Real.cos qz157) 468937 1048576 1 1048576 1039185 1048576 76420631 104439742464 487312296345 1099511627776 71880084489311 219026014787862528 qz299 (@Enclosure.Real.IsNear.recentre' (Real.cos qz157) Bool.false 1039185 1048576 76420631 104439742464 1039185 1048576 76420631 104439742464 (ep772 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz27 (@Neg.neg Real Real.instNeg (Real.sin qz157)) 468937 1048576 1 1048576 140019 1048576 76420631 104439742464 65660089803 1099511627776 71700967924613 219026014787862528 qz299 (@Enclosure.Real.IsNear.neg (Real.sin qz157) Bool.false 140019 1048576 76420631 104439742464 (@Enclosure.Real.IsNear.recentre' (Real.sin qz157) Bool.false 140019 1048576 76420631 104439742464 140019 1048576 76420631 104439742464 (ep774 rfl rfl) rfl)) rfl)

noncomputable def ep776 := @ep728 487312296345 1099511627776 71880084489311 219026014787862528 Bool.true 65660089803 1099511627776 71700967924613 219026014787862528 Bool.false ep729 1326813091815 549755813888 29845527302349 18252167898988544 Bool.true 10080936287481635012608 73348465139 1099511627776 119332483160427 73008671595954176 (ep730 (BSN.head_sum_c_succ qz149 4 5 rfl rfl) (ep768 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep769 ep775) rfl rfl

noncomputable abbrev qz158 := (@HMul.hMul Real Real Real qz267 qz452 qz550)

noncomputable def ep777 := @Enclosure.Complex.IsNear.of_eq qz592 (Complex.mk (@HMul.hMul Real Real Real qz0 qz30 (Real.cos qz158)) (@HMul.hMul Real Real Real qz0 qz30 (@Neg.neg Real Real.instNeg (Real.sin qz158)))) Bool.false 97314770991 1099511627776 65473572055747 219026014787862528 Bool.true 438197503323 1099511627776 65632198998271 219026014787862528 (BSN.cpow_neg_s_mk qz152 144530 1000 6 qz153 rfl)

noncomputable def ep778 := @Enclosure.Real.IsNear.mulLit_ff qz152 qz550 144530 1000 0 1 4034681531866359 2251799813685248 500000000199203 99601500000000000000 58313252180064486627 225179981368524800 7226500002879080959 9960150000000000000000 qz154 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 500000000199203 99601500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz300) Bool.false 33845361775666394038272 18889465931478580854784 1000000000398406 199203000000000000000 4034681531866359 2251799813685248 500000000199203 99601500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 212580 524288 24973259072661432 36028797018963968 199203 1000000000000000 rfl rfl rfl rfl (ep116 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep779 := nat_lit 2545984708353539407147116394000950400573655718407624061718437236960828793323776

noncomputable def ep780 := nat_lit 5057396395646300863071653436225842446472368553969414390875775007293456548096

noncomputable def ep781 := nat_lit 7627839332269325619715205875130399516828022418114933356373560160867899466875136

noncomputable def ep782 := BSN.cos_dyadic_bound_f 2903961634 2147483648 3 2 1048576 398796 ep779 ep57 ep780 ep781 ep60 ep780 227329 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2903961634) qz281 0 2 ep779 ep57 ep780 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2903961634) qz282 0 2 ep781 ep60 ep780 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz458 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8485695) (@Nat.cast Real Real.instNatCast 32768))

noncomputable def ep783 := @Enclosure.Real.IsNear.cos_image qz158 qz458 Bool.false 8485695 32768 381 524288 Bool.false 227329 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz158 Bool.false 58313252180064486627 225179981368524800 7226500002879080959 9960150000000000000000 8485695 32768 381 524288 (ep778 rfl) rfl) (Enclosure.sfrac_false_div 8485695 32768) (BSN.cos_reduce0 qz458 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6385879167710139514880) (@Nat.cast Real Real.instNatCast 4722366482869645213696)) 226375608064910080 72057594037927936 Bool.false 227329 1048576 41 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q0 8485695 32768 226375608064910080 72057594037927936 41 6385879167710139514880 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 227329 1048576 6385879167710139514880 4722366482869645213696 2903961634 2147483648 398796 398406 (ep782 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep784 := nat_lit 4578726557919853892174352186452730047075402398290547779580486406523657062744320

noncomputable def ep785 := nat_lit 11983714724197142373344996858955641616474622446435484180363665524216817187062016

noncomputable def ep786 := BSN.sin_dyadic_bound_f 2903961634 2147483648 3 2 1048576 398796 ep784 ep64 ep780 ep785 ep66 ep780 1023637 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2903961634) qz285 0 2 ep784 ep64 ep780 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2903961634) qz286 0 2 ep785 ep66 ep780 rfl rfl rfl rfl) rfl rfl

noncomputable def ep787 := @Enclosure.Real.IsNear.sin_image qz158 qz458 Bool.false 8485695 32768 381 524288 Bool.false 1023637 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz158 Bool.false 58313252180064486627 225179981368524800 7226500002879080959 9960150000000000000000 8485695 32768 381 524288 (ep778 rfl) rfl) (Enclosure.sfrac_false_div 8485695 32768) (BSN.sin_reduce0 qz458 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6385879167710139514880) (@Nat.cast Real Real.instNatCast 4722366482869645213696)) 226375608064910080 72057594037927936 Bool.false 1023637 1048576 41 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q0 8485695 32768 226375608064910080 72057594037927936 41 6385879167710139514880 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1023637 1048576 6385879167710139514880 4722366482869645213696 2903961634 2147483648 398796 398406 (ep786 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep788 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz30 (Real.cos qz158)) (@HMul.hMul Real Real Real qz0 qz30 (@Neg.neg Real Real.instNeg (Real.sin qz158))) Bool.false 97314770991 1099511627776 65473572055747 219026014787862528 Bool.true 438197503323 1099511627776 65632198998271 219026014787862528 (@Enclosure.Real.IsNear.mulLit_ff qz30 (Real.cos qz158) 428079 1048576 1 1048576 227329 1048576 76420631 104439742464 97314770991 1099511627776 65473572055747 219026014787862528 qz303 (@Enclosure.Real.IsNear.recentre' (Real.cos qz158) Bool.false 227329 1048576 76420631 104439742464 227329 1048576 76420631 104439742464 (ep783 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz30 (@Neg.neg Real Real.instNeg (Real.sin qz158)) 428079 1048576 1 1048576 1023637 1048576 76420631 104439742464 438197503323 1099511627776 65632198998271 219026014787862528 qz303 (@Enclosure.Real.IsNear.neg (Real.sin qz158) Bool.false 1023637 1048576 76420631 104439742464 (@Enclosure.Real.IsNear.recentre' (Real.sin qz158) Bool.false 1023637 1048576 76420631 104439742464 1023637 1048576 76420631 104439742464 (ep787 rfl rfl) rfl)) rfl)

noncomputable def ep789 := @ep725 97314770991 1099511627776 65473572055747 219026014787862528 Bool.true 438197503323 1099511627776 65632198998271 219026014787862528 Bool.false ep726 2750940954621 1099511627776 423619899683935 219026014787862528 Bool.true 562450740465903979200512 255772984231 549755813888 6619213257493 3422281481060352 (ep727 (BSN.head_sum_c_succ qz149 5 6 rfl rfl) (ep776 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep777 ep788) rfl rfl

noncomputable abbrev qz159 := (@HMul.hMul Real Real Real qz267 qz452 qz551)

noncomputable def ep790 := @Enclosure.Complex.IsNear.of_eq qz591 (Complex.mk (@HMul.hMul Real Real Real qz0 qz33 (Real.cos qz159)) (@HMul.hMul Real Real Real qz0 qz33 (@Neg.neg Real Real.instNeg (Real.sin qz159)))) Bool.false 28908341825 1099511627776 60589496069435 219026014787862528 Bool.false 414569821375 1099511627776 60783339313517 219026014787862528 (BSN.cpow_neg_s_mk qz152 144530 1000 7 qz153 rfl)

noncomputable def ep791 := @Enclosure.Real.IsNear.mulLit_ff qz152 qz551 144530 1000 0 1 4381796493761783 2251799813685248 500000000199203 99601500000000000000 63330104724339049699 225179981368524800 7226500002879080959 9960150000000000000000 qz154 (BSN.isNear_log_sfrac 7 1 4381796493761783 2251799813685248 500000000199203 99601500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz304) Bool.false 36757173121942042968064 18889465931478580854784 1000000000398406 199203000000000000000 4381796493761783 2251799813685248 500000000199203 99601500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 293399 524288 24973259072661432 36028797018963968 199203 1000000000000000 rfl rfl rfl rfl (ep131 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep792 := BSN.sin_dyadic_bound_f 149504162 2147483648 1 0 1048576 398796 0 1 1 0 1 1 72941 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 149504162) qz285 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 149504162) qz286 0 0 rfl) rfl rfl

noncomputable abbrev qz459 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 73725945) qz32)

noncomputable def ep793 := @Enclosure.Real.IsNear.cos_image qz159 qz459 Bool.false 73725945 262144 381 524288 Bool.false 72941 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz159 Bool.false 63330104724339049699 225179981368524800 7226500002879080959 9960150000000000000000 73725945 262144 381 524288 (ep791 rfl) rfl) (Enclosure.sfrac_false_div 73725945 262144) (BSN.cos_reduce3 qz459 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2630105043571792936960) qz302) 226375608064910080 72057594037927936 Bool.false 72941 1048576 44 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q3 73725945 262144 226375608064910080 72057594037927936 44 2630105043571792936960 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 72941 1048576 2630105043571792936960 37778931862957161709568 149504162 2147483648 398796 398406 (ep792 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep794 := nat_lit 499589304386301016983417881195536

noncomputable def ep795 := BSN.cos_dyadic_bound_f 149504162 2147483648 2 1 1048576 398796 ep794 ep184 ep794 ep794 ep185 ep794 1046035 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 149504162) qz281 0 1 ep794 ep184 ep794 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 149504162) qz282 0 1 ep794 ep185 ep794 rfl rfl rfl rfl) rfl rfl

noncomputable def ep796 := @Enclosure.Real.IsNear.sin_image qz159 qz459 Bool.false 73725945 262144 381 524288 Bool.true 1046035 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz159 Bool.false 63330104724339049699 225179981368524800 7226500002879080959 9960150000000000000000 73725945 262144 381 524288 (ep791 rfl) rfl) (Enclosure.sfrac_false_div 73725945 262144) (BSN.sin_reduce3 qz459 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2630105043571792936960) qz302) 226375608064910080 72057594037927936 Bool.false 1046035 1048576 44 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q3 73725945 262144 226375608064910080 72057594037927936 44 2630105043571792936960 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1046035 1048576 2630105043571792936960 37778931862957161709568 149504162 2147483648 398796 398406 (ep795 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep797 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz33 (Real.cos qz159)) (@HMul.hMul Real Real Real qz0 qz33 (@Neg.neg Real Real.instNeg (Real.sin qz159))) Bool.false 28908341825 1099511627776 60589496069435 219026014787862528 Bool.false 414569821375 1099511627776 60783339313517 219026014787862528 (@Enclosure.Real.IsNear.mulLit_ff qz33 (Real.cos qz159) 396325 1048576 1 1048576 72941 1048576 76420631 104439742464 28908341825 1099511627776 60589496069435 219026014787862528 qz306 (@Enclosure.Real.IsNear.recentre' (Real.cos qz159) Bool.false 72941 1048576 76420631 104439742464 72941 1048576 76420631 104439742464 (ep793 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz33 (@Neg.neg Real Real.instNeg (Real.sin qz159)) 396325 1048576 1 1048576 1046035 1048576 76420631 104439742464 414569821375 1099511627776 60783339313517 219026014787862528 qz306 (@Enclosure.Real.IsNear.neg (Real.sin qz159) Bool.true 1046035 1048576 76420631 104439742464 (@Enclosure.Real.IsNear.recentre' (Real.sin qz159) Bool.true 1046035 1048576 76420631 104439742464 1046035 1048576 76420631 104439742464 (ep796 rfl rfl) rfl)) rfl)

noncomputable def ep798 := @ep722 28908341825 1099511627776 60589496069435 219026014787862528 Bool.false 414569821375 1099511627776 60783339313517 219026014787862528 Bool.false ep723 1389924648223 549755813888 80701565958895 36504335797977088 Bool.true 53313200669536085344256 96976147087 1099511627776 161470995931023 73008671595954176 (ep724 (BSN.head_sum_c_succ qz149 6 7 rfl rfl) (ep789 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep790 ep797) rfl rfl

noncomputable abbrev qz160 := (@HMul.hMul Real Real Real qz267 qz452 qz552)

noncomputable def ep799 := @Enclosure.Complex.IsNear.of_eq qz590 (Complex.mk (@HMul.hMul Real Real Real qz0 qz35 (Real.cos qz160)) (@HMul.hMul Real Real Real qz0 qz35 (@Neg.neg Real Real.instNeg (Real.sin qz160)))) Bool.false 3015864145 17179869184 1182630175597 4563041974747136 Bool.false 337431637403 1099511627776 18947949252701 73008671595954176 (BSN.cpow_neg_s_mk qz152 144530 1000 8 qz153 rfl)

noncomputable def ep800 := @Enclosure.Real.IsNear.mulLit_ff qz152 qz552 144530 1000 0 1 9364972152248037 4503599627370496 1000000000597609 199203000000000000000 135351942516440878761 450359962737049600 14453000008637242877 19920300000000000000000 qz154 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 1000000000597609 199203000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz307) Bool.false 39279540158062550581248 18889465931478580854784 1000000000597609 199203000000000000000 9364972152248037 4503599627370496 1000000000597609 199203000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 524288 24973259072661432 36028797018963968 199203 1000000000000000 rfl rfl rfl rfl (ep146 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep801 := nat_lit 1550070747280157968884306703155641761

noncomputable def ep802 := BSN.sin_dyadic_bound_f 1115803913 2147483648 2 1 1048576 398796 ep801 ep180 ep801 ep801 ep181 ep801 520640 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1115803913) qz285 0 1 ep801 ep180 ep801 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1115803913) qz286 0 1 ep801 ep181 ep801 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz460 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 157570399) qz37)

noncomputable def ep803 := @Enclosure.Real.IsNear.cos_image qz160 qz460 Bool.false 157570399 524288 381 524288 Bool.false 520640 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz160 Bool.false 135351942516440878761 450359962737049600 14453000008637242877 19920300000000000000000 157570399 524288 381 524288 (ep800 rfl) rfl) (Enclosure.sfrac_false_div 157570399 524288) (BSN.cos_reduce3 qz460 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 39258860055756997132288) qz38) 226375608064910080 72057594037927936 Bool.false 520640 1048576 47 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q3 157570399 524288 226375608064910080 72057594037927936 47 39258860055756997132288 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 520640 1048576 39258860055756997132288 75557863725914323419136 1115803913 2147483648 398796 398406 (ep802 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep804 := BSN.cos_dyadic_bound_f 1115803913 2147483648 2 1 1048576 398796 ep801 ep184 ep801 ep801 ep185 ep801 910189 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1115803913) qz281 0 1 ep801 ep184 ep801 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1115803913) qz282 0 1 ep801 ep185 ep801 rfl rfl rfl rfl) rfl rfl

noncomputable def ep805 := @Enclosure.Real.IsNear.sin_image qz160 qz460 Bool.false 157570399 524288 381 524288 Bool.true 910189 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz160 Bool.false 135351942516440878761 450359962737049600 14453000008637242877 19920300000000000000000 157570399 524288 381 524288 (ep800 rfl) rfl) (Enclosure.sfrac_false_div 157570399 524288) (BSN.sin_reduce3 qz460 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 39258860055756997132288) qz38) 226375608064910080 72057594037927936 Bool.false 910189 1048576 47 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q3 157570399 524288 226375608064910080 72057594037927936 47 39258860055756997132288 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 910189 1048576 39258860055756997132288 75557863725914323419136 1115803913 2147483648 398796 398406 (ep804 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep806 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz35 (Real.cos qz160)) (@HMul.hMul Real Real Real qz0 qz35 (@Neg.neg Real Real.instNeg (Real.sin qz160))) Bool.false 3015864145 17179869184 1182630175597 4563041974747136 Bool.false 337431637403 1099511627776 18947949252701 73008671595954176 (@Enclosure.Real.IsNear.mulLit_ff qz35 (Real.cos qz160) 370727 1048576 1 1048576 8135 16384 76420631 104439742464 3015864145 17179869184 1182630175597 4563041974747136 qz309 (@Enclosure.Real.IsNear.recentre' (Real.cos qz160) Bool.false 520640 1048576 76420631 104439742464 8135 16384 76420631 104439742464 (ep803 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz35 (@Neg.neg Real Real.instNeg (Real.sin qz160)) 370727 1048576 1 1048576 910189 1048576 76420631 104439742464 337431637403 1099511627776 18947949252701 73008671595954176 qz309 (@Enclosure.Real.IsNear.neg (Real.sin qz160) Bool.true 910189 1048576 76420631 104439742464 (@Enclosure.Real.IsNear.recentre' (Real.sin qz160) Bool.true 910189 1048576 76420631 104439742464 910189 1048576 76420631 104439742464 (ep805 rfl rfl) rfl)) rfl)

noncomputable def ep807 := @ep720 3015864145 17179869184 1182630175597 4563041974747136 Bool.false 337431637403 1099511627776 18947949252701 73008671595954176 Bool.false 25536712479698470305792 1486432300863 549755813888 90162607363671 36504335797977088 Bool.false 264383607565021364617216 60113872579 274877906944 45104736295931 18252167898988544 (ep721 (BSN.head_sum_c_succ qz149 7 8 rfl rfl) (ep798 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep799 ep806) rfl rfl

theorem EMRow50.d12 : Enclosure.Complex.IsNear qz148 Bool.false 1486432300863 549755813888 90162607363671 36504335797977088 Bool.false 60113872579 274877906944 45104736295931 18252167898988544 := ep719 (BSN.head_sum_c_succ qz149 8 9 rfl rfl) (ep807 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz161 := (BSN.headSumC qz450 17)

noncomputable def ep808 := @Enclosure.Complex.IsNear.of_eq qz161 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz149 16) (@HPow.hPow Complex Complex Complex qz6 qz310 qz150)) Bool.false 3506039949239 1099511627776 909314292051689 219026014787862528 Bool.false 71941935661 549755813888 113708183402449 27378251848482816

noncomputable def ep809 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz149 16) (@HPow.hPow Complex Complex Complex qz6 qz310 qz150) Bool.false 3459757029731 1099511627776 869212701781093 219026014787862528 Bool.true 63534091025 549755813888 217348287604063 54756503696965632 Bool.false

noncomputable def ep810 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz149 16) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz149 15) (@HPow.hPow Complex Complex Complex qz6 qz311 qz150)) Bool.false 3459757029731 1099511627776 869212701781093 219026014787862528 Bool.true 63534091025 549755813888 217348287604063 54756503696965632

noncomputable def ep811 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz149 15) (@HPow.hPow Complex Complex Complex qz6 qz311 qz150) Bool.false 1767184323367 549755813888 68981437988695 18252167898988544 Bool.false 18355534753 137438953472 137968510832651 36504335797977088 Bool.true

noncomputable def ep812 := nat_lit 1902021541734495318704128

noncomputable def ep813 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz149 15) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz149 14) (@HPow.hPow Complex Complex Complex qz6 qz312 qz150)) Bool.false 1767184323367 549755813888 68981437988695 18252167898988544 Bool.false 18355534753 137438953472 137968510832651 36504335797977088

noncomputable def ep814 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz149 14) (@HPow.hPow Complex Complex Complex qz6 qz312 qz150) Bool.false 903949713811 274877906944 392443263410351 109513007393931264 Bool.true 135503627149 1099511627776 784777519154245 219026014787862528 Bool.true

noncomputable def ep815 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz149 14) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz149 13) (@HPow.hPow Complex Complex Complex qz6 qz313 qz150)) Bool.false 903949713811 274877906944 392443263410351 109513007393931264 Bool.true 135503627149 1099511627776 784777519154245 219026014787862528

noncomputable def ep816 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz149 13) (@HPow.hPow Complex Complex Complex qz6 qz313 qz150) Bool.false 3310851454603 1099511627776 246742580649571 73008671595954176 Bool.true 134301364867 1099511627776 246775596156385 73008671595954176 Bool.false

noncomputable def ep817 := nat_lit 3975612885039927833657344

noncomputable def ep818 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz149 13) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz149 12) (@HPow.hPow Complex Complex Complex qz6 qz314 qz150)) Bool.false 3310851454603 1099511627776 246742580649571 73008671595954176 Bool.true 134301364867 1099511627776 246775596156385 73008671595954176

noncomputable def ep819 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz149 12) (@HPow.hPow Complex Complex Complex qz6 qz314 qz150) Bool.false 3139856103121 1099511627776 693850466653919 219026014787862528 Bool.false 133100559539 1099511627776 693886068612485 219026014787862528 Bool.false

noncomputable def ep820 := nat_lit 1820159836087540948926464

noncomputable def ep821 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz149 12) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz149 11) (@HPow.hPow Complex Complex Complex qz6 qz315 qz150)) Bool.false 3139856103121 1099511627776 693850466653919 219026014787862528 Bool.false 133100559539 1099511627776 693886068612485 219026014787862528

noncomputable def ep822 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz149 11) (@HPow.hPow Complex Complex Complex qz6 qz315 qz150) Bool.false 369830747027 137438953472 161353575688757 54756503696965632 Bool.false 102676422779 274877906944 322694584257853 109513007393931264 Bool.false

noncomputable def ep823 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz149 11) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz149 10) (@HPow.hPow Complex Complex Complex qz6 qz316 qz150)) Bool.false 369830747027 137438953472 161353575688757 54756503696965632 Bool.false 102676422779 274877906944 322694584257853 109513007393931264

noncomputable def ep824 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz149 10) (@HPow.hPow Complex Complex Complex qz6 qz316 qz150) Bool.false 2619054075701 1099511627776 594529657924043 219026014787862528 Bool.false 336073296941 1099511627776 594663698833901 219026014787862528 Bool.false

noncomputable def ep825 := nat_lit 3253065653322166740975616

noncomputable abbrev qz596 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 9) qz150)

noncomputable def ep826 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz149 10) (@HAdd.hAdd Complex Complex Complex qz4 qz148 qz596) Bool.false 2619054075701 1099511627776 594529657924043 219026014787862528 Bool.false 336073296941 1099511627776 594663698833901 219026014787862528

noncomputable def ep827 := @Enclosure.Complex.IsNear.addLitP qz148 qz596 Bool.false 1486432300863 549755813888 90162607363671 36504335797977088 Bool.false 60113872579 274877906944 45104736295931 18252167898988544 Bool.true

noncomputable def ep828 := nat_lit 1439840205003686819135488

noncomputable abbrev qz162 := (@HMul.hMul Real Real Real qz267 qz452 qz554)

noncomputable def ep829 := @Enclosure.Complex.IsNear.of_eq qz596 (Complex.mk (@HMul.hMul Real Real Real qz0 qz40 (Real.cos qz162)) (@HMul.hMul Real Real Real qz0 qz40 (@Neg.neg Real Real.instNeg (Real.sin qz162)))) Bool.true 353810526025 1099511627776 53554013742017 219026014787862528 Bool.false 95617806625 1099511627776 53406863282729 219026014787862528 (BSN.cpow_neg_s_mk qz152 144530 1000 9 qz153 rfl)

noncomputable def ep830 := @Enclosure.Real.IsNear.mulLit_ff qz152 qz554 144530 1000 0 1 9895417793173221 4503599627370496 1000000000597609 199203000000000000000 143018473364732563113 450359962737049600 14453000008637242877 19920300000000000000000 qz154 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 1000000000597609 199203000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz317) Bool.false 41504390431577613533184 18889465931478580854784 1000000000597609 199203000000000000000 9895417793173221 4503599627370496 1000000000597609 199203000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 61752 524288 24973259072661432 36028797018963968 199203 1000000000000000 rfl rfl rfl rfl (ep177 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep831 := nat_lit 103223890768586658847516009971201601

noncomputable def ep832 := BSN.cos_dyadic_bound_f 566819857 2147483648 2 1 1048576 398796 ep831 ep184 ep831 ep831 ep185 ep831 1012261 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 566819857) qz281 0 1 ep831 ep184 ep831 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 566819857) qz282 0 1 ep831 ep185 ep831 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz461 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 20811927) (@Nat.cast Real Real.instNatCast 65536))

noncomputable def ep833 := @Enclosure.Real.IsNear.cos_image qz162 qz461 Bool.false 20811927 65536 761 1048576 Bool.true 1012261 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz162 Bool.false 143018473364732563113 450359962737049600 14453000008637242877 19920300000000000000000 20811927 65536 761 1048576 (ep830 rfl) rfl) (Enclosure.sfrac_false_div 20811927 65536) (BSN.cos_reduce2 qz461 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2492900097309576003584) qz556) 226375608064910080 72057594037927936 Bool.false 1012261 1048576 50 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q2 20811927 65536 226375608064910080 72057594037927936 50 2492900097309576003584 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1012261 1048576 2492900097309576003584 9444732965739290427392 566819857 2147483648 398796 398406 (ep832 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep834 := BSN.sin_dyadic_bound_f 566819857 2147483648 2 1 1048576 398796 ep831 ep180 ep831 ep831 ep181 ep831 273565 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 566819857) qz285 0 1 ep831 ep180 ep831 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 566819857) qz286 0 1 ep831 ep181 ep831 rfl rfl rfl rfl) rfl rfl

noncomputable def ep835 := @Enclosure.Real.IsNear.sin_image qz162 qz461 Bool.false 20811927 65536 761 1048576 Bool.true 273565 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz162 Bool.false 143018473364732563113 450359962737049600 14453000008637242877 19920300000000000000000 20811927 65536 761 1048576 (ep830 rfl) rfl) (Enclosure.sfrac_false_div 20811927 65536) (BSN.sin_reduce2 qz461 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2492900097309576003584) qz556) 226375608064910080 72057594037927936 Bool.false 273565 1048576 50 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q2 20811927 65536 226375608064910080 72057594037927936 50 2492900097309576003584 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 273565 1048576 2492900097309576003584 9444732965739290427392 566819857 2147483648 398796 398406 (ep834 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep836 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz40 (Real.cos qz162)) (@HMul.hMul Real Real Real qz0 qz40 (@Neg.neg Real Real.instNeg (Real.sin qz162))) Bool.true 353810526025 1099511627776 53554013742017 219026014787862528 Bool.false 95617806625 1099511627776 53406863282729 219026014787862528 (@Enclosure.Real.IsNear.mulLit_ft qz40 (Real.cos qz162) 349525 1048576 1 1048576 1012261 1048576 152642059 208879484928 353810526025 1099511627776 53554013742017 219026014787862528 qz319 (@Enclosure.Real.IsNear.recentre' (Real.cos qz162) Bool.true 1012261 1048576 152642059 208879484928 1012261 1048576 152642059 208879484928 (ep833 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz40 (@Neg.neg Real Real.instNeg (Real.sin qz162)) 349525 1048576 1 1048576 273565 1048576 152642059 208879484928 95617806625 1099511627776 53406863282729 219026014787862528 qz319 (@Enclosure.Real.IsNear.neg (Real.sin qz162) Bool.true 273565 1048576 152642059 208879484928 (@Enclosure.Real.IsNear.recentre' (Real.sin qz162) Bool.true 273565 1048576 152642059 208879484928 273565 1048576 152642059 208879484928 (ep835 rfl rfl) rfl)) rfl)

noncomputable def ep837 := @ep827 353810526025 1099511627776 53554013742017 219026014787862528 Bool.false 95617806625 1099511627776 53406863282729 219026014787862528 Bool.false ep828 2619054075701 1099511627776 594529657924043 219026014787862528 Bool.false 92379124442911477858304 336073296941 1099511627776 594663698833901 219026014787862528 EMRow50.d12 (ep829 ep836) rfl rfl

noncomputable abbrev qz163 := (@HMul.hMul Real Real Real qz267 qz452 qz555)

noncomputable def ep838 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz316 qz150) (Complex.mk (@HMul.hMul Real Real Real qz0 qz42 (Real.cos qz163)) (@HMul.hMul Real Real Real qz0 qz42 (@Neg.neg Real Real.instNeg (Real.sin qz163)))) Bool.false 339591900515 1099511627776 16961548276995 73008671595954176 Bool.false 74632394175 1099511627776 16908489893935 73008671595954176 (BSN.cpow_neg_s_mk qz152 144530 1000 10 qz153 rfl)

noncomputable def ep839 := @Enclosure.Real.IsNear.mulLit_ff qz152 qz555 144530 1000 0 1 10369917190100709 4503599627370496 1000000000597609 199203000000000000000 149876413148525547177 450359962737049600 14453000008637242877 19920300000000000000000 qz154 (BSN.isNear_log_sfrac 10 1 10369917190100709 4503599627370496 1000000000597609 199203000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz321) Bool.false 43494585150108164161536 18889465931478580854784 1000000000597609 199203000000000000000 10369917190100709 4503599627370496 1000000000597609 199203000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 116991 524288 24973259072661432 36028797018963968 199203 1000000000000000 rfl rfl rfl rfl (ep192 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep840 := nat_lit 4608650732503134797052750654923565201821064327275367279793293906222632525267200

noncomputable def ep841 := nat_lit 5123643542530227121439890014202982644300708470192972164470721099793666048256

noncomputable def ep842 := nat_lit 12061980305106018386465349036205389747154872091055173301668531444040562106859776

noncomputable def ep843 := BSN.sin_dyadic_bound_f 2908689502 2147483648 3 2 1048576 398796 ep840 ep64 ep841 ep842 ep66 ep841 1024135 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2908689502) qz285 0 2 ep840 ep64 ep841 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2908689502) qz286 0 2 ep842 ep66 ep841 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz462 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 348958217) qz16)

noncomputable def ep844 := @Enclosure.Real.IsNear.cos_image qz163 qz462 Bool.false 348958217 1048576 381 524288 Bool.false 1024135 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz163 Bool.false 149876413148525547177 450359962737049600 14453000008637242877 19920300000000000000000 348958217 1048576 381 524288 (ep839 rfl) rfl) (Enclosure.sfrac_false_div 348958217 1048576) (BSN.cos_reduce3 qz462 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 204680827491112760377344) qz19) 226375608064910080 72057594037927936 Bool.false 1024135 1048576 52 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q3 348958217 1048576 226375608064910080 72057594037927936 52 204680827491112760377344 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1024135 1048576 204680827491112760377344 151115727451828646838272 2908689502 2147483648 398796 398406 (ep843 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep845 := nat_lit 2562638692965088321527723648297181993298058274473067587513816935056926365614336

noncomputable def ep846 := nat_lit 7677668791810204510340291164863140014605573406478816818212509362971191764746496

noncomputable def ep847 := BSN.cos_dyadic_bound_f 2908689502 2147483648 3 2 1048576 398796 ep845 ep57 ep841 ep846 ep60 ep841 225075 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2908689502) qz281 0 2 ep845 ep57 ep841 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2908689502) qz282 0 2 ep846 ep60 ep841 rfl rfl rfl rfl) rfl rfl

noncomputable def ep848 := @Enclosure.Real.IsNear.sin_image qz163 qz462 Bool.false 348958217 1048576 381 524288 Bool.true 225075 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz163 Bool.false 149876413148525547177 450359962737049600 14453000008637242877 19920300000000000000000 348958217 1048576 381 524288 (ep839 rfl) rfl) (Enclosure.sfrac_false_div 348958217 1048576) (BSN.sin_reduce3 qz462 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 204680827491112760377344) qz19) 226375608064910080 72057594037927936 Bool.false 225075 1048576 52 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q3 348958217 1048576 226375608064910080 72057594037927936 52 204680827491112760377344 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 225075 1048576 204680827491112760377344 151115727451828646838272 2908689502 2147483648 398796 398406 (ep847 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep849 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz42 (Real.cos qz163)) (@HMul.hMul Real Real Real qz0 qz42 (@Neg.neg Real Real.instNeg (Real.sin qz163))) Bool.false 339591900515 1099511627776 16961548276995 73008671595954176 Bool.false 74632394175 1099511627776 16908489893935 73008671595954176 (@Enclosure.Real.IsNear.mulLit_ff qz42 (Real.cos qz163) 331589 1048576 1 1048576 1024135 1048576 76420631 104439742464 339591900515 1099511627776 16961548276995 73008671595954176 qz323 (@Enclosure.Real.IsNear.recentre' (Real.cos qz163) Bool.false 1024135 1048576 76420631 104439742464 1024135 1048576 76420631 104439742464 (ep844 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz42 (@Neg.neg Real Real.instNeg (Real.sin qz163)) 331589 1048576 1 1048576 225075 1048576 76420631 104439742464 74632394175 1099511627776 16908489893935 73008671595954176 qz323 (@Enclosure.Real.IsNear.neg (Real.sin qz163) Bool.true 225075 1048576 76420631 104439742464 (@Enclosure.Real.IsNear.recentre' (Real.sin qz163) Bool.true 225075 1048576 76420631 104439742464 225075 1048576 76420631 104439742464 (ep848 rfl rfl) rfl)) rfl)

noncomputable def ep850 := @ep824 339591900515 1099511627776 16961548276995 73008671595954176 Bool.false 74632394175 1099511627776 16908489893935 73008671595954176 Bool.false ep825 369830747027 137438953472 161353575688757 54756503696965632 Bool.false 451575682975820222038016 102676422779 274877906944 322694584257853 109513007393931264 (ep826 (BSN.head_sum_c_succ qz149 9 10 rfl rfl) (ep837 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep838 ep849) rfl rfl

noncomputable abbrev qz164 := (@HMul.hMul Real Real Real qz267 qz452 qz557)

noncomputable def ep851 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz315 qz150) (Complex.mk (@HMul.hMul Real Real Real qz0 qz44 (Real.cos qz164)) (@HMul.hMul Real Real Real qz0 qz44 (@Neg.neg Real Real.instNeg (Real.sin qz164)))) Bool.false 181210126905 1099511627776 701973389839 3174290069389312 Bool.true 277605131577 1099511627776 702853624591 3174290069389312 (BSN.cpow_neg_s_mk qz152 144530 1000 11 qz153 rfl)

noncomputable def ep852 := @Enclosure.Real.IsNear.mulLit_ff qz152 qz557 144530 1000 0 1 10799156221662949 4503599627370496 1000000000597609 199203000000000000000 156080204871694601897 450359962737049600 14453000008637242877 19920300000000000000000 qz154 (BSN.isNear_log_sfrac 11 1 10799156221662949 4503599627370496 1000000000597609 199203000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz325) Bool.false 45294944137145793642496 18889465931478580854784 1000000000597609 199203000000000000000 10799156221662949 4503599627370496 1000000000597609 199203000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 166961 524288 24973259072661432 36028797018963968 199203 1000000000000000 rfl rfl rfl rfl (ep207 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep853 := nat_lit 737715894904582719042727698123485363239842744815764562677629116854005877144161

noncomputable def ep854 := nat_lit 425813371348527212004593265673380649072335335741590460655658312114504170081

noncomputable def ep855 := nat_lit 2212296057971051102704173907839109328421383563775810507111576033937788623092321

noncomputable def ep856 := BSN.cos_dyadic_bound_f 2131338411 2147483648 3 2 1048576 398796 ep853 ep57 ep854 ep855 ep60 ep854 573165 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2131338411) qz281 0 2 ep853 ep57 ep854 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2131338411) qz282 0 2 ep855 ep60 ep854 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz463 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 363402545) qz16)

noncomputable def ep857 := @Enclosure.Real.IsNear.cos_image qz164 qz463 Bool.false 363402545 1048576 381 524288 Bool.false 573165 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz164 Bool.false 156080204871694601897 450359962737049600 14453000008637242877 19920300000000000000000 363402545 1048576 381 524288 (ep852 rfl) rfl) (Enclosure.sfrac_false_div 363402545 1048576) (BSN.cos_reduce0 qz463 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 149979607420023487856640) qz19) 226375608064910080 72057594037927936 Bool.false 573165 1048576 55 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q0 363402545 1048576 226375608064910080 72057594037927936 55 149979607420023487856640 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 573165 1048576 149979607420023487856640 151115727451828646838272 2131338411 2147483648 398796 398406 (ep856 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep858 := nat_lit 1327547960131170072507306182009734949312459072399782940451207883687518975523425

noncomputable def ep859 := nat_lit 3476221912028024002985413516166787012862704265741564173769244820009602405333601

noncomputable def ep860 := BSN.sin_dyadic_bound_f 2131338411 2147483648 3 2 1048576 398796 ep858 ep64 ep854 ep859 ep66 ep854 878061 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2131338411) qz285 0 2 ep858 ep64 ep854 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2131338411) qz286 0 2 ep859 ep66 ep854 rfl rfl rfl rfl) rfl rfl

noncomputable def ep861 := @Enclosure.Real.IsNear.sin_image qz164 qz463 Bool.false 363402545 1048576 381 524288 Bool.false 878061 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz164 Bool.false 156080204871694601897 450359962737049600 14453000008637242877 19920300000000000000000 363402545 1048576 381 524288 (ep852 rfl) rfl) (Enclosure.sfrac_false_div 363402545 1048576) (BSN.sin_reduce0 qz463 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 149979607420023487856640) qz19) 226375608064910080 72057594037927936 Bool.false 878061 1048576 55 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q0 363402545 1048576 226375608064910080 72057594037927936 55 149979607420023487856640 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 878061 1048576 149979607420023487856640 151115727451828646838272 2131338411 2147483648 398796 398406 (ep860 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep862 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz44 (Real.cos qz164)) (@HMul.hMul Real Real Real qz0 qz44 (@Neg.neg Real Real.instNeg (Real.sin qz164))) Bool.false 181210126905 1099511627776 701973389839 3174290069389312 Bool.true 277605131577 1099511627776 702853624591 3174290069389312 (@Enclosure.Real.IsNear.mulLit_ff qz44 (Real.cos qz164) 316157 1048576 1 1048576 573165 1048576 76420631 104439742464 181210126905 1099511627776 701973389839 3174290069389312 qz327 (@Enclosure.Real.IsNear.recentre' (Real.cos qz164) Bool.false 573165 1048576 76420631 104439742464 573165 1048576 76420631 104439742464 (ep857 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz44 (@Neg.neg Real Real.instNeg (Real.sin qz164)) 316157 1048576 1 1048576 878061 1048576 76420631 104439742464 277605131577 1099511627776 702853624591 3174290069389312 qz327 (@Enclosure.Real.IsNear.neg (Real.sin qz164) Bool.false 878061 1048576 76420631 104439742464 (@Enclosure.Real.IsNear.recentre' (Real.sin qz164) Bool.false 878061 1048576 76420631 104439742464 878061 1048576 76420631 104439742464 (ep861 rfl rfl) rfl)) rfl)

noncomputable def ep863 := @ep822 181210126905 1099511627776 701973389839 3174290069389312 Bool.true 277605131577 1099511627776 702853624591 3174290069389312 Bool.false 431538536865622352986112 3139856103121 1099511627776 693850466653919 219026014787862528 Bool.false 36586403219155573538816 133100559539 1099511627776 693886068612485 219026014787862528 (ep823 (BSN.head_sum_c_succ qz149 10 11 rfl rfl) (ep850 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep851 ep862) rfl rfl

noncomputable abbrev qz165 := (@HMul.hMul Real Real Real qz267 qz452 qz558)

noncomputable def ep864 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz314 qz150) (Complex.mk (@HMul.hMul Real Real Real qz0 qz46 (Real.cos qz165)) (@HMul.hMul Real Real Real qz0 qz46 (@Neg.neg Real Real.instNeg (Real.sin qz165)))) Bool.false 85497675741 549755813888 23188637647397 109513007393931264 Bool.true 133700962203 549755813888 23220359928335 109513007393931264 (BSN.cpow_neg_s_mk qz152 144530 1000 12 qz153 rfl)

noncomputable def ep865 := @Enclosure.Real.IsNear.mulLit_ff qz152 qz558 144530 1000 0 1 11191020447815397 4503599627370496 1000000000597609 199203000000000000000 161743818532275932841 450359962737049600 14453000008637242877 19920300000000000000000 qz154 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 1000000000597609 199203000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz329) Bool.false 46938541828353910898688 18889465931478580854784 1000000000597609 199203000000000000000 11191020447815397 4503599627370496 1000000000597609 199203000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 212580 524288 24973259072661432 36028797018963968 199203 1000000000000000 rfl rfl rfl rfl (ep222 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep866 := nat_lit 766012843815972632200276929864326022596798999417489044026333167638642375926016

noncomputable def ep867 := nat_lit 459085839652433281553213478525340329295609700736864604875091510856696340736

noncomputable def ep868 := nat_lit 2297120359768613030037724362635927387131805778850993402869249319894213735096576

noncomputable def ep869 := BSN.cos_dyadic_bound_f 2151477146 2147483648 3 2 1048576 398796 ep866 ep57 ep867 ep868 ep60 ep867 564906 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2151477146) qz281 0 2 ep866 ep57 ep867 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2151477146) qz282 0 2 ep868 ep60 ep867 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz464 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 376589173) qz16)

noncomputable def ep870 := @Enclosure.Real.IsNear.cos_image qz165 qz464 Bool.false 376589173 1048576 381 524288 Bool.false 564906 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz165 Bool.false 161743818532275932841 450359962737049600 14453000008637242877 19920300000000000000000 376589173 1048576 381 524288 (ep865 rfl) rfl) (Enclosure.sfrac_false_div 376589173 1048576) (BSN.cos_reduce0 qz464 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 151396744908201437167616) qz19) 226375608064910080 72057594037927936 Bool.false 564906 1048576 57 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q0 376589173 1048576 226375608064910080 72057594037927936 57 151396744908201437167616 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 564906 1048576 151396744908201437167616 151115727451828646838272 2151477146 2147483648 398796 398406 (ep869 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep871 := nat_lit 1378455850197028791335255902972966568410801711190890787563499628540870919594240

noncomputable def ep872 := nat_lit 3609498230585161942469822162154442842447525875508282853306034593256132042957056

noncomputable def ep873 := BSN.sin_dyadic_bound_f 2151477146 2147483648 3 2 1048576 398796 ep871 ep64 ep867 ep872 ep66 ep867 883398 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2151477146) qz285 0 2 ep871 ep64 ep867 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2151477146) qz286 0 2 ep872 ep66 ep867 rfl rfl rfl rfl) rfl rfl

noncomputable def ep874 := @Enclosure.Real.IsNear.sin_image qz165 qz464 Bool.false 376589173 1048576 381 524288 Bool.false 883398 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz165 Bool.false 161743818532275932841 450359962737049600 14453000008637242877 19920300000000000000000 376589173 1048576 381 524288 (ep865 rfl) rfl) (Enclosure.sfrac_false_div 376589173 1048576) (BSN.sin_reduce0 qz464 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 151396744908201437167616) qz19) 226375608064910080 72057594037927936 Bool.false 883398 1048576 57 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q0 376589173 1048576 226375608064910080 72057594037927936 57 151396744908201437167616 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 883398 1048576 151396744908201437167616 151115727451828646838272 2151477146 2147483648 398796 398406 (ep873 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep875 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz46 (Real.cos qz165)) (@HMul.hMul Real Real Real qz0 qz46 (@Neg.neg Real Real.instNeg (Real.sin qz165))) Bool.false 85497675741 549755813888 23188637647397 109513007393931264 Bool.true 133700962203 549755813888 23220359928335 109513007393931264 (@Enclosure.Real.IsNear.mulLit_ff qz46 (Real.cos qz165) 302697 1048576 1 1048576 282453 524288 76420631 104439742464 85497675741 549755813888 23188637647397 109513007393931264 qz331 (@Enclosure.Real.IsNear.recentre' (Real.cos qz165) Bool.false 564906 1048576 76420631 104439742464 282453 524288 76420631 104439742464 (ep870 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz46 (@Neg.neg Real Real.instNeg (Real.sin qz165)) 302697 1048576 1 1048576 441699 524288 76420631 104439742464 133700962203 549755813888 23220359928335 109513007393931264 qz331 (@Enclosure.Real.IsNear.neg (Real.sin qz165) Bool.false 441699 524288 76420631 104439742464 (@Enclosure.Real.IsNear.recentre' (Real.sin qz165) Bool.false 883398 1048576 76420631 104439742464 441699 524288 76420631 104439742464 (ep874 rfl rfl) rfl)) rfl)

noncomputable def ep876 := @ep819 85497675741 549755813888 23188637647397 109513007393931264 Bool.true 133700962203 549755813888 23220359928335 109513007393931264 Bool.false ep820 3310851454603 1099511627776 246742580649571 73008671595954176 Bool.true 73832956148726833872896 134301364867 1099511627776 246775596156385 73008671595954176 (ep821 (BSN.head_sum_c_succ qz149 11 12 rfl rfl) (ep863 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep864 ep875) rfl rfl

noncomputable abbrev qz166 := (@HMul.hMul Real Real Real qz267 qz452 qz559)

noncomputable def ep877 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz313 qz150) (Complex.mk (@HMul.hMul Real Real Real qz0 qz48 (Real.cos qz166)) (@HMul.hMul Real Real Real qz0 qz48 (@Neg.neg Real Real.instNeg (Real.sin qz166)))) Bool.false 304947400641 1099511627776 44658784871989 219026014787862528 Bool.true 601131141 549755813888 22225365342545 109513007393931264 (BSN.cpow_neg_s_mk qz152 144530 1000 13 qz153 rfl)

noncomputable def ep878 := @Enclosure.Real.IsNear.mulLit_ff qz152 qz559 144530 1000 0 1 11551497052968677 4503599627370496 1000000000597609 199203000000000000000 166953786906556288681 450359962737049600 14453000008637242877 19920300000000000000000 qz154 (BSN.isNear_log_sfrac 13 1 11551497052968677 4503599627370496 1000000000597609 199203000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz333) Bool.false 48450490295254733815808 18889465931478580854784 1000000000597609 199203000000000000000 11551497052968677 4503599627370496 1000000000597609 199203000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 254545 524288 24973259072661432 36028797018963968 199203 1000000000000000 rfl rfl rfl rfl (ep236 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep879 := BSN.cos_dyadic_bound_f 8467081 2147483648 1 0 1048576 398796 0 1 1 0 1 1 1048567 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 8467081) qz281 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 8467081) qz282 0 0 rfl) rfl rfl

noncomputable abbrev qz465 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 48589947) (@Nat.cast Real Real.instNatCast 131072))

noncomputable def ep880 := @Enclosure.Real.IsNear.cos_image qz166 qz465 Bool.false 48589947 131072 381 524288 Bool.false 1048567 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz166 Bool.false 166953786906556288681 450359962737049600 14453000008637242877 19920300000000000000000 48589947 131072 381 524288 (ep878 rfl) rfl) (Enclosure.sfrac_false_div 48589947 131072) (BSN.cos_reduce0 qz465 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 74477233869814759424) qz295) 226375608064910080 72057594037927936 Bool.false 1048567 1048576 59 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q0 48589947 131072 226375608064910080 72057594037927936 59 74477233869814759424 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1048567 1048576 74477233869814759424 18889465931478580854784 8467081 2147483648 398796 398406 (ep879 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep881 := BSN.sin_dyadic_bound_f 8467081 2147483648 1 0 1048576 398796 0 1 1 0 1 1 4134 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 8467081) qz285 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 8467081) qz286 0 0 rfl) rfl rfl

noncomputable def ep882 := @Enclosure.Real.IsNear.sin_image qz166 qz465 Bool.false 48589947 131072 381 524288 Bool.false 4134 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz166 Bool.false 166953786906556288681 450359962737049600 14453000008637242877 19920300000000000000000 48589947 131072 381 524288 (ep878 rfl) rfl) (Enclosure.sfrac_false_div 48589947 131072) (BSN.sin_reduce0 qz465 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 74477233869814759424) qz295) 226375608064910080 72057594037927936 Bool.false 4134 1048576 59 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q0 48589947 131072 226375608064910080 72057594037927936 59 74477233869814759424 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 4134 1048576 74477233869814759424 18889465931478580854784 8467081 2147483648 398796 398406 (ep881 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep883 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz48 (Real.cos qz166)) (@HMul.hMul Real Real Real qz0 qz48 (@Neg.neg Real Real.instNeg (Real.sin qz166))) Bool.false 304947400641 1099511627776 44658784871989 219026014787862528 Bool.true 601131141 549755813888 22225365342545 109513007393931264 (@Enclosure.Real.IsNear.mulLit_ff qz48 (Real.cos qz166) 290823 1048576 1 1048576 1048567 1048576 76420631 104439742464 304947400641 1099511627776 44658784871989 219026014787862528 qz335 (@Enclosure.Real.IsNear.recentre' (Real.cos qz166) Bool.false 1048567 1048576 76420631 104439742464 1048567 1048576 76420631 104439742464 (ep880 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz48 (@Neg.neg Real Real.instNeg (Real.sin qz166)) 290823 1048576 1 1048576 2067 524288 76420631 104439742464 601131141 549755813888 22225365342545 109513007393931264 qz335 (@Enclosure.Real.IsNear.neg (Real.sin qz166) Bool.false 2067 524288 76420631 104439742464 (@Enclosure.Real.IsNear.recentre' (Real.sin qz166) Bool.false 4134 1048576 76420631 104439742464 2067 524288 76420631 104439742464 (ep882 rfl rfl) rfl)) rfl)

noncomputable def ep884 := @ep816 304947400641 1099511627776 44658784871989 219026014787862528 Bool.true 601131141 549755813888 22225365342545 109513007393931264 Bool.false ep817 903949713811 274877906944 392443263410351 109513007393931264 Bool.true 74493906828074588045312 135503627149 1099511627776 784777519154245 219026014787862528 (ep818 (BSN.head_sum_c_succ qz149 12 13 rfl rfl) (ep876 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep877 ep883) rfl rfl

noncomputable abbrev qz167 := (@HMul.hMul Real Real Real qz267 qz452 qz560)

noncomputable def ep885 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz312 qz150) (Complex.mk (@HMul.hMul Real Real Real qz0 qz50 (Real.cos qz167)) (@HMul.hMul Real Real Real qz0 qz50 (@Neg.neg Real Real.instNeg (Real.sin qz167)))) Bool.true 40715104255 549755813888 21445364521819 109513007393931264 Bool.false 282347905173 1099511627776 43033545841661 219026014787862528 (BSN.cpow_neg_s_mk qz152 144530 1000 14 qz153 rfl)

noncomputable def ep886 := @Enclosure.Real.IsNear.mulLit_ff qz152 qz560 144530 1000 0 1 11885250371606245 4503599627370496 1000000000597609 199203000000000000000 34355504724165011797 90071992547409920 14453000008637242877 19920300000000000000000 qz154 (BSN.isNear_log_sfrac 14 1 11885250371606245 4503599627370496 1000000000597609 199203000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz337) Bool.false 49850353174629559828480 18889465931478580854784 1000000000597609 199203000000000000000 11885250371606245 4503599627370496 1000000000597609 199203000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 293399 524288 24973259072661432 36028797018963968 199203 1000000000000000 rfl rfl rfl rfl (ep251 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep887 := nat_lit 2107842478620458292846292737226663451518063840314331506274925865367168000000000

noncomputable def ep888 := nat_lit 3468871437773708848239235728278227954304391041743223744611210000000000000000

noncomputable def ep889 := nat_lit 6316589692985827460842399740223433898645582738859508071335555176101504000000000

noncomputable def ep890 := BSN.cos_dyadic_bound_f 2770279100 2147483648 3 2 1048576 398796 ep887 ep57 ep888 ep889 ep60 ep888 290570 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2770279100) qz281 0 2 ep887 ep57 ep888 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2770279100) qz282 0 2 ep889 ep60 ep888 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz466 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 399950713) qz16)

noncomputable def ep891 := @Enclosure.Real.IsNear.cos_image qz167 qz466 Bool.false 399950713 1048576 381 524288 Bool.true 290570 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz167 Bool.false 34355504724165011797 90071992547409920 14453000008637242877 19920300000000000000000 399950713 1048576 381 524288 (ep886 rfl) rfl) (Enclosure.sfrac_false_div 399950713 1048576) (BSN.cos_reduce2 qz466 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 194941061318035296485376) qz19) 226375608064910080 72057594037927936 Bool.false 290570 1048576 60 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q2 399950713 1048576 226375608064910080 72057594037927936 60 194941061318035296485376 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 290570 1048576 194941061318035296485376 151115727451828646838272 2770279100 2147483648 398796 398406 (ep890 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep892 := nat_lit 3791341364366605960044735538425371630369071399732402132299177589660902400000000

noncomputable def ep893 := nat_lit 9924087305299001033410491457077808567612027509041087984244666013873792000000000

noncomputable def ep894 := BSN.sin_dyadic_bound_f 2770279100 2147483648 3 2 1048576 398796 ep892 ep64 ep888 ep893 ep66 ep888 1007511 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2770279100) qz285 0 2 ep892 ep64 ep888 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2770279100) qz286 0 2 ep893 ep66 ep888 rfl rfl rfl rfl) rfl rfl

noncomputable def ep895 := @Enclosure.Real.IsNear.sin_image qz167 qz466 Bool.false 399950713 1048576 381 524288 Bool.true 1007511 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz167 Bool.false 34355504724165011797 90071992547409920 14453000008637242877 19920300000000000000000 399950713 1048576 381 524288 (ep886 rfl) rfl) (Enclosure.sfrac_false_div 399950713 1048576) (BSN.sin_reduce2 qz466 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 194941061318035296485376) qz19) 226375608064910080 72057594037927936 Bool.false 1007511 1048576 60 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q2 399950713 1048576 226375608064910080 72057594037927936 60 194941061318035296485376 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1007511 1048576 194941061318035296485376 151115727451828646838272 2770279100 2147483648 398796 398406 (ep894 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep896 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz50 (Real.cos qz167)) (@HMul.hMul Real Real Real qz0 qz50 (@Neg.neg Real Real.instNeg (Real.sin qz167))) Bool.true 40715104255 549755813888 21445364521819 109513007393931264 Bool.false 282347905173 1099511627776 43033545841661 219026014787862528 (@Enclosure.Real.IsNear.mulLit_ft qz50 (Real.cos qz167) 280243 1048576 1 1048576 145285 524288 76420631 104439742464 40715104255 549755813888 21445364521819 109513007393931264 qz339 (@Enclosure.Real.IsNear.recentre' (Real.cos qz167) Bool.true 290570 1048576 76420631 104439742464 145285 524288 76420631 104439742464 (ep891 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz50 (@Neg.neg Real Real.instNeg (Real.sin qz167)) 280243 1048576 1 1048576 1007511 1048576 76420631 104439742464 282347905173 1099511627776 43033545841661 219026014787862528 qz339 (@Enclosure.Real.IsNear.neg (Real.sin qz167) Bool.true 1007511 1048576 76420631 104439742464 (@Enclosure.Real.IsNear.recentre' (Real.sin qz167) Bool.true 1007511 1048576 76420631 104439742464 1007511 1048576 76420631 104439742464 (ep895 rfl rfl) rfl)) rfl)

noncomputable def ep897 := @ep814 40715104255 549755813888 21445364521819 109513007393931264 Bool.false 282347905173 1099511627776 43033545841661 219026014787862528 Bool.false 485759927991369830760448 1767184323367 549755813888 68981437988695 18252167898988544 Bool.false 161456991159759744794624 18355534753 137438953472 137968510832651 36504335797977088 (ep815 (BSN.head_sum_c_succ qz149 13 14 rfl rfl) (ep884 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep885 ep896) rfl rfl

noncomputable abbrev qz168 := (@HMul.hMul Real Real Real qz267 qz452 qz561)

noncomputable def ep898 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz311 qz150) (Complex.mk (@HMul.hMul Real Real Real qz0 qz52 (Real.cos qz168)) (@HMul.hMul Real Real Real qz0 qz52 (@Neg.neg Real Real.instNeg (Real.sin qz168)))) Bool.true 74611617003 1099511627776 41435445916753 219026014787862528 Bool.true 136956230037 549755813888 20791042710173 109513007393931264 (BSN.cpow_neg_s_mk qz152 144530 1000 15 qz153 rfl)

noncomputable def ep899 := @Enclosure.Real.IsNear.mulLit_ff qz152 qz561 144530 1000 0 1 12195965485668069 4503599627370496 1000000000597609 199203000000000000000 176268289164360601257 450359962737049600 14453000008637242877 19920300000000000000000 qz154 (BSN.isNear_log_sfrac 15 1 12195965485668069 4503599627370496 1000000000597609 199203000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz341) Bool.false 51153586820399524478976 18889465931478580854784 1000000000597609 199203000000000000000 12195965485668069 4503599627370496 1000000000597609 199203000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 329571 524288 24973259072661432 36028797018963968 199203 1000000000000000 rfl rfl rfl rfl (ep265 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep900 := nat_lit 106379686464765909133794408821769361

noncomputable def ep901 := BSN.sin_dyadic_bound_f 571103309 2147483648 2 1 1048576 398796 ep900 ep180 ep900 ep900 ep181 ep900 275583 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 571103309) qz285 0 1 ep900 ep180 ep900 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 571103309) qz286 0 1 ep900 ep181 ep900 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz467 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6412603) (@Nat.cast Real Real.instNatCast 16384))

noncomputable def ep902 := @Enclosure.Real.IsNear.cos_image qz168 qz467 Bool.false 6412603 16384 381 524288 Bool.true 275583 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz168 Bool.false 176268289164360601257 450359962737049600 14453000008637242877 19920300000000000000000 6412603 16384 381 524288 (ep899 rfl) rfl) (Enclosure.sfrac_false_div 6412603 16384) (BSN.cos_reduce1 qz467 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 627934729461391425536) qz291) 226375608064910080 72057594037927936 Bool.false 275583 1048576 62 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q1 6412603 16384 226375608064910080 72057594037927936 62 627934729461391425536 2361183241434822606848 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 275583 1048576 627934729461391425536 2361183241434822606848 571103309 2147483648 398796 398406 (ep901 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep903 := BSN.cos_dyadic_bound_f 571103309 2147483648 2 1 1048576 398796 ep900 ep184 ep900 ep900 ep185 ep900 1011714 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 571103309) qz281 0 1 ep900 ep184 ep900 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 571103309) qz282 0 1 ep900 ep185 ep900 rfl rfl rfl rfl) rfl rfl

noncomputable def ep904 := @Enclosure.Real.IsNear.sin_image qz168 qz467 Bool.false 6412603 16384 381 524288 Bool.false 1011714 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz168 Bool.false 176268289164360601257 450359962737049600 14453000008637242877 19920300000000000000000 6412603 16384 381 524288 (ep899 rfl) rfl) (Enclosure.sfrac_false_div 6412603 16384) (BSN.sin_reduce1 qz467 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 627934729461391425536) qz291) 226375608064910080 72057594037927936 Bool.false 1011714 1048576 62 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q1 6412603 16384 226375608064910080 72057594037927936 62 627934729461391425536 2361183241434822606848 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1011714 1048576 627934729461391425536 2361183241434822606848 571103309 2147483648 398796 398406 (ep903 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep905 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz52 (Real.cos qz168)) (@HMul.hMul Real Real Real qz0 qz52 (@Neg.neg Real Real.instNeg (Real.sin qz168))) Bool.true 74611617003 1099511627776 41435445916753 219026014787862528 Bool.true 136956230037 549755813888 20791042710173 109513007393931264 (@Enclosure.Real.IsNear.mulLit_ft qz52 (Real.cos qz168) 270741 1048576 1 1048576 275583 1048576 76420631 104439742464 74611617003 1099511627776 41435445916753 219026014787862528 qz343 (@Enclosure.Real.IsNear.recentre' (Real.cos qz168) Bool.true 275583 1048576 76420631 104439742464 275583 1048576 76420631 104439742464 (ep902 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz52 (@Neg.neg Real Real.instNeg (Real.sin qz168)) 270741 1048576 1 1048576 505857 524288 76420631 104439742464 136956230037 549755813888 20791042710173 109513007393931264 qz343 (@Enclosure.Real.IsNear.neg (Real.sin qz168) Bool.false 505857 524288 76420631 104439742464 (@Enclosure.Real.IsNear.recentre' (Real.sin qz168) Bool.false 1011714 1048576 76420631 104439742464 505857 524288 76420631 104439742464 (ep904 rfl rfl) rfl)) rfl)

noncomputable def ep906 := @ep811 74611617003 1099511627776 41435445916753 219026014787862528 Bool.true 136956230037 549755813888 20791042710173 109513007393931264 Bool.false ep812 3459757029731 1099511627776 869212701781093 219026014787862528 Bool.true 8732058980270787788800 63534091025 549755813888 217348287604063 54756503696965632 (ep813 (BSN.head_sum_c_succ qz149 14 15 rfl rfl) (ep897 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep898 ep905) rfl rfl

noncomputable abbrev qz169 := (@HMul.hMul Real Real Real qz267 qz452 qz562)

noncomputable def ep907 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz310 qz150) (Complex.mk (@HMul.hMul Real Real Real qz0 qz54 (Real.cos qz169)) (@HMul.hMul Real Real Real qz0 qz54 (@Neg.neg Real Real.instNeg (Real.sin qz169)))) Bool.false 11570729877 274877906944 10025397567649 54756503696965632 Bool.false 67738013343 274877906944 10068079200835 54756503696965632 (BSN.cpow_neg_s_mk qz152 144530 1000 16 qz153 rfl)

noncomputable def ep908 := @Enclosure.Real.IsNear.mulLit_ff qz152 qz562 144530 1000 0 1 3121657384082679 1125899906842624 250000000199203 49800750000000000000 45117314172146959587 112589990684262400 3613250002879080959 4980075000000000000000 qz154 (BSN.isNear_log_sfrac 16 1 3121657384082679 1125899906842624 250000000199203 49800750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz345) Bool.false 52372720210750067441664 18889465931478580854784 1000000000796812 199203000000000000000 3121657384082679 1125899906842624 250000000199203 49800750000000000000 (BSN.log_rat_reduce_isNear 16 1 4 32 32 0 524288 24973259072661432 36028797018963968 199203 1000000000000000 rfl rfl rfl rfl (ep280 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep909 := nat_lit 17424265018910355113911071514034176

noncomputable def ep910 := BSN.sin_dyadic_bound_f 363319424 2147483648 2 1 1048576 398796 ep909 ep180 ep909 ep909 ep181 ep909 176556 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 363319424) qz285 0 1 ep909 ep180 ep909 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 363319424) qz286 0 1 ep909 ep181 ep909 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz468 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 420187731) qz16)

noncomputable def ep911 := @Enclosure.Real.IsNear.cos_image qz169 qz468 Bool.false 420187731 1048576 381 524288 Bool.false 176556 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz169 Bool.false 45117314172146959587 112589990684262400 3613250002879080959 4980075000000000000000 420187731 1048576 381 524288 (ep908 rfl) rfl) (Enclosure.sfrac_false_div 420187731 1048576) (BSN.cos_reduce3 qz468 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 25566331652990966956032) qz19) 226375608064910080 72057594037927936 Bool.false 176556 1048576 63 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q3 420187731 1048576 226375608064910080 72057594037927936 63 25566331652990966956032 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 176556 1048576 25566331652990966956032 151115727451828646838272 363319424 2147483648 398796 398406 (ep910 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep912 := BSN.cos_dyadic_bound_f 363319424 2147483648 2 1 1048576 398796 ep909 ep184 ep909 ep909 ep185 ep909 1033604 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 363319424) qz281 0 1 ep909 ep184 ep909 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 363319424) qz282 0 1 ep909 ep185 ep909 rfl rfl rfl rfl) rfl rfl

noncomputable def ep913 := @Enclosure.Real.IsNear.sin_image qz169 qz468 Bool.false 420187731 1048576 381 524288 Bool.true 1033604 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz169 Bool.false 45117314172146959587 112589990684262400 3613250002879080959 4980075000000000000000 420187731 1048576 381 524288 (ep908 rfl) rfl) (Enclosure.sfrac_false_div 420187731 1048576) (BSN.sin_reduce3 qz468 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 25566331652990966956032) qz19) 226375608064910080 72057594037927936 Bool.false 1033604 1048576 63 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q3 420187731 1048576 226375608064910080 72057594037927936 63 25566331652990966956032 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1033604 1048576 25566331652990966956032 151115727451828646838272 363319424 2147483648 398796 398406 (ep912 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep914 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz54 (Real.cos qz169)) (@HMul.hMul Real Real Real qz0 qz54 (@Neg.neg Real Real.instNeg (Real.sin qz169))) Bool.false 11570729877 274877906944 10025397567649 54756503696965632 Bool.false 67738013343 274877906944 10068079200835 54756503696965632 (@Enclosure.Real.IsNear.mulLit_ff qz54 (Real.cos qz169) 262143 1048576 1 1048576 44139 262144 76420631 104439742464 11570729877 274877906944 10025397567649 54756503696965632 qz347 (@Enclosure.Real.IsNear.recentre' (Real.cos qz169) Bool.false 176556 1048576 76420631 104439742464 44139 262144 76420631 104439742464 (ep911 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz54 (@Neg.neg Real Real.instNeg (Real.sin qz169)) 262143 1048576 1 1048576 258401 262144 76420631 104439742464 67738013343 274877906944 10068079200835 54756503696965632 qz347 (@Enclosure.Real.IsNear.neg (Real.sin qz169) Bool.true 258401 262144 76420631 104439742464 (@Enclosure.Real.IsNear.recentre' (Real.sin qz169) Bool.true 1033604 1048576 76420631 104439742464 258401 262144 76420631 104439742464 (ep913 rfl rfl) rfl)) rfl)

noncomputable def ep915 := @ep809 11570729877 274877906944 10025397567649 54756503696965632 Bool.false 67738013343 274877906944 10068079200835 54756503696965632 Bool.false 963732922908864325615616 3506039949239 1099511627776 909314292051689 219026014787862528 Bool.false 19775248695995593129984 71941935661 549755813888 113708183402449 27378251848482816 (ep810 (BSN.head_sum_c_succ qz149 15 16 rfl rfl) (ep906 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep907 ep914) rfl rfl

theorem EMRow50.d13 : Enclosure.Complex.IsNear qz161 Bool.false 3506039949239 1099511627776 909314292051689 219026014787862528 Bool.false 71941935661 549755813888 113708183402449 27378251848482816 := ep808 (BSN.head_sum_c_succ qz149 16 17 rfl rfl) (ep915 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz170 := (BSN.headSumC qz450 25)

noncomputable def ep916 := @Enclosure.Complex.IsNear.of_eq qz170 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz149 24) (@HPow.hPow Complex Complex Complex qz6 qz348 qz150)) Bool.false 4313657170945 1099511627776 1195143206873119 219026014787862528 Bool.true 217394862351 1099511627776 1195098304126483 219026014787862528

noncomputable def ep917 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz149 24) (@HPow.hPow Complex Complex Complex qz6 qz348 qz150) Bool.false 2067592622807 549755813888 18160358779943 3422281481060352 Bool.true 40654540095 549755813888 581128753669903 109513007393931264 Bool.false

noncomputable def ep918 := nat_lit 2371458108846676021084160

noncomputable def ep919 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz149 24) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz149 23) (@HPow.hPow Complex Complex Complex qz6 qz349 qz150)) Bool.false 2067592622807 549755813888 18160358779943 3422281481060352 Bool.true 40654540095 549755813888 581128753669903 109513007393931264

noncomputable def ep920 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz149 23) (@HPow.hPow Complex Complex Complex qz6 qz349 qz150) Bool.false 3972741586405 1099511627776 1128697136569135 219026014787862528 Bool.false 80474277159 1099511627776 1128692283585649 219026014787862528 Bool.false

noncomputable def ep921 := nat_lit 4546684260560347504574464

noncomputable def ep922 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz149 23) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz149 22) (@HPow.hPow Complex Complex Complex qz6 qz350 qz150)) Bool.false 3972741586405 1099511627776 1128697136569135 219026014787862528 Bool.false 80474277159 1099511627776 1128692283585649 219026014787862528

noncomputable def ep923 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz149 22) (@HPow.hPow Complex Complex Complex qz6 qz350 qz150) Bool.false 3785008701427 1099511627776 364786989400959 73008671595954176 Bool.false 110428559433 549755813888 22799964729425 4563041974747136 Bool.false

noncomputable def ep924 := nat_lit 2184037784200785050992640

noncomputable def ep925 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz149 22) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz149 21) (@HPow.hPow Complex Complex Complex qz6 qz351 qz150)) Bool.false 3785008701427 1099511627776 364786989400959 73008671595954176 Bool.false 110428559433 549755813888 22799964729425 4563041974747136

noncomputable def ep926 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz149 21) (@HPow.hPow Complex Complex Complex qz6 qz351 qz150) Bool.false 3549939622485 1099511627776 1059024122208983 219026014787862528 Bool.false 67230714191 274877906944 529693530754627 109513007393931264 Bool.false

noncomputable def ep927 := nat_lit 2080830539226162372018176

noncomputable def ep928 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz149 21) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz149 20) (@HPow.hPow Complex Complex Complex qz6 qz352 qz150)) Bool.false 3549939622485 1099511627776 1059024122208983 219026014787862528 Bool.false 67230714191 274877906944 529693530754627 109513007393931264

noncomputable def ep929 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz149 20) (@HPow.hPow Complex Complex Complex qz6 qz352 qz150) Bool.false 1671259600397 549755813888 170501868127521 36504335797977088 Bool.false 136926422993 1099511627776 341146075895479 73008671595954176 Bool.false

noncomputable def ep930 := nat_lit 1951599946412500640071680

noncomputable def ep931 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz149 20) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz149 19) (@HPow.hPow Complex Complex Complex qz6 qz353 qz150)) Bool.false 1671259600397 549755813888 170501868127521 36504335797977088 Bool.false 136926422993 1099511627776 341146075895479 73008671595954176

noncomputable def ep932 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz149 19) (@HPow.hPow Complex Complex Complex qz6 qz353 qz150) Bool.false 1687114844087 549755813888 493108727919473 109513007393931264 Bool.true 56658380335 549755813888 493231755692273 109513007393931264 Bool.true

noncomputable def ep933 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz149 19) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz149 18) (@HPow.hPow Complex Complex Complex qz6 qz354 qz150)) Bool.false 1687114844087 549755813888 493108727919473 109513007393931264 Bool.true 56658380335 549755813888 493231755692273 109513007393931264

noncomputable def ep934 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz149 18) (@HPow.hPow Complex Complex Complex qz6 qz354 qz150) Bool.false 3632418204683 1099511627776 948283566466201 219026014787862528 Bool.true 90938967677 1099511627776 948719684781349 219026014787862528 Bool.true

noncomputable def ep935 := nat_lit 3710004776934299637121024

noncomputable def ep936 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz149 18) (@HAdd.hAdd Complex Complex Complex qz4 qz161 (@HPow.hPow Complex Complex Complex qz6 qz355 qz150)) Bool.false 3632418204683 1099511627776 948283566466201 219026014787862528 Bool.true 90938967677 1099511627776 948719684781349 219026014787862528

noncomputable def ep937 := @Enclosure.Complex.IsNear.addLitP qz161 (@HPow.hPow Complex Complex Complex qz6 qz355 qz150) Bool.false 3506039949239 1099511627776 909314292051689 219026014787862528 Bool.false 71941935661 549755813888 113708183402449 27378251848482816 Bool.false

noncomputable abbrev qz171 := (@HMul.hMul Real Real Real qz267 qz452 qz563)

noncomputable def ep938 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz355 qz150) (Complex.mk (@HMul.hMul Real Real Real qz0 qz57 (Real.cos qz171)) (@HMul.hMul Real Real Real qz0 qz57 (@Neg.neg Real Real.instNeg (Real.sin qz171)))) Bool.false 31594563861 274877906944 2435579650907 13689125924241408 Bool.true 234822838999 1099511627776 39054217561757 219026014787862528 (BSN.cpow_neg_s_mk qz152 144530 1000 17 qz153 rfl)

noncomputable def ep939 := @Enclosure.Real.IsNear.mulLit_ff qz152 qz563 144530 1000 0 1 3189913004350711 1125899906842624 250000000199203 49800750000000000000 46103812651880826083 112589990684262400 3613250002879080959 4980075000000000000000 qz154 (BSN.isNear_log_sfrac 17 1 3189913004350711 1125899906842624 250000000199203 49800750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz357) Bool.false 53517859495200818200576 18889465931478580854784 1000000000796812 199203000000000000000 3189913004350711 1125899906842624 250000000199203 49800750000000000000 (BSN.log_rat_reduce_isNear 17 1 4 34 32 31784 524288 24973259072661432 36028797018963968 199203 1000000000000000 rfl rfl rfl rfl (ep311 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep940 := nat_lit 1023457060987369766432946589594702923596300048345969454528433908725056942530816

noncomputable def ep941 := nat_lit 819193038144323593032706376836280365176844936384286916445033699811112673536

noncomputable def ep942 := nat_lit 3068732796885820652112774356030436210058546455165139789752411658775548602245376

noncomputable def ep943 := BSN.cos_dyadic_bound_f 2312987478 2147483648 3 2 1048576 398796 ep940 ep57 ep941 ep942 ep60 ep941 496932 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2312987478) qz281 0 2 ep940 ep57 ep941 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2312987478) qz282 0 2 ep942 ep60 ep941 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz469 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 214687607) qz37)

noncomputable def ep944 := @Enclosure.Real.IsNear.cos_image qz171 qz469 Bool.false 214687607 524288 381 524288 Bool.false 496932 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz171 Bool.false 46103812651880826083 112589990684262400 3613250002879080959 4980075000000000000000 214687607 524288 381 524288 (ep939 rfl) rfl) (Enclosure.sfrac_false_div 214687607 524288) (BSN.cos_reduce0 qz469 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 81381012065181870587904) qz38) 226375608064910080 72057594037927936 Bool.false 496932 1048576 65 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q0 214687607 524288 226375608064910080 72057594037927936 65 81381012065181870587904 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 496932 1048576 81381012065181870587904 75557863725914323419136 2312987478 2147483648 398796 398406 (ep943 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep945 := nat_lit 1841567355346750120704877696168996238181198611073637588618025008745253606416640

noncomputable def ep946 := nat_lit 4821826284798778554124055298689636169883329089581571505658678301675970024857856

noncomputable def ep947 := BSN.sin_dyadic_bound_f 2312987478 2147483648 3 2 1048576 398796 ep945 ep64 ep941 ep946 ep66 ep941 923347 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2312987478) qz285 0 2 ep945 ep64 ep941 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2312987478) qz286 0 2 ep946 ep66 ep941 rfl rfl rfl rfl) rfl rfl

noncomputable def ep948 := @Enclosure.Real.IsNear.sin_image qz171 qz469 Bool.false 214687607 524288 381 524288 Bool.false 923347 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz171 Bool.false 46103812651880826083 112589990684262400 3613250002879080959 4980075000000000000000 214687607 524288 381 524288 (ep939 rfl) rfl) (Enclosure.sfrac_false_div 214687607 524288) (BSN.sin_reduce0 qz469 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 81381012065181870587904) qz38) 226375608064910080 72057594037927936 Bool.false 923347 1048576 65 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q0 214687607 524288 226375608064910080 72057594037927936 65 81381012065181870587904 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 923347 1048576 81381012065181870587904 75557863725914323419136 2312987478 2147483648 398796 398406 (ep947 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep949 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz57 (Real.cos qz171)) (@HMul.hMul Real Real Real qz0 qz57 (@Neg.neg Real Real.instNeg (Real.sin qz171))) Bool.false 31594563861 274877906944 2435579650907 13689125924241408 Bool.true 234822838999 1099511627776 39054217561757 219026014787862528 (@Enclosure.Real.IsNear.mulLit_ff qz57 (Real.cos qz171) 254317 1048576 1 1048576 124233 262144 76420631 104439742464 31594563861 274877906944 2435579650907 13689125924241408 qz359 (@Enclosure.Real.IsNear.recentre' (Real.cos qz171) Bool.false 496932 1048576 76420631 104439742464 124233 262144 76420631 104439742464 (ep944 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz57 (@Neg.neg Real Real.instNeg (Real.sin qz171)) 254317 1048576 1 1048576 923347 1048576 76420631 104439742464 234822838999 1099511627776 39054217561757 219026014787862528 qz359 (@Enclosure.Real.IsNear.neg (Real.sin qz171) Bool.false 923347 1048576 76420631 104439742464 (@Enclosure.Real.IsNear.recentre' (Real.sin qz171) Bool.false 923347 1048576 76420631 104439742464 923347 1048576 76420631 104439742464 (ep948 rfl rfl) rfl)) rfl)

noncomputable def ep950 := @ep937 31594563861 274877906944 2435579650907 13689125924241408 Bool.true 234822838999 1099511627776 39054217561757 219026014787862528 Bool.false 998471513248545219018752 3632418204683 1099511627776 948283566466201 219026014787862528 Bool.true 49994226189403659698176 90938967677 1099511627776 948719684781349 219026014787862528 EMRow50.d13 (ep938 ep949) rfl rfl

noncomputable abbrev qz172 := (@HMul.hMul Real Real Real qz267 qz452 qz564)

noncomputable def ep951 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz354 qz150) (Complex.mk (@HMul.hMul Real Real Real qz0 qz59 (Real.cos qz172)) (@HMul.hMul Real Real Real qz0 qz59 (@Neg.neg Real Real.instNeg (Real.sin qz172)))) Bool.true 258188516509 1099511627776 12644629790915 73008671595954176 Bool.true 22377792993 1099511627776 12581275534399 73008671595954176 (BSN.cpow_neg_s_mk qz152 144530 1000 18 qz153 rfl)

noncomputable def ep952 := @Enclosure.Real.IsNear.mulLit_ff qz152 qz564 144530 1000 0 1 3254268794313975 1125899906842624 250000000199203 49800750000000000000 1881357875368795227 4503599627370496 3613250002879080959 4980075000000000000000 qz154 (BSN.isNear_log_sfrac 18 1 3254268794313975 1125899906842624 250000000199203 49800750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz361) Bool.false 54597570484265130393600 18889465931478580854784 1000000000796812 199203000000000000000 3254268794313975 1125899906842624 250000000199203 49800750000000000000 (BSN.log_rat_reduce_isNear 18 1 4 36 32 61752 524288 24973259072661432 36028797018963968 199203 1000000000000000 rfl rfl rfl rfl (ep322 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep953 := nat_lit 6650438643660222586536180107238859646490709384616819122122733742619147651030625

noncomputable def ep954 := nat_lit 10658715541863907528013951444390772316799475020605640170331486805983250390625

noncomputable def ep955 := nat_lit 17400558527280422352549401502334666395153230190629736188140908823459509061590625

noncomputable def ep956 := BSN.sin_dyadic_bound_f 3187594795 2147483648 3 2 1048576 398796 ep953 ep64 ep954 ep955 ep66 ep954 1044659 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3187594795) qz285 0 2 ep953 ep64 ep954 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3187594795) qz286 0 2 ep955 ep66 ep954 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz470 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 438037765) qz16)

noncomputable def ep957 := @Enclosure.Real.IsNear.cos_image qz172 qz470 Bool.false 438037765 1048576 761 1048576 Bool.true 1044659 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz172 Bool.false 1881357875368795227 4503599627370496 3613250002879080959 4980075000000000000000 438037765 1048576 761 1048576 (ep952 rfl) rfl) (Enclosure.sfrac_false_div 438037765 1048576) (BSN.cos_reduce1 qz470 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 224307042700701340794880) qz19) 226375608064910080 72057594037927936 Bool.false 1044659 1048576 66 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q1 438037765 1048576 226375608064910080 72057594037927936 66 224307042700701340794880 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1044659 1048576 224307042700701340794880 151115727451828646838272 3187594795 2147483648 398796 398406 (ep956 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep958 := nat_lit 3699425342274285395865884037996873480191193869240724241254999406702185695190625

noncomputable def ep959 := nat_lit 11076958595739128372541624211101838895939982657680961443424335246494590584790625

noncomputable def ep960 := BSN.cos_dyadic_bound_f 3187594795 2147483648 3 2 1048576 398796 ep958 ep57 ep954 ep959 ep60 ep954 90543 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3187594795) qz281 0 2 ep958 ep57 ep954 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3187594795) qz282 0 2 ep959 ep60 ep954 rfl rfl rfl rfl) rfl rfl

noncomputable def ep961 := @Enclosure.Real.IsNear.sin_image qz172 qz470 Bool.false 438037765 1048576 761 1048576 Bool.false 90543 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz172 Bool.false 1881357875368795227 4503599627370496 3613250002879080959 4980075000000000000000 438037765 1048576 761 1048576 (ep952 rfl) rfl) (Enclosure.sfrac_false_div 438037765 1048576) (BSN.sin_reduce1 qz470 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 224307042700701340794880) qz19) 226375608064910080 72057594037927936 Bool.false 90543 1048576 66 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q1 438037765 1048576 226375608064910080 72057594037927936 66 224307042700701340794880 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 90543 1048576 224307042700701340794880 151115727451828646838272 3187594795 2147483648 398796 398406 (ep960 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep962 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz59 (Real.cos qz172)) (@HMul.hMul Real Real Real qz0 qz59 (@Neg.neg Real Real.instNeg (Real.sin qz172))) Bool.true 258188516509 1099511627776 12644629790915 73008671595954176 Bool.true 22377792993 1099511627776 12581275534399 73008671595954176 (@Enclosure.Real.IsNear.mulLit_ft qz59 (Real.cos qz172) 247151 1048576 1 1048576 1044659 1048576 152642059 208879484928 258188516509 1099511627776 12644629790915 73008671595954176 qz363 (@Enclosure.Real.IsNear.recentre' (Real.cos qz172) Bool.true 1044659 1048576 152642059 208879484928 1044659 1048576 152642059 208879484928 (ep957 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz59 (@Neg.neg Real Real.instNeg (Real.sin qz172)) 247151 1048576 1 1048576 90543 1048576 152642059 208879484928 22377792993 1099511627776 12581275534399 73008671595954176 qz363 (@Enclosure.Real.IsNear.neg (Real.sin qz172) Bool.false 90543 1048576 152642059 208879484928 (@Enclosure.Real.IsNear.recentre' (Real.sin qz172) Bool.false 90543 1048576 152642059 208879484928 90543 1048576 152642059 208879484928 (ep961 rfl rfl) rfl)) rfl)

noncomputable def ep963 := @ep934 258188516509 1099511627776 12644629790915 73008671595954176 Bool.true 22377792993 1099511627776 12581275534399 73008671595954176 Bool.false ep935 1687114844087 549755813888 493108727919473 109513007393931264 Bool.true 124593095978575116369920 56658380335 549755813888 493231755692273 109513007393931264 (ep936 (BSN.head_sum_c_succ qz149 17 18 rfl rfl) (ep950 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep951 ep962) rfl rfl

noncomputable abbrev qz173 := (@HMul.hMul Real Real Real qz267 qz452 qz565)

noncomputable def ep964 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz353 qz150) (Complex.mk (@HMul.hMul Real Real Real qz0 qz61 (Real.cos qz173)) (@HMul.hMul Real Real Real qz0 qz61 (@Neg.neg Real Real.instNeg (Real.sin qz173)))) Bool.true 7927621845 274877906944 9198438231545 54756503696965632 Bool.false 250243183663 1099511627776 36974716301891 219026014787862528 (BSN.cpow_neg_s_mk qz152 144530 1000 19 qz153 rfl)

noncomputable def ep965 := @Enclosure.Real.IsNear.mulLit_ff qz152 qz565 144530 1000 0 1 3315143513283831 1125899906842624 250000000199203 49800750000000000000 47913769197491209443 112589990684262400 3613250002879080959 4980075000000000000000 qz154 (BSN.isNear_log_sfrac 19 1 3315143513283831 1125899906842624 250000000199203 49800750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz365) Bool.false 55618878793361701994496 18889465931478580854784 1000000000796812 199203000000000000000 3315143513283831 1125899906842624 250000000199203 49800750000000000000 (BSN.log_rat_reduce_isNear 19 1 4 38 32 90099 524288 24973259072661432 36028797018963968 199203 1000000000000000 rfl rfl rfl rfl (ep333 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep966 := nat_lit 3319270386931495579538105560126194985802097683521483327382063930040168203943936

noncomputable def ep967 := nat_lit 8585748040176877100939863460881514377413526183539407010507570842392231673856

noncomputable def ep968 := nat_lit 9940639664714132984412436953456821928651465998197371168125176648435720148484096

noncomputable def ep969 := BSN.cos_dyadic_bound_f 3102574848 2147483648 3 2 1048576 398796 ep966 ep57 ep967 ep968 ep60 ep967 131820 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3102574848) qz281 0 2 ep966 ep57 ep967 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3102574848) qz282 0 2 ep968 ep60 ep967 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz471 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 111557937) qz32)

noncomputable def ep970 := @Enclosure.Real.IsNear.cos_image qz173 qz471 Bool.false 111557937 262144 381 524288 Bool.true 131820 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz173 Bool.false 47913769197491209443 112589990684262400 3613250002879080959 4980075000000000000000 111557937 262144 381 524288 (ep965 rfl) rfl) (Enclosure.sfrac_false_div 111557937 262144) (BSN.cos_reduce2 qz471 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 54581073956177826545664) qz302) 226375608064910080 72057594037927936 Bool.false 131820 1048576 67 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q2 111557937 262144 226375608064910080 72057594037927936 67 54581073956177826545664 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 131820 1048576 54581073956177826545664 37778931862957161709568 3102574848 2147483648 398796 398406 (ep969 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep971 := nat_lit 5967818098044550541487838117458445762941845009391838463679309017398388981760000

noncomputable def ep972 := nat_lit 15616099045670679331447578147740216451093781696490989317333558978489050386661376

noncomputable def ep973 := BSN.sin_dyadic_bound_f 3102574848 2147483648 3 2 1048576 398796 ep971 ep64 ep967 ep972 ep66 ep967 1040257 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3102574848) qz285 0 2 ep971 ep64 ep967 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3102574848) qz286 0 2 ep972 ep66 ep967 rfl rfl rfl rfl) rfl rfl

noncomputable def ep974 := @Enclosure.Real.IsNear.sin_image qz173 qz471 Bool.false 111557937 262144 381 524288 Bool.true 1040257 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz173 Bool.false 47913769197491209443 112589990684262400 3613250002879080959 4980075000000000000000 111557937 262144 381 524288 (ep965 rfl) rfl) (Enclosure.sfrac_false_div 111557937 262144) (BSN.sin_reduce2 qz471 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 54581073956177826545664) qz302) 226375608064910080 72057594037927936 Bool.false 1040257 1048576 67 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q2 111557937 262144 226375608064910080 72057594037927936 67 54581073956177826545664 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1040257 1048576 54581073956177826545664 37778931862957161709568 3102574848 2147483648 398796 398406 (ep973 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep975 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz61 (Real.cos qz173)) (@HMul.hMul Real Real Real qz0 qz61 (@Neg.neg Real Real.instNeg (Real.sin qz173))) Bool.true 7927621845 274877906944 9198438231545 54756503696965632 Bool.false 250243183663 1099511627776 36974716301891 219026014787862528 (@Enclosure.Real.IsNear.mulLit_ft qz61 (Real.cos qz173) 240559 1048576 1 1048576 32955 262144 76420631 104439742464 7927621845 274877906944 9198438231545 54756503696965632 qz367 (@Enclosure.Real.IsNear.recentre' (Real.cos qz173) Bool.true 131820 1048576 76420631 104439742464 32955 262144 76420631 104439742464 (ep970 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz61 (@Neg.neg Real Real.instNeg (Real.sin qz173)) 240559 1048576 1 1048576 1040257 1048576 76420631 104439742464 250243183663 1099511627776 36974716301891 219026014787862528 qz367 (@Enclosure.Real.IsNear.neg (Real.sin qz173) Bool.true 1040257 1048576 76420631 104439742464 (@Enclosure.Real.IsNear.recentre' (Real.sin qz173) Bool.true 1040257 1048576 76420631 104439742464 1040257 1048576 76420631 104439742464 (ep974 rfl rfl) rfl)) rfl)

noncomputable def ep976 := @ep932 7927621845 274877906944 9198438231545 54756503696965632 Bool.false 250243183663 1099511627776 36974716301891 219026014787862528 Bool.false 459392340917193191456768 1671259600397 549755813888 170501868127521 36504335797977088 Bool.false 75276097115289271926784 136926422993 1099511627776 341146075895479 73008671595954176 (ep933 (BSN.head_sum_c_succ qz149 18 19 rfl rfl) (ep963 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep964 ep975) rfl rfl

noncomputable abbrev qz174 := (@HMul.hMul Real Real Real qz267 qz452 qz566)

noncomputable def ep977 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz352 qz150) (Complex.mk (@HMul.hMul Real Real Real qz0 qz63 (Real.cos qz174)) (@HMul.hMul Real Real Real qz0 qz63 (@Neg.neg Real Real.instNeg (Real.sin qz174)))) Bool.false 207420421691 1099511627776 36012913443857 219026014787862528 Bool.false 131996433771 1099511627776 35948833822817 219026014787862528 (BSN.cpow_neg_s_mk qz152 144530 1000 20 qz153 rfl)

noncomputable def ep978 := @Enclosure.Real.IsNear.mulLit_ff qz152 qz566 144530 1000 0 1 3372893643545847 1125899906842624 250000000199203 49800750000000000000 48748431830168126691 112589990684262400 3613250002879080959 4980075000000000000000 qz154 (BSN.isNear_log_sfrac 20 1 3372893643545847 1125899906842624 250000000199203 49800750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz369) Bool.false 56587765202795681021952 18889465931478580854784 1000000000796812 199203000000000000000 3372893643545847 1125899906842624 250000000199203 49800750000000000000 (BSN.log_rat_reduce_isNear 20 1 4 40 32 116991 524288 24973259072661432 36028797018963968 199203 1000000000000000 rfl rfl rfl rfl (ep344 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep979 := nat_lit 1390616551671224802839765178025666929981176829269616275094300282763788267577600

noncomputable def ep980 := nat_lit 467218911024753391201017679481960184852258450854566378579163157687814349056

noncomputable def ep981 := nat_lit 3641334518997262978137440485252823547746654705833325708253086857364141382328576

noncomputable def ep982 := BSN.sin_dyadic_bound_f 2156205014 2147483648 3 2 1048576 398796 ep979 ep64 ep980 ep981 ep66 ep980 884639 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2156205014) qz285 0 2 ep979 ep64 ep980 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2156205014) qz286 0 2 ep981 ep66 ep980 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz472 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 227002575) qz37)

noncomputable def ep983 := @Enclosure.Real.IsNear.cos_image qz174 qz472 Bool.false 227002575 524288 381 524288 Bool.false 884639 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz174 Bool.false 48748431830168126691 112589990684262400 3613250002879080959 4980075000000000000000 227002575 524288 381 524288 (ep978 rfl) rfl) (Enclosure.sfrac_false_div 227002575 524288) (BSN.cos_reduce3 qz472 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 75864719516294866534400) qz38) 226375608064910080 72057594037927936 Bool.false 884639 1048576 68 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q3 227002575 524288 226375608064910080 72057594037927936 68 75864719516294866534400 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 884639 1048576 75864719516294866534400 75557863725914323419136 2156205014 2147483648 398796 398406 (ep982 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep984 := nat_lit 772772403777802558640403328982918054516143686683499960109535340716632510587136

noncomputable def ep985 := nat_lit 2317382773511358169138807951589790243178726543148790747571447695834521903063296

noncomputable def ep986 := BSN.cos_dyadic_bound_f 2156205014 2147483648 3 2 1048576 398796 ep984 ep57 ep980 ep985 ep60 ep980 562959 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2156205014) qz281 0 2 ep984 ep57 ep980 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2156205014) qz282 0 2 ep985 ep60 ep980 rfl rfl rfl rfl) rfl rfl

noncomputable def ep987 := @Enclosure.Real.IsNear.sin_image qz174 qz472 Bool.false 227002575 524288 381 524288 Bool.true 562959 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz174 Bool.false 48748431830168126691 112589990684262400 3613250002879080959 4980075000000000000000 227002575 524288 381 524288 (ep978 rfl) rfl) (Enclosure.sfrac_false_div 227002575 524288) (BSN.sin_reduce3 qz472 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 75864719516294866534400) qz38) 226375608064910080 72057594037927936 Bool.false 562959 1048576 68 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q3 227002575 524288 226375608064910080 72057594037927936 68 75864719516294866534400 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 562959 1048576 75864719516294866534400 75557863725914323419136 2156205014 2147483648 398796 398406 (ep986 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep988 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz63 (Real.cos qz174)) (@HMul.hMul Real Real Real qz0 qz63 (@Neg.neg Real Real.instNeg (Real.sin qz174))) Bool.false 207420421691 1099511627776 36012913443857 219026014787862528 Bool.false 131996433771 1099511627776 35948833822817 219026014787862528 (@Enclosure.Real.IsNear.mulLit_ff qz63 (Real.cos qz174) 234469 1048576 1 1048576 884639 1048576 76420631 104439742464 207420421691 1099511627776 36012913443857 219026014787862528 qz371 (@Enclosure.Real.IsNear.recentre' (Real.cos qz174) Bool.false 884639 1048576 76420631 104439742464 884639 1048576 76420631 104439742464 (ep983 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz63 (@Neg.neg Real Real.instNeg (Real.sin qz174)) 234469 1048576 1 1048576 562959 1048576 76420631 104439742464 131996433771 1099511627776 35948833822817 219026014787862528 qz371 (@Enclosure.Real.IsNear.neg (Real.sin qz174) Bool.true 562959 1048576 76420631 104439742464 (@Enclosure.Real.IsNear.recentre' (Real.sin qz174) Bool.true 562959 1048576 76420631 104439742464 562959 1048576 76420631 104439742464 (ep987 rfl rfl) rfl)) rfl)

noncomputable def ep989 := @ep929 207420421691 1099511627776 36012913443857 219026014787862528 Bool.false 131996433771 1099511627776 35948833822817 219026014787862528 Bool.false ep930 3549939622485 1099511627776 1059024122208983 219026014787862528 Bool.false 295683807986757731876864 67230714191 274877906944 529693530754627 109513007393931264 (ep931 (BSN.head_sum_c_succ qz149 19 20 rfl rfl) (ep976 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep977 ep988) rfl rfl

noncomputable abbrev qz175 := (@HMul.hMul Real Real Real qz267 qz452 qz567)

noncomputable def ep990 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz351 qz150) (Complex.mk (@HMul.hMul Real Real Real qz0 qz65 (Real.cos qz175)) (@HMul.hMul Real Real Real qz0 qz65 (@Neg.neg Real Real.instNeg (Real.sin qz175)))) Bool.false 117534539471 549755813888 17668422996947 109513007393931264 Bool.true 24032868949 549755813888 17505622751573 109513007393931264 (BSN.cpow_neg_s_mk qz152 144530 1000 21 qz153 rfl)

noncomputable def ep991 := @Enclosure.Real.IsNear.mulLit_ff qz152 qz567 144530 1000 0 1 3427826275261687 1125899906842624 250000000199203 49800750000000000000 49542373156357162211 112589990684262400 3613250002879080959 4980075000000000000000 qz154 (BSN.isNear_log_sfrac 21 1 3427826275261687 1125899906842624 250000000199203 49800750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz373) Bool.false 57509381830540779323392 18889465931478580854784 1000000000796812 199203000000000000000 3427826275261687 1125899906842624 250000000199203 49800750000000000000 (BSN.log_rat_reduce_isNear 21 1 4 42 32 142571 524288 24973259072661432 36028797018963968 199203 1000000000000000 rfl rfl rfl rfl (ep359 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep992 := nat_lit 35196739367020235600627165984856241

noncomputable def ep993 := BSN.cos_dyadic_bound_f 433137323 2147483648 2 1 1048576 398796 ep992 ep184 ep992 ep992 ep185 ep992 1027319 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 433137323) qz281 0 1 ep992 ep184 ep992 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 433137323) qz282 0 1 ep992 ep185 ep992 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz473 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 461399305) qz16)

noncomputable def ep994 := @Enclosure.Real.IsNear.cos_image qz175 qz473 Bool.false 461399305 1048576 761 1048576 Bool.false 1027319 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz175 Bool.false 49542373156357162211 112589990684262400 3613250002879080959 4980075000000000000000 461399305 1048576 761 1048576 (ep991 rfl) rfl) (Enclosure.sfrac_false_div 461399305 1048576) (BSN.cos_reduce0 qz473 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 30479329508264048066560) qz19) 226375608064910080 72057594037927936 Bool.false 1027319 1048576 70 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q0 461399305 1048576 226375608064910080 72057594037927936 70 30479329508264048066560 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1027319 1048576 30479329508264048066560 151115727451828646838272 433137323 2147483648 398796 398406 (ep993 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep995 := BSN.sin_dyadic_bound_f 433137323 2147483648 2 1 1048576 398796 ep992 ep180 ep992 ep992 ep181 ep992 210061 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 433137323) qz285 0 1 ep992 ep180 ep992 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 433137323) qz286 0 1 ep992 ep181 ep992 rfl rfl rfl rfl) rfl rfl

noncomputable def ep996 := @Enclosure.Real.IsNear.sin_image qz175 qz473 Bool.false 461399305 1048576 761 1048576 Bool.false 210061 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz175 Bool.false 49542373156357162211 112589990684262400 3613250002879080959 4980075000000000000000 461399305 1048576 761 1048576 (ep991 rfl) rfl) (Enclosure.sfrac_false_div 461399305 1048576) (BSN.sin_reduce0 qz473 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 30479329508264048066560) qz19) 226375608064910080 72057594037927936 Bool.false 210061 1048576 70 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q0 461399305 1048576 226375608064910080 72057594037927936 70 30479329508264048066560 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 210061 1048576 30479329508264048066560 151115727451828646838272 433137323 2147483648 398796 398406 (ep995 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep997 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz65 (Real.cos qz175)) (@HMul.hMul Real Real Real qz0 qz65 (@Neg.neg Real Real.instNeg (Real.sin qz175))) Bool.false 117534539471 549755813888 17668422996947 109513007393931264 Bool.true 24032868949 549755813888 17505622751573 109513007393931264 (@Enclosure.Real.IsNear.mulLit_ff qz65 (Real.cos qz175) 114409 524288 1 524288 1027319 1048576 152642059 208879484928 117534539471 549755813888 17668422996947 109513007393931264 qz375 (@Enclosure.Real.IsNear.recentre' (Real.cos qz175) Bool.false 1027319 1048576 152642059 208879484928 1027319 1048576 152642059 208879484928 (ep994 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz65 (@Neg.neg Real Real.instNeg (Real.sin qz175)) 114409 524288 1 524288 210061 1048576 152642059 208879484928 24032868949 549755813888 17505622751573 109513007393931264 qz375 (@Enclosure.Real.IsNear.neg (Real.sin qz175) Bool.false 210061 1048576 152642059 208879484928 (@Enclosure.Real.IsNear.recentre' (Real.sin qz175) Bool.false 210061 1048576 152642059 208879484928 210061 1048576 152642059 208879484928 (ep996 rfl rfl) rfl)) rfl)

noncomputable def ep998 := @ep926 117534539471 549755813888 17668422996947 109513007393931264 Bool.true 24032868949 549755813888 17505622751573 109513007393931264 Bool.false ep927 3785008701427 1099511627776 364786989400959 73008671595954176 Bool.false 30354371283784147402752 110428559433 549755813888 22799964729425 4563041974747136 (ep928 (BSN.head_sum_c_succ qz149 20 21 rfl rfl) (ep989 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep990 ep997) rfl rfl

noncomputable abbrev qz176 := (@HMul.hMul Real Real Real qz267 qz452 qz568)

noncomputable def ep999 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz350 qz150) (Complex.mk (@HMul.hMul Real Real Real qz0 qz67 (Real.cos qz176)) (@HMul.hMul Real Real Real qz0 qz67 (@Neg.neg Real Real.instNeg (Real.sin qz176)))) Bool.false 93866442489 549755813888 17168084183129 109513007393931264 Bool.true 140382841707 1099511627776 34293976573249 219026014787862528 (BSN.cpow_neg_s_mk qz152 144530 1000 22 qz153 rfl)

noncomputable def ep1000 := @Enclosure.Real.IsNear.mulLit_ff qz152 qz568 144530 1000 0 1 3480203401436407 1125899906842624 250000000199203 49800750000000000000 50299379760960390371 112589990684262400 3613250002879080959 4980075000000000000000 qz154 (BSN.isNear_log_sfrac 22 1 3480203401436407 1125899906842624 250000000199203 49800750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz377) Bool.false 58388124189833310502912 18889465931478580854784 1000000000796812 199203000000000000000 3480203401436407 1125899906842624 250000000199203 49800750000000000000 (BSN.log_rat_reduce_isNear 22 1 4 44 32 166961 524288 24973259072661432 36028797018963968 199203 1000000000000000 rfl rfl rfl rfl (ep370 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1001 := nat_lit 129165257381538430906429867138039284782913040191880012551569041027529662300416

noncomputable def ep1002 := nat_lit 13066102778970217181929346902013911103980618551473750054759295200715899136

noncomputable def ep1003 := nat_lit 387469639939057352284925742720313826526531159338537090154597604492187555102976

noncomputable def ep1004 := BSN.cos_dyadic_bound_f 1378853922 2147483648 3 2 1048576 398796 ep1001 ep57 ep1002 ep1003 ep60 ep1002 839754 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1378853922) qz281 0 2 ep1001 ep57 ep1002 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1378853922) qz282 0 2 ep1003 ep60 ep1002 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz474 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 234224739) qz37)

noncomputable def ep1005 := @Enclosure.Real.IsNear.cos_image qz176 qz474 Bool.false 234224739 524288 381 524288 Bool.false 839754 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz176 Bool.false 50299379760960390371 112589990684262400 3613250002879080959 4980075000000000000000 234224739 524288 381 524288 (ep1000 rfl) rfl) (Enclosure.sfrac_false_div 234224739 524288) (BSN.cos_reduce0 qz474 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 48514109480750230274048) qz38) 226375608064910080 72057594037927936 Bool.false 839754 1048576 71 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q0 234224739 524288 226375608064910080 72057594037927936 71 48514109480750230274048 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 839754 1048576 48514109480750230274048 75557863725914323419136 1378853922 2147483648 398796 398406 (ep1004 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1006 := nat_lit 3614706458202410822965970527607383056

noncomputable def ep1007 := BSN.sin_dyadic_bound_f 1378853922 2147483648 2 1 1048576 398796 ep1006 ep180 ep1006 ep1006 ep181 ep1006 627951 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1378853922) qz285 0 1 ep1006 ep180 ep1006 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1378853922) qz286 0 1 ep1006 ep181 ep1006 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1008 := @Enclosure.Real.IsNear.sin_image qz176 qz474 Bool.false 234224739 524288 381 524288 Bool.false 627951 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz176 Bool.false 50299379760960390371 112589990684262400 3613250002879080959 4980075000000000000000 234224739 524288 381 524288 (ep1000 rfl) rfl) (Enclosure.sfrac_false_div 234224739 524288) (BSN.sin_reduce0 qz474 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 48514109480750230274048) qz38) 226375608064910080 72057594037927936 Bool.false 627951 1048576 71 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q0 234224739 524288 226375608064910080 72057594037927936 71 48514109480750230274048 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 627951 1048576 48514109480750230274048 75557863725914323419136 1378853922 2147483648 398796 398406 (ep1007 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1009 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz67 (Real.cos qz176)) (@HMul.hMul Real Real Real qz0 qz67 (@Neg.neg Real Real.instNeg (Real.sin qz176))) Bool.false 93866442489 549755813888 17168084183129 109513007393931264 Bool.true 140382841707 1099511627776 34293976573249 219026014787862528 (@Enclosure.Real.IsNear.mulLit_ff qz67 (Real.cos qz176) 223557 1048576 1 1048576 419877 524288 76420631 104439742464 93866442489 549755813888 17168084183129 109513007393931264 qz379 (@Enclosure.Real.IsNear.recentre' (Real.cos qz176) Bool.false 839754 1048576 76420631 104439742464 419877 524288 76420631 104439742464 (ep1005 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz67 (@Neg.neg Real Real.instNeg (Real.sin qz176)) 223557 1048576 1 1048576 627951 1048576 76420631 104439742464 140382841707 1099511627776 34293976573249 219026014787862528 qz379 (@Enclosure.Real.IsNear.neg (Real.sin qz176) Bool.false 627951 1048576 76420631 104439742464 (@Enclosure.Real.IsNear.recentre' (Real.sin qz176) Bool.false 627951 1048576 76420631 104439742464 627951 1048576 76420631 104439742464 (ep1008 rfl rfl) rfl)) rfl)

noncomputable def ep1010 := @ep923 93866442489 549755813888 17168084183129 109513007393931264 Bool.true 140382841707 1099511627776 34293976573249 219026014787862528 Bool.false ep924 3972741586405 1099511627776 1128697136569135 219026014787862528 Bool.false 44241201736594533384192 80474277159 1099511627776 1128692283585649 219026014787862528 (ep925 (BSN.head_sum_c_succ qz149 21 22 rfl rfl) (ep998 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep999 ep1009) rfl rfl

noncomputable abbrev qz177 := (@HMul.hMul Real Real Real qz267 qz452 qz569)

noncomputable def ep1011 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz349 qz150) (Complex.mk (@HMul.hMul Real Real Real qz0 qz69 (Real.cos qz177)) (@HMul.hMul Real Real Real qz0 qz69 (@Neg.neg Real Real.instNeg (Real.sin qz177)))) Bool.false 162443659209 1099511627776 33565825347217 219026014787862528 Bool.true 161783357349 1099511627776 33565223754157 219026014787862528 (BSN.cpow_neg_s_mk qz152 144530 1000 23 qz153 rfl)

noncomputable def ep1012 := @Enclosure.Real.IsNear.mulLit_ff qz152 qz569 144530 1000 0 1 3530250507853047 1125899906842624 250000000199203 49800750000000000000 51022710590000088291 112589990684262400 3613250002879080959 4980075000000000000000 qz154 (BSN.isNear_log_sfrac 23 1 3530250507853047 1125899906842624 250000000199203 49800750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz381) Bool.false 59227775304360265777152 18889465931478580854784 1000000000796812 199203000000000000000 3530250507853047 1125899906842624 250000000199203 49800750000000000000 (BSN.log_rat_reduce_isNear 23 1 4 46 32 190266 524288 24973259072661432 36028797018963968 199203 1000000000000000 rfl rfl rfl rfl (ep384 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1013 := nat_lit 286216532210809588940211401128086374424056110485629702550279221528266177126656

noncomputable def ep1014 := nat_lit 64141227949288329561369055935026688388187144315588190632870142625474027776

noncomputable def ep1015 := nat_lit 858521314176530190161511465272389069895391957168257931269571924299547583324416

noncomputable def ep1016 := BSN.cos_dyadic_bound_f 1682256282 2147483648 3 2 1048576 398796 ep1013 ep57 ep1014 ep1015 ep60 ep1014 742963 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1682256282) qz281 0 2 ep1013 ep57 ep1014 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1682256282) qz282 0 2 ep1015 ep60 ep1014 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz475 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 475186021) qz16)

noncomputable def ep1017 := @Enclosure.Real.IsNear.cos_image qz177 qz475 Bool.false 475186021 1048576 381 524288 Bool.false 742963 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz177 Bool.false 51022710590000088291 112589990684262400 3613250002879080959 4980075000000000000000 475186021 1048576 381 524288 (ep1012 rfl) rfl) (Enclosure.sfrac_false_div 475186021 1048576) (BSN.cos_reduce0 qz475 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 118378261978506195894272) qz19) 226375608064910080 72057594037927936 Bool.false 742963 1048576 72 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q0 475186021 1048576 226375608064910080 72057594037927936 72 118378261978506195894272 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 742963 1048576 118378261978506195894272 151115727451828646838272 1682256282 2147483648 398796 398406 (ep1016 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1018 := nat_lit 8008821882729589683040771790598498576

noncomputable def ep1019 := BSN.sin_dyadic_bound_f 1682256282 2147483648 2 1 1048576 398796 ep1018 ep180 ep1018 ep1018 ep181 ep1018 739943 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1682256282) qz285 0 1 ep1018 ep180 ep1018 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1682256282) qz286 0 1 ep1018 ep181 ep1018 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1020 := @Enclosure.Real.IsNear.sin_image qz177 qz475 Bool.false 475186021 1048576 381 524288 Bool.false 739943 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz177 Bool.false 51022710590000088291 112589990684262400 3613250002879080959 4980075000000000000000 475186021 1048576 381 524288 (ep1012 rfl) rfl) (Enclosure.sfrac_false_div 475186021 1048576) (BSN.sin_reduce0 qz475 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 118378261978506195894272) qz19) 226375608064910080 72057594037927936 Bool.false 739943 1048576 72 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q0 475186021 1048576 226375608064910080 72057594037927936 72 118378261978506195894272 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 739943 1048576 118378261978506195894272 151115727451828646838272 1682256282 2147483648 398796 398406 (ep1019 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1021 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz69 (Real.cos qz177)) (@HMul.hMul Real Real Real qz0 qz69 (@Neg.neg Real Real.instNeg (Real.sin qz177))) Bool.false 162443659209 1099511627776 33565825347217 219026014787862528 Bool.true 161783357349 1099511627776 33565223754157 219026014787862528 (@Enclosure.Real.IsNear.mulLit_ff qz69 (Real.cos qz177) 218643 1048576 1 1048576 742963 1048576 76420631 104439742464 162443659209 1099511627776 33565825347217 219026014787862528 qz383 (@Enclosure.Real.IsNear.recentre' (Real.cos qz177) Bool.false 742963 1048576 76420631 104439742464 742963 1048576 76420631 104439742464 (ep1017 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz69 (@Neg.neg Real Real.instNeg (Real.sin qz177)) 218643 1048576 1 1048576 739943 1048576 76420631 104439742464 161783357349 1099511627776 33565223754157 219026014787862528 qz383 (@Enclosure.Real.IsNear.neg (Real.sin qz177) Bool.false 739943 1048576 76420631 104439742464 (@Enclosure.Real.IsNear.recentre' (Real.sin qz177) Bool.false 739943 1048576 76420631 104439742464 739943 1048576 76420631 104439742464 (ep1020 rfl rfl) rfl)) rfl)

noncomputable def ep1022 := @ep920 162443659209 1099511627776 33565825347217 219026014787862528 Bool.true 161783357349 1099511627776 33565223754157 219026014787862528 Bool.false ep921 2067592622807 549755813888 18160358779943 3422281481060352 Bool.true 89400279112676215357440 40654540095 549755813888 581128753669903 109513007393931264 (ep922 (BSN.head_sum_c_succ qz149 22 23 rfl rfl) (ep1010 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1011 ep1021) rfl rfl

noncomputable abbrev qz178 := (@HMul.hMul Real Real Real qz267 qz452 qz570)

noncomputable def ep1023 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz348 qz150) (Complex.mk (@HMul.hMul Real Real Real qz0 qz71 (Real.cos qz178)) (@HMul.hMul Real Real Real qz0 qz71 (@Neg.neg Real Real.instNeg (Real.sin qz178)))) Bool.false 178471925331 1099511627776 32880244956767 219026014787862528 Bool.true 136085782161 1099511627776 32840796786677 219026014787862528 (BSN.cpow_neg_s_mk qz152 144530 1000 24 qz153 rfl)

noncomputable def ep1024 := @Enclosure.Real.IsNear.mulLit_ff qz152 qz570 144530 1000 0 1 3578169457974519 1125899906842624 250000000199203 49800750000000000000 51715283176105723107 112589990684262400 3613250002879080959 4980075000000000000000 qz154 (BSN.isNear_log_sfrac 24 1 3578169457974519 1125899906842624 250000000199203 49800750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz385) Bool.false 60031721881041427759104 18889465931478580854784 1000000000796812 199203000000000000000 3578169457974519 1125899906842624 250000000199203 49800750000000000000 (BSN.log_rat_reduce_isNear 24 1 4 48 32 212580 524288 24973259072661432 36028797018963968 199203 1000000000000000 rfl rfl rfl rfl (ep398 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1025 := nat_lit 136879068787492297759651892500511320366728883327461141735653596013752552625281

noncomputable def ep1026 := nat_lit 14673154142704994753229804579511418498415484880189892049594726526154806401

noncomputable def ep1027 := nat_lit 410607860054191483289449217892374938263189819012623045422861598588205348263041

noncomputable def ep1028 := BSN.cos_dyadic_bound_f 1398992657 2147483648 3 2 1048576 398796 ep1025 ep57 ep1026 ep1027 ep60 ep1026 833829 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1398992657) qz281 0 2 ep1025 ep57 ep1026 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1398992657) qz282 0 2 ep1027 ep60 ep1026 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz476 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 240818053) qz37)

noncomputable def ep1029 := @Enclosure.Real.IsNear.cos_image qz178 qz476 Bool.false 240818053 524288 381 524288 Bool.false 833829 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz178 Bool.false 51715283176105723107 112589990684262400 3613250002879080959 4980075000000000000000 240818053 524288 381 524288 (ep1024 rfl) rfl) (Enclosure.sfrac_false_div 240818053 524288) (BSN.cos_reduce0 qz476 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 49222678224839204929536) qz38) 226375608064910080 72057594037927936 Bool.false 833829 1048576 73 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q0 240818053 524288 226375608064910080 72057594037927936 73 49222678224839204929536 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 833829 1048576 49222678224839204929536 75557863725914323419136 1398992657 2147483648 398796 398406 (ep1028 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1030 := nat_lit 3830555330850214302022226659776283201

noncomputable def ep1031 := BSN.sin_dyadic_bound_f 1398992657 2147483648 2 1 1048576 398796 ep1030 ep180 ep1030 ep1030 ep181 ep1030 635799 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1398992657) qz285 0 1 ep1030 ep180 ep1030 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1398992657) qz286 0 1 ep1030 ep181 ep1030 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1032 := @Enclosure.Real.IsNear.sin_image qz178 qz476 Bool.false 240818053 524288 381 524288 Bool.false 635799 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz178 Bool.false 51715283176105723107 112589990684262400 3613250002879080959 4980075000000000000000 240818053 524288 381 524288 (ep1024 rfl) rfl) (Enclosure.sfrac_false_div 240818053 524288) (BSN.sin_reduce0 qz476 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 49222678224839204929536) qz38) 226375608064910080 72057594037927936 Bool.false 635799 1048576 73 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q0 240818053 524288 226375608064910080 72057594037927936 73 49222678224839204929536 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 635799 1048576 49222678224839204929536 75557863725914323419136 1398992657 2147483648 398796 398406 (ep1031 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1033 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz71 (Real.cos qz178)) (@HMul.hMul Real Real Real qz0 qz71 (@Neg.neg Real Real.instNeg (Real.sin qz178))) Bool.false 178471925331 1099511627776 32880244956767 219026014787862528 Bool.true 136085782161 1099511627776 32840796786677 219026014787862528 (@Enclosure.Real.IsNear.mulLit_ff qz71 (Real.cos qz178) 214039 1048576 1 1048576 833829 1048576 76420631 104439742464 178471925331 1099511627776 32880244956767 219026014787862528 qz387 (@Enclosure.Real.IsNear.recentre' (Real.cos qz178) Bool.false 833829 1048576 76420631 104439742464 833829 1048576 76420631 104439742464 (ep1029 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz71 (@Neg.neg Real Real.instNeg (Real.sin qz178)) 214039 1048576 1 1048576 635799 1048576 76420631 104439742464 136085782161 1099511627776 32840796786677 219026014787862528 qz387 (@Enclosure.Real.IsNear.neg (Real.sin qz178) Bool.false 635799 1048576 76420631 104439742464 (@Enclosure.Real.IsNear.recentre' (Real.sin qz178) Bool.false 635799 1048576 76420631 104439742464 635799 1048576 76420631 104439742464 (ep1032 rfl rfl) rfl)) rfl)

noncomputable def ep1034 := @ep917 178471925331 1099511627776 32880244956767 219026014787862528 Bool.true 136085782161 1099511627776 32840796786677 219026014787862528 Bool.false ep918 4313657170945 1099511627776 1195143206873119 219026014787862528 Bool.true 119514089486843734130688 217394862351 1099511627776 1195098304126483 219026014787862528 (ep919 (BSN.head_sum_c_succ qz149 23 24 rfl rfl) (ep1022 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1023 ep1033) rfl rfl

theorem EMRow50.d14 : Enclosure.Complex.IsNear qz170 Bool.false 4313657170945 1099511627776 1195143206873119 219026014787862528 Bool.true 217394862351 1099511627776 1195098304126483 219026014787862528 := ep916 (BSN.head_sum_c_succ qz149 24 25 rfl rfl) (ep1034 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep1035 := nat_lit 2338006098761582178885955161603

noncomputable def ep1036 := nat_lit 558738924781207479970043002880

noncomputable def ep1037 := nat_lit 2582135003329393500307590457696744636297

noncomputable def ep1038 := nat_lit 332576789070325824003141220453915086028800

noncomputable abbrev qz597 := (@HAdd.hAdd Complex Complex Complex qz609 (@HAdd.hAdd Complex Complex Complex qz609 qz612 (@HMul.hMul Complex Complex Complex qz611 Complex.I (@HDiv.hDiv Complex Complex Complex qz613 (↑qz616) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz477 := qz597

noncomputable abbrev qz179 := (Complex.Stirling.logGammaStirling 1 qz477)

noncomputable abbrev qz598 := (@HAdd.hAdd Complex Complex Complex qz609 qz612 (@HMul.hMul Complex Complex Complex qz611 Complex.I (@HDiv.hDiv Complex Complex Complex qz613 (↑qz616) (2 : Complex))))

noncomputable abbrev qz478 := qz598

noncomputable abbrev qz180 := qz478

noncomputable abbrev qz181 := (@HMul.hMul Real Real Real qz267 (@HDiv.hDiv Real Real Real qz270 qz452 (2 : Real)) (Real.log Real.pi))

noncomputable def ep1039 := Complex.re (@HMul.hMul Complex Complex Complex qz73 (Complex.exp (@HMul.hMul Complex Complex Complex qz73 Complex.I ↑(@HSub.hSub Real Real Real qz392 (Complex.im (@HSub.hSub Complex Complex Complex qz74 qz179 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz180 (@Nat.cast Complex Complex.instNatCast j))))) qz181))) (zetaApproximant qz149 1 29))

noncomputable def ep1040 := @Enclosure.Real.IsNear.of_eq ep1039 (@HSub.hSub Real Real Real qz392 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz392 (Complex.im (@HSub.hSub Complex Complex Complex qz74 qz179 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz180 (@Nat.cast Complex Complex.instNatCast j))))) qz181)) (Complex.re (zetaApproximant qz149 1 29))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz392 (Complex.im (@HSub.hSub Complex Complex Complex qz74 qz179 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz180 (@Nat.cast Complex Complex.instNatCast j))))) qz181)) (Complex.im (zetaApproximant qz149 1 29))))

noncomputable def ep1041 := nat_lit 467594453849344371130711008615

noncomputable def ep1042 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz392 (Complex.im (@HSub.hSub Complex Complex Complex qz74 qz179 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz180 (@Nat.cast Complex Complex.instNatCast j))))) qz181)) (Complex.re (zetaApproximant qz149 1 29))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz392 (Complex.im (@HSub.hSub Complex Complex Complex qz74 qz179 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz180 (@Nat.cast Complex Complex.instNatCast j))))) qz181)) (Complex.im (zetaApproximant qz149 1 29))) ep1041

noncomputable def ep1043 := nat_lit 111747784956241495994008600576

noncomputable def ep1044 := nat_lit 2569370855030654122103947444364428060187

noncomputable def ep1045 := nat_lit 2182573924926591718632980480

noncomputable def ep1046 := nat_lit 1276414829873937820364301333231657611

noncomputable def ep1047 := nat_lit 33257678907032582400314122045391508602880

noncomputable def ep1048 := nat_lit 1020574229495275009169094686343413610516673833480788901888

noncomputable def ep1049 := @Enclosure.Real.IsNear.mulLit_tf (Real.cos (@HSub.hSub Real Real Real qz392 (Complex.im (@HSub.hSub Complex Complex Complex qz74 qz179 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz180 (@Nat.cast Complex Complex.instNatCast j))))) qz181)) (Complex.re (zetaApproximant qz149 1 29)) 1048575 1048576 79733761

noncomputable def ep1050 := nat_lit 2229666232026056176862461

noncomputable def ep1051 := nat_lit 9753860793804591160346990447

noncomputable def ep1052 := nat_lit 1592194605348456482398116249600

noncomputable def ep1053 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz392 (Complex.im (@HSub.hSub Complex Complex Complex qz74 qz179 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz180 (@Nat.cast Complex Complex.instNatCast j))))) qz181)) Bool.true 1048575 1048576 79733761

noncomputable abbrev qz479 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 161414965) qz16)

noncomputable def ep1054 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz392 (Complex.im (@HSub.hSub Complex Complex Complex qz74 qz179 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz180 (@Nat.cast Complex Complex.instNatCast j))))) qz181) qz479 Bool.false 161414965 1048576 395

noncomputable def ep1055 := nat_lit 2616394276874000661519259

noncomputable def ep1056 := nat_lit 6962649497600000000000000000

noncomputable def ep1057 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz392 (Complex.im (@HSub.hSub Complex Complex Complex qz74 qz179 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz180 (@Nat.cast Complex Complex.instNatCast j))))) qz181) Bool.false 2773087996454021113 18014398509481984 ep1055 ep1056

noncomputable def ep1058 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz74 qz179 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz180 (@Nat.cast Complex Complex.instNatCast j))))) qz181 106582725936074614609 450359962737049600 697006970874000661519259 ep1056 1084278513 13107200

noncomputable def ep1059 := nat_lit 908685474678053638307840000

noncomputable def ep1060 := nat_lit 1963456372551839962580173

noncomputable def ep1061 := nat_lit 10443974246400000000000000000

noncomputable def ep1062 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz74 qz179 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz180 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 25595029096446227291 225179981368524800 ep1060 ep1061 Bool.false 106582725936074614609 450359962737049600

noncomputable def ep1063 := nat_lit 151361945600000000000000000

noncomputable def ep1064 := nat_lit 1986163312601114036064977

noncomputable def ep1065 := @Enclosure.Complex.IsNear.subLitP qz179 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz180 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 23667300461769855091 225179981368524800 28075970614876989443817 ep1063 Bool.false 107988226778650747409 450359962737049600 ep1064

noncomputable def ep1066 := nat_lit 20887948492800000000000000000

noncomputable def ep1067 := nat_lit 28817440875323058038355440470851584

noncomputable def ep1068 := nat_lit 30000370300614833364104565703573504

noncomputable abbrev qz480 := (@HSub.hSub Complex Complex Complex qz572 qz597 qz575)

noncomputable abbrev qz481 := (Complex.log qz597)

noncomputable abbrev qz182 := (@HSub.hSub Complex Complex Complex qz389 (@HMul.hMul Complex Complex Complex qz388 qz480 qz481) qz477)

noncomputable abbrev qz183 := qz477

noncomputable def ep1069 := @Enclosure.Complex.IsNear.of_eq qz179 (@HAdd.hAdd Complex Complex Complex qz4 (@HAdd.hAdd Complex Complex Complex qz4 qz182 qz79) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz81 2 k))) (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz73 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz82 qz183 (@HSub.hSub Int Int Int qz399 qz84 (@HMul.hMul Int Int Int qz400 qz85 (@Nat.cast Int instNatCastInt k)))))) Bool.true 23667300461769855091

noncomputable def ep1070 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz4 qz182 qz79) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz81 2 k))) (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz73 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz82 qz183 (@HSub.hSub Int Int Int qz399 qz84 (@HMul.hMul Int Int Int qz400 qz85 (@Nat.cast Int instNatCastInt k))))) Bool.true 23667308538849202291 225179981368524800

noncomputable def ep1071 := nat_lit 1626404503486515614312065662976

noncomputable def ep1072 := nat_lit 74208944378773822580417877770240

noncomputable def ep1073 := @ep1070 107101303127511543 577400000000000000000 Bool.false 21597749122865976221 90071992547409920 1262750005769782093 13280200000000000000000 Bool.false 2464929 68719476736 3 68719476736 Bool.true 3958402093 3435973836800 14453 10307921510400 Bool.true ep1071 23667300461769855091 225179981368524800 28075970614876989443817 ep1063 Bool.false ep1072

noncomputable def ep1074 := @Enclosure.Complex.IsNear.addLitP qz182 qz79 Bool.true 23874234909209727091 225179981368524800 212000000053851211 1154800000000000000000

noncomputable def ep1075 := nat_lit 3102121464804042642685952

noncomputable def ep1076 := @ep1074 Bool.false 21597749122865976221 90071992547409920 1262750005769782093 13280200000000000000000 Bool.false 120447 131072 1 524288 Bool.false 0 1 0 1 Bool.true ep1075 23667308538849202291 225179981368524800 107101303127511543 577400000000000000000 Bool.false 21597749122865976221 21597749122865976221 90071992547409920

noncomputable abbrev qz184 := (@HMul.hMul Complex Complex Complex qz388 qz480 qz481)

noncomputable def ep1077 := @Enclosure.Complex.IsNear.subLitP qz184 qz183 Bool.true 23367579951130546291 225179981368524800 212000000053851211 1154800000000000000000 Bool.false 140534008321522770449

noncomputable def ep1078 := @ep1077 450359962737049600 1262750005769782093 13280200000000000000000 Bool.false 9000 4000 0 1 Bool.false 289060 4000 0 1 Bool.true 95496939636838908364000 23874234909209727091 225179981368524800 212000000053851211 1154800000000000000000 Bool.false 431954982457319524420000 21597749122865976221 90071992547409920 1262750005769782093 13280200000000000000000

noncomputable abbrev qz185 := qz480

noncomputable abbrev qz186 := qz481

noncomputable def ep1079 := @Enclosure.Complex.IsNear.mul qz185 qz186 Bool.true 23367579951130546291 225179981368524800 212000000053851211 1154800000000000000000 Bool.false 140534008321522770449 450359962737049600 1262750005769782093

noncomputable abbrev qz187 := (Complex.re qz480)

noncomputable abbrev qz188 := (Complex.re qz481)

noncomputable abbrev qz189 := (Complex.im qz480)

noncomputable abbrev qz190 := (Complex.im qz481)

noncomputable def ep1080 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz187 qz188) (@HMul.hMul Real Real Real qz0 qz189 qz190) 67476913526104131 9007199254740992 875000004183263 398406000000000000000 12527251394641574783 112589990684262400

noncomputable def ep1081 := nat_lit 105238224360461801406027896335630336

noncomputable def ep1082 := @Enclosure.Real.IsNear.mulLit_ff qz187 qz188 7000 4000 0 1 9639559075157733 2251799813685248 125000000597609 99601500000000000000

noncomputable def ep1083 := @Enclosure.Complex.IsNear.re_isNear qz185 Bool.false 7000 4000 0 1 Bool.false 289060 4000 0 1

noncomputable abbrev qz599 := (Enclosure.sfrac Bool.false 289060 4000)

noncomputable abbrev qz482 := qz599

noncomputable def ep1084 := @Enclosure.Complex.IsNear.of_eq qz185 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz482) Bool.false 7000 4000 0 1 Bool.false 289060 4000 0

noncomputable abbrev qz483 := (Complex.log (Complex.mk qz578 qz599))

noncomputable def ep1085 := @Enclosure.Complex.IsNear.of_eq qz186 qz483 Bool.false 9639559075157733 2251799813685248 125000000597609 99601500000000000000 Bool.false 866757863048611 562949953421312 1000000000199203 398406000000000000000

noncomputable def ep1086 := nat_lit 1156978038421400796819911409123086857504841107980821729280000000000000

noncomputable def ep1087 := nat_lit 5728949035783701728984880619731350768724894775738822656000000000000

noncomputable def ep1088 := nat_lit 527546955325799617195938504920727015328707455447040000000000000

noncomputable def ep1089 := BSN.log_dyadic_bound 18100683600 149172683600 4 3 ep1086 1048576 398406 ep1087 ep1088 255729 167273367200 131072000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 18100683600) (BSN.artanhQ 149172683600) 0 3 ep1087 ep1086 ep1088 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz600 := (Real.log (Enclosure.sfrac Bool.false 83636683600 16000000))

noncomputable def ep1090 := @Enclosure.Real.IsNear.mulLit_ff qz94 qz600 1 2 0 1 9639559075157733 1125899906842624 125000000597609 49800750000000000000 9639559075157733 2251799813685248 125000000597609 99601500000000000000 qz402 (BSN.isNear_log_sfrac 83636683600 16000000 9639559075157733 1125899906842624 125000000597609 49800750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 83636683600) qz403)) Bool.false 323449929497363041222656 37778931862957161709568 1000000004780872 398406000000000000000 9639559075157733 1125899906842624 125000000597609 49800750000000000000 (BSN.log_rat_reduce_isNear 83636683600 16000000 12 167273367200 131072000000 255729 1048576 24973259072661432 36028797018963968 398406 1000000000000000 rfl rfl rfl rfl (ep1089 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1091 := BSN.arctan_dyadic_bound_f 9000 289060 1 0 1048576 398406 0 1 1 0 1 1 32637 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 289060) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 289060) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz484 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 289060)))

noncomputable def ep1092 := @Enclosure.Real.IsNear.subLit_ff_p qz95 qz484 884279719003555 562949953421312 1 2000000000000000 32637 1048576 1 398406 908861493004060327936 866757863048611 562949953421312 1000000000199203 398406000000000000000 qz96 (ep1091 rfl) rfl rfl

noncomputable abbrev qz485 := (Complex.mk qz578 qz599)

noncomputable abbrev qz486 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 289060) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep1093 := @Enclosure.Complex.IsNear.re_isNear qz186 Bool.false 9639559075157733 2251799813685248 125000000597609 99601500000000000000 Bool.false 866757863048611 562949953421312 1000000000199203 398406000000000000000 (ep1085 (@congrArg Complex Complex qz183 qz485 Complex.log (BSN.w_shift_mk qz152 Bool.false 144530 1000 2 qz153 rfl)) (@Enclosure.Complex.IsNear.of_parts qz483 Bool.false 9639559075157733 2251799813685248 125000000597609 99601500000000000000 Bool.false 866757863048611 562949953421312 1000000000199203 398406000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz483) (@HMul.hMul Real Real Real qz0 qz94 qz600) Bool.false 9639559075157733 2251799813685248 125000000597609 99601500000000000000 (Enclosure.clog_re_eq 9000 289060 4000 83636683600 16000000 rfl rfl rfl) (ep1090 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz483) qz486 Bool.false 866757863048611 562949953421312 1000000000199203 398406000000000000000 (Enclosure.clog_im_eq 9000 289060 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz486 (@HSub.hSub Real Real Real qz392 qz95 qz484) Bool.false 866757863048611 562949953421312 1000000000199203 398406000000000000000 (BSN.arctan_recip 289060 9000 rfl rfl) ep1092))))

noncomputable def ep1094 := @Enclosure.Real.IsNear.mulLit_ff qz189 qz190 289060 4000 0 1 866757863048611 562949953421312 1000000000199203 398406000000000000000

noncomputable def ep1095 := @Enclosure.Complex.IsNear.im_isNear qz185 Bool.false 7000 4000 0 1 Bool.false 289060 4000 0 1

noncomputable def ep1096 := @Enclosure.Complex.IsNear.im_isNear qz186 Bool.false 9639559075157733 2251799813685248 125000000597609 99601500000000000000 Bool.false 866757863048611 562949953421312 1000000000199203 398406000000000000000 (ep1085 (@congrArg Complex Complex qz183 qz485 Complex.log (BSN.w_shift_mk qz152 Bool.false 144530 1000 2 qz153 rfl)) (@Enclosure.Complex.IsNear.of_parts qz483 Bool.false 9639559075157733 2251799813685248 125000000597609 99601500000000000000 Bool.false 866757863048611 562949953421312 1000000000199203 398406000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz483) (@HMul.hMul Real Real Real qz0 qz94 qz600) Bool.false 9639559075157733 2251799813685248 125000000597609 99601500000000000000 (Enclosure.clog_re_eq 9000 289060 4000 83636683600 16000000 rfl rfl rfl) (ep1090 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz483) qz486 Bool.false 866757863048611 562949953421312 1000000000199203 398406000000000000000 (Enclosure.clog_im_eq 9000 289060 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz486 (@HSub.hSub Real Real Real qz392 qz95 qz484) Bool.false 866757863048611 562949953421312 1000000000199203 398406000000000000000 (BSN.arctan_recip 289060 9000 rfl rfl) ep1092))))

noncomputable abbrev qz191 := (@ep1084 1 (BSN.w_sub_half_mk qz452 Bool.false 144530 1000 2 qz453 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz482 Bool.false 7000 4000 0 1 Bool.false 289060 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) (Enclosure.Real.IsNear.const Bool.false 289060 4000)))

noncomputable def ep1097 := @ep1080 14453000002879080959 79681200000000000000000 ep1081 23367579951130546291 225179981368524800 212000000053851211 1154800000000000000000 (@ep1082 67476913526104131 9007199254740992 875000004183263 398406000000000000000 (ep1083 qz191) ep1093 rfl) (@ep1094 12527251394641574783 112589990684262400 14453000002879080959 79681200000000000000000 (ep1095 qz191) ep1096 rfl) rfl

noncomputable def ep1098 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz187 qz190) (@HMul.hMul Real Real Real qz0 qz189 qz188) 6067305041340277 2251799813685248 7000000001394421 1593624000000000000000 139320547313254715049 450359962737049600

noncomputable def ep1099 := nat_lit 316454453754846066506606961441636352

noncomputable def ep1100 := @Enclosure.Real.IsNear.mulLit_ff qz187 qz190 7000 4000 0 1 866757863048611 562949953421312 1000000000199203 398406000000000000000

noncomputable def ep1101 := @Enclosure.Real.IsNear.mulLit_ff qz189 qz188 289060 4000 0 1 9639559075157733 2251799813685248 125000000597609 99601500000000000000

noncomputable def ep1102 := @ep1098 1806625008637242877 19920300000000000000000 ep1099 140534008321522770449 450359962737049600 1262750005769782093 13280200000000000000000 (@ep1100 6067305041340277 2251799813685248 7000000001394421 1593624000000000000000 (ep1083 qz191) ep1096 rfl) (@ep1101 139320547313254715049 450359962737049600 1806625008637242877 19920300000000000000000 (ep1095 qz191) ep1093 rfl) rfl

noncomputable def ep1103 := @Enclosure.Complex.IsNear.of_eq qz183 qz485 Bool.false 9000 4000 0 1 Bool.false 289060 4000 0 1 (BSN.w_shift_mk qz152 Bool.false 144530 1000 2 qz153 rfl)

noncomputable abbrev qz487 := (ep1103 (@Enclosure.Complex.IsNear.mk qz578 qz599 Bool.false 9000 4000 0 1 Bool.false 289060 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 289060 4000)))

noncomputable abbrev qz192 := qz487

noncomputable def ep1104 := ep1078 (@ep1079 13280200000000000000000 (ep1097 rfl) (ep1102 rfl)) qz192 rfl rfl rfl rfl rfl rfl

noncomputable def ep1105 := @ep1076 1262750005769782093 13280200000000000000000 (ep1104 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz99 (↑qz2) Bool.false 120447 131072 1 524288 Bool.false 0 1 0 1 (@ep481 131072 1 524288 (ep483 rfl) (ep485 rfl) rfl rfl) (@ep486 1 0 1 (ep488 rfl) (ep490 rfl) rfl rfl))

noncomputable abbrev qz488 := (@HPow.hPow Complex Int Complex qz577 qz597 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz193 := qz488

noncomputable def ep1106 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz81 2 k))) (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz73 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz82 qz183 (@HSub.hSub Int Int Int qz399 qz84 (@HMul.hMul Int Int Int qz400 qz85 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz81 2 k))) (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz73 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz82 qz183 (@HSub.hSub Int Int Int qz399 qz84 (@HMul.hMul Int Int Int qz400 qz85 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102) qz193)) Bool.false 2464929 68719476736 3 68719476736

noncomputable def ep1107 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz81 2 k))) (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz73 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz82 qz183 (@HSub.hSub Int Int Int qz399 qz84 (@HMul.hMul Int Int Int qz400 qz85 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102) qz193) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1108 := @ep1107 0 1 0 1 Bool.false 2464929 68719476736 3 68719476736 Bool.true 3958402093 3435973836800 14453 10307921510400 Bool.false 2464929 2464929 68719476736 3 68719476736 Bool.true 3958402093 3958402093 3435973836800 14453

noncomputable def ep1109 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz81 2 k))) (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz73 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz82 qz183 (@HSub.hSub Int Int Int qz399 qz84 (@HMul.hMul Int Int Int qz400 qz85 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1110 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz80 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102) qz193 Bool.false 2464929 68719476736 3 68719476736 Bool.true 3958402093 3435973836800 14453 10307921510400

noncomputable abbrev qz194 := (Complex.re qz488)

noncomputable abbrev qz195 := (Complex.im qz488)

noncomputable def ep1111 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz80 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102)) qz194) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz80 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102)) qz195) 2464929 68719476736 3 68719476736 0 1 0

noncomputable def ep1112 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz80 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102)) qz194 1 12 0 1 7394787 17179869184 9 17179869184 2464929

noncomputable def ep1113 := @Enclosure.Complex.IsNear.re_isNear qz193 Bool.false 7394787 17179869184 9 17179869184 Bool.true 11875206279 858993459200 14453 858993459200

noncomputable abbrev qz489 := (@HPow.hPow Complex Nat Complex qz580 qz597 1)

noncomputable abbrev qz196 := (@Inv.inv Complex Complex.instInv qz489)

noncomputable def ep1114 := @Enclosure.Complex.IsNear.of_eq qz193 qz196 Bool.false 7394787 17179869184 9 17179869184 Bool.true 11875206279 858993459200 14453

noncomputable def ep1115 := @Enclosure.Complex.IsNear.of_parts qz196 Bool.false 7394787 17179869184 9 17179869184 Bool.true 11875206279 858993459200 14453

noncomputable abbrev qz197 := (Complex.re qz489)

noncomputable abbrev qz198 := qz489

noncomputable def ep1116 := @Enclosure.Real.IsNear.mulLit_ff qz197 (@Inv.inv Real Real.instInv (@DFunLike.coe qz108 Complex (fun (x : Complex) => Real) qz109 Complex.normSq qz198)) 9000 4000 0 1 821643 4294967296 1 4294967296

noncomputable def ep1117 := @Enclosure.Complex.IsNear.re_isNear qz198 Bool.false 9000 4000 0 1 Bool.false 289060 4000 0 1

noncomputable def ep1118 := @Enclosure.Complex.IsNear.of_eq qz198 qz183 Bool.false 9000 4000 0 1 Bool.false 289060 4000 0

noncomputable def ep1119 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz108 Complex (fun (x : Complex) => Real) qz109 Complex.normSq qz198)) Bool.false 821643 4294967296 1 4294967296 821643 4294967296 1

noncomputable abbrev qz199 := (Complex.im qz489)

noncomputable def ep1120 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz108 Complex (fun (x : Complex) => Real) qz109 Complex.normSq qz198) (@HAdd.hAdd Real Real Real qz412 (@HMul.hMul Real Real Real qz0 qz197 qz197) (@HMul.hMul Real Real Real qz0 qz199 qz199)) Bool.false 209091709 40000 0 1

noncomputable def ep1121 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz197 qz197) (@HMul.hMul Real Real Real qz0 qz199 qz199) 81 16 0 1 208889209 40000

noncomputable def ep1122 := @Enclosure.Real.IsNear.mulLit_ff qz197 qz197 9000 4000 0 1 9000 4000 0 1

noncomputable def ep1123 := @Enclosure.Real.IsNear.mulLit_ff qz199 qz199 289060 4000 0 1 289060 4000 0 1

noncomputable def ep1124 := @Enclosure.Complex.IsNear.im_isNear qz198 Bool.false 9000 4000 0 1 Bool.false 289060 4000 0 1

noncomputable abbrev qz200 := (ep1117 (@ep1118 1 (BSN.pow_one_c qz477) qz487))

noncomputable abbrev qz201 := (ep1124 (@ep1118 1 (BSN.pow_one_c qz477) qz487))

noncomputable def ep1125 := @ep1121 0 1 3345467344 209091709 40000 0 1 (@ep1122 81 16 0 1 qz200 qz200 rfl) (@ep1123 208889209 40000 0 1 qz201 qz201 rfl)

noncomputable def ep1126 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz108 Complex (fun (x : Complex) => Real) qz109 Complex.normSq qz198) 209091709 40000 0 1 410821 410822 2147483648 (ep1120 (Enclosure.Complex.normSq_eq_mul_add_mul qz198) (ep1125 rfl rfl)) rfl

noncomputable def ep1127 := @Enclosure.Real.IsNear.of_eq (Complex.re qz196) (@HMul.hMul Real Real Real qz0 qz197 (@Inv.inv Real Real.instInv (@DFunLike.coe qz108 Complex (fun (x : Complex) => Real) qz109 Complex.normSq qz198))) Bool.false 7394787 17179869184 9 17179869184 (Enclosure.Complex.inv_re_eq_mul qz198) (@ep1116 7394787 17179869184 9 17179869184 qz200 (@ep1119 4294967296 (ep1126 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep1128 := @Enclosure.Real.IsNear.of_eq (Complex.im qz196) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz199) (@Inv.inv Real Real.instInv (@DFunLike.coe qz108 Complex (fun (x : Complex) => Real) qz109 Complex.normSq qz198))) Bool.true 11875206279 858993459200 14453 858993459200 (Enclosure.Complex.inv_im_eq_mul qz198)

noncomputable def ep1129 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz199) (@Inv.inv Real Real.instInv (@DFunLike.coe qz108 Complex (fun (x : Complex) => Real) qz109 Complex.normSq qz198)) 289060 4000 0 1 821643 4294967296 1

noncomputable def ep1130 := @ep1129 4294967296 11875206279 858993459200 14453 858993459200 (@Enclosure.Real.IsNear.neg qz199 Bool.false 289060 4000 0 1 qz201) (@ep1119 4294967296 (ep1126 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep1131 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz80 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102)) qz195 0 1 0 1 11875206279 858993459200 14453 858993459200 0

noncomputable def ep1132 := @Enclosure.Complex.IsNear.im_isNear qz193 Bool.false 7394787 17179869184 9 17179869184 Bool.true 11875206279 858993459200 14453 858993459200

noncomputable abbrev qz202 := (@ep1114 858993459200 (BSN.zpow_one_sub_two_mul qz477 1 1 rfl rfl) (@ep1115 858993459200 ep1127 (ep1128 ep1130)))

noncomputable def ep1133 := @ep1111 1 2464929 2464929 68719476736 3 68719476736 (@ep1112 68719476736 3 68719476736 ep500 (ep1113 qz202) rfl) (@ep1131 1 0 1 ep520 (ep1132 qz202) rfl) rfl

noncomputable def ep1134 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz80 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102)) qz195) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz80 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102)) qz194) 3958402093 3435973836800 14453 10307921510400 0 1 0

noncomputable def ep1135 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz80 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102)) qz195 1 12 0 1 11875206279 858993459200 14453 858993459200 3958402093

noncomputable def ep1136 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz80 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102)) qz194 0 1 0 1 7394787 17179869184 9 17179869184 0

noncomputable def ep1137 := @ep1134 1 3958402093 3958402093 3435973836800 14453 10307921510400 (@ep1135 3435973836800 14453 10307921510400 ep500 (ep1132 qz202) rfl) (@ep1136 1 0 1 ep520 (ep1113 qz202) rfl) rfl

noncomputable def ep1138 := @ep1108 10307921510400 (@ep1109 0 1 0 1 (BSN.stirling_sum_base qz183) qz115) (ep1110 (ep1133 rfl) (ep1137 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep1139 := @ep1073 107988226778650747409 450359962737049600 ep1064 ep1066 (ep1105 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep1106 Bool.true 3958402093 3435973836800 14453 10307921510400 (BSN.stirling_sum_succ qz183 0 1 rfl) (ep1138 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep1140 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz180 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz152 2) Bool.false 9638643173381861 1125899906842624 125000000597609 49800750000000000000 Bool.false 878438026610083 281474976710656

noncomputable abbrev qz203 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz272 qz478 qz408))

noncomputable def ep1141 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz152 2) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz152 1) qz203) Bool.false 9638643173381861 1125899906842624 125000000597609 49800750000000000000 Bool.false 878438026610083 281474976710656 1000000000199203 199203000000000000000

noncomputable def ep1142 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz152 1) qz203 Bool.false 9638481038366437 2251799813685248 125000000597609 99601500000000000000 Bool.false 882332488205731 562949953421312 1000000000199203 398406000000000000000 Bool.false

noncomputable def ep1143 := nat_lit 43408589803999724269331132973056

noncomputable def ep1144 := nat_lit 989033292327310912086492577792

noncomputable abbrev qz204 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz272 qz478 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep1145 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz152 1) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz152 0) qz204) Bool.false 9638481038366437 2251799813685248 125000000597609 99601500000000000000 Bool.false 882332488205731 562949953421312 1000000000199203 398406000000000000000

noncomputable def ep1146 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz152 0) qz204 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz490 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz599))

noncomputable def ep1147 := @Enclosure.Complex.IsNear.of_eq qz204 qz490 Bool.false 9638481038366437 2251799813685248 125000000597609 99601500000000000000 Bool.false 882332488205731 562949953421312 1000000000199203 398406000000000000000

noncomputable def ep1148 := nat_lit 1153260163240354830251032192219273955985555773252117729280000000000000

noncomputable def ep1149 := nat_lit 5665856001819777994319944578467967153204588907758022656000000000000

noncomputable def ep1150 := nat_lit 513710956408620598139643930132710501502374783447040000000000000

noncomputable def ep1151 := BSN.log_dyadic_bound 18020683600 149092683600 4 3 ep1148 1048576 398406 ep1149 ep1150 254725 167113367200 131072000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 18020683600) (BSN.artanhQ 149092683600) 0 3 ep1149 ep1148 ep1150 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1152 := @Enclosure.Real.IsNear.mulLit_ff qz94 (Real.log (Enclosure.sfrac Bool.false 83556683600 16000000)) 1 2 0 1 9638481038366437 1125899906842624 125000000597609 49800750000000000000 9638481038366437 2251799813685248 125000000597609 99601500000000000000 qz402 (BSN.isNear_log_sfrac 83556683600 16000000 9638481038366437 1125899906842624 125000000597609 49800750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 83556683600) qz403)) Bool.false 323413756585156001398784 37778931862957161709568 1000000004780872 398406000000000000000 9638481038366437 1125899906842624 125000000597609 49800750000000000000 (BSN.log_rat_reduce_isNear 83556683600 16000000 12 167113367200 131072000000 254725 1048576 24973259072661432 36028797018963968 398406 1000000000000000 rfl rfl rfl rfl (ep1151 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1153 := BSN.arctan_dyadic_bound_f 1000 289060 1 0 1048576 398406 0 1 1 0 1 1 3627 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 289060) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 289060) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz491 := (@Nat.cast Real Real.instNatCast 289060)

noncomputable def ep1154 := @Enclosure.Real.IsNear.subLit_ff_p qz95 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz414 qz491)) 884279719003555 562949953421312 1 2000000000000000 3627 1048576 1 398406 925192671152812589056 882332488205731 562949953421312 1000000000199203 398406000000000000000 qz96 (ep1153 rfl) rfl rfl

noncomputable abbrev qz205 := (@HAdd.hAdd Complex Complex Complex qz272 qz478 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz492 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz599)

noncomputable def ep1155 := @ep1146 9638481038366437 2251799813685248 125000000597609 99601500000000000000 Bool.false 882332488205731 562949953421312 1000000000199203 398406000000000000000 Bool.false 9638481038366437 9638481038366437 2251799813685248 125000000597609 99601500000000000000 Bool.false 882332488205731 882332488205731 562949953421312 1000000000199203 398406000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz152 0) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz152) qz115) (ep1147 (@congrArg Complex Complex qz205 qz492 Complex.log (BSN.w_shift_mk qz152 Bool.false 144530 1000 0 qz153 rfl)) (@Enclosure.Complex.IsNear.of_parts qz490 Bool.false 9638481038366437 2251799813685248 125000000597609 99601500000000000000 Bool.false 882332488205731 562949953421312 1000000000199203 398406000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz490) (@HMul.hMul Real Real Real qz0 qz94 (Real.log (Enclosure.sfrac Bool.false 83556683600 16000000))) Bool.false 9638481038366437 2251799813685248 125000000597609 99601500000000000000 (Enclosure.clog_re_eq 1000 289060 4000 83556683600 16000000 rfl rfl rfl) (ep1152 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz490) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz491 qz414)) Bool.false 882332488205731 562949953421312 1000000000199203 398406000000000000000 (Enclosure.clog_im_eq 1000 289060 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz491 qz414)) (@HSub.hSub Real Real Real qz392 qz95 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz414 qz491))) Bool.false 882332488205731 562949953421312 1000000000199203 398406000000000000000 (BSN.arctan_recip 289060 1000 rfl rfl) ep1154)))) rfl rfl

noncomputable abbrev qz493 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz599))

noncomputable def ep1156 := @Enclosure.Complex.IsNear.of_eq qz203 qz493 Bool.false 9638805308397285 2251799813685248 125000000597609 99601500000000000000 Bool.false 874543565014435 562949953421312 1000000000199203 398406000000000000000

noncomputable def ep1157 := nat_lit 1154374478885351619545224531027566262688860482790728929280000000000000

noncomputable def ep1158 := nat_lit 5684734606284847285519654569436490428372169692152262656000000000000

noncomputable def ep1159 := nat_lit 517829618908272375316618734159904951294434585047040000000000000

noncomputable def ep1160 := BSN.log_dyadic_bound 18044683600 149116683600 4 3 ep1157 1048576 398406 ep1158 ep1159 255027 167161367200 131072000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 18044683600) (BSN.artanhQ 149116683600) 0 3 ep1158 ep1157 ep1159 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1161 := @Enclosure.Real.IsNear.mulLit_ff qz94 (Real.log (Enclosure.sfrac Bool.false 83580683600 16000000)) 1 2 0 1 9638805308397285 1125899906842624 125000000597609 49800750000000000000 9638805308397285 2251799813685248 125000000597609 99601500000000000000 qz402 (BSN.isNear_log_sfrac 83580683600 16000000 9638805308397285 1125899906842624 125000000597609 49800750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 83580683600) qz403)) Bool.false 323424637281855728517120 37778931862957161709568 1000000004780872 398406000000000000000 9638805308397285 1125899906842624 125000000597609 49800750000000000000 (BSN.log_rat_reduce_isNear 83580683600 16000000 12 167161367200 131072000000 255027 1048576 24973259072661432 36028797018963968 398406 1000000000000000 rfl rfl rfl rfl (ep1160 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1162 := BSN.arctan_dyadic_bound_f 5000 289060 1 0 1048576 398406 0 1 1 0 1 1 18135 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 289060) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 289060) 0 0 rfl) rfl rfl rfl

noncomputable def ep1163 := @Enclosure.Real.IsNear.subLit_ff_p qz95 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz418 qz491)) 884279719003555 562949953421312 1 2000000000000000 18135 1048576 1 398406 917025393228576194560 874543565014435 562949953421312 1000000000199203 398406000000000000000 qz96 (ep1162 rfl) rfl rfl

noncomputable abbrev qz206 := (@HAdd.hAdd Complex Complex Complex qz272 qz478 qz408)

noncomputable abbrev qz494 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz599)

noncomputable def ep1164 := @ep1142 9638805308397285 2251799813685248 125000000597609 99601500000000000000 Bool.false 874543565014435 562949953421312 1000000000199203 398406000000000000000 Bool.false ep1143 9638643173381861 1125899906842624 125000000597609 49800750000000000000 Bool.false ep1144 878438026610083 281474976710656 1000000000199203 199203000000000000000 (ep1145 (BSN.log_sum_c_succ qz152 0 1 rfl) (ep1155 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1156 (@congrArg Complex Complex qz206 qz494 Complex.log (BSN.w_shift_mk qz152 Bool.false 144530 1000 1 qz153 rfl)) (@Enclosure.Complex.IsNear.of_parts qz493 Bool.false 9638805308397285 2251799813685248 125000000597609 99601500000000000000 Bool.false 874543565014435 562949953421312 1000000000199203 398406000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz493) (@HMul.hMul Real Real Real qz0 qz94 (Real.log (Enclosure.sfrac Bool.false 83580683600 16000000))) Bool.false 9638805308397285 2251799813685248 125000000597609 99601500000000000000 (Enclosure.clog_re_eq 5000 289060 4000 83580683600 16000000 rfl rfl rfl) (ep1161 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz493) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz491 qz418)) Bool.false 874543565014435 562949953421312 1000000000199203 398406000000000000000 (Enclosure.clog_im_eq 5000 289060 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz491 qz418)) (@HSub.hSub Real Real Real qz392 qz95 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz418 qz491))) Bool.false 874543565014435 562949953421312 1000000000199203 398406000000000000000 (BSN.arctan_recip 289060 5000 rfl rfl) ep1163)))) rfl rfl

noncomputable def ep1165 := @ep1065 ep1066 Bool.false 9638643173381861 1125899906842624 125000000597609 49800750000000000000 Bool.false 878438026610083 281474976710656 1000000000199203 199203000000000000000 Bool.true ep1067 25595029096446227291 225179981368524800 ep1060 ep1061 Bool.false ep1068 106582725936074614609 450359962737049600 697006970874000661519259 ep1056 (@ep1069 225179981368524800 28075970614876989443817 ep1063 Bool.false 107988226778650747409 450359962737049600 ep1064 ep1066 (BSN.logGammaStirling_unfold 1 qz183) (ep1139 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep1140 1000000000199203 199203000000000000000 (BSN.log_sum_c_eq qz152 2) (ep1141 (BSN.log_sum_c_succ qz152 1 2 rfl) (ep1164 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz207 := (@HDiv.hDiv Real Real Real qz270 qz452 (2 : Real))

noncomputable def ep1166 := @Enclosure.Real.IsNear.mulLit_ff qz207 (Real.log Real.pi) 144530 2000 0 1 75021 65536 1 262144 1084278513 13107200 14453 52428800 (@Enclosure.Real.IsNear.of_eq qz207 (Enclosure.sfrac Bool.false 144530 2000) Bool.false 144530 2000 0 1 (BSN.t_half_eq qz152 Bool.false 144530 1000 qz153) (Enclosure.Real.IsNear.const Bool.false 144530 2000)) EMRow50.d5 rfl

noncomputable def ep1167 := @ep1058 14453 52428800 ep1059 2773087996454021113 18014398509481984 ep1055 ep1056 (@ep1062 697006970874000661519259 ep1056 (ep1165 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep1166 rfl rfl

noncomputable def ep1168 := nat_lit 8328380085751228669187526868463175687454186091993780953618714597251550644330625

noncomputable def ep1169 := nat_lit 16702247111967114706728188730316660152314015770337461294724999552435062890625

noncomputable def ep1170 := nat_lit 21785382300690985471680248540411614112609598024926975179286126326859642538090625

noncomputable def ep1171 := BSN.sin_dyadic_bound_f 3371683985 2147483648 3 2 1048576 398796 ep1168 ep64 ep1169 ep1170 ep66 ep1169 1048575 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3371683985) qz285 0 2 ep1168 ep64 ep1169 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3371683985) qz286 0 2 ep1170 ep66 ep1169 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1172 := @ep1054 1048576 Bool.true 1048575 1048576 1 199203 (@ep1057 161414965 1048576 395 1048576 ep1167 rfl) (Enclosure.sfrac_false_div 161414965 1048576) (BSN.cos_reduce1 qz479 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 237261167812391175454720) qz19) 226375608064910080 72057594037927936 Bool.false 1048575 1048576 24 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q1 161414965 1048576 226375608064910080 72057594037927936 24 237261167812391175454720 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1048575 1048576 237261167812391175454720 151115727451828646838272 3371683985 2147483648 398796 398406 (ep1171 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1173 := nat_lit 9752403513468653382419668721

noncomputable abbrev qz495 := (@HPow.hPow Complex Complex Complex qz536 qz581 qz589)

noncomputable abbrev qz208 := qz495

noncomputable abbrev qz209 := (@HAdd.hAdd Complex Complex Complex qz272 (@HDiv.hDiv Complex Complex Complex qz397 qz421 (@HSub.hSub Complex Complex Complex qz389 qz450 (1 : Complex))) qz396)

noncomputable def ep1174 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz149 1 29) (@HAdd.hAdd Complex Complex Complex qz4 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 29, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz150) (@HMul.hMul Complex Complex Complex qz73 qz208 (@HAdd.hAdd Complex Complex Complex qz4 qz209 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz81 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz81 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz81 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz81 2 k) 1))))))) Bool.false ep1050 532854962140281181306880 ep1051

noncomputable def ep1175 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 29, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz150) (@HMul.hMul Complex Complex Complex qz73 qz208 (@HAdd.hAdd Complex Complex Complex qz4 qz209 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz81 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz81 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz81 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz81 2 k) 1)))))) Bool.false 4687488770357 1099511627776 440120011695901 73008671595954176

noncomputable def ep1176 := nat_lit 155593998782586649852930847

noncomputable def ep1177 := nat_lit 155292186252703658441079521

noncomputable def ep1178 := nat_lit 2451543948172149529467663842579316736

noncomputable def ep1179 := nat_lit 48432219988211430382505554761220096

noncomputable def ep1180 := @ep1175 Bool.false 160561332779 1099511627776 440067028744377 73008671595954176 Bool.true 42025661140926689799699 532854962140281181306880 ep1176 ep1052 Bool.true 33763792917794219147199 532854962140281181306880 ep1177 ep1052 Bool.false ep1178 ep1050 532854962140281181306880 ep1051 ep1052 Bool.false ep1179 44048847474379208854321 532854962140281181306880

noncomputable def ep1181 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 29, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz150) (BSN.headSumC qz149 29) Bool.false 4687488770357 1099511627776 440120011695901 73008671595954176 Bool.false 160561332779 1099511627776 440067028744377

noncomputable def ep1182 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz149 29) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz149 28) (@HPow.hPow Complex Complex Complex qz6 qz423 qz150)) Bool.false 4687488770357 1099511627776 440120011695901 73008671595954176 Bool.false 160561332779 1099511627776 440067028744377 73008671595954176

noncomputable def ep1183 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz149 28) (@HPow.hPow Complex Complex Complex qz6 qz423 qz150) Bool.false 4810105693541 1099511627776 1289949138802831 219026014787862528 Bool.true 7192365893 1099511627776 1289744816285731 219026014787862528 Bool.true

noncomputable def ep1184 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz149 28) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz149 27) (@HPow.hPow Complex Complex Complex qz6 qz424 qz150)) Bool.false 4810105693541 1099511627776 1289949138802831 219026014787862528 Bool.true 7192365893 1099511627776 1289744816285731 219026014787862528

noncomputable def ep1185 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz149 27) (@HPow.hPow Complex Complex Complex qz6 qz424 qz150) Bool.false 2364260288815 549755813888 13685056919017 2380717552041984 Bool.true 202433301991 1099511627776 54726466100575 9522870208167936 Bool.false

noncomputable def ep1186 := nat_lit 2644383570439935159697408

noncomputable def ep1187 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz149 27) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz149 26) (@HPow.hPow Complex Complex Complex qz6 qz425 qz150)) Bool.false 2364260288815 549755813888 13685056919017 2380717552041984 Bool.true 202433301991 1099511627776 54726466100575 9522870208167936

noncomputable def ep1188 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz149 26) (@HPow.hPow Complex Complex Complex qz6 qz425 qz150) Bool.false 1131425264005 274877906944 613698940062013 109513007393931264 Bool.true 137827788393 549755813888 613603451307151 109513007393931264 Bool.false

noncomputable def ep1189 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz149 26) (@HAdd.hAdd Complex Complex Complex qz4 qz170 (@HPow.hPow Complex Complex Complex qz6 qz426 qz150)) Bool.false 1131425264005 274877906944 613698940062013 109513007393931264 Bool.true 137827788393 549755813888 613603451307151 109513007393931264

noncomputable def ep1190 := @Enclosure.Complex.IsNear.addLitP qz170 (@HPow.hPow Complex Complex Complex qz6 qz426 qz150) Bool.false 4313657170945 1099511627776 1195143206873119 219026014787862528 Bool.true 217394862351 1099511627776 1195098304126483 219026014787862528 Bool.false

noncomputable def ep1191 := nat_lit 4976060934932112364011520

noncomputable abbrev qz210 := (@HMul.hMul Real Real Real qz267 qz452 qz582)

noncomputable def ep1192 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz426 qz150) (Complex.mk (@HMul.hMul Real Real Real qz0 qz126 (Real.cos qz210)) (@HMul.hMul Real Real Real qz0 qz126 (@Neg.neg Real Real.instNeg (Real.sin qz210)))) Bool.false 212043885075 1099511627776 32254673250907 219026014787862528 Bool.true 58260714435 1099511627776 32108598487819 219026014787862528 (BSN.cpow_neg_s_mk qz152 144530 1000 25 qz153 rfl)

noncomputable def ep1193 := @Enclosure.Real.IsNear.mulLit_ff qz152 qz582 144530 1000 0 1 3624129903009015 1125899906842624 250000000199203 49800750000000000000 10475909897637858759 22517998136852480 3613250002879080959 4980075000000000000000 qz154 (BSN.isNear_log_sfrac 25 1 3624129903009015 1125899906842624 250000000199203 49800750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz428) Bool.false 60802810194841294602240 18889465931478580854784 1000000000796812 199203000000000000000 3624129903009015 1125899906842624 250000000199203 49800750000000000000 (BSN.log_rat_reduce_isNear 25 1 4 50 32 233982 524288 24973259072661432 36028797018963968 199203 1000000000000000 rfl rfl rfl rfl (ep586 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1194 := nat_lit 109944756459039496428636992283646881

noncomputable def ep1195 := BSN.cos_dyadic_bound_f 575829129 2147483648 2 1 1048576 398796 ep1194 ep184 ep1194 ep1194 ep185 ep1194 1011105 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 575829129) qz281 0 1 ep1194 ep184 ep1194 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 575829129) qz282 0 1 ep1194 ep185 ep1194 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz496 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 60977821) (@Nat.cast Real Real.instNatCast 131072))

noncomputable def ep1196 := @Enclosure.Real.IsNear.cos_image qz210 qz496 Bool.false 60977821 131072 381 524288 Bool.false 1011105 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz210 Bool.false 10475909897637858759 22517998136852480 3613250002879080959 4980075000000000000000 60977821 131072 381 524288 (ep1193 rfl) rfl) (Enclosure.sfrac_false_div 60977821 131072) (BSN.cos_reduce0 qz496 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 5065046586841158909952) qz295) 226375608064910080 72057594037927936 Bool.false 1011105 1048576 74 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q0 60977821 131072 226375608064910080 72057594037927936 74 5065046586841158909952 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1011105 1048576 5065046586841158909952 18889465931478580854784 575829129 2147483648 398796 398406 (ep1195 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1197 := BSN.sin_dyadic_bound_f 575829129 2147483648 2 1 1048576 398796 ep1194 ep180 ep1194 ep1194 ep181 ep1194 277809 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 575829129) qz285 0 1 ep1194 ep180 ep1194 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 575829129) qz286 0 1 ep1194 ep181 ep1194 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1198 := @Enclosure.Real.IsNear.sin_image qz210 qz496 Bool.false 60977821 131072 381 524288 Bool.false 277809 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz210 Bool.false 10475909897637858759 22517998136852480 3613250002879080959 4980075000000000000000 60977821 131072 381 524288 (ep1193 rfl) rfl) (Enclosure.sfrac_false_div 60977821 131072) (BSN.sin_reduce0 qz496 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 5065046586841158909952) qz295) 226375608064910080 72057594037927936 Bool.false 277809 1048576 74 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q0 60977821 131072 226375608064910080 72057594037927936 74 5065046586841158909952 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 277809 1048576 5065046586841158909952 18889465931478580854784 575829129 2147483648 398796 398406 (ep1197 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1199 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz126 (Real.cos qz210)) (@HMul.hMul Real Real Real qz0 qz126 (@Neg.neg Real Real.instNeg (Real.sin qz210))) Bool.false 212043885075 1099511627776 32254673250907 219026014787862528 Bool.true 58260714435 1099511627776 32108598487819 219026014787862528 (@Enclosure.Real.IsNear.mulLit_ff qz126 (Real.cos qz210) 209715 1048576 1 1048576 1011105 1048576 76420631 104439742464 212043885075 1099511627776 32254673250907 219026014787862528 qz430 (@Enclosure.Real.IsNear.recentre' (Real.cos qz210) Bool.false 1011105 1048576 76420631 104439742464 1011105 1048576 76420631 104439742464 (ep1196 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz126 (@Neg.neg Real Real.instNeg (Real.sin qz210)) 209715 1048576 1 1048576 277809 1048576 76420631 104439742464 58260714435 1099511627776 32108598487819 219026014787862528 qz430 (@Enclosure.Real.IsNear.neg (Real.sin qz210) Bool.false 277809 1048576 76420631 104439742464 (@Enclosure.Real.IsNear.recentre' (Real.sin qz210) Bool.false 277809 1048576 76420631 104439742464 277809 1048576 76420631 104439742464 (ep1198 rfl rfl) rfl)) rfl)

noncomputable def ep1200 := @ep1190 212043885075 1099511627776 32254673250907 219026014787862528 Bool.true 58260714435 1099511627776 32108598487819 219026014787862528 Bool.false ep1191 1131425264005 274877906944 613698940062013 109513007393931264 Bool.true 303086511937507018407936 137827788393 549755813888 613603451307151 109513007393931264 EMRow50.d14 (ep1192 ep1199) rfl rfl

noncomputable abbrev qz211 := (@HMul.hMul Real Real Real qz267 qz452 qz583)

noncomputable def ep1201 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz425 qz150) (Complex.mk (@HMul.hMul Real Real Real qz0 qz128 (Real.cos qz211)) (@HMul.hMul Real Real Real qz0 qz128 (@Neg.neg Real Real.instNeg (Real.sin qz211)))) Bool.false 101409760805 549755813888 5271226070923 36504335797977088 Bool.false 73222274795 1099511627776 10500605899641 73008671595954176 (BSN.cpow_neg_s_mk qz152 144530 1000 26 qz153 rfl)

noncomputable def ep1202 := @Enclosure.Real.IsNear.mulLit_ff qz152 qz583 144530 1000 0 1 3668288609262839 1125899906842624 250000000199203 49800750000000000000 53017775269675812067 112589990684262400 3613250002879080959 4980075000000000000000 qz154 (BSN.isNear_log_sfrac 26 1 3668288609262839 1125899906842624 250000000199203 49800750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz432) Bool.false 61543670347942250676224 18889465931478580854784 1000000000796812 199203000000000000000 3668288609262839 1125899906842624 250000000199203 49800750000000000000 (BSN.log_rat_reduce_isNear 26 1 4 52 32 254545 524288 24973259072661432 36028797018963968 199203 1000000000000000 rfl rfl rfl rfl (ep597 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1203 := nat_lit 3075714999523853569914205420592108590124400800091478451240262548480695712252160

noncomputable def ep1204 := nat_lit 2283728717470096652536358797677837724238387647848360776317198290695433912576

noncomputable def ep1205 := nat_lit 8051746580829426812337860092068805998772282801190689073896174067835934258135296

noncomputable def ep1206 := BSN.sin_dyadic_bound_f 2629242018 2147483648 3 2 1048576 398796 ep1203 ep64 ep1204 ep1205 ep66 ep1204 986270 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2629242018) qz285 0 2 ep1203 ep64 ep1204 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2629242018) qz286 0 2 ep1205 ep66 ep1204 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz497 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 493766509) qz16)

noncomputable def ep1207 := @Enclosure.Real.IsNear.cos_image qz211 qz497 Bool.false 493766509 1048576 381 524288 Bool.false 986270 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz211 Bool.false 53017775269675812067 112589990684262400 3613250002879080959 4980075000000000000000 493766509 1048576 381 524288 (ep1202 rfl) rfl) (Enclosure.sfrac_false_div 493766509 1048576) (BSN.cos_reduce3 qz497 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 185016459014706642812928) qz19) 226375608064910080 72057594037927936 Bool.false 986270 1048576 74 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q3 493766509 1048576 226375608064910080 72057594037927936 74 185016459014706642812928 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 986270 1048576 185016459014706642812928 151115727451828646838272 2629242018 2147483648 398796 398406 (ep1206 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1208 := nat_lit 1709745545832127581797908059794583811279884172338753966589620170618473366323456

noncomputable def ep1209 := nat_lit 5124669180061442552088651461788395758391175741720565178216226115274029231145216

noncomputable def ep1210 := BSN.cos_dyadic_bound_f 2629242018 2147483648 3 2 1048576 398796 ep1208 ep57 ep1204 ep1209 ep60 ep1204 356065 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2629242018) qz281 0 2 ep1208 ep57 ep1204 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2629242018) qz282 0 2 ep1209 ep60 ep1204 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1211 := @Enclosure.Real.IsNear.sin_image qz211 qz497 Bool.false 493766509 1048576 381 524288 Bool.true 356065 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz211 Bool.false 53017775269675812067 112589990684262400 3613250002879080959 4980075000000000000000 493766509 1048576 381 524288 (ep1202 rfl) rfl) (Enclosure.sfrac_false_div 493766509 1048576) (BSN.sin_reduce3 qz497 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 185016459014706642812928) qz19) 226375608064910080 72057594037927936 Bool.false 356065 1048576 74 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q3 493766509 1048576 226375608064910080 72057594037927936 74 185016459014706642812928 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 356065 1048576 185016459014706642812928 151115727451828646838272 2629242018 2147483648 398796 398406 (ep1210 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1212 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz128 (Real.cos qz211)) (@HMul.hMul Real Real Real qz0 qz128 (@Neg.neg Real Real.instNeg (Real.sin qz211))) Bool.false 101409760805 549755813888 5271226070923 36504335797977088 Bool.false 73222274795 1099511627776 10500605899641 73008671595954176 (@Enclosure.Real.IsNear.mulLit_ff qz128 (Real.cos qz211) 205643 1048576 1 1048576 493135 524288 76420631 104439742464 101409760805 549755813888 5271226070923 36504335797977088 qz434 (@Enclosure.Real.IsNear.recentre' (Real.cos qz211) Bool.false 986270 1048576 76420631 104439742464 493135 524288 76420631 104439742464 (ep1207 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz128 (@Neg.neg Real Real.instNeg (Real.sin qz211)) 205643 1048576 1 1048576 356065 1048576 76420631 104439742464 73222274795 1099511627776 10500605899641 73008671595954176 qz434 (@Enclosure.Real.IsNear.neg (Real.sin qz211) Bool.true 356065 1048576 76420631 104439742464 (@Enclosure.Real.IsNear.recentre' (Real.sin qz211) Bool.true 356065 1048576 76420631 104439742464 356065 1048576 76420631 104439742464 (ep1211 rfl rfl) rfl)) rfl)

noncomputable def ep1213 := @ep1188 101409760805 549755813888 5271226070923 36504335797977088 Bool.false 73222274795 1099511627776 10500605899641 73008671595954176 Bool.false 649882919660284134031360 2364260288815 549755813888 13685056919017 2380717552041984 Bool.true 111288884694097495851008 202433301991 1099511627776 54726466100575 9522870208167936 (ep1189 (BSN.head_sum_c_succ qz149 25 26 rfl rfl) (ep1200 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1201 ep1212) rfl rfl

noncomputable abbrev qz212 := (@HMul.hMul Real Real Real qz267 qz452 qz584)

noncomputable def ep1214 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz424 qz150) (Complex.mk (@HMul.hMul Real Real Real qz0 qz130 (Real.cos qz212)) (@HMul.hMul Real Real Real qz0 qz130 (@Neg.neg Real Real.instNeg (Real.sin qz212)))) Bool.false 81585115911 1099511627776 30923902253267 219026014787862528 Bool.false 97620468049 549755813888 15518047986253 109513007393931264 (BSN.cpow_neg_s_mk qz152 144530 1000 27 qz153 rfl)

noncomputable def ep1215 := @Enclosure.Real.IsNear.mulLit_ff qz152 qz584 144530 1000 0 1 3710780868205815 1125899906842624 250000000199203 49800750000000000000 10726383177635728839 22517998136852480 3613250002879080959 4980075000000000000000 qz154 (BSN.isNear_log_sfrac 27 1 3710780868205815 1125899906842624 250000000199203 49800750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz436) Bool.false 62256572154556490711040 18889465931478580854784 1000000000796812 199203000000000000000 3710780868205815 1125899906842624 250000000199203 49800750000000000000 (BSN.log_rat_reduce_isNear 27 1 4 54 32 274332 524288 24973259072661432 36028797018963968 199203 1000000000000000 rfl rfl rfl rfl (ep612 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1216 := nat_lit 522022350087210518052011302408567056

noncomputable def ep1217 := BSN.sin_dyadic_bound_f 850006554 2147483648 2 1 1048576 398796 ep1216 ep180 ep1216 ep1216 ep181 ep1216 404289 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 850006554) qz285 0 1 ep1216 ep180 ep1216 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 850006554) qz286 0 1 ep1216 ep181 ep1216 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz498 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 499486139) qz16)

noncomputable def ep1218 := @Enclosure.Real.IsNear.cos_image qz212 qz498 Bool.false 499486139 1048576 381 524288 Bool.false 404289 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz212 Bool.false 10726383177635728839 22517998136852480 3613250002879080959 4980075000000000000000 499486139 1048576 381 524288 (ep1215 rfl) rfl) (Enclosure.sfrac_false_div 499486139 1048576) (BSN.cos_reduce3 qz498 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 59813893779929555795968) qz19) 226375608064910080 72057594037927936 Bool.false 404289 1048576 75 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q3 499486139 1048576 226375608064910080 72057594037927936 75 59813893779929555795968 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 404289 1048576 59813893779929555795968 151115727451828646838272 850006554 2147483648 398796 398406 (ep1217 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1219 := BSN.cos_dyadic_bound_f 850006554 2147483648 2 1 1048576 398796 ep1216 ep184 ep1216 ep1216 ep185 ep1216 967502 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 850006554) qz281 0 1 ep1216 ep184 ep1216 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 850006554) qz282 0 1 ep1216 ep185 ep1216 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1220 := @Enclosure.Real.IsNear.sin_image qz212 qz498 Bool.false 499486139 1048576 381 524288 Bool.true 967502 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz212 Bool.false 10726383177635728839 22517998136852480 3613250002879080959 4980075000000000000000 499486139 1048576 381 524288 (ep1215 rfl) rfl) (Enclosure.sfrac_false_div 499486139 1048576) (BSN.sin_reduce3 qz498 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 59813893779929555795968) qz19) 226375608064910080 72057594037927936 Bool.false 967502 1048576 75 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q3 499486139 1048576 226375608064910080 72057594037927936 75 59813893779929555795968 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 967502 1048576 59813893779929555795968 151115727451828646838272 850006554 2147483648 398796 398406 (ep1219 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1221 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz130 (Real.cos qz212)) (@HMul.hMul Real Real Real qz0 qz130 (@Neg.neg Real Real.instNeg (Real.sin qz212))) Bool.false 81585115911 1099511627776 30923902253267 219026014787862528 Bool.false 97620468049 549755813888 15518047986253 109513007393931264 (@Enclosure.Real.IsNear.mulLit_ff qz130 (Real.cos qz212) 201799 1048576 1 1048576 404289 1048576 76420631 104439742464 81585115911 1099511627776 30923902253267 219026014787862528 qz438 (@Enclosure.Real.IsNear.recentre' (Real.cos qz212) Bool.false 404289 1048576 76420631 104439742464 404289 1048576 76420631 104439742464 (ep1218 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz130 (@Neg.neg Real Real.instNeg (Real.sin qz212)) 201799 1048576 1 1048576 483751 524288 76420631 104439742464 97620468049 549755813888 15518047986253 109513007393931264 qz438 (@Enclosure.Real.IsNear.neg (Real.sin qz212) Bool.true 483751 524288 76420631 104439742464 (@Enclosure.Real.IsNear.recentre' (Real.sin qz212) Bool.true 967502 1048576 76420631 104439742464 483751 524288 76420631 104439742464 (ep1220 rfl rfl) rfl)) rfl)

noncomputable def ep1222 := @ep1185 81585115911 1099511627776 30923902253267 219026014787862528 Bool.false 97620468049 549755813888 15518047986253 109513007393931264 Bool.false ep1186 4810105693541 1099511627776 1289949138802831 219026014787862528 Bool.true 3954044965286506921984 7192365893 1099511627776 1289744816285731 219026014787862528 (ep1187 (BSN.head_sum_c_succ qz149 26 27 rfl rfl) (ep1213 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1214 ep1221) rfl rfl

noncomputable abbrev qz213 := (@HMul.hMul Real Real Real qz267 qz452 qz585)

noncomputable def ep1223 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz423 qz150) (Complex.mk (@HMul.hMul Real Real Real qz0 qz132 (Real.cos qz213)) (@HMul.hMul Real Real Real qz0 qz132 (@Neg.neg Real Real.instNeg (Real.sin qz213)))) Bool.true 7663557699 68719476736 3801362035609 27378251848482816 Bool.false 10484606167 68719476736 3807033743425 27378251848482816 (BSN.cpow_neg_s_mk qz152 144530 1000 28 qz153 rfl)

noncomputable def ep1224 := @Enclosure.Real.IsNear.mulLit_ff qz152 qz585 144530 1000 0 1 3751726938922231 1125899906842624 250000000199203 49800750000000000000 54223709448243004643 112589990684262400 3613250002879080959 4980075000000000000000 qz154 (BSN.isNear_log_sfrac 28 1 3751726938922231 1125899906842624 250000000199203 49800750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz439) Bool.false 62943533227317076688896 18889465931478580854784 1000000000796812 199203000000000000000 3751726938922231 1125899906842624 250000000199203 49800750000000000000 (BSN.log_rat_reduce_isNear 28 1 4 56 32 293399 524288 24973259072661432 36028797018963968 199203 1000000000000000 rfl rfl rfl rfl (ep622 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1225 := nat_lit 592567766868779640312269871447670591536016669796797170766314172271348406091776

noncomputable def ep1226 := nat_lit 274799326653203750103953218192135871210844079554343980549877793355003396096

noncomputable def ep1227 := nat_lit 1777153701953032513436601707906627502865628321231282824337842761227335211483136

noncomputable def ep1228 := BSN.cos_dyadic_bound_f 2017794612 2147483648 3 2 1048576 398796 ep1225 ep57 ep1226 ep1227 ep60 ep1226 618768 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2017794612) qz281 0 2 ep1225 ep57 ep1226 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2017794612) qz282 0 2 ep1227 ep60 ep1226 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz499 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 252498823) qz37)

noncomputable def ep1229 := @Enclosure.Real.IsNear.cos_image qz213 qz499 Bool.false 252498823 524288 381 524288 Bool.true 618768 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz213 Bool.false 54223709448243004643 112589990684262400 3613250002879080959 4980075000000000000000 252498823 524288 381 524288 (ep1224 rfl) rfl) (Enclosure.sfrac_false_div 252498823 524288) (BSN.cos_reduce2 qz499 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 70994836429756134588416) qz38) 226375608064910080 72057594037927936 Bool.false 618768 1048576 76 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q2 252498823 524288 226375608064910080 72057594037927936 76 70994836429756134588416 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 618768 1048576 70994836429756134588416 75557863725914323419136 2017794612 2147483648 398796 398406 (ep1228 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1230 := nat_lit 1066402140902480789562002606031253356067861330370591432194925607853743128248320

noncomputable def ep1231 := nat_lit 2792513074882392118971743282014304855433866879603699098827724408903895330390016

noncomputable def ep1232 := BSN.sin_dyadic_bound_f 2017794612 2147483648 3 2 1048576 398796 ep1230 ep64 ep1226 ep1231 ep66 ep1226 846544 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2017794612) qz285 0 2 ep1230 ep64 ep1226 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2017794612) qz286 0 2 ep1231 ep66 ep1226 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1233 := @Enclosure.Real.IsNear.sin_image qz213 qz499 Bool.false 252498823 524288 381 524288 Bool.true 846544 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz213 Bool.false 54223709448243004643 112589990684262400 3613250002879080959 4980075000000000000000 252498823 524288 381 524288 (ep1224 rfl) rfl) (Enclosure.sfrac_false_div 252498823 524288) (BSN.sin_reduce2 qz499 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 70994836429756134588416) qz38) 226375608064910080 72057594037927936 Bool.false 846544 1048576 76 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q2 252498823 524288 226375608064910080 72057594037927936 76 70994836429756134588416 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 846544 1048576 70994836429756134588416 75557863725914323419136 2017794612 2147483648 398796 398406 (ep1232 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1234 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz132 (Real.cos qz213)) (@HMul.hMul Real Real Real qz0 qz132 (@Neg.neg Real Real.instNeg (Real.sin qz213))) Bool.true 7663557699 68719476736 3801362035609 27378251848482816 Bool.false 10484606167 68719476736 3807033743425 27378251848482816 (@Enclosure.Real.IsNear.mulLit_ft qz132 (Real.cos qz213) 198163 1048576 1 1048576 38673 65536 76420631 104439742464 7663557699 68719476736 3801362035609 27378251848482816 qz441 (@Enclosure.Real.IsNear.recentre' (Real.cos qz213) Bool.true 618768 1048576 76420631 104439742464 38673 65536 76420631 104439742464 (ep1229 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz132 (@Neg.neg Real Real.instNeg (Real.sin qz213)) 198163 1048576 1 1048576 52909 65536 76420631 104439742464 10484606167 68719476736 3807033743425 27378251848482816 qz441 (@Enclosure.Real.IsNear.neg (Real.sin qz213) Bool.true 52909 65536 76420631 104439742464 (@Enclosure.Real.IsNear.recentre' (Real.sin qz213) Bool.true 846544 1048576 76420631 104439742464 52909 65536 76420631 104439742464 (ep1233 rfl rfl) rfl)) rfl)

noncomputable def ep1235 := @ep1183 7663557699 68719476736 3801362035609 27378251848482816 Bool.false 10484606167 68719476736 3807033743425 27378251848482816 Bool.false 322121775504809107914752 4687488770357 1099511627776 440120011695901 73008671595954176 Bool.false 11033690772607644729344 160561332779 1099511627776 440067028744377 73008671595954176 (ep1184 (BSN.head_sum_c_succ qz149 27 28 rfl rfl) (ep1222 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1223 ep1234) rfl rfl

noncomputable def ep1236 := @Enclosure.Complex.IsNear.mul qz208 (@HAdd.hAdd Complex Complex Complex qz4 qz209 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz81 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz81 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz81 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz81 2 k) 1))))) Bool.true 42025661140926689799699 532854962140281181306880 ep1176 ep1052 Bool.true

noncomputable def ep1237 := nat_lit 2181291152529458997016343

noncomputable abbrev qz214 := (Complex.re qz495)

noncomputable abbrev qz215 := (Complex.im qz495)

noncomputable def ep1238 := @Enclosure.Real.IsNear.subLit_tt_n (@HMul.hMul Real Real Real qz0 qz214 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz209 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz81 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz81 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz81 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz81 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz215 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz209 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz81 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz81 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz81 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz81 2 k) 1))))))) 4772848568362547939085 53285496214028118130688 ep1237

noncomputable def ep1239 := nat_lit 31843892106969129647962324992

noncomputable def ep1240 := nat_lit 46529441156113700002113697

noncomputable def ep1241 := nat_lit 2239358207616877732805623662688801173025062912

noncomputable def ep1242 := @Enclosure.Real.IsNear.mulLit_tf qz214 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz209 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz81 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz81 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz81 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz81 2 k) 1)))))) 196677143055 1099511627776 29961849540223 219026014787862528 72802286441

noncomputable abbrev qz500 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) qz595 (Real.log (Enclosure.sfrac Bool.false 29 1)))

noncomputable abbrev qz216 := (Real.cos qz500)

noncomputable abbrev qz217 := (Real.sin qz500)

noncomputable abbrev qz601 := (@Neg.neg Real Real.instNeg qz217)

noncomputable def ep1243 := @Enclosure.Complex.IsNear.of_eq qz208 (Complex.mk (@HMul.hMul Real Real Real qz0 qz136 qz216) (@HMul.hMul Real Real Real qz0 qz136 qz601)) Bool.true 196677143055 1099511627776 29961849540223 219026014787862528 Bool.true 54816750945 1099511627776 29816719397761 219026014787862528 (BSN.cpow_neg_s_mk qz152 144530 1000 29 qz153 rfl)

noncomputable def ep1244 := @Enclosure.Real.IsNear.mulLit_ff qz152 qz139 144530 1000 0 1 3791236343078135 1125899906842624 250000000199203 49800750000000000000 10958947773301657031 22517998136852480 3613250002879080959 4980075000000000000000 qz154 (BSN.isNear_log_sfrac 29 1 3791236343078135 1125899906842624 250000000199203 49800750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz446 Bool.false 63606391034871975772160 18889465931478580854784 1000000000796812 199203000000000000000 3791236343078135 1125899906842624 250000000199203 49800750000000000000 (BSN.log_rat_reduce_isNear 29 1 4 58 32 311797 524288 24973259072661432 36028797018963968 199203 1000000000000000 rfl rfl rfl rfl (ep643 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1245 := nat_lit 3897977403596259163462750066172215390806997589679156930769600462216203815004705

noncomputable def ep1246 := nat_lit 3666559437780966776277086679573426808536884110095756914808190541096331422241

noncomputable def ep1247 := nat_lit 10203052103662366720002753937731730951566410160600494069391645092547330216995361

noncomputable def ep1248 := BSN.sin_dyadic_bound_f 2789538381 2147483648 3 2 1048576 398796 ep1245 ep64 ep1246 ep1247 ep66 ep1246 1010077 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2789538381) qz285 0 2 ep1245 ep64 ep1246 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2789538381) qz286 0 2 ep1247 ep66 ep1246 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz218 := qz500

noncomputable abbrev qz501 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 127578943) qz32)

noncomputable def ep1249 := @Enclosure.Real.IsNear.cos_image qz218 qz501 Bool.false 127578943 262144 381 524288 Bool.true 1010077 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 10958947773301657031 22517998136852480 3613250002879080959 4980075000000000000000 127578943 262144 381 524288 (ep1244 rfl) rfl) (Enclosure.sfrac_false_div 127578943 262144) (BSN.cos_reduce1 qz501 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 49074078188449474543616) qz302) 226375608064910080 72057594037927936 Bool.false 1010077 1048576 77 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q1 127578943 262144 226375608064910080 72057594037927936 77 49074078188449474543616 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1010077 1048576 49074078188449474543616 37778931862957161709568 2789538381 2147483648 398796 398406 (ep1248 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1250 := nat_lit 2167172583970268853824317630842152295696570609426240853500803897027267155634721

noncomputable def ep1251 := nat_lit 6494184633035244627920398719167310033472638060058531046672795309999608804059681

noncomputable def ep1252 := BSN.cos_dyadic_bound_f 2789538381 2147483648 3 2 1048576 398796 ep1250 ep57 ep1246 ep1251 ep60 ep1246 281523 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2789538381) qz281 0 2 ep1250 ep57 ep1246 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2789538381) qz282 0 2 ep1251 ep60 ep1246 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1253 := @Enclosure.Real.IsNear.sin_image qz218 qz501 Bool.false 127578943 262144 381 524288 Bool.false 281523 1048576 1 199203 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 10958947773301657031 22517998136852480 3613250002879080959 4980075000000000000000 127578943 262144 381 524288 (ep1244 rfl) rfl) (Enclosure.sfrac_false_div 127578943 262144) (BSN.sin_reduce1 qz501 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 49074078188449474543616) qz302) 226375608064910080 72057594037927936 Bool.false 281523 1048576 77 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q1 127578943 262144 226375608064910080 72057594037927936 77 49074078188449474543616 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 281523 1048576 49074078188449474543616 37778931862957161709568 2789538381 2147483648 398796 398406 (ep1252 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1254 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz136 qz216) (@HMul.hMul Real Real Real qz0 qz136 qz601) Bool.true 196677143055 1099511627776 29961849540223 219026014787862528 Bool.true 54816750945 1099511627776 29816719397761 219026014787862528 (@Enclosure.Real.IsNear.mulLit_ft qz136 qz216 194715 1048576 1 1048576 1010077 1048576 76420631 104439742464 196677143055 1099511627776 29961849540223 219026014787862528 qz448 (@Enclosure.Real.IsNear.recentre' qz216 Bool.true 1010077 1048576 76420631 104439742464 1010077 1048576 76420631 104439742464 (ep1249 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz136 qz601 194715 1048576 1 1048576 281523 1048576 76420631 104439742464 54816750945 1099511627776 29816719397761 219026014787862528 qz448 (@Enclosure.Real.IsNear.neg qz217 Bool.false 281523 1048576 76420631 104439742464 (@Enclosure.Real.IsNear.recentre' qz217 Bool.false 281523 1048576 76420631 104439742464 281523 1048576 76420631 104439742464 (ep1253 rfl rfl) rfl)) rfl)

noncomputable def ep1255 := @ep1242 145388629464 0 1 4772848568362547939085 53285496214028118130688 ep1237 ep1239 (@Enclosure.Complex.IsNear.re_isNear qz208 Bool.true 196677143055 1099511627776 29961849540223 219026014787862528 Bool.true 54816750945 1099511627776 29816719397761 219026014787862528 (ep1243 ep1254))

noncomputable def ep1256 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz209 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz81 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz81 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz81 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz81 2 k) 1))))) Bool.false 72802286441 145388629464 0 1 Bool.false

noncomputable def ep1257 := @Enclosure.Complex.IsNear.addLitP qz209 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz81 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz81 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz81 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz81 2 k) 1)))) Bool.false 208601709 417783418 0 1 Bool.true 41913700

noncomputable def ep1258 := @ep1257 208891709 0 1 Bool.false 1 696 0 1 Bool.false 14453 34800 0 1 Bool.false 145604572882 72802286441 145388629464 0 1 Bool.false 1560515110177 1560515110177 7269431473200 0 1

noncomputable abbrev qz219 := (@HDiv.hDiv Complex Complex Complex qz397 qz421 (@HSub.hSub Complex Complex Complex qz389 qz450 (1 : Complex)))

noncomputable def ep1259 := @Enclosure.Complex.IsNear.addLitP qz219 qz99 Bool.true 58000000 83556683600 0 1 Bool.true 16765480000 83556683600 0 1

noncomputable def ep1260 := @Enclosure.Complex.IsNear.of_eq qz219 (Complex.mk (Enclosure.sfrac Bool.true 58000000 83556683600) (Enclosure.sfrac Bool.true 16765480000 83556683600)) Bool.true 58000000 83556683600 0 1 Bool.true 16765480000 83556683600 0 1

noncomputable def ep1261 := @ep1259 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 83440683600 208601709 417783418 0 1 Bool.true 16765480000 41913700 208891709 0 1 (ep1260 (BSN.N_div_s_sub_one_mk qz152 144530 1000 29 qz153 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 58000000 83556683600) (Enclosure.sfrac Bool.true 16765480000 83556683600) Bool.true 58000000 83556683600 0 1 Bool.true 16765480000 83556683600 0 1 (Enclosure.Real.IsNear.const Bool.true 58000000 83556683600) (Enclosure.Real.IsNear.const Bool.true 16765480000 83556683600))) qz100 rfl

noncomputable def ep1262 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz81 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz81 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz81 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz81 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz81 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz81 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz81 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz81 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1))) qz143)) Bool.false 1 696 0 1

noncomputable def ep1263 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz81 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz81 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz81 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz81 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1))) qz143) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1264 := @ep1263 0 1 0 1 Bool.false 1 696 0 1 Bool.false 14453 34800 0 1 Bool.false 1 1 696 0 1 Bool.false 14453 14453 34800 0

noncomputable def ep1265 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz81 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz81 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz81 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz81 2 k) 1)))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1266 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1))) qz143 Bool.false 1 696 0 1 Bool.false 14453 34800 0 1

noncomputable def ep1267 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1)))) qz144) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1)))) qz145) 1 696 0 1 0 1 0

noncomputable def ep1268 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1)))) qz144 1 24 0 1 1 29 0 1 1

noncomputable def ep1269 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz142)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz142)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep1270 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz142)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep1271 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1)) qz149 Bool.false 1 2 0 1 Bool.false 144530 1000 0 1 (BSN.ascPochhammer_one_eval qz149)

noncomputable def ep1272 := ep1271 (@Enclosure.Complex.IsNear.of_eq qz149 (Complex.mk qz94 qz152) Bool.false 1 2 0 1 Bool.false 144530 1000 0 1 (BSN.s_crit_mk qz152 Bool.false 144530 1000 qz153) (@Enclosure.Complex.IsNear.mk qz94 qz152 Bool.false 1 2 0 1 Bool.false 144530 1000 0 1 qz402 qz154))

noncomputable def ep1273 := @ep1270 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz142) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep670) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 144530 1000 0 1 ep1272)

noncomputable def ep1274 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz142)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 144530 1000 0 1 0 1 0

noncomputable def ep1275 := @ep1274 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz142) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep670) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 144530 1000 0 1 ep1272)

noncomputable def ep1276 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz142)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz142)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1)))) 14453 1200 0 1 0 1 0 1 14453

noncomputable def ep1277 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz142)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 144530 1000 0 1 14453 1200 0

noncomputable def ep1278 := @ep1277 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz142) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep670) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 144530 1000 0 1 ep1272)

noncomputable def ep1279 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz142)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep1280 := @ep1279 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz142) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep670) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 144530 1000 0 1 ep1272)

noncomputable def ep1281 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 14453 1200 0 1 (@ep1269 1 24 0 1 (ep1273 rfl) (ep1275 rfl) rfl rfl) (@ep1276 14453 1200 0 1 (ep1278 rfl) (ep1280 rfl) rfl rfl)

noncomputable def ep1282 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 14453 1200 0 1 ep1281

noncomputable def ep1283 := @ep1268 696 0 1 ep1282 qz146

noncomputable def ep1284 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1)))) qz145 14453 1200 0 1 0 1 0 1 0

noncomputable def ep1285 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 14453 1200 0 1 ep1281

noncomputable def ep1286 := @ep1284 1 0 1 ep1285 qz147

noncomputable def ep1287 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1)))) qz145) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1)))) qz144) 0 1 0 1 14453 34800 0

noncomputable def ep1288 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1)))) qz145 1 24 0 1 0 1 0 1 0

noncomputable def ep1289 := @ep1288 1 0 1 ep1282 qz147

noncomputable def ep1290 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz142) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1)))) qz144 14453 1200 0 1 1 29 0 1 14453

noncomputable def ep1291 := @ep1290 34800 0 1 ep1285 qz146

noncomputable def ep1292 := @ep1264 1 (@ep1265 0 1 0 1 (BSN.bern_sum_base qz149 29) qz115) (ep1266 (@ep1267 1 1 1 696 0 1 (ep1283 rfl) (ep1286 rfl) rfl rfl) (@ep1287 1 14453 14453 34800 0 1 (ep1289 rfl) (ep1291 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep1293 := ep1258 (ep1261 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep1262 Bool.false 14453 34800 0 1 (BSN.bern_sum_succ qz149 29 0 1 1 rfl rfl) (ep1292 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep1294 := @Enclosure.Real.IsNear.mulLit_tf qz215 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz209 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz81 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz81 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz81 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz81 2 k) 1)))))) 54816750945 1099511627776 29816719397761 219026014787862528 1560515110177

noncomputable def ep1295 := @ep1294 7269431473200 0 1 5702824542698789591151 532854962140281181306880 ep1240 ep1052 (@Enclosure.Complex.IsNear.im_isNear qz208 Bool.true 196677143055 1099511627776 29961849540223 219026014787862528 Bool.true 54816750945 1099511627776 29816719397761 219026014787862528 (ep1243 ep1254))

noncomputable def ep1296 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz209 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz81 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz81 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz81 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz81 2 k) 1))))) Bool.false 72802286441 145388629464 0 1 Bool.false

noncomputable def ep1297 := nat_lit 46755918936367791638149471

noncomputable def ep1298 := @Enclosure.Real.IsNear.addLit_tt (@HMul.hMul Real Real Real qz0 qz214 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz209 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz81 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz81 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz81 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz81 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz215 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz209 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz81 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz81 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz81 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz81 2 k) 1))))))) 20461176904251394358049 532854962140281181306880 ep1297

noncomputable def ep1299 := nat_lit 2170725346326717336058601

noncomputable def ep1300 := nat_lit 1799120459692353252340943729899257853391142912

noncomputable def ep1301 := @Enclosure.Real.IsNear.mulLit_tf qz214 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz209 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz81 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz81 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz81 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz81 2 k) 1)))))) 196677143055 1099511627776 29961849540223 219026014787862528 1560515110177

noncomputable def ep1302 := @ep1301 7269431473200 0 1 20461176904251394358049 532854962140281181306880 ep1297 ep1052 (@Enclosure.Complex.IsNear.re_isNear qz208 Bool.true 196677143055 1099511627776 29961849540223 219026014787862528 Bool.true 54816750945 1099511627776 29816719397761 219026014787862528 (ep1243 ep1254))

noncomputable def ep1303 := @Enclosure.Real.IsNear.mulLit_tf qz215 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz209 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz81 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz81 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz81 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz81 2 k) 1)))))) 54816750945 1099511627776 29816719397761 219026014787862528 72802286441

noncomputable def ep1304 := @ep1303 145388629464 0 1 1330261601354282478915 53285496214028118130688 ep1299 ep1239 (@Enclosure.Complex.IsNear.im_isNear qz208 Bool.true 196677143055 1099511627776 29961849540223 219026014787862528 Bool.true 54816750945 1099511627776 29816719397761 219026014787862528 (ep1243 ep1254))

noncomputable abbrev qz602 := (ep1293 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep1305 := @ep1236 33763792917794219147199 532854962140281181306880 ep1177 ep1052 (@ep1238 ep1239 5702824542698789591151 532854962140281181306880 ep1240 ep1052 ep1241 42025661140926689799699 532854962140281181306880 ep1176 ep1052 (ep1255 (@ep1256 1560515110177 7269431473200 0 1 qz602) rfl) (ep1295 (@ep1296 1560515110177 7269431473200 0 1 qz602) rfl) rfl rfl) (@ep1298 ep1052 1330261601354282478915 53285496214028118130688 ep1299 ep1239 ep1300 33763792917794219147199 532854962140281181306880 ep1177 ep1052 (ep1302 (@ep1296 1560515110177 7269431473200 0 1 qz602) rfl) (ep1304 (@ep1256 1560515110177 7269431473200 0 1 qz602) rfl) rfl rfl)

noncomputable def ep1306 := @ep1180 ep1173 ep1052 (@ep1181 73008671595954176 (BSN.head_sum_c_eq qz149 29) (ep1182 (BSN.head_sum_c_succ qz149 28 29 rfl rfl) (ep1235 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep1305 rfl rfl rfl

noncomputable def ep1307 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz149 1 29) Bool.false ep1050 532854962140281181306880 ep1051 ep1052 Bool.false 44048847474379208854321 532854962140281181306880 ep1173 ep1052 (@ep1174 ep1052 Bool.false 44048847474379208854321 532854962140281181306880 ep1173 ep1052 (BSN.zetaApproximant_eq_folded' qz149 1 29 rfl) (ep1306 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep1308 := @Enclosure.Real.IsNear.mulLit_ff (Real.sin (@HSub.hSub Real Real Real qz392 (Complex.im (@HSub.hSub Complex Complex Complex qz74 qz179 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz180 (@Nat.cast Complex Complex.instNatCast j))))) qz181)) (Complex.im (zetaApproximant qz149 1 29)) 3 4096 79733761

noncomputable def ep1309 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz392 (Complex.im (@HSub.hSub Complex Complex Complex qz74 qz179 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz180 (@Nat.cast Complex Complex.instNatCast j))))) qz181)) Bool.false 768 1048576 79733761

noncomputable def ep1310 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz392 (Complex.im (@HSub.hSub Complex Complex Complex qz74 qz179 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz180 (@Nat.cast Complex Complex.instNatCast j))))) qz181) qz479 Bool.false 161414965 1048576 395

noncomputable def ep1311 := nat_lit 4634301046356001311640505233026349453097798502561139401474719220496388163690625

noncomputable def ep1312 := nat_lit 13869498644844069705508059321618415038988767476142743281834707662384294365290625

noncomputable def ep1313 := BSN.cos_dyadic_bound_f 3371683985 2147483648 3 2 1048576 398796 ep1311 ep57 ep1169 ep1312 ep60 ep1169 768 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3371683985) qz281 0 2 ep1311 ep57 ep1169 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3371683985) qz282 0 2 ep1312 ep60 ep1169 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1314 := @ep1310 1048576 Bool.false 768 1048576 1 199203 (@ep1057 161414965 1048576 395 1048576 ep1167 rfl) (Enclosure.sfrac_false_div 161414965 1048576) (BSN.sin_reduce1 qz479 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 237261167812391175454720) qz19) 226375608064910080 72057594037927936 Bool.false 768 1048576 24 1000000000000000 398406 199203 (BSN.sin_reduce_arg_pos_rat_q1 161414965 1048576 226375608064910080 72057594037927936 24 237261167812391175454720 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 768 1048576 237261167812391175454720 151115727451828646838272 3371683985 2147483648 398796 398406 (ep1313 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1315 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz149 1 29) Bool.false ep1050 532854962140281181306880 ep1051 ep1052 Bool.false 44048847474379208854321 532854962140281181306880 ep1173 ep1052 (@ep1174 ep1052 Bool.false 44048847474379208854321 532854962140281181306880 ep1173 ep1052 (BSN.zetaApproximant_eq_folded' qz149 1 29 rfl) (ep1306 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow50.d15 : Enclosure.Real.IsNear (hardyZApproximantEM 1 29 qz152) Bool.true ep1035 ep1036 ep1037 ep1038 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 29 qz152) ep1039 Bool.true ep1035 ep1036 ep1037 ep1038 (@Eq.refl Real ep1039) (@ep1040 Bool.true ep1035 ep1036 ep1037 ep1038 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz392 (Complex.im (@HSub.hSub Complex Complex Complex qz74 qz179 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz180 (@Nat.cast Complex Complex.instNatCast j))))) qz181) (zetaApproximant qz149 1 29)) (@ep1042 ep1043 ep1044 ep1038 132146542423137626562963 ep1045 ep1046 ep1047 ep1048 ep1035 ep1036 ep1037 ep1038 (@ep1049 208879484928 ep1050 532854962140281181306880 ep1051 ep1052 ep1041 ep1043 ep1044 ep1038 (@ep1053 208879484928 1048575 1048576 79733761 208879484928 (ep1172 rfl rfl) rfl) ep1307 rfl) (@ep1308 208879484928 44048847474379208854321 532854962140281181306880 ep1173 ep1052 132146542423137626562963 ep1045 ep1046 ep1047 (@ep1309 208879484928 3 4096 79733761 208879484928 (ep1314 rfl rfl) rfl) ep1315 rfl) rfl rfl))

theorem EMRow50.d16 : @Eq Nat (Nat.mul (BSN.factNat (Nat.succ (Nat.mul 2 1))) (Nat.pow 4 (Nat.mul 2 1))) 96 := @Eq.refl Nat 96

theorem EMRow50.d17 : @Eq Nat (Nat.mul (Nat.mul 2 1) (Nat.pow (Nat.succ (Nat.mul 4 2)) (Nat.mul 2 1))) 162 := @Eq.refl Nat 162

theorem EMRow50.d18 : @Eq Nat (BSN.factNat (Nat.mul 2 2)) 24 := @Eq.refl Nat 24

theorem EMRow50.d19 : @Eq Nat (Nat.pow 29 (Nat.succ (Nat.mul 2 3))) 17249876309 := @Eq.refl Nat 17249876309

noncomputable abbrev qz603 := (@HAdd.hAdd Complex Complex Complex qz609 qz608 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz502 := qz603

noncomputable abbrev qz220 := (@HDiv.hDiv Real Real Real qz270 (@Norm.norm Complex Complex.instNorm qz502) (@HAdd.hAdd Real Real Real qz412 (Complex.re qz271) qz547))

noncomputable abbrev qz221 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)

noncomputable abbrev qz222 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)))

noncomputable abbrev qz503 := (@HPow.hPow Complex Complex Complex qz536 qz581 (@HSub.hSub Complex Complex Complex qz572 qz537 qz543))

noncomputable abbrev qz223 := qz503

noncomputable def ep1316 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 29))) (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) 43335413623 1855425871872 177126677 1855425871872 5032993333947636525 4035225266123964416 660779127275

noncomputable def ep1317 := nat_lit 9513214200735219802951770963968

noncomputable def ep1318 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 29)) 26561 1769472 1 1769472 1631543 1048576 6607 1048576 43335413623 1855425871872

noncomputable abbrev qz224 := (@HMul.hMul Real Real Real qz267 (2 : Real) Real.pi)

noncomputable abbrev qz604 := (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid)))

noncomputable abbrev qz504 := (@Inv.inv Real Real.instInv (@HPow.hPow Real Nat Real qz604 qz224 2))

noncomputable def ep1319 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 96 162) qz504 96 162 0 1 26561 1048576 1 1048576 26561 1769472 1 1769472

noncomputable def ep1320 := nat_lit 781950621441006189802102638025

noncomputable def ep1321 := nat_lit 19807040628566084398385987584

noncomputable def ep1322 := nat_lit 26986075409044041160201671

noncomputable def ep1323 := nat_lit 1073741824000000000000000000000000000000

noncomputable abbrev qz505 := (@HPow.hPow Real Nat Real qz604 qz224 1)

noncomputable def ep1324 := @Enclosure.Real.IsNear.mulLit_ff qz505 qz224 884279719003555 140737488355328 1 500000000000000 884279719003555 140737488355328 1 500000000000000 ep1320 ep1321 ep1322 ep1323

noncomputable def ep1325 := ep1324 (@Enclosure.Real.IsNear.of_eq qz505 qz224 Bool.false 884279719003555 140737488355328 1 500000000000000 (BSN.pow_one_r qz224) (@Enclosure.Real.IsNear.of_eq qz224 qz268 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz269)) (@Enclosure.Real.IsNear.of_eq qz224 qz268 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz269) rfl

noncomputable abbrev qz506 := (@HPow.hPow Real Nat Real qz604 qz224 2)

noncomputable def ep1326 := @Enclosure.Real.IsNear.inv_image qz506 ep1320 ep1321 ep1322 ep1323 13280 13281 524288 (@Enclosure.Real.IsNear.of_eq qz506 (@HMul.hMul Real Real Real qz0 qz505 qz224) Bool.false ep1320 ep1321 ep1322 ep1323 (BSN.pow_succ_r qz224 1 2 rfl) ep1325) rfl rfl rfl

noncomputable def ep1327 := ep1319 (Enclosure.Real.IsNear.const Bool.false 96 162) (@Enclosure.Real.IsNear.recentre' qz504 Bool.false 26561 1048576 1 1048576 26561 1048576 1 1048576 (ep1326 rfl rfl rfl) rfl)

noncomputable def ep1328 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 29)) (Real.sqrt (@HAdd.hAdd Real Real Real qz412 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 29)) (Complex.re (zetaApproximant qz5 1 29))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 29)) (Complex.im (zetaApproximant qz5 1 29))))) Bool.false 1631543 1048576 6607 1048576

noncomputable def ep1329 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz412 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 29)) (Complex.re (zetaApproximant qz5 1 29))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 29)) (Complex.im (zetaApproximant qz5 1 29))))) Bool.false 1631543 1048576 6607 1048576

noncomputable def ep1330 := nat_lit 6896534990834814377343390621978710326957

noncomputable def ep1331 := nat_lit 2848569393897571539530919382135865344000

noncomputable def ep1332 := nat_lit 1406705926760610544815055720811633214763934313646098930450877

noncomputable def ep1333 := nat_lit 71752615440686498019009124505176547274151660478426775552000000

noncomputable def ep1334 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz412 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 29)) (Complex.re (zetaApproximant qz5 1 29))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 29)) (Complex.im (zetaApproximant qz5 1 29)))) ep1330 ep1331 ep1332 ep1333 812468 819075

noncomputable def ep1335 := nat_lit 10140446004657910811525869808752948503533033788781761

noncomputable def ep1336 := nat_lit 4195019382184156164341002136235386876711623720960000

noncomputable def ep1337 := nat_lit 69635661037136725473732636798839168815246553810718517233331

noncomputable def ep1338 := nat_lit 3699245951608726120091137085600213103911818940221113761792000

noncomputable def ep1339 := nat_lit 15914594610529718743805784746388784887331298664369

noncomputable def ep1340 := nat_lit 3248825085336595441324015408380661539155817154415406078653491

noncomputable def ep1341 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 29)) (Complex.re (zetaApproximant qz5 1 29))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 29)) (Complex.im (zetaApproximant qz5 1 29))) ep1335 ep1336 ep1337 ep1338 ep1339 ep1336 ep1340

noncomputable def ep1342 := nat_lit 4161651695559816885102529221300239741900796307748752982016000000

noncomputable def ep1343 := nat_lit 42606129566382599457021004676626114730331742253215543494345293388653952616126868283159970814151884800000

noncomputable def ep1344 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz5 1 29)) (Complex.re (zetaApproximant qz5 1 29)) ep424 ep425 ep426 ep427 ep424 ep425 ep426 ep427 ep1335

noncomputable def ep1345 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (zetaApproximant qz5 1 29)) (Complex.im (zetaApproximant qz5 1 29)) ep562 ep425 ep563 ep564 ep562 ep425 ep563 ep564 ep1339

noncomputable def ep1346 := @ep1316 4035225266123964416 ep1317 138435486598394633663 108951082185347039232 10418764854305737 108951082185347039232 (@ep1318 177126677 1855425871872 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) qz504) Bool.false 26561 1769472 1 1769472 (BSN.theta_err_eq 1 2 96 162 EMRow50.d16 EMRow50.d17 rfl) (ep1327 rfl)) (ep1328 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz5 1 29)) (@ep1329 1631543 1048576 6607 1048576 (@ep1334 524288 (@ep1341 ep1342 ep1343 ep1330 ep1331 ep1332 ep1333 (@ep1344 ep1336 ep1337 ep1338 ep710 ep710 rfl) (@ep1345 ep1336 ep1340 ep1342 ep718 ep718 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz225 := (@Norm.norm Complex Complex.instNorm qz502)

noncomputable abbrev qz605 := (Enclosure.sfrac Bool.false 2 7)

noncomputable def ep1347 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz225 qz605) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) Bool.false 5032993333947636525 4035225266123964416 660779127275 4035225266123964416 (BSN.zrb_shape_eq qz225 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) qz13 3)

noncomputable def ep1348 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz225 qz605) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) 149490205 3670016 1 3670016 33667713105 1099511627776 4195 1099511627776

noncomputable def ep1349 := @Enclosure.Real.IsNear.mulLit_ff qz225 qz605 149490205 1048576 1 1048576 2 7 0 1 149490205 3670016

noncomputable abbrev qz507 := (Complex.re qz603)

noncomputable abbrev qz508 := (Complex.im qz603)

noncomputable abbrev qz226 := (@HAdd.hAdd Real Real Real qz412 (@HMul.hMul Real Real Real qz267 qz507 qz507) (@HMul.hMul Real Real Real qz267 qz508 qz508))

noncomputable abbrev qz227 := qz502

noncomputable def ep1350 := @Enclosure.Real.IsNear.of_eq qz225 (Real.sqrt qz226) Bool.false 149490205 1048576 1 1048576 (BSN.norm_eq_sqrt_mul_add qz227)

noncomputable def ep1351 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz226) Bool.false 149490205 1048576 1 1048576 149490205

noncomputable def ep1352 := @Enclosure.Real.IsNear.sqrt_image qz226 5081192621 250000 0 1 74745102 74745103 524288

noncomputable abbrev qz228 := (@HMul.hMul Real Real Real qz267 qz507 qz507)

noncomputable abbrev qz229 := (@HMul.hMul Real Real Real qz267 qz508 qz508)

noncomputable def ep1353 := @Enclosure.Real.IsNear.addLit_ff qz228 qz229 49 4 0 1 5078130121 250000 0 1

noncomputable abbrev qz230 := qz507

noncomputable def ep1354 := @Enclosure.Real.IsNear.mulLit_ff qz230 qz230 7 2 0 1 7 2 0 1 49 4

noncomputable abbrev qz509 := (Enclosure.sfrac Bool.false 7 2)

noncomputable def ep1355 := @Enclosure.Complex.IsNear.of_eq qz227 (Complex.mk qz509 qz13) Bool.false 7 2 0 1 Bool.false 142522 1000 0 1 (BSN.s_add_nat_mk qz13 Bool.false 142522 1000 3 qz14)

noncomputable abbrev qz510 := (ep1355 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz13 Bool.false 7 2 0 1 Bool.false 142522 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz18))

noncomputable def ep1356 := @ep1354 0 1 (@Enclosure.Complex.IsNear.re_isNear qz227 Bool.false 7 2 0 1 Bool.false 142522 1000 0 1 qz510)

noncomputable def ep1357 := ep1356 (@Enclosure.Complex.IsNear.re_isNear qz227 Bool.false 7 2 0 1 Bool.false 142522 1000 0 1 qz510)

noncomputable abbrev qz231 := qz508

noncomputable def ep1358 := @Enclosure.Real.IsNear.mulLit_ff qz231 qz231 142522 1000 0 1 142522 1000 0 1 5078130121 250000

noncomputable def ep1359 := @ep1358 0 1 (@Enclosure.Complex.IsNear.im_isNear qz227 Bool.false 7 2 0 1 Bool.false 142522 1000 0 1 qz510)

noncomputable def ep1360 := ep1359 (@Enclosure.Complex.IsNear.im_isNear qz227 Bool.false 7 2 0 1 Bool.false 142522 1000 0 1 qz510)

noncomputable def ep1361 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Real.sqrt (@HAdd.hAdd Real Real Real qz412 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))))) Bool.false 33667713105 1099511627776

noncomputable def ep1362 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz412 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))))) Bool.false 33667713105 1099511627776

noncomputable def ep1363 := nat_lit 1233301892856078839436504382687567482345062751290174653982528484677

noncomputable def ep1364 := nat_lit 1315351473597812626383316349444654717690339288678400000000000000000000

noncomputable def ep1365 := nat_lit 103769348638463887359506765863039671180341987485610440596921458955892022385937967

noncomputable def ep1366 := nat_lit 444226421249239848473696668309913173766360153552353538497153160812953600000000000000000000

noncomputable def ep1367 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz412 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)))) ep1363 ep1364 ep1365 ep1366

noncomputable def ep1368 := nat_lit 133557432844501030933369894369408697316741007328397220749849052009

noncomputable def ep1369 := nat_lit 328837868399453156595829087361163679422584822169600000000000000000000

noncomputable def ep1370 := nat_lit 11676464840985103846921015298926818359775214716885014322868810037439031384273339

noncomputable def ep1371 := nat_lit 111056605312309962118424167077478293441590038388088384624288290203238400000000000000000000

noncomputable def ep1372 := nat_lit 699072161478074715703024805209932693078098721976585770983132276641

noncomputable def ep1373 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) ep1368 ep1369 ep1370 ep1371 ep1372

noncomputable def ep1374 := nat_lit 57063489274523471971822704667332397741241128618070383305446218806135896848844611

noncomputable def ep1375 := nat_lit 405556365539803730537186110034597865037070581293372177601401607047104297038485556511983758268172458805596603495219200000000000000000000

noncomputable def ep1376 := nat_lit 365455103733004433373686390998253

noncomputable def ep1377 := nat_lit 18133887294219437620592640000000000

noncomputable def ep1378 := nat_lit 869292706625547795913937268477387211

noncomputable def ep1379 := nat_lit 333251564605944441645974541796638720000000000

noncomputable def ep1380 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) ep1376 ep1377 ep1378 ep1379 ep1376 ep1377 ep1378

noncomputable def ep1381 := nat_lit 836105353097368176216869791688879

noncomputable def ep1382 := nat_lit 36267774588438875241185280000000000

noncomputable def ep1383 := nat_lit 1856889298098053802863168521108615613

noncomputable def ep1384 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223) Bool.false ep1376 ep1377 ep1378 ep1379 Bool.true ep1381 ep1382 ep1383

noncomputable def ep1385 := nat_lit 666503129211888883291949083593277440000000000

noncomputable def ep1386 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223 Bool.false ep1376 ep1377 ep1378 ep1379 Bool.true ep1381 ep1382 ep1383 ep1385

noncomputable def ep1387 := nat_lit 34202073819625657112081305217

noncomputable def ep1388 := nat_lit 48357032784585166988247040000000

noncomputable def ep1389 := nat_lit 1747007430459787489324184487615277

noncomputable def ep1390 := nat_lit 20439429295831259087619771896860508160000000

noncomputable def ep1391 := nat_lit 94570220353841013697679220113657

noncomputable def ep1392 := nat_lit 4533471823554859405148160000000000

noncomputable def ep1393 := nat_lit 9669302232982589498761993996062088489

noncomputable abbrev qz232 := (Complex.re qz503)

noncomputable abbrev qz233 := (Complex.im qz503)

noncomputable def ep1394 := @Enclosure.Real.IsNear.subLit_tt_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz232) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz233) ep1387 ep1388 ep1389 ep1390 ep1391 ep1392 ep1393

noncomputable def ep1395 := nat_lit 3832392992968361078928707230661345280000000000

noncomputable def ep1396 := nat_lit 4418081108127717107464912080432822741706006376826043105280000000

noncomputable def ep1397 := nat_lit 1208925819614629174706176

noncomputable def ep1398 := nat_lit 170328577465260492396831432473837568

noncomputable def ep1399 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz232 15234077863 120000000 0 1 6735308981719425477 ep1397 114677596252993989920779 ep1398 ep1387

noncomputable def ep1400 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) 15234077863 120000000 0 1 0 1 0 1 15234077863

noncomputable def ep1401 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 45702233589 500000 0 1 15234077863 120000000 0

noncomputable def ep1402 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (Complex.mk (Enclosure.sfrac Bool.true 1 720) qz10) Bool.true 1 720 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 2 1 30 24 Bool.true BSN.bern_real_2 EMRow50.d18 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 1 720) qz10 Bool.true 1 720 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.true 1 720) qz20)

noncomputable abbrev qz511 := (@HAdd.hAdd Complex Complex Complex qz535 qz534 qz544)

noncomputable abbrev qz234 := qz511

noncomputable def ep1403 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz73 (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) qz234) Bool.true 45702233589 500000 0 1 Bool.true 361770192865081 125000000 0 1

noncomputable abbrev qz235 := (Complex.re qz511)

noncomputable abbrev qz236 := (Complex.im qz511)

noncomputable def ep1404 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz235) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz236) 5077942621 100000 0 1 5078130121 125000 0 1

noncomputable def ep1405 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz235 5077942621 250000 0 1 5 2 0 1 5077942621 100000

noncomputable abbrev qz512 := (@HAdd.hAdd Complex Complex Complex qz535 qz534 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz237 := qz512

noncomputable def ep1406 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz73 (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz237) Bool.true 5077942621 250000 0 1 Bool.false 71261 250 0 1

noncomputable abbrev qz238 := (Complex.re qz512)

noncomputable abbrev qz239 := (Complex.im qz512)

noncomputable def ep1407 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz238) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz239) 3 4 0 1 5078130121 250000 0 1

noncomputable def ep1408 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz238 1 2 0 1 3 2 0 1 3 4

noncomputable def ep1409 := @ep1408 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 142522 1000 0 1 ep672)

noncomputable abbrev qz513 := (Enclosure.sfrac Bool.false 3 2)

noncomputable def ep1410 := @Enclosure.Complex.IsNear.of_eq qz237 (Complex.mk qz513 qz13) Bool.false 3 2 0 1 Bool.false 142522 1000 0 1 (BSN.s_add_nat_mk qz13 Bool.false 142522 1000 1 qz14)

noncomputable abbrev qz514 := (ep1410 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz13 Bool.false 3 2 0 1 Bool.false 142522 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz18))

noncomputable def ep1411 := ep1409 (@Enclosure.Complex.IsNear.re_isNear qz237 Bool.false 3 2 0 1 Bool.false 142522 1000 0 1 qz514)

noncomputable def ep1412 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz239 142522 1000 0 1 142522 1000 0 1 5078130121 250000

noncomputable def ep1413 := @ep1412 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 142522 1000 0 1 ep672)

noncomputable def ep1414 := ep1413 (@Enclosure.Complex.IsNear.im_isNear qz237 Bool.false 3 2 0 1 Bool.false 142522 1000 0 1 qz514)

noncomputable def ep1415 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz237 Bool.true 5077942621 250000 0 1 Bool.false 71261 250 0 1 (@ep1407 20311770484 5077942621 250000 0 1 (ep1411 rfl) (ep1414 rfl) rfl rfl)

noncomputable def ep1416 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz239) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz238) 71261 1000 0 1 213783 1000 0 1

noncomputable def ep1417 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz239 1 2 0 1 142522 1000 0 1 71261 1000

noncomputable def ep1418 := @ep1417 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 142522 1000 0 1 ep672)

noncomputable def ep1419 := ep1418 (@Enclosure.Complex.IsNear.im_isNear qz237 Bool.false 3 2 0 1 Bool.false 142522 1000 0 1 qz514)

noncomputable def ep1420 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz238 142522 1000 0 1 3 2 0 1 213783 1000

noncomputable def ep1421 := @ep1420 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 142522 1000 0 1 ep672)

noncomputable def ep1422 := ep1421 (@Enclosure.Complex.IsNear.re_isNear qz237 Bool.false 3 2 0 1 Bool.false 142522 1000 0 1 qz514)

noncomputable abbrev qz240 := (ep1406 (BSN.ascPochhammer_succ_eval_c 1 2 qz271 rfl) (ep1415 (@ep1416 285044000 71261 250 0 1 (ep1419 rfl) (ep1422 rfl) rfl rfl)))

noncomputable def ep1423 := @ep1405 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 5077942621 250000 0 1 Bool.false 71261 250 0 1 qz240)

noncomputable abbrev qz515 := (Enclosure.sfrac Bool.false 5 2)

noncomputable def ep1424 := @Enclosure.Complex.IsNear.of_eq qz234 (Complex.mk qz515 qz13) Bool.false 5 2 0 1 Bool.false 142522 1000 0 1 (BSN.s_add_nat_mk qz13 Bool.false 142522 1000 2 qz14)

noncomputable abbrev qz516 := (ep1424 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz13 Bool.false 5 2 0 1 Bool.false 142522 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz18))

noncomputable def ep1425 := ep1423 (@Enclosure.Complex.IsNear.re_isNear qz234 Bool.false 5 2 0 1 Bool.false 142522 1000 0 1 qz516)

noncomputable def ep1426 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz236 71261 250 0 1 142522 1000 0 1 5078130121 125000

noncomputable def ep1427 := @ep1426 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 5077942621 250000 0 1 Bool.false 71261 250 0 1 qz240)

noncomputable def ep1428 := ep1427 (@Enclosure.Complex.IsNear.im_isNear qz234 Bool.false 5 2 0 1 Bool.false 142522 1000 0 1 qz516)

noncomputable def ep1429 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) qz234 Bool.true 45702233589 500000 0 1 Bool.true 361770192865081 125000000 0 1 (@ep1404 1142555839725000 45702233589 500000 0 1 (ep1425 rfl) (ep1428 rfl) rfl rfl)

noncomputable def ep1430 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz236) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz235) 361859269115081 125000000 0 1 71261 100 0 1

noncomputable def ep1431 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz236 5077942621 250000 0 1 142522 1000 0 1 361859269115081 125000000

noncomputable def ep1432 := @ep1431 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 5077942621 250000 0 1 Bool.false 71261 250 0 1 qz240)

noncomputable def ep1433 := ep1432 (@Enclosure.Complex.IsNear.im_isNear qz234 Bool.false 5 2 0 1 Bool.false 142522 1000 0 1 qz516)

noncomputable def ep1434 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz235 71261 250 0 1 5 2 0 1 71261 100

noncomputable def ep1435 := @ep1434 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 5077942621 250000 0 1 Bool.false 71261 250 0 1 qz240)

noncomputable def ep1436 := ep1435 (@Enclosure.Complex.IsNear.re_isNear qz234 Bool.false 5 2 0 1 Bool.false 142522 1000 0 1 qz516)

noncomputable abbrev qz241 := (ep1403 (BSN.ascPochhammer_succ_eval_c 2 3 qz271 rfl) (ep1429 (@ep1430 36177019286508100 361770192865081 125000000 0 1 (ep1433 rfl) (ep1436 rfl) rfl rfl)))

noncomputable def ep1437 := @ep1401 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1402) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 45702233589 500000 0 1 Bool.true 361770192865081 125000000 0 1 qz241)

noncomputable def ep1438 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 361770192865081 125000000 0 1 0 1 0

noncomputable def ep1439 := @ep1438 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1402) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 45702233589 500000 0 1 Bool.true 361770192865081 125000000 0 1 qz241)

noncomputable def ep1440 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) 361770192865081 90000000000 0 1 0 1 0 1 361770192865081

noncomputable def ep1441 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 361770192865081 125000000 0 1 361770192865081 90000000000 0

noncomputable def ep1442 := @ep1441 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1402) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 45702233589 500000 0 1 Bool.true 361770192865081 125000000 0 1 qz241)

noncomputable def ep1443 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 45702233589 500000 0 1 0 1 0

noncomputable def ep1444 := @ep1443 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1402) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 45702233589 500000 0 1 Bool.true 361770192865081 125000000 0 1 qz241)

noncomputable def ep1445 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 15234077863 120000000 0 1 Bool.false 361770192865081 90000000000 0 1 (@ep1400 15234077863 120000000 0 1 (ep1437 rfl) (ep1439 rfl) rfl rfl) (@ep1440 361770192865081 90000000000 0 1 (ep1442 rfl) (ep1444 rfl) rfl rfl)

noncomputable def ep1446 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 15234077863 120000000 0 1 Bool.false 361770192865081 90000000000 0 1 ep1445

noncomputable def ep1447 := nat_lit 42582144366315123099207858118459392

noncomputable def ep1448 := @Enclosure.Complex.IsNear.re_isNear qz223 Bool.true 6735308981719425477 ep1397 114677596252993989920779 ep1398 Bool.true 784228957102970691 151115727451828646838272 26727747126996364825969 ep1447

noncomputable abbrev qz606 := (@Nat.cast Real Real.instNatCast 17249876309)

noncomputable abbrev qz242 := (@Inv.inv Real Real.instInv (Real.sqrt qz606))

noncomputable def ep1449 := @Enclosure.Complex.IsNear.of_eq qz223 (Complex.mk (@HMul.hMul Real Real Real qz0 qz242 qz137) (@HMul.hMul Real Real Real qz0 qz242 qz586)) Bool.true 6735308981719425477 ep1397 114677596252993989920779 ep1398 Bool.true 784228957102970691 151115727451828646838272 26727747126996364825969

noncomputable def ep1450 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz606) 144408520715049219 1099511627776 1 1099511627776 4185784 4185785 549755813888 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz606) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz606 qz15)) Bool.false 144408520715049219 1099511627776 1 1099511627776 (BSN.sqrt_natCast_div_one 17249876309) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz606 qz15)) Bool.false 144408520715049219 1099511627776 1 1099511627776 144408520715049219 1099511627776 1 1099511627776 (BSN.sqrt_enclosure 17249876309 1 72204260357524609 72204260357524610 549755813888 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep1451 := nat_lit 17611562130375000000000000000

noncomputable def ep1452 := nat_lit 35223124260750000000000000

noncomputable def ep1453 := nat_lit 66696165312933809461506605056

noncomputable def ep1454 := nat_lit 140892497043000000000000000

noncomputable def ep1455 := nat_lit 15941573931076398915349137361049652099609375

noncomputable def ep1456 := nat_lit 467100286100398663927513626167054072422200

noncomputable def ep1457 := nat_lit 12443102352736214051826697839075

noncomputable def ep1458 := BSN.log_dyadic_bound 13 45 11 10 ep1455 549755813888 140892497043 ep1456 ep1457 326943690044 58 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP 13) (BSN.artanhQ 45) 0 10 ep1456 ep1455 ep1457 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1459 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz139 142522 1000 0 1 3791238061292791 1125899906842624 250140892497043 ep1452 270167415485785579451 562949953421312000 17825290140231781223 ep1451 qz18 (BSN.isNear_log_sfrac 29 1 3791238061292791 1125899906842624 250140892497043 ep1452 Bool.false (@Enclosure.Real.IsNear.recentre' qz446 Bool.false ep1453 ep1321 1000563569988172 ep1454 3791238061292791 1125899906842624 250140892497043 ep1452 (BSN.log_rat_reduce_isNear 29 1 4 58 32 326943690044 549755813888 24973259072661432 36028797018963968 140892497043 1000000000000000 rfl rfl rfl rfl (ep1458 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1460 := nat_lit 65034960804501384711754481664

noncomputable def ep1461 := nat_lit 79228162514264337593543950336

noncomputable def ep1462 := nat_lit 400489204228461260547865275241434715574344615310442755800814493825852937576747653773240951139710760407887835242236446443081003611475894281033525339265648629706730746970741088834260499846660096

noncomputable def ep1463 := nat_lit 105837034526088297993462992180381389879322393587938448256862118304383601140722304680429244037940156116138104563485128823993096599821236196995637140025443129138277048165837662434864861216033996800

noncomputable def ep1464 := nat_lit 1590614493991090774681733250596031579361434398948630263217060994096770769886111149829543954865972091994822018067422625209165530053281469397646350208322244471380726693763998551004676096

noncomputable def ep1465 := nat_lit 2002260191870855180039558626939568008391238028477791430950159881232159134773316835189675933509520177423724583196169747009947484446102958169893525820825045529694856018501780555605147122722144256

noncomputable def ep1466 := nat_lit 3704296208413090429771204726313348645776283775577845688990174140653426039925280663815023541327905464064833659721979508839758380993743266894847299900890509519839696685804318185220270142561189888000

noncomputable def ep1467 := BSN.sin_dyadic_bound_f 1848404758803252 2251799813685248 4 3 1099511627776 282060174745 ep1462 ep1463 ep1464 ep1465 ep1466 ep1464 804545597333 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 1848404758803252) (BSN.sinEvenQ 2251799813685248) 0 3 ep1462 ep1463 ep1464 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 1848404758803252) (BSN.sinOddQ 2251799813685248) 0 3 ep1465 ep1466 ep1464 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz517 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 263835366685337) (@Nat.cast Real Real.instNatCast 549755813888))

noncomputable def ep1468 := @Enclosure.Real.IsNear.cos_image qz140 qz517 Bool.false 263835366685337 549755813888 557 549755813888 Bool.true 804545597333 1099511627776 1 140892497043 (@Enclosure.Real.IsNear.recentre' qz140 Bool.false 270167415485785579451 562949953421312000 17825290140231781223 ep1451 263835366685337 549755813888 557 549755813888 (ep1459 rfl) rfl) (Enclosure.sfrac_false_div 263835366685337 549755813888) (BSN.cos_reduce1 qz517 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1460) (@Nat.cast Real Real.instNatCast ep1461)) 226375608064910080 72057594037927936 Bool.false 804545597333 1099511627776 76 1000000000000000 281784994086 140892497043 (BSN.sin_reduce_arg_pos_rat_q1 263835366685337 549755813888 226375608064910080 72057594037927936 76 ep1460 ep1461 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 804545597333 1099511627776 ep1460 ep1461 1848404758803252 2251799813685248 282060174745 281784994086 (ep1467 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1469 := nat_lit 154052808505613699355365593050373164619907145558252384840676749064944568231211850978020136320598480587252703428379318956643606590332487545798146625274548828683228044699231771040902675196542976

noncomputable def ep1470 := nat_lit 8141310348160638307189460936952414606101722583687572942835547561875661626209408052340711079841550470472161889498856063384084353832402784384279780001957163779867465243525974033451143170464153600

noncomputable def ep1471 := nat_lit 934418696514247254001501244255813972147704654385949090725400729942585954735551917512274862058929046241459338678982038018256639427712033789779744269508358868072962930212978342103306195236290560

noncomputable def ep1472 := nat_lit 740859241682618085954240945262669729155256755115569137798034828130685207985056132763004708265581092812966731944395901767951676198748653378969459980178101903967939337160863637044054028512237977600

noncomputable def ep1473 := BSN.cos_dyadic_bound_f 1848404758803252 2251799813685248 4 3 1099511627776 282060174745 ep1469 ep1470 ep1464 ep1471 ep1472 ep1464 749421244312 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 1848404758803252) (BSN.cosEvenQ 2251799813685248) 0 3 ep1469 ep1470 ep1464 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 1848404758803252) (BSN.cosOddQ 2251799813685248) 0 3 ep1471 ep1472 ep1464 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1474 := @Enclosure.Real.IsNear.sin_image qz140 qz517 Bool.false 263835366685337 549755813888 557 549755813888 Bool.false 749421244312 1099511627776 1 140892497043 (@Enclosure.Real.IsNear.recentre' qz140 Bool.false 270167415485785579451 562949953421312000 17825290140231781223 ep1451 263835366685337 549755813888 557 549755813888 (ep1459 rfl) rfl) (Enclosure.sfrac_false_div 263835366685337 549755813888) (BSN.sin_reduce1 qz517 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1460) (@Nat.cast Real Real.instNatCast ep1461)) 226375608064910080 72057594037927936 Bool.false 749421244312 1099511627776 76 1000000000000000 281784994086 140892497043 (BSN.sin_reduce_arg_pos_rat_q1 263835366685337 549755813888 226375608064910080 72057594037927936 76 ep1460 ep1461 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 749421244312 1099511627776 ep1460 ep1461 1848404758803252 2251799813685248 282060174745 281784994086 (ep1473 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz518 := (@Enclosure.Real.IsNear.recentre' qz242 Bool.false 8371569 1099511627776 1 1099511627776 8371569 1099511627776 1 1099511627776 (ep1450 rfl rfl) rfl)

noncomputable def ep1475 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz242 qz137) (@HMul.hMul Real Real Real qz0 qz242 qz586) Bool.true 6735308981719425477 ep1397 114677596252993989920779 ep1398 Bool.true 784228957102970691 151115727451828646838272 26727747126996364825969 ep1447 (@Enclosure.Real.IsNear.mulLit_ft qz242 qz137 8371569 1099511627776 1 1099511627776 804545597333 1099511627776 79026876666839 77456469382587098333184 6735308981719425477 ep1397 114677596252993989920779 ep1398 qz518 (@Enclosure.Real.IsNear.recentre' qz137 Bool.true 804545597333 1099511627776 79026876666839 77456469382587098333184 804545597333 1099511627776 79026876666839 77456469382587098333184 (ep1468 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz242 qz586 8371569 1099511627776 1 1099511627776 93677655539 137438953472 79026876666839 77456469382587098333184 784228957102970691 151115727451828646838272 26727747126996364825969 ep1447 qz518 (@Enclosure.Real.IsNear.neg qz138 Bool.false 93677655539 137438953472 79026876666839 77456469382587098333184 (@Enclosure.Real.IsNear.recentre' qz138 Bool.false 749421244312 1099511627776 79026876666839 77456469382587098333184 93677655539 137438953472 79026876666839 77456469382587098333184 (ep1474 rfl rfl) rfl)) rfl)

noncomputable def ep1476 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz233 361770192865081 90000000000 0 1 784228957102970691 151115727451828646838272 26727747126996364825969 ep1447 ep1391

noncomputable def ep1477 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 15234077863 120000000 0 1 Bool.false 361770192865081 90000000000 0 1 ep1445

noncomputable def ep1478 := @Enclosure.Complex.IsNear.im_isNear qz223 Bool.true 6735308981719425477 ep1397 114677596252993989920779 ep1398 Bool.true 784228957102970691 151115727451828646838272 26727747126996364825969 ep1447

noncomputable def ep1479 := nat_lit 3982334998308647471766971111

noncomputable def ep1480 := nat_lit 6044629098073145873530880000000

noncomputable def ep1481 := nat_lit 407172580835237171076766190424247

noncomputable def ep1482 := nat_lit 5109857323957814771904942974215127040000000

noncomputable def ep1483 := nat_lit 812211343107516291386267965022879

noncomputable def ep1484 := nat_lit 41486936113749525952622577414225418099

noncomputable def ep1485 := @Enclosure.Real.IsNear.addLit_tt (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz233) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz232) ep1479 ep1480 ep1481 ep1482 ep1483 ep1382 ep1484

noncomputable def ep1486 := nat_lit 15329571971873444315714828922645381120000000000

noncomputable def ep1487 := nat_lit 5053946746387073761595834560423928162031565033858159083520000000

noncomputable def ep1488 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz233 15234077863 120000000 0 1 784228957102970691 151115727451828646838272 26727747126996364825969 ep1447 ep1479

noncomputable def ep1489 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz232 361770192865081 90000000000 0 1 6735308981719425477 ep1397 114677596252993989920779 ep1398 ep1483

noncomputable abbrev qz519 := (@ep1449 ep1447 (BSN.cpow_neg_s_sub_mk qz13 142522 1000 29 3 17249876309 qz14 rfl EMRow50.d19) ep1475)

noncomputable def ep1490 := ep1386 (@ep1394 ep1395 ep1396 ep1376 ep1377 ep1378 ep1379 (@ep1399 ep1388 ep1389 ep1390 ep1446 (ep1448 qz519) rfl) (@ep1476 ep1392 ep1393 ep1395 ep1477 (ep1478 qz519) rfl) rfl rfl) (@ep1485 ep1486 ep1487 ep1381 ep1382 ep1383 ep1385 (@ep1488 ep1480 ep1481 ep1482 ep1446 (ep1478 qz519) rfl) (@ep1489 ep1382 ep1484 ep1486 ep1477 (ep1448 qz519) rfl) rfl rfl)

noncomputable def ep1491 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) ep1381 ep1382 ep1383 ep1385 ep1381 ep1382 ep1383

noncomputable def ep1492 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223) Bool.false ep1376 ep1377 ep1378 ep1379 Bool.true ep1381 ep1382 ep1383

noncomputable def ep1493 := @ep1348 5032993333947636525 4035225266123964416 660779127275 4035225266123964416 (@ep1349 1 3670016 (ep1350 (@ep1351 1048576 1 1048576 (ep1352 (@ep1353 20324770484 5081192621 250000 0 1 (ep1357 rfl) (ep1360 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep1361 4195 1099511627776 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (@ep1362 4195 1099511627776 33667713105 1099511627776 4195 1099511627776 (@ep1367 16833854455 16833858650 549755813888 (@ep1373 ep1364 ep1374 ep1366 ep1375 ep1363 ep1364 ep1365 ep1366 (@ep1380 ep1379 ep1368 ep1369 ep1370 ep1371 (@ep1384 ep1385 ep1490) (@ep1384 ep1385 ep1490) rfl) (@ep1491 ep1385 ep1372 ep1364 ep1374 ep1366 (@ep1492 ep1385 ep1490) (@ep1492 ep1385 ep1490) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow50.d20 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz412 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 29))) (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)))) Bool.false 138435486598394633663 108951082185347039232 10418764854305737 108951082185347039232 := ep1346 (ep1347 ep1493) rfl rfl

noncomputable abbrev qz607 := (@HAdd.hAdd Complex Complex Complex qz609 qz615 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz520 := qz607

noncomputable abbrev qz243 := (@HDiv.hDiv Real Real Real qz270 (@Norm.norm Complex Complex.instNorm qz520) (@HAdd.hAdd Real Real Real qz412 (Complex.re qz450) qz547))

noncomputable abbrev qz521 := (@HPow.hPow Complex Complex Complex qz536 qz581 (@HSub.hSub Complex Complex Complex qz572 qz589 qz543))

noncomputable abbrev qz244 := qz521

noncomputable def ep1494 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz149 1 29))) (@HMul.hMul Real Real Real qz0 qz243 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) 116562656329 1855425871872 178608647 1855425871872 1330652191483761141 1008806316530991104 171742427771

noncomputable def ep1495 := nat_lit 2586515646518471315903026823168

noncomputable def ep1496 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz149 1 29)) 26561 1769472 1 1769472 4388489 1048576 6559 1048576 116562656329 1855425871872

noncomputable def ep1497 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz149 1 29)) (Real.sqrt (@HAdd.hAdd Real Real Real qz412 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz149 1 29)) (Complex.re (zetaApproximant qz149 1 29))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz149 1 29)) (Complex.im (zetaApproximant qz149 1 29))))) Bool.false 4388489 1048576 6559 1048576

noncomputable def ep1498 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz412 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz149 1 29)) (Complex.re (zetaApproximant qz149 1 29))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz149 1 29)) (Complex.im (zetaApproximant qz149 1 29))))) Bool.false 4388489 1048576 6559 1048576

noncomputable def ep1499 := nat_lit 11904138826307108490787019748150026747609

noncomputable def ep1500 := nat_lit 679621063078000120839798661673962700800

noncomputable def ep1501 := nat_lit 1020958474983505423255286706648386633142706849379482278149

noncomputable def ep1502 := nat_lit 19500643548467131444804140228285965505259972019965919232000

noncomputable def ep1503 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz412 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz149 1 29)) (Complex.re (zetaApproximant qz149 1 29))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz149 1 29)) (Complex.im (zetaApproximant qz149 1 29)))) ep1499 ep1500 ep1501 ep1502 2190965 2197524

noncomputable def ep1504 := nat_lit 4971411506237270979371176924586591847962110976521

noncomputable def ep1505 := nat_lit 283934410677520491088864115305973738744735334400

noncomputable def ep1506 := nat_lit 130062270873170728127029772684465913355259708189148861557839

noncomputable def ep1507 := nat_lit 2535083661300727087824538229677175515683796362595569500160000

noncomputable def ep1508 := nat_lit 1940300963821123606645695829025503445400371041

noncomputable def ep1509 := nat_lit 2662330874684976896157499179824348953292182230183834601531

noncomputable def ep1510 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz149 1 29)) (Complex.re (zetaApproximant qz149 1 29))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz149 1 29)) (Complex.im (zetaApproximant qz149 1 29))) ep1504 ep1505 ep1506 ep1507 ep1508 ep1505 ep1509

noncomputable def ep1511 := nat_lit 1412105714469623596387241074610409934659367457477427779445659912782479401103877600854380694732800

noncomputable def ep1512 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz149 1 29)) (Complex.re (zetaApproximant qz149 1 29)) ep1050 532854962140281181306880 ep1051 ep1052 ep1050 532854962140281181306880 ep1051 ep1052 ep1504

noncomputable def ep1513 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (zetaApproximant qz149 1 29)) (Complex.im (zetaApproximant qz149 1 29)) 44048847474379208854321 532854962140281181306880 ep1173 ep1052 44048847474379208854321 532854962140281181306880 ep1173 ep1052 ep1508

noncomputable def ep1514 := @ep1494 1008806316530991104 ep1495 37638756424981275863 27237770546336759808 2626623414463225 27237770546336759808 (@ep1496 178608647 1855425871872 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) qz504) Bool.false 26561 1769472 1 1769472 (BSN.theta_err_eq 1 2 96 162 EMRow50.d16 EMRow50.d17 rfl) (ep1327 rfl)) (ep1497 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz149 1 29)) (@ep1498 4388489 1048576 6559 1048576 (@ep1503 524288 (@ep1510 ep1507 ep1511 ep1499 ep1500 ep1501 ep1502 (@ep1512 ep1505 ep1506 ep1507 ep1307 ep1307 rfl) (@ep1513 ep1505 ep1509 ep1507 ep1315 ep1315 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz245 := (@Norm.norm Complex Complex.instNorm qz520)

noncomputable def ep1515 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz243 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz245 qz605) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) Bool.false 1330652191483761141 1008806316530991104 171742427771 1008806316530991104 (BSN.zrb_shape_eq qz245 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) qz152 3)

noncomputable def ep1516 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz245 qz605) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) 151595121 3670016 1 3670016 8777671621 274877906944 1075 274877906944

noncomputable def ep1517 := @Enclosure.Real.IsNear.mulLit_ff qz245 qz605 151595121 1048576 1 1048576 2 7 0 1 151595121 3670016

noncomputable abbrev qz522 := (Complex.re qz607)

noncomputable abbrev qz523 := (Complex.im qz607)

noncomputable abbrev qz246 := (@HAdd.hAdd Real Real Real qz412 (@HMul.hMul Real Real Real qz267 qz522 qz522) (@HMul.hMul Real Real Real qz267 qz523 qz523))

noncomputable abbrev qz247 := qz520

noncomputable def ep1518 := @Enclosure.Real.IsNear.of_eq qz245 (Real.sqrt qz246) Bool.false 151595121 1048576 1 1048576 (BSN.norm_eq_sqrt_mul_add qz247)

noncomputable def ep1519 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz246) Bool.false 151595121 1048576 1 1048576 151595121

noncomputable def ep1520 := @Enclosure.Real.IsNear.sqrt_image qz246 209011709 10000 0 1 75797560 75797561 524288

noncomputable abbrev qz248 := (@HMul.hMul Real Real Real qz267 qz522 qz522)

noncomputable abbrev qz249 := (@HMul.hMul Real Real Real qz267 qz523 qz523)

noncomputable def ep1521 := @Enclosure.Real.IsNear.addLit_ff qz248 qz249 49 4 0 1 208889209 10000 0 1

noncomputable abbrev qz250 := qz522

noncomputable def ep1522 := @Enclosure.Real.IsNear.mulLit_ff qz250 qz250 7 2 0 1 7 2 0 1 49 4

noncomputable def ep1523 := @Enclosure.Complex.IsNear.of_eq qz247 (Complex.mk qz509 qz152) Bool.false 7 2 0 1 Bool.false 144530 1000 0 1 (BSN.s_add_nat_mk qz152 Bool.false 144530 1000 3 qz153)

noncomputable abbrev qz524 := (ep1523 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz152 Bool.false 7 2 0 1 Bool.false 144530 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz154))

noncomputable def ep1524 := @ep1522 0 1 (@Enclosure.Complex.IsNear.re_isNear qz247 Bool.false 7 2 0 1 Bool.false 144530 1000 0 1 qz524)

noncomputable def ep1525 := ep1524 (@Enclosure.Complex.IsNear.re_isNear qz247 Bool.false 7 2 0 1 Bool.false 144530 1000 0 1 qz524)

noncomputable abbrev qz251 := qz523

noncomputable def ep1526 := @Enclosure.Real.IsNear.mulLit_ff qz251 qz251 144530 1000 0 1 144530 1000 0 1 208889209 10000

noncomputable def ep1527 := @ep1526 0 1 (@Enclosure.Complex.IsNear.im_isNear qz247 Bool.false 7 2 0 1 Bool.false 144530 1000 0 1 qz524)

noncomputable def ep1528 := ep1527 (@Enclosure.Complex.IsNear.im_isNear qz247 Bool.false 7 2 0 1 Bool.false 144530 1000 0 1 qz524)

noncomputable def ep1529 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Real.sqrt (@HAdd.hAdd Real Real Real qz412 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))))) Bool.false 8777671621 274877906944

noncomputable def ep1530 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz412 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))))) Bool.false 35110686484 1099511627776

noncomputable def ep1531 := nat_lit 85842187925409951665085001417903138141738487754310509858641173

noncomputable def ep1532 := nat_lit 84182494310260008088532246364457901932181714475417600000000000000

noncomputable def ep1533 := nat_lit 3755747276305072452335316870176395054705991612105896117350126758462268214804607

noncomputable def ep1534 := nat_lit 15039729717814264309925474402300420411033889358668481399359617412483357081600000000000000

noncomputable def ep1535 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz412 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)))) ep1531 ep1532 ep1533 ep1534

noncomputable def ep1536 := nat_lit 135239439702304210436629101963548277053739714772680036644929

noncomputable def ep1537 := nat_lit 2338402619729444669125895732346052831449492068761600000000000000

noncomputable def ep1538 := nat_lit 8372373636491884256267756469373785457575632022489552577689729350104319004353

noncomputable def ep1539 := nat_lit 469991553681695759685171075071888137844809042458390043729988044140104908800000000000000

noncomputable def ep1540 := nat_lit 80973568096127000089366353747215400167803858022494028539423729

noncomputable def ep1541 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) ep1536 ep1537 ep1538 ep1539 ep1540

noncomputable def ep1542 := nat_lit 3487831319937332156134748663156433920063571387386230434864055419258930006665311

noncomputable def ep1543 := nat_lit 200733597128085933990591802169944318889474966596259172400642423488869425838636308374435562993988655830056881356800000000000000

noncomputable def ep1544 := nat_lit 367749153231253831580069971423

noncomputable def ep1545 := nat_lit 17954218699078236535736651223403091

noncomputable def ep1546 := nat_lit 15329571971873444315714828922645381120000000

noncomputable def ep1547 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) ep1544 ep1388 ep1545 ep1546 ep1544 ep1388 ep1545

noncomputable def ep1548 := nat_lit 8998531441081205673278024799527

noncomputable def ep1549 := nat_lit 290142196707511001929482240000000

noncomputable def ep1550 := nat_lit 458505650343192858125977578791138977

noncomputable def ep1551 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz244) Bool.false ep1544 ep1388 ep1545 ep1546 Bool.true ep1548 ep1549 ep1550

noncomputable def ep1552 := nat_lit 122636575774987554525718631381163048960000000

noncomputable def ep1553 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz244 Bool.false ep1544 ep1388 ep1545 ep1546 Bool.true ep1548 ep1549 ep1550 ep1552

noncomputable def ep1554 := nat_lit 1852232638208004566509583777

noncomputable def ep1555 := nat_lit 1934281311383406679529881600000

noncomputable def ep1556 := nat_lit 94358806817395820990276977742227

noncomputable def ep1557 := nat_lit 817577171833250363504790875874420326400000

noncomputable def ep1558 := nat_lit 51756871148306743217851195731

noncomputable def ep1559 := nat_lit 64739964285008259568675831562945339

noncomputable abbrev qz252 := (Complex.re qz521)

noncomputable abbrev qz253 := (Complex.im qz521)

noncomputable def ep1560 := @Enclosure.Real.IsNear.subLit_tt_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3)))) qz252) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253) ep1554 ep1555 ep1556 ep1557 ep1558 ep1480 ep1559

noncomputable def ep1561 := nat_lit 61318287887493777262859315690581524480000000

noncomputable def ep1562 := nat_lit 88916289296535878657848950760096859520961917348321689600000

noncomputable def ep1563 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3)))) qz252 626655127 4800000 0 1 8867234424819464853 ep1397 150575336819028085587301 ep1398 ep1554

noncomputable def ep1564 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3)))) 626655127 4800000 0 1 0 1 0 1 626655127

noncomputable def ep1565 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 1879965381 20000 0 1 626655127 4800000 0

noncomputable abbrev qz525 := (@HAdd.hAdd Complex Complex Complex qz535 qz588 qz544)

noncomputable abbrev qz254 := qz525

noncomputable def ep1566 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz73 (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 2)) qz254) Bool.true 1879965381 20000 0 1 Bool.true 3018244690177 1000000 0 1

noncomputable abbrev qz255 := (Complex.re qz525)

noncomputable abbrev qz256 := (Complex.im qz525)

noncomputable def ep1567 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 2))) qz255) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 2))) qz256) 208881709 4000 0 1 208889209 5000 0 1

noncomputable def ep1568 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 2))) qz255 208881709 10000 0 1 5 2 0 1 208881709 4000

noncomputable abbrev qz526 := (@HAdd.hAdd Complex Complex Complex qz535 qz588 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz257 := qz526

noncomputable def ep1569 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz73 (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1)) qz257) Bool.true 208881709 10000 0 1 Bool.false 14453 50 0 1

noncomputable abbrev qz258 := (Complex.re qz526)

noncomputable abbrev qz259 := (Complex.im qz526)

noncomputable def ep1570 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1))) qz258) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1))) qz259) 3 4 0 1 208889209 10000 0 1

noncomputable def ep1571 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1))) qz258 1 2 0 1 3 2 0 1 3 4

noncomputable def ep1572 := @ep1571 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 144530 1000 0 1 ep1272)

noncomputable def ep1573 := @Enclosure.Complex.IsNear.of_eq qz257 (Complex.mk qz513 qz152) Bool.false 3 2 0 1 Bool.false 144530 1000 0 1 (BSN.s_add_nat_mk qz152 Bool.false 144530 1000 1 qz153)

noncomputable abbrev qz527 := (ep1573 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz152 Bool.false 3 2 0 1 Bool.false 144530 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz154))

noncomputable def ep1574 := ep1572 (@Enclosure.Complex.IsNear.re_isNear qz257 Bool.false 3 2 0 1 Bool.false 144530 1000 0 1 qz527)

noncomputable def ep1575 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1))) qz259 144530 1000 0 1 144530 1000 0 1 208889209 10000

noncomputable def ep1576 := @ep1575 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 144530 1000 0 1 ep1272)

noncomputable def ep1577 := ep1576 (@Enclosure.Complex.IsNear.im_isNear qz257 Bool.false 3 2 0 1 Bool.false 144530 1000 0 1 qz527)

noncomputable def ep1578 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1)) qz257 Bool.true 208881709 10000 0 1 Bool.false 14453 50 0 1 (@ep1570 835526836 208881709 10000 0 1 (ep1574 rfl) (ep1577 rfl) rfl rfl)

noncomputable def ep1579 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1))) qz259) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1))) qz258) 14453 200 0 1 43359 200 0 1

noncomputable def ep1580 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1))) qz259 1 2 0 1 144530 1000 0 1 14453 200

noncomputable def ep1581 := @ep1580 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 144530 1000 0 1 ep1272)

noncomputable def ep1582 := ep1581 (@Enclosure.Complex.IsNear.im_isNear qz257 Bool.false 3 2 0 1 Bool.false 144530 1000 0 1 qz527)

noncomputable def ep1583 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1))) qz258 144530 1000 0 1 3 2 0 1 43359 200

noncomputable def ep1584 := @ep1583 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 144530 1000 0 1 ep1272)

noncomputable def ep1585 := ep1584 (@Enclosure.Complex.IsNear.re_isNear qz257 Bool.false 3 2 0 1 Bool.false 144530 1000 0 1 qz527)

noncomputable abbrev qz260 := (ep1569 (BSN.ascPochhammer_succ_eval_c 1 2 qz450 rfl) (ep1578 (@ep1579 11562400 14453 50 0 1 (ep1582 rfl) (ep1585 rfl) rfl rfl)))

noncomputable def ep1586 := @ep1568 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 208881709 10000 0 1 Bool.false 14453 50 0 1 qz260)

noncomputable def ep1587 := @Enclosure.Complex.IsNear.of_eq qz254 (Complex.mk qz515 qz152) Bool.false 5 2 0 1 Bool.false 144530 1000 0 1 (BSN.s_add_nat_mk qz152 Bool.false 144530 1000 2 qz153)

noncomputable abbrev qz528 := (ep1587 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz152 Bool.false 5 2 0 1 Bool.false 144530 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz154))

noncomputable def ep1588 := ep1586 (@Enclosure.Complex.IsNear.re_isNear qz254 Bool.false 5 2 0 1 Bool.false 144530 1000 0 1 qz528)

noncomputable def ep1589 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 2))) qz256 14453 50 0 1 144530 1000 0 1 208889209 5000

noncomputable def ep1590 := @ep1589 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 208881709 10000 0 1 Bool.false 14453 50 0 1 qz260)

noncomputable def ep1591 := ep1590 (@Enclosure.Complex.IsNear.im_isNear qz254 Bool.false 5 2 0 1 Bool.false 144530 1000 0 1 qz528)

noncomputable def ep1592 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 2)) qz254 Bool.true 1879965381 20000 0 1 Bool.true 3018244690177 1000000 0 1 (@ep1567 1879965381000 1879965381 20000 0 1 (ep1588 rfl) (ep1591 rfl) rfl rfl)

noncomputable def ep1593 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 2))) qz256) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 2))) qz255) 3018967340177 1000000 0 1 14453 20 0 1

noncomputable def ep1594 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 2))) qz256 208881709 10000 0 1 144530 1000 0 1 3018967340177 1000000

noncomputable def ep1595 := @ep1594 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 208881709 10000 0 1 Bool.false 14453 50 0 1 qz260)

noncomputable def ep1596 := ep1595 (@Enclosure.Complex.IsNear.im_isNear qz254 Bool.false 5 2 0 1 Bool.false 144530 1000 0 1 qz528)

noncomputable def ep1597 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 2))) qz255 14453 50 0 1 5 2 0 1 14453 20

noncomputable def ep1598 := @ep1597 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 208881709 10000 0 1 Bool.false 14453 50 0 1 qz260)

noncomputable def ep1599 := ep1598 (@Enclosure.Complex.IsNear.re_isNear qz254 Bool.false 5 2 0 1 Bool.false 144530 1000 0 1 qz528)

noncomputable abbrev qz261 := (ep1566 (BSN.ascPochhammer_succ_eval_c 2 3 qz450 rfl) (ep1592 (@ep1593 60364893803540 3018244690177 1000000 0 1 (ep1596 rfl) (ep1599 rfl) rfl rfl)))

noncomputable def ep1600 := @ep1565 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1402) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 1879965381 20000 0 1 Bool.true 3018244690177 1000000 0 1 qz261)

noncomputable def ep1601 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 3018244690177 1000000 0 1 0 1 0

noncomputable def ep1602 := @ep1601 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1402) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 1879965381 20000 0 1 Bool.true 3018244690177 1000000 0 1 qz261)

noncomputable def ep1603 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3)))) 3018244690177 720000000 0 1 0 1 0 1 3018244690177

noncomputable def ep1604 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 3018244690177 1000000 0 1 3018244690177 720000000 0

noncomputable def ep1605 := @ep1604 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1402) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 1879965381 20000 0 1 Bool.true 3018244690177 1000000 0 1 qz261)

noncomputable def ep1606 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 1879965381 20000 0 1 0 1 0

noncomputable def ep1607 := @ep1606 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1402) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 1879965381 20000 0 1 Bool.true 3018244690177 1000000 0 1 qz261)

noncomputable def ep1608 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 626655127 4800000 0 1 Bool.false 3018244690177 720000000 0 1 (@ep1564 626655127 4800000 0 1 (ep1600 rfl) (ep1602 rfl) rfl rfl) (@ep1603 3018244690177 720000000 0 1 (ep1605 rfl) (ep1607 rfl) rfl rfl)

noncomputable def ep1609 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 626655127 4800000 0 1 Bool.false 3018244690177 720000000 0 1 ep1608

noncomputable def ep1610 := nat_lit 85164288732630246198415716236918784

noncomputable def ep1611 := @Enclosure.Complex.IsNear.re_isNear qz244 Bool.true 8867234424819464853 ep1397 150575336819028085587301 ep1398 Bool.true 154332033400328427 75557863725914323419136 21449541349548995893307 ep1610

noncomputable def ep1612 := @Enclosure.Complex.IsNear.of_eq qz244 (Complex.mk (@HMul.hMul Real Real Real qz0 qz242 qz216) (@HMul.hMul Real Real Real qz0 qz242 qz601)) Bool.true 8867234424819464853 ep1397 150575336819028085587301 ep1398 Bool.true 154332033400328427 75557863725914323419136 21449541349548995893307

noncomputable def ep1613 := nat_lit 3522312426075000000000000000

noncomputable def ep1614 := @Enclosure.Real.IsNear.mulLit_ff qz152 qz139 144530 1000 0 1 3791238061292791 1125899906842624 250140892497043 ep1452 54794763699864708323 112589990684262400 3615286319259762479 ep1613 qz154 (BSN.isNear_log_sfrac 29 1 3791238061292791 1125899906842624 250140892497043 ep1452 Bool.false (@Enclosure.Real.IsNear.recentre' qz446 Bool.false ep1453 ep1321 1000563569988172 ep1454 3791238061292791 1125899906842624 250140892497043 ep1452 (BSN.log_rat_reduce_isNear 29 1 4 58 32 326943690044 549755813888 24973259072661432 36028797018963968 140892497043 1000000000000000 rfl rfl rfl rfl (ep1458 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1615 := nat_lit 205866667947143400781808402432

noncomputable def ep1616 := nat_lit 158456325028528675187087900672

noncomputable def ep1617 := nat_lit 2515192850395268241260542857627862067674464580599277789923173295423519692698215593935640102502573355059602300686228119456548474894691483195378304087422929867505823608112834879181560073584377856

noncomputable def ep1618 := nat_lit 393074451606890277791081621662155836567658868464880185757746832618414912057291378347662706921347128792741781693111031987541491155947202469474088102432537964920625584457663956926286790656

noncomputable def ep1619 := nat_lit 12568645014927681415643602490694555348190956677880608770043287472944206299216783923945763400996726027501759625368083722859764865629437229267966861029048738643383356883290533108774846272127369216

noncomputable def ep1620 := BSN.sin_dyadic_bound_f 2925541308899588 2251799813685248 4 3 1099511627776 282060174745 ep1617 ep1463 ep1618 ep1619 ep1466 ep1618 1059208187237 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 2925541308899588) (BSN.sinEvenQ 2251799813685248) 0 3 ep1617 ep1463 ep1618 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 2925541308899588) (BSN.sinOddQ 2251799813685248) 0 3 ep1619 ep1466 ep1618 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz529 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 535105114256491) (@Nat.cast Real Real.instNatCast 1099511627776))

noncomputable def ep1621 := @Enclosure.Real.IsNear.cos_image qz218 qz529 Bool.false 535105114256491 1099511627776 1129 1099511627776 Bool.true 1059208187237 1099511627776 1 140892497043 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 54794763699864708323 112589990684262400 3615286319259762479 ep1613 535105114256491 1099511627776 1129 1099511627776 (ep1614 rfl) rfl) (Enclosure.sfrac_false_div 535105114256491 1099511627776) (BSN.cos_reduce1 qz529 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1615) (@Nat.cast Real Real.instNatCast ep1616)) 226375608064910080 72057594037927936 Bool.false 1059208187237 1099511627776 77 1000000000000000 281784994086 140892497043 (BSN.sin_reduce_arg_pos_rat_q1 535105114256491 1099511627776 226375608064910080 72057594037927936 77 ep1615 ep1616 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1059208187237 1099511627776 ep1615 ep1616 2925541308899588 2251799813685248 282060174745 281784994086 (ep1620 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1622 := nat_lit 1087243209115847651833633912981033710083975853468950402215572369539890968074851100115302757521780539086193761365084932148769314628226733053077556425838891113082541271956263753088474040539837738401324747607460989783887864472297781629148427246169737715091767296

noncomputable def ep1623 := nat_lit 9143154438917106547073450216747265219935699251911401668599841096795265811183449112191507787131973854900989849820006257944449176726486799171479583678624634615830042174450721079826584645260284745242101100073037662116721455541889816942397816655933916701523968000

noncomputable def ep1624 := nat_lit 28793851217951328805226224309244295250246422275869091966620498800752284493654885425903812455097756282713921348802628356806284604585025389943073095646239077229557182423063855853586678416347460550560182771641687852492346564560291151270811412113391616

noncomputable def ep1625 := nat_lit 11077360092088823943761430851754527672802537241981810311878443997801677290182286103393731224460166551287651758638789484496792954555869628759753723906243770088098379172277414742363957161101568064562010884384094734074708119255859343841582615153263031889812258816

noncomputable def ep1626 := nat_lit 1398902629154317301702237883162331578650161985542444455295775687809675669111067714165300691431191999799851447022460957465500724039152480273236376302829569096221996452690960325213467450724823566022041468311174762303858382697909141992186865948357889255333167104000

noncomputable def ep1627 := BSN.cos_dyadic_bound_f 2925541308899588 2251799813685248 5 4 1099511627776 282060174745 ep1622 ep1623 ep1624 ep1625 ep1626 ep1624 294964126128 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.cosEvenP 2925541308899588) (BSN.cosEvenQ 2251799813685248) 0 4 ep1622 ep1623 ep1624 rfl rfl rfl rfl) (@BSN.binarySplit_of_base4 (BSN.cosOddP 2925541308899588) (BSN.cosOddQ 2251799813685248) 0 4 ep1625 ep1626 ep1624 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1628 := @Enclosure.Real.IsNear.sin_image qz218 qz529 Bool.false 535105114256491 1099511627776 1129 1099511627776 Bool.false 294964126128 1099511627776 1 140892497043 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 54794763699864708323 112589990684262400 3615286319259762479 ep1613 535105114256491 1099511627776 1129 1099511627776 (ep1614 rfl) rfl) (Enclosure.sfrac_false_div 535105114256491 1099511627776) (BSN.sin_reduce1 qz529 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1615) (@Nat.cast Real Real.instNatCast ep1616)) 226375608064910080 72057594037927936 Bool.false 294964126128 1099511627776 77 1000000000000000 281784994086 140892497043 (BSN.sin_reduce_arg_pos_rat_q1 535105114256491 1099511627776 226375608064910080 72057594037927936 77 ep1615 ep1616 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 294964126128 1099511627776 ep1615 ep1616 2925541308899588 2251799813685248 282060174745 281784994086 (ep1627 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1629 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz242 qz216) (@HMul.hMul Real Real Real qz0 qz242 qz601) Bool.true 8867234424819464853 ep1397 150575336819028085587301 ep1398 Bool.true 154332033400328427 75557863725914323419136 21449541349548995893307 ep1610 (@Enclosure.Real.IsNear.mulLit_ft qz242 qz216 8371569 1099511627776 1 1099511627776 1059208187237 1099511627776 160167140789323 154912938765174196666368 8867234424819464853 ep1397 150575336819028085587301 ep1398 qz518 (@Enclosure.Real.IsNear.recentre' qz216 Bool.true 1059208187237 1099511627776 160167140789323 154912938765174196666368 1059208187237 1099511627776 160167140789323 154912938765174196666368 (ep1621 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz242 qz601 8371569 1099511627776 1 1099511627776 18435257883 68719476736 160167140789323 154912938765174196666368 154332033400328427 75557863725914323419136 21449541349548995893307 ep1610 qz518 (@Enclosure.Real.IsNear.neg qz217 Bool.false 18435257883 68719476736 160167140789323 154912938765174196666368 (@Enclosure.Real.IsNear.recentre' qz217 Bool.false 294964126128 1099511627776 160167140789323 154912938765174196666368 18435257883 68719476736 160167140789323 154912938765174196666368 (ep1628 rfl rfl) rfl)) rfl)

noncomputable def ep1630 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253 3018244690177 720000000 0 1 154332033400328427 75557863725914323419136 21449541349548995893307 ep1610 ep1558

noncomputable def ep1631 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 626655127 4800000 0 1 Bool.false 3018244690177 720000000 0 1 ep1608

noncomputable def ep1632 := @Enclosure.Complex.IsNear.im_isNear qz244 Bool.true 8867234424819464853 ep1397 150575336819028085587301 ep1398 Bool.true 154332033400328427 75557863725914323419136 21449541349548995893307 ep1610

noncomputable def ep1633 := nat_lit 32237653330217017421131743

noncomputable def ep1634 := nat_lit 120892581961462917470617600000

noncomputable def ep1635 := nat_lit 13441465058493377414242776534989

noncomputable def ep1636 := nat_lit 408788585916625181752395437937210163200000

noncomputable def ep1637 := nat_lit 8921161073088684831467308616327

noncomputable def ep1638 := nat_lit 454473210825644844901704745830642277

noncomputable def ep1639 := @Enclosure.Real.IsNear.addLit_tt (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3)))) qz252) ep1633 ep1634 ep1635 ep1636 ep1637 ep1549 ep1638

noncomputable def ep1640 := nat_lit 1087855699773710676727440059429843704003057804152877875200000

noncomputable def ep1641 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253 626655127 4800000 0 1 154332033400328427 75557863725914323419136 21449541349548995893307 ep1610 ep1633

noncomputable def ep1642 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3)))) qz252 3018244690177 720000000 0 1 8867234424819464853 ep1397 150575336819028085587301 ep1398 ep1637

noncomputable abbrev qz530 := (@ep1612 ep1610 (BSN.cpow_neg_s_sub_mk qz152 144530 1000 29 3 17249876309 qz153 rfl EMRow50.d19) ep1629)

noncomputable def ep1643 := ep1553 (@ep1560 ep1561 ep1562 ep1544 ep1388 ep1545 ep1546 (@ep1563 ep1555 ep1556 ep1557 ep1609 (ep1611 qz530) rfl) (@ep1630 ep1480 ep1559 ep1561 ep1631 (ep1632 qz530) rfl) rfl rfl) (@ep1639 ep1552 ep1640 ep1548 ep1549 ep1550 ep1552 (@ep1641 ep1634 ep1635 ep1636 ep1609 (ep1632 qz530) rfl) (@ep1642 ep1549 ep1638 ep1552 ep1631 (ep1611 qz530) rfl) rfl rfl)

noncomputable def ep1644 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) ep1548 ep1549 ep1550 ep1552 ep1548 ep1549 ep1550

noncomputable def ep1645 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz244) Bool.false ep1544 ep1388 ep1545 ep1546 Bool.true ep1548 ep1549 ep1550

noncomputable def ep1646 := @ep1516 1330652191483761141 1008806316530991104 171742427771 1008806316530991104 (@ep1517 1 3670016 (ep1518 (@ep1519 1048576 1 1048576 (ep1520 (@ep1521 836046836 209011709 10000 0 1 (ep1525 rfl) (ep1528 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep1529 1075 274877906944 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (@ep1530 4300 1099511627776 8777671621 274877906944 1075 274877906944 (@ep1535 17555341092 17555345392 549755813888 (@ep1541 ep1532 ep1542 ep1534 ep1543 ep1531 ep1532 ep1533 ep1534 (@ep1547 ep1546 ep1536 ep1537 ep1538 ep1539 (@ep1551 ep1552 ep1643) (@ep1551 ep1552 ep1643) rfl) (@ep1644 ep1552 ep1540 ep1532 ep1542 ep1534 (@ep1645 ep1552 ep1643) (@ep1645 ep1552 ep1643) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow50.d21 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz412 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz149 1 29))) (@HMul.hMul Real Real Real qz0 qz243 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)))) Bool.false 37638756424981275863 27237770546336759808 2626623414463225 27237770546336759808 := ep1514 (ep1515 ep1646) rfl rfl

noncomputable def EMRow50.d22 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J))

noncomputable abbrev qz531 := (EMRow50.d3 qz546 qz595 (@Enclosure.dec_le_dec qz546 qz595 142522 1000 144530 1000 (@Eq.refl Real qz546) (@Eq.refl Real qz595) rfl rfl rfl) 29 29 1 1)

noncomputable abbrev qz262 := qz531

noncomputable def ep1647 := @Zeta.Certificates.ZIntervalEM.Certificate.mk qz262 (@Enclosure.dec_nonneg qz13 142522 1000 qz14) (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 29 rfl)

noncomputable abbrev qz263 := (Zeta.Certificates.ZIntervalEM.fstVal qz531)

noncomputable def ep1648 := @Enclosure.Real.IsNear.pos_val qz263 ep407 ep408

noncomputable def ep1649 := @Enclosure.Real.IsNear.of_eq qz263 (hardyZApproximantEM 1 29 qz13) Bool.false

noncomputable abbrev qz264 := (Zeta.Certificates.ZIntervalEM.sndVal qz531)

noncomputable def ep1650 := BSN.mul_neg_of_pos_neg_r qz263 qz264 (@ep1648 ep409 ep410 (@ep1649 ep407 ep408 ep409 ep410 (@Eq.refl Real (hardyZApproximantEM 1 29 qz13)) EMRow50.d11) rfl rfl rfl)

noncomputable def ep1651 := @Enclosure.Real.IsNear.neg_val qz264 ep1035 ep1036

noncomputable def ep1652 := @Enclosure.Real.IsNear.of_eq qz264 (hardyZApproximantEM 1 29 qz152) Bool.true

noncomputable def ep1653 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz263) (BSN.hardyZErrorBoundStrong 1 29 qz13)

noncomputable def ep1654 := @Enclosure.norm_gt_of_isNear qz263 (BSN.hardyZErrorBoundStrong 1 29 qz13) Bool.false

noncomputable def ep1655 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 29 qz13) (@HAdd.hAdd Real Real Real qz412 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 29))) (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)))) Bool.false 138435486598394633663 108951082185347039232 10418764854305737 108951082185347039232 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz412 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 29))) (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)))))

noncomputable def ep1656 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz264) (BSN.hardyZErrorBoundStrong 1 29 qz152)

noncomputable def ep1657 := @Enclosure.norm_gt_of_isNear qz264 (BSN.hardyZErrorBoundStrong 1 29 qz152) Bool.true

noncomputable def ep1658 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 29 qz152) (@HAdd.hAdd Real Real Real qz412 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz149 1 29))) (@HMul.hMul Real Real Real qz0 qz243 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)))) Bool.false 37638756424981275863 27237770546336759808 2626623414463225 27237770546336759808 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz412 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz149 1 29))) (@HMul.hMul Real Real Real qz0 qz243 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz73 (@HDiv.hDiv Complex Complex Complex qz80 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz149 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)))))

noncomputable def ep1659 := @List.cons EMRow50.d0 (@PSigma.mk Zeta.Certificates.ZIntervalEM Zeta.Certificates.ZIntervalEM.Certificate qz262 (ep1647 (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 29 rfl) (ep1650 (@ep1651 ep1037 ep1038 (@ep1652 ep1035 ep1036 ep1037 ep1038 (@Eq.refl Real (hardyZApproximantEM 1 29 qz152)) EMRow50.d15) rfl rfl rfl)) (ep1653 (hardyZErrorBoundEM 1 29 qz13) (BSN.hardyZErrorBoundEM_le_strong 1 29 qz13 rfl) (@ep1654 Bool.false ep407 ep408 ep409 ep410 138435486598394633663 108951082185347039232 10418764854305737 108951082185347039232 (@ep1649 ep407 ep408 ep409 ep410 (@Eq.refl Real (hardyZApproximantEM 1 29 qz13)) EMRow50.d11) (ep1655 EMRow50.d20) rfl rfl rfl rfl rfl)) (ep1656 (hardyZErrorBoundEM 1 29 qz152) (BSN.hardyZErrorBoundEM_le_strong 1 29 qz152 rfl) (@ep1657 Bool.false ep1035 ep1036 ep1037 ep1038 37638756424981275863 27237770546336759808 2626623414463225 27237770546336759808 (@ep1652 ep1035 ep1036 ep1037 ep1038 (@Eq.refl Real (hardyZApproximantEM 1 29 qz152)) EMRow50.d15) (ep1658 EMRow50.d21) rfl rfl rfl rfl rfl)))) (@List.nil EMRow50.d0)

noncomputable abbrev qz532 := (@Enclosure.dec_le_dec qz546 qz595 142522 1000 144530 1000 (@Eq.refl Real qz546) (@Eq.refl Real qz595) rfl rfl rfl)

noncomputable abbrev qz265 := (Zeta.Certificates.CertifiedZeroIntervals.intervals (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1659 (@List.IsChain.singleton EMRow50.d1 EMRow50.d22 (EMRow50.d2 qz278 qz452 qz532))))

noncomputable abbrev qz533 := (@NonemptyInterval Real Real.instLE)

noncomputable def ep1660 := And (@Eq (Option Real) (@Option.map qz533 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz533 qz265)) (@Option.some Real qz13))

noncomputable def ep1661 := ep1660 (@Eq (Option Real) (@Option.map qz533 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz533 qz265)) (@Option.some Real qz152))

noncomputable def ep1662 := @And.intro (@Eq Nat (@List.length qz533 qz265) 1) ep1661

noncomputable def ep1663 := @And.intro (@Eq (Option Real) (@Option.map qz533 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz533 qz265)) (@Option.some Real qz13))

noncomputable def ep1664 := @ep1663 (@Eq (Option Real) (@Option.map qz533 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz533 qz265)) (@Option.some Real qz152))

noncomputable abbrev qz266 := (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1659 (@List.IsChain.singleton EMRow50.d1 EMRow50.d22 (EMRow50.d2 qz278 qz452 qz532)))

theorem EMRow50.d23 : Zeta.Certificates.BatchSpec 1 142522 1000 144530 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz533 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 1) (And (@Eq (Option Real) (@Option.map qz533 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz533 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz13)) (@Eq (Option Real) (@Option.map qz533 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz533 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz152)))) qz266 (ep1662 (@Eq.refl Nat 1) (ep1664 (@Eq.refl (Option Real) (@Option.some Real qz13)) (@Eq.refl (Option Real) (@Option.some Real qz152))))

theorem solution : Zeta.Certificates.BatchSpec 1 142522 1000 144530 1000 := EMRow50.d23
#print axioms solution
#check solution
