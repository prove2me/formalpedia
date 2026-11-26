-- Prove2me | solution 1 for RHHeight1000.em_main_0043_0043
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T08:28:43.347585+00:00
-- url     : https://prove2.me/submissions/b64a42b2-1e61-4d04-8241-4df65f73c9cd

import Definitions.Def_RHT1000_Support_20261118_S005
/- Copyright (c) 2026 Salvatore Mercuri, Bhavik Mehta.
Apache 2.0 license; see the source project LICENSE. -/
set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def EMRow43.d0 := @PSigma Zeta.Certificates.ZIntervalEM fun (I : Zeta.Certificates.ZIntervalEM) => Zeta.Certificates.ZIntervalEM.Certificate I

noncomputable def EMRow43.d1 := @NonemptyInterval Real Real.instLE

noncomputable def EMRow43.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h

noncomputable def EMRow43.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) (fc sc fb sb : Nat) => Zeta.Certificates.ZIntervalEM.mk (EMRow43.d2 a b h) fc sc fb sb

noncomputable def ep0 := nat_lit 26986075409044028275299783

noncomputable def ep1 := nat_lit 4294967296000000000000000

noncomputable def ep2 := nat_lit 26986075409044045455168967

noncomputable abbrev qz267 := (@instHMul Real Real.instMul)

noncomputable abbrev qz0 := qz267

noncomputable abbrev qz268 := (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 2 1) Real.pi)

noncomputable def ep3 := @BSN.isNear_log_image_fff qz268 884279719003555 140737488355328 1 500000000000000 ep0 ep1 ep2 ep1 4138529546116343 2251799813685248 62500000048123 24061500000000000000 4138529546116343 2251799813685248 62500000048123 24061500000000000000 963576 524288

noncomputable abbrev qz269 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 2 1) Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) BSN.pi_near_15 rfl)

noncomputable def ep4 := @ep3 2 524288 qz269 rfl rfl rfl rfl

noncomputable def ep5 := nat_lit 53972150818088056550599566

noncomputable def ep6 := nat_lit 34359738368000000000000000

noncomputable def ep7 := nat_lit 9806206225044028275299783

noncomputable def ep8 := nat_lit 44165944593044028275299783

noncomputable def ep9 := nat_lit 13681445815609410487519367394620474863599256634174726093703677122907123617368241606644861540940610176751640793056574796245399519365549113997355475306157239709119582688278313060810592403844863400465080549957745

noncomputable def ep10 := nat_lit 231714499556395493334623298703961145503103241611736774613091488581016477543539392410113701224645713379230392133956226737605624599560350113120270717249177907454870984269546186598262646369758174842349131395304

noncomputable def ep11 := nat_lit 8978369550011295664474073352761810093897501552430546263638635096022803738134167562509900960712119243631997923545019968443113540909076206607473711060286601587364321108377403290080403445693385008949995305

noncomputable def ep12 := BSN.log_dyadic_bound ep7 ep8 5 4 ep9 1048576 384984 ep10 ep11 473518 ep5 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep7) (BSN.artanhQ ep8) 0 4 ep10 ep9 ep11 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz270 := (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))

noncomputable abbrev qz1 := qz270

noncomputable def ep13 := ep4 rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep1 4138529546116343 2251799813685248 62500000048123 24061500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep0) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 69433004117575847641088 37778931862957161709568 1000000000769968 384984000000000000000 4138529546116343 2251799813685248 62500000048123 24061500000000000000 (BSN.log_rat_reduce_isNear ep0 ep1 2 ep5 ep6 473518 1048576 24973259072661432 36028797018963968 384984 1000000000000000 rfl rfl rfl rfl (ep12 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep14 := nat_lit 53972150818088090910337934

noncomputable def ep15 := nat_lit 9806206225044045455168967

noncomputable def ep16 := nat_lit 44165944593044045455168967

noncomputable def ep17 := nat_lit 13681445815609453062485491347592146866046743284321690683909457683007658987562290830600045658905080811372395010565947827677605470036294121079488508864180301737865471494204890974265645509835068840465080549957745

noncomputable def ep18 := nat_lit 231714499556396865510889920206523150079811393376960301632499817942333196803513131357563499488546302200815366867712007119763002650772307103678175657719139104636874731038771518520299266622696414842349131395304

noncomputable def ep19 := nat_lit 8978369550011421500876706511871067098718760264493934208903156435737864998391937547068187824077011975074541700434630537294838404525415248443919841847024664017658842168336182958576672102333385008949995305

noncomputable def ep20 := BSN.log_dyadic_bound ep15 ep16 5 4 ep17 1048576 384984 ep18 ep19 473518 ep14 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep15) (BSN.artanhQ ep16) 0 4 ep18 ep17 ep19 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep21 := ep13 (BSN.isNear_log_sfrac ep2 ep1 4138529546116343 2251799813685248 62500000048123 24061500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep2) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 69433004117575847641088 37778931862957161709568 1000000000769968 384984000000000000000 4138529546116343 2251799813685248 62500000048123 24061500000000000000 (BSN.log_rat_reduce_isNear ep2 ep1 2 ep14 ep6 473518 1048576 24973259072661432 36028797018963968 384984 1000000000000000 rfl rfl rfl rfl (ep20 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable abbrev qz2 := (Real.log (@HMul.hMul Real Real Real qz267 (2 : Real) Real.pi))

theorem EMRow43.d4 : Enclosure.Real.IsNear qz2 Bool.false 120447 65536 1 262144 := @Enclosure.Real.IsNear.of_eq qz2 (Real.log qz268) Bool.false 120447 65536 1 262144 BSN.log_two_pi_eq (@Enclosure.Real.IsNear.recentre' (Real.log qz268) Bool.false 963576 524288 2 524288 120447 65536 1 262144 (ep21 rfl rfl rfl rfl rfl rfl rfl rfl) rfl)

noncomputable def ep22 := nat_lit 8589934592000000000000000

noncomputable def ep23 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 ep0 ep22 ep2 ep22 1200336 1048576 1 384984 1200336 1048576 1 384984 600168 524288 2 524288 BSN.pi_near_15 rfl rfl rfl

noncomputable def ep24 := nat_lit 17179869184000000000000000

noncomputable def ep25 := nat_lit 18396140817044028275299783

noncomputable def ep26 := nat_lit 35576010001044028275299783

noncomputable def ep27 := nat_lit 145019262663961446558303139663424756232419223153299357158415217874016130572233056993847515999529612750616182853355499335896178729185698845314776375864537073527142908641610750276034469165612529925303649396973267518946591078603565291376312767403717761600170009932259137778521478520425507632472584532570900560707662248426541531715360699177249902784721815296292248142738824858695953661559845440650653128788875447728828657762006237171740033404723254477174341920697506370253193455781322964835857351124092897592956162654178130575

noncomputable def ep28 := nat_lit 15500762873619990602332184736899274490522931101512051618692838888825382235673431503644115344741331161500627469184702974962114537943617674254904297224139410345221262767191485292268260077615645253784097850065864022184521411511133693085443040736512010941548648374196772723338837137976260321103066698629790037694560548409922339907589559883712609967105556007429010014773911317423638534096849366294542840133852248768895750397896505791271178551667935288585787166713880920071720072716082683081155281219708172458141800988558163320

noncomputable def ep29 := nat_lit 12900190794487083783367107939442176642390171280542213571554777169279725287102813254708993369099729304728646904879886535518616983985412662170766446331701281703998252143668221340329975389245922410714088123244705567402747658401492589451585970559635763980329972215329212888079422466283203384882259392047898400615815810081169907384366653346471604103896809335921621947903075223769953790093549808584241881353287841076643853121427928248525828402335494512605306631304432120211393210317325496757155861061354331245840675149075

noncomputable def ep30 := BSN.log_dyadic_bound ep25 ep26 11 10 ep27 1048576 384984 ep28 ep29 1200336 ep5 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep25) (BSN.artanhQ ep26) 0 10 ep28 ep27 ep29 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep31 := nat_lit 18396140817044045455168967

noncomputable def ep32 := nat_lit 35576010001044045455168967

noncomputable def ep33 := nat_lit 145019262663962847171784895425483977818796535899227200426399035286881207006285364467913811844950531107314785650583974625982406238691319033447632878979985852280879486690814033867010958364699188952871572448188560932645032521756218245629809291975913196623825614492380080480004685076434733043183791438169545293975334857826316990371107134320667652578346815517853870648072772035977941843998949310557583393428557296298890786965786350523173236912472938174255438182435383147950274229549088258679583524155427309880956162654178130575

noncomputable def ep34 := nat_lit 15500762873620157189619721156942591192100275120160672416764593300158228469749443299607348495591439275767946573253526107895503597951484257520435868240203420954375895980141891044871083424251900562230440202302413072793440172565998181227591194192658878334739610458454844032013325963992941389843551995646587189684848765634635122388286241104146031552341815777883628509454807838726994150833304950745987647656768534710890974432620160470644835720379148964170536679305861738540146791997074363921127776563807649880221800988558163320

noncomputable def ep35 := nat_lit 12900190794487324729109480814509220959173684627296055849229843377126536688487849343376525559792931631054411655715865486295286288812423905434305314401904993536755333953308594664509631000767632482919425633906965368325056855874260596615770736441041599390097968820060635361729170158825410327022636428624381203910573184452046894301676992229743752846881064485858738985580654099214803581683226335297196686880535448467637789069028262446657986458573827723305156755787640135484017403116612632808333639900906331245840675149075

noncomputable def ep36 := BSN.log_dyadic_bound ep31 ep32 11 10 ep33 1048576 384984 ep34 ep35 1200336 ep14 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep31) (BSN.artanhQ ep32) 0 10 ep34 ep33 ep35 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep37 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 600168 524288 2 524288 75021 65536 1 262144 (ep23 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep22 1200336 1048576 1 384984 Bool.false (BSN.logfrac_isNear ep5 ep24 1 ep0 ep22 1200336 1048576 384984 rfl rfl rfl (ep30 rfl))) (BSN.isNear_log_sfrac ep2 ep22 1200336 1048576 1 384984 Bool.false (BSN.logfrac_isNear ep14 ep24 1 ep2 ep22 1200336 1048576 384984 rfl rfl rfl (ep36 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl

theorem EMRow43.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 75021 65536 1 262144 := ep37

noncomputable abbrev qz651 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 128194 1000)))

noncomputable abbrev qz528 := qz651

noncomputable abbrev qz271 := qz528

noncomputable abbrev qz3 := (BSN.headSumC qz271 9)

noncomputable abbrev qz652 := (@instHAdd Complex Complex.instAdd)

noncomputable abbrev qz529 := qz652

noncomputable abbrev qz272 := qz529

noncomputable abbrev qz4 := qz272

noncomputable abbrev qz5 := qz271

noncomputable abbrev qz530 := (@instHPow Complex Complex Complex.instPow)

noncomputable abbrev qz273 := qz530

noncomputable abbrev qz6 := qz273

noncomputable abbrev qz531 := (@Neg.neg Complex Complex.instNeg qz651)

noncomputable abbrev qz274 := qz531

noncomputable abbrev qz7 := qz274

noncomputable abbrev qz532 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 8) qz7)

noncomputable def ep38 := @Enclosure.Complex.IsNear.of_eq qz3 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 8) qz532) Bool.false 71874769533 274877906944 10011543774991 4409316505288704 Bool.true 83381101039 137438953472 20027485911977 8818633010577408

noncomputable def ep39 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 8) qz532 Bool.false 635229511595 1099511627776 35841887786539 17637266021154816 Bool.true 123317817129 274877906944 17929105642295 8818633010577408 Bool.true

noncomputable abbrev qz533 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 7) qz7)

noncomputable def ep40 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 8) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 7) qz533) Bool.false 635229511595 1099511627776 35841887786539 17637266021154816 Bool.true 123317817129 274877906944 17929105642295 8818633010577408

noncomputable def ep41 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 7) qz533 Bool.false 379579178735 549755813888 47037558091343 26455899031732224 Bool.true 444969742983 549755813888 47045484911903 26455899031732224 Bool.true

noncomputable abbrev qz534 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 6) qz7)

noncomputable def ep42 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 7) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 6) qz534) Bool.false 379579178735 549755813888 47037558091343 26455899031732224 Bool.true 444969742983 549755813888 47045484911903 26455899031732224

noncomputable def ep43 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 6) qz534 Bool.false 1179819176479 1099511627776 26498420938211 17637266021154816 Bool.true 1046564602407 1099511627776 26513599445723 17637266021154816 Bool.true

noncomputable abbrev qz535 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 5) qz7)

noncomputable def ep44 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 6) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 5) qz535) Bool.false 1179819176479 1099511627776 26498420938211 17637266021154816 Bool.true 1046564602407 1099511627776 26513599445723 17637266021154816

noncomputable def ep45 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 5) qz535 Bool.false 462300341583 549755813888 15893004244627 13227949515866112 Bool.true 1466859705271 1099511627776 63600612098215 52911798063464448 Bool.false

noncomputable abbrev qz536 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 4) qz7)

noncomputable def ep46 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 5) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 4) qz536) Bool.false 462300341583 549755813888 15893004244627 13227949515866112 Bool.true 1466859705271 1099511627776 63600612098215 52911798063464448

noncomputable def ep47 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 4) qz536 Bool.false 260406696109 274877906944 22881309246703 26455899031732224 Bool.true 464852564715 549755813888 22876325532577 26455899031732224 Bool.true

noncomputable abbrev qz537 := (@Nat.cast Complex Complex.instNatCast 3)

noncomputable abbrev qz275 := qz537

noncomputable abbrev qz8 := qz275

noncomputable def ep48 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 4) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz7)) Bool.false 260406696109 274877906944 22881309246703 26455899031732224 Bool.true 464852564715 549755813888 22876325532577 26455899031732224

noncomputable def ep49 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz7) Bool.false 1587330442831 1099511627776 2796345472051 5879088673718272 Bool.true 605388368585 1099511627776 2797193324453 5879088673718272 Bool.true

noncomputable abbrev qz538 := (@Nat.cast Complex Complex.instNatCast 2)

noncomputable abbrev qz276 := qz538

noncomputable abbrev qz9 := qz276

noncomputable def ep50 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 3) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz7)) Bool.false 1587330442831 1099511627776 2796345472051 5879088673718272 Bool.true 605388368585 1099511627776 2797193324453 5879088673718272

noncomputable def ep51 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz7) Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz277 := (Enclosure.sfrac Bool.false 0 1)

noncomputable abbrev qz10 := qz277

noncomputable def ep52 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz10) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz5)

noncomputable abbrev qz653 := (Enclosure.sfrac Bool.false 128194 1000)

noncomputable abbrev qz539 := qz653

noncomputable abbrev qz278 := qz539

noncomputable abbrev qz279 := (Real.log (Enclosure.sfrac Bool.false 2 1))

noncomputable abbrev qz11 := (@HMul.hMul Real Real Real qz267 qz278 qz279)

noncomputable abbrev qz12 := qz278

noncomputable abbrev qz280 := (@Eq.refl Real qz539)

noncomputable abbrev qz13 := qz280

noncomputable abbrev qz281 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2)))

noncomputable def ep53 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz9 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz281 (Real.cos qz11)) (@HMul.hMul Real Real Real qz0 qz281 (@Neg.neg Real Real.instNeg (Real.sin qz11)))) Bool.false 487818815055 1099511627776 2796345472051 5879088673718272 Bool.true 605388368585 1099511627776 2797193324453 5879088673718272 (BSN.cpow_neg_s_mk qz12 128194 1000 2 qz13 rfl)

noncomputable abbrev qz14 := (@Nat.cast Real Real.instNatCast 1)

noncomputable abbrev qz282 := (Real.sqrt (@Nat.cast Real Real.instNatCast 2))

noncomputable abbrev qz283 := (@Nat.cast Real Real.instNatCast 2)

noncomputable def ep54 := @Enclosure.Real.IsNear.inv_image qz282 1482911 1048576 1 1048576 370727 370728 524288 (@Enclosure.Real.IsNear.of_eq qz282 (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz283 qz14)) Bool.false 1482911 1048576 1 1048576 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz283 qz14)) Bool.false 1482911 1048576 1 1048576 1482911 1048576 1 1048576 (BSN.sqrt_enclosure 2 1 741455 741456 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep55 := BSN.log_dyadic_bound 1 3 6 5 613814355 524288 192492 24381081 945 363408 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 1) (BSN.artanhQ 3) 0 5 24381081 613814355 945 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep56 := nat_lit 482399978991659211785040281693601139610630501379006914074197693788887906779136

noncomputable def ep57 := nat_lit 18237254054877300779212430138868345486890022584838388836214569481246317918289920

noncomputable def ep58 := nat_lit 182149942680904595086931320042174755992541871846653020492764745046012461056

noncomputable def ep59 := nat_lit 1446835637089615826164946982440719069319906420393327436181607551876571695415296

noncomputable def ep60 := nat_lit 820676432469478535064559356249075546910051016317727497629655626656084306323046400

noncomputable abbrev qz15 := (BSN.cosEvenQ 2147483648)

noncomputable abbrev qz16 := (BSN.cosOddQ 2147483648)

noncomputable def ep61 := BSN.cos_dyadic_bound_f 1916697736 2147483648 3 2 1048576 385360 ep56 ep57 ep58 ep59 ep60 ep58 657921 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1916697736) qz15 0 2 ep56 ep57 ep58 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1916697736) qz16 0 2 ep59 ep60 ep58 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz17 := (@Nat.cast Real Real.instNatCast 524288)

noncomputable abbrev qz18 := (Enclosure.Real.IsNear.const Bool.false 128194 1000)

noncomputable abbrev qz19 := (@Nat.cast Real Real.instNatCast 75557863725914323419136)

noncomputable abbrev qz284 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 46586725) qz17)

noncomputable abbrev qz285 := (BSN.isNear_log_sfrac 2 1 363408 524288 1 192492 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 363408 524288 192492 rfl rfl rfl (ep55 rfl)))

noncomputable def ep62 := @Enclosure.Real.IsNear.cos_image qz11 qz284 Bool.false 46586725 524288 699 1048576 Bool.false 657921 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz11 Bool.false 1455835161 16384000 64097 96246000 46586725 524288 699 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz12 qz279 128194 1000 0 1 363408 524288 1 192492 1455835161 16384000 64097 96246000 qz18 qz285 rfl) rfl) (Enclosure.sfrac_false_div 46586725 524288) (BSN.cos_reduce0 qz284 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 67437806349584391208960) qz19) 226375608064910080 72057594037927936 Bool.false 657921 1048576 14 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q0 46586725 524288 226375608064910080 72057594037927936 14 67437806349584391208960 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 657921 1048576 67437806349584391208960 75557863725914323419136 1916697736 2147483648 385360 384984 (ep61 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep63 := nat_lit 868174242230841857537002961992448311494340868984735122917161637023961422233600

noncomputable def ep64 := nat_lit 164135286493895707012911871249815109382010203263545499525931125331216861264609280

noncomputable def ep65 := nat_lit 2273494772602150067062009868795391580499285779548459312273673144523157799960576

noncomputable def ep66 := nat_lit 3009146919054754628570050972913277005336853726498334157975403964405642456517836800

noncomputable abbrev qz20 := (BSN.sinEvenQ 2147483648)

noncomputable abbrev qz21 := (BSN.sinOddQ 2147483648)

noncomputable def ep67 := BSN.sin_dyadic_bound_f 1916697736 2147483648 3 2 1048576 385360 ep63 ep64 ep58 ep65 ep66 ep58 816487 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1916697736) qz20 0 2 ep63 ep64 ep58 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1916697736) qz21 0 2 ep65 ep66 ep58 rfl rfl rfl rfl) rfl rfl

noncomputable def ep68 := @Enclosure.Real.IsNear.sin_image qz11 qz284 Bool.false 46586725 524288 699 1048576 Bool.false 816487 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz11 Bool.false 1455835161 16384000 64097 96246000 46586725 524288 699 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz12 qz279 128194 1000 0 1 363408 524288 1 192492 1455835161 16384000 64097 96246000 qz18 qz285 rfl) rfl) (Enclosure.sfrac_false_div 46586725 524288) (BSN.sin_reduce0 qz284 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 67437806349584391208960) qz19) 226375608064910080 72057594037927936 Bool.false 816487 1048576 14 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q0 46586725 524288 226375608064910080 72057594037927936 14 67437806349584391208960 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 816487 1048576 67437806349584391208960 75557863725914323419136 1916697736 2147483648 385360 384984 (ep67 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz286 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2))) Bool.false 741455 1048576 1 1048576 741455 1048576 1 1048576 (ep54 rfl rfl) rfl)

noncomputable def ep69 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz281 (Real.cos qz11)) (@HMul.hMul Real Real Real qz0 qz281 (@Neg.neg Real Real.instNeg (Real.sin qz11))) Bool.false 487818815055 1099511627776 2796345472051 5879088673718272 Bool.true 605388368585 1099511627776 2797193324453 5879088673718272 (@Enclosure.Real.IsNear.mulLit_ff qz281 (Real.cos qz11) 741455 1048576 1 1048576 657921 1048576 33900121 50460622848 487818815055 1099511627776 2796345472051 5879088673718272 qz286 (@Enclosure.Real.IsNear.recentre' (Real.cos qz11) Bool.false 657921 1048576 135600484 201842491392 657921 1048576 33900121 50460622848 (ep62 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz281 (@Neg.neg Real Real.instNeg (Real.sin qz11)) 741455 1048576 1 1048576 816487 1048576 33900121 50460622848 605388368585 1099511627776 2797193324453 5879088673718272 qz286 (@Enclosure.Real.IsNear.neg (Real.sin qz11) Bool.false 816487 1048576 33900121 50460622848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz11) Bool.false 816487 1048576 135600484 201842491392 816487 1048576 33900121 50460622848 (ep68 rfl rfl) rfl)) rfl)

noncomputable abbrev qz287 := (Enclosure.Real.IsNear.const Bool.false 0 1)

noncomputable abbrev qz22 := qz287

noncomputable def ep70 := @ep51 487818815055 1099511627776 2796345472051 5879088673718272 Bool.true 605388368585 1099511627776 2797193324453 5879088673718272 Bool.false 1587330442831 1587330442831 1099511627776 2796345472051 5879088673718272 Bool.true 605388368585 605388368585 1099511627776 2797193324453 5879088673718272 (ep52 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz10 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz22)) (ep53 ep69) rfl rfl

noncomputable abbrev qz288 := (Real.log (Enclosure.sfrac Bool.false 3 1))

noncomputable abbrev qz23 := (@HMul.hMul Real Real Real qz267 qz278 qz288)

noncomputable abbrev qz289 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 3)))

noncomputable def ep71 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz8 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz289 (Real.cos qz23)) (@HMul.hMul Real Real Real qz0 qz289 (@Neg.neg Real Real.instNeg (Real.sin qz23)))) Bool.true 545703658395 1099511627776 20595509244947 52911798063464448 Bool.true 324316760845 1099511627776 20577911145077 52911798063464448 (BSN.cpow_neg_s_mk qz12 128194 1000 3 qz13 rfl)

noncomputable abbrev qz290 := (Real.sqrt (@Nat.cast Real Real.instNatCast 3))

noncomputable abbrev qz291 := (@Nat.cast Real Real.instNatCast 3)

noncomputable def ep72 := @Enclosure.Real.IsNear.inv_image qz290 1816187 1048576 1 1048576 302697 302698 524288 (@Enclosure.Real.IsNear.of_eq qz290 (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz291 qz14)) Bool.false 1816187 1048576 1 1048576 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz291 qz14)) Bool.false 1816187 1048576 1 1048576 1816187 1048576 1 1048576 (BSN.sqrt_enclosure 3 1 908093 908094 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep73 := BSN.log_dyadic_bound 1 2 10 9 171633298636800 524288 192492 16925142283965 34459425 575989 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP 1) (BSN.artanhQ 2) 0 9 16925142283965 171633298636800 34459425 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep74 := nat_lit 1567570297906400496407423662424762759756383072339497423473097921665226222240000

noncomputable def ep75 := nat_lit 593639179887460618999924396376214999889270425183869355257865926672100000000

noncomputable def ep76 := nat_lit 4104580126320754935302966857327864784600230180200766987282934202384790039200000

noncomputable def ep77 := BSN.sin_dyadic_bound_f 2221725090 2147483648 3 2 1048576 385360 ep74 ep64 ep75 ep76 ep66 ep75 901401 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2221725090) qz20 0 2 ep74 ep64 ep75 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2221725090) qz21 0 2 ep76 ep66 ep75 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz24 := (@Nat.cast Real Real.instNatCast 1048576)

noncomputable abbrev qz25 := (@Nat.cast Real Real.instNatCast 151115727451828646838272)

noncomputable abbrev qz292 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 147676667) qz24)

noncomputable abbrev qz293 := (BSN.isNear_log_sfrac 3 1 575989 524288 1 192492 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 575989 524288 192492 rfl rfl rfl (ep73 rfl)))

noncomputable def ep78 := @Enclosure.Real.IsNear.cos_image qz23 qz292 Bool.false 147676667 1048576 175 262144 Bool.true 901401 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz23 Bool.false 36919166933 262144000 64097 96246000 147676667 1048576 175 262144 (@Enclosure.Real.IsNear.mulLit_ff qz12 qz288 128194 1000 0 1 575989 524288 1 192492 36919166933 262144000 64097 96246000 qz18 qz293 rfl) rfl) (Enclosure.sfrac_false_div 147676667 1048576) (BSN.cos_reduce1 qz292 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 156340004518405817237504) qz25) 226375608064910080 72057594037927936 Bool.false 901401 1048576 22 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q1 147676667 1048576 226375608064910080 72057594037927936 22 156340004518405817237504 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 901401 1048576 156340004518405817237504 151115727451828646838272 2221725090 2147483648 385360 384984 (ep77 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep79 := nat_lit 871136227361283591612568667745479850975719160377580288309613452448091056800000

noncomputable def ep80 := nat_lit 2612221403724075853599706154443687122927378940282373126218324625490928970400000

noncomputable def ep81 := BSN.cos_dyadic_bound_f 2221725090 2147483648 3 2 1048576 385360 ep79 ep57 ep75 ep80 ep60 ep75 535711 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2221725090) qz15 0 2 ep79 ep57 ep75 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2221725090) qz16 0 2 ep80 ep60 ep75 rfl rfl rfl rfl) rfl rfl

noncomputable def ep82 := @Enclosure.Real.IsNear.sin_image qz23 qz292 Bool.false 147676667 1048576 175 262144 Bool.false 535711 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz23 Bool.false 36919166933 262144000 64097 96246000 147676667 1048576 175 262144 (@Enclosure.Real.IsNear.mulLit_ff qz12 qz288 128194 1000 0 1 575989 524288 1 192492 36919166933 262144000 64097 96246000 qz18 qz293 rfl) rfl) (Enclosure.sfrac_false_div 147676667 1048576) (BSN.sin_reduce1 qz292 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 156340004518405817237504) qz25) 226375608064910080 72057594037927936 Bool.false 535711 1048576 22 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q1 147676667 1048576 226375608064910080 72057594037927936 22 156340004518405817237504 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 535711 1048576 156340004518405817237504 151115727451828646838272 2221725090 2147483648 385360 384984 (ep81 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz294 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 3))) Bool.false 605395 1048576 1 1048576 605395 1048576 1 1048576 (ep72 rfl rfl) rfl)

noncomputable def ep83 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz289 (Real.cos qz23)) (@HMul.hMul Real Real Real qz0 qz289 (@Neg.neg Real Real.instNeg (Real.sin qz23))) Bool.true 545703658395 1099511627776 20595509244947 52911798063464448 Bool.true 324316760845 1099511627776 20577911145077 52911798063464448 (@Enclosure.Real.IsNear.mulLit_ft qz289 (Real.cos qz23) 605395 1048576 1 1048576 901401 1048576 8487061 12615155712 545703658395 1099511627776 20595509244947 52911798063464448 qz294 (@Enclosure.Real.IsNear.recentre' (Real.cos qz23) Bool.true 901401 1048576 33948244 50460622848 901401 1048576 8487061 12615155712 (ep78 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz289 (@Neg.neg Real Real.instNeg (Real.sin qz23)) 605395 1048576 1 1048576 535711 1048576 8487061 12615155712 324316760845 1099511627776 20577911145077 52911798063464448 qz294 (@Enclosure.Real.IsNear.neg (Real.sin qz23) Bool.false 535711 1048576 8487061 12615155712 (@Enclosure.Real.IsNear.recentre' (Real.sin qz23) Bool.false 535711 1048576 33948244 50460622848 535711 1048576 8487061 12615155712 (ep82 rfl rfl) rfl)) rfl)

noncomputable def ep84 := @ep49 545703658395 1099511627776 20595509244947 52911798063464448 Bool.true 324316760845 1099511627776 20577911145077 52911798063464448 Bool.false 1145280761290307022094336 260406696109 274877906944 22881309246703 26455899031732224 Bool.true 1022221600211276063047680 464852564715 549755813888 22876325532577 26455899031732224 (ep50 (BSN.head_sum_c_succ qz5 2 3 rfl rfl) (ep70 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep71 ep83) rfl rfl

noncomputable abbrev qz295 := (Real.log (Enclosure.sfrac Bool.false 4 1))

noncomputable abbrev qz26 := (@HMul.hMul Real Real Real qz267 qz278 qz295)

noncomputable abbrev qz296 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 4)))

noncomputable def ep85 := @Enclosure.Complex.IsNear.of_eq qz536 (Complex.mk (@HMul.hMul Real Real Real qz0 qz296 (Real.cos qz26)) (@HMul.hMul Real Real Real qz0 qz296 (@Neg.neg Real Real.instNeg (Real.sin qz26)))) Bool.true 58513050635 549755813888 8904699242551 26455899031732224 Bool.true 537154575841 1099511627776 17847961033061 52911798063464448 (BSN.cpow_neg_s_mk qz12 128194 1000 4 qz13 rfl)

noncomputable abbrev qz297 := (Real.sqrt (@Nat.cast Real Real.instNatCast 4))

noncomputable abbrev qz298 := (@Nat.cast Real Real.instNatCast 4)

noncomputable def ep86 := @Enclosure.Real.IsNear.inv_image qz297 2097153 1048576 1 1048576 262143 262144 524288 (@Enclosure.Real.IsNear.of_eq qz297 (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz298 qz14)) Bool.false 2097153 1048576 1 1048576 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz298 qz14)) Bool.false 2097153 1048576 1 1048576 2097153 1048576 1 1048576 (BSN.sqrt_enclosure 4 1 1048576 1048577 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep87 := nat_lit 318077276165597140789031982421875

noncomputable def ep88 := nat_lit 49379992292270016474244603430625

noncomputable def ep89 := nat_lit 20095619060363156210525625

noncomputable def ep90 := BSN.log_dyadic_bound 3 5 14 13 ep87 524288 192492 ep88 ep89 726817 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base13 (BSN.artanhP 3) (BSN.artanhQ 5) 0 13 ep88 ep87 ep89 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep91 := nat_lit 45032211599548294205346014384450625

noncomputable def ep92 := nat_lit 2552117751907038475975309555738261585920

noncomputable def ep93 := nat_lit 17864824263349269331827166890167831101440

noncomputable def ep94 := BSN.sin_dyadic_bound_f 460660335 2147483648 2 1 1048576 385360 ep91 ep92 ep91 ep91 ep93 ep91 223210 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 460660335) qz20 0 1 ep91 ep92 ep91 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 460660335) qz21 0 1 ep91 ep93 ep91 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz299 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 46586789) (@Nat.cast Real Real.instNatCast 262144))

noncomputable abbrev qz300 := (BSN.isNear_log_sfrac 4 1 726817 524288 1 192492 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 726817 524288 192492 rfl rfl rfl (ep90 rfl)))

noncomputable abbrev qz301 := (@Nat.cast Real Real.instNatCast 37778931862957161709568)

noncomputable def ep95 := @Enclosure.Real.IsNear.cos_image qz26 qz299 Bool.false 46586789 262144 175 262144 Bool.true 223210 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz26 Bool.false 46586789249 262144000 64097 96246000 46586789 262144 175 262144 (@Enclosure.Real.IsNear.mulLit_ff qz12 qz295 128194 1000 0 1 726817 524288 1 192492 46586789249 262144000 64097 96246000 qz18 qz300 rfl) rfl) (Enclosure.sfrac_false_div 46586789 262144) (BSN.cos_reduce1 qz299 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8104022321053457973248) qz301) 226375608064910080 72057594037927936 Bool.false 223210 1048576 28 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q1 46586789 262144 226375608064910080 72057594037927936 28 8104022321053457973248 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 223210 1048576 8104022321053457973248 37778931862957161709568 460660335 2147483648 385360 384984 (ep94 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep96 := nat_lit 510423550381407695195061911147652317184

noncomputable def ep97 := nat_lit 7656353255721115427925928667214784757760

noncomputable def ep98 := BSN.cos_dyadic_bound_f 460660335 2147483648 2 1 1048576 385360 ep91 ep96 ep91 ep91 ep97 ep91 1024543 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 460660335) qz15 0 1 ep91 ep96 ep91 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 460660335) qz16 0 1 ep91 ep97 ep91 rfl rfl rfl rfl) rfl rfl

noncomputable def ep99 := @Enclosure.Real.IsNear.sin_image qz26 qz299 Bool.false 46586789 262144 175 262144 Bool.false 1024543 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz26 Bool.false 46586789249 262144000 64097 96246000 46586789 262144 175 262144 (@Enclosure.Real.IsNear.mulLit_ff qz12 qz295 128194 1000 0 1 726817 524288 1 192492 46586789249 262144000 64097 96246000 qz18 qz300 rfl) rfl) (Enclosure.sfrac_false_div 46586789 262144) (BSN.sin_reduce1 qz299 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8104022321053457973248) qz301) 226375608064910080 72057594037927936 Bool.false 1024543 1048576 28 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q1 46586789 262144 226375608064910080 72057594037927936 28 8104022321053457973248 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1024543 1048576 8104022321053457973248 37778931862957161709568 460660335 2147483648 385360 384984 (ep98 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz302 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 4))) Bool.false 524287 1048576 1 1048576 524287 1048576 1 1048576 (ep86 rfl rfl) rfl)

noncomputable def ep100 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz296 (Real.cos qz26)) (@HMul.hMul Real Real Real qz0 qz296 (@Neg.neg Real Real.instNeg (Real.sin qz26))) Bool.true 58513050635 549755813888 8904699242551 26455899031732224 Bool.true 537154575841 1099511627776 17847961033061 52911798063464448 (@Enclosure.Real.IsNear.mulLit_ft qz296 (Real.cos qz26) 524287 1048576 1 1048576 111605 524288 8487061 12615155712 58513050635 549755813888 8904699242551 26455899031732224 qz302 (@Enclosure.Real.IsNear.recentre' (Real.cos qz26) Bool.true 223210 1048576 33948244 50460622848 111605 524288 8487061 12615155712 (ep95 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz296 (@Neg.neg Real Real.instNeg (Real.sin qz26)) 524287 1048576 1 1048576 1024543 1048576 8487061 12615155712 537154575841 1099511627776 17847961033061 52911798063464448 qz302 (@Enclosure.Real.IsNear.neg (Real.sin qz26) Bool.false 1024543 1048576 8487061 12615155712 (@Enclosure.Real.IsNear.recentre' (Real.sin qz26) Bool.false 1024543 1048576 33948244 50460622848 1024543 1048576 8487061 12615155712 (ep99 rfl rfl) rfl)) rfl)

noncomputable def ep101 := @ep47 58513050635 549755813888 8904699242551 26455899031732224 Bool.true 537154575841 1099511627776 17847961033061 52911798063464448 Bool.false 127076150273831287652352 462300341583 549755813888 15893004244627 13227949515866112 Bool.true 806414651130770408603648 1466859705271 1099511627776 63600612098215 52911798063464448 (ep48 (BSN.head_sum_c_succ qz5 3 4 rfl rfl) (ep84 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep85 ep100) rfl rfl

noncomputable abbrev qz540 := (Real.log (Enclosure.sfrac Bool.false 5 1))

noncomputable abbrev qz27 := (@HMul.hMul Real Real Real qz267 qz278 qz540)

noncomputable abbrev qz303 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 5)))

noncomputable def ep102 := @Enclosure.Complex.IsNear.of_eq qz535 (Complex.mk (@HMul.hMul Real Real Real qz0 qz303 (Real.cos qz27)) (@HMul.hMul Real Real Real qz0 qz303 (@Neg.neg Real Real.instNeg (Real.sin qz27)))) Bool.false 255218493313 1099511627776 15923245836125 52911798063464448 Bool.false 26268443929 68719476736 7970093119477 26455899031732224 (BSN.cpow_neg_s_mk qz12 128194 1000 5 qz13 rfl)

noncomputable abbrev qz304 := (Real.sqrt (@Nat.cast Real Real.instNatCast 5))

noncomputable abbrev qz305 := (@Nat.cast Real Real.instNatCast 5)

noncomputable def ep103 := @Enclosure.Real.IsNear.inv_image qz304 2344687 1048576 1 1048576 234468 234469 524288 (@Enclosure.Real.IsNear.of_eq qz304 (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz305 qz14)) Bool.false 2344687 1048576 1 1048576 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz305 qz14)) Bool.false 2344687 1048576 1 1048576 2344687 1048576 1 1048576 (BSN.sqrt_enclosure 5 1 1172343 1172344 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep104 := nat_lit 3696382175741467532940033205863946875

noncomputable def ep105 := nat_lit 765440954430599474856563326857688500

noncomputable def ep106 := nat_lit 108794268166472120024432640000

noncomputable def ep107 := BSN.log_dyadic_bound 2 3 18 17 ep104 524288 192492 ep105 ep106 843808 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.artanhP 2) (BSN.artanhQ 3) 0 17 8 307084260767580 1483365253795425 132843110400 1663129201793174588340 2491889415829100854875 818968088287641600 ep105 ep104 ep106 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.artanhP 2) (BSN.artanhQ 3) 0 8 307084260767580 1483365253795425 132843110400 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.artanhP 2) (BSN.artanhQ 3) 8 17 1663129201793174588340 2491889415829100854875 818968088287641600 rfl rfl rfl rfl)) rfl rfl

noncomputable def ep108 := nat_lit 1886301192762191662396826140863369216

noncomputable def ep109 := BSN.sin_dyadic_bound_f 1171932936 2147483648 2 1 1048576 385360 ep108 ep92 ep108 ep108 ep93 ep108 544249 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1171932936) qz20 0 1 ep108 ep92 ep108 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1171932936) qz21 0 1 ep108 ep93 ep108 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz306 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 216342245) qz24)

noncomputable abbrev qz307 := (BSN.isNear_log_sfrac 5 1 843808 524288 1 192492 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 843808 524288 192492 rfl rfl rfl (ep107 rfl rfl)))

noncomputable def ep110 := @Enclosure.Real.IsNear.cos_image qz27 qz306 Bool.false 216342245 1048576 699 1048576 Bool.false 544249 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz27 Bool.false 1690173793 8192000 64097 96246000 216342245 1048576 699 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz12 qz540 128194 1000 0 1 843808 524288 1 192492 1690173793 8192000 64097 96246000 qz18 qz307 rfl) rfl) (Enclosure.sfrac_false_div 216342245 1048576) (BSN.cos_reduce3 qz306 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 82467449030368726876160) qz25) 226375608064910080 72057594037927936 Bool.false 544249 1048576 32 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q3 216342245 1048576 226375608064910080 72057594037927936 32 82467449030368726876160 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 544249 1048576 82467449030368726876160 151115727451828646838272 1171932936 2147483648 385360 384984 (ep109 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep111 := BSN.cos_dyadic_bound_f 1171932936 2147483648 2 1 1048576 385360 ep108 ep96 ep108 ep108 ep97 ep108 896272 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1171932936) qz15 0 1 ep108 ep96 ep108 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1171932936) qz16 0 1 ep108 ep97 ep108 rfl rfl rfl rfl) rfl rfl

noncomputable def ep112 := @Enclosure.Real.IsNear.sin_image qz27 qz306 Bool.false 216342245 1048576 699 1048576 Bool.true 896272 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz27 Bool.false 1690173793 8192000 64097 96246000 216342245 1048576 699 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz12 qz540 128194 1000 0 1 843808 524288 1 192492 1690173793 8192000 64097 96246000 qz18 qz307 rfl) rfl) (Enclosure.sfrac_false_div 216342245 1048576) (BSN.sin_reduce3 qz306 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 82467449030368726876160) qz25) 226375608064910080 72057594037927936 Bool.false 896272 1048576 32 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q3 216342245 1048576 226375608064910080 72057594037927936 32 82467449030368726876160 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 896272 1048576 82467449030368726876160 151115727451828646838272 1171932936 2147483648 385360 384984 (ep111 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz308 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 5))) Bool.false 468937 1048576 1 1048576 468937 1048576 1 1048576 (ep103 rfl rfl) rfl)

noncomputable def ep113 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz303 (Real.cos qz27)) (@HMul.hMul Real Real Real qz0 qz303 (@Neg.neg Real Real.instNeg (Real.sin qz27))) Bool.false 255218493313 1099511627776 15923245836125 52911798063464448 Bool.false 26268443929 68719476736 7970093119477 26455899031732224 (@Enclosure.Real.IsNear.mulLit_ff qz303 (Real.cos qz27) 468937 1048576 1 1048576 544249 1048576 33900121 50460622848 255218493313 1099511627776 15923245836125 52911798063464448 qz308 (@Enclosure.Real.IsNear.recentre' (Real.cos qz27) Bool.false 544249 1048576 135600484 201842491392 544249 1048576 33900121 50460622848 (ep110 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz303 (@Neg.neg Real Real.instNeg (Real.sin qz27)) 468937 1048576 1 1048576 56017 65536 33900121 50460622848 26268443929 68719476736 7970093119477 26455899031732224 qz308 (@Enclosure.Real.IsNear.neg (Real.sin qz27) Bool.true 56017 65536 33900121 50460622848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz27) Bool.true 896272 1048576 135600484 201842491392 56017 65536 33900121 50460622848 (ep112 rfl rfl) rfl)) rfl)

noncomputable def ep114 := @ep45 255218493313 1099511627776 15923245836125 52911798063464448 Bool.false 26268443929 68719476736 7970093119477 26455899031732224 Bool.false 648612451605882551140352 1179819176479 1099511627776 26498420938211 17637266021154816 Bool.true 71919371847828926103552 1046564602407 1099511627776 26513599445723 17637266021154816 (ep46 (BSN.head_sum_c_succ qz5 4 5 rfl rfl) (ep101 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep102 ep113) rfl rfl

noncomputable abbrev qz541 := (Real.log (Enclosure.sfrac Bool.false 6 1))

noncomputable abbrev qz28 := (@HMul.hMul Real Real Real qz267 qz278 qz541)

noncomputable abbrev qz309 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 6)))

noncomputable def ep115 := @Enclosure.Complex.IsNear.of_eq qz534 (Complex.mk (@HMul.hMul Real Real Real qz0 qz309 (Real.cos qz28)) (@HMul.hMul Real Real Real qz0 qz309 (@Neg.neg Real Real.instNeg (Real.sin qz28)))) Bool.true 420660819009 1099511627776 14579853368053 52911798063464448 Bool.false 156625116441 1099511627776 14550171486637 52911798063464448 (BSN.cpow_neg_s_mk qz12 128194 1000 6 qz13 rfl)

noncomputable abbrev qz310 := (Real.sqrt (@Nat.cast Real Real.instNatCast 6))

noncomputable abbrev qz311 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6) qz14)

noncomputable def ep116 := @Enclosure.Real.IsNear.inv_image qz310 2568477 1048576 1 1048576 214039 214040 524288 (@Enclosure.Real.IsNear.of_eq qz310 (Real.sqrt qz311) Bool.false 2568477 1048576 1 1048576 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz311) Bool.false 2568477 1048576 1 1048576 2568477 1048576 1 1048576 (BSN.sqrt_enclosure 6 1 1284238 1284239 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep117 := BSN.log_dyadic_bound 2 10 4 3 105000000 524288 192492 1434560 960 212580 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 2) (BSN.artanhQ 10) 0 3 1434560 105000000 960 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep118 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz541 128194 1000 0 1 4034681531866359 2251799813685248 125000000048123 24061500000000000000 258610982148038012823 1125899906842624000 8012125003084539931 12030750000000000000000 qz18 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 125000000048123 24061500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz311) Bool.false 33845361775666394038272 18889465931478580854784 1000000000384984 192492000000000000000 4034681531866359 2251799813685248 125000000048123 24061500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 212580 524288 24973259072661432 36028797018963968 192492 1000000000000000 rfl rfl rfl rfl (ep117 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep119 := nat_lit 343250996024563912014150312230916096

noncomputable def ep120 := BSN.cos_dyadic_bound_f 765425544 2147483648 2 1 1048576 385360 ep119 ep96 ep119 ep119 ep97 ep119 982671 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 765425544) qz15 0 1 ep119 ep96 ep119 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 765425544) qz16 0 1 ep119 ep97 ep119 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz312 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 240850245) qz24)

noncomputable def ep121 := @Enclosure.Real.IsNear.cos_image qz28 qz312 Bool.false 240850245 1048576 175 262144 Bool.true 982671 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz28 Bool.false 258610982148038012823 1125899906842624000 8012125003084539931 12030750000000000000000 240850245 1048576 175 262144 (ep118 rfl) rfl) (Enclosure.sfrac_false_div 240850245 1048576) (BSN.cos_reduce2 qz312 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 53862034359377157160960) qz25) 226375608064910080 72057594037927936 Bool.false 982671 1048576 36 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q2 240850245 1048576 226375608064910080 72057594037927936 36 53862034359377157160960 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 982671 1048576 53862034359377157160960 151115727451828646838272 765425544 2147483648 385360 384984 (ep120 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep122 := BSN.sin_dyadic_bound_f 765425544 2147483648 2 1 1048576 385360 ep119 ep92 ep119 ep119 ep93 ep119 365879 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 765425544) qz20 0 1 ep119 ep92 ep119 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 765425544) qz21 0 1 ep119 ep93 ep119 rfl rfl rfl rfl) rfl rfl

noncomputable def ep123 := @Enclosure.Real.IsNear.sin_image qz28 qz312 Bool.false 240850245 1048576 175 262144 Bool.true 365879 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz28 Bool.false 258610982148038012823 1125899906842624000 8012125003084539931 12030750000000000000000 240850245 1048576 175 262144 (ep118 rfl) rfl) (Enclosure.sfrac_false_div 240850245 1048576) (BSN.sin_reduce2 qz312 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 53862034359377157160960) qz25) 226375608064910080 72057594037927936 Bool.false 365879 1048576 36 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q2 240850245 1048576 226375608064910080 72057594037927936 36 53862034359377157160960 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 365879 1048576 53862034359377157160960 151115727451828646838272 765425544 2147483648 385360 384984 (ep122 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz313 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 6))) Bool.false 428079 1048576 1 1048576 428079 1048576 1 1048576 (ep116 rfl rfl) rfl)

noncomputable def ep124 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz309 (Real.cos qz28)) (@HMul.hMul Real Real Real qz0 qz309 (@Neg.neg Real Real.instNeg (Real.sin qz28))) Bool.true 420660819009 1099511627776 14579853368053 52911798063464448 Bool.false 156625116441 1099511627776 14550171486637 52911798063464448 (@Enclosure.Real.IsNear.mulLit_ft qz309 (Real.cos qz28) 428079 1048576 1 1048576 982671 1048576 8487061 12615155712 420660819009 1099511627776 14579853368053 52911798063464448 qz313 (@Enclosure.Real.IsNear.recentre' (Real.cos qz28) Bool.true 982671 1048576 33948244 50460622848 982671 1048576 8487061 12615155712 (ep121 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz309 (@Neg.neg Real Real.instNeg (Real.sin qz28)) 428079 1048576 1 1048576 365879 1048576 8487061 12615155712 156625116441 1099511627776 14550171486637 52911798063464448 qz313 (@Enclosure.Real.IsNear.neg (Real.sin qz28) Bool.true 365879 1048576 8487061 12615155712 (@Enclosure.Real.IsNear.recentre' (Real.sin qz28) Bool.true 365879 1048576 33948244 50460622848 365879 1048576 8487061 12615155712 (ep123 rfl rfl) rfl)) rfl)

noncomputable def ep125 := @ep43 420660819009 1099511627776 14579853368053 52911798063464448 Bool.false 156625116441 1099511627776 14550171486637 52911798063464448 Bool.false 834703441361594189086720 379579178735 549755813888 47037558091343 26455899031732224 Bool.true 978498812836613367791616 444969742983 549755813888 47045484911903 26455899031732224 (ep44 (BSN.head_sum_c_succ qz5 5 6 rfl rfl) (ep114 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep115 ep124) rfl rfl

noncomputable abbrev qz542 := (Real.log (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz29 := (@HMul.hMul Real Real Real qz267 qz278 qz542)

noncomputable abbrev qz314 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 7)))

noncomputable def ep126 := @Enclosure.Complex.IsNear.of_eq qz533 (Complex.mk (@HMul.hMul Real Real Real qz0 qz314 (Real.cos qz29)) (@HMul.hMul Real Real Real qz0 qz314 (@Neg.neg Real Real.instNeg (Real.sin qz29)))) Bool.true 123928845875 1099511627776 13450547176931 52911798063464448 Bool.false 198334108725 549755813888 3370916007491 13227949515866112 (BSN.cpow_neg_s_mk qz12 128194 1000 7 qz13 rfl)

noncomputable abbrev qz315 := (Real.sqrt (@Nat.cast Real Real.instNatCast 7))

noncomputable abbrev qz316 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 7) qz14)

noncomputable def ep127 := @Enclosure.Real.IsNear.inv_image qz315 2774271 1048576 1 1048576 198162 198163 524288 (@Enclosure.Real.IsNear.of_eq qz315 (Real.sqrt qz316) Bool.false 2774271 1048576 1 1048576 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz316) Bool.false 2774271 1048576 1 1048576 2774271 1048576 1 1048576 (BSN.sqrt_enclosure 7 1 1387135 1387136 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep128 := BSN.log_dyadic_bound 3 11 5 4 202569142545 524288 192492 5259111624 688905 293399 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 3) (BSN.artanhQ 11) 0 4 5259111624 202569142545 688905 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep129 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz542 128194 1000 0 1 4381796493761783 2251799813685248 125000000048123 24061500000000000000 280860009860649004951 1125899906842624000 8012125003084539931 12030750000000000000000 qz18 (BSN.isNear_log_sfrac 7 1 4381796493761783 2251799813685248 125000000048123 24061500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz316) Bool.false 36757173121942042968064 18889465931478580854784 1000000000384984 192492000000000000000 4381796493761783 2251799813685248 125000000048123 24061500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 293399 524288 24973259072661432 36028797018963968 192492 1000000000000000 rfl rfl rfl rfl (ep128 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep130 := nat_lit 1967274691020606395038468206532658002452367442491625726731485950521034933558401

noncomputable def ep131 := nat_lit 3022296681489025207728883677046835515683487088205848546258140103698621422721

noncomputable def ep132 := nat_lit 5895779479698841134699946852243880336325735353298465483101941571355707557829761

noncomputable def ep133 := BSN.cos_dyadic_bound_f 2722965487 2147483648 3 2 1048576 385360 ep130 ep57 ep131 ep132 ep60 ep131 312695 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2722965487) qz15 0 2 ep130 ep57 ep131 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2722965487) qz16 0 2 ep132 ep60 ep131 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz317 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 261571267) qz24)

noncomputable def ep134 := @Enclosure.Real.IsNear.cos_image qz29 qz317 Bool.false 261571267 1048576 699 1048576 Bool.true 312695 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz29 Bool.false 280860009860649004951 1125899906842624000 8012125003084539931 12030750000000000000000 261571267 1048576 699 1048576 (ep129 rfl) rfl) (Enclosure.sfrac_false_div 261571267 1048576) (BSN.cos_reduce2 qz317 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 191611661786070525149184) qz25) 226375608064910080 72057594037927936 Bool.false 312695 1048576 39 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q2 261571267 1048576 226375608064910080 72057594037927936 39 191611661786070525149184 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 312695 1048576 191611661786070525149184 151115727451828646838272 2722965487 2147483648 385360 384984 (ep133 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep135 := nat_lit 3538676606491900290903059664817146936001714606814361629279668198854903983266945

noncomputable def ep136 := nat_lit 9263069298565899482981214262853499479645764991132899559990903532071141235776641

noncomputable def ep137 := BSN.sin_dyadic_bound_f 2722965487 2147483648 3 2 1048576 385360 ep135 ep64 ep131 ep136 ep66 ep131 1000866 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2722965487) qz20 0 2 ep135 ep64 ep131 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2722965487) qz21 0 2 ep136 ep66 ep131 rfl rfl rfl rfl) rfl rfl

noncomputable def ep138 := @Enclosure.Real.IsNear.sin_image qz29 qz317 Bool.false 261571267 1048576 699 1048576 Bool.true 1000866 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz29 Bool.false 280860009860649004951 1125899906842624000 8012125003084539931 12030750000000000000000 261571267 1048576 699 1048576 (ep129 rfl) rfl) (Enclosure.sfrac_false_div 261571267 1048576) (BSN.sin_reduce2 qz317 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 191611661786070525149184) qz25) 226375608064910080 72057594037927936 Bool.false 1000866 1048576 39 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q2 261571267 1048576 226375608064910080 72057594037927936 39 191611661786070525149184 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1000866 1048576 191611661786070525149184 151115727451828646838272 2722965487 2147483648 385360 384984 (ep137 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz318 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 7))) Bool.false 396325 1048576 1 1048576 396325 1048576 1 1048576 (ep127 rfl rfl) rfl)

noncomputable def ep139 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz314 (Real.cos qz29)) (@HMul.hMul Real Real Real qz0 qz314 (@Neg.neg Real Real.instNeg (Real.sin qz29))) Bool.true 123928845875 1099511627776 13450547176931 52911798063464448 Bool.false 198334108725 549755813888 3370916007491 13227949515866112 (@Enclosure.Real.IsNear.mulLit_ft qz314 (Real.cos qz29) 396325 1048576 1 1048576 312695 1048576 33900121 50460622848 123928845875 1099511627776 13450547176931 52911798063464448 qz318 (@Enclosure.Real.IsNear.recentre' (Real.cos qz29) Bool.true 312695 1048576 135600484 201842491392 312695 1048576 33900121 50460622848 (ep134 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz314 (@Neg.neg Real Real.instNeg (Real.sin qz29)) 396325 1048576 1 1048576 500433 524288 33900121 50460622848 198334108725 549755813888 3370916007491 13227949515866112 qz318 (@Enclosure.Real.IsNear.neg (Real.sin qz29) Bool.true 500433 524288 33900121 50460622848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz29) Bool.true 1000866 1048576 135600484 201842491392 500433 524288 33900121 50460622848 (ep138 rfl rfl) rfl)) rfl)

noncomputable def ep140 := @ep41 123928845875 1099511627776 13450547176931 52911798063464448 Bool.false 198334108725 549755813888 3370916007491 13227949515866112 Bool.false 349221117152585958031360 635229511595 1099511627776 35841887786539 17637266021154816 Bool.true 135589373845289884975104 123317817129 274877906944 17929105642295 8818633010577408 (ep42 (BSN.head_sum_c_succ qz5 6 7 rfl rfl) (ep125 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep126 ep139) rfl rfl

noncomputable abbrev qz543 := (Real.log (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz30 := (@HMul.hMul Real Real Real qz267 qz278 qz543)

noncomputable abbrev qz319 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 8)))

noncomputable def ep141 := @Enclosure.Complex.IsNear.of_eq qz532 (Complex.mk (@HMul.hMul Real Real Real qz0 qz319 (Real.cos qz30)) (@HMul.hMul Real Real Real qz0 qz319 (@Neg.neg Real Real.instNeg (Real.sin qz30)))) Bool.true 347730433463 1099511627776 1401429104475 5879088673718272 Bool.true 43444384949 274877906944 349730044947 1469772168429568 (BSN.cpow_neg_s_mk qz12 128194 1000 8 qz13 rfl)

noncomputable abbrev qz320 := (Real.sqrt (@Nat.cast Real Real.instNatCast 8))

noncomputable abbrev qz321 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8) qz14)

noncomputable def ep142 := @Enclosure.Real.IsNear.inv_image qz320 2965821 1048576 1 1048576 185363 185364 524288 (@Enclosure.Real.IsNear.of_eq qz320 (Real.sqrt qz321) Bool.false 2965821 1048576 1 1048576 (BSN.sqrt_natCast_div_one 8) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz321) Bool.false 2965821 1048576 1 1048576 2965821 1048576 1 1048576 (BSN.sqrt_enclosure 8 1 1482910 1482911 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep143 := BSN.log_dyadic_bound 0 16 1 0 1 524288 192492 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl

noncomputable def ep144 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz543 128194 1000 0 1 9364972152248037 4503599627370496 250000000144369 48123000000000000000 600266620042642427589 2251799813685248000 16024250009253619793 24061500000000000000000 qz18 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 250000000144369 48123000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz321) Bool.false 39279540158062550581248 18889465931478580854784 1000000000577476 192492000000000000000 9364972152248037 4503599627370496 250000000144369 48123000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 524288 24973259072661432 36028797018963968 192492 1000000000000000 rfl rfl rfl rfl (ep143 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep145 := nat_lit 2057670582024070178752450196795007599391614319141208065097871777020121416236865

noncomputable def ep146 := nat_lit 1022627382879734148820245940544334171720612053929466593356706127716826775361

noncomputable def ep147 := nat_lit 5387481556205045184301184402940329076414299368711087700771848558464966942031681

noncomputable def ep148 := BSN.sin_dyadic_bound_f 2378015479 2147483648 3 2 1048576 385360 ep145 ep64 ep146 ep147 ep66 ep146 937969 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2378015479) qz20 0 2 ep145 ep64 ep146 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2378015479) qz21 0 2 ep147 ep66 ep146 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz322 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 279520927) qz24)

noncomputable def ep149 := @Enclosure.Real.IsNear.cos_image qz30 qz322 Bool.false 279520927 1048576 699 1048576 Bool.true 937969 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz30 Bool.false 600266620042642427589 2251799813685248000 16024250009253619793 24061500000000000000000 279520927 1048576 699 1048576 (ep144 rfl) rfl) (Enclosure.sfrac_false_div 279520927 1048576) (BSN.cos_reduce1 qz322 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 167337962958754964045824) qz25) 226375608064910080 72057594037927936 Bool.false 937969 1048576 42 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q1 279520927 1048576 226375608064910080 72057594037927936 42 167337962958754964045824 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 937969 1048576 167337962958754964045824 151115727451828646838272 2378015479 2147483648 385360 384984 (ep148 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep150 := nat_lit 1143604824405763314484170218637468370404994893769084243540309523290163820920641

noncomputable def ep151 := nat_lit 3428769218451530475154870164031316442871543457199393797434215157615057809211201

noncomputable def ep152 := BSN.cos_dyadic_bound_f 2378015479 2147483648 3 2 1048576 385360 ep150 ep57 ep146 ep151 ep60 ep146 468748 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2378015479) qz15 0 2 ep150 ep57 ep146 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2378015479) qz16 0 2 ep151 ep60 ep146 rfl rfl rfl rfl) rfl rfl

noncomputable def ep153 := @Enclosure.Real.IsNear.sin_image qz30 qz322 Bool.false 279520927 1048576 699 1048576 Bool.false 468748 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz30 Bool.false 600266620042642427589 2251799813685248000 16024250009253619793 24061500000000000000000 279520927 1048576 699 1048576 (ep144 rfl) rfl) (Enclosure.sfrac_false_div 279520927 1048576) (BSN.sin_reduce1 qz322 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 167337962958754964045824) qz25) 226375608064910080 72057594037927936 Bool.false 468748 1048576 42 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q1 279520927 1048576 226375608064910080 72057594037927936 42 167337962958754964045824 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 468748 1048576 167337962958754964045824 151115727451828646838272 2378015479 2147483648 385360 384984 (ep152 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz323 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 8))) Bool.false 370727 1048576 1 1048576 370727 1048576 1 1048576 (ep142 rfl rfl) rfl)

noncomputable def ep154 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz319 (Real.cos qz30)) (@HMul.hMul Real Real Real qz0 qz319 (@Neg.neg Real Real.instNeg (Real.sin qz30))) Bool.true 347730433463 1099511627776 1401429104475 5879088673718272 Bool.true 43444384949 274877906944 349730044947 1469772168429568 (@Enclosure.Real.IsNear.mulLit_ft qz319 (Real.cos qz30) 370727 1048576 1 1048576 937969 1048576 33900121 50460622848 347730433463 1099511627776 1401429104475 5879088673718272 qz323 (@Enclosure.Real.IsNear.recentre' (Real.cos qz30) Bool.true 937969 1048576 135600484 201842491392 937969 1048576 33900121 50460622848 (ep149 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz319 (@Neg.neg Real Real.instNeg (Real.sin qz30)) 370727 1048576 1 1048576 117187 262144 33900121 50460622848 43444384949 274877906944 349730044947 1469772168429568 qz323 (@Enclosure.Real.IsNear.neg (Real.sin qz30) Bool.false 117187 262144 33900121 50460622848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz30) Bool.false 468748 1048576 135600484 201842491392 117187 262144 33900121 50460622848 (ep153 rfl rfl) rfl)) rfl)

noncomputable def ep155 := @ep39 347730433463 1099511627776 1401429104475 5879088673718272 Bool.true 43444384949 274877906944 349730044947 1469772168429568 Bool.false 316108579381014725394432 71874769533 274877906944 10011543774991 4409316505288704 Bool.true 45839245064573007429632 83381101039 137438953472 20027485911977 8818633010577408 (ep40 (BSN.head_sum_c_succ qz5 7 8 rfl rfl) (ep140 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep141 ep154) rfl rfl

theorem EMRow43.d6 : Enclosure.Complex.IsNear qz3 Bool.false 71874769533 274877906944 10011543774991 4409316505288704 Bool.true 83381101039 137438953472 20027485911977 8818633010577408 := ep38 (BSN.head_sum_c_succ qz5 8 9 rfl rfl) (ep155 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz31 := (BSN.headSumC qz271 17)

noncomputable abbrev qz544 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 16) qz7)

noncomputable def ep156 := @Enclosure.Complex.IsNear.of_eq qz31 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 16) qz544) Bool.false 761764839889 1099511627776 201911535746669 52911798063464448 Bool.true 35716939049 1099511627776 201983308121297 52911798063464448

noncomputable def ep157 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 16) qz544 Bool.false 505851099833 549755813888 24122367510281 6613974757933056 Bool.true 75061086769 549755813888 48268898204461 13227949515866112 Bool.true

noncomputable abbrev qz545 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 15) qz7)

noncomputable def ep158 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 16) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 15) qz545) Bool.false 505851099833 549755813888 24122367510281 6613974757933056 Bool.true 75061086769 549755813888 48268898204461 13227949515866112

noncomputable def ep159 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 15) qz545 Bool.false 507208053725 549755813888 30633378522919 8818633010577408 Bool.false 66878672855 549755813888 30641157990853 8818633010577408 Bool.true

noncomputable abbrev qz546 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 14) qz7)

noncomputable def ep160 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 15) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 14) qz546) Bool.false 507208053725 549755813888 30633378522919 8818633010577408 Bool.false 66878672855 549755813888 30641157990853 8818633010577408

noncomputable def ep161 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 14) qz546 Bool.false 212737731509 274877906944 43564602349081 13227949515866112 Bool.true 110436035499 1099511627776 174291223651933 52911798063464448 Bool.false

noncomputable abbrev qz547 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 13) qz7)

noncomputable def ep162 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 14) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 13) qz547) Bool.false 212737731509 274877906944 43564602349081 13227949515866112 Bool.true 110436035499 1099511627776 174291223651933 52911798063464448

noncomputable def ep163 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 13) qz547 Bool.false 1001005996877 1099511627776 54791536908893 17637266021154816 Bool.false 155040576759 1099511627776 54796108658057 17637266021154816 Bool.true

noncomputable abbrev qz548 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 12) qz7)

noncomputable def ep164 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 13) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 12) qz548) Bool.false 1001005996877 1099511627776 54791536908893 17637266021154816 Bool.false 155040576759 1099511627776 54796108658057 17637266021154816

noncomputable def ep165 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 12) qz548 Bool.false 1101347025407 1099511627776 154097159606951 52911798063464448 Bool.true 9130131009 68719476736 38519738608859 13227949515866112 Bool.true

noncomputable abbrev qz549 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 11) qz7)

noncomputable def ep166 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 12) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 11) qz549) Bool.false 1101347025407 1099511627776 154097159606951 52911798063464448 Bool.true 9130131009 68719476736 38519738608859 13227949515866112

noncomputable def ep167 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 11) qz549 Bool.false 50459875361 68719476736 71659700960395 26455899031732224 Bool.true 299288932931 1099511627776 143322625536191 52911798063464448 Bool.false

noncomputable abbrev qz550 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 10) qz7)

noncomputable def ep168 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 11) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 10) qz550) Bool.false 50459875361 68719476736 71659700960395 26455899031732224 Bool.true 299288932931 1099511627776 143322625536191 52911798063464448

noncomputable def ep169 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 10) qz550 Bool.false 462697435807 1099511627776 132028440741617 52911798063464448 Bool.true 345132438537 1099511627776 132075031216559 52911798063464448 Bool.false

noncomputable abbrev qz551 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 9) qz7)

noncomputable def ep170 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 10) (@HAdd.hAdd Complex Complex Complex qz4 qz3 qz551) Bool.false 462697435807 1099511627776 132028440741617 52911798063464448 Bool.true 345132438537 1099511627776 132075031216559 52911798063464448

noncomputable def ep171 := @Enclosure.Complex.IsNear.addLitP qz3 qz551 Bool.false 71874769533 274877906944 10011543774991 4409316505288704 Bool.true 83381101039 137438953472 20027485911977 8818633010577408 Bool.false

noncomputable abbrev qz552 := (Real.log (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz32 := (@HMul.hMul Real Real Real qz267 qz278 qz552)

noncomputable abbrev qz324 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 9)))

noncomputable def ep172 := @Enclosure.Complex.IsNear.of_eq qz551 (Complex.mk (@HMul.hMul Real Real Real qz0 qz324 (Real.cos qz32)) (@HMul.hMul Real Real Real qz0 qz324 (@Neg.neg Real Real.instNeg (Real.sin qz32)))) Bool.false 175198357675 1099511627776 11889915441725 52911798063464448 Bool.false 321916369775 1099511627776 11910115744697 52911798063464448 (BSN.cpow_neg_s_mk qz12 128194 1000 9 qz13 rfl)

noncomputable abbrev qz325 := (Real.sqrt (@Nat.cast Real Real.instNatCast 9))

noncomputable abbrev qz326 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9) qz14)

noncomputable def ep173 := @Enclosure.Real.IsNear.inv_image qz325 3145729 1048576 1 1048576 174762 174763 524288 (@Enclosure.Real.IsNear.of_eq qz325 (Real.sqrt qz326) Bool.false 3145729 1048576 1 1048576 (BSN.sqrt_natCast_div_one 9) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz326) Bool.false 3145729 1048576 1 1048576 3145729 1048576 1 1048576 (BSN.sqrt_enclosure 9 1 1572864 1572865 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep174 := BSN.log_dyadic_bound 1 17 3 2 1252815 524288 192492 1448 3 61752 18 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 1) (BSN.artanhQ 17) 0 2 1448 1252815 3 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep175 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz552 128194 1000 0 1 9895417793173221 4503599627370496 250000000144369 48123000000000000000 634266594289023946437 2251799813685248000 16024250009253619793 24061500000000000000000 qz18 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 250000000144369 48123000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz326) Bool.false 41504390431577613533184 18889465931478580854784 1000000000577476 192492000000000000000 9895417793173221 4503599627370496 250000000144369 48123000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 61752 524288 24973259072661432 36028797018963968 192492 1000000000000000 rfl rfl rfl rfl (ep174 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep176 := nat_lit 1312373724374064438655784765685724176

noncomputable def ep177 := BSN.sin_dyadic_bound_f 1070321826 2147483648 2 1 1048576 385360 ep176 ep92 ep176 ep176 ep93 ep176 501247 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1070321826) qz20 0 1 ep176 ep92 ep176 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1070321826) qz21 0 1 ep176 ep93 ep176 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz327 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 147676699) qz17)

noncomputable def ep178 := @Enclosure.Real.IsNear.cos_image qz32 qz327 Bool.false 147676699 524288 175 262144 Bool.false 501247 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz32 Bool.false 634266594289023946437 2251799813685248000 16024250009253619793 24061500000000000000000 147676699 524288 175 262144 (ep175 rfl) rfl) (Enclosure.sfrac_false_div 147676699 524288) (BSN.cos_reduce3 qz327 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 37658601403288668602368) qz19) 226375608064910080 72057594037927936 Bool.false 501247 1048576 44 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q3 147676699 524288 226375608064910080 72057594037927936 44 37658601403288668602368 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 501247 1048576 37658601403288668602368 75557863725914323419136 1070321826 2147483648 385360 384984 (ep177 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep179 := BSN.cos_dyadic_bound_f 1070321826 2147483648 2 1 1048576 385360 ep176 ep96 ep176 ep176 ep97 ep176 921011 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1070321826) qz15 0 1 ep176 ep96 ep176 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1070321826) qz16 0 1 ep176 ep97 ep176 rfl rfl rfl rfl) rfl rfl

noncomputable def ep180 := @Enclosure.Real.IsNear.sin_image qz32 qz327 Bool.false 147676699 524288 175 262144 Bool.true 921011 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz32 Bool.false 634266594289023946437 2251799813685248000 16024250009253619793 24061500000000000000000 147676699 524288 175 262144 (ep175 rfl) rfl) (Enclosure.sfrac_false_div 147676699 524288) (BSN.sin_reduce3 qz327 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 37658601403288668602368) qz19) 226375608064910080 72057594037927936 Bool.false 921011 1048576 44 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q3 147676699 524288 226375608064910080 72057594037927936 44 37658601403288668602368 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 921011 1048576 37658601403288668602368 75557863725914323419136 1070321826 2147483648 385360 384984 (ep179 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz328 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 9))) Bool.false 349525 1048576 1 1048576 349525 1048576 1 1048576 (ep173 rfl rfl) rfl)

noncomputable def ep181 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz324 (Real.cos qz32)) (@HMul.hMul Real Real Real qz0 qz324 (@Neg.neg Real Real.instNeg (Real.sin qz32))) Bool.false 175198357675 1099511627776 11889915441725 52911798063464448 Bool.false 321916369775 1099511627776 11910115744697 52911798063464448 (@Enclosure.Real.IsNear.mulLit_ff qz324 (Real.cos qz32) 349525 1048576 1 1048576 501247 1048576 8487061 12615155712 175198357675 1099511627776 11889915441725 52911798063464448 qz328 (@Enclosure.Real.IsNear.recentre' (Real.cos qz32) Bool.false 501247 1048576 33948244 50460622848 501247 1048576 8487061 12615155712 (ep178 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz324 (@Neg.neg Real Real.instNeg (Real.sin qz32)) 349525 1048576 1 1048576 921011 1048576 8487061 12615155712 321916369775 1099511627776 11910115744697 52911798063464448 qz328 (@Enclosure.Real.IsNear.neg (Real.sin qz32) Bool.true 921011 1048576 8487061 12615155712 (@Enclosure.Real.IsNear.recentre' (Real.sin qz32) Bool.true 921011 1048576 33948244 50460622848 921011 1048576 8487061 12615155712 (ep180 rfl rfl) rfl)) rfl)

noncomputable def ep182 := @ep171 175198357675 1099511627776 11889915441725 52911798063464448 Bool.false 321916369775 1099511627776 11910115744697 52911798063464448 Bool.false 127185302702983959543808 462697435807 1099511627776 132028440741617 52911798063464448 Bool.true 47434641161764642750464 345132438537 1099511627776 132075031216559 52911798063464448 EMRow43.d6 (ep172 ep181) rfl rfl

noncomputable abbrev qz33 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 10)))

noncomputable abbrev qz553 := (Real.log (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz34 := (@HMul.hMul Real Real Real qz267 qz278 qz553)

noncomputable def ep183 := @Enclosure.Complex.IsNear.of_eq qz550 (Complex.mk (@HMul.hMul Real Real Real qz0 qz33 (Real.cos qz34)) (@HMul.hMul Real Real Real qz0 qz33 (@Neg.neg Real Real.instNeg (Real.sin qz34)))) Bool.false 344660569969 1099511627776 3763653726391 17637266021154816 Bool.false 22921752803 549755813888 234324881659 1102329126322176 (BSN.cpow_neg_s_mk qz12 128194 1000 10 qz13 rfl)

noncomputable abbrev qz329 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 10) qz14)

noncomputable def ep184 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 10)) 3315889 1048576 1 1048576 165794 165795 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 10)) (Real.sqrt qz329) Bool.false 3315889 1048576 1 1048576 (BSN.sqrt_natCast_div_one 10) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz329) Bool.false 3315889 1048576 1 1048576 3315889 1048576 1 1048576 (BSN.sqrt_enclosure 10 1 1657944 1657945 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep185 := BSN.log_dyadic_bound 2 18 3 2 1574640 524288 192492 6528 48 116991 20 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 2) (BSN.artanhQ 18) 0 2 6528 1574640 48 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep186 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz553 128194 1000 0 1 10369917190100709 4503599627370496 250000000144369 48123000000000000000 664680582133885144773 2251799813685248000 16024250009253619793 24061500000000000000000 qz18 (BSN.isNear_log_sfrac 10 1 10369917190100709 4503599627370496 250000000144369 48123000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz329) Bool.false 43494585150108164161536 18889465931478580854784 1000000000577476 192492000000000000000 10369917190100709 4503599627370496 250000000144369 48123000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 116991 524288 24973259072661432 36028797018963968 192492 1000000000000000 rfl rfl rfl rfl (ep185 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep187 := nat_lit 5866085045413739785267045810465656222686967361591391530984517536560664317720705

noncomputable def ep188 := nat_lit 8295927871012611745394937344009554726564552471223937232359770112140635994241

noncomputable def ep189 := nat_lit 15350124569054345685254480557424512732718095719214520016107058682239226469087361

noncomputable def ep190 := BSN.sin_dyadic_bound_f 3089286033 2147483648 3 2 1048576 385360 ep187 ep64 ep188 ep189 ep66 ep188 1039421 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3089286033) qz20 0 2 ep187 ep64 ep188 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3089286033) qz21 0 2 ep189 ep66 ep188 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz330 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 309516015) qz24)

noncomputable def ep191 := @Enclosure.Real.IsNear.cos_image qz34 qz330 Bool.false 309516015 1048576 699 1048576 Bool.false 1039421 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz34 Bool.false 664680582133885144773 2251799813685248000 16024250009253619793 24061500000000000000000 309516015 1048576 699 1048576 (ep186 rfl) rfl) (Enclosure.sfrac_false_div 309516015 1048576) (BSN.cos_reduce3 qz330 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 217389178589721783173120) qz25) 226375608064910080 72057594037927936 Bool.false 1039421 1048576 46 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q3 309516015 1048576 226375608064910080 72057594037927936 46 217389178589721783173120 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1039421 1048576 217389178589721783173120 151115727451828646838272 3089286033 2147483648 385360 384984 (ep190 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep192 := nat_lit 3262623215394749930368534311300479925815677224204650378205780751472431570286721

noncomputable def ep193 := nat_lit 9771277790442224567614813059213420667993902567671503260152622714193013438871681

noncomputable def ep194 := BSN.cos_dyadic_bound_f 3089286033 2147483648 3 2 1048576 385360 ep192 ep57 ep188 ep193 ep60 ep188 138254 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3089286033) qz15 0 2 ep192 ep57 ep188 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3089286033) qz16 0 2 ep193 ep60 ep188 rfl rfl rfl rfl) rfl rfl

noncomputable def ep195 := @Enclosure.Real.IsNear.sin_image qz34 qz330 Bool.false 309516015 1048576 699 1048576 Bool.true 138254 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz34 Bool.false 664680582133885144773 2251799813685248000 16024250009253619793 24061500000000000000000 309516015 1048576 699 1048576 (ep186 rfl) rfl) (Enclosure.sfrac_false_div 309516015 1048576) (BSN.sin_reduce3 qz330 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 217389178589721783173120) qz25) 226375608064910080 72057594037927936 Bool.false 138254 1048576 46 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q3 309516015 1048576 226375608064910080 72057594037927936 46 217389178589721783173120 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 138254 1048576 217389178589721783173120 151115727451828646838272 3089286033 2147483648 385360 384984 (ep194 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz331 := (@Enclosure.Real.IsNear.recentre' qz33 Bool.false 331589 1048576 1 1048576 331589 1048576 1 1048576 (ep184 rfl rfl) rfl)

noncomputable def ep196 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz33 (Real.cos qz34)) (@HMul.hMul Real Real Real qz0 qz33 (@Neg.neg Real Real.instNeg (Real.sin qz34))) Bool.false 344660569969 1099511627776 3763653726391 17637266021154816 Bool.false 22921752803 549755813888 234324881659 1102329126322176 (@Enclosure.Real.IsNear.mulLit_ff qz33 (Real.cos qz34) 331589 1048576 1 1048576 1039421 1048576 33900121 50460622848 344660569969 1099511627776 3763653726391 17637266021154816 qz331 (@Enclosure.Real.IsNear.recentre' (Real.cos qz34) Bool.false 1039421 1048576 135600484 201842491392 1039421 1048576 33900121 50460622848 (ep191 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz33 (@Neg.neg Real Real.instNeg (Real.sin qz34)) 331589 1048576 1 1048576 69127 524288 33900121 50460622848 22921752803 549755813888 234324881659 1102329126322176 qz331 (@Enclosure.Real.IsNear.neg (Real.sin qz34) Bool.true 69127 524288 33900121 50460622848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz34) Bool.true 138254 1048576 135600484 201842491392 69127 524288 33900121 50460622848 (ep195 rfl rfl) rfl)) rfl)

noncomputable def ep197 := @ep169 344660569969 1099511627776 3763653726391 17637266021154816 Bool.false 22921752803 549755813888 234324881659 1102329126322176 Bool.false 887699515128754970034176 50459875361 68719476736 71659700960395 26455899031732224 Bool.true 164535830911152950345728 299288932931 1099511627776 143322625536191 52911798063464448 (ep170 (BSN.head_sum_c_succ qz5 9 10 rfl rfl) (ep182 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep183 ep196) rfl rfl

noncomputable abbrev qz35 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 11)))

noncomputable abbrev qz554 := (Real.log (Enclosure.sfrac Bool.false 11 1))

noncomputable abbrev qz36 := (@HMul.hMul Real Real Real qz267 qz278 qz554)

noncomputable def ep198 := @Enclosure.Complex.IsNear.of_eq qz549 (Complex.mk (@HMul.hMul Real Real Real qz0 qz35 (Real.cos qz36)) (@HMul.hMul Real Real Real qz0 qz35 (@Neg.neg Real Real.instNeg (Real.sin qz36)))) Bool.false 293989019631 1099511627776 3592585895387 17637266021154816 Bool.false 153206836787 1099511627776 3585442966415 17637266021154816 (BSN.cpow_neg_s_mk qz12 128194 1000 11 qz13 rfl)

noncomputable abbrev qz332 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11) qz14)

noncomputable def ep199 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 11)) 3477733 1048576 1 1048576 158078 158079 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 11)) (Real.sqrt qz332) Bool.false 3477733 1048576 1 1048576 (BSN.sqrt_natCast_div_one 11) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz332) Bool.false 3477733 1048576 1 1048576 3477733 1048576 1 1048576 (BSN.sqrt_enclosure 11 1 1738866 1738867 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep200 := BSN.log_dyadic_bound 3 19 4 3 4939817505 524288 192492 41676111 10935 166961 22 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 3) (BSN.artanhQ 19) 0 3 41676111 4939817505 10935 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep201 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz554 128194 1000 0 1 10799156221662949 4503599627370496 250000000144369 48123000000000000000 692193516339930042053 2251799813685248000 16024250009253619793 24061500000000000000000 qz18 (BSN.isNear_log_sfrac 11 1 10799156221662949 4503599627370496 250000000144369 48123000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz332) Bool.false 45294944137145793642496 18889465931478580854784 1000000000577476 192492000000000000000 10799156221662949 4503599627370496 250000000144369 48123000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 166961 524288 24973259072661432 36028797018963968 192492 1000000000000000 rfl rfl rfl rfl (ep200 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep202 := nat_lit 1934401417231446988248367346544290399235539097741211093620607038769067647303680

noncomputable def ep203 := nat_lit 903825879505089439625365962633170265521520915360612177160103821980588834816

noncomputable def ep204 := nat_lit 5064826088944114824414901981771735436615567555459254730243330647731018122919936

noncomputable def ep205 := BSN.sin_dyadic_bound_f 2341588608 2147483648 3 2 1048576 385360 ep202 ep64 ep203 ep204 ep66 ep203 929883 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2341588608) qz20 0 2 ep202 ep64 ep203 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2341588608) qz21 0 2 ep204 ep66 ep203 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz333 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 322327723) qz24)

noncomputable def ep206 := @Enclosure.Real.IsNear.cos_image qz36 qz333 Bool.false 322327723 1048576 175 262144 Bool.false 929883 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz36 Bool.false 692193516339930042053 2251799813685248000 16024250009253619793 24061500000000000000000 322327723 1048576 175 262144 (ep201 rfl) rfl) (Enclosure.sfrac_false_div 322327723 1048576) (BSN.cos_reduce3 qz333 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 164774649764499848953856) qz25) 226375608064910080 72057594037927936 Bool.false 929883 1048576 48 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q3 322327723 1048576 226375608064910080 72057594037927936 48 164774649764499848953856 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 929883 1048576 164774649764499848953856 151115727451828646838272 2341588608 2147483648 385360 384984 (ep205 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep207 := nat_lit 1075069154408361699888926466285776075248864619151944212979075067681473399095296

noncomputable def ep208 := nat_lit 3223399811466074920787528666932061885215550815625111414582904995400459019616256

noncomputable def ep209 := BSN.cos_dyadic_bound_f 2341588608 2147483648 3 2 1048576 385360 ep207 ep57 ep203 ep208 ep60 ep203 484591 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2341588608) qz15 0 2 ep207 ep57 ep203 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2341588608) qz16 0 2 ep208 ep60 ep203 rfl rfl rfl rfl) rfl rfl

noncomputable def ep210 := @Enclosure.Real.IsNear.sin_image qz36 qz333 Bool.false 322327723 1048576 175 262144 Bool.true 484591 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz36 Bool.false 692193516339930042053 2251799813685248000 16024250009253619793 24061500000000000000000 322327723 1048576 175 262144 (ep201 rfl) rfl) (Enclosure.sfrac_false_div 322327723 1048576) (BSN.sin_reduce3 qz333 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 164774649764499848953856) qz25) 226375608064910080 72057594037927936 Bool.false 484591 1048576 48 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q3 322327723 1048576 226375608064910080 72057594037927936 48 164774649764499848953856 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 484591 1048576 164774649764499848953856 151115727451828646838272 2341588608 2147483648 385360 384984 (ep209 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz334 := (@Enclosure.Real.IsNear.recentre' qz35 Bool.false 316157 1048576 1 1048576 316157 1048576 1 1048576 (ep199 rfl rfl) rfl)

noncomputable def ep211 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz35 (Real.cos qz36)) (@HMul.hMul Real Real Real qz0 qz35 (@Neg.neg Real Real.instNeg (Real.sin qz36))) Bool.false 293989019631 1099511627776 3592585895387 17637266021154816 Bool.false 153206836787 1099511627776 3585442966415 17637266021154816 (@Enclosure.Real.IsNear.mulLit_ff qz35 (Real.cos qz36) 316157 1048576 1 1048576 929883 1048576 8487061 12615155712 293989019631 1099511627776 3592585895387 17637266021154816 qz334 (@Enclosure.Real.IsNear.recentre' (Real.cos qz36) Bool.false 929883 1048576 33948244 50460622848 929883 1048576 8487061 12615155712 (ep206 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz35 (@Neg.neg Real Real.instNeg (Real.sin qz36)) 316157 1048576 1 1048576 484591 1048576 8487061 12615155712 153206836787 1099511627776 3585442966415 17637266021154816 qz334 (@Enclosure.Real.IsNear.neg (Real.sin qz36) Bool.true 484591 1048576 8487061 12615155712 (@Enclosure.Real.IsNear.recentre' (Real.sin qz36) Bool.true 484591 1048576 33948244 50460622848 484591 1048576 8487061 12615155712 (ep210 rfl rfl) rfl)) rfl)

noncomputable def ep212 := @ep167 293989019631 1099511627776 3592585895387 17637266021154816 Bool.false 153206836787 1099511627776 3585442966415 17637266021154816 Bool.false 75683991290719137431552 1101347025407 1099511627776 154097159606951 52911798063464448 Bool.true 160618963320219572895744 9130131009 68719476736 38519738608859 13227949515866112 (ep168 (BSN.head_sum_c_succ qz5 10 11 rfl rfl) (ep197 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep198 ep211) rfl rfl

noncomputable abbrev qz37 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 12)))

noncomputable abbrev qz555 := (Real.log (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz38 := (@HMul.hMul Real Real Real qz267 qz278 qz555)

noncomputable def ep213 := @Enclosure.Complex.IsNear.of_eq qz548 (Complex.mk (@HMul.hMul Real Real Real qz0 qz37 (Real.cos qz38)) (@HMul.hMul Real Real Real qz0 qz37 (@Neg.neg Real Real.instNeg (Real.sin qz38)))) Bool.true 50170514265 549755813888 642340694983 3306987378966528 Bool.false 301122672903 1099511627776 10309371538735 52911798063464448 (BSN.cpow_neg_s_mk qz12 128194 1000 12 qz13 rfl)

noncomputable abbrev qz335 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 12) qz14)

noncomputable def ep214 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 12)) 3632373 1048576 1 1048576 151348 151349 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 12)) (Real.sqrt qz335) Bool.false 3632373 1048576 1 1048576 (BSN.sqrt_natCast_div_one 12) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz335) Bool.false 3632373 1048576 1 1048576 3632373 1048576 1 1048576 (BSN.sqrt_enclosure 12 1 1816186 1816187 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep215 := BSN.log_dyadic_bound 4 20 4 3 6720000000 524288 192492 91811840 61440 212580 24 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 4) (BSN.artanhQ 20) 0 3 91811840 6720000000 61440 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep216 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz555 128194 1000 0 1 11191020447815397 4503599627370496 250000000144369 48123000000000000000 717310837643623501509 2251799813685248000 16024250009253619793 24061500000000000000000 qz18 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 250000000144369 48123000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz335) Bool.false 46938541828353910898688 18889465931478580854784 1000000000577476 192492000000000000000 11191020447815397 4503599627370496 250000000144369 48123000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 212580 524288 24973259072661432 36028797018963968 192492 1000000000000000 rfl rfl rfl rfl (ep215 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep217 := nat_lit 1852800333695761860930388897598376405296582647453115525408978667930944307690625

noncomputable def ep218 := nat_lit 2681278120912970921771409328279809981533400482857738171468086782441062890625

noncomputable def ep219 := nat_lit 5553038444845459640947623874138569595926681141393631099883999830227950797290625

noncomputable def ep220 := BSN.cos_dyadic_bound_f 2682518545 2147483648 3 2 1048576 385360 ep217 ep57 ep218 ep219 ep60 ep218 331490 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2682518545) qz15 0 2 ep217 ep57 ep218 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2682518545) qz16 0 2 ep219 ep60 ep218 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz336 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 20876493) (@Nat.cast Real Real.instNatCast 65536))

noncomputable abbrev qz337 := (@Nat.cast Real Real.instNatCast 9444732965739290427392)

noncomputable def ep221 := @Enclosure.Real.IsNear.cos_image qz38 qz336 Bool.false 20876493 65536 699 1048576 Bool.true 331490 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz38 Bool.false 717310837643623501509 2251799813685248000 16024250009253619793 24061500000000000000000 20876493 65536 699 1048576 (ep216 rfl) rfl) (Enclosure.sfrac_false_div 20876493 65536) (BSN.cos_reduce2 qz336 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11797841330615286235136) qz337) 226375608064910080 72057594037927936 Bool.false 331490 1048576 50 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q2 20876493 65536 226375608064910080 72057594037927936 50 11797841330615286235136 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 331490 1048576 11797841330615286235136 9444732965739290427392 2682518545 2147483648 385360 384984 (ep220 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep222 := nat_lit 3332895578155640972937282888214453681548622045029321755198987132849746903530625

noncomputable def ep223 := nat_lit 8724671111545200595248110996887306616466765564771215878005446540768242074090625

noncomputable def ep224 := BSN.sin_dyadic_bound_f 2682518545 2147483648 3 2 1048576 385360 ep222 ep64 ep218 ep223 ep66 ep218 994799 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2682518545) qz20 0 2 ep222 ep64 ep218 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2682518545) qz21 0 2 ep223 ep66 ep218 rfl rfl rfl rfl) rfl rfl

noncomputable def ep225 := @Enclosure.Real.IsNear.sin_image qz38 qz336 Bool.false 20876493 65536 699 1048576 Bool.true 994799 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz38 Bool.false 717310837643623501509 2251799813685248000 16024250009253619793 24061500000000000000000 20876493 65536 699 1048576 (ep216 rfl) rfl) (Enclosure.sfrac_false_div 20876493 65536) (BSN.sin_reduce2 qz336 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11797841330615286235136) qz337) 226375608064910080 72057594037927936 Bool.false 994799 1048576 50 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q2 20876493 65536 226375608064910080 72057594037927936 50 11797841330615286235136 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 994799 1048576 11797841330615286235136 9444732965739290427392 2682518545 2147483648 385360 384984 (ep224 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz338 := (@Enclosure.Real.IsNear.recentre' qz37 Bool.false 302697 1048576 1 1048576 302697 1048576 1 1048576 (ep214 rfl rfl) rfl)

noncomputable def ep226 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz37 (Real.cos qz38)) (@HMul.hMul Real Real Real qz0 qz37 (@Neg.neg Real Real.instNeg (Real.sin qz38))) Bool.true 50170514265 549755813888 642340694983 3306987378966528 Bool.false 301122672903 1099511627776 10309371538735 52911798063464448 (@Enclosure.Real.IsNear.mulLit_ft qz37 (Real.cos qz38) 302697 1048576 1 1048576 165745 524288 33900121 50460622848 50170514265 549755813888 642340694983 3306987378966528 qz338 (@Enclosure.Real.IsNear.recentre' (Real.cos qz38) Bool.true 331490 1048576 135600484 201842491392 165745 524288 33900121 50460622848 (ep221 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz37 (@Neg.neg Real Real.instNeg (Real.sin qz38)) 302697 1048576 1 1048576 994799 1048576 33900121 50460622848 301122672903 1099511627776 10309371538735 52911798063464448 qz338 (@Enclosure.Real.IsNear.neg (Real.sin qz38) Bool.true 994799 1048576 33900121 50460622848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz38) Bool.true 994799 1048576 135600484 201842491392 994799 1048576 33900121 50460622848 (ep225 rfl rfl) rfl)) rfl)

noncomputable def ep227 := @ep165 50170514265 549755813888 642340694983 3306987378966528 Bool.false 301122672903 1099511627776 10309371538735 52911798063464448 Bool.false 550308866519883921227776 1001005996877 1099511627776 54791536908893 17637266021154816 Bool.false 10654307307726122778624 155040576759 1099511627776 54796108658057 17637266021154816 (ep166 (BSN.head_sum_c_succ qz5 11 12 rfl rfl) (ep212 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep213 ep226) rfl rfl

noncomputable abbrev qz39 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 13)))

noncomputable abbrev qz556 := (Real.log (Enclosure.sfrac Bool.false 13 1))

noncomputable abbrev qz40 := (@HMul.hMul Real Real Real qz267 qz278 qz556)

noncomputable def ep228 := @Enclosure.Complex.IsNear.of_eq qz547 (Complex.mk (@HMul.hMul Real Real Real qz0 qz39 (Real.cos qz40)) (@HMul.hMul Real Real Real qz0 qz39 (@Neg.neg Real Real.instNeg (Real.sin qz40)))) Bool.true 150055070841 1099511627776 9883798669645 52911798063464448 Bool.true 132738306129 549755813888 4951448838881 26455899031732224 (BSN.cpow_neg_s_mk qz12 128194 1000 13 qz13 rfl)

noncomputable abbrev qz339 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13) qz14)

noncomputable def ep229 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 13)) 3780695 1048576 1 1048576 145411 145412 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 13)) (Real.sqrt qz339) Bool.false 3780695 1048576 1 1048576 (BSN.sqrt_natCast_div_one 13) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz339) Bool.false 3780695 1048576 1 1048576 3780695 1048576 1 1048576 (BSN.sqrt_enclosure 13 1 1890347 1890348 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep230 := BSN.log_dyadic_bound 5 21 5 4 35742602096145 524288 192492 699352521000 41015625 254545 26 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 5) (BSN.artanhQ 21) 0 4 699352521000 35742602096145 41015625 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep231 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz556 128194 1000 0 1 11551497052968677 4503599627370496 250000000144369 48123000000000000000 740416306604133289669 2251799813685248000 16024250009253619793 24061500000000000000000 qz18 (BSN.isNear_log_sfrac 13 1 11551497052968677 4503599627370496 250000000144369 48123000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz339) Bool.false 48450490295254733815808 18889465931478580854784 1000000000577476 192492000000000000000 11551497052968677 4503599627370496 250000000144369 48123000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 254545 524288 24973259072661432 36028797018963968 192492 1000000000000000 rfl rfl rfl rfl (ep230 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep232 := nat_lit 1489790690886295146476848076218536976

noncomputable def ep233 := BSN.sin_dyadic_bound_f 1104794018 2147483648 2 1 1048576 385360 ep232 ep92 ep232 ep232 ep93 ep232 515967 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1104794018) qz20 0 1 ep232 ep92 ep232 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1104794018) qz21 0 1 ep232 ep93 ep232 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz340 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 172391605) qz17)

noncomputable def ep234 := @Enclosure.Real.IsNear.cos_image qz40 qz340 Bool.false 172391605 524288 699 1048576 Bool.true 515967 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz40 Bool.false 740416306604133289669 2251799813685248000 16024250009253619793 24061500000000000000000 172391605 524288 699 1048576 (ep231 rfl) rfl) (Enclosure.sfrac_false_div 172391605 524288) (BSN.cos_reduce1 qz340 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 38871483836320133939200) qz19) 226375608064910080 72057594037927936 Bool.false 515967 1048576 52 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q1 172391605 524288 226375608064910080 72057594037927936 52 38871483836320133939200 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 515967 1048576 38871483836320133939200 75557863725914323419136 1104794018 2147483648 385360 384984 (ep233 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep235 := BSN.cos_dyadic_bound_f 1104794018 2147483648 2 1 1048576 385360 ep232 ep96 ep232 ep232 ep97 ep232 912846 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1104794018) qz15 0 1 ep232 ep96 ep232 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1104794018) qz16 0 1 ep232 ep97 ep232 rfl rfl rfl rfl) rfl rfl

noncomputable def ep236 := @Enclosure.Real.IsNear.sin_image qz40 qz340 Bool.false 172391605 524288 699 1048576 Bool.false 912846 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz40 Bool.false 740416306604133289669 2251799813685248000 16024250009253619793 24061500000000000000000 172391605 524288 699 1048576 (ep231 rfl) rfl) (Enclosure.sfrac_false_div 172391605 524288) (BSN.sin_reduce1 qz340 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 38871483836320133939200) qz19) 226375608064910080 72057594037927936 Bool.false 912846 1048576 52 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q1 172391605 524288 226375608064910080 72057594037927936 52 38871483836320133939200 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 912846 1048576 38871483836320133939200 75557863725914323419136 1104794018 2147483648 385360 384984 (ep235 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz341 := (@Enclosure.Real.IsNear.recentre' qz39 Bool.false 290823 1048576 1 1048576 290823 1048576 1 1048576 (ep229 rfl rfl) rfl)

noncomputable def ep237 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz39 (Real.cos qz40)) (@HMul.hMul Real Real Real qz0 qz39 (@Neg.neg Real Real.instNeg (Real.sin qz40))) Bool.true 150055070841 1099511627776 9883798669645 52911798063464448 Bool.true 132738306129 549755813888 4951448838881 26455899031732224 (@Enclosure.Real.IsNear.mulLit_ft qz39 (Real.cos qz40) 290823 1048576 1 1048576 515967 1048576 33900121 50460622848 150055070841 1099511627776 9883798669645 52911798063464448 qz341 (@Enclosure.Real.IsNear.recentre' (Real.cos qz40) Bool.true 515967 1048576 135600484 201842491392 515967 1048576 33900121 50460622848 (ep234 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz39 (@Neg.neg Real Real.instNeg (Real.sin qz40)) 290823 1048576 1 1048576 456423 524288 33900121 50460622848 132738306129 549755813888 4951448838881 26455899031732224 qz341 (@Enclosure.Real.IsNear.neg (Real.sin qz40) Bool.false 456423 524288 33900121 50460622848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz40) Bool.false 912846 1048576 135600484 201842491392 456423 524288 33900121 50460622848 (ep236 rfl rfl) rfl)) rfl)

noncomputable def ep238 := @ep163 150055070841 1099511627776 9883798669645 52911798063464448 Bool.true 132738306129 549755813888 4951448838881 26455899031732224 Bool.false 935630437843336939175936 212737731509 274877906944 43564602349081 13227949515866112 Bool.true 60712852578316805210112 110436035499 1099511627776 174291223651933 52911798063464448 (ep164 (BSN.head_sum_c_succ qz5 12 13 rfl rfl) (ep227 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep228 ep237) rfl rfl

noncomputable abbrev qz41 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 14)))

noncomputable abbrev qz557 := (Real.log (Enclosure.sfrac Bool.false 14 1))

noncomputable abbrev qz42 := (@HMul.hMul Real Real Real qz267 qz278 qz557)

noncomputable def ep239 := @Enclosure.Complex.IsNear.of_eq qz546 (Complex.mk (@HMul.hMul Real Real Real qz0 qz41 (Real.cos qz42)) (@HMul.hMul Real Real Real qz0 qz41 (@Neg.neg Real Real.instNeg (Real.sin qz42)))) Bool.false 81732590707 549755813888 4770930870595 26455899031732224 Bool.false 244193381209 1099511627776 9555724293185 52911798063464448 (BSN.cpow_neg_s_mk qz12 128194 1000 14 qz13 rfl)

noncomputable abbrev qz342 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14) qz14)

noncomputable def ep240 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 14)) 3923413 1048576 1 1048576 140121 140122 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 14)) (Real.sqrt qz342) Bool.false 3923413 1048576 1 1048576 (BSN.sqrt_natCast_div_one 14) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz342) Bool.false 3923413 1048576 1 1048576 3923413 1048576 1 1048576 (BSN.sqrt_enclosure 14 1 1961706 1961707 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep241 := BSN.log_dyadic_bound 6 22 5 4 51857700491520 524288 192492 1346332575744 176359680 293399 28 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 6) (BSN.artanhQ 22) 0 4 1346332575744 51857700491520 176359680 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep242 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz557 128194 1000 0 1 11885250371606245 4503599627370496 250000000144369 48123000000000000000 152361778613769097153 450359962737049600 16024250009253619793 24061500000000000000000 qz18 (BSN.isNear_log_sfrac 14 1 11885250371606245 4503599627370496 250000000144369 48123000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz342) Bool.false 49850353174629559828480 18889465931478580854784 1000000000577476 192492000000000000000 11885250371606245 4503599627370496 250000000144369 48123000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 293399 524288 24973259072661432 36028797018963968 192492 1000000000000000 rfl rfl rfl rfl (ep241 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep243 := nat_lit 2575301748360410075941442086538064561

noncomputable def ep244 := BSN.sin_dyadic_bound_f 1266797013 2147483648 2 1 1048576 385360 ep243 ep92 ep243 ep243 ep93 ep243 583298 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1266797013) qz20 0 1 ep243 ep92 ep243 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1266797013) qz21 0 1 ep243 ep93 ep243 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz343 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 354744909) qz24)

noncomputable def ep245 := @Enclosure.Real.IsNear.cos_image qz42 qz343 Bool.false 354744909 1048576 175 262144 Bool.false 583298 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz42 Bool.false 152361778613769097153 450359962737049600 16024250009253619793 24061500000000000000000 354744909 1048576 175 262144 (ep242 rfl) rfl) (Enclosure.sfrac_false_div 354744909 1048576) (BSN.cos_reduce3 qz343 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 89142914999078719848448) qz25) 226375608064910080 72057594037927936 Bool.false 583298 1048576 53 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q3 354744909 1048576 226375608064910080 72057594037927936 53 89142914999078719848448 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 583298 1048576 89142914999078719848448 151115727451828646838272 1266797013 2147483648 385360 384984 (ep244 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep246 := BSN.cos_dyadic_bound_f 1266797013 2147483648 2 1 1048576 385360 ep243 ep96 ep243 ep243 ep97 ep243 871363 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1266797013) qz15 0 1 ep243 ep96 ep243 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1266797013) qz16 0 1 ep243 ep97 ep243 rfl rfl rfl rfl) rfl rfl

noncomputable def ep247 := @Enclosure.Real.IsNear.sin_image qz42 qz343 Bool.false 354744909 1048576 175 262144 Bool.true 871363 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz42 Bool.false 152361778613769097153 450359962737049600 16024250009253619793 24061500000000000000000 354744909 1048576 175 262144 (ep242 rfl) rfl) (Enclosure.sfrac_false_div 354744909 1048576) (BSN.sin_reduce3 qz343 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 89142914999078719848448) qz25) 226375608064910080 72057594037927936 Bool.false 871363 1048576 53 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q3 354744909 1048576 226375608064910080 72057594037927936 53 89142914999078719848448 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 871363 1048576 89142914999078719848448 151115727451828646838272 1266797013 2147483648 385360 384984 (ep246 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz344 := (@Enclosure.Real.IsNear.recentre' qz41 Bool.false 280243 1048576 1 1048576 280243 1048576 1 1048576 (ep240 rfl rfl) rfl)

noncomputable def ep248 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz41 (Real.cos qz42)) (@HMul.hMul Real Real Real qz0 qz41 (@Neg.neg Real Real.instNeg (Real.sin qz42))) Bool.false 81732590707 549755813888 4770930870595 26455899031732224 Bool.false 244193381209 1099511627776 9555724293185 52911798063464448 (@Enclosure.Real.IsNear.mulLit_ff qz41 (Real.cos qz42) 280243 1048576 1 1048576 291649 524288 8487061 12615155712 81732590707 549755813888 4770930870595 26455899031732224 qz344 (@Enclosure.Real.IsNear.recentre' (Real.cos qz42) Bool.false 583298 1048576 33948244 50460622848 291649 524288 8487061 12615155712 (ep245 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz41 (@Neg.neg Real Real.instNeg (Real.sin qz42)) 280243 1048576 1 1048576 871363 1048576 8487061 12615155712 244193381209 1099511627776 9555724293185 52911798063464448 qz344 (@Enclosure.Real.IsNear.neg (Real.sin qz42) Bool.true 871363 1048576 8487061 12615155712 (@Enclosure.Real.IsNear.recentre' (Real.sin qz42) Bool.true 871363 1048576 33948244 50460622848 871363 1048576 8487061 12615155712 (ep247 rfl rfl) rfl)) rfl)

noncomputable def ep249 := @ep161 81732590707 549755813888 4770930870595 26455899031732224 Bool.false 244193381209 1099511627776 9555724293185 52911798063464448 Bool.false 139420288193067902566400 507208053725 549755813888 30633378522919 8818633010577408 Bool.false 147067756908599270440960 66878672855 549755813888 30641157990853 8818633010577408 (ep162 (BSN.head_sum_c_succ qz5 13 14 rfl rfl) (ep238 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep239 ep248) rfl rfl

noncomputable abbrev qz43 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 15)))

noncomputable abbrev qz558 := (Real.log (Enclosure.sfrac Bool.false 15 1))

noncomputable abbrev qz44 := (@HMul.hMul Real Real Real qz267 qz278 qz558)

noncomputable def ep250 := @Enclosure.Complex.IsNear.of_eq qz545 (Complex.mk (@HMul.hMul Real Real Real qz0 qz43 (Real.cos qz44)) (@HMul.hMul Real Real Real qz0 qz43 (@Neg.neg Real Real.instNeg (Real.sin qz44)))) Bool.true 339238473 137438953472 4589334472367 26455899031732224 Bool.true 17742469953 68719476736 4614322436363 26455899031732224 (BSN.cpow_neg_s_mk qz12 128194 1000 15 qz13 rfl)

noncomputable abbrev qz345 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 15) qz14)

noncomputable def ep251 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 15)) 4061117 1048576 1 1048576 135370 135371 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 15)) (Real.sqrt qz345) Bool.false 4061117 1048576 1 1048576 (BSN.sqrt_natCast_div_one 15) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz345) Bool.false 4061117 1048576 1 1048576 4061117 1048576 1 1048576 (BSN.sqrt_enclosure 15 1 2030558 2030559 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep252 := BSN.log_dyadic_bound 7 23 6 5 430628584065881355 524288 192492 14087658153505881 266939110305 329571 30 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 7) (BSN.artanhQ 23) 0 5 14087658153505881 430628584065881355 266939110305 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep253 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz558 128194 1000 0 1 12195965485668069 4503599627370496 250000000144369 48123000000000000000 781724799734866218693 2251799813685248000 16024250009253619793 24061500000000000000000 qz18 (BSN.isNear_log_sfrac 15 1 12195965485668069 4503599627370496 250000000144369 48123000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz345) Bool.false 51153586820399524478976 18889465931478580854784 1000000000577476 192492000000000000000 12195965485668069 4503599627370496 250000000144369 48123000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 329571 524288 24973259072661432 36028797018963968 192492 1000000000000000 rfl rfl rfl rfl (ep252 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep254 := BSN.sin_dyadic_bound_f 20529673 2147483648 1 0 1048576 385360 0 1 1 0 1 1 10024 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 20529673) qz20 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 20529673) qz21 0 0 rfl) rfl rfl

noncomputable abbrev qz346 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11375593) (@Nat.cast Real Real.instNatCast 32768))

noncomputable def ep255 := @Enclosure.Real.IsNear.cos_image qz44 qz346 Bool.false 11375593 32768 699 1048576 Bool.true 10024 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz44 Bool.false 781724799734866218693 2251799813685248000 16024250009253619793 24061500000000000000000 11375593 32768 699 1048576 (ep253 rfl) rfl) (Enclosure.sfrac_false_div 11375593 32768) (BSN.cos_reduce1 qz346 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 45145228704382713856) (@Nat.cast Real Real.instNatCast 4722366482869645213696)) 226375608064910080 72057594037927936 Bool.false 10024 1048576 55 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q1 11375593 32768 226375608064910080 72057594037927936 55 45145228704382713856 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 10024 1048576 45145228704382713856 4722366482869645213696 20529673 2147483648 385360 384984 (ep254 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep256 := BSN.cos_dyadic_bound_f 20529673 2147483648 1 0 1048576 385360 0 1 1 0 1 1 1048528 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 20529673) qz15 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 20529673) qz16 0 0 rfl) rfl rfl

noncomputable def ep257 := @Enclosure.Real.IsNear.sin_image qz44 qz346 Bool.false 11375593 32768 699 1048576 Bool.false 1048528 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz44 Bool.false 781724799734866218693 2251799813685248000 16024250009253619793 24061500000000000000000 11375593 32768 699 1048576 (ep253 rfl) rfl) (Enclosure.sfrac_false_div 11375593 32768) (BSN.sin_reduce1 qz346 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 45145228704382713856) (@Nat.cast Real Real.instNatCast 4722366482869645213696)) 226375608064910080 72057594037927936 Bool.false 1048528 1048576 55 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q1 11375593 32768 226375608064910080 72057594037927936 55 45145228704382713856 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1048528 1048576 45145228704382713856 4722366482869645213696 20529673 2147483648 385360 384984 (ep256 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz347 := (@Enclosure.Real.IsNear.recentre' qz43 Bool.false 270741 1048576 1 1048576 270741 1048576 1 1048576 (ep251 rfl rfl) rfl)

noncomputable def ep258 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz43 (Real.cos qz44)) (@HMul.hMul Real Real Real qz0 qz43 (@Neg.neg Real Real.instNeg (Real.sin qz44))) Bool.true 339238473 137438953472 4589334472367 26455899031732224 Bool.true 17742469953 68719476736 4614322436363 26455899031732224 (@Enclosure.Real.IsNear.mulLit_ft qz43 (Real.cos qz44) 270741 1048576 1 1048576 1253 131072 33900121 50460622848 339238473 137438953472 4589334472367 26455899031732224 qz347 (@Enclosure.Real.IsNear.recentre' (Real.cos qz44) Bool.true 10024 1048576 135600484 201842491392 1253 131072 33900121 50460622848 (ep255 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz43 (@Neg.neg Real Real.instNeg (Real.sin qz44)) 270741 1048576 1 1048576 65533 65536 33900121 50460622848 17742469953 68719476736 4614322436363 26455899031732224 qz347 (@Enclosure.Real.IsNear.neg (Real.sin qz44) Bool.false 65533 65536 33900121 50460622848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz44) Bool.false 1048528 1048576 135600484 201842491392 65533 65536 33900121 50460622848 (ep257 rfl rfl) rfl)) rfl)

noncomputable def ep259 := @ep159 339238473 137438953472 4589334472367 26455899031732224 Bool.true 17742469953 68719476736 4614322436363 26455899031732224 Bool.false 69523645773707713970176 505851099833 549755813888 24122367510281 6613974757933056 Bool.true 5158158606001172905984 75061086769 549755813888 48268898204461 13227949515866112 (ep160 (BSN.head_sum_c_succ qz5 14 15 rfl rfl) (ep249 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep250 ep258) rfl rfl

noncomputable abbrev qz45 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 16)))

noncomputable abbrev qz559 := (Real.log (Enclosure.sfrac Bool.false 16 1))

noncomputable abbrev qz46 := (@HMul.hMul Real Real Real qz267 qz278 qz559)

noncomputable def ep260 := @Enclosure.Complex.IsNear.of_eq qz544 (Complex.mk (@HMul.hMul Real Real Real qz0 qz45 (Real.cos qz46)) (@HMul.hMul Real Real Real qz0 qz45 (@Neg.neg Real Real.instNeg (Real.sin qz46)))) Bool.true 249937359777 1099511627776 8932595664421 52911798063464448 Bool.false 114405234489 1099511627776 8907715303453 52911798063464448 (BSN.cpow_neg_s_mk qz12 128194 1000 16 qz13 rfl)

noncomputable abbrev qz348 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16) qz14)

noncomputable def ep261 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 16)) 4194305 1048576 1 1048576 131071 131072 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 16)) (Real.sqrt qz348) Bool.false 4194305 1048576 1 1048576 (BSN.sqrt_natCast_div_one 16) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz348) Bool.false 4194305 1048576 1 1048576 4194305 1048576 1 1048576 (BSN.sqrt_enclosure 16 1 2097152 2097153 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep262 := BSN.log_dyadic_bound 0 32 1 0 1 524288 192492 0 1 0 32 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 32) 0 0 rfl) rfl rfl rfl

noncomputable def ep263 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz559 128194 1000 0 1 3121657384082679 1125899906842624 62500000048123 12030750000000000000 200088873347547475863 562949953421312000 4006062503084539931 6015375000000000000000 qz18 (BSN.isNear_log_sfrac 16 1 3121657384082679 1125899906842624 62500000048123 12030750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz348) Bool.false 52372720210750067441664 18889465931478580854784 1000000000769968 192492000000000000000 3121657384082679 1125899906842624 62500000048123 12030750000000000000 (BSN.log_rat_reduce_isNear 16 1 4 32 32 0 524288 24973259072661432 36028797018963968 192492 1000000000000000 rfl rfl rfl rfl (ep262 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep264 := nat_lit 722163273443609792115588492819809296

noncomputable def ep265 := BSN.cos_dyadic_bound_f 921847006 2147483648 2 1 1048576 385360 ep264 ep96 ep264 ep264 ep97 ep264 953439 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 921847006) qz15 0 1 ep264 ep96 ep264 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 921847006) qz16 0 1 ep264 ep97 ep264 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz349 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 372694569) qz24)

noncomputable def ep266 := @Enclosure.Real.IsNear.cos_image qz46 qz349 Bool.false 372694569 1048576 699 1048576 Bool.true 953439 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz46 Bool.false 200088873347547475863 562949953421312000 4006062503084539931 6015375000000000000000 372694569 1048576 699 1048576 (ep263 rfl) rfl) (Enclosure.sfrac_false_div 372694569 1048576) (BSN.cos_reduce2 qz349 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 64869216171763158745088) qz25) 226375608064910080 72057594037927936 Bool.false 953439 1048576 56 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q2 372694569 1048576 226375608064910080 72057594037927936 56 64869216171763158745088 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 953439 1048576 64869216171763158745088 151115727451828646838272 921847006 2147483648 385360 384984 (ep265 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep267 := BSN.sin_dyadic_bound_f 921847006 2147483648 2 1 1048576 385360 ep264 ep92 ep264 ep264 ep93 ep264 436423 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 921847006) qz20 0 1 ep264 ep92 ep264 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 921847006) qz21 0 1 ep264 ep93 ep264 rfl rfl rfl rfl) rfl rfl

noncomputable def ep268 := @Enclosure.Real.IsNear.sin_image qz46 qz349 Bool.false 372694569 1048576 699 1048576 Bool.true 436423 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz46 Bool.false 200088873347547475863 562949953421312000 4006062503084539931 6015375000000000000000 372694569 1048576 699 1048576 (ep263 rfl) rfl) (Enclosure.sfrac_false_div 372694569 1048576) (BSN.sin_reduce2 qz349 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 64869216171763158745088) qz25) 226375608064910080 72057594037927936 Bool.false 436423 1048576 56 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q2 372694569 1048576 226375608064910080 72057594037927936 56 64869216171763158745088 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 436423 1048576 64869216171763158745088 151115727451828646838272 921847006 2147483648 385360 384984 (ep267 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz350 := (@Enclosure.Real.IsNear.recentre' qz45 Bool.false 262143 1048576 1 1048576 262143 1048576 1 1048576 (ep261 rfl rfl) rfl)

noncomputable def ep269 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz45 (Real.cos qz46)) (@HMul.hMul Real Real Real qz0 qz45 (@Neg.neg Real Real.instNeg (Real.sin qz46))) Bool.true 249937359777 1099511627776 8932595664421 52911798063464448 Bool.false 114405234489 1099511627776 8907715303453 52911798063464448 (@Enclosure.Real.IsNear.mulLit_ft qz45 (Real.cos qz46) 262143 1048576 1 1048576 953439 1048576 33900121 50460622848 249937359777 1099511627776 8932595664421 52911798063464448 qz350 (@Enclosure.Real.IsNear.recentre' (Real.cos qz46) Bool.true 953439 1048576 135600484 201842491392 953439 1048576 33900121 50460622848 (ep266 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz45 (@Neg.neg Real Real.instNeg (Real.sin qz46)) 262143 1048576 1 1048576 436423 1048576 33900121 50460622848 114405234489 1099511627776 8907715303453 52911798063464448 qz350 (@Enclosure.Real.IsNear.neg (Real.sin qz46) Bool.true 436423 1048576 33900121 50460622848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz46) Bool.true 436423 1048576 135600484 201842491392 436423 1048576 33900121 50460622848 (ep268 rfl rfl) rfl)) rfl)

noncomputable def ep270 := @ep157 249937359777 1099511627776 8932595664421 52911798063464448 Bool.false 114405234489 1099511627776 8907715303453 52911798063464448 Bool.false 418784649544439202578432 761764839889 1099511627776 201911535746669 52911798063464448 Bool.true 19635594896471083712512 35716939049 1099511627776 201983308121297 52911798063464448 (ep158 (BSN.head_sum_c_succ qz5 15 16 rfl rfl) (ep259 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep260 ep269) rfl rfl

theorem EMRow43.d7 : Enclosure.Complex.IsNear qz31 Bool.false 761764839889 1099511627776 201911535746669 52911798063464448 Bool.true 35716939049 1099511627776 201983308121297 52911798063464448 := ep156 (BSN.head_sum_c_succ qz5 16 17 rfl rfl) (ep270 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz47 := (BSN.headSumC qz271 25)

noncomputable abbrev qz560 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 24) qz7)

noncomputable def ep271 := @Enclosure.Complex.IsNear.of_eq qz47 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 24) qz560) Bool.false 2251041895485 1099511627776 265399267266013 52911798063464448 Bool.true 12002851551 274877906944 16586073004849 3306987378966528

noncomputable def ep272 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 24) qz560 Bool.false 532432057237 274877906944 2016531328663 413373422370816 Bool.true 118417663885 549755813888 129039366178441 26455899031732224 Bool.false

noncomputable abbrev qz561 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 23) qz7)

noncomputable def ep273 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 24) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 23) qz561) Bool.false 532432057237 274877906944 2016531328663 413373422370816 Bool.true 118417663885 549755813888 129039366178441 26455899031732224

noncomputable def ep274 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 23) qz561 Bool.false 1903869354019 1099511627776 250654240809571 52911798063464448 Bool.true 276200469419 1099511627776 250658010091669 52911798063464448 Bool.false

noncomputable def ep275 := nat_lit 2341660951731113084059648

noncomputable abbrev qz562 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 22) qz7)

noncomputable def ep276 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 23) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 22) qz562) Bool.false 1903869354019 1099511627776 250654240809571 52911798063464448 Bool.true 276200469419 1099511627776 250658010091669 52911798063464448

noncomputable def ep277 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 22) qz562 Bool.false 1689097249891 1099511627776 81009788533487 17637266021154816 Bool.true 91132138573 549755813888 5063732210123 1102329126322176 Bool.false

noncomputable abbrev qz563 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 21) qz7)

noncomputable def ep278 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 22) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 21) qz563) Bool.false 1689097249891 1099511627776 81009788533487 17637266021154816 Bool.true 91132138573 549755813888 5063732210123 1102329126322176

noncomputable def ep279 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 21) qz563 Bool.false 1510605938447 1099511627776 235186250946113 52911798063464448 Bool.true 10962548821 549755813888 14701479164171 3306987378966528 Bool.false

noncomputable abbrev qz564 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 20) qz7)

noncomputable def ep280 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 21) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 20) qz564) Bool.false 1510605938447 1099511627776 235186250946113 52911798063464448 Bool.true 10962548821 549755813888 14701479164171 3306987378966528

noncomputable def ep281 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 20) qz564 Bool.false 83280004601 68719476736 3155414544173 734886084214784 Bool.false 36884343027 274877906944 12623835608767 2939544336859136 Bool.false

noncomputable abbrev qz565 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 19) qz7)

noncomputable def ep282 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 20) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 19) qz565) Bool.false 83280004601 68719476736 3155414544173 734886084214784 Bool.false 36884343027 274877906944 12623835608767 2939544336859136

noncomputable def ep283 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 19) qz565 Bool.false 553695711453 549755813888 109489114696973 26455899031732224 Bool.false 261389376187 1099511627776 219039675679603 52911798063464448 Bool.false

noncomputable abbrev qz566 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 18) qz7)

noncomputable def ep284 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 19) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 18) qz566) Bool.false 553695711453 549755813888 109489114696973 26455899031732224 Bool.false 261389376187 1099511627776 219039675679603 52911798063464448

noncomputable def ep285 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 18) qz566 Bool.false 426203362405 549755813888 105275049190973 26455899031732224 Bool.false 215076244599 1099511627776 210652175301487 52911798063464448 Bool.false

noncomputable abbrev qz567 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 17) qz7)

noncomputable def ep286 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 18) (@HAdd.hAdd Complex Complex Complex qz4 qz31 qz567) Bool.false 426203362405 549755813888 105275049190973 26455899031732224 Bool.false 215076244599 1099511627776 210652175301487 52911798063464448

noncomputable def ep287 := @Enclosure.Complex.IsNear.addLitP qz31 qz567 Bool.false 761764839889 1099511627776 201911535746669 52911798063464448 Bool.true 35716939049 1099511627776 201983308121297 52911798063464448 Bool.false

noncomputable abbrev qz48 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 17)))

noncomputable abbrev qz568 := (Real.log (Enclosure.sfrac Bool.false 17 1))

noncomputable abbrev qz49 := (@HMul.hMul Real Real Real qz267 qz278 qz568)

noncomputable def ep288 := @Enclosure.Complex.IsNear.of_eq qz567 (Complex.mk (@HMul.hMul Real Real Real qz0 qz48 (Real.cos qz49)) (@HMul.hMul Real Real Real qz0 qz48 (@Neg.neg Real Real.instNeg (Real.sin qz49)))) Bool.false 90641884921 1099511627776 8638562635277 52911798063464448 Bool.false 7837286989 34359738368 4334433590095 26455899031732224 (BSN.cpow_neg_s_mk qz12 128194 1000 17 qz13 rfl)

noncomputable abbrev qz351 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 17) qz14)

noncomputable def ep289 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 17)) 4323389 1048576 1 1048576 127158 127159 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 17)) (Real.sqrt qz351) Bool.false 4323389 1048576 1 1048576 (BSN.sqrt_natCast_div_one 17) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz351) Bool.false 4323389 1048576 1 1048576 4323389 1048576 1 1048576 (BSN.sqrt_enclosure 17 1 2161694 2161695 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep290 := BSN.log_dyadic_bound 1 33 2 1 3267 524288 192492 1 1 31784 34 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1) (BSN.artanhQ 33) 0 1 1 3267 1 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep291 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz568 128194 1000 0 1 3189913004350711 1125899906842624 62500000048123 12030750000000000000 204463853839867522967 562949953421312000 4006062503084539931 6015375000000000000000 qz18 (BSN.isNear_log_sfrac 17 1 3189913004350711 1125899906842624 62500000048123 12030750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz351) Bool.false 53517859495200818200576 18889465931478580854784 1000000000769968 192492000000000000000 3189913004350711 1125899906842624 62500000048123 12030750000000000000 (BSN.log_rat_reduce_isNear 17 1 4 34 32 31784 524288 24973259072661432 36028797018963968 192492 1000000000000000 rfl rfl rfl rfl (ep290 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep292 := nat_lit 307681771361872572554416591817204881

noncomputable def ep293 := BSN.sin_dyadic_bound_f 744775603 2147483648 2 1 1048576 385360 ep292 ep92 ep292 ep292 ep93 ep292 356413 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 744775603) qz20 0 1 ep292 ep92 ep292 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 744775603) qz21 0 1 ep292 ep93 ep292 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz352 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 380843605) qz24)

noncomputable def ep294 := @Enclosure.Real.IsNear.cos_image qz49 qz352 Bool.false 380843605 1048576 699 1048576 Bool.false 356413 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz49 Bool.false 204463853839867522967 562949953421312000 4006062503084539931 6015375000000000000000 380843605 1048576 699 1048576 (ep291 rfl) rfl) (Enclosure.sfrac_false_div 380843605 1048576) (BSN.cos_reduce3 qz352 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 52408923937327630254080) qz25) 226375608064910080 72057594037927936 Bool.false 356413 1048576 57 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q3 380843605 1048576 226375608064910080 72057594037927936 57 52408923937327630254080 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 356413 1048576 52408923937327630254080 151115727451828646838272 744775603 2147483648 385360 384984 (ep293 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep295 := BSN.cos_dyadic_bound_f 744775603 2147483648 2 1 1048576 385360 ep292 ep96 ep292 ep292 ep97 ep292 986144 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 744775603) qz15 0 1 ep292 ep96 ep292 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 744775603) qz16 0 1 ep292 ep97 ep292 rfl rfl rfl rfl) rfl rfl

noncomputable def ep296 := @Enclosure.Real.IsNear.sin_image qz49 qz352 Bool.false 380843605 1048576 699 1048576 Bool.true 986144 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz49 Bool.false 204463853839867522967 562949953421312000 4006062503084539931 6015375000000000000000 380843605 1048576 699 1048576 (ep291 rfl) rfl) (Enclosure.sfrac_false_div 380843605 1048576) (BSN.sin_reduce3 qz352 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 52408923937327630254080) qz25) 226375608064910080 72057594037927936 Bool.false 986144 1048576 57 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q3 380843605 1048576 226375608064910080 72057594037927936 57 52408923937327630254080 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 986144 1048576 52408923937327630254080 151115727451828646838272 744775603 2147483648 385360 384984 (ep295 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz353 := (@Enclosure.Real.IsNear.recentre' qz48 Bool.false 254317 1048576 1 1048576 254317 1048576 1 1048576 (ep289 rfl rfl) rfl)

noncomputable def ep297 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz48 (Real.cos qz49)) (@HMul.hMul Real Real Real qz0 qz48 (@Neg.neg Real Real.instNeg (Real.sin qz49))) Bool.false 90641884921 1099511627776 8638562635277 52911798063464448 Bool.false 7837286989 34359738368 4334433590095 26455899031732224 (@Enclosure.Real.IsNear.mulLit_ff qz48 (Real.cos qz49) 254317 1048576 1 1048576 356413 1048576 33900121 50460622848 90641884921 1099511627776 8638562635277 52911798063464448 qz353 (@Enclosure.Real.IsNear.recentre' (Real.cos qz49) Bool.false 356413 1048576 135600484 201842491392 356413 1048576 33900121 50460622848 (ep294 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz48 (@Neg.neg Real Real.instNeg (Real.sin qz49)) 254317 1048576 1 1048576 30817 32768 33900121 50460622848 7837286989 34359738368 4334433590095 26455899031732224 qz353 (@Enclosure.Real.IsNear.neg (Real.sin qz49) Bool.true 30817 32768 33900121 50460622848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz49) Bool.true 986144 1048576 135600484 201842491392 30817 32768 33900121 50460622848 (ep296 rfl rfl) rfl)) rfl)

noncomputable def ep298 := @ep287 90641884921 1099511627776 8638562635277 52911798063464448 Bool.false 7837286989 34359738368 4334433590095 26455899031732224 Bool.false 937231105523051984322560 426203362405 549755813888 105275049190973 26455899031732224 Bool.false 7389963493593613074432 215076244599 1099511627776 210652175301487 52911798063464448 EMRow43.d7 (ep288 ep297) rfl rfl

noncomputable abbrev qz50 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 18)))

noncomputable abbrev qz569 := (Real.log (Enclosure.sfrac Bool.false 18 1))

noncomputable abbrev qz51 := (@HMul.hMul Real Real Real qz267 qz278 qz569)

noncomputable def ep299 := @Enclosure.Complex.IsNear.of_eq qz566 (Complex.mk (@HMul.hMul Real Real Real qz0 qz50 (Real.cos qz51)) (@HMul.hMul Real Real Real qz0 qz50 (@Neg.neg Real Real.instNeg (Real.sin qz51)))) Bool.false 15936543631 68719476736 87793031375 551164563161088 Bool.false 11578282897 274877906944 698958364843 4409316505288704 (BSN.cpow_neg_s_mk qz12 128194 1000 18 qz13 rfl)

noncomputable abbrev qz354 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 18) qz14)

noncomputable def ep300 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 18)) 4448731 1048576 1 1048576 123575 123576 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 18)) (Real.sqrt qz354) Bool.false 4448731 1048576 1 1048576 (BSN.sqrt_natCast_div_one 18) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz354) Bool.false 4448731 1048576 1 1048576 4448731 1048576 1 1048576 (BSN.sqrt_enclosure 18 1 2224365 2224366 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep301 := BSN.log_dyadic_bound 2 34 3 2 20045040 524288 192492 23168 48 61752 36 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 2) (BSN.artanhQ 34) 0 2 23168 20045040 48 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep302 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz569 128194 1000 0 1 3254268794313975 1125899906842624 62500000048123 12030750000000000000 8343554676365714223 22517998136852480 4006062503084539931 6015375000000000000000 qz18 (BSN.isNear_log_sfrac 18 1 3254268794313975 1125899906842624 62500000048123 12030750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz354) Bool.false 54597570484265130393600 18889465931478580854784 1000000000769968 192492000000000000000 3254268794313975 1125899906842624 62500000048123 12030750000000000000 (BSN.log_rat_reduce_isNear 18 1 4 36 32 61752 524288 24973259072661432 36028797018963968 192492 1000000000000000 rfl rfl rfl rfl (ep301 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep303 := nat_lit 5128860654202629248042945751339963713238798670160419934174425256626889114224225

noncomputable def ep304 := nat_lit 6344015816681912895740226027718775333644588395840833264245105357881826051681

noncomputable def ep305 := nat_lit 13422459021113210647805088030416931707942381469207833716600431215824329485551201

noncomputable def ep306 := BSN.sin_dyadic_bound_f 2987414827 2147483648 3 2 1048576 385360 ep303 ep64 ep304 ep305 ep66 ep304 1031696 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2987414827) qz20 0 2 ep303 ep64 ep304 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2987414827) qz21 0 2 ep305 ep66 ep304 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz355 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 388527041) qz24)

noncomputable def ep307 := @Enclosure.Real.IsNear.cos_image qz51 qz355 Bool.false 388527041 1048576 699 1048576 Bool.false 1031696 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz51 Bool.false 8343554676365714223 22517998136852480 4006062503084539931 6015375000000000000000 388527041 1048576 699 1048576 (ep302 rfl) rfl) (Enclosure.sfrac_false_div 388527041 1048576) (BSN.cos_reduce3 qz355 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 210220629737044759805952) qz25) 226375608064910080 72057594037927936 Bool.false 1031696 1048576 58 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q3 388527041 1048576 226375608064910080 72057594037927936 58 210220629737044759805952 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1031696 1048576 210220629737044759805952 151115727451828646838272 2987414827 2147483648 385360 384984 (ep306 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep308 := nat_lit 2852186592697763765755298851201188185280952411598384778214345189396219208369761

noncomputable def ep309 := nat_lit 8543871746459927471474416101548127005175568058003472668114545357472893973005921

noncomputable def ep310 := BSN.cos_dyadic_bound_f 2987414827 2147483648 3 2 1048576 385360 ep308 ep57 ep304 ep309 ep60 ep304 187388 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2987414827) qz15 0 2 ep308 ep57 ep304 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2987414827) qz16 0 2 ep309 ep60 ep304 rfl rfl rfl rfl) rfl rfl

noncomputable def ep311 := @Enclosure.Real.IsNear.sin_image qz51 qz355 Bool.false 388527041 1048576 699 1048576 Bool.true 187388 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz51 Bool.false 8343554676365714223 22517998136852480 4006062503084539931 6015375000000000000000 388527041 1048576 699 1048576 (ep302 rfl) rfl) (Enclosure.sfrac_false_div 388527041 1048576) (BSN.sin_reduce3 qz355 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 210220629737044759805952) qz25) 226375608064910080 72057594037927936 Bool.false 187388 1048576 58 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q3 388527041 1048576 226375608064910080 72057594037927936 58 210220629737044759805952 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 187388 1048576 210220629737044759805952 151115727451828646838272 2987414827 2147483648 385360 384984 (ep310 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz356 := (@Enclosure.Real.IsNear.recentre' qz50 Bool.false 247151 1048576 1 1048576 247151 1048576 1 1048576 (ep300 rfl rfl) rfl)

noncomputable def ep312 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz50 (Real.cos qz51)) (@HMul.hMul Real Real Real qz0 qz50 (@Neg.neg Real Real.instNeg (Real.sin qz51))) Bool.false 15936543631 68719476736 87793031375 551164563161088 Bool.false 11578282897 274877906944 698958364843 4409316505288704 (@Enclosure.Real.IsNear.mulLit_ff qz50 (Real.cos qz51) 247151 1048576 1 1048576 64481 65536 33900121 50460622848 15936543631 68719476736 87793031375 551164563161088 qz356 (@Enclosure.Real.IsNear.recentre' (Real.cos qz51) Bool.false 1031696 1048576 135600484 201842491392 64481 65536 33900121 50460622848 (ep307 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz50 (@Neg.neg Real Real.instNeg (Real.sin qz51)) 247151 1048576 1 1048576 46847 262144 33900121 50460622848 11578282897 274877906944 698958364843 4409316505288704 qz356 (@Enclosure.Real.IsNear.neg (Real.sin qz51) Bool.true 46847 262144 33900121 50460622848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz51) Bool.true 187388 1048576 135600484 201842491392 46847 262144 33900121 50460622848 (ep311 rfl rfl) rfl)) rfl)

noncomputable def ep313 := @ep285 15936543631 68719476736 87793031375 551164563161088 Bool.false 11578282897 274877906944 698958364843 4409316505288704 Bool.false 38049679562017402257408 553695711453 549755813888 109489114696973 26455899031732224 Bool.false 71850164623680395542528 261389376187 1099511627776 219039675679603 52911798063464448 (ep286 (BSN.head_sum_c_succ qz5 17 18 rfl rfl) (ep298 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep299 ep312) rfl rfl

noncomputable abbrev qz52 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 19)))

noncomputable abbrev qz570 := (Real.log (Enclosure.sfrac Bool.false 19 1))

noncomputable abbrev qz53 := (@HMul.hMul Real Real Real qz267 qz278 qz570)

noncomputable def ep314 := @Enclosure.Complex.IsNear.of_eq qz565 (Complex.mk (@HMul.hMul Real Real Real qz0 qz52 (Real.cos qz53)) (@HMul.hMul Real Real Real qz0 qz52 (@Neg.neg Real Real.instNeg (Real.sin qz53)))) Bool.false 112544325355 549755813888 4105808893255 26455899031732224 Bool.true 113852004079 1099511627776 8189365278203 52911798063464448 (BSN.cpow_neg_s_mk qz12 128194 1000 19 qz13 rfl)

noncomputable abbrev qz357 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 19) qz14)

noncomputable def ep315 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 19)) 4570637 1048576 1 1048576 120279 120280 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 19)) (Real.sqrt qz357) Bool.false 4570637 1048576 1 1048576 (BSN.sqrt_natCast_div_one 19) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz357) Bool.false 4570637 1048576 1 1048576 4570637 1048576 1 1048576 (BSN.sqrt_enclosure 19 1 2285318 2285319 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep316 := BSN.log_dyadic_bound 3 35 3 2 22509375 524288 192492 55368 243 90099 38 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 3) (BSN.artanhQ 35) 0 2 55368 22509375 243 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep317 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz570 128194 1000 0 1 3315143513283831 1125899906842624 62500000048123 12030750000000000000 212490753770953715607 562949953421312000 4006062503084539931 6015375000000000000000 qz18 (BSN.isNear_log_sfrac 19 1 3315143513283831 1125899906842624 62500000048123 12030750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz357) Bool.false 55618878793361701994496 18889465931478580854784 1000000000769968 192492000000000000000 3315143513283831 1125899906842624 62500000048123 12030750000000000000 (BSN.log_rat_reduce_isNear 19 1 4 38 32 90099 524288 24973259072661432 36028797018963968 192492 1000000000000000 rfl rfl rfl rfl (ep316 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep318 := nat_lit 1022725280534395431793287313663983616

noncomputable def ep319 := BSN.cos_dyadic_bound_f 1005633536 2147483648 2 1 1048576 385360 ep318 ep96 ep318 ep318 ep97 ep318 935690 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1005633536) qz15 0 1 ep318 ep96 ep318 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1005633536) qz16 0 1 ep318 ep97 ep318 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz358 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 395794871) qz24)

noncomputable def ep320 := @Enclosure.Real.IsNear.cos_image qz53 qz358 Bool.false 395794871 1048576 175 262144 Bool.false 935690 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz53 Bool.false 212490753770953715607 562949953421312000 4006062503084539931 6015375000000000000000 395794871 1048576 175 262144 (ep317 rfl) rfl) (Enclosure.sfrac_false_div 395794871 1048576) (BSN.cos_reduce0 qz358 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 70765169079036581773312) qz25) 226375608064910080 72057594037927936 Bool.false 935690 1048576 60 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q0 395794871 1048576 226375608064910080 72057594037927936 60 70765169079036581773312 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 935690 1048576 70765169079036581773312 151115727451828646838272 1005633536 2147483648 385360 384984 (ep319 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep321 := BSN.sin_dyadic_bound_f 1005633536 2147483648 2 1 1048576 385360 ep318 ep92 ep318 ep318 ep93 ep318 473281 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1005633536) qz20 0 1 ep318 ep92 ep318 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1005633536) qz21 0 1 ep318 ep93 ep318 rfl rfl rfl rfl) rfl rfl

noncomputable def ep322 := @Enclosure.Real.IsNear.sin_image qz53 qz358 Bool.false 395794871 1048576 175 262144 Bool.false 473281 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz53 Bool.false 212490753770953715607 562949953421312000 4006062503084539931 6015375000000000000000 395794871 1048576 175 262144 (ep317 rfl) rfl) (Enclosure.sfrac_false_div 395794871 1048576) (BSN.sin_reduce0 qz358 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 70765169079036581773312) qz25) 226375608064910080 72057594037927936 Bool.false 473281 1048576 60 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q0 395794871 1048576 226375608064910080 72057594037927936 60 70765169079036581773312 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 473281 1048576 70765169079036581773312 151115727451828646838272 1005633536 2147483648 385360 384984 (ep321 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz359 := (@Enclosure.Real.IsNear.recentre' qz52 Bool.false 240559 1048576 1 1048576 240559 1048576 1 1048576 (ep315 rfl rfl) rfl)

noncomputable def ep323 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz52 (Real.cos qz53)) (@HMul.hMul Real Real Real qz0 qz52 (@Neg.neg Real Real.instNeg (Real.sin qz53))) Bool.false 112544325355 549755813888 4105808893255 26455899031732224 Bool.true 113852004079 1099511627776 8189365278203 52911798063464448 (@Enclosure.Real.IsNear.mulLit_ff qz52 (Real.cos qz53) 240559 1048576 1 1048576 467845 524288 8487061 12615155712 112544325355 549755813888 4105808893255 26455899031732224 qz359 (@Enclosure.Real.IsNear.recentre' (Real.cos qz53) Bool.false 935690 1048576 33948244 50460622848 467845 524288 8487061 12615155712 (ep320 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz52 (@Neg.neg Real Real.instNeg (Real.sin qz53)) 240559 1048576 1 1048576 473281 1048576 8487061 12615155712 113852004079 1099511627776 8189365278203 52911798063464448 qz359 (@Enclosure.Real.IsNear.neg (Real.sin qz53) Bool.false 473281 1048576 8487061 12615155712 (@Enclosure.Real.IsNear.recentre' (Real.sin qz53) Bool.false 473281 1048576 33948244 50460622848 473281 1048576 8487061 12615155712 (ep322 rfl rfl) rfl)) rfl)

noncomputable def ep324 := @ep283 112544325355 549755813888 4105808893255 26455899031732224 Bool.true 113852004079 1099511627776 8189365278203 52911798063464448 Bool.false 366269333680153117589504 83280004601 68719476736 3155414544173 734886084214784 Bool.false 162219056164260500471808 36884343027 274877906944 12623835608767 2939544336859136 (ep284 (BSN.head_sum_c_succ qz5 18 19 rfl rfl) (ep313 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep314 ep323) rfl rfl

noncomputable abbrev qz54 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 20)))

noncomputable abbrev qz571 := (Real.log (Enclosure.sfrac Bool.false 20 1))

noncomputable abbrev qz55 := (@HMul.hMul Real Real Real qz267 qz278 qz571)

noncomputable def ep325 := @Enclosure.Complex.IsNear.of_eq qz564 (Complex.mk (@HMul.hMul Real Real Real qz0 qz54 (Real.cos qz55)) (@HMul.hMul Real Real Real qz0 qz54 (@Neg.neg Real Real.instNeg (Real.sin qz55)))) Bool.false 178125864831 1099511627776 7996403765657 52911798063464448 Bool.true 84731234875 549755813888 3997312834465 26455899031732224 (BSN.cpow_neg_s_mk qz12 128194 1000 20 qz13 rfl)

noncomputable abbrev qz360 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 20) qz14)

noncomputable def ep326 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 20)) 4689375 1048576 1 1048576 117234 117235 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 20)) (Real.sqrt qz360) Bool.false 4689375 1048576 1 1048576 (BSN.sqrt_natCast_div_one 20) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz360) Bool.false 4689375 1048576 1 1048576 4689375 1048576 1 1048576 (BSN.sqrt_enclosure 20 1 2344687 2344688 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep327 := BSN.log_dyadic_bound 4 36 3 2 25194240 524288 192492 104448 768 116991 40 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 4) (BSN.artanhQ 36) 0 2 104448 25194240 768 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep328 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz571 128194 1000 0 1 3372893643545847 1125899906842624 62500000048123 12030750000000000000 216192363870358155159 562949953421312000 4006062503084539931 6015375000000000000000 qz18 (BSN.isNear_log_sfrac 20 1 3372893643545847 1125899906842624 62500000048123 12030750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz360) Bool.false 56587765202795681021952 18889465931478580854784 1000000000769968 192492000000000000000 3372893643545847 1125899906842624 62500000048123 12030750000000000000 (BSN.log_rat_reduce_isNear 20 1 4 40 32 116991 524288 24973259072661432 36028797018963968 192492 1000000000000000 rfl rfl rfl rfl (ep327 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep329 := nat_lit 254205528666156705430093881741953175610582336329838165522990203950648524800000

noncomputable def ep330 := nat_lit 50598726742945126599000652598888029466143679105273520861303806361600000000

noncomputable def ep331 := nat_lit 762515388544984226037083643920661750772814721631303949527248004239222374400000

noncomputable def ep332 := BSN.cos_dyadic_bound_f 1633117560 2147483648 3 2 1048576 385360 ep329 ep57 ep330 ep331 ep60 ep330 759699 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1633117560) qz15 0 2 ep329 ep57 ep330 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1633117560) qz16 0 2 ep331 ep60 ep330 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz361 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 402689657) qz24)

noncomputable def ep333 := @Enclosure.Real.IsNear.cos_image qz55 qz361 Bool.false 402689657 1048576 175 262144 Bool.false 759699 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz55 Bool.false 216192363870358155159 562949953421312000 4006062503084539931 6015375000000000000000 402689657 1048576 175 262144 (ep328 rfl) rfl) (Enclosure.sfrac_false_div 402689657 1048576) (BSN.cos_reduce0 qz361 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 114920431802729977872384) qz25) 226375608064910080 72057594037927936 Bool.false 759699 1048576 61 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q0 402689657 1048576 226375608064910080 72057594037927936 61 114920431802729977872384 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 759699 1048576 114920431802729977872384 151115727451828646838272 1633117560 2147483648 385360 384984 (ep332 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep334 := nat_lit 7113278199462265274449092541032960000

noncomputable def ep335 := BSN.sin_dyadic_bound_f 1633117560 2147483648 2 1 1048576 385360 ep334 ep92 ep334 ep334 ep93 ep334 722750 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1633117560) qz20 0 1 ep334 ep92 ep334 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1633117560) qz21 0 1 ep334 ep93 ep334 rfl rfl rfl rfl) rfl rfl

noncomputable def ep336 := @Enclosure.Real.IsNear.sin_image qz55 qz361 Bool.false 402689657 1048576 175 262144 Bool.false 722750 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz55 Bool.false 216192363870358155159 562949953421312000 4006062503084539931 6015375000000000000000 402689657 1048576 175 262144 (ep328 rfl) rfl) (Enclosure.sfrac_false_div 402689657 1048576) (BSN.sin_reduce0 qz361 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 114920431802729977872384) qz25) 226375608064910080 72057594037927936 Bool.false 722750 1048576 61 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q0 402689657 1048576 226375608064910080 72057594037927936 61 114920431802729977872384 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 722750 1048576 114920431802729977872384 151115727451828646838272 1633117560 2147483648 385360 384984 (ep335 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz362 := (@Enclosure.Real.IsNear.recentre' qz54 Bool.false 234469 1048576 1 1048576 234469 1048576 1 1048576 (ep326 rfl rfl) rfl)

noncomputable def ep337 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz54 (Real.cos qz55)) (@HMul.hMul Real Real Real qz0 qz54 (@Neg.neg Real Real.instNeg (Real.sin qz55))) Bool.false 178125864831 1099511627776 7996403765657 52911798063464448 Bool.true 84731234875 549755813888 3997312834465 26455899031732224 (@Enclosure.Real.IsNear.mulLit_ff qz54 (Real.cos qz55) 234469 1048576 1 1048576 759699 1048576 8487061 12615155712 178125864831 1099511627776 7996403765657 52911798063464448 qz362 (@Enclosure.Real.IsNear.recentre' (Real.cos qz55) Bool.false 759699 1048576 33948244 50460622848 759699 1048576 8487061 12615155712 (ep333 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz54 (@Neg.neg Real Real.instNeg (Real.sin qz55)) 234469 1048576 1 1048576 361375 524288 8487061 12615155712 84731234875 549755813888 3997312834465 26455899031732224 qz362 (@Enclosure.Real.IsNear.neg (Real.sin qz55) Bool.false 361375 524288 8487061 12615155712 (@Enclosure.Real.IsNear.recentre' (Real.sin qz55) Bool.false 722750 1048576 33948244 50460622848 361375 524288 8487061 12615155712 (ep336 rfl rfl) rfl)) rfl)

noncomputable def ep338 := @ep281 178125864831 1099511627776 7996403765657 52911798063464448 Bool.true 84731234875 549755813888 3997312834465 26455899031732224 Bool.false 103808049644372064468992 1510605938447 1099511627776 235186250946113 52911798063464448 Bool.true 3013362474687894913024 10962548821 549755813888 14701479164171 3306987378966528 (ep282 (BSN.head_sum_c_succ qz5 19 20 rfl rfl) (ep324 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep325 ep337) rfl rfl

noncomputable abbrev qz56 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 21)))

noncomputable abbrev qz572 := (Real.log (Enclosure.sfrac Bool.false 21 1))

noncomputable abbrev qz57 := (@HMul.hMul Real Real Real qz267 qz278 qz572)

noncomputable def ep339 := @Enclosure.Complex.IsNear.of_eq qz563 (Complex.mk (@HMul.hMul Real Real Real qz0 qz56 (Real.cos qz57)) (@HMul.hMul Real Real Real qz0 qz56 (@Neg.neg Real Real.instNeg (Real.sin qz57)))) Bool.false 44622827861 274877906944 1960778663587 13227949515866112 Bool.true 10021198719 68719476736 244858733099 1653493689483264 (BSN.cpow_neg_s_mk qz12 128194 1000 21 qz13 rfl)

noncomputable abbrev qz363 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 21) qz14)

noncomputable def ep340 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 21)) 4805179 1048576 1 1048576 114408 114410 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 21)) (Real.sqrt qz363) Bool.false 4805179 1048576 1 1048576 (BSN.sqrt_natCast_div_one 21) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz363) Bool.false 4805179 1048576 1 1048576 4805179 1048576 1 1048576 (BSN.sqrt_enclosure 21 1 2402589 2402590 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep341 := BSN.log_dyadic_bound 5 37 4 3 269401272945 524288 192492 1658093375 234375 142571 42 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 5) (BSN.artanhQ 37) 0 3 1658093375 269401272945 234375 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep342 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz572 128194 1000 0 1 3427826275261687 1125899906842624 62500000048123 12030750000000000000 219713380765448351639 562949953421312000 4006062503084539931 6015375000000000000000 qz18 (BSN.isNear_log_sfrac 21 1 3427826275261687 1125899906842624 62500000048123 12030750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz363) Bool.false 57509381830540779323392 18889465931478580854784 1000000000769968 192492000000000000000 3427826275261687 1125899906842624 62500000048123 12030750000000000000 (BSN.log_rat_reduce_isNear 21 1 4 42 32 142571 524288 24973259072661432 36028797018963968 192492 1000000000000000 rfl rfl rfl rfl (ep341 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep343 := nat_lit 218059046727577379984383670560287228956907596294605126324034043805430867690625

noncomputable def ep344 := nat_lit 37234232256294845591534967784798073489987348435136568994551573981062890625

noncomputable def ep345 := nat_lit 654102671718219550261967941745292090723742814186945105834113028268330477290625

noncomputable def ep346 := BSN.cos_dyadic_bound_f 1571693295 2147483648 3 2 1048576 385360 ep343 ep57 ep344 ep345 ep60 ep344 780058 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1571693295) qz15 0 2 ep343 ep57 ep344 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1571693295) qz16 0 2 ep345 ep60 ep344 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz364 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 204624031) qz17)

noncomputable def ep347 := @Enclosure.Real.IsNear.cos_image qz57 qz364 Bool.false 204624031 524288 175 262144 Bool.false 780058 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz57 Bool.false 219713380765448351639 562949953421312000 4006062503084539931 6015375000000000000000 204624031 524288 175 262144 (ep342 rfl) rfl) (Enclosure.sfrac_false_div 204624031 524288) (BSN.cos_reduce0 qz364 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 55299041723139449946112) qz19) 226375608064910080 72057594037927936 Bool.false 780058 1048576 62 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q0 204624031 524288 226375608064910080 72057594037927936 62 55299041723139449946112 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 780058 1048576 55299041723139449946112 75557863725914323419136 1571693295 2147483648 385360 384984 (ep346 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep348 := nat_lit 6101985927244903568955329551246850625

noncomputable def ep349 := BSN.sin_dyadic_bound_f 1571693295 2147483648 2 1 1048576 385360 ep348 ep92 ep348 ep348 ep93 ep348 700728 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1571693295) qz20 0 1 ep348 ep92 ep348 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1571693295) qz21 0 1 ep348 ep93 ep348 rfl rfl rfl rfl) rfl rfl

noncomputable def ep350 := @Enclosure.Real.IsNear.sin_image qz57 qz364 Bool.false 204624031 524288 175 262144 Bool.false 700728 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz57 Bool.false 219713380765448351639 562949953421312000 4006062503084539931 6015375000000000000000 204624031 524288 175 262144 (ep342 rfl) rfl) (Enclosure.sfrac_false_div 204624031 524288) (BSN.sin_reduce0 qz364 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 55299041723139449946112) qz19) 226375608064910080 72057594037927936 Bool.false 700728 1048576 62 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q0 204624031 524288 226375608064910080 72057594037927936 62 55299041723139449946112 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 700728 1048576 55299041723139449946112 75557863725914323419136 1571693295 2147483648 385360 384984 (ep349 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz365 := (@Enclosure.Real.IsNear.recentre' qz56 Bool.false 228818 1048576 2 1048576 114409 524288 1 524288 (ep340 rfl rfl) rfl)

noncomputable def ep351 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz56 (Real.cos qz57)) (@HMul.hMul Real Real Real qz0 qz56 (@Neg.neg Real Real.instNeg (Real.sin qz57))) Bool.false 44622827861 274877906944 1960778663587 13227949515866112 Bool.true 10021198719 68719476736 244858733099 1653493689483264 (@Enclosure.Real.IsNear.mulLit_ff qz56 (Real.cos qz57) 114409 524288 1 524288 390029 524288 8487061 12615155712 44622827861 274877906944 1960778663587 13227949515866112 qz365 (@Enclosure.Real.IsNear.recentre' (Real.cos qz57) Bool.false 780058 1048576 33948244 50460622848 390029 524288 8487061 12615155712 (ep347 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz56 (@Neg.neg Real Real.instNeg (Real.sin qz57)) 114409 524288 1 524288 87591 131072 8487061 12615155712 10021198719 68719476736 244858733099 1653493689483264 qz365 (@Enclosure.Real.IsNear.neg (Real.sin qz57) Bool.false 87591 131072 8487061 12615155712 (@Enclosure.Real.IsNear.recentre' (Real.sin qz57) Bool.false 700728 1048576 33948244 50460622848 87591 131072 8487061 12615155712 (ep350 rfl rfl) rfl)) rfl)

noncomputable def ep352 := @ep279 44622827861 274877906944 1960778663587 13227949515866112 Bool.true 10021198719 68719476736 244858733099 1653493689483264 Bool.false 464295516674904612143104 1689097249891 1099511627776 81009788533487 17637266021154816 Bool.true 6262552876569201737728 91132138573 549755813888 5063732210123 1102329126322176 (ep280 (BSN.head_sum_c_succ qz5 20 21 rfl rfl) (ep338 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep339 ep351) rfl rfl

noncomputable abbrev qz58 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 22)))

noncomputable abbrev qz573 := (Real.log (Enclosure.sfrac Bool.false 22 1))

noncomputable abbrev qz59 := (@HMul.hMul Real Real Real qz267 qz278 qz573)

noncomputable def ep353 := @Enclosure.Complex.IsNear.of_eq qz562 (Complex.mk (@HMul.hMul Real Real Real qz0 qz58 (Real.cos qz59)) (@HMul.hMul Real Real Real qz0 qz58 (@Neg.neg Real Real.instNeg (Real.sin qz59)))) Bool.false 3355814127 17179869184 3812437604555 26455899031732224 Bool.true 93936192273 1099511627776 7598864005765 52911798063464448 (BSN.cpow_neg_s_mk qz12 128194 1000 22 qz13 rfl)

noncomputable abbrev qz366 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 22) qz14)

noncomputable def ep354 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 22)) 4918257 1048576 1 1048576 111778 111779 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 22)) (Real.sqrt qz366) Bool.false 4918257 1048576 1 1048576 (BSN.sqrt_natCast_div_one 22) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz366) Bool.false 4918257 1048576 1 1048576 4918257 1048576 1 1048576 (BSN.sqrt_enclosure 22 1 2459128 2459129 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep355 := BSN.log_dyadic_bound 6 38 4 3 316148320320 524288 192492 2667271104 699840 166961 44 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 6) (BSN.artanhQ 38) 0 3 2667271104 316148320320 699840 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep356 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz573 128194 1000 0 1 3480203401436407 1125899906842624 62500000048123 12030750000000000000 223070597421869379479 562949953421312000 4006062503084539931 6015375000000000000000 qz18 (BSN.isNear_log_sfrac 22 1 3480203401436407 1125899906842624 62500000048123 12030750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz366) Bool.false 58388124189833310502912 18889465931478580854784 1000000000769968 192492000000000000000 3480203401436407 1125899906842624 62500000048123 12030750000000000000 (BSN.log_rat_reduce_isNear 22 1 4 44 32 166961 524288 24973259072661432 36028797018963968 192492 1000000000000000 rfl rfl rfl rfl (ep355 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep357 := nat_lit 614612790048260426847836216443569121

noncomputable def ep358 := BSN.cos_dyadic_bound_f 885422183 2147483648 2 1 1048576 385360 ep357 ep96 ep357 ep357 ep97 ep357 960704 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 885422183) qz15 0 1 ep357 ep96 ep357 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 885422183) qz16 0 1 ep357 ep97 ep357 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz367 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 207750683) qz17)

noncomputable def ep359 := @Enclosure.Real.IsNear.cos_image qz59 qz367 Bool.false 207750683 524288 699 1048576 Bool.false 960704 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz59 Bool.false 223070597421869379479 562949953421312000 4006062503084539931 6015375000000000000000 207750683 524288 699 1048576 (ep356 rfl) rfl) (Enclosure.sfrac_false_div 207750683 524288) (BSN.cos_reduce0 qz367 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 31153023546348059754496) qz19) 226375608064910080 72057594037927936 Bool.false 960704 1048576 63 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q0 207750683 524288 226375608064910080 72057594037927936 63 31153023546348059754496 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 960704 1048576 31153023546348059754496 75557863725914323419136 885422183 2147483648 385360 384984 (ep358 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep360 := BSN.sin_dyadic_bound_f 885422183 2147483648 2 1 1048576 385360 ep357 ep92 ep357 ep357 ep93 ep357 420189 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 885422183) qz20 0 1 ep357 ep92 ep357 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 885422183) qz21 0 1 ep357 ep93 ep357 rfl rfl rfl rfl) rfl rfl

noncomputable def ep361 := @Enclosure.Real.IsNear.sin_image qz59 qz367 Bool.false 207750683 524288 699 1048576 Bool.false 420189 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz59 Bool.false 223070597421869379479 562949953421312000 4006062503084539931 6015375000000000000000 207750683 524288 699 1048576 (ep356 rfl) rfl) (Enclosure.sfrac_false_div 207750683 524288) (BSN.sin_reduce0 qz367 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 31153023546348059754496) qz19) 226375608064910080 72057594037927936 Bool.false 420189 1048576 63 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q0 207750683 524288 226375608064910080 72057594037927936 63 31153023546348059754496 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 420189 1048576 31153023546348059754496 75557863725914323419136 885422183 2147483648 385360 384984 (ep360 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz368 := (@Enclosure.Real.IsNear.recentre' qz58 Bool.false 223557 1048576 1 1048576 223557 1048576 1 1048576 (ep354 rfl rfl) rfl)

noncomputable def ep362 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz58 (Real.cos qz59)) (@HMul.hMul Real Real Real qz0 qz58 (@Neg.neg Real Real.instNeg (Real.sin qz59))) Bool.false 3355814127 17179869184 3812437604555 26455899031732224 Bool.true 93936192273 1099511627776 7598864005765 52911798063464448 (@Enclosure.Real.IsNear.mulLit_ff qz58 (Real.cos qz59) 223557 1048576 1 1048576 15011 16384 33900121 50460622848 3355814127 17179869184 3812437604555 26455899031732224 qz368 (@Enclosure.Real.IsNear.recentre' (Real.cos qz59) Bool.false 960704 1048576 135600484 201842491392 15011 16384 33900121 50460622848 (ep359 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz58 (@Neg.neg Real Real.instNeg (Real.sin qz59)) 223557 1048576 1 1048576 420189 1048576 33900121 50460622848 93936192273 1099511627776 7598864005765 52911798063464448 qz368 (@Enclosure.Real.IsNear.neg (Real.sin qz59) Bool.false 420189 1048576 33900121 50460622848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz59) Bool.false 420189 1048576 135600484 201842491392 420189 1048576 33900121 50460622848 (ep361 rfl rfl) rfl)) rfl)

noncomputable def ep363 := @ep277 3355814127 17179869184 3812437604555 26455899031732224 Bool.true 93936192273 1099511627776 7598864005765 52911798063464448 Bool.false 32708226445473004650496 1903869354019 1099511627776 250654240809571 52911798063464448 Bool.true 151842813861689999491072 276200469419 1099511627776 250658010091669 52911798063464448 (ep278 (BSN.head_sum_c_succ qz5 21 22 rfl rfl) (ep352 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep353 ep362) rfl rfl

noncomputable abbrev qz60 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 23)))

noncomputable abbrev qz574 := (Real.log (Enclosure.sfrac Bool.false 23 1))

noncomputable abbrev qz61 := (@HMul.hMul Real Real Real qz267 qz278 qz574)

noncomputable def ep364 := @Enclosure.Complex.IsNear.of_eq qz561 (Complex.mk (@HMul.hMul Real Real Real qz0 qz60 (Real.cos qz61)) (@HMul.hMul Real Real Real qz0 qz60 (@Neg.neg Real Real.instNeg (Real.sin qz61)))) Bool.false 225858874929 1099511627776 7461769259293 52911798063464448 Bool.false 39365141649 1099511627776 7420722265213 52911798063464448 (BSN.cpow_neg_s_mk qz12 128194 1000 23 qz13 rfl)

noncomputable abbrev qz369 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 23) qz14)

noncomputable def ep365 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 23)) 5028793 1048576 1 1048576 109321 109322 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 23)) (Real.sqrt qz369) Bool.false 5028793 1048576 1 1048576 (BSN.sqrt_natCast_div_one 23) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz369) Bool.false 5028793 1048576 1 1048576 5028793 1048576 1 1048576 (BSN.sqrt_enclosure 23 1 2514396 2514397 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep366 := BSN.log_dyadic_bound 7 39 4 3 369468094905 524288 192492 4046006391 1764735 190266 46 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 7) (BSN.artanhQ 39) 0 3 4046006391 369468094905 1764735 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep367 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz574 128194 1000 0 1 3530250507853047 1125899906842624 62500000048123 12030750000000000000 226278466801856753559 562949953421312000 4006062503084539931 6015375000000000000000 qz18 (BSN.isNear_log_sfrac 23 1 3530250507853047 1125899906842624 62500000048123 12030750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz369) Bool.false 59227775304360265777152 18889465931478580854784 1000000000769968 192492000000000000000 3530250507853047 1125899906842624 62500000048123 12030750000000000000 (BSN.log_rat_reduce_isNear 23 1 4 46 32 190266 524288 24973259072661432 36028797018963968 192492 1000000000000000 rfl rfl rfl rfl (ep366 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep368 := nat_lit 5234726685255253329224290140415968244413830678557309899884043534937714851840000

noncomputable def ep369 := nat_lit 6608278407724293087666136584497928990324102777039387393900169238937600000000

noncomputable def ep370 := nat_lit 13699299343960776530588348051381205897956650848868224062963323269878592307200000

noncomputable def ep371 := BSN.sin_dyadic_bound_f 3002693760 2147483648 3 2 1048576 385360 ep368 ep64 ep369 ep370 ep66 ep369 1033003 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3002693760) qz20 0 2 ep368 ep64 ep369 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3002693760) qz21 0 2 ep370 ep66 ep369 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz370 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 52684561) (@Nat.cast Real Real.instNatCast 131072))

noncomputable abbrev qz371 := (@Nat.cast Real Real.instNatCast 18889465931478580854784)

noncomputable def ep372 := @Enclosure.Real.IsNear.cos_image qz61 qz370 Bool.false 52684561 131072 699 1048576 Bool.false 1033003 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz61 Bool.false 226278466801856753559 562949953421312000 4006062503084539931 6015375000000000000000 52684561 131072 699 1048576 (ep367 rfl) rfl) (Enclosure.sfrac_false_div 52684561 131072) (BSN.cos_reduce3 qz370 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26411973636508344123392) qz371) 226375608064910080 72057594037927936 Bool.false 1033003 1048576 63 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q3 52684561 131072 226375608064910080 72057594037927936 63 26411973636508344123392 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1033003 1048576 26411973636508344123392 18889465931478580854784 3002693760 2147483648 385360 384984 (ep371 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep373 := nat_lit 2911118504434129313163568360935314770892272200432745227666202039071591628800000

noncomputable def ep374 := nat_lit 8720138956486939353315372809636948454696168395744156908210805778736899686400000

noncomputable def ep375 := BSN.cos_dyadic_bound_f 3002693760 2147483648 3 2 1048576 385360 ep373 ep57 ep369 ep374 ep60 ep369 180043 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3002693760) qz15 0 2 ep373 ep57 ep369 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3002693760) qz16 0 2 ep374 ep60 ep369 rfl rfl rfl rfl) rfl rfl

noncomputable def ep376 := @Enclosure.Real.IsNear.sin_image qz61 qz370 Bool.false 52684561 131072 699 1048576 Bool.true 180043 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz61 Bool.false 226278466801856753559 562949953421312000 4006062503084539931 6015375000000000000000 52684561 131072 699 1048576 (ep367 rfl) rfl) (Enclosure.sfrac_false_div 52684561 131072) (BSN.sin_reduce3 qz370 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26411973636508344123392) qz371) 226375608064910080 72057594037927936 Bool.false 180043 1048576 63 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q3 52684561 131072 226375608064910080 72057594037927936 63 26411973636508344123392 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 180043 1048576 26411973636508344123392 18889465931478580854784 3002693760 2147483648 385360 384984 (ep375 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz372 := (@Enclosure.Real.IsNear.recentre' qz60 Bool.false 218643 1048576 1 1048576 218643 1048576 1 1048576 (ep365 rfl rfl) rfl)

noncomputable def ep377 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz60 (Real.cos qz61)) (@HMul.hMul Real Real Real qz0 qz60 (@Neg.neg Real Real.instNeg (Real.sin qz61))) Bool.false 225858874929 1099511627776 7461769259293 52911798063464448 Bool.false 39365141649 1099511627776 7420722265213 52911798063464448 (@Enclosure.Real.IsNear.mulLit_ff qz60 (Real.cos qz61) 218643 1048576 1 1048576 1033003 1048576 33900121 50460622848 225858874929 1099511627776 7461769259293 52911798063464448 qz372 (@Enclosure.Real.IsNear.recentre' (Real.cos qz61) Bool.false 1033003 1048576 135600484 201842491392 1033003 1048576 33900121 50460622848 (ep372 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz60 (@Neg.neg Real Real.instNeg (Real.sin qz61)) 218643 1048576 1 1048576 180043 1048576 33900121 50460622848 39365141649 1099511627776 7420722265213 52911798063464448 qz372 (@Enclosure.Real.IsNear.neg (Real.sin qz61) Bool.true 180043 1048576 33900121 50460622848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz61) Bool.true 180043 1048576 135600484 201842491392 180043 1048576 33900121 50460622848 (ep376 rfl rfl) rfl)) rfl)

noncomputable def ep378 := @ep274 225858874929 1099511627776 7461769259293 52911798063464448 Bool.false 39365141649 1099511627776 7420722265213 52911798063464448 Bool.false ep275 532432057237 274877906944 2016531328663 413373422370816 Bool.true 260403196751255196139520 118417663885 549755813888 129039366178441 26455899031732224 (ep276 (BSN.head_sum_c_succ qz5 22 23 rfl rfl) (ep363 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep364 ep377) rfl rfl

noncomputable abbrev qz62 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 24)))

noncomputable abbrev qz575 := (Real.log (Enclosure.sfrac Bool.false 24 1))

noncomputable abbrev qz63 := (@HMul.hMul Real Real Real qz267 qz278 qz575)

noncomputable def ep379 := @Enclosure.Complex.IsNear.of_eq qz560 (Complex.mk (@HMul.hMul Real Real Real qz0 qz62 (Real.cos qz63)) (@HMul.hMul Real Real Real qz0 qz62 (@Neg.neg Real Real.instNeg (Real.sin qz63)))) Bool.false 121313666537 1099511627776 7283257197149 52911798063464448 Bool.false 94411960783 549755813888 3649217860351 26455899031732224 (BSN.cpow_neg_s_mk qz12 128194 1000 24 qz13 rfl)

noncomputable abbrev qz373 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 24) qz14)

noncomputable def ep380 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 24)) 5136953 1048576 1 1048576 107019 107020 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 24)) (Real.sqrt qz373) Bool.false 5136953 1048576 1 1048576 (BSN.sqrt_natCast_div_one 24) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz373) Bool.false 5136953 1048576 1 1048576 5136953 1048576 1 1048576 (BSN.sqrt_enclosure 24 1 2568476 2568477 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep381 := BSN.log_dyadic_bound 8 40 4 3 430080000000 524288 192492 5875957760 3932160 212580 48 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 8) (BSN.artanhQ 40) 0 3 5875957760 430080000000 3932160 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep382 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz575 128194 1000 0 1 3578169457974519 1125899906842624 62500000048123 12030750000000000000 229349927747792744343 562949953421312000 4006062503084539931 6015375000000000000000 qz18 (BSN.isNear_log_sfrac 24 1 3578169457974519 1125899906842624 62500000048123 12030750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz373) Bool.false 60031721881041427759104 18889465931478580854784 1000000000769968 192492000000000000000 3578169457974519 1125899906842624 62500000048123 12030750000000000000 (BSN.log_rat_reduce_isNear 24 1 4 48 32 212580 524288 24973259072661432 36028797018963968 192492 1000000000000000 rfl rfl rfl rfl (ep381 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep383 := nat_lit 2261818977566339427212997970766073856

noncomputable def ep384 := BSN.sin_dyadic_bound_f 1226350072 2147483648 2 1 1048576 385360 ep383 ep92 ep383 ep383 ep93 ep383 566783 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1226350072) qz20 0 1 ep383 ep92 ep383 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1226350072) qz21 0 1 ep383 ep93 ep383 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz374 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 213598765) qz17)

noncomputable def ep385 := @Enclosure.Real.IsNear.cos_image qz63 qz374 Bool.false 213598765 524288 699 1048576 Bool.false 566783 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz63 Bool.false 229349927747792744343 562949953421312000 4006062503084539931 6015375000000000000000 213598765 524288 699 1048576 (ep382 rfl) rfl) (Enclosure.sfrac_false_div 213598765 524288) (BSN.cos_reduce3 qz374 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 43148357251426387230720) qz19) 226375608064910080 72057594037927936 Bool.false 566783 1048576 64 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q3 213598765 524288 226375608064910080 72057594037927936 64 43148357251426387230720 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 566783 1048576 43148357251426387230720 75557863725914323419136 1226350072 2147483648 385360 384984 (ep384 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep386 := BSN.cos_dyadic_bound_f 1226350072 2147483648 2 1 1048576 385360 ep383 ep96 ep383 ep383 ep97 ep383 882194 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1226350072) qz15 0 1 ep383 ep96 ep383 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1226350072) qz16 0 1 ep383 ep97 ep383 rfl rfl rfl rfl) rfl rfl

noncomputable def ep387 := @Enclosure.Real.IsNear.sin_image qz63 qz374 Bool.false 213598765 524288 699 1048576 Bool.true 882194 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz63 Bool.false 229349927747792744343 562949953421312000 4006062503084539931 6015375000000000000000 213598765 524288 699 1048576 (ep382 rfl) rfl) (Enclosure.sfrac_false_div 213598765 524288) (BSN.sin_reduce3 qz374 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 43148357251426387230720) qz19) 226375608064910080 72057594037927936 Bool.false 882194 1048576 64 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q3 213598765 524288 226375608064910080 72057594037927936 64 43148357251426387230720 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 882194 1048576 43148357251426387230720 75557863725914323419136 1226350072 2147483648 385360 384984 (ep386 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz375 := (@Enclosure.Real.IsNear.recentre' qz62 Bool.false 214039 1048576 1 1048576 214039 1048576 1 1048576 (ep380 rfl rfl) rfl)

noncomputable def ep388 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz62 (Real.cos qz63)) (@HMul.hMul Real Real Real qz0 qz62 (@Neg.neg Real Real.instNeg (Real.sin qz63))) Bool.false 121313666537 1099511627776 7283257197149 52911798063464448 Bool.false 94411960783 549755813888 3649217860351 26455899031732224 (@Enclosure.Real.IsNear.mulLit_ff qz62 (Real.cos qz63) 214039 1048576 1 1048576 566783 1048576 33900121 50460622848 121313666537 1099511627776 7283257197149 52911798063464448 qz375 (@Enclosure.Real.IsNear.recentre' (Real.cos qz63) Bool.false 566783 1048576 135600484 201842491392 566783 1048576 33900121 50460622848 (ep385 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz62 (@Neg.neg Real Real.instNeg (Real.sin qz63)) 214039 1048576 1 1048576 441097 524288 33900121 50460622848 94411960783 549755813888 3649217860351 26455899031732224 qz375 (@Enclosure.Real.IsNear.neg (Real.sin qz63) Bool.true 441097 524288 33900121 50460622848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz63) Bool.true 882194 1048576 135600484 201842491392 441097 524288 33900121 50460622848 (ep387 rfl rfl) rfl)) rfl)

noncomputable def ep389 := @ep272 121313666537 1099511627776 7283257197149 52911798063464448 Bool.false 94411960783 549755813888 3649217860351 26455899031732224 Bool.false 618761684674171203747840 2251041895485 1099511627776 265399267266013 52911798063464448 Bool.true 13197274846793696280576 12002851551 274877906944 16586073004849 3306987378966528 (ep273 (BSN.head_sum_c_succ qz5 23 24 rfl rfl) (ep378 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep379 ep388) rfl rfl

theorem EMRow43.d8 : Enclosure.Complex.IsNear qz47 Bool.false 2251041895485 1099511627776 265399267266013 52911798063464448 Bool.true 12002851551 274877906944 16586073004849 3306987378966528 := ep271 (BSN.head_sum_c_succ qz5 24 25 rfl rfl) (ep389 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz576 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 32) qz7)

noncomputable def ep390 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 33) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 32) qz576) Bool.false 1034081122067 549755813888 159532442385535 26455899031732224 Bool.false 25505546097 274877906944 159529748556241 26455899031732224

noncomputable def ep391 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 32) qz576 Bool.false 2116025751179 1099511627776 312759676389809 52911798063464448 Bool.true 86359452067 1099511627776 312717808128611 52911798063464448 Bool.true

noncomputable def ep392 := nat_lit 2273968435552639447465984

noncomputable abbrev qz577 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 31) qz7)

noncomputable def ep393 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 32) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 31) qz577) Bool.false 2116025751179 1099511627776 312759676389809 52911798063464448 Bool.true 86359452067 1099511627776 312717808128611 52911798063464448

noncomputable def ep394 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 31) qz577 Bool.false 1933642297709 1099511627776 102109554281663 17637266021154816 Bool.true 5319852999 549755813888 51052341659863 8818633010577408 Bool.false

noncomputable abbrev qz578 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 30) qz7)

noncomputable def ep395 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 31) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 30) qz578) Bool.false 1933642297709 1099511627776 102109554281663 17637266021154816 Bool.true 5319852999 549755813888 51052341659863 8818633010577408

noncomputable def ep396 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 30) qz578 Bool.false 2091172701803 1099511627776 299789876825119 52911798063464448 Bool.false 113785800207 1099511627776 299783585512837 52911798063464448 Bool.true

noncomputable abbrev qz579 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 29) qz7)

noncomputable def ep397 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 30) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 29) qz579) Bool.false 2091172701803 1099511627776 299789876825119 52911798063464448 Bool.false 113785800207 1099511627776 299783585512837 52911798063464448

noncomputable def ep398 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 29) qz579 Bool.false 2151912488333 1099511627776 32574885475513 5879088673718272 Bool.true 5071473813 68719476736 16285250753821 2939544336859136 Bool.true

noncomputable abbrev qz580 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 28) qz7)

noncomputable def ep399 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 29) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 28) qz580) Bool.false 2151912488333 1099511627776 32574885475513 5879088673718272 Bool.true 5071473813 68719476736 16285250753821 2939544336859136

noncomputable def ep400 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 28) qz580 Bool.false 972465518335 549755813888 143202960590075 26455899031732224 Bool.true 99442943243 1099511627776 286412286072499 52911798063464448 Bool.false

noncomputable abbrev qz581 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 27) qz7)

noncomputable def ep401 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 28) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 27) qz581) Bool.false 972465518335 549755813888 143202960590075 26455899031732224 Bool.true 99442943243 1099511627776 286412286072499 52911798063464448

noncomputable def ep402 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 27) qz581 Bool.false 1936918203777 1099511627776 279562965942389 52911798063464448 Bool.false 56003345167 549755813888 139760408634235 26455899031732224 Bool.false

noncomputable def ep403 := nat_lit 2138474290041094846545920

noncomputable abbrev qz582 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 26) qz7)

noncomputable def ep404 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 27) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 26) qz582) Bool.false 1936918203777 1099511627776 279562965942389 52911798063464448 Bool.false 56003345167 549755813888 139760408634235 26455899031732224

noncomputable def ep405 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 26) qz582 Bool.false 1074835243965 549755813888 68132981648255 13227949515866112 Bool.false 73565668653 549755813888 136265672489221 26455899031732224 Bool.true

noncomputable abbrev qz583 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 25) qz7)

noncomputable def ep406 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 26) (@HAdd.hAdd Complex Complex Complex qz4 qz47 qz583) Bool.false 1074835243965 549755813888 68132981648255 13227949515866112 Bool.false 73565668653 549755813888 136265672489221 26455899031732224

noncomputable def ep407 := @Enclosure.Complex.IsNear.addLitP qz47 qz583 Bool.false 2251041895485 1099511627776 265399267266013 52911798063464448 Bool.true 12002851551 274877906944 16586073004849 3306987378966528 Bool.true

noncomputable def ep408 := nat_lit 2363587697365942460743680

noncomputable abbrev qz64 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 25)))

noncomputable abbrev qz584 := (Real.log (Enclosure.sfrac Bool.false 25 1))

noncomputable abbrev qz65 := (@HMul.hMul Real Real Real qz267 qz278 qz584)

noncomputable def ep409 := @Enclosure.Complex.IsNear.of_eq qz583 (Complex.mk (@HMul.hMul Real Real Real qz0 qz64 (Real.cos qz65)) (@HMul.hMul Real Real Real qz0 qz64 (@Neg.neg Real Real.instNeg (Real.sin qz65)))) Bool.true 101371407555 1099511627776 7132659327007 52911798063464448 Bool.false 97571371755 549755813888 3577088450429 26455899031732224 (BSN.cpow_neg_s_mk qz12 128194 1000 25 qz13 rfl)

noncomputable abbrev qz376 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 25) qz14)

noncomputable def ep410 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 25)) 5242881 1048576 1 1048576 104857 104858 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 25)) (Real.sqrt qz376) Bool.false 5242881 1048576 1 1048576 (BSN.sqrt_natCast_div_one 25) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz376) Bool.false 5242881 1048576 1 1048576 5242881 1048576 1 1048576 (BSN.sqrt_enclosure 25 1 2621440 2621441 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep411 := BSN.log_dyadic_bound 9 41 5 4 7545754341519345 524288 192492 124828057765224 4519905705 233982 50 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 9) (BSN.artanhQ 41) 0 4 124828057765224 7545754341519345 4519905705 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep412 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz584 128194 1000 0 1 3624129903009015 1125899906842624 62500000048123 12030750000000000000 46459170878633766891 112589990684262400 4006062503084539931 6015375000000000000000 qz18 (BSN.isNear_log_sfrac 25 1 3624129903009015 1125899906842624 62500000048123 12030750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz376) Bool.false 60802810194841294602240 18889465931478580854784 1000000000769968 192492000000000000000 3624129903009015 1125899906842624 62500000048123 12030750000000000000 (BSN.log_rat_reduce_isNear 25 1 4 50 32 233982 524288 24973259072661432 36028797018963968 192492 1000000000000000 rfl rfl rfl rfl (ep411 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep413 := nat_lit 1080227740472095641005039540465771314400428278322436943729637874513288674348161

noncomputable def ep414 := nat_lit 912513126369180661048312710394999918952104472250367913066604377797260414081

noncomputable def ep415 := nat_lit 3238858195163548561693021995976523943363380626022810095362780414784271502216321

noncomputable def ep416 := BSN.cos_dyadic_bound_f 2344390161 2147483648 3 2 1048576 385360 ep413 ep57 ep414 ep415 ep60 ep414 483377 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2344390161) qz15 0 2 ep413 ep57 ep414 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2344390161) qz16 0 2 ep415 ep60 ep414 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz377 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 216342373) qz17)

noncomputable def ep417 := @Enclosure.Real.IsNear.cos_image qz65 qz377 Bool.false 216342373 524288 699 1048576 Bool.true 483377 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz65 Bool.false 46459170878633766891 112589990684262400 4006062503084539931 6015375000000000000000 216342373 524288 699 1048576 (ep412 rfl) rfl) (Enclosure.sfrac_false_div 216342373 524288) (BSN.cos_reduce2 qz377 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 82485895774442436427776) qz19) 226375608064910080 72057594037927936 Bool.false 483377 1048576 65 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q2 216342373 524288 226375608064910080 72057594037927936 65 82485895774442436427776 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 483377 1048576 82485895774442436427776 75557863725914323419136 2344390161 2147483648 385360 384984 (ep416 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep418 := nat_lit 1943679922348676809280232522670072365985609217402586204382894890621681805495425

noncomputable def ep419 := nat_lit 5089112870613365350854149814985740482474482638337415653905474020730828211817601

noncomputable def ep420 := BSN.sin_dyadic_bound_f 2344390161 2147483648 3 2 1048576 385360 ep418 ep64 ep414 ep419 ep66 ep414 930514 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2344390161) qz20 0 2 ep418 ep64 ep414 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2344390161) qz21 0 2 ep419 ep66 ep414 rfl rfl rfl rfl) rfl rfl

noncomputable def ep421 := @Enclosure.Real.IsNear.sin_image qz65 qz377 Bool.false 216342373 524288 699 1048576 Bool.true 930514 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz65 Bool.false 46459170878633766891 112589990684262400 4006062503084539931 6015375000000000000000 216342373 524288 699 1048576 (ep412 rfl) rfl) (Enclosure.sfrac_false_div 216342373 524288) (BSN.sin_reduce2 qz377 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 82485895774442436427776) qz19) 226375608064910080 72057594037927936 Bool.false 930514 1048576 65 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q2 216342373 524288 226375608064910080 72057594037927936 65 82485895774442436427776 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 930514 1048576 82485895774442436427776 75557863725914323419136 2344390161 2147483648 385360 384984 (ep420 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz378 := (@Enclosure.Real.IsNear.recentre' qz64 Bool.false 209715 1048576 1 1048576 209715 1048576 1 1048576 (ep410 rfl rfl) rfl)

noncomputable def ep422 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz64 (Real.cos qz65)) (@HMul.hMul Real Real Real qz0 qz64 (@Neg.neg Real Real.instNeg (Real.sin qz65))) Bool.true 101371407555 1099511627776 7132659327007 52911798063464448 Bool.false 97571371755 549755813888 3577088450429 26455899031732224 (@Enclosure.Real.IsNear.mulLit_ft qz64 (Real.cos qz65) 209715 1048576 1 1048576 483377 1048576 33900121 50460622848 101371407555 1099511627776 7132659327007 52911798063464448 qz378 (@Enclosure.Real.IsNear.recentre' (Real.cos qz65) Bool.true 483377 1048576 135600484 201842491392 483377 1048576 33900121 50460622848 (ep417 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz64 (@Neg.neg Real Real.instNeg (Real.sin qz65)) 209715 1048576 1 1048576 465257 524288 33900121 50460622848 97571371755 549755813888 3577088450429 26455899031732224 qz378 (@Enclosure.Real.IsNear.neg (Real.sin qz65) Bool.true 465257 524288 33900121 50460622848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz65) Bool.true 930514 1048576 135600484 201842491392 465257 524288 33900121 50460622848 (ep421 rfl rfl) rfl)) rfl)

noncomputable def ep423 := @ep407 101371407555 1099511627776 7132659327007 52911798063464448 Bool.false 97571371755 549755813888 3577088450429 26455899031732224 Bool.false ep408 1074835243965 549755813888 68132981648255 13227949515866112 Bool.false 20221577022272471826432 73565668653 549755813888 136265672489221 26455899031732224 EMRow43.d8 (ep409 ep422) rfl rfl

noncomputable abbrev qz66 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 26)))

noncomputable abbrev qz585 := (Real.log (Enclosure.sfrac Bool.false 26 1))

noncomputable abbrev qz67 := (@HMul.hMul Real Real Real qz267 qz278 qz585)

noncomputable def ep424 := @Enclosure.Complex.IsNear.of_eq qz582 (Complex.mk (@HMul.hMul Real Real Real qz0 qz66 (Real.cos qz67)) (@HMul.hMul Real Real Real qz0 qz66 (@Neg.neg Real Real.instNeg (Real.sin qz67)))) Bool.true 212752284153 1099511627776 2343679783123 17637266021154816 Bool.true 8781161743 274877906944 582456024169 4409316505288704 (BSN.cpow_neg_s_mk qz12 128194 1000 26 qz13 rfl)

noncomputable abbrev qz379 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26) qz14)

noncomputable def ep425 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 26)) 5346709 1048576 1 1048576 102821 102822 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 26)) (Real.sqrt qz379) Bool.false 5346709 1048576 1 1048576 (BSN.sqrt_natCast_div_one 26) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz379) Bool.false 5346709 1048576 1 1048576 5346709 1048576 1 1048576 (BSN.sqrt_enclosure 26 1 2673354 2673355 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep426 := BSN.log_dyadic_bound 10 42 5 4 9150106136613120 524288 192492 179034245376000 10500000000 254545 52 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 10) (BSN.artanhQ 42) 0 4 179034245376000 9150106136613120 10500000000 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep427 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz585 128194 1000 0 1 3668288609262839 1125899906842624 62500000048123 12030750000000000000 235126294987920191383 562949953421312000 4006062503084539931 6015375000000000000000 qz18 (BSN.isNear_log_sfrac 26 1 3668288609262839 1125899906842624 62500000048123 12030750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz379) Bool.false 61543670347942250676224 18889465931478580854784 1000000000769968 192492000000000000000 3668288609262839 1125899906842624 62500000048123 12030750000000000000 (BSN.log_rat_reduce_isNear 26 1 4 52 32 254545 524288 24973259072661432 36028797018963968 192492 1000000000000000 rfl rfl rfl rfl (ep426 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep428 := nat_lit 5370017629260295697045437794770550448779050307785975118866776980647752790957665

noncomputable def ep429 := nat_lit 6953819765233284912750821257372628292032891180203858934555630820226366692961

noncomputable def ep430 := nat_lit 14053073320823730078593597656649028824805649934671509539709421070844700335005281

noncomputable def ep431 := BSN.sin_dyadic_bound_f 3021884971 2147483648 3 2 1048576 385360 ep428 ep64 ep429 ep430 ep66 ep429 1034571 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3021884971) qz20 0 2 ep428 ep64 ep429 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3021884971) qz21 0 2 ep430 ep66 ep429 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz380 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 109489213) (@Nat.cast Real Real.instNatCast 262144))

noncomputable def ep432 := @Enclosure.Real.IsNear.cos_image qz67 qz380 Bool.false 109489213 262144 175 262144 Bool.true 1034571 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz67 Bool.false 235126294987920191383 562949953421312000 4006062503084539931 6015375000000000000000 109489213 262144 175 262144 (ep427 rfl) rfl) (Enclosure.sfrac_false_div 109489213 262144) (BSN.cos_reduce1 qz380 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 53161562621979903655936) qz301) 226375608064910080 72057594037927936 Bool.false 1034571 1048576 66 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q1 109489213 262144 226375608064910080 72057594037927936 66 53161562621979903655936 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1034571 1048576 53161562621979903655936 37778931862957161709568 3021884971 2147483648 385360 384984 (ep431 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep433 := nat_lit 2986433713929156847208688028764693639673709233738965670008011936279963269062241

noncomputable def ep434 := nat_lit 8945393502257003971800562443779335662437061918856489292154924547199437073800801

noncomputable def ep435 := BSN.cos_dyadic_bound_f 3021884971 2147483648 3 2 1048576 385360 ep433 ep57 ep429 ep434 ep60 ep429 170804 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3021884971) qz15 0 2 ep433 ep57 ep429 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3021884971) qz16 0 2 ep434 ep60 ep429 rfl rfl rfl rfl) rfl rfl

noncomputable def ep436 := @Enclosure.Real.IsNear.sin_image qz67 qz380 Bool.false 109489213 262144 175 262144 Bool.false 170804 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz67 Bool.false 235126294987920191383 562949953421312000 4006062503084539931 6015375000000000000000 109489213 262144 175 262144 (ep427 rfl) rfl) (Enclosure.sfrac_false_div 109489213 262144) (BSN.sin_reduce1 qz380 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 53161562621979903655936) qz301) 226375608064910080 72057594037927936 Bool.false 170804 1048576 66 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q1 109489213 262144 226375608064910080 72057594037927936 66 53161562621979903655936 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 170804 1048576 53161562621979903655936 37778931862957161709568 3021884971 2147483648 385360 384984 (ep435 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz381 := (@Enclosure.Real.IsNear.recentre' qz66 Bool.false 205643 1048576 1 1048576 205643 1048576 1 1048576 (ep425 rfl rfl) rfl)

noncomputable def ep437 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz66 (Real.cos qz67)) (@HMul.hMul Real Real Real qz0 qz66 (@Neg.neg Real Real.instNeg (Real.sin qz67))) Bool.true 212752284153 1099511627776 2343679783123 17637266021154816 Bool.true 8781161743 274877906944 582456024169 4409316505288704 (@Enclosure.Real.IsNear.mulLit_ft qz66 (Real.cos qz67) 205643 1048576 1 1048576 1034571 1048576 8487061 12615155712 212752284153 1099511627776 2343679783123 17637266021154816 qz381 (@Enclosure.Real.IsNear.recentre' (Real.cos qz67) Bool.true 1034571 1048576 33948244 50460622848 1034571 1048576 8487061 12615155712 (ep432 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz66 (@Neg.neg Real Real.instNeg (Real.sin qz67)) 205643 1048576 1 1048576 42701 262144 8487061 12615155712 8781161743 274877906944 582456024169 4409316505288704 qz381 (@Enclosure.Real.IsNear.neg (Real.sin qz67) Bool.false 42701 262144 8487061 12615155712 (@Enclosure.Real.IsNear.recentre' (Real.sin qz67) Bool.false 170804 1048576 33948244 50460622848 42701 262144 8487061 12615155712 (ep436 rfl rfl) rfl)) rfl)

noncomputable def ep438 := @ep405 212752284153 1099511627776 2343679783123 17637266021154816 Bool.true 8781161743 274877906944 582456024169 4409316505288704 Bool.false 1064832043551907670654976 1936918203777 1099511627776 279562965942389 52911798063464448 Bool.false 15394082301367338139648 56003345167 549755813888 139760408634235 26455899031732224 (ep406 (BSN.head_sum_c_succ qz5 25 26 rfl rfl) (ep423 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep424 ep437) rfl rfl

noncomputable abbrev qz68 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 27)))

noncomputable abbrev qz586 := (Real.log (Enclosure.sfrac Bool.false 27 1))

noncomputable abbrev qz69 := (@HMul.hMul Real Real Real qz267 qz278 qz586)

noncomputable def ep439 := @Enclosure.Complex.IsNear.of_eq qz581 (Complex.mk (@HMul.hMul Real Real Real qz0 qz68 (Real.cos qz69)) (@HMul.hMul Real Real Real qz0 qz68 (@Neg.neg Real Real.instNeg (Real.sin qz69)))) Bool.false 8012832893 1099511627776 6842955237761 52911798063464448 Bool.true 211449633577 1099511627776 6891468804029 52911798063464448 (BSN.cpow_neg_s_mk qz12 128194 1000 27 qz13 rfl)

noncomputable abbrev qz382 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 27) qz14)

noncomputable def ep440 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 27)) 5448561 1048576 1 1048576 100899 100900 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 27)) (Real.sqrt qz382) Bool.false 5448561 1048576 1 1048576 (BSN.sqrt_natCast_div_one 27) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz382) Bool.false 5448561 1048576 1 1048576 5448561 1048576 1 1048576 (BSN.sqrt_enclosure 27 1 2724280 2724281 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep441 := BSN.log_dyadic_bound 11 43 5 4 11045349262332945 524288 192492 250863800262504 22507682505 274332 54 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 11) (BSN.artanhQ 43) 0 4 250863800262504 11045349262332945 22507682505 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep442 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz586 128194 1000 0 1 3710780868205815 1125899906842624 62500000048123 12030750000000000000 47569984261877624811 112589990684262400 4006062503084539931 6015375000000000000000 qz18 (BSN.isNear_log_sfrac 27 1 3710780868205815 1125899906842624 62500000048123 12030750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz382) Bool.false 62256572154556490711040 18889465931478580854784 1000000000769968 192492000000000000000 3710780868205815 1125899906842624 62500000048123 12030750000000000000 (BSN.log_rat_reduce_isNear 27 1 4 54 32 274332 524288 24973259072661432 36028797018963968 192492 1000000000000000 rfl rfl rfl rfl (ep441 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep443 := nat_lit 4209686945913591303725117989437799288643976265468996936372489124785466334298081

noncomputable def ep444 := nat_lit 13790879254417118683292512758312888215439630878225575454715405889560463327201

noncomputable def ep445 := nat_lit 12601479079231939673808768942796772089501049534650539658208036562577278076239841

noncomputable def ep446 := BSN.cos_dyadic_bound_f 3291917893 2147483648 3 2 1048576 385360 ep443 ep57 ep444 ep445 ep60 ep444 39707 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3291917893) qz15 0 2 ep443 ep57 ep444 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3291917893) qz16 0 2 ep445 ep60 ep444 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz383 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 221515001) qz17)

noncomputable def ep447 := @Enclosure.Real.IsNear.cos_image qz69 qz383 Bool.false 221515001 524288 699 1048576 Bool.false 39707 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz69 Bool.false 47569984261877624811 112589990684262400 4006062503084539931 6015375000000000000000 221515001 524288 699 1048576 (ep442 rfl) rfl) (Enclosure.sfrac_false_div 221515001 524288) (BSN.cos_reduce0 qz383 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 115824064034067187761152) qz19) 226375608064910080 72057594037927936 Bool.false 39707 1048576 67 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q0 221515001 524288 226375608064910080 72057594037927936 67 115824064034067187761152 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 39707 1048576 115824064034067187761152 75557863725914323419136 3291917893 2147483648 385360 384984 (ep446 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep448 := nat_lit 7566403799240930651758578370781388408986805573141614025106708099902191031074785

noncomputable def ep449 := nat_lit 19794443764933381133880469759961605918807112336806147705495648652113116712189921

noncomputable def ep450 := BSN.sin_dyadic_bound_f 3291917893 2147483648 3 2 1048576 385360 ep448 ep64 ep444 ep449 ep66 ep444 1047823 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3291917893) qz20 0 2 ep448 ep64 ep444 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3291917893) qz21 0 2 ep449 ep66 ep444 rfl rfl rfl rfl) rfl rfl

noncomputable def ep451 := @Enclosure.Real.IsNear.sin_image qz69 qz383 Bool.false 221515001 524288 699 1048576 Bool.false 1047823 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz69 Bool.false 47569984261877624811 112589990684262400 4006062503084539931 6015375000000000000000 221515001 524288 699 1048576 (ep442 rfl) rfl) (Enclosure.sfrac_false_div 221515001 524288) (BSN.sin_reduce0 qz383 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 115824064034067187761152) qz19) 226375608064910080 72057594037927936 Bool.false 1047823 1048576 67 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q0 221515001 524288 226375608064910080 72057594037927936 67 115824064034067187761152 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1047823 1048576 115824064034067187761152 75557863725914323419136 3291917893 2147483648 385360 384984 (ep450 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz384 := (@Enclosure.Real.IsNear.recentre' qz68 Bool.false 201799 1048576 1 1048576 201799 1048576 1 1048576 (ep440 rfl rfl) rfl)

noncomputable def ep452 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz68 (Real.cos qz69)) (@HMul.hMul Real Real Real qz0 qz68 (@Neg.neg Real Real.instNeg (Real.sin qz69))) Bool.false 8012832893 1099511627776 6842955237761 52911798063464448 Bool.true 211449633577 1099511627776 6891468804029 52911798063464448 (@Enclosure.Real.IsNear.mulLit_ff qz68 (Real.cos qz69) 201799 1048576 1 1048576 39707 1048576 33900121 50460622848 8012832893 1099511627776 6842955237761 52911798063464448 qz384 (@Enclosure.Real.IsNear.recentre' (Real.cos qz69) Bool.false 39707 1048576 135600484 201842491392 39707 1048576 33900121 50460622848 (ep447 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz68 (@Neg.neg Real Real.instNeg (Real.sin qz69)) 201799 1048576 1 1048576 1047823 1048576 33900121 50460622848 211449633577 1099511627776 6891468804029 52911798063464448 qz384 (@Enclosure.Real.IsNear.neg (Real.sin qz69) Bool.false 1047823 1048576 33900121 50460622848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz69) Bool.false 1047823 1048576 135600484 201842491392 1047823 1048576 33900121 50460622848 (ep451 rfl rfl) rfl)) rfl)

noncomputable def ep453 := @ep402 8012832893 1099511627776 6842955237761 52911798063464448 Bool.true 211449633577 1099511627776 6891468804029 52911798063464448 Bool.false ep403 972465518335 549755813888 143202960590075 26455899031732224 Bool.true 54669336197973655158784 99442943243 1099511627776 286412286072499 52911798063464448 (ep404 (BSN.head_sum_c_succ qz5 26 27 rfl rfl) (ep438 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep439 ep452) rfl rfl

noncomputable abbrev qz70 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 28)))

noncomputable abbrev qz587 := (Real.log (Enclosure.sfrac Bool.false 28 1))

noncomputable abbrev qz71 := (@HMul.hMul Real Real Real qz267 qz278 qz587)

noncomputable def ep454 := @Enclosure.Complex.IsNear.of_eq qz580 (Complex.mk (@HMul.hMul Real Real Real qz0 qz70 (Real.cos qz71)) (@HMul.hMul Real Real Real qz0 qz70 (@Neg.neg Real Real.instNeg (Real.sin qz71)))) Bool.false 206981451663 1099511627776 6768048099467 52911798063464448 Bool.false 18299362235 1099511627776 6722227496279 52911798063464448 (BSN.cpow_neg_s_mk qz12 128194 1000 28 qz13 rfl)

noncomputable abbrev qz385 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 28) qz14)

noncomputable def ep455 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 28)) 5548543 1048576 1 1048576 99081 99082 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 28)) (Real.sqrt qz385) Bool.false 5548543 1048576 1 1048576 (BSN.sqrt_natCast_div_one 28) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz385) Bool.false 5548543 1048576 1 1048576 5548543 1048576 1 1048576 (BSN.sqrt_enclosure 28 1 2774271 2774272 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep456 := BSN.log_dyadic_bound 12 44 5 4 13275571325829120 524288 192492 344661139390464 45148078080 293399 56 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 12) (BSN.artanhQ 44) 0 4 344661139390464 13275571325829120 45148078080 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep457 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz587 128194 1000 0 1 3751726938922231 1125899906842624 62500000048123 12030750000000000000 240474441604098240407 562949953421312000 4006062503084539931 6015375000000000000000 qz18 (BSN.isNear_log_sfrac 28 1 3751726938922231 1125899906842624 62500000048123 12030750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz385) Bool.false 62943533227317076688896 18889465931478580854784 1000000000769968 192492000000000000000 3751726938922231 1125899906842624 62500000048123 12030750000000000000 (BSN.log_rat_reduce_isNear 28 1 4 56 32 293399 524288 24973259072661432 36028797018963968 192492 1000000000000000 rfl rfl rfl rfl (ep456 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep458 := nat_lit 6619525386398522447286420866086769384504913956547778631635952758081364116537600

noncomputable def ep459 := nat_lit 10560013042559426892587047161634231490020975590447381291832983426968280269056

noncomputable def ep460 := nat_lit 17319755038498653051733580382441750108433788306669172084574051440855147851448576

noncomputable def ep461 := BSN.sin_dyadic_bound_f 3183890014 2147483648 3 2 1048576 385360 ep458 ep64 ep459 ep460 ep66 ep459 1044501 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3183890014) qz20 0 2 ep458 ep64 ep459 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3183890014) qz21 0 2 ep460 ep66 ep459 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz386 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 55989819) (@Nat.cast Real Real.instNatCast 131072))

noncomputable def ep462 := @Enclosure.Real.IsNear.cos_image qz71 qz386 Bool.false 55989819 131072 699 1048576 Bool.false 1044501 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz71 Bool.false 240474441604098240407 562949953421312000 4006062503084539931 6015375000000000000000 55989819 131072 699 1048576 (ep457 rfl) rfl) (Enclosure.sfrac_false_div 55989819 131072) (BSN.cos_reduce3 qz386 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 28005792741193267806208) qz371) 226375608064910080 72057594037927936 Bool.false 1044501 1048576 67 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q3 55989819 131072 226375608064910080 72057594037927936 67 28005792741193267806208 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1044501 1048576 28005792741193267806208 18889465931478580854784 3183890014 2147483648 385360 384984 (ep461 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep463 := nat_lit 3682207442684761104889161391008931538720517076122298075927455080457188189307136

noncomputable def ep464 := nat_lit 11025502301969164460882310078703526153181509277185999465198699274517628007383296

noncomputable def ep465 := BSN.cos_dyadic_bound_f 3183890014 2147483648 3 2 1048576 385360 ep463 ep57 ep459 ep464 ep60 ep459 92345 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3183890014) qz15 0 2 ep463 ep57 ep459 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3183890014) qz16 0 2 ep464 ep60 ep459 rfl rfl rfl rfl) rfl rfl

noncomputable def ep466 := @Enclosure.Real.IsNear.sin_image qz71 qz386 Bool.false 55989819 131072 699 1048576 Bool.true 92345 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz71 Bool.false 240474441604098240407 562949953421312000 4006062503084539931 6015375000000000000000 55989819 131072 699 1048576 (ep457 rfl) rfl) (Enclosure.sfrac_false_div 55989819 131072) (BSN.sin_reduce3 qz386 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 28005792741193267806208) qz371) 226375608064910080 72057594037927936 Bool.false 92345 1048576 67 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q3 55989819 131072 226375608064910080 72057594037927936 67 28005792741193267806208 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 92345 1048576 28005792741193267806208 18889465931478580854784 3183890014 2147483648 385360 384984 (ep465 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz387 := (@Enclosure.Real.IsNear.recentre' qz70 Bool.false 198163 1048576 1 1048576 198163 1048576 1 1048576 (ep455 rfl rfl) rfl)

noncomputable def ep467 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz70 (Real.cos qz71)) (@HMul.hMul Real Real Real qz0 qz70 (@Neg.neg Real Real.instNeg (Real.sin qz71))) Bool.false 206981451663 1099511627776 6768048099467 52911798063464448 Bool.false 18299362235 1099511627776 6722227496279 52911798063464448 (@Enclosure.Real.IsNear.mulLit_ff qz70 (Real.cos qz71) 198163 1048576 1 1048576 1044501 1048576 33900121 50460622848 206981451663 1099511627776 6768048099467 52911798063464448 qz387 (@Enclosure.Real.IsNear.recentre' (Real.cos qz71) Bool.false 1044501 1048576 135600484 201842491392 1044501 1048576 33900121 50460622848 (ep462 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz70 (@Neg.neg Real Real.instNeg (Real.sin qz71)) 198163 1048576 1 1048576 92345 1048576 33900121 50460622848 18299362235 1099511627776 6722227496279 52911798063464448 qz387 (@Enclosure.Real.IsNear.neg (Real.sin qz71) Bool.true 92345 1048576 33900121 50460622848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz71) Bool.true 92345 1048576 135600484 201842491392 92345 1048576 33900121 50460622848 (ep466 rfl rfl) rfl)) rfl)

noncomputable def ep468 := @ep400 206981451663 1099511627776 6768048099467 52911798063464448 Bool.false 18299362235 1099511627776 6722227496279 52911798063464448 Bool.false 1183026401439259719368704 2151912488333 1099511627776 32574885475513 5879088673718272 Bool.true 89218310837679798878208 5071473813 68719476736 16285250753821 2939544336859136 (ep401 (BSN.head_sum_c_succ qz5 27 28 rfl rfl) (ep453 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep454 ep467) rfl rfl

noncomputable abbrev qz72 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 29)))

noncomputable abbrev qz588 := (Real.log (Enclosure.sfrac Bool.false 29 1))

noncomputable abbrev qz73 := (@HMul.hMul Real Real Real qz267 qz278 qz588)

noncomputable def ep469 := @Enclosure.Complex.IsNear.of_eq qz579 (Complex.mk (@HMul.hMul Real Real Real qz0 qz72 (Real.cos qz73)) (@HMul.hMul Real Real Real qz0 qz72 (@Neg.neg Real Real.instNeg (Real.sin qz73)))) Bool.true 30369893265 549755813888 3307953772751 26455899031732224 Bool.false 194929381215 1099511627776 6649071944059 52911798063464448 (BSN.cpow_neg_s_mk qz12 128194 1000 29 qz13 rfl)

noncomputable abbrev qz388 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 29) qz14)

noncomputable def ep470 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 29)) 5646755 1048576 1 1048576 97357 97358 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 29)) (Real.sqrt qz388) Bool.false 5646755 1048576 1 1048576 (BSN.sqrt_natCast_div_one 29) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz388) Bool.false 5646755 1048576 1 1048576 5646755 1048576 1 1048576 (BSN.sqrt_enclosure 29 1 2823377 2823378 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep471 := BSN.log_dyadic_bound 13 45 6 5 353956287581982421875 524288 192492 10371179520995104305 130276274797305 311797 58 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 13) (BSN.artanhQ 45) 0 5 10371179520995104305 353956287581982421875 130276274797305 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep472 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz588 128194 1000 0 1 3791236343078135 1125899906842624 62500000048123 12030750000000000000 48601375176455843819 112589990684262400 4006062503084539931 6015375000000000000000 qz18 (BSN.isNear_log_sfrac 29 1 3791236343078135 1125899906842624 62500000048123 12030750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz388) Bool.false 63606391034871975772160 18889465931478580854784 1000000000769968 192492000000000000000 3791236343078135 1125899906842624 62500000048123 12030750000000000000 (BSN.log_rat_reduce_isNear 29 1 4 58 32 311797 524288 24973259072661432 36028797018963968 192492 1000000000000000 rfl rfl rfl rfl (ep471 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep473 := nat_lit 1971954668445826662593882046570829720070347173870029637098250271704464779902976

noncomputable def ep474 := nat_lit 3036671191403257285905088183233648913522770279255616219247717166472071479296

noncomputable def ep475 := nat_lit 5909790662954673473209835963346021862383995981051577678856255380780450196750336

noncomputable def ep476 := BSN.cos_dyadic_bound_f 2724580984 2147483648 3 2 1048576 385360 ep473 ep57 ep474 ep475 ep60 ep474 311942 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2724580984) qz15 0 2 ep473 ep57 ep474 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2724580984) qz16 0 2 ep475 ep60 ep474 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz389 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 226317789) qz17)

noncomputable def ep477 := @Enclosure.Real.IsNear.cos_image qz73 qz389 Bool.false 226317789 524288 699 1048576 Bool.true 311942 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz73 Bool.false 48601375176455843819 112589990684262400 4006062503084539931 6015375000000000000000 226317789 524288 699 1048576 (ep472 rfl) rfl) (Enclosure.sfrac_false_div 226317789 524288) (BSN.cos_reduce2 qz389 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 95862671135717403394048) qz19) 226375608064910080 72057594037927936 Bool.false 311942 1048576 68 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q2 226317789 524288 226375608064910080 72057594037927936 68 95862671135717403394048 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 311942 1048576 95862671135717403394048 75557863725914323419136 2724580984 2147483648 385360 384984 (ep476 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep478 := nat_lit 3547089066249365386840263613280906576995806696742648853801452315334858946641920

noncomputable def ep479 := nat_lit 9285078658247970739452082177724757984367123530064333143220259759988437696905216

noncomputable def ep480 := BSN.sin_dyadic_bound_f 2724580984 2147483648 3 2 1048576 385360 ep478 ep64 ep474 ep479 ep66 ep474 1001101 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2724580984) qz20 0 2 ep478 ep64 ep474 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2724580984) qz21 0 2 ep479 ep66 ep474 rfl rfl rfl rfl) rfl rfl

noncomputable def ep481 := @Enclosure.Real.IsNear.sin_image qz73 qz389 Bool.false 226317789 524288 699 1048576 Bool.true 1001101 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz73 Bool.false 48601375176455843819 112589990684262400 4006062503084539931 6015375000000000000000 226317789 524288 699 1048576 (ep472 rfl) rfl) (Enclosure.sfrac_false_div 226317789 524288) (BSN.sin_reduce2 qz389 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 95862671135717403394048) qz19) 226375608064910080 72057594037927936 Bool.false 1001101 1048576 68 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q2 226317789 524288 226375608064910080 72057594037927936 68 95862671135717403394048 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1001101 1048576 95862671135717403394048 75557863725914323419136 2724580984 2147483648 385360 384984 (ep480 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz390 := (@Enclosure.Real.IsNear.recentre' qz72 Bool.false 194715 1048576 1 1048576 194715 1048576 1 1048576 (ep470 rfl rfl) rfl)

noncomputable def ep482 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz72 (Real.cos qz73)) (@HMul.hMul Real Real Real qz0 qz72 (@Neg.neg Real Real.instNeg (Real.sin qz73))) Bool.true 30369893265 549755813888 3307953772751 26455899031732224 Bool.false 194929381215 1099511627776 6649071944059 52911798063464448 (@Enclosure.Real.IsNear.mulLit_ft qz72 (Real.cos qz73) 194715 1048576 1 1048576 155971 524288 33900121 50460622848 30369893265 549755813888 3307953772751 26455899031732224 qz390 (@Enclosure.Real.IsNear.recentre' (Real.cos qz73) Bool.true 311942 1048576 135600484 201842491392 155971 524288 33900121 50460622848 (ep477 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz72 (@Neg.neg Real Real.instNeg (Real.sin qz73)) 194715 1048576 1 1048576 1001101 1048576 33900121 50460622848 194929381215 1099511627776 6649071944059 52911798063464448 qz390 (@Enclosure.Real.IsNear.neg (Real.sin qz73) Bool.true 1001101 1048576 33900121 50460622848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz73) Bool.true 1001101 1048576 135600484 201842491392 1001101 1048576 33900121 50460622848 (ep481 rfl rfl) rfl)) rfl)

noncomputable def ep483 := @ep398 30369893265 549755813888 3307953772751 26455899031732224 Bool.false 194929381215 1099511627776 6649071944059 52911798063464448 Bool.false 1149634350660076190040064 2091172701803 1099511627776 299789876825119 52911798063464448 Bool.false 7819300650212080484352 113785800207 1099511627776 299783585512837 52911798063464448 (ep399 (BSN.head_sum_c_succ qz5 28 29 rfl rfl) (ep468 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep469 ep482) rfl rfl

noncomputable abbrev qz74 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 30)))

noncomputable abbrev qz589 := (Real.log (Enclosure.sfrac Bool.false 30 1))

noncomputable abbrev qz75 := (@HMul.hMul Real Real Real qz267 qz278 qz589)

noncomputable def ep484 := @Enclosure.Complex.IsNear.of_eq qz578 (Complex.mk (@HMul.hMul Real Real Real qz0 qz74 (Real.cos qz75)) (@HMul.hMul Real Real Real qz0 qz74 (@Neg.neg Real Real.instNeg (Real.sin qz75)))) Bool.true 78765202047 549755813888 3269393009935 26455899031732224 Bool.true 124425506205 1099511627776 6530464446341 52911798063464448 (BSN.cpow_neg_s_mk qz12 128194 1000 30 qz13 rfl)

noncomputable abbrev qz391 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 30) qz14)

noncomputable def ep485 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 30)) 5743287 1048576 1 1048576 95721 95722 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 30)) (Real.sqrt qz391) Bool.false 5743287 1048576 1 1048576 (BSN.sqrt_natCast_div_one 30) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz391) Bool.false 5743287 1048576 1 1048576 5743287 1048576 1 1048576 (BSN.sqrt_enclosure 30 1 2871643 2871644 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep486 := BSN.log_dyadic_bound 14 46 6 5 440963670083462507520 524288 192492 14425761949190022144 273345648952320 329571 60 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 14) (BSN.artanhQ 46) 0 5 14425761949190022144 440963670083462507520 273345648952320 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep487 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz589 128194 1000 0 1 3829405717437687 1125899906842624 62500000048123 12030750000000000000 245453418270603423639 562949953421312000 4006062503084539931 6015375000000000000000 qz18 (BSN.isNear_log_sfrac 30 1 3829405717437687 1125899906842624 62500000048123 12030750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz391) Bool.false 64246766873087041339392 18889465931478580854784 1000000000769968 192492000000000000000 3829405717437687 1125899906842624 62500000048123 12030750000000000000 (BSN.log_rat_reduce_isNear 30 1 4 60 32 329571 524288 24973259072661432 36028797018963968 192492 1000000000000000 rfl rfl rfl rfl (ep486 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep488 := nat_lit 906716285450077552200439618058258524011364404427461743649741950654449462890625

noncomputable def ep489 := nat_lit 198678096006286652877536648402009889416601470033079409040510654449462890625

noncomputable def ep490 := nat_lit 2374411459261431029753635368912311927827851323501393866706115710654449462890625

noncomputable def ep491 := BSN.sin_dyadic_bound_f 1937620625 2147483648 3 2 1048576 385360 ep488 ep64 ep489 ep490 ep66 ep489 822858 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1937620625) qz20 0 2 ep488 ep64 ep489 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1937620625) qz21 0 2 ep490 ep66 ep489 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz392 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 228596309) qz17)

noncomputable def ep492 := @Enclosure.Real.IsNear.cos_image qz75 qz392 Bool.false 228596309 524288 175 262144 Bool.true 822858 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz75 Bool.false 245453418270603423639 562949953421312000 4006062503084539931 6015375000000000000000 228596309 524288 175 262144 (ep487 rfl) rfl) (Enclosure.sfrac_false_div 228596309 524288) (BSN.cos_reduce1 qz392 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 68173965066909796794368) qz19) 226375608064910080 72057594037927936 Bool.false 822858 1048576 69 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q1 228596309 524288 226375608064910080 72057594037927936 69 68173965066909796794368 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 822858 1048576 68173965066909796794368 75557863725914323419136 1937620625 2147483648 385360 384984 (ep491 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep493 := nat_lit 503819571070490323068189804098322295512720936446382337320541310654449462890625

noncomputable def ep494 := nat_lit 1511061357019458395898814338998162866759329606399080853143542910654449462890625

noncomputable def ep495 := BSN.cos_dyadic_bound_f 1937620625 2147483648 3 2 1048576 385360 ep493 ep57 ep489 ep494 ep60 ep489 649935 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1937620625) qz15 0 2 ep493 ep57 ep489 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1937620625) qz16 0 2 ep494 ep60 ep489 rfl rfl rfl rfl) rfl rfl

noncomputable def ep496 := @Enclosure.Real.IsNear.sin_image qz75 qz392 Bool.false 228596309 524288 175 262144 Bool.false 649935 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz75 Bool.false 245453418270603423639 562949953421312000 4006062503084539931 6015375000000000000000 228596309 524288 175 262144 (ep487 rfl) rfl) (Enclosure.sfrac_false_div 228596309 524288) (BSN.sin_reduce1 qz392 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 68173965066909796794368) qz19) 226375608064910080 72057594037927936 Bool.false 649935 1048576 69 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q1 228596309 524288 226375608064910080 72057594037927936 69 68173965066909796794368 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 649935 1048576 68173965066909796794368 75557863725914323419136 1937620625 2147483648 385360 384984 (ep495 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz393 := (@Enclosure.Real.IsNear.recentre' qz74 Bool.false 191443 1048576 1 1048576 191443 1048576 1 1048576 (ep485 rfl rfl) rfl)

noncomputable def ep497 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz74 (Real.cos qz75)) (@HMul.hMul Real Real Real qz0 qz74 (@Neg.neg Real Real.instNeg (Real.sin qz75))) Bool.true 78765202047 549755813888 3269393009935 26455899031732224 Bool.true 124425506205 1099511627776 6530464446341 52911798063464448 (@Enclosure.Real.IsNear.mulLit_ft qz74 (Real.cos qz75) 191443 1048576 1 1048576 411429 524288 8487061 12615155712 78765202047 549755813888 3269393009935 26455899031732224 qz393 (@Enclosure.Real.IsNear.recentre' (Real.cos qz75) Bool.true 822858 1048576 33948244 50460622848 411429 524288 8487061 12615155712 (ep492 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz74 (@Neg.neg Real Real.instNeg (Real.sin qz75)) 191443 1048576 1 1048576 649935 1048576 8487061 12615155712 124425506205 1099511627776 6530464446341 52911798063464448 qz393 (@Enclosure.Real.IsNear.neg (Real.sin qz75) Bool.false 649935 1048576 8487061 12615155712 (@Enclosure.Real.IsNear.recentre' (Real.sin qz75) Bool.false 649935 1048576 33948244 50460622848 649935 1048576 8487061 12615155712 (ep496 rfl rfl) rfl)) rfl)

noncomputable def ep498 := @ep396 78765202047 549755813888 3269393009935 26455899031732224 Bool.true 124425506205 1099511627776 6530464446341 52911798063464448 Bool.false 1063031095145273692782592 1933642297709 1099511627776 102109554281663 17637266021154816 Bool.true 11698480460919050600448 5319852999 549755813888 51052341659863 8818633010577408 (ep397 (BSN.head_sum_c_succ qz5 29 30 rfl rfl) (ep483 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep484 ep497) rfl rfl

noncomputable abbrev qz76 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 31)))

noncomputable abbrev qz590 := (Real.log (Enclosure.sfrac Bool.false 31 1))

noncomputable abbrev qz77 := (@HMul.hMul Real Real Real qz267 qz278 qz590)

noncomputable def ep499 := @Enclosure.Complex.IsNear.of_eq qz577 (Complex.mk (@HMul.hMul Real Real Real qz0 qz76 (Real.cos qz77)) (@HMul.hMul Real Real Real qz0 qz76 (@Neg.neg Real Real.instNeg (Real.sin qz77)))) Bool.false 91191726735 549755813888 1607753386205 13227949515866112 Bool.true 75719746069 1099511627776 6403758169433 52911798063464448 (BSN.cpow_neg_s_mk qz12 128194 1000 31 qz13 rfl)

noncomputable abbrev qz394 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 31) qz14)

noncomputable def ep500 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 31)) 5838225 1048576 1 1048576 94164 94165 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 31)) (Real.sqrt qz394) Bool.false 5838225 1048576 1 1048576 (BSN.sqrt_natCast_div_one 31) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz394) Bool.false 5838225 1048576 1 1048576 5838225 1048576 1 1048576 (BSN.sqrt_enclosure 31 1 2919112 2919113 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep501 := BSN.log_dyadic_bound 15 47 6 5 546767979591453359355 524288 192492 19788004106328479625 544934619140625 346763 62 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 15) (BSN.artanhQ 47) 0 5 19788004106328479625 546767979591453359355 544934619140625 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep502 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz590 128194 1000 0 1 3866325256314103 1125899906842624 62500000048123 12030750000000000000 247819849953965059991 562949953421312000 4006062503084539931 6015375000000000000000 qz18 (BSN.isNear_log_sfrac 31 1 3866325256314103 1125899906842624 62500000048123 12030750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz394) Bool.false 64866173951437069877248 18889465931478580854784 1000000000769968 192492000000000000000 3866325256314103 1125899906842624 62500000048123 12030750000000000000 (BSN.log_rat_reduce_isNear 31 1 4 62 32 346763 524288 24973259072661432 36028797018963968 192492 1000000000000000 rfl rfl rfl rfl (ep501 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep503 := nat_lit 509985816382875592869493033813940401

noncomputable def ep504 := BSN.cos_dyadic_bound_f 845063851 2147483648 2 1 1048576 385360 ep503 ep96 ep503 ep503 ep97 ep503 968430 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 845063851) qz15 0 1 ep503 ep96 ep503 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 845063851) qz16 0 1 ep503 ep97 ep503 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz395 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 461600441) qz24)

noncomputable def ep505 := @Enclosure.Real.IsNear.cos_image qz77 qz395 Bool.false 461600441 1048576 699 1048576 Bool.false 968430 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz77 Bool.false 247819849953965059991 562949953421312000 4006062503084539931 6015375000000000000000 461600441 1048576 699 1048576 (ep502 rfl) rfl) (Enclosure.sfrac_false_div 461600441 1048576) (BSN.cos_reduce0 qz395 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 59466081977089394737152) qz25) 226375608064910080 72057594037927936 Bool.false 968430 1048576 70 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q0 461600441 1048576 226375608064910080 72057594037927936 70 59466081977089394737152 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 968430 1048576 59466081977089394737152 151115727451828646838272 845063851 2147483648 385360 384984 (ep504 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep506 := BSN.sin_dyadic_bound_f 845063851 2147483648 2 1 1048576 385360 ep503 ep92 ep503 ep503 ep93 ep503 402061 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 845063851) qz20 0 1 ep503 ep92 ep503 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 845063851) qz21 0 1 ep503 ep93 ep503 rfl rfl rfl rfl) rfl rfl

noncomputable def ep507 := @Enclosure.Real.IsNear.sin_image qz77 qz395 Bool.false 461600441 1048576 699 1048576 Bool.false 402061 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz77 Bool.false 247819849953965059991 562949953421312000 4006062503084539931 6015375000000000000000 461600441 1048576 699 1048576 (ep502 rfl) rfl) (Enclosure.sfrac_false_div 461600441 1048576) (BSN.sin_reduce0 qz395 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 59466081977089394737152) qz25) 226375608064910080 72057594037927936 Bool.false 402061 1048576 70 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q0 461600441 1048576 226375608064910080 72057594037927936 70 59466081977089394737152 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 402061 1048576 59466081977089394737152 151115727451828646838272 845063851 2147483648 385360 384984 (ep506 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz396 := (@Enclosure.Real.IsNear.recentre' qz76 Bool.false 188329 1048576 1 1048576 188329 1048576 1 1048576 (ep500 rfl rfl) rfl)

noncomputable def ep508 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz76 (Real.cos qz77)) (@HMul.hMul Real Real Real qz0 qz76 (@Neg.neg Real Real.instNeg (Real.sin qz77))) Bool.false 91191726735 549755813888 1607753386205 13227949515866112 Bool.true 75719746069 1099511627776 6403758169433 52911798063464448 (@Enclosure.Real.IsNear.mulLit_ff qz76 (Real.cos qz77) 188329 1048576 1 1048576 484215 524288 33900121 50460622848 91191726735 549755813888 1607753386205 13227949515866112 qz396 (@Enclosure.Real.IsNear.recentre' (Real.cos qz77) Bool.false 968430 1048576 135600484 201842491392 484215 524288 33900121 50460622848 (ep505 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz76 (@Neg.neg Real Real.instNeg (Real.sin qz77)) 188329 1048576 1 1048576 402061 1048576 33900121 50460622848 75719746069 1099511627776 6403758169433 52911798063464448 qz396 (@Enclosure.Real.IsNear.neg (Real.sin qz77) Bool.false 402061 1048576 33900121 50460622848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz77) Bool.false 402061 1048576 135600484 201842491392 402061 1048576 33900121 50460622848 (ep507 rfl rfl) rfl)) rfl)

noncomputable def ep509 := @ep394 91191726735 549755813888 1607753386205 13227949515866112 Bool.true 75719746069 1099511627776 6403758169433 52911798063464448 Bool.false 1163297459047377720573952 2116025751179 1099511627776 312759676389809 52911798063464448 Bool.true 47476610858015308906496 86359452067 1099511627776 312717808128611 52911798063464448 (ep395 (BSN.head_sum_c_succ qz5 30 31 rfl rfl) (ep498 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep499 ep508) rfl rfl

noncomputable abbrev qz78 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 32)))

noncomputable abbrev qz591 := (Real.log (Enclosure.sfrac Bool.false 32 1))

noncomputable abbrev qz79 := (@HMul.hMul Real Real Real qz267 qz278 qz591)

noncomputable def ep510 := @Enclosure.Complex.IsNear.of_eq qz576 (Complex.mk (@HMul.hMul Real Real Real qz0 qz78 (Real.cos qz79)) (@HMul.hMul Real Real Real qz0 qz78 (@Neg.neg Real Real.instNeg (Real.sin qz79)))) Bool.true 47863507045 1099511627776 700578709029 5879088673718272 Bool.false 188381636455 1099511627776 704632109319 5879088673718272 (BSN.cpow_neg_s_mk qz12 128194 1000 32 qz13 rfl)

noncomputable abbrev qz397 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 32) qz14)

noncomputable def ep511 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 32)) 5931641 1048576 1 1048576 92681 92682 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 32)) (Real.sqrt qz397) Bool.false 5931641 1048576 1 1048576 (BSN.sqrt_natCast_div_one 32) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz397) Bool.false 5931641 1048576 1 1048576 5931641 1048576 1 1048576 (BSN.sqrt_enclosure 32 1 2965820 2965821 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep512 := BSN.log_dyadic_bound 0 64 1 0 1 524288 192492 0 1 0 64 64 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 64) 0 0 rfl) rfl rfl rfl

noncomputable def ep513 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz591 128194 1000 0 1 15608286920413395 4503599627370496 50000000048123 9624600000000000000 200088873347547475863 450359962737049600 3204850003084539931 4812300000000000000000 qz18 (BSN.isNear_log_sfrac 32 1 15608286920413395 4503599627370496 50000000048123 9624600000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz397) Bool.false 65465900263437584302080 18889465931478580854784 1000000000962460 192492000000000000000 15608286920413395 4503599627370496 50000000048123 9624600000000000000 (BSN.log_rat_reduce_isNear 32 1 5 64 64 0 524288 24973259072661432 36028797018963968 192492 1000000000000000 rfl rfl rfl rfl (ep512 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep514 := nat_lit 2325097575624950682080893603260067116822855931348694152768577812778151657636801

noncomputable def ep515 := nat_lit 4219366144730680088749587349104519678002642322984088335206186554426810205121

noncomputable def ep516 := nat_lit 6966853994585390686065181635081992311112562509400114281635321065225601352500161

noncomputable def ep517 := BSN.cos_dyadic_bound_f 2838937959 2147483648 3 2 1048576 385360 ep514 ep57 ep515 ep516 ep60 ep515 258215 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2838937959) qz15 0 2 ep514 ep57 ep515 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2838937959) qz16 0 2 ep516 ep60 ep515 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz398 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 465868211) qz24)

noncomputable def ep518 := @Enclosure.Real.IsNear.cos_image qz79 qz398 Bool.false 465868211 1048576 175 262144 Bool.true 258215 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz79 Bool.false 200088873347547475863 450359962737049600 3204850003084539931 4812300000000000000000 465868211 1048576 175 262144 (ep513 rfl) rfl) (Enclosure.sfrac_false_div 465868211 1048576) (BSN.cos_reduce2 qz398 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 199772498987042505490432) qz25) 226375608064910080 72057594037927936 Bool.false 258215 1048576 70 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q2 465868211 1048576 226375608064910080 72057594037927936 70 199772498987042505490432 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 258215 1048576 199772498987042505490432 151115727451828646838272 2838937959 2147483648 385360 384984 (ep517 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep519 := nat_lit 4181800143209126683674608815988837194538738562569262204315275113757131535582145

noncomputable def ep520 := nat_lit 10945502353694339260908857090929356763360882433444188677806815281609129662383041

noncomputable def ep521 := BSN.sin_dyadic_bound_f 2838937959 2147483648 3 2 1048576 385360 ep519 ep64 ep515 ep520 ep66 ep515 1016285 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2838937959) qz20 0 2 ep519 ep64 ep515 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2838937959) qz21 0 2 ep520 ep66 ep515 rfl rfl rfl rfl) rfl rfl

noncomputable def ep522 := @Enclosure.Real.IsNear.sin_image qz79 qz398 Bool.false 465868211 1048576 175 262144 Bool.true 1016285 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz79 Bool.false 200088873347547475863 450359962737049600 3204850003084539931 4812300000000000000000 465868211 1048576 175 262144 (ep513 rfl) rfl) (Enclosure.sfrac_false_div 465868211 1048576) (BSN.sin_reduce2 qz398 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 199772498987042505490432) qz25) 226375608064910080 72057594037927936 Bool.false 1016285 1048576 70 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q2 465868211 1048576 226375608064910080 72057594037927936 70 199772498987042505490432 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1016285 1048576 199772498987042505490432 151115727451828646838272 2838937959 2147483648 385360 384984 (ep521 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz399 := (@Enclosure.Real.IsNear.recentre' qz78 Bool.false 185363 1048576 1 1048576 185363 1048576 1 1048576 (ep511 rfl rfl) rfl)

noncomputable def ep523 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz78 (Real.cos qz79)) (@HMul.hMul Real Real Real qz0 qz78 (@Neg.neg Real Real.instNeg (Real.sin qz79))) Bool.true 47863507045 1099511627776 700578709029 5879088673718272 Bool.false 188381636455 1099511627776 704632109319 5879088673718272 (@Enclosure.Real.IsNear.mulLit_ft qz78 (Real.cos qz79) 185363 1048576 1 1048576 258215 1048576 8487061 12615155712 47863507045 1099511627776 700578709029 5879088673718272 qz399 (@Enclosure.Real.IsNear.recentre' (Real.cos qz79) Bool.true 258215 1048576 33948244 50460622848 258215 1048576 8487061 12615155712 (ep518 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz78 (@Neg.neg Real Real.instNeg (Real.sin qz79)) 185363 1048576 1 1048576 1016285 1048576 8487061 12615155712 188381636455 1099511627776 704632109319 5879088673718272 qz399 (@Enclosure.Real.IsNear.neg (Real.sin qz79) Bool.true 1016285 1048576 8487061 12615155712 (@Enclosure.Real.IsNear.recentre' (Real.sin qz79) Bool.true 1016285 1048576 33948244 50460622848 1016285 1048576 8487061 12615155712 (ep522 rfl rfl) rfl)) rfl)

noncomputable def ep524 := @ep391 47863507045 1099511627776 700578709029 5879088673718272 Bool.false 188381636455 1099511627776 704632109319 5879088673718272 Bool.false ep392 1034081122067 549755813888 159532442385535 26455899031732224 Bool.false 112174578025713094361088 25505546097 274877906944 159529748556241 26455899031732224 (ep393 (BSN.head_sum_c_succ qz5 31 32 rfl rfl) (ep509 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep510 ep523) rfl rfl

theorem EMRow43.d9 : Enclosure.Complex.IsNear (BSN.headSumC qz5 33) Bool.false 1034081122067 549755813888 159532442385535 26455899031732224 Bool.false 25505546097 274877906944 159529748556241 26455899031732224 := ep390 (BSN.head_sum_c_succ qz5 32 33 rfl rfl) (ep524 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

theorem EMRow43.d10 : @Eq Nat (BSN.factNat (Nat.mul 2 1)) 2 := @Eq.refl Nat 2

theorem EMRow43.d11 : @Eq Nat (Nat.pow 33 1) 33 := @Eq.refl Nat 33

noncomputable def ep525 := nat_lit 576781467304105200788826827732671

noncomputable def ep526 := nat_lit 312626428072419027567608070144000

noncomputable def ep527 := nat_lit 4879832485494591364120100650330762739239

noncomputable def ep528 := nat_lit 723987512866762871020755380046529560576000

noncomputable abbrev qz654 := (@instHMul Complex Complex.instMul)

noncomputable abbrev qz592 := qz654

noncomputable abbrev qz400 := qz592

noncomputable abbrev qz80 := qz400

noncomputable abbrev qz593 := (@instHSub Complex Complex.instSub)

noncomputable abbrev qz401 := qz593

noncomputable abbrev qz81 := qz401

noncomputable abbrev qz655 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (4 : Complex))

noncomputable abbrev qz656 := (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid))

noncomputable abbrev qz594 := (@HAdd.hAdd Complex Complex Complex qz652 (@HAdd.hAdd Complex Complex Complex qz652 qz655 (@HMul.hMul Complex Complex Complex qz654 Complex.I (@HDiv.hDiv Complex Complex Complex qz656 (↑qz653) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz402 := qz594

noncomputable abbrev qz82 := (Complex.Stirling.logGammaStirling 1 qz402)

noncomputable abbrev qz595 := (@HAdd.hAdd Complex Complex Complex qz652 qz655 (@HMul.hMul Complex Complex Complex qz654 Complex.I (@HDiv.hDiv Complex Complex Complex qz656 (↑qz653) (2 : Complex))))

noncomputable abbrev qz403 := qz595

noncomputable abbrev qz83 := qz403

noncomputable abbrev qz84 := (@HMul.hMul Real Real Real qz267 (@HDiv.hDiv Real Real Real qz270 qz278 (2 : Real)) (Real.log Real.pi))

noncomputable abbrev qz404 := (@instHSub Real Real.instSub)

noncomputable def ep529 := Complex.re (@HMul.hMul Complex Complex Complex qz80 (Complex.exp (@HMul.hMul Complex Complex Complex qz80 Complex.I ↑(@HSub.hSub Real Real Real qz404 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz82 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz83 (@Nat.cast Complex Complex.instNatCast j))))) qz84))) (zetaApproximant qz5 1 33))

noncomputable def ep530 := @Enclosure.Real.IsNear.of_eq ep529 (@HSub.hSub Real Real Real qz404 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz404 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz82 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz83 (@Nat.cast Complex Complex.instNatCast j))))) qz84)) (Complex.re (zetaApproximant qz5 1 33))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz404 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz82 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz83 (@Nat.cast Complex Complex.instNatCast j))))) qz84)) (Complex.im (zetaApproximant qz5 1 33))))

noncomputable def ep531 := nat_lit 2097393210898990181911888000481

noncomputable def ep532 := @Enclosure.Real.IsNear.subLit_tt_n (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz404 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz82 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz83 (@Nat.cast Complex Complex.instNatCast j))))) qz84)) (Complex.re (zetaApproximant qz5 1 33))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz404 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz82 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz83 (@Nat.cast Complex Complex.instNatCast j))))) qz84)) (Complex.im (zetaApproximant qz5 1 33))) ep531

noncomputable def ep533 := nat_lit 1136823374808796463882211164160

noncomputable def ep534 := nat_lit 4873318919311795689701844355320326571917

noncomputable def ep535 := nat_lit 138807759758269745197699967

noncomputable def ep536 := nat_lit 26052202339368252297300672512000

noncomputable def ep537 := nat_lit 3256783091397837209128147505218083661

noncomputable def ep538 := nat_lit 361993756433381435510377690023264780288000

noncomputable def ep539 := nat_lit 54641554515651864133337921443245615864722506696446038014689280

noncomputable def ep540 := @Enclosure.Real.IsNear.mulLit_tf (Real.cos (@HSub.hSub Real Real Real qz404 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz82 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz83 (@Nat.cast Complex Complex.instNatCast j))))) qz84)) (Complex.re (zetaApproximant qz5 1 33)) 1048575 1048576 8648843

noncomputable def ep541 := nat_lit 1650191353972454903156481511

noncomputable def ep542 := nat_lit 894431385247475702956032000

noncomputable def ep543 := nat_lit 87472718523049152908528720921

noncomputable def ep544 := nat_lit 14347573850754757751117709312000

noncomputable def ep545 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz404 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz82 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz83 (@Nat.cast Complex Complex.instNatCast j))))) qz84)) Bool.true 1048575 1048576 34595372

noncomputable abbrev qz405 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 67531293) qz17)

noncomputable def ep546 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz404 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz82 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz83 (@Nat.cast Complex Complex.instNatCast j))))) qz84) qz405 Bool.false 67531293 524288 177

noncomputable def ep547 := nat_lit 8515201745313205120187893

noncomputable def ep548 := nat_lit 25230311424000000000000000000

noncomputable def ep549 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz404 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz82 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz83 (@Nat.cast Complex Complex.instNatCast j))))) qz84) Bool.false 870134084865771871783 6755399441055744000 ep547 ep548

noncomputable def ep550 := nat_lit 2346121883313205120187893

noncomputable def ep551 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz82 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz83 (@Nat.cast Complex Complex.instNatCast j))))) qz84 1365802967092314414631 6755399441055744000 ep550 ep548 4808621037 65536000

noncomputable def ep552 := nat_lit 57025107385763225389170688000

noncomputable def ep553 := nat_lit 2185832547412167362371657

noncomputable def ep554 := nat_lit 12615155712000000000000000000

noncomputable def ep555 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz81 qz82 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz83 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 113495775242190786391 1125899906842624000 ep553 ep554 Bool.false 1365802967092314414631 6755399441055744000

noncomputable def ep556 := nat_lit 2153064547260785493827657

noncomputable def ep557 := nat_lit 2215049883287974808763893

noncomputable def ep558 := @Enclosure.Complex.IsNear.subLitP qz82 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz83 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 104127170621352157391 1125899906842624000 ep556 ep554 Bool.false 1386867614814488694631 6755399441055744000 ep557

noncomputable def ep559 := nat_lit 127784882772213997749368748437929984

noncomputable def ep560 := nat_lit 384439358353654063024670566500007936

noncomputable abbrev qz657 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex))

noncomputable abbrev qz596 := qz657

noncomputable abbrev qz406 := (@HSub.hSub Complex Complex Complex qz593 qz594 qz596)

noncomputable abbrev qz407 := (Complex.log qz594)

noncomputable abbrev qz85 := (@HSub.hSub Complex Complex Complex qz401 (@HMul.hMul Complex Complex Complex qz400 qz406 qz407) qz402)

noncomputable abbrev qz408 := qz596

noncomputable abbrev qz86 := (@HMul.hMul Complex Complex Complex qz400 qz408 ↑(Real.log (@HMul.hMul Real Real Real qz267 (2 : Real) Real.pi)))

noncomputable abbrev qz597 := qz656

noncomputable abbrev qz409 := qz597

noncomputable abbrev qz87 := qz409

noncomputable abbrev qz88 := (@instHMul Nat instMulNat)

noncomputable abbrev qz598 := (@instHPow Complex Int (@ZPow.toPow Complex (@DivInvMonoid.toZPow Complex Complex.instDivInvMonoid)))

noncomputable abbrev qz410 := qz598

noncomputable abbrev qz89 := qz410

noncomputable abbrev qz90 := qz402

noncomputable abbrev qz91 := (@OfNat.ofNat Int 1 (@instOfNat 1))

noncomputable abbrev qz92 := (@OfNat.ofNat Int 2 (@instOfNat 2))

noncomputable abbrev qz411 := (@instHSub Int Int.instSub)

noncomputable abbrev qz412 := (@instHMul Int Int.instMul)

noncomputable def ep561 := @Enclosure.Complex.IsNear.of_eq qz82 (@HAdd.hAdd Complex Complex Complex qz4 (@HAdd.hAdd Complex Complex Complex qz4 qz85 qz86) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz89 qz90 (@HSub.hSub Int Int Int qz411 qz91 (@HMul.hMul Int Int Int qz412 qz92 (@Nat.cast Int instNatCastInt k)))))) Bool.true 104127170621352157391

noncomputable def ep562 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz4 qz85 qz86) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz89 qz90 (@HSub.hSub Int Int Int qz411 qz91 (@HMul.hMul Int Int Int qz412 qz92 (@Nat.cast Int instNatCastInt k))))) Bool.true 104127221941889245391 1125899906842624000

noncomputable def ep563 := nat_lit 7155564679099512244694234955776

noncomputable def ep564 := nat_lit 23826204198039016201607503151104000

noncomputable def ep565 := @ep562 8213287340304397403 48123000000000000000000 Bool.false 462292128931465768909 2251799813685248000 4224812518549347211 48123000000000000000000 Bool.false 3132357 68719476736 3 68719476736 Bool.true 66924895543 51539607552000 64097 51539607552000 Bool.true ep563 104127170621352157391 1125899906842624000 ep556 ep554 Bool.false ep564

noncomputable def ep566 := @Enclosure.Complex.IsNear.addLitP qz85 qz86 Bool.true 105161853793691869391 1125899906842624000 16243000004095122931 96246000000000000000000

noncomputable def ep567 := nat_lit 13648163234367307171889152

noncomputable def ep568 := @ep566 Bool.false 462292128931465768909 2251799813685248000 4224812518549347211 48123000000000000000000 Bool.false 120447 131072 1 524288 Bool.false 0 1 0 1 Bool.true ep567 104127221941889245391 1125899906842624000 8213287340304397403 48123000000000000000000 Bool.false 462292128931465768909 462292128931465768909 2251799813685248000

noncomputable abbrev qz93 := (@HMul.hMul Complex Complex Complex qz400 qz406 qz407)

noncomputable def ep569 := @Enclosure.Complex.IsNear.subLitP qz93 qz90 Bool.true 102628579003295965391 1125899906842624000 16243000004095122931 96246000000000000000000 Bool.false 121325148317849821993

noncomputable def ep570 := @ep569 450359962737049600 4224812518549347211 48123000000000000000000 Bool.false 9000 4000 0 1 Bool.false 256388 4000 0 1 Bool.true 420647415174767477564000 105161853793691869391 1125899906842624000 16243000004095122931 96246000000000000000000 Bool.false 369833703145172615127200 462292128931465768909 2251799813685248000 4224812518549347211 48123000000000000000000

noncomputable abbrev qz94 := qz406

noncomputable abbrev qz95 := qz407

noncomputable def ep571 := @Enclosure.Complex.IsNear.mul qz94 qz95 Bool.true 102628579003295965391 1125899906842624000 16243000004095122931 96246000000000000000000 Bool.false 121325148317849821993 450359962737049600 4224812518549347211

noncomputable abbrev qz96 := (Complex.re qz406)

noncomputable abbrev qz97 := (Complex.re qz407)

noncomputable abbrev qz98 := (Complex.im qz406)

noncomputable abbrev qz99 := (Complex.im qz407)

noncomputable def ep572 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz96 qz97) (@HMul.hMul Real Real Real qz0 qz98 qz99) 65588379898830915 9007199254740992 218750001010583 96246000000000000000 55413563245324914883 562949953421312000

noncomputable def ep573 := nat_lit 462198030156807219511917651150503936

noncomputable def ep574 := @Enclosure.Real.IsNear.mulLit_ff qz96 qz97 7000 4000 0 1 9369768556975845 2251799813685248 31250000144369 24061500000000000000

noncomputable def ep575 := @Enclosure.Complex.IsNear.re_isNear qz94 Bool.false 7000 4000 0 1 Bool.false 256388 4000 0 1

noncomputable abbrev qz599 := (Enclosure.sfrac Bool.false 256388 4000)

noncomputable abbrev qz413 := qz599

noncomputable def ep576 := @Enclosure.Complex.IsNear.of_eq qz94 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz413) Bool.false 7000 4000 0 1 Bool.false 256388 4000 0

noncomputable abbrev qz600 := (Enclosure.sfrac Bool.false 9000 4000)

noncomputable abbrev qz414 := (Complex.log (Complex.mk qz600 qz599))

noncomputable def ep577 := @Enclosure.Complex.IsNear.of_eq qz95 qz414 Bool.false 9369768556975845 2251799813685248 31250000144369 24061500000000000000 Bool.false 864526627538339 562949953421312 250000000048123 96246000000000000000

noncomputable def ep578 := BSN.log_dyadic_bound 279806544 131351806544 1 0 1 1048576 384984 0 1 4467 131631613088 131072000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 279806544) (BSN.artanhQ 131351806544) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz100 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz415 := (Enclosure.Real.IsNear.const Bool.false 1 2)

noncomputable abbrev qz601 := (Real.log (Enclosure.sfrac Bool.false 65815806544 16000000))

noncomputable abbrev qz602 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable def ep579 := @Enclosure.Real.IsNear.mulLit_ff qz100 qz601 1 2 0 1 9369768556975845 1125899906842624 31250000144369 12030750000000000000 9369768556975845 2251799813685248 31250000144369 24061500000000000000 qz415 (BSN.isNear_log_sfrac 65815806544 16000000 9369768556975845 1125899906842624 31250000144369 12030750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 65815806544) qz602)) Bool.false 314397261900784116695040 37778931862957161709568 1000000004619808 384984000000000000000 9369768556975845 1125899906842624 31250000144369 12030750000000000000 (BSN.log_rat_reduce_isNear 65815806544 16000000 12 131631613088 131072000000 4467 1048576 24973259072661432 36028797018963968 384984 1000000000000000 rfl rfl rfl rfl (ep578 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep580 := BSN.arctan_dyadic_bound_f 9000 256388 1 0 1048576 384984 0 1 1 0 1 1 36793 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 256388) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 256388) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz101 := (@HMul.hMul Real Real Real qz267 (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz102 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 2) Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 qz415 BSN.pi_near_15 rfl)

noncomputable abbrev qz416 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 256388)))

noncomputable def ep581 := @Enclosure.Real.IsNear.subLit_ff_p qz101 qz416 884279719003555 562949953421312 1 2000000000000000 36793 1048576 1 384984 906521872997641355264 864526627538339 562949953421312 250000000048123 96246000000000000000 qz102 (ep580 rfl) rfl rfl

noncomputable abbrev qz417 := (Complex.mk qz600 qz599)

noncomputable abbrev qz418 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 256388) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep582 := @Enclosure.Complex.IsNear.re_isNear qz95 Bool.false 9369768556975845 2251799813685248 31250000144369 24061500000000000000 Bool.false 864526627538339 562949953421312 250000000048123 96246000000000000000 (ep577 (@congrArg Complex Complex qz90 qz417 Complex.log (BSN.w_shift_mk qz12 Bool.false 128194 1000 2 qz13 rfl)) (@Enclosure.Complex.IsNear.of_parts qz414 Bool.false 9369768556975845 2251799813685248 31250000144369 24061500000000000000 Bool.false 864526627538339 562949953421312 250000000048123 96246000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz414) (@HMul.hMul Real Real Real qz0 qz100 qz601) Bool.false 9369768556975845 2251799813685248 31250000144369 24061500000000000000 (Enclosure.clog_re_eq 9000 256388 4000 65815806544 16000000 rfl rfl rfl) (ep579 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz414) qz418 Bool.false 864526627538339 562949953421312 250000000048123 96246000000000000000 (Enclosure.clog_im_eq 9000 256388 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz418 (@HSub.hSub Real Real Real qz404 qz101 qz416) Bool.false 864526627538339 562949953421312 250000000048123 96246000000000000000 (BSN.arctan_recip 256388 9000 rfl rfl) ep581))))

noncomputable def ep583 := @Enclosure.Real.IsNear.mulLit_ff qz98 qz99 256388 4000 0 1 864526627538339 562949953421312 250000000048123 96246000000000000000

noncomputable def ep584 := @Enclosure.Complex.IsNear.im_isNear qz94 Bool.false 7000 4000 0 1 Bool.false 256388 4000 0 1

noncomputable def ep585 := @Enclosure.Complex.IsNear.im_isNear qz95 Bool.false 9369768556975845 2251799813685248 31250000144369 24061500000000000000 Bool.false 864526627538339 562949953421312 250000000048123 96246000000000000000 (ep577 (@congrArg Complex Complex qz90 qz417 Complex.log (BSN.w_shift_mk qz12 Bool.false 128194 1000 2 qz13 rfl)) (@Enclosure.Complex.IsNear.of_parts qz414 Bool.false 9369768556975845 2251799813685248 31250000144369 24061500000000000000 Bool.false 864526627538339 562949953421312 250000000048123 96246000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz414) (@HMul.hMul Real Real Real qz0 qz100 qz601) Bool.false 9369768556975845 2251799813685248 31250000144369 24061500000000000000 (Enclosure.clog_re_eq 9000 256388 4000 65815806544 16000000 rfl rfl rfl) (ep579 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz414) qz418 Bool.false 864526627538339 562949953421312 250000000048123 96246000000000000000 (Enclosure.clog_im_eq 9000 256388 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz418 (@HSub.hSub Real Real Real qz404 qz101 qz416) Bool.false 864526627538339 562949953421312 250000000048123 96246000000000000000 (BSN.arctan_recip 256388 9000 rfl rfl) ep581))))

noncomputable abbrev qz103 := (@ep576 1 (BSN.w_sub_half_mk qz278 Bool.false 128194 1000 2 qz280 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz413 Bool.false 7000 4000 0 1 Bool.false 256388 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) (Enclosure.Real.IsNear.const Bool.false 256388 4000)))

noncomputable def ep586 := @ep572 16024250003084539931 96246000000000000000000 ep573 102628579003295965391 1125899906842624000 16243000004095122931 96246000000000000000000 (@ep574 65588379898830915 9007199254740992 218750001010583 96246000000000000000 (ep575 qz103) ep582 rfl) (@ep583 55413563245324914883 562949953421312000 16024250003084539931 96246000000000000000000 (ep584 qz103) ep585 rfl) rfl

noncomputable def ep587 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz96 qz99) (@HMul.hMul Real Real Real qz0 qz98 qz97) 6051686392768373 2251799813685248 1750000000336861 384984000000000000000 120114811039296147393 450359962737049600

noncomputable def ep588 := nat_lit 273199946377469308960430642130059264

noncomputable def ep589 := @Enclosure.Real.IsNear.mulLit_ff qz96 qz99 7000 4000 0 1 864526627538339 562949953421312 250000000048123 96246000000000000000

noncomputable def ep590 := @Enclosure.Real.IsNear.mulLit_ff qz98 qz97 256388 4000 0 1 9369768556975845 2251799813685248 31250000144369 24061500000000000000

noncomputable def ep591 := @ep587 2003031259253619793 24061500000000000000000 ep588 121325148317849821993 450359962737049600 4224812518549347211 48123000000000000000000 (@ep589 6051686392768373 2251799813685248 1750000000336861 384984000000000000000 (ep575 qz103) ep585 rfl) (@ep590 120114811039296147393 450359962737049600 2003031259253619793 24061500000000000000000 (ep584 qz103) ep582 rfl) rfl

noncomputable def ep592 := @Enclosure.Complex.IsNear.of_eq qz90 qz417 Bool.false 9000 4000 0 1 Bool.false 256388 4000 0 1 (BSN.w_shift_mk qz12 Bool.false 128194 1000 2 qz13 rfl)

noncomputable abbrev qz419 := (ep592 (@Enclosure.Complex.IsNear.mk qz600 qz599 Bool.false 9000 4000 0 1 Bool.false 256388 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 256388 4000)))

noncomputable abbrev qz104 := qz419

noncomputable def ep593 := ep570 (@ep571 48123000000000000000000 (ep586 rfl) (ep591 rfl)) qz104 rfl rfl rfl rfl rfl rfl

noncomputable abbrev qz105 := qz408

noncomputable def ep594 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re qz105) (Complex.re ↑qz2)) (@HMul.hMul Real Real Real qz0 (Complex.im qz105) (Complex.im ↑qz2)) 120447 131072 1 524288 0 1 0 1 120447 120447

noncomputable def ep595 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz105) (Complex.re ↑qz2) 1 2 0 1 120447 65536 1 262144 120447 131072 1 524288

noncomputable abbrev qz106 := (@Enclosure.Complex.IsNear.of_eq qz408 (Complex.mk (Enclosure.sfrac Bool.false 1 2) qz277) Bool.false 1 2 0 1 Bool.false 0 1 0 1 BSN.half_c_mk (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 2) qz277 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz415 qz287))

noncomputable def ep596 := ep595 (@Enclosure.Complex.IsNear.re_isNear qz105 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz106) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz2) qz2 Bool.false 120447 65536 1 262144 (Complex.ofReal_re qz2) EMRow43.d4)

noncomputable def ep597 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz105) (Complex.im ↑qz2) 0 1 0 1 0 1 0 1 0 1 0 1

noncomputable def ep598 := ep597 (@Enclosure.Complex.IsNear.im_isNear qz105 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz106) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz2) qz10 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz2) (0 : Real) qz10 (Complex.ofReal_im qz2) Enclosure.sfrac_zero_eq) qz22)

noncomputable def ep599 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re qz105) (Complex.im ↑qz2)) (@HMul.hMul Real Real Real qz0 (Complex.im qz105) (Complex.re ↑qz2)) 0 1 0 1 0 1 0 1 0 0

noncomputable def ep600 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz105) (Complex.im ↑qz2) 1 2 0 1 0 1 0 1 0 1 0 1

noncomputable def ep601 := ep600 (@Enclosure.Complex.IsNear.re_isNear qz105 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz106) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz2) qz10 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz2) (0 : Real) qz10 (Complex.ofReal_im qz2) Enclosure.sfrac_zero_eq) qz22)

noncomputable def ep602 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz105) (Complex.re ↑qz2) 0 1 0 1 120447 65536 1 262144 0 1 0 1

noncomputable def ep603 := ep602 (@Enclosure.Complex.IsNear.im_isNear qz105 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz106) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz2) qz2 Bool.false 120447 65536 1 262144 (Complex.ofReal_re qz2) EMRow43.d4)

noncomputable def ep604 := @ep568 4224812518549347211 48123000000000000000000 (ep593 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz105 (↑qz2) Bool.false 120447 131072 1 524288 Bool.false 0 1 0 1 (@ep594 131072 1 524288 (ep596 rfl) (ep598 rfl) rfl rfl) (@ep599 1 0 1 (ep601 rfl) (ep603 rfl) rfl rfl))

noncomputable abbrev qz107 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)

noncomputable abbrev qz420 := (@Nat.cast Complex Complex.instNatCast 1)

noncomputable abbrev qz108 := (@HMul.hMul Complex Complex Complex qz400 (@HMul.hMul Complex Complex Complex qz400 (2 : Complex) qz420) (@HSub.hSub Complex Complex Complex qz401 (@HMul.hMul Complex Complex Complex qz400 (2 : Complex) qz420) (1 : Complex)))

noncomputable abbrev qz421 := (@HPow.hPow Complex Int Complex qz598 qz594 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz109 := qz421

noncomputable def ep605 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz89 qz90 (@HSub.hSub Int Int Int qz411 qz91 (@HMul.hMul Int Int Int qz412 qz92 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz89 qz90 (@HSub.hSub Int Int Int qz411 qz91 (@HMul.hMul Int Int Int qz412 qz92 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108) qz109)) Bool.false 3132357 68719476736 3 68719476736

noncomputable def ep606 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz89 qz90 (@HSub.hSub Int Int Int qz411 qz91 (@HMul.hMul Int Int Int qz412 qz92 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108) qz109) Bool.false 0 1 0 1 Bool.false

noncomputable def ep607 := @ep606 0 1 0 1 Bool.false 3132357 68719476736 3 68719476736 Bool.true 66924895543 51539607552000 64097 51539607552000 Bool.false 3132357 3132357 68719476736 3 68719476736 Bool.true 66924895543 66924895543 51539607552000 64097

noncomputable def ep608 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz89 qz90 (@HSub.hSub Int Int Int qz411 qz91 (@HMul.hMul Int Int Int qz412 qz92 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep609 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108) qz109 Bool.false 3132357 68719476736 3 68719476736 Bool.true 66924895543 51539607552000 64097 51539607552000

noncomputable abbrev qz110 := (Complex.re qz421)

noncomputable abbrev qz111 := (Complex.im qz421)

noncomputable def ep610 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108)) qz110) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108)) qz111) 3132357 68719476736 3 68719476736 0 1 0

noncomputable def ep611 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108)) qz110 1 12 0 1 9397071 17179869184 9 17179869184 3132357

noncomputable def ep612 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz10) Bool.false 1 12 0 1 Bool.false 0 1 0 1

noncomputable abbrev qz422 := (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 12) qz10 Bool.false 1 12 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 12) qz22)

noncomputable def ep613 := @Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep612 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz422)

noncomputable def ep614 := @Enclosure.Complex.IsNear.re_isNear qz109 Bool.false 9397071 17179869184 9 17179869184 Bool.true 66924895543 4294967296000 64097 4294967296000

noncomputable abbrev qz603 := (@instHPow Complex Nat (@NPow.toPow Complex (@Monoid.toNPow Complex (@Semiring.toMonoid Complex Complex.instSemiring))))

noncomputable abbrev qz423 := (@HPow.hPow Complex Nat Complex qz603 qz594 1)

noncomputable abbrev qz112 := (@Inv.inv Complex Complex.instInv qz423)

noncomputable def ep615 := @Enclosure.Complex.IsNear.of_eq qz109 qz112 Bool.false 9397071 17179869184 9 17179869184 Bool.true 66924895543 4294967296000 64097

noncomputable def ep616 := @Enclosure.Complex.IsNear.of_parts qz112 Bool.false 9397071 17179869184 9 17179869184 Bool.true 66924895543 4294967296000 64097

noncomputable abbrev qz113 := (Complex.re qz423)

noncomputable abbrev qz114 := (@MonoidWithZeroHom Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz115 := (@MonoidWithZeroHom.funLike Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz116 := qz423

noncomputable def ep617 := @Enclosure.Real.IsNear.mulLit_ff qz113 (@Inv.inv Real Real.instInv (@DFunLike.coe qz114 Complex (fun (x : Complex) => Real) qz115 Complex.normSq qz116)) 9000 4000 0 1 1044119 4294967296 1 4294967296

noncomputable def ep618 := @Enclosure.Complex.IsNear.re_isNear qz116 Bool.false 9000 4000 0 1 Bool.false 256388 4000 0 1

noncomputable def ep619 := @Enclosure.Complex.IsNear.of_eq qz116 qz90 Bool.false 9000 4000 0 1 Bool.false 256388 4000 0

noncomputable def ep620 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz114 Complex (fun (x : Complex) => Real) qz115 Complex.normSq qz116)) Bool.false 1044119 4294967296 1 4294967296 1044119 4294967296 1

noncomputable abbrev qz117 := (Complex.im qz423)

noncomputable abbrev qz424 := (@instHAdd Real Real.instAdd)

noncomputable def ep621 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz114 Complex (fun (x : Complex) => Real) qz115 Complex.normSq qz116) (@HAdd.hAdd Real Real Real qz424 (@HMul.hMul Real Real Real qz0 qz113 qz113) (@HMul.hMul Real Real Real qz0 qz117 qz117)) Bool.false 4113487909 1000000 0 1

noncomputable def ep622 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz113 qz113) (@HMul.hMul Real Real Real qz0 qz117 qz117) 81 16 0 1 4108425409 1000000

noncomputable def ep623 := @Enclosure.Real.IsNear.mulLit_ff qz113 qz113 9000 4000 0 1 9000 4000 0 1

noncomputable def ep624 := @Enclosure.Real.IsNear.mulLit_ff qz117 qz117 256388 4000 0 1 256388 4000 0 1

noncomputable def ep625 := @Enclosure.Complex.IsNear.im_isNear qz116 Bool.false 9000 4000 0 1 Bool.false 256388 4000 0 1

noncomputable abbrev qz118 := (ep618 (@ep619 1 (BSN.pow_one_c qz402) qz419))

noncomputable abbrev qz119 := (ep625 (@ep619 1 (BSN.pow_one_c qz402) qz419))

noncomputable def ep626 := @ep622 0 1 65815806544 4113487909 1000000 0 1 (@ep623 81 16 0 1 qz118 qz118 rfl) (@ep624 4108425409 1000000 0 1 qz119 qz119 rfl)

noncomputable def ep627 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz114 Complex (fun (x : Complex) => Real) qz115 Complex.normSq qz116) 4113487909 1000000 0 1 522059 522060 2147483648 (ep621 (Enclosure.Complex.normSq_eq_mul_add_mul qz116) (ep626 rfl rfl)) rfl

noncomputable def ep628 := @Enclosure.Real.IsNear.of_eq (Complex.re qz112) (@HMul.hMul Real Real Real qz0 qz113 (@Inv.inv Real Real.instInv (@DFunLike.coe qz114 Complex (fun (x : Complex) => Real) qz115 Complex.normSq qz116))) Bool.false 9397071 17179869184 9 17179869184 (Enclosure.Complex.inv_re_eq_mul qz116) (@ep617 9397071 17179869184 9 17179869184 qz118 (@ep620 4294967296 (ep627 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep629 := @Enclosure.Real.IsNear.of_eq (Complex.im qz112) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz117) (@Inv.inv Real Real.instInv (@DFunLike.coe qz114 Complex (fun (x : Complex) => Real) qz115 Complex.normSq qz116))) Bool.true 66924895543 4294967296000 64097 4294967296000 (Enclosure.Complex.inv_im_eq_mul qz116)

noncomputable def ep630 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz117) (@Inv.inv Real Real.instInv (@DFunLike.coe qz114 Complex (fun (x : Complex) => Real) qz115 Complex.normSq qz116)) 256388 4000 0 1 1044119 4294967296 1

noncomputable def ep631 := @ep630 4294967296 66924895543 4294967296000 64097 4294967296000 (@Enclosure.Real.IsNear.neg qz117 Bool.false 256388 4000 0 1 qz119) (@ep620 4294967296 (ep627 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep632 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108)) qz111 0 1 0 1 66924895543 4294967296000 64097 4294967296000 0

noncomputable def ep633 := @Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep612 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz422)

noncomputable def ep634 := @Enclosure.Complex.IsNear.im_isNear qz109 Bool.false 9397071 17179869184 9 17179869184 Bool.true 66924895543 4294967296000 64097 4294967296000

noncomputable abbrev qz120 := (@ep615 4294967296000 (BSN.zpow_one_sub_two_mul qz402 1 1 rfl rfl) (@ep616 4294967296000 ep628 (ep629 ep631)))

noncomputable def ep635 := @ep610 1 3132357 3132357 68719476736 3 68719476736 (@ep611 68719476736 3 68719476736 ep613 (ep614 qz120) rfl) (@ep632 1 0 1 ep633 (ep634 qz120) rfl) rfl

noncomputable def ep636 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108)) qz111) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108)) qz110) 66924895543 51539607552000 64097 51539607552000 0 1 0

noncomputable def ep637 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108)) qz111 1 12 0 1 66924895543 4294967296000 64097 4294967296000 66924895543

noncomputable def ep638 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108)) qz110 0 1 0 1 9397071 17179869184 9 17179869184 0

noncomputable def ep639 := @ep636 1 66924895543 66924895543 51539607552000 64097 51539607552000 (@ep637 51539607552000 64097 51539607552000 ep613 (ep634 qz120) rfl) (@ep638 1 0 1 ep633 (ep614 qz120) rfl) rfl

noncomputable abbrev qz121 := (@Enclosure.Complex.IsNear.mk qz277 qz277 Bool.false 0 1 0 1 Bool.false 0 1 0 1 qz287 qz287)

noncomputable def ep640 := @ep607 51539607552000 (@ep608 0 1 0 1 (BSN.stirling_sum_base qz90) qz121) (ep609 (ep635 rfl) (ep639 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep641 := @ep565 1386867614814488694631 6755399441055744000 ep557 ep548 (ep604 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep605 Bool.true 66924895543 51539607552000 64097 51539607552000 (BSN.stirling_sum_succ qz90 0 1 rfl) (ep640 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep642 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz83 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz12 2) Bool.false 9368604620838629 1125899906842624 31250000144369 12030750000000000000 Bool.false 877693655090595 281474976710656

noncomputable abbrev qz122 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz272 qz403 qz420))

noncomputable def ep643 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz12 2) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz12 1) qz122) Bool.false 9368604620838629 1125899906842624 31250000144369 12030750000000000000 Bool.false 877693655090595 281474976710656 250000000048123 48123000000000000000

noncomputable def ep644 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz12 1) qz122 Bool.false 9368399536150245 2251799813685248 31250000144369 24061500000000000000 Bool.false 882084453844387 562949953421312 250000000048123 96246000000000000000 Bool.false

noncomputable def ep645 := nat_lit 42192444279390356529193611689984

noncomputable def ep646 := nat_lit 988195204502863070411127521280

noncomputable abbrev qz123 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz272 qz403 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep647 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz12 1) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz12 0) qz123) Bool.false 9368399536150245 2251799813685248 31250000144369 24061500000000000000 Bool.false 882084453844387 562949953421312 250000000048123 96246000000000000000

noncomputable def ep648 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz12 0) qz123 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz425 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz599))

noncomputable def ep649 := @Enclosure.Complex.IsNear.of_eq qz123 qz425 Bool.false 9368399536150245 2251799813685248 31250000144369 24061500000000000000 Bool.false 882084453844387 562949953421312 250000000048123 96246000000000000000

noncomputable def ep650 := BSN.log_dyadic_bound 199806544 131271806544 1 0 1 1048576 384984 0 1 3192 131471613088 131072000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 199806544) (BSN.artanhQ 131271806544) 0 0 rfl) rfl rfl rfl

noncomputable def ep651 := @Enclosure.Real.IsNear.mulLit_ff qz100 (Real.log (Enclosure.sfrac Bool.false 65735806544 16000000)) 1 2 0 1 9368399536150245 1125899906842624 31250000144369 12030750000000000000 9368399536150245 2251799813685248 31250000144369 24061500000000000000 qz415 (BSN.isNear_log_sfrac 65735806544 16000000 9368399536150245 1125899906842624 31250000144369 12030750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 65735806544) qz602)) Bool.false 314351325184584937635840 37778931862957161709568 1000000004619808 384984000000000000000 9368399536150245 1125899906842624 31250000144369 12030750000000000000 (BSN.log_rat_reduce_isNear 65735806544 16000000 12 131471613088 131072000000 3192 1048576 24973259072661432 36028797018963968 384984 1000000000000000 rfl rfl rfl rfl (ep650 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep652 := BSN.arctan_dyadic_bound_f 1000 256388 1 0 1048576 384984 0 1 1 0 1 1 4089 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 256388) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 256388) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz426 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable abbrev qz427 := (@Nat.cast Real Real.instNatCast 256388)

noncomputable def ep653 := @Enclosure.Real.IsNear.subLit_ff_p qz101 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz426 qz427)) 884279719003555 562949953421312 1 2000000000000000 4089 1048576 1 384984 924932588274331942912 882084453844387 562949953421312 250000000048123 96246000000000000000 qz102 (ep652 rfl) rfl rfl

noncomputable abbrev qz124 := (@HAdd.hAdd Complex Complex Complex qz272 qz403 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz428 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz599)

noncomputable def ep654 := @ep648 9368399536150245 2251799813685248 31250000144369 24061500000000000000 Bool.false 882084453844387 562949953421312 250000000048123 96246000000000000000 Bool.false 9368399536150245 9368399536150245 2251799813685248 31250000144369 24061500000000000000 Bool.false 882084453844387 882084453844387 562949953421312 250000000048123 96246000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz12 0) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz12) qz121) (ep649 (@congrArg Complex Complex qz124 qz428 Complex.log (BSN.w_shift_mk qz12 Bool.false 128194 1000 0 qz13 rfl)) (@Enclosure.Complex.IsNear.of_parts qz425 Bool.false 9368399536150245 2251799813685248 31250000144369 24061500000000000000 Bool.false 882084453844387 562949953421312 250000000048123 96246000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz425) (@HMul.hMul Real Real Real qz0 qz100 (Real.log (Enclosure.sfrac Bool.false 65735806544 16000000))) Bool.false 9368399536150245 2251799813685248 31250000144369 24061500000000000000 (Enclosure.clog_re_eq 1000 256388 4000 65735806544 16000000 rfl rfl rfl) (ep651 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz425) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz427 qz426)) Bool.false 882084453844387 562949953421312 250000000048123 96246000000000000000 (Enclosure.clog_im_eq 1000 256388 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz427 qz426)) (@HSub.hSub Real Real Real qz404 qz101 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz426 qz427))) Bool.false 882084453844387 562949953421312 250000000048123 96246000000000000000 (BSN.arctan_recip 256388 1000 rfl rfl) ep653)))) rfl rfl

noncomputable abbrev qz429 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz599))

noncomputable def ep655 := @Enclosure.Complex.IsNear.of_eq qz122 qz429 Bool.false 9368809705527013 2251799813685248 31250000144369 24061500000000000000 Bool.false 873302856336803 562949953421312 250000000048123 96246000000000000000

noncomputable def ep656 := BSN.log_dyadic_bound 223806544 131295806544 1 0 1 1048576 384984 0 1 3574 131519613088 131072000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 223806544) (BSN.artanhQ 131295806544) 0 0 rfl) rfl rfl rfl

noncomputable def ep657 := @Enclosure.Real.IsNear.mulLit_ff qz100 (Real.log (Enclosure.sfrac Bool.false 65759806544 16000000)) 1 2 0 1 9368809705527013 1125899906842624 31250000144369 12030750000000000000 9368809705527013 2251799813685248 31250000144369 24061500000000000000 qz415 (BSN.isNear_log_sfrac 65759806544 16000000 9368809705527013 1125899906842624 31250000144369 12030750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 65759806544) qz602)) Bool.false 314365088185046181871616 37778931862957161709568 1000000004619808 384984000000000000000 9368809705527013 1125899906842624 31250000144369 12030750000000000000 (BSN.log_rat_reduce_isNear 65759806544 16000000 12 131519613088 131072000000 3574 1048576 24973259072661432 36028797018963968 384984 1000000000000000 rfl rfl rfl rfl (ep656 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep658 := BSN.arctan_dyadic_bound_f 5000 256388 1 0 1048576 384984 0 1 1 0 1 1 20446 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 256388) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 256388) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz430 := (@Nat.cast Real Real.instNatCast 5000)

noncomputable def ep659 := @Enclosure.Real.IsNear.subLit_ff_p qz101 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz430 qz427)) 884279719003555 562949953421312 1 2000000000000000 20446 1048576 1 384984 915724415886219542528 873302856336803 562949953421312 250000000048123 96246000000000000000 qz102 (ep658 rfl) rfl rfl

noncomputable abbrev qz125 := (@HAdd.hAdd Complex Complex Complex qz272 qz403 qz420)

noncomputable abbrev qz431 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz599)

noncomputable def ep660 := @ep644 9368809705527013 2251799813685248 31250000144369 24061500000000000000 Bool.false 873302856336803 562949953421312 250000000048123 96246000000000000000 Bool.false ep645 9368604620838629 1125899906842624 31250000144369 12030750000000000000 Bool.false ep646 877693655090595 281474976710656 250000000048123 48123000000000000000 (ep647 (BSN.log_sum_c_succ qz12 0 1 rfl) (ep654 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep655 (@congrArg Complex Complex qz125 qz431 Complex.log (BSN.w_shift_mk qz12 Bool.false 128194 1000 1 qz13 rfl)) (@Enclosure.Complex.IsNear.of_parts qz429 Bool.false 9368809705527013 2251799813685248 31250000144369 24061500000000000000 Bool.false 873302856336803 562949953421312 250000000048123 96246000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz429) (@HMul.hMul Real Real Real qz0 qz100 (Real.log (Enclosure.sfrac Bool.false 65759806544 16000000))) Bool.false 9368809705527013 2251799813685248 31250000144369 24061500000000000000 (Enclosure.clog_re_eq 5000 256388 4000 65759806544 16000000 rfl rfl rfl) (ep657 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz429) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz427 qz430)) Bool.false 873302856336803 562949953421312 250000000048123 96246000000000000000 (Enclosure.clog_im_eq 5000 256388 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz427 qz430)) (@HSub.hSub Real Real Real qz404 qz101 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz430 qz427))) Bool.false 873302856336803 562949953421312 250000000048123 96246000000000000000 (BSN.arctan_recip 256388 5000 rfl rfl) ep659)))) rfl rfl

noncomputable def ep661 := @ep558 ep548 Bool.false 9368604620838629 1125899906842624 31250000144369 12030750000000000000 Bool.false 877693655090595 281474976710656 250000000048123 48123000000000000000 Bool.true ep559 113495775242190786391 1125899906842624000 ep553 ep554 Bool.false ep560 1365802967092314414631 6755399441055744000 ep550 ep548 (@ep561 1125899906842624000 ep556 ep554 Bool.false 1386867614814488694631 6755399441055744000 ep557 ep548 (BSN.logGammaStirling_unfold 1 qz90) (ep641 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep642 250000000048123 48123000000000000000 (BSN.log_sum_c_eq qz12 2) (ep643 (BSN.log_sum_c_succ qz12 1 2 rfl) (ep660 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz126 := (@HDiv.hDiv Real Real Real qz270 qz278 (2 : Real))

noncomputable def ep662 := @Enclosure.Real.IsNear.mulLit_ff qz126 (Real.log Real.pi) 128194 2000 0 1 75021 65536 1 262144 4808621037 65536000 64097 262144000 (@Enclosure.Real.IsNear.of_eq qz126 (Enclosure.sfrac Bool.false 128194 2000) Bool.false 128194 2000 0 1 (BSN.t_half_eq qz12 Bool.false 128194 1000 qz13) (Enclosure.Real.IsNear.const Bool.false 128194 2000)) EMRow43.d5 rfl

noncomputable def ep663 := @ep551 64097 262144000 ep552 870134084865771871783 6755399441055744000 ep547 ep548 (@ep555 ep550 ep548 (ep661 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep662 rfl rfl

noncomputable def ep664 := BSN.cos_dyadic_bound_f 903185 2147483648 1 0 1048576 385360 0 1 1 0 1 1 1048575 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 903185) qz15 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 903185) qz16 0 0 rfl) rfl rfl

noncomputable def ep665 := @ep546 524288 Bool.true 1048575 1048576 1 192492 (@ep549 67531293 524288 177 524288 ep663 rfl) (Enclosure.sfrac_false_div 67531293 524288) (BSN.cos_reduce2 qz405 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 31778007611883913216) qz19) 226375608064910080 72057594037927936 Bool.false 1048575 1048576 20 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q2 67531293 524288 226375608064910080 72057594037927936 20 31778007611883913216 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1048575 1048576 31778007611883913216 75557863725914323419136 903185 2147483648 385360 384984 (ep664 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep666 := nat_lit 2832811423638158065259183

noncomputable def ep667 := nat_lit 223607846311868925739008000

noncomputable def ep668 := nat_lit 8747318109162555226884867821

noncomputable def ep669 := nat_lit 1434757385075475775111770931200

noncomputable abbrev qz604 := (@Nat.cast Complex Complex.instNatCast 33)

noncomputable abbrev qz432 := (@HPow.hPow Complex Complex Complex qz530 qz604 qz531)

noncomputable abbrev qz127 := qz432

noncomputable abbrev qz433 := qz604

noncomputable abbrev qz128 := (@HAdd.hAdd Complex Complex Complex qz272 (@HDiv.hDiv Complex Complex Complex qz409 qz433 (@HSub.hSub Complex Complex Complex qz401 qz271 (1 : Complex))) qz408)

noncomputable abbrev qz129 := (@instHSub Nat instSubNat)

noncomputable abbrev qz434 := qz603

noncomputable abbrev qz130 := qz434

noncomputable abbrev qz131 := qz433

noncomputable def ep670 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz5 1 33) (@HAdd.hAdd Complex Complex Complex qz4 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 33, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz7) (@HMul.hMul Complex Complex Complex qz80 qz127 (@HAdd.hAdd Complex Complex Complex qz4 qz128 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1))))))) Bool.false ep541 ep542 ep543

noncomputable def ep671 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 33, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz7) (@HMul.hMul Complex Complex Complex qz80 qz127 (@HAdd.hAdd Complex Complex Complex qz4 qz128 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))))) Bool.false 1034081122067 549755813888 159532442385535 26455899031732224

noncomputable def ep672 := nat_lit 32218521654764441653106489

noncomputable def ep673 := nat_lit 955019919333477261015140921

noncomputable def ep674 := nat_lit 17915455671251236886994817

noncomputable def ep675 := nat_lit 95694340650087341015957021

noncomputable def ep676 := nat_lit 907202290874067647218167713302229024768

noncomputable def ep677 := nat_lit 778677274896709774589876783915466752

noncomputable def ep678 := @ep671 Bool.false 25505546097 274877906944 159529748556241 26455899031732224 Bool.true ep672 ep542 ep673 ep544 Bool.true ep674 ep667 ep675 ep669 Bool.false ep676 ep541 ep542 ep543 ep544 Bool.false ep677 ep666 ep667

noncomputable def ep679 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 33, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz7) (BSN.headSumC qz5 33) Bool.false 1034081122067 549755813888 159532442385535 26455899031732224 Bool.false 25505546097 274877906944 159529748556241

noncomputable def ep680 := @Enclosure.Complex.IsNear.mul qz127 (@HAdd.hAdd Complex Complex Complex qz4 qz128 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1))))) Bool.true ep672 ep542 ep673 ep544 Bool.true

noncomputable def ep681 := nat_lit 1788862770494951405912064

noncomputable abbrev qz132 := (Complex.re qz432)

noncomputable abbrev qz133 := (Complex.im qz432)

noncomputable def ep682 := @Enclosure.Real.IsNear.subLit_tt_n (@HMul.hMul Real Real Real qz0 qz132 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz128 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz133 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz128 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1))))))) 81992688761792873286859 ep681 158061775254743254077295

noncomputable def ep683 := nat_lit 2690170097016517078334570496

noncomputable def ep684 := nat_lit 27103981371135627362304000

noncomputable def ep685 := nat_lit 30551941265867247073518433

noncomputable def ep686 := nat_lit 3912974686569479386668466176000

noncomputable def ep687 := nat_lit 1746500421472530466136769457342157122941392781312

noncomputable def ep688 := @Enclosure.Real.IsNear.mulLit_tf qz132 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz128 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))))) 50370163883 549755813888 97101310415 826746844741632 1627802699873

noncomputable abbrev qz435 := (@Nat.cast Real Real.instNatCast 33)

noncomputable abbrev qz134 := (@Inv.inv Real Real.instInv (Real.sqrt qz435))

noncomputable abbrev qz605 := (Real.log (Enclosure.sfrac Bool.false 33 1))

noncomputable abbrev qz135 := (@HMul.hMul Real Real Real qz267 qz278 qz605)

noncomputable abbrev qz136 := (Real.sin (@HMul.hMul Real Real Real qz267 qz278 qz605))

noncomputable abbrev qz606 := (@Neg.neg Real Real.instNeg qz136)

noncomputable def ep689 := @Enclosure.Complex.IsNear.of_eq qz127 (Complex.mk (@HMul.hMul Real Real Real qz0 qz134 (Real.cos qz135)) (@HMul.hMul Real Real Real qz0 qz134 qz606)) Bool.true 50370163883 549755813888 97101310415 826746844741632 Bool.true 162742589607 1099511627776 6230830142831 52911798063464448 (BSN.cpow_neg_s_mk qz12 128194 1000 33 qz13 rfl)

noncomputable abbrev qz436 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 33) qz14)

noncomputable def ep690 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz435) 6023611 1048576 1 1048576 91266 91267 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz435) (Real.sqrt qz436) Bool.false 6023611 1048576 1 1048576 (BSN.sqrt_natCast_div_one 33) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz436) Bool.false 6023611 1048576 1 1048576 6023611 1048576 1 1048576 (BSN.sqrt_enclosure 33 1 3011805 3011806 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep691 := BSN.log_dyadic_bound 1 65 2 1 12675 524288 192492 1 1 16133 66 64 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1) (BSN.artanhQ 65) 0 1 1 12675 1 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz137 := qz605

noncomputable abbrev qz437 := (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 33) qz14))

noncomputable def ep692 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz137 128194 1000 0 1 15746868335186131 4503599627370496 50000000048123 9624600000000000000 1009327019680425438707 2251799813685248000 3204850003084539931 4812300000000000000000 qz18 (BSN.isNear_log_sfrac 33 1 15746868335186131 4503599627370496 50000000048123 9624600000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz437 Bool.false 66047152845744529997824 18889465931478580854784 1000000000962460 192492000000000000000 15746868335186131 4503599627370496 50000000048123 9624600000000000000 (BSN.log_rat_reduce_isNear 33 1 5 66 64 16133 524288 24973259072661432 36028797018963968 192492 1000000000000000 rfl rfl rfl rfl (ep691 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep693 := nat_lit 2007486721776243010269265661437935616

noncomputable def ep694 := BSN.sin_dyadic_bound_f 1190318464 2147483648 2 1 1048576 385360 ep693 ep92 ep693 ep693 ep93 ep693 551902 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1190318464) qz20 0 1 ep693 ep92 ep693 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1190318464) qz21 0 1 ep693 ep93 ep693 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz438 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 470004519) qz24)

noncomputable def ep695 := @Enclosure.Real.IsNear.cos_image qz135 qz438 Bool.false 470004519 1048576 699 1048576 Bool.true 551902 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz135 Bool.false 1009327019680425438707 2251799813685248000 3204850003084539931 4812300000000000000000 470004519 1048576 699 1048576 (ep692 rfl) rfl) (Enclosure.sfrac_false_div 470004519 1048576) (BSN.cos_reduce1 qz438 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 83761215539896299552768) qz25) 226375608064910080 72057594037927936 Bool.false 551902 1048576 71 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q1 470004519 1048576 226375608064910080 72057594037927936 71 83761215539896299552768 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 551902 1048576 83761215539896299552768 151115727451828646838272 1190318464 2147483648 385360 384984 (ep694 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep696 := BSN.cos_dyadic_bound_f 1190318464 2147483648 2 1 1048576 385360 ep693 ep96 ep693 ep693 ep97 ep693 891579 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1190318464) qz15 0 1 ep693 ep96 ep693 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1190318464) qz16 0 1 ep693 ep97 ep693 rfl rfl rfl rfl) rfl rfl

noncomputable def ep697 := @Enclosure.Real.IsNear.sin_image qz135 qz438 Bool.false 470004519 1048576 699 1048576 Bool.false 891579 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz135 Bool.false 1009327019680425438707 2251799813685248000 3204850003084539931 4812300000000000000000 470004519 1048576 699 1048576 (ep692 rfl) rfl) (Enclosure.sfrac_false_div 470004519 1048576) (BSN.sin_reduce1 qz438 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 83761215539896299552768) qz25) 226375608064910080 72057594037927936 Bool.false 891579 1048576 71 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q1 470004519 1048576 226375608064910080 72057594037927936 71 83761215539896299552768 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 891579 1048576 83761215539896299552768 151115727451828646838272 1190318464 2147483648 385360 384984 (ep696 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz439 := (@Enclosure.Real.IsNear.recentre' qz134 Bool.false 182533 1048576 1 1048576 182533 1048576 1 1048576 (ep690 rfl rfl) rfl)

noncomputable def ep698 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz134 (Real.cos qz135)) (@HMul.hMul Real Real Real qz0 qz134 qz606) Bool.true 50370163883 549755813888 97101310415 826746844741632 Bool.true 162742589607 1099511627776 6230830142831 52911798063464448 (@Enclosure.Real.IsNear.mulLit_ft qz134 (Real.cos qz135) 182533 1048576 1 1048576 275951 524288 33900121 50460622848 50370163883 549755813888 97101310415 826746844741632 qz439 (@Enclosure.Real.IsNear.recentre' (Real.cos qz135) Bool.true 551902 1048576 135600484 201842491392 275951 524288 33900121 50460622848 (ep695 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz134 qz606 182533 1048576 1 1048576 891579 1048576 33900121 50460622848 162742589607 1099511627776 6230830142831 52911798063464448 qz439 (@Enclosure.Real.IsNear.neg qz136 Bool.false 891579 1048576 33900121 50460622848 (@Enclosure.Real.IsNear.recentre' qz136 Bool.false 891579 1048576 135600484 201842491392 891579 1048576 33900121 50460622848 (ep697 rfl rfl) rfl)) rfl)

noncomputable def ep699 := @ep688 3253922423928 0 1 81992688761792873286859 ep681 158061775254743254077295 ep683 (@Enclosure.Complex.IsNear.re_isNear qz127 Bool.true 50370163883 549755813888 97101310415 826746844741632 Bool.true 162742589607 1099511627776 6230830142831 52911798063464448 (ep689 ep698))

noncomputable def ep700 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz128 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1))))) Bool.false 1627802699873 3253922423928 0 1 Bool.false

noncomputable def ep701 := @Enclosure.Complex.IsNear.addLitP qz128 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) Bool.false 4100237909 8216975818 0 1 Bool.true 1057600500

noncomputable def ep702 := @ep701 4108487909 0 1 Bool.false 1 792 0 1 Bool.false 5827 18000 0 1 Bool.false 3255605399746 1627802699873 3253922423928 0 1 Bool.false 4903350045743 4903350045743 73952782362000 0 1

noncomputable abbrev qz138 := (@HDiv.hDiv Complex Complex Complex qz409 qz433 (@HSub.hSub Complex Complex Complex qz401 qz271 (1 : Complex)))

noncomputable def ep703 := @Enclosure.Complex.IsNear.addLitP qz138 qz105 Bool.true 66000000 65735806544 0 1 Bool.true 16921608000 65735806544 0 1

noncomputable def ep704 := @Enclosure.Complex.IsNear.of_eq qz138 (Complex.mk (Enclosure.sfrac Bool.true 66000000 65735806544) (Enclosure.sfrac Bool.true 16921608000 65735806544)) Bool.true 66000000 65735806544 0 1 Bool.true 16921608000 65735806544 0 1

noncomputable def ep705 := @ep703 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 65603806544 4100237909 8216975818 0 1 Bool.true 16921608000 1057600500 4108487909 0 1 (ep704 (BSN.N_div_s_sub_one_mk qz12 128194 1000 33 qz13 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 66000000 65735806544) (Enclosure.sfrac Bool.true 16921608000 65735806544) Bool.true 66000000 65735806544 0 1 Bool.true 16921608000 65735806544 0 1 (Enclosure.Real.IsNear.const Bool.true 66000000 65735806544) (Enclosure.Real.IsNear.const Bool.true 16921608000 65735806544))) qz106 rfl

noncomputable abbrev qz139 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)))

noncomputable abbrev qz440 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz603 qz604 1))

noncomputable abbrev qz140 := qz440

noncomputable def ep706 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz140)) Bool.false 1 792 0 1

noncomputable def ep707 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz140) Bool.false 0 1 0 1 Bool.false

noncomputable def ep708 := @ep707 0 1 0 1 Bool.false 1 792 0 1 Bool.false 5827 18000 0 1 Bool.false 1 1 792 0 1 Bool.false 5827 5827 18000 0

noncomputable def ep709 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep710 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz140 Bool.false 1 792 0 1 Bool.false 5827 18000 0 1

noncomputable abbrev qz141 := (Complex.re qz440)

noncomputable abbrev qz142 := (Complex.im qz440)

noncomputable def ep711 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz141) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz142) 1 792 0 1 0 1 0

noncomputable def ep712 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz141 1 24 0 1 1 33 0 1 1

noncomputable def ep713 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep714 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep715 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz10) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 1 1 6 2 Bool.false BSN.bern_real_1 EMRow43.d10 rfl) qz422

noncomputable def ep716 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz5 Bool.false 1 2 0 1 Bool.false 128194 1000 0 1 (BSN.ascPochhammer_one_eval qz5)

noncomputable def ep717 := ep716 (@Enclosure.Complex.IsNear.of_eq qz5 (Complex.mk qz100 qz12) Bool.false 1 2 0 1 Bool.false 128194 1000 0 1 (BSN.s_crit_mk qz12 Bool.false 128194 1000 qz13) (@Enclosure.Complex.IsNear.mk qz100 qz12 Bool.false 1 2 0 1 Bool.false 128194 1000 0 1 qz415 qz18))

noncomputable def ep718 := @ep714 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep715) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 128194 1000 0 1 ep717)

noncomputable def ep719 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 128194 1000 0 1 0 1 0

noncomputable def ep720 := @ep719 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep715) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 128194 1000 0 1 ep717)

noncomputable def ep721 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) 64097 6000 0 1 0 1 0 1 64097

noncomputable def ep722 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 128194 1000 0 1 64097 6000 0

noncomputable def ep723 := @ep722 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep715) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 128194 1000 0 1 ep717)

noncomputable def ep724 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep725 := @ep724 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep715) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 128194 1000 0 1 ep717)

noncomputable def ep726 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 64097 6000 0 1 (@ep713 1 24 0 1 (ep718 rfl) (ep720 rfl) rfl rfl) (@ep721 64097 6000 0 1 (ep723 rfl) (ep725 rfl) rfl rfl)

noncomputable def ep727 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 64097 6000 0 1 ep726

noncomputable abbrev qz143 := (@Enclosure.Complex.IsNear.re_isNear qz440 Bool.false 1 33 0 1 Bool.false 0 1 0 1 (@Enclosure.Complex.IsNear.of_eq qz440 (Complex.mk (Enclosure.sfrac Bool.false 1 33) qz277) Bool.false 1 33 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 33 1 33 EMRow43.d11 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 33) qz277 Bool.false 1 33 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 33) qz287)))

noncomputable def ep728 := @ep712 792 0 1 ep727 qz143

noncomputable def ep729 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz142 64097 6000 0 1 0 1 0 1 0

noncomputable def ep730 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 64097 6000 0 1 ep726

noncomputable abbrev qz144 := (@Enclosure.Complex.IsNear.im_isNear qz440 Bool.false 1 33 0 1 Bool.false 0 1 0 1 (@Enclosure.Complex.IsNear.of_eq qz440 (Complex.mk (Enclosure.sfrac Bool.false 1 33) qz277) Bool.false 1 33 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 33 1 33 EMRow43.d11 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 33) qz277 Bool.false 1 33 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 33) qz287)))

noncomputable def ep731 := @ep729 1 0 1 ep730 qz144

noncomputable def ep732 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz142) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz141) 0 1 0 1 5827 18000 0

noncomputable def ep733 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz142 1 24 0 1 0 1 0 1 0

noncomputable def ep734 := @ep733 1 0 1 ep727 qz144

noncomputable def ep735 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz141 64097 6000 0 1 1 33 0 1 5827

noncomputable def ep736 := @ep735 18000 0 1 ep730 qz143

noncomputable def ep737 := @ep708 1 (@ep709 0 1 0 1 (BSN.bern_sum_base qz5 33) qz121) (ep710 (@ep711 1 1 1 792 0 1 (ep728 rfl) (ep731 rfl) rfl rfl) (@ep732 1 5827 5827 18000 0 1 (ep734 rfl) (ep736 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep738 := ep702 (ep705 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep706 Bool.false 5827 18000 0 1 (BSN.bern_sum_succ qz5 33 0 1 1 rfl rfl) (ep737 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep739 := @Enclosure.Real.IsNear.mulLit_tf qz133 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz128 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))))) 162742589607 1099511627776 6230830142831 52911798063464448 4903350045743

noncomputable def ep740 := @ep739 73952782362000 0 1 265994628064605908797667 ep684 ep685 ep686 (@Enclosure.Complex.IsNear.im_isNear qz127 Bool.true 50370163883 549755813888 97101310415 826746844741632 Bool.true 162742589607 1099511627776 6230830142831 52911798063464448 (ep689 ep698))

noncomputable def ep741 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz128 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1))))) Bool.false 1627802699873 3253922423928 0 1 Bool.false

noncomputable def ep742 := nat_lit 40655972056703441043456000

noncomputable def ep743 := @Enclosure.Real.IsNear.addLit_tt (@HMul.hMul Real Real Real qz0 qz132 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz128 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz133 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz128 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1))))))) 246982545379790456500069 ep742 95224342973019098462669

noncomputable def ep744 := nat_lit 12228045895529623083338956800

noncomputable def ep745 := nat_lit 10142562128950372015560463

noncomputable def ep746 := nat_lit 172170886209057093013412511744

noncomputable def ep747 := nat_lit 3884641414151997206743852761310677457208233426944

noncomputable def ep748 := @Enclosure.Real.IsNear.mulLit_tf qz132 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz128 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))))) 50370163883 549755813888 97101310415 826746844741632 4903350045743

noncomputable def ep749 := @ep748 73952782362000 0 1 246982545379790456500069 ep742 95224342973019098462669 ep744 (@Enclosure.Complex.IsNear.re_isNear qz127 Bool.true 50370163883 549755813888 97101310415 826746844741632 Bool.true 162742589607 1099511627776 6230830142831 52911798063464448 (ep689 ep698))

noncomputable def ep750 := @Enclosure.Real.IsNear.mulLit_tf qz133 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz128 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))))) 162742589607 1099511627776 6230830142831 52911798063464448 1627802699873

noncomputable def ep751 := @ep750 3253922423928 0 1 88304275582199410006637 1192575180329967603941376 ep745 ep746 (@Enclosure.Complex.IsNear.im_isNear qz127 Bool.true 50370163883 549755813888 97101310415 826746844741632 Bool.true 162742589607 1099511627776 6230830142831 52911798063464448 (ep689 ep698))

noncomputable abbrev qz607 := (ep738 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep752 := @ep680 ep674 ep667 ep675 ep669 (@ep682 ep683 265994628064605908797667 ep684 ep685 ep686 ep687 ep672 ep542 ep673 ep544 (ep699 (@ep700 4903350045743 73952782362000 0 1 qz607) rfl) (ep740 (@ep741 4903350045743 73952782362000 0 1 qz607) rfl) rfl rfl) (@ep743 ep744 88304275582199410006637 1192575180329967603941376 ep745 ep746 ep747 ep674 ep667 ep675 ep669 (ep749 (@ep741 4903350045743 73952782362000 0 1 qz607) rfl) (ep751 (@ep700 4903350045743 73952782362000 0 1 qz607) rfl) rfl rfl)

noncomputable def ep753 := @ep678 ep668 ep669 (@ep679 26455899031732224 (BSN.head_sum_c_eq qz5 33) EMRow43.d9) ep752 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def ep754 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz5 1 33) Bool.false ep541 ep542 ep543 ep544 Bool.false ep666 ep667 ep668 ep669 (@ep670 ep544 Bool.false ep666 ep667 ep668 ep669 (BSN.zetaApproximant_eq_folded' qz5 1 33 rfl) (ep753 rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep755 := @Enclosure.Real.IsNear.mulLit_tf (Real.sin (@HSub.hSub Real Real Real qz404 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz82 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz83 (@Nat.cast Complex Complex.instNatCast j))))) qz84)) (Complex.im (zetaApproximant qz5 1 33)) 441 1048576 8648843

noncomputable def ep756 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz404 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz82 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz83 (@Nat.cast Complex Complex.instNatCast j))))) qz84)) Bool.true 441 1048576 34595372

noncomputable def ep757 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz404 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz82 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz83 (@Nat.cast Complex Complex.instNatCast j))))) qz84) qz405 Bool.false 67531293 524288 177

noncomputable def ep758 := BSN.sin_dyadic_bound_f 903185 2147483648 1 0 1048576 385360 0 1 1 0 1 1 441 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 903185) qz20 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 903185) qz21 0 0 rfl) rfl rfl

noncomputable def ep759 := @ep757 524288 Bool.true 441 1048576 1 192492 (@ep549 67531293 524288 177 524288 ep663 rfl) (Enclosure.sfrac_false_div 67531293 524288) (BSN.sin_reduce2 qz405 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 31778007611883913216) qz19) 226375608064910080 72057594037927936 Bool.false 441 1048576 20 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q2 67531293 524288 226375608064910080 72057594037927936 20 31778007611883913216 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 441 1048576 31778007611883913216 75557863725914323419136 903185 2147483648 385360 384984 (ep758 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep760 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz5 1 33) Bool.false ep541 ep542 ep543 ep544 Bool.false ep666 ep667 ep668 ep669 (@ep670 ep544 Bool.false ep666 ep667 ep668 ep669 (BSN.zetaApproximant_eq_folded' qz5 1 33 rfl) (ep753 rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow43.d12 : Enclosure.Real.IsNear (hardyZApproximantEM 1 33 qz12) Bool.true ep525 ep526 ep527 ep528 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 33 qz12) ep529 Bool.true ep525 ep526 ep527 ep528 (@Eq.refl Real ep529) (@ep530 Bool.true ep525 ep526 ep527 ep528 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz404 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz82 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz83 (@Nat.cast Complex Complex.instNatCast j))))) qz84) (zetaApproximant qz5 1 33)) (@ep532 ep533 ep534 ep528 ep535 ep536 ep537 ep538 ep539 ep525 ep526 ep527 ep528 (@ep540 25230311424 ep541 ep542 ep543 ep544 ep531 ep533 ep534 ep528 (@ep545 100921245696 1048575 1048576 8648843 25230311424 (ep665 rfl rfl) rfl) ep754 rfl) (@ep755 25230311424 ep666 ep667 ep668 ep669 ep535 ep536 ep537 ep538 (@ep756 100921245696 441 1048576 8648843 25230311424 (ep759 rfl rfl) rfl) ep760 rfl) rfl rfl))

noncomputable abbrev qz658 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 130272 1000)))

noncomputable abbrev qz608 := qz658

noncomputable abbrev qz441 := qz608

noncomputable abbrev qz145 := (BSN.headSumC qz441 9)

noncomputable abbrev qz146 := qz441

noncomputable abbrev qz609 := (@Neg.neg Complex Complex.instNeg qz658)

noncomputable abbrev qz442 := qz609

noncomputable abbrev qz147 := qz442

noncomputable abbrev qz610 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 8) qz147)

noncomputable def ep761 := @Enclosure.Complex.IsNear.of_eq qz145 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 8) qz610) Bool.false 637992116669 1099511627776 40665427686847 17637266021154816 Bool.true 354427700139 549755813888 20351436184799 8818633010577408

noncomputable def ep762 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 8) qz610 Bool.false 172362964115 549755813888 18199040831243 8818633010577408 Bool.true 453688825629 1099511627776 36437174878807 17637266021154816 Bool.false

noncomputable abbrev qz611 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 7) qz147)

noncomputable def ep763 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 8) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 7) qz611) Bool.false 172362964115 549755813888 18199040831243 8818633010577408 Bool.true 453688825629 1099511627776 36437174878807 17637266021154816

noncomputable def ep764 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 7) qz611 Bool.false 289549925415 549755813888 47760245436335 26455899031732224 Bool.true 110508630179 1099511627776 95624558929459 52911798063464448 Bool.true

noncomputable abbrev qz612 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 6) qz147)

noncomputable def ep765 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 7) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 6) qz612) Bool.false 289549925415 549755813888 47760245436335 26455899031732224 Bool.true 110508630179 1099511627776 95624558929459 52911798063464448

noncomputable def ep766 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 6) qz612 Bool.false 156837729993 549755813888 13455247192747 8818633010577408 Bool.false 251481821485 1099511627776 26941565208977 17637266021154816 Bool.false

noncomputable abbrev qz613 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 5) qz147)

noncomputable def ep767 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 6) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 5) qz613) Bool.false 156837729993 549755813888 13455247192747 8818633010577408 Bool.false 251481821485 1099511627776 26941565208977 17637266021154816

noncomputable def ep768 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 5) qz613 Bool.false 324161016711 549755813888 16132321463563 13227949515866112 Bool.false 611753926223 1099511627776 64619868595243 52911798063464448 Bool.true

noncomputable abbrev qz614 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 4) qz147)

noncomputable def ep769 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 5) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 4) qz614) Bool.false 324161016711 549755813888 16132321463563 13227949515866112 Bool.false 611753926223 1099511627776 64619868595243 52911798063464448

noncomputable def ep770 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 4) qz614 Bool.false 673800808761 1099511627776 46450756844885 52911798063464448 Bool.false 7823754045 137438953472 5811658978885 6613974757933056 Bool.true

noncomputable def ep771 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 4) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz147)) Bool.false 673800808761 1099511627776 46450756844885 52911798063464448 Bool.false 7823754045 137438953472 5811658978885 6613974757933056

noncomputable def ep772 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz147) Bool.false 281358742803 549755813888 1422136720113 2939544336859136 Bool.true 140604336015 274877906944 711114555463 1469772168429568 Bool.false

noncomputable def ep773 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 3) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz147)) Bool.false 281358742803 549755813888 1422136720113 2939544336859136 Bool.true 140604336015 274877906944 711114555463 1469772168429568

noncomputable def ep774 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz147) Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.true

noncomputable def ep775 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz10) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz146)

noncomputable abbrev qz659 := (Enclosure.sfrac Bool.false 130272 1000)

noncomputable abbrev qz615 := qz659

noncomputable abbrev qz443 := qz615

noncomputable abbrev qz148 := (@HMul.hMul Real Real Real qz267 qz443 qz279)

noncomputable abbrev qz149 := qz443

noncomputable abbrev qz444 := (@Eq.refl Real qz615)

noncomputable abbrev qz150 := qz444

noncomputable def ep776 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz9 qz147) (Complex.mk (@HMul.hMul Real Real Real qz0 qz281 (Real.cos qz148)) (@HMul.hMul Real Real Real qz0 qz281 (@Neg.neg Real Real.instNeg (Real.sin qz148)))) Bool.true 268397071085 549755813888 1422136720113 2939544336859136 Bool.true 140604336015 274877906944 711114555463 1469772168429568 (BSN.cpow_neg_s_mk qz149 130272 1000 2 qz150 rfl)

noncomputable def ep777 := nat_lit 7173791674376708010234701701066963216

noncomputable def ep778 := BSN.sin_dyadic_bound_f 1636579814 2147483648 2 1 1048576 385360 ep777 ep92 ep777 ep777 ep93 ep777 723974 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1636579814) qz20 0 1 ep777 ep92 ep777 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1636579814) qz21 0 1 ep777 ep93 ep777 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz151 := (Enclosure.Real.IsNear.const Bool.false 130272 1000)

noncomputable abbrev qz445 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 94683773) qz24)

noncomputable def ep779 := @Enclosure.Real.IsNear.cos_image qz148 qz445 Bool.false 94683773 1048576 711 1048576 Bool.true 723974 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz148 Bool.false 92464623 1024000 1357 2005125 94683773 1048576 711 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz149 qz279 130272 1000 0 1 363408 524288 1 192492 92464623 1024000 1357 2005125 qz151 qz285 rfl) rfl) (Enclosure.sfrac_false_div 94683773 1048576) (BSN.cos_reduce1 qz445 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 115164066297188498538496) qz25) 226375608064910080 72057594037927936 Bool.false 723974 1048576 14 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q1 94683773 1048576 226375608064910080 72057594037927936 14 115164066297188498538496 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 723974 1048576 115164066297188498538496 151115727451828646838272 1636579814 2147483648 385360 384984 (ep778 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep780 := nat_lit 256368518416223344748019237273646015576426772600520486687528460344378786324736

noncomputable def ep781 := nat_lit 51463286987356571850843528622950623392370313236168846482403744904297062656

noncomputable def ep782 := nat_lit 769002628674695321100356024763692145482495577175089122369620573543327764848896

noncomputable def ep783 := BSN.cos_dyadic_bound_f 1636579814 2147483648 3 2 1048576 385360 ep780 ep57 ep781 ep782 ep60 ep781 758532 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1636579814) qz15 0 2 ep780 ep57 ep781 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1636579814) qz16 0 2 ep782 ep60 ep781 rfl rfl rfl rfl) rfl rfl

noncomputable def ep784 := @Enclosure.Real.IsNear.sin_image qz148 qz445 Bool.false 94683773 1048576 711 1048576 Bool.false 758532 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz148 Bool.false 92464623 1024000 1357 2005125 94683773 1048576 711 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz149 qz279 130272 1000 0 1 363408 524288 1 192492 92464623 1024000 1357 2005125 qz151 qz285 rfl) rfl) (Enclosure.sfrac_false_div 94683773 1048576) (BSN.sin_reduce1 qz445 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 115164066297188498538496) qz25) 226375608064910080 72057594037927936 Bool.false 758532 1048576 14 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q1 94683773 1048576 226375608064910080 72057594037927936 14 115164066297188498538496 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 758532 1048576 115164066297188498538496 151115727451828646838272 1636579814 2147483648 385360 384984 (ep783 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep785 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz281 (Real.cos qz148)) (@HMul.hMul Real Real Real qz0 qz281 (@Neg.neg Real Real.instNeg (Real.sin qz148))) Bool.true 268397071085 549755813888 1422136720113 2939544336859136 Bool.true 140604336015 274877906944 711114555463 1469772168429568 (@Enclosure.Real.IsNear.mulLit_ft qz281 (Real.cos qz148) 741455 1048576 1 1048576 361987 524288 34477597 50460622848 268397071085 549755813888 1422136720113 2939544336859136 qz286 (@Enclosure.Real.IsNear.recentre' (Real.cos qz148) Bool.true 723974 1048576 137910388 201842491392 361987 524288 34477597 50460622848 (ep779 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz281 (@Neg.neg Real Real.instNeg (Real.sin qz148)) 741455 1048576 1 1048576 189633 262144 34477597 50460622848 140604336015 274877906944 711114555463 1469772168429568 qz286 (@Enclosure.Real.IsNear.neg (Real.sin qz148) Bool.false 189633 262144 34477597 50460622848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz148) Bool.false 758532 1048576 137910388 201842491392 189633 262144 34477597 50460622848 (ep784 rfl rfl) rfl)) rfl)

noncomputable def ep786 := @ep774 268397071085 549755813888 1422136720113 2939544336859136 Bool.true 140604336015 274877906944 711114555463 1469772168429568 Bool.false 281358742803 281358742803 549755813888 1422136720113 2939544336859136 Bool.true 140604336015 140604336015 274877906944 711114555463 1469772168429568 (ep775 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz10 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz22)) (ep776 ep785) rfl rfl

noncomputable abbrev qz152 := (@HMul.hMul Real Real Real qz267 qz443 qz288)

noncomputable def ep787 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz8 qz147) (Complex.mk (@HMul.hMul Real Real Real qz0 qz289 (Real.cos qz152)) (@HMul.hMul Real Real Real qz0 qz289 (@Neg.neg Real Real.instNeg (Real.sin qz152)))) Bool.false 111083323155 1099511627776 20852295882851 52911798063464448 Bool.false 156251844105 274877906944 5223286958603 13227949515866112 (BSN.cpow_neg_s_mk qz149 130272 1000 3 qz150 rfl)

noncomputable def ep788 := nat_lit 20357820324651621110333612664837136

noncomputable def ep789 := BSN.sin_dyadic_bound_f 377731166 2147483648 2 1 1048576 385360 ep788 ep92 ep788 ep788 ep93 ep788 183489 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 377731166) qz20 0 1 ep788 ep92 ep788 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 377731166) qz21 0 1 ep788 ep93 ep788 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz446 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 75035239) qz17)

noncomputable def ep790 := @Enclosure.Real.IsNear.cos_image qz152 qz446 Bool.false 75035239 524288 355 524288 Bool.false 183489 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz152 Bool.false 2344851219 16384000 1357 2005125 75035239 524288 355 524288 (@Enclosure.Real.IsNear.mulLit_ff qz149 qz288 130272 1000 0 1 575989 524288 1 192492 2344851219 16384000 1357 2005125 qz151 qz293 rfl) rfl) (Enclosure.sfrac_false_div 75035239 524288) (BSN.cos_reduce3 qz446 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13290233898458066976768) qz19) 226375608064910080 72057594037927936 Bool.false 183489 1048576 22 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q3 75035239 524288 226375608064910080 72057594037927936 22 13290233898458066976768 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 183489 1048576 13290233898458066976768 75557863725914323419136 377731166 2147483648 385360 384984 (ep789 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep791 := BSN.cos_dyadic_bound_f 377731166 2147483648 2 1 1048576 385360 ep788 ep96 ep788 ep788 ep97 ep788 1032396 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 377731166) qz15 0 1 ep788 ep96 ep788 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 377731166) qz16 0 1 ep788 ep97 ep788 rfl rfl rfl rfl) rfl rfl

noncomputable def ep792 := @Enclosure.Real.IsNear.sin_image qz152 qz446 Bool.false 75035239 524288 355 524288 Bool.true 1032396 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz152 Bool.false 2344851219 16384000 1357 2005125 75035239 524288 355 524288 (@Enclosure.Real.IsNear.mulLit_ff qz149 qz288 130272 1000 0 1 575989 524288 1 192492 2344851219 16384000 1357 2005125 qz151 qz293 rfl) rfl) (Enclosure.sfrac_false_div 75035239 524288) (BSN.sin_reduce3 qz446 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13290233898458066976768) qz19) 226375608064910080 72057594037927936 Bool.false 1032396 1048576 22 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q3 75035239 524288 226375608064910080 72057594037927936 22 13290233898458066976768 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1032396 1048576 13290233898458066976768 75557863725914323419136 377731166 2147483648 385360 384984 (ep791 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep793 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz289 (Real.cos qz152)) (@HMul.hMul Real Real Real qz0 qz289 (@Neg.neg Real Real.instNeg (Real.sin qz152))) Bool.false 111083323155 1099511627776 20852295882851 52911798063464448 Bool.false 156251844105 274877906944 5223286958603 13227949515866112 (@Enclosure.Real.IsNear.mulLit_ff qz289 (Real.cos qz152) 605395 1048576 1 1048576 183489 1048576 17214737 25230311424 111083323155 1099511627776 20852295882851 52911798063464448 qz294 (@Enclosure.Real.IsNear.recentre' (Real.cos qz152) Bool.false 183489 1048576 68858948 100921245696 183489 1048576 17214737 25230311424 (ep790 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz289 (@Neg.neg Real Real.instNeg (Real.sin qz152)) 605395 1048576 1 1048576 258099 262144 17214737 25230311424 156251844105 274877906944 5223286958603 13227949515866112 qz294 (@Enclosure.Real.IsNear.neg (Real.sin qz152) Bool.true 258099 262144 17214737 25230311424 (@Enclosure.Real.IsNear.recentre' (Real.sin qz152) Bool.true 1032396 1048576 68858948 100921245696 258099 262144 17214737 25230311424 (ep792 rfl rfl) rfl)) rfl)

noncomputable def ep794 := @ep772 111083323155 1099511627776 20852295882851 52911798063464448 Bool.false 156251844105 274877906944 5223286958603 13227949515866112 Bool.false 370425912018796195872768 673800808761 1099511627776 46450756844885 52911798063464448 Bool.false 4301154272668507176960 7823754045 137438953472 5811658978885 6613974757933056 (ep773 (BSN.head_sum_c_succ qz146 2 3 rfl rfl) (ep786 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep787 ep793) rfl rfl

noncomputable abbrev qz153 := (@HMul.hMul Real Real Real qz267 qz443 qz295)

noncomputable def ep795 := @Enclosure.Complex.IsNear.of_eq qz614 (Complex.mk (@HMul.hMul Real Real Real qz0 qz296 (Real.cos qz153)) (@HMul.hMul Real Real Real qz0 qz296 (@Neg.neg Real Real.instNeg (Real.sin qz153)))) Bool.true 25478775339 1099511627776 18078529009367 52911798063464448 Bool.false 549163893863 1099511627776 18126596764163 52911798063464448 (BSN.cpow_neg_s_mk qz149 130272 1000 4 qz150 rfl)

noncomputable def ep796 := nat_lit 4116954628064624453698687877334111275255071524513042215757053750298547910190625

noncomputable def ep797 := nat_lit 13191889340565136142537054767657356953217901643688899745690942982277625390625

noncomputable def ep798 := nat_lit 12324480105512743088810989522467019111858778770251748847779779364931088479790625

noncomputable def ep799 := BSN.cos_dyadic_bound_f 3273696205 2147483648 3 2 1048576 385360 ep796 ep57 ep797 ep798 ep60 ep797 48597 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3273696205) qz15 0 2 ep796 ep57 ep797 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3273696205) qz16 0 2 ep798 ep60 ep797 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz447 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 369859) (@Nat.cast Real Real.instNatCast 2048))

noncomputable def ep800 := @Enclosure.Real.IsNear.cos_image qz153 qz447 Bool.false 369859 2048 711 1048576 Bool.true 48597 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz153 Bool.false 2958872007 16384000 1357 2005125 369859 2048 711 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz149 qz295 130272 1000 0 1 726817 524288 1 192492 2958872007 16384000 1357 2005125 qz151 qz300 rfl) rfl) (Enclosure.sfrac_false_div 369859 2048) (BSN.cos_reduce2 qz447 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 449933380417290764288) (@Nat.cast Real Real.instNatCast 295147905179352825856)) 226375608064910080 72057594037927936 Bool.false 48597 1048576 28 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q2 369859 2048 226375608064910080 72057594037927936 28 449933380417290764288 295147905179352825856 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 48597 1048576 449933380417290764288 295147905179352825856 3273696205 2147483648 385360 384984 (ep799 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep801 := nat_lit 7399964819043871907743608535387274409896554422808524868566143996151564138030625

noncomputable def ep802 := nat_lit 19359501943325416204621533789723797257519099266599211675227829891758980396590625

noncomputable def ep803 := BSN.sin_dyadic_bound_f 3273696205 2147483648 3 2 1048576 385360 ep801 ep64 ep797 ep802 ep66 ep797 1047449 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3273696205) qz20 0 2 ep801 ep64 ep797 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3273696205) qz21 0 2 ep802 ep66 ep797 rfl rfl rfl rfl) rfl rfl

noncomputable def ep804 := @Enclosure.Real.IsNear.sin_image qz153 qz447 Bool.false 369859 2048 711 1048576 Bool.true 1047449 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz153 Bool.false 2958872007 16384000 1357 2005125 369859 2048 711 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz149 qz295 130272 1000 0 1 726817 524288 1 192492 2958872007 16384000 1357 2005125 qz151 qz300 rfl) rfl) (Enclosure.sfrac_false_div 369859 2048) (BSN.sin_reduce2 qz447 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 449933380417290764288) (@Nat.cast Real Real.instNatCast 295147905179352825856)) 226375608064910080 72057594037927936 Bool.false 1047449 1048576 28 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q2 369859 2048 226375608064910080 72057594037927936 28 449933380417290764288 295147905179352825856 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1047449 1048576 449933380417290764288 295147905179352825856 3273696205 2147483648 385360 384984 (ep803 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep805 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz296 (Real.cos qz153)) (@HMul.hMul Real Real Real qz0 qz296 (@Neg.neg Real Real.instNeg (Real.sin qz153))) Bool.true 25478775339 1099511627776 18078529009367 52911798063464448 Bool.false 549163893863 1099511627776 18126596764163 52911798063464448 (@Enclosure.Real.IsNear.mulLit_ft qz296 (Real.cos qz153) 524287 1048576 1 1048576 48597 1048576 34477597 50460622848 25478775339 1099511627776 18078529009367 52911798063464448 qz302 (@Enclosure.Real.IsNear.recentre' (Real.cos qz153) Bool.true 48597 1048576 137910388 201842491392 48597 1048576 34477597 50460622848 (ep800 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz296 (@Neg.neg Real Real.instNeg (Real.sin qz153)) 524287 1048576 1 1048576 1047449 1048576 34477597 50460622848 549163893863 1099511627776 18126596764163 52911798063464448 qz302 (@Enclosure.Real.IsNear.neg (Real.sin qz153) Bool.true 1047449 1048576 34477597 50460622848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz153) Bool.true 1047449 1048576 137910388 201842491392 1047449 1048576 34477597 50460622848 (ep804 rfl rfl) rfl)) rfl)

noncomputable def ep806 := @ep770 25478775339 1099511627776 18078529009367 52911798063464448 Bool.false 549163893863 1099511627776 18126596764163 52911798063464448 Bool.false 712837614290869495529472 324161016711 549755813888 16132321463563 13227949515866112 Bool.false 84078819402476217696256 611753926223 1099511627776 64619868595243 52911798063464448 (ep771 (BSN.head_sum_c_succ qz146 3 4 rfl rfl) (ep794 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep795 ep805) rfl rfl

noncomputable abbrev qz154 := (@HMul.hMul Real Real Real qz267 qz443 qz540)

noncomputable def ep807 := @Enclosure.Complex.IsNear.of_eq qz613 (Complex.mk (@HMul.hMul Real Real Real qz0 qz303 (Real.cos qz154)) (@HMul.hMul Real Real Real qz0 qz303 (@Neg.neg Real Real.instNeg (Real.sin qz154)))) Bool.true 83661643359 274877906944 8101098651115 26455899031732224 Bool.true 180136052369 549755813888 2025603378961 6613974757933056 (BSN.cpow_neg_s_mk qz149 130272 1000 5 qz150 rfl)

noncomputable def ep808 := nat_lit 6676942158607202929940826609372610816

noncomputable def ep809 := BSN.sin_dyadic_bound_f 1607475652 2147483648 2 1 1048576 385360 ep808 ep92 ep808 ep808 ep93 ep808 713628 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1607475652) qz20 0 1 ep808 ep92 ep808 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1607475652) qz21 0 1 ep808 ep93 ep808 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz448 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 219849111) qz24)

noncomputable def ep810 := @Enclosure.Real.IsNear.cos_image qz154 qz448 Bool.false 219849111 1048576 711 1048576 Bool.true 713628 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz154 Bool.false 107348199 512000 1357 2005125 219849111 1048576 711 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz149 qz540 130272 1000 0 1 843808 524288 1 192492 107348199 512000 1357 2005125 qz151 qz307 rfl) rfl) (Enclosure.sfrac_false_div 219849111 1048576) (BSN.cos_reduce1 qz448 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 113116042972650801201152) qz25) 226375608064910080 72057594037927936 Bool.false 713628 1048576 33 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q1 219849111 1048576 226375608064910080 72057594037927936 33 113116042972650801201152 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 713628 1048576 113116042972650801201152 151115727451828646838272 1607475652 2147483648 385360 384984 (ep809 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep811 := nat_lit 238609378116720594846161029758031342347891140276807079162802423125943674535936

noncomputable def ep812 := nat_lit 44581556589386214647134746665105090563423892844608123350126844708200185856

noncomputable def ep813 := nat_lit 715738971236983012109188819780763816862546573044732021241707015688414623236096

noncomputable def ep814 := BSN.cos_dyadic_bound_f 1607475652 2147483648 3 2 1048576 385360 ep811 ep57 ep812 ep813 ep60 ep812 768274 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1607475652) qz15 0 2 ep811 ep57 ep812 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1607475652) qz16 0 2 ep813 ep60 ep812 rfl rfl rfl rfl) rfl rfl

noncomputable def ep815 := @Enclosure.Real.IsNear.sin_image qz154 qz448 Bool.false 219849111 1048576 711 1048576 Bool.false 768274 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz154 Bool.false 107348199 512000 1357 2005125 219849111 1048576 711 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz149 qz540 130272 1000 0 1 843808 524288 1 192492 107348199 512000 1357 2005125 qz151 qz307 rfl) rfl) (Enclosure.sfrac_false_div 219849111 1048576) (BSN.sin_reduce1 qz448 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 113116042972650801201152) qz25) 226375608064910080 72057594037927936 Bool.false 768274 1048576 33 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q1 219849111 1048576 226375608064910080 72057594037927936 33 113116042972650801201152 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 768274 1048576 113116042972650801201152 151115727451828646838272 1607475652 2147483648 385360 384984 (ep814 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep816 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz303 (Real.cos qz154)) (@HMul.hMul Real Real Real qz0 qz303 (@Neg.neg Real Real.instNeg (Real.sin qz154))) Bool.true 83661643359 274877906944 8101098651115 26455899031732224 Bool.true 180136052369 549755813888 2025603378961 6613974757933056 (@Enclosure.Real.IsNear.mulLit_ft qz303 (Real.cos qz154) 468937 1048576 1 1048576 178407 262144 34477597 50460622848 83661643359 274877906944 8101098651115 26455899031732224 qz308 (@Enclosure.Real.IsNear.recentre' (Real.cos qz154) Bool.true 713628 1048576 137910388 201842491392 178407 262144 34477597 50460622848 (ep810 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz303 (@Neg.neg Real Real.instNeg (Real.sin qz154)) 468937 1048576 1 1048576 384137 524288 34477597 50460622848 180136052369 549755813888 2025603378961 6613974757933056 qz308 (@Enclosure.Real.IsNear.neg (Real.sin qz154) Bool.false 384137 524288 34477597 50460622848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz154) Bool.false 768274 1048576 137910388 201842491392 384137 524288 34477597 50460622848 (ep815 rfl rfl) rfl)) rfl)

noncomputable def ep817 := @ep768 83661643359 274877906944 8101098651115 26455899031732224 Bool.true 180136052369 549755813888 2025603378961 6613974757933056 Bool.false 43111226950324051771392 156837729993 549755813888 13455247192747 8818633010577408 Bool.false 138253593448522899783680 251481821485 1099511627776 26941565208977 17637266021154816 (ep769 (BSN.head_sum_c_succ qz146 4 5 rfl rfl) (ep806 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep807 ep816) rfl rfl

noncomputable abbrev qz155 := (@HMul.hMul Real Real Real qz267 qz443 qz541)

noncomputable def ep818 := @Enclosure.Complex.IsNear.of_eq qz612 (Complex.mk (@HMul.hMul Real Real Real qz0 qz309 (Real.cos qz155)) (@HMul.hMul Real Real Real qz0 qz309 (@Neg.neg Real Real.instNeg (Real.sin qz155)))) Bool.false 66356097711 274877906944 3697251929047 13227949515866112 Bool.true 22624403229 68719476736 115623932051 413373422370816 (BSN.cpow_neg_s_mk qz149 130272 1000 6 qz150 rfl)

noncomputable def ep819 := @Enclosure.Real.IsNear.mulLit_ff qz149 qz541 130272 1000 0 1 4034681531866359 2251799813685248 125000000048123 24061500000000000000 16425188516227947489 70368744177664000 169625000065302911 250640625000000000000 qz151 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 125000000048123 24061500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz311) Bool.false 33845361775666394038272 18889465931478580854784 1000000000384984 192492000000000000000 4034681531866359 2251799813685248 125000000048123 24061500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 212580 524288 24973259072661432 36028797018963968 192492 1000000000000000 rfl rfl rfl rfl (ep117 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep820 := nat_lit 588795640435092169811770877751466960759983167466102287426085288069542092800000

noncomputable def ep821 := nat_lit 271313466686994288252949187574657456274539798541335140554274705433600000000

noncomputable def ep822 := nat_lit 1765844294371902520858806734879251567367400422801224191997147314797759078400000

noncomputable def ep823 := BSN.cos_dyadic_bound_f 2014577220 2147483648 3 2 1048576 385360 ep820 ep57 ep821 ep822 ep60 ep821 620036 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2014577220) qz15 0 2 ep820 ep57 ep821 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2014577220) qz16 0 2 ep822 ep60 ep821 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz449 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 244754381) qz24)

noncomputable def ep824 := @Enclosure.Real.IsNear.cos_image qz155 qz449 Bool.false 244754381 1048576 711 1048576 Bool.false 620036 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz155 Bool.false 16425188516227947489 70368744177664000 169625000065302911 250640625000000000000 244754381 1048576 711 1048576 (ep819 rfl) rfl) (Enclosure.sfrac_false_div 244754381 1048576) (BSN.cos_reduce0 qz449 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 141763269068554493755392) qz25) 226375608064910080 72057594037927936 Bool.false 620036 1048576 37 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q0 244754381 1048576 226375608064910080 72057594037927936 37 141763269068554493755392 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 620036 1048576 141763269068554493755392 151115727451828646838272 2014577220 2147483648 385360 384984 (ep823 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep825 := nat_lit 1059615102009816310230585220602580803402950069600151049254510098760828887040000

noncomputable def ep826 := nat_lit 2774743140603454250327694612417352658745186641659900110200914766279087923200000

noncomputable def ep827 := BSN.sin_dyadic_bound_f 2014577220 2147483648 3 2 1048576 385360 ep825 ep64 ep821 ep826 ep66 ep821 845616 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2014577220) qz20 0 2 ep825 ep64 ep821 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2014577220) qz21 0 2 ep826 ep66 ep821 rfl rfl rfl rfl) rfl rfl

noncomputable def ep828 := @Enclosure.Real.IsNear.sin_image qz155 qz449 Bool.false 244754381 1048576 711 1048576 Bool.false 845616 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz155 Bool.false 16425188516227947489 70368744177664000 169625000065302911 250640625000000000000 244754381 1048576 711 1048576 (ep819 rfl) rfl) (Enclosure.sfrac_false_div 244754381 1048576) (BSN.sin_reduce0 qz449 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 141763269068554493755392) qz25) 226375608064910080 72057594037927936 Bool.false 845616 1048576 37 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q0 244754381 1048576 226375608064910080 72057594037927936 37 141763269068554493755392 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 845616 1048576 141763269068554493755392 151115727451828646838272 2014577220 2147483648 385360 384984 (ep827 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep829 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz309 (Real.cos qz155)) (@HMul.hMul Real Real Real qz0 qz309 (@Neg.neg Real Real.instNeg (Real.sin qz155))) Bool.false 66356097711 274877906944 3697251929047 13227949515866112 Bool.true 22624403229 68719476736 115623932051 413373422370816 (@Enclosure.Real.IsNear.mulLit_ff qz309 (Real.cos qz155) 428079 1048576 1 1048576 155009 262144 34477597 50460622848 66356097711 274877906944 3697251929047 13227949515866112 qz313 (@Enclosure.Real.IsNear.recentre' (Real.cos qz155) Bool.false 620036 1048576 137910388 201842491392 155009 262144 34477597 50460622848 (ep824 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz309 (@Neg.neg Real Real.instNeg (Real.sin qz155)) 428079 1048576 1 1048576 52851 65536 34477597 50460622848 22624403229 68719476736 115623932051 413373422370816 qz313 (@Enclosure.Real.IsNear.neg (Real.sin qz155) Bool.false 52851 65536 34477597 50460622848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz155) Bool.false 845616 1048576 137910388 201842491392 52851 65536 34477597 50460622848 (ep828 rfl rfl) rfl)) rfl)

noncomputable def ep830 := @ep766 66356097711 274877906944 3697251929047 13227949515866112 Bool.true 22624403229 68719476736 115623932051 413373422370816 Bool.false 79590877453866510581760 289549925415 549755813888 47760245436335 26455899031732224 Bool.true 7594095240713018015744 110508630179 1099511627776 95624558929459 52911798063464448 (ep767 (BSN.head_sum_c_succ qz146 5 6 rfl rfl) (ep817 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep818 ep829) rfl rfl

noncomputable abbrev qz156 := (@HMul.hMul Real Real Real qz267 qz443 qz542)

noncomputable def ep831 := @Enclosure.Complex.IsNear.of_eq qz611 (Complex.mk (@HMul.hMul Real Real Real qz0 qz314 (Real.cos qz156)) (@HMul.hMul Real Real Real qz0 qz314 (@Neg.neg Real Real.instNeg (Real.sin qz156)))) Bool.true 29296740325 137438953472 3418438528697 13227949515866112 Bool.true 171590097725 549755813888 6843482853481 26455899031732224 (BSN.cpow_neg_s_mk qz149 130272 1000 7 qz150 rfl)

noncomputable def ep832 := @Enclosure.Real.IsNear.mulLit_ff qz149 qz542 130272 1000 0 1 4381796493761783 2251799813685248 125000000048123 24061500000000000000 17838293526104218593 70368744177664000 169625000065302911 250640625000000000000 qz151 (BSN.isNear_log_sfrac 7 1 4381796493761783 2251799813685248 125000000048123 24061500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz316) Bool.false 36757173121942042968064 18889465931478580854784 1000000000384984 192492000000000000000 4381796493761783 2251799813685248 125000000048123 24061500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 293399 524288 24973259072661432 36028797018963968 192492 1000000000000000 rfl rfl rfl rfl (ep128 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep833 := nat_lit 2741411526009613906324810876143538176

noncomputable def ep834 := BSN.sin_dyadic_bound_f 1286748168 2147483648 2 1 1048576 385360 ep833 ep92 ep833 ep833 ep93 ep833 591368 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1286748168) qz20 0 1 ep833 ep92 ep833 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1286748168) qz21 0 1 ep833 ep93 ep833 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz450 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 265811287) qz24)

noncomputable def ep835 := @Enclosure.Real.IsNear.cos_image qz156 qz450 Bool.false 265811287 1048576 355 524288 Bool.true 591368 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz156 Bool.false 17838293526104218593 70368744177664000 169625000065302911 250640625000000000000 265811287 1048576 355 524288 (ep832 rfl) rfl) (Enclosure.sfrac_false_div 265811287 1048576) (BSN.cos_reduce1 qz450 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 90546852724647483408384) qz25) 226375608064910080 72057594037927936 Bool.false 591368 1048576 40 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q1 265811287 1048576 226375608064910080 72057594037927936 40 90546852724647483408384 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 591368 1048576 90546852724647483408384 151115727451828646838272 1286748168 2147483648 385360 384984 (ep834 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep836 := BSN.cos_dyadic_bound_f 1286748168 2147483648 2 1 1048576 385360 ep833 ep96 ep833 ep833 ep97 ep833 865906 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1286748168) qz15 0 1 ep833 ep96 ep833 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1286748168) qz16 0 1 ep833 ep97 ep833 rfl rfl rfl rfl) rfl rfl

noncomputable def ep837 := @Enclosure.Real.IsNear.sin_image qz156 qz450 Bool.false 265811287 1048576 355 524288 Bool.false 865906 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz156 Bool.false 17838293526104218593 70368744177664000 169625000065302911 250640625000000000000 265811287 1048576 355 524288 (ep832 rfl) rfl) (Enclosure.sfrac_false_div 265811287 1048576) (BSN.sin_reduce1 qz450 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 90546852724647483408384) qz25) 226375608064910080 72057594037927936 Bool.false 865906 1048576 40 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q1 265811287 1048576 226375608064910080 72057594037927936 40 90546852724647483408384 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 865906 1048576 90546852724647483408384 151115727451828646838272 1286748168 2147483648 385360 384984 (ep836 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep838 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz314 (Real.cos qz156)) (@HMul.hMul Real Real Real qz0 qz314 (@Neg.neg Real Real.instNeg (Real.sin qz156))) Bool.true 29296740325 137438953472 3418438528697 13227949515866112 Bool.true 171590097725 549755813888 6843482853481 26455899031732224 (@Enclosure.Real.IsNear.mulLit_ft qz314 (Real.cos qz156) 396325 1048576 1 1048576 73921 131072 17214737 25230311424 29296740325 137438953472 3418438528697 13227949515866112 qz318 (@Enclosure.Real.IsNear.recentre' (Real.cos qz156) Bool.true 591368 1048576 68858948 100921245696 73921 131072 17214737 25230311424 (ep835 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz314 (@Neg.neg Real Real.instNeg (Real.sin qz156)) 396325 1048576 1 1048576 432953 524288 17214737 25230311424 171590097725 549755813888 6843482853481 26455899031732224 qz318 (@Enclosure.Real.IsNear.neg (Real.sin qz156) Bool.false 432953 524288 17214737 25230311424 (@Enclosure.Real.IsNear.recentre' (Real.sin qz156) Bool.false 865906 1048576 68858948 100921245696 432953 524288 17214737 25230311424 (ep837 rfl rfl) rfl)) rfl)

noncomputable def ep839 := @ep764 29296740325 137438953472 3418438528697 13227949515866112 Bool.true 171590097725 549755813888 6843482853481 26455899031732224 Bool.false 23689385405297490657280 172362964115 549755813888 18199040831243 8818633010577408 Bool.true 249418069585561808535552 453688825629 1099511627776 36437174878807 17637266021154816 (ep765 (BSN.head_sum_c_succ qz146 6 7 rfl rfl) (ep830 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep831 ep838) rfl rfl

noncomputable abbrev qz157 := (@HMul.hMul Real Real Real qz267 qz443 qz543)

noncomputable def ep840 := @Enclosure.Complex.IsNear.of_eq qz610 (Complex.mk (@HMul.hMul Real Real Real qz0 qz319 (Real.cos qz157)) (@HMul.hMul Real Real Real qz0 qz319 (@Neg.neg Real Real.instNeg (Real.sin qz157)))) Bool.false 293266188439 1099511627776 1422448674787 5879088673718272 Bool.true 255166574649 1099511627776 1421899163597 5879088673718272 (BSN.cpow_neg_s_mk qz149 130272 1000 8 qz150 rfl)

noncomputable def ep841 := @Enclosure.Real.IsNear.mulLit_ff qz149 qz543 130272 1000 0 1 9364972152248037 4503599627370496 250000000144369 48123000000000000000 38124801631801758627 140737488355328000 339250000195908733 501281250000000000000 qz151 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 250000000144369 48123000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz321) Bool.false 39279540158062550581248 18889465931478580854784 1000000000577476 192492000000000000000 9364972152248037 4503599627370496 250000000144369 48123000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 524288 24973259072661432 36028797018963968 192492 1000000000000000 rfl rfl rfl rfl (ep143 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep842 := nat_lit 199786136367826746535059932482945338678611985586102077441784891817209121846401

noncomputable def ep843 := nat_lit 31256281391515484543478755755830163219935496071303952737528673716234990721

noncomputable def ep844 := nat_lit 599295896540697208636092839937324355709396085766163624419879618104194895557761

noncomputable def ep845 := BSN.cos_dyadic_bound_f 1537684241 2147483648 3 2 1048576 385360 ep842 ep57 ep843 ep844 ep60 ep843 791057 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1537684241) qz15 0 2 ep842 ep57 ep843 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1537684241) qz16 0 2 ep844 ep60 ep843 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz451 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 284051907) qz24)

noncomputable def ep846 := @Enclosure.Real.IsNear.cos_image qz157 qz451 Bool.false 284051907 1048576 355 524288 Bool.false 791057 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz157 Bool.false 38124801631801758627 140737488355328000 339250000195908733 501281250000000000000 284051907 1048576 355 524288 (ep841 rfl) rfl) (Enclosure.sfrac_false_div 284051907 1048576) (BSN.cos_reduce0 qz451 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 108204909019882946822144) qz25) 226375608064910080 72057594037927936 Bool.false 791057 1048576 43 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q0 284051907 1048576 226375608064910080 72057594037927936 43 108204909019882946822144 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 791057 1048576 108204909019882946822144 151115727451828646838272 1537684241 2147483648 385360 384984 (ep845 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep847 := nat_lit 5590731740256858768849887557714858561

noncomputable def ep848 := BSN.sin_dyadic_bound_f 1537684241 2147483648 2 1 1048576 385360 ep847 ep92 ep847 ep847 ep93 ep847 688287 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1537684241) qz20 0 1 ep847 ep92 ep847 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1537684241) qz21 0 1 ep847 ep93 ep847 rfl rfl rfl rfl) rfl rfl

noncomputable def ep849 := @Enclosure.Real.IsNear.sin_image qz157 qz451 Bool.false 284051907 1048576 355 524288 Bool.false 688287 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz157 Bool.false 38124801631801758627 140737488355328000 339250000195908733 501281250000000000000 284051907 1048576 355 524288 (ep841 rfl) rfl) (Enclosure.sfrac_false_div 284051907 1048576) (BSN.sin_reduce0 qz451 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 108204909019882946822144) qz25) 226375608064910080 72057594037927936 Bool.false 688287 1048576 43 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q0 284051907 1048576 226375608064910080 72057594037927936 43 108204909019882946822144 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 688287 1048576 108204909019882946822144 151115727451828646838272 1537684241 2147483648 385360 384984 (ep848 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep850 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz319 (Real.cos qz157)) (@HMul.hMul Real Real Real qz0 qz319 (@Neg.neg Real Real.instNeg (Real.sin qz157))) Bool.false 293266188439 1099511627776 1422448674787 5879088673718272 Bool.true 255166574649 1099511627776 1421899163597 5879088673718272 (@Enclosure.Real.IsNear.mulLit_ff qz319 (Real.cos qz157) 370727 1048576 1 1048576 791057 1048576 17214737 25230311424 293266188439 1099511627776 1422448674787 5879088673718272 qz323 (@Enclosure.Real.IsNear.recentre' (Real.cos qz157) Bool.false 791057 1048576 68858948 100921245696 791057 1048576 17214737 25230311424 (ep846 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz319 (@Neg.neg Real Real.instNeg (Real.sin qz157)) 370727 1048576 1 1048576 688287 1048576 17214737 25230311424 255166574649 1099511627776 1421899163597 5879088673718272 qz323 (@Enclosure.Real.IsNear.neg (Real.sin qz157) Bool.false 688287 1048576 17214737 25230311424 (@Enclosure.Real.IsNear.recentre' (Real.sin qz157) Bool.false 688287 1048576 68858948 100921245696 688287 1048576 17214737 25230311424 (ep849 rfl rfl) rfl)) rfl)

noncomputable def ep851 := @ep762 293266188439 1099511627776 1422448674787 5879088673718272 Bool.true 255166574649 1099511627776 1421899163597 5879088673718272 Bool.false 350739875353493946499072 637992116669 1099511627776 40665427686847 17637266021154816 Bool.true 779394755017471822921728 354427700139 549755813888 20351436184799 8818633010577408 (ep763 (BSN.head_sum_c_succ qz146 7 8 rfl rfl) (ep839 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep840 ep850) rfl rfl

theorem EMRow43.d13 : Enclosure.Complex.IsNear qz145 Bool.false 637992116669 1099511627776 40665427686847 17637266021154816 Bool.true 354427700139 549755813888 20351436184799 8818633010577408 := ep761 (BSN.head_sum_c_succ qz146 8 9 rfl rfl) (ep851 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz158 := (BSN.headSumC qz441 17)

noncomputable abbrev qz616 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 16) qz147)

noncomputable def ep852 := @Enclosure.Complex.IsNear.of_eq qz158 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 16) qz616) Bool.true 144940736397 1099511627776 205072673922983 52911798063464448 Bool.true 110863325915 1099511627776 205225125565817 52911798063464448

noncomputable def ep853 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 16) qz616 Bool.false 32190364797 274877906944 97992166875665 26455899031732224 Bool.true 42739878541 549755813888 49045592644909 13227949515866112 Bool.true

noncomputable abbrev qz617 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 15) qz147)

noncomputable def ep854 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 16) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 15) qz617) Bool.false 32190364797 274877906944 97992166875665 26455899031732224 Bool.true 42739878541 549755813888 49045592644909 13227949515866112

noncomputable def ep855 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 15) qz617 Bool.true 1319041137 34359738368 7775808787285 2204658252644352 Bool.false 141156180313 1099511627776 62269184496659 17637266021154816 Bool.false

noncomputable abbrev qz618 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 14) qz147)

noncomputable def ep856 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 15) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 14) qz618) Bool.true 1319041137 34359738368 7775808787285 2204658252644352 Bool.false 141156180313 1099511627776 62269184496659 17637266021154816

noncomputable def ep857 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 14) qz618 Bool.false 18854792587 1099511627776 176960271525853 52911798063464448 Bool.true 146285141385 1099511627776 177109540890943 52911798063464448 Bool.true

noncomputable abbrev qz619 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 13) qz147)

noncomputable def ep858 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 14) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 13) qz619) Bool.false 18854792587 1099511627776 176960271525853 52911798063464448 Bool.true 146285141385 1099511627776 177109540890943 52911798063464448

noncomputable def ep859 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 13) qz619 Bool.true 27673587131 274877906944 27818653688119 8818633010577408 Bool.false 32444720547 274877906944 27839491235857 8818633010577408 Bool.false

noncomputable abbrev qz620 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 12) qz147)

noncomputable def ep860 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 13) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 12) qz620) Bool.true 27673587131 274877906944 27818653688119 8818633010577408 Bool.false 32444720547 274877906944 27839491235857 8818633010577408

noncomputable def ep861 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 12) qz620 Bool.false 204044846227 1099511627776 156425584994699 52911798063464448 Bool.false 88761319809 1099511627776 156594126755075 52911798063464448 Bool.true

noncomputable abbrev qz621 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 11) qz147)

noncomputable def ep862 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 12) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 11) qz621) Bool.false 204044846227 1099511627776 156425584994699 52911798063464448 Bool.false 88761319809 1099511627776 156594126755075 52911798063464448

noncomputable def ep863 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 11) qz621 Bool.false 273143487833 1099511627776 145529913687173 52911798063464448 Bool.true 58867977689 274877906944 36414905203037 13227949515866112 Bool.true

noncomputable abbrev qz622 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 10) qz147)

noncomputable def ep864 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 11) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 10) qz622) Bool.false 273143487833 1099511627776 145529913687173 52911798063464448 Bool.true 58867977689 274877906944 36414905203037 13227949515866112

noncomputable def ep865 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 10) qz622 Bool.false 293942076269 1099511627776 134094468830891 52911798063464448 Bool.true 291272726939 549755813888 16772103021883 6613974757933056 Bool.true

noncomputable abbrev qz623 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 9) qz147)

noncomputable def ep866 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 10) (@HAdd.hAdd Complex Complex Complex qz4 qz145 qz623) Bool.false 293942076269 1099511627776 134094468830891 52911798063464448 Bool.true 291272726939 549755813888 16772103021883 6613974757933056

noncomputable def ep867 := @Enclosure.Complex.IsNear.addLitP qz145 qz623 Bool.false 637992116669 1099511627776 40665427686847 17637266021154816 Bool.true 354427700139 549755813888 20351436184799 8818633010577408 Bool.true

noncomputable abbrev qz159 := (@HMul.hMul Real Real Real qz267 qz443 qz552)

noncomputable def ep868 := @Enclosure.Complex.IsNear.of_eq qz623 (Complex.mk (@HMul.hMul Real Real Real qz0 qz324 (Real.cos qz159)) (@HMul.hMul Real Real Real qz0 qz324 (@Neg.neg Real Real.instNeg (Real.sin qz159)))) Bool.true 21503127525 68719476736 6049092885175 26455899031732224 Bool.false 3947185825 34359738368 6034103533135 26455899031732224 (BSN.cpow_neg_s_mk qz149 130272 1000 9 qz150 rfl)

noncomputable def ep869 := @Enclosure.Real.IsNear.mulLit_ff qz149 qz552 130272 1000 0 1 9895417793173221 4503599627370496 250000000144369 48123000000000000000 40284245836008182691 140737488355328000 339250000195908733 501281250000000000000 qz151 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 250000000144369 48123000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz326) Bool.false 41504390431577613533184 18889465931478580854784 1000000000577476 192492000000000000000 9895417793173221 4503599627370496 250000000144369 48123000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 61752 524288 24973259072661432 36028797018963968 192492 1000000000000000 rfl rfl rfl rfl (ep174 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep870 := nat_lit 325951236035398044113056662957670656

noncomputable def ep871 := BSN.cos_dyadic_bound_f 755593404 2147483648 2 1 1048576 385360 ep870 ep96 ep870 ep870 ep97 ep870 984336 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 755593404) qz15 0 1 ep870 ep96 ep870 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 755593404) qz16 0 1 ep870 ep97 ep870 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz452 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 75035255) (@Nat.cast Real Real.instNatCast 262144))

noncomputable def ep872 := @Enclosure.Real.IsNear.cos_image qz159 qz452 Bool.false 75035255 262144 711 1048576 Bool.true 984336 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz159 Bool.false 40284245836008182691 140737488355328000 339250000195908733 501281250000000000000 75035255 262144 711 1048576 (ep869 rfl) rfl) (Enclosure.sfrac_false_div 75035255 262144) (BSN.cos_reduce2 qz452 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13292539741467280670720) qz301) 226375608064910080 72057594037927936 Bool.false 984336 1048576 45 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q2 75035255 262144 226375608064910080 72057594037927936 45 13292539741467280670720 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 984336 1048576 13292539741467280670720 37778931862957161709568 755593404 2147483648 385360 384984 (ep871 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep873 := BSN.sin_dyadic_bound_f 755593404 2147483648 2 1 1048576 385360 ep870 ep92 ep870 ep870 ep93 ep870 361376 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 755593404) qz20 0 1 ep870 ep92 ep870 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 755593404) qz21 0 1 ep870 ep93 ep870 rfl rfl rfl rfl) rfl rfl

noncomputable def ep874 := @Enclosure.Real.IsNear.sin_image qz159 qz452 Bool.false 75035255 262144 711 1048576 Bool.true 361376 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz159 Bool.false 40284245836008182691 140737488355328000 339250000195908733 501281250000000000000 75035255 262144 711 1048576 (ep869 rfl) rfl) (Enclosure.sfrac_false_div 75035255 262144) (BSN.sin_reduce2 qz452 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13292539741467280670720) qz301) 226375608064910080 72057594037927936 Bool.false 361376 1048576 45 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q2 75035255 262144 226375608064910080 72057594037927936 45 13292539741467280670720 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 361376 1048576 13292539741467280670720 37778931862957161709568 755593404 2147483648 385360 384984 (ep873 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep875 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz324 (Real.cos qz159)) (@HMul.hMul Real Real Real qz0 qz324 (@Neg.neg Real Real.instNeg (Real.sin qz159))) Bool.true 21503127525 68719476736 6049092885175 26455899031732224 Bool.false 3947185825 34359738368 6034103533135 26455899031732224 (@Enclosure.Real.IsNear.mulLit_ft qz324 (Real.cos qz159) 349525 1048576 1 1048576 61521 65536 34477597 50460622848 21503127525 68719476736 6049092885175 26455899031732224 qz328 (@Enclosure.Real.IsNear.recentre' (Real.cos qz159) Bool.true 984336 1048576 137910388 201842491392 61521 65536 34477597 50460622848 (ep872 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz324 (@Neg.neg Real Real.instNeg (Real.sin qz159)) 349525 1048576 1 1048576 11293 32768 34477597 50460622848 3947185825 34359738368 6034103533135 26455899031732224 qz328 (@Enclosure.Real.IsNear.neg (Real.sin qz159) Bool.true 11293 32768 34477597 50460622848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz159) Bool.true 361376 1048576 137910388 201842491392 11293 32768 34477597 50460622848 (ep874 rfl rfl) rfl)) rfl)

noncomputable def ep876 := @ep867 21503127525 68719476736 6049092885175 26455899031732224 Bool.false 3947185825 34359738368 6034103533135 26455899031732224 Bool.false 20199545671899083177984 293942076269 1099511627776 134094468830891 52911798063464448 Bool.true 10008054691357945495552 291272726939 549755813888 16772103021883 6613974757933056 EMRow43.d13 (ep868 ep875) rfl rfl

noncomputable abbrev qz160 := (@HMul.hMul Real Real Real qz267 qz443 qz553)

noncomputable def ep877 := @Enclosure.Complex.IsNear.of_eq qz622 (Complex.mk (@HMul.hMul Real Real Real qz0 qz33 (Real.cos qz160)) (@HMul.hMul Real Real Real qz0 qz33 (@Neg.neg Real Real.instNeg (Real.sin qz160)))) Bool.true 5199647109 274877906944 1905907476047 8818633010577408 Bool.false 173536771561 549755813888 956899719757 4409316505288704 (BSN.cpow_neg_s_mk qz149 130272 1000 10 qz150 rfl)

noncomputable def ep878 := @Enclosure.Real.IsNear.mulLit_ff qz149 qz553 130272 1000 0 1 10369917190100709 4503599627370496 250000000144369 48123000000000000000 42215932880899986339 140737488355328000 339250000195908733 501281250000000000000 qz151 (BSN.isNear_log_sfrac 10 1 10369917190100709 4503599627370496 250000000144369 48123000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz329) Bool.false 43494585150108164161536 18889465931478580854784 1000000000577476 192492000000000000000 10369917190100709 4503599627370496 250000000144369 48123000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 116991 524288 24973259072661432 36028797018963968 192492 1000000000000000 rfl rfl rfl rfl (ep185 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep879 := nat_lit 3972688697766373587816199880557886431742976168791583816430970706364640879190625

noncomputable def ep880 := nat_lit 12286300729935418217494114873446194864665730537826391734191076529529250390625

noncomputable def ep881 := nat_lit 11893493491839249927013611411926766905499597045299098665824529966034864136790625

noncomputable def ep882 := BSN.cos_dyadic_bound_f 3244723115 2147483648 3 2 1048576 385360 ep879 ep57 ep880 ep881 ep60 ep880 62724 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3244723115) qz15 0 2 ep879 ep57 ep880 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3244723115) qz16 0 2 ep881 ep60 ep880 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz453 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 157266605) qz17)

noncomputable def ep883 := @Enclosure.Real.IsNear.cos_image qz160 qz453 Bool.false 157266605 524288 711 1048576 Bool.true 62724 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz160 Bool.false 42215932880899986339 140737488355328000 339250000195908733 501281250000000000000 157266605 524288 711 1048576 (ep878 rfl) rfl) (Enclosure.sfrac_false_div 157266605 524288) (BSN.cos_reduce2 qz453 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 114163545410576014376960) qz19) 226375608064910080 72057594037927936 Bool.false 62724 1048576 47 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q2 157266605 524288 226375608064910080 72057594037927936 47 114163545410576014376960 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 62724 1048576 114163545410576014376960 75557863725914323419136 3244723115 2147483648 385360 384984 (ep882 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep884 := nat_lit 7141010615395524123495164493105438621245624519394589756188394410232730182230625

noncomputable def ep885 := nat_lit 18682754743901715360611392724528664454433843510876968536733295045752198357590625

noncomputable def ep886 := BSN.sin_dyadic_bound_f 3244723115 2147483648 3 2 1048576 385360 ep884 ep64 ep880 ep885 ep66 ep880 1046698 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3244723115) qz20 0 2 ep884 ep64 ep880 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3244723115) qz21 0 2 ep885 ep66 ep880 rfl rfl rfl rfl) rfl rfl

noncomputable def ep887 := @Enclosure.Real.IsNear.sin_image qz160 qz453 Bool.false 157266605 524288 711 1048576 Bool.true 1046698 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz160 Bool.false 42215932880899986339 140737488355328000 339250000195908733 501281250000000000000 157266605 524288 711 1048576 (ep878 rfl) rfl) (Enclosure.sfrac_false_div 157266605 524288) (BSN.sin_reduce2 qz453 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 114163545410576014376960) qz19) 226375608064910080 72057594037927936 Bool.false 1046698 1048576 47 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q2 157266605 524288 226375608064910080 72057594037927936 47 114163545410576014376960 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1046698 1048576 114163545410576014376960 75557863725914323419136 3244723115 2147483648 385360 384984 (ep886 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep888 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz33 (Real.cos qz160)) (@HMul.hMul Real Real Real qz0 qz33 (@Neg.neg Real Real.instNeg (Real.sin qz160))) Bool.true 5199647109 274877906944 1905907476047 8818633010577408 Bool.false 173536771561 549755813888 956899719757 4409316505288704 (@Enclosure.Real.IsNear.mulLit_ft qz33 (Real.cos qz160) 331589 1048576 1 1048576 15681 262144 34477597 50460622848 5199647109 274877906944 1905907476047 8818633010577408 qz331 (@Enclosure.Real.IsNear.recentre' (Real.cos qz160) Bool.true 62724 1048576 137910388 201842491392 15681 262144 34477597 50460622848 (ep883 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz33 (@Neg.neg Real Real.instNeg (Real.sin qz160)) 331589 1048576 1 1048576 523349 524288 34477597 50460622848 173536771561 549755813888 956899719757 4409316505288704 qz331 (@Enclosure.Real.IsNear.neg (Real.sin qz160) Bool.true 523349 524288 34477597 50460622848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz160) Bool.true 1046698 1048576 137910388 201842491392 523349 524288 34477597 50460622848 (ep887 rfl rfl) rfl)) rfl)

noncomputable def ep889 := @ep865 5199647109 274877906944 1905907476047 8818633010577408 Bool.false 173536771561 549755813888 956899719757 4409316505288704 Bool.false 75081110230918970212352 273143487833 1099511627776 145529913687173 52911798063464448 Bool.true 64726025972713640689664 58867977689 274877906944 36414905203037 13227949515866112 (ep866 (BSN.head_sum_c_succ qz146 9 10 rfl rfl) (ep876 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep877 ep888) rfl rfl

noncomputable abbrev qz161 := (@HMul.hMul Real Real Real qz267 qz443 qz554)

noncomputable def ep890 := @Enclosure.Complex.IsNear.of_eq qz621 (Complex.mk (@HMul.hMul Real Real Real qz0 qz35 (Real.cos qz161)) (@HMul.hMul Real Real Real qz0 qz35 (@Neg.neg Real Real.instNeg (Real.sin qz161)))) Bool.true 34549320803 549755813888 1815945217921 8818633010577408 Bool.false 324233230565 1099511627776 3644835314309 17637266021154816 (BSN.cpow_neg_s_mk qz149 130272 1000 11 qz150 rfl)

noncomputable def ep891 := @Enclosure.Real.IsNear.mulLit_ff qz149 qz554 130272 1000 0 1 10799156221662949 4503599627370496 250000000144369 48123000000000000000 43963364978389865379 140737488355328000 339250000195908733 501281250000000000000 qz151 (BSN.isNear_log_sfrac 11 1 10799156221662949 4503599627370496 250000000144369 48123000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz332) Bool.false 45294944137145793642496 18889465931478580854784 1000000000577476 192492000000000000000 10799156221662949 4503599627370496 250000000144369 48123000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 166961 524288 24973259072661432 36028797018963968 192492 1000000000000000 rfl rfl rfl rfl (ep200 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep892 := nat_lit 2611204987368270322019119452812176632277997371946113182124349651102945437163776

noncomputable def ep893 := nat_lit 5319284733454303091656813461861444751125487096769708099508621683497370788096

noncomputable def ep894 := nat_lit 7822976392637902359874044731512807007331741141644800130174031709941841569915136

noncomputable def ep895 := BSN.cos_dyadic_bound_f 2922346138 2147483648 3 2 1048576 385360 ep892 ep57 ep893 ep894 ep60 ep893 218558 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2922346138) qz15 0 2 ep892 ep57 ep893 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2922346138) qz16 0 2 ep894 ep60 ep893 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz454 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 163776297) qz17)

noncomputable def ep896 := @Enclosure.Real.IsNear.cos_image qz161 qz454 Bool.false 163776297 524288 355 524288 Bool.true 218558 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz161 Bool.false 43963364978389865379 140737488355328000 339250000195908733 501281250000000000000 163776297 524288 355 524288 (ep891 rfl) rfl) (Enclosure.sfrac_false_div 163776297 524288) (BSN.cos_reduce2 qz454 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 102820913897385769304064) qz19) 226375608064910080 72057594037927936 Bool.false 218558 1048576 49 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q2 163776297 524288 226375608064910080 72057594037927936 49 102820913897385769304064 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 218558 1048576 102820913897385769304064 75557863725914323419136 2922346138 2147483648 385360 384984 (ep895 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep897 := nat_lit 4695913549476123137161089564292428782299494879825587961344222474638503890264320

noncomputable def ep898 := nat_lit 12290209025726158392321123541827633043092092944243674657073759188946609683702016

noncomputable def ep899 := BSN.sin_dyadic_bound_f 2922346138 2147483648 3 2 1048576 385360 ep897 ep64 ep893 ep898 ep66 ep893 1025545 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2922346138) qz20 0 2 ep897 ep64 ep893 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2922346138) qz21 0 2 ep898 ep66 ep893 rfl rfl rfl rfl) rfl rfl

noncomputable def ep900 := @Enclosure.Real.IsNear.sin_image qz161 qz454 Bool.false 163776297 524288 355 524288 Bool.true 1025545 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz161 Bool.false 43963364978389865379 140737488355328000 339250000195908733 501281250000000000000 163776297 524288 355 524288 (ep891 rfl) rfl) (Enclosure.sfrac_false_div 163776297 524288) (BSN.sin_reduce2 qz454 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 102820913897385769304064) qz19) 226375608064910080 72057594037927936 Bool.false 1025545 1048576 49 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q2 163776297 524288 226375608064910080 72057594037927936 49 102820913897385769304064 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1025545 1048576 102820913897385769304064 75557863725914323419136 2922346138 2147483648 385360 384984 (ep899 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep901 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz35 (Real.cos qz161)) (@HMul.hMul Real Real Real qz0 qz35 (@Neg.neg Real Real.instNeg (Real.sin qz161))) Bool.true 34549320803 549755813888 1815945217921 8818633010577408 Bool.false 324233230565 1099511627776 3644835314309 17637266021154816 (@Enclosure.Real.IsNear.mulLit_ft qz35 (Real.cos qz161) 316157 1048576 1 1048576 109279 524288 17214737 25230311424 34549320803 549755813888 1815945217921 8818633010577408 qz334 (@Enclosure.Real.IsNear.recentre' (Real.cos qz161) Bool.true 218558 1048576 68858948 100921245696 109279 524288 17214737 25230311424 (ep896 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz35 (@Neg.neg Real Real.instNeg (Real.sin qz161)) 316157 1048576 1 1048576 1025545 1048576 17214737 25230311424 324233230565 1099511627776 3644835314309 17637266021154816 qz334 (@Enclosure.Real.IsNear.neg (Real.sin qz161) Bool.true 1025545 1048576 17214737 25230311424 (@Enclosure.Real.IsNear.recentre' (Real.sin qz161) Bool.true 1025545 1048576 68858948 100921245696 1025545 1048576 17214737 25230311424 (ep900 rfl rfl) rfl)) rfl)

noncomputable def ep902 := @ep863 34549320803 549755813888 1815945217921 8818633010577408 Bool.false 324233230565 1099511627776 3644835314309 17637266021154816 Bool.false 112174840507176191000576 204044846227 1099511627776 156425584994699 52911798063464448 Bool.false 24398525806684925853696 88761319809 1099511627776 156594126755075 52911798063464448 (ep864 (BSN.head_sum_c_succ qz146 10 11 rfl rfl) (ep889 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep890 ep901) rfl rfl

noncomputable abbrev qz162 := (@HMul.hMul Real Real Real qz267 qz443 qz555)

noncomputable def ep903 := @Enclosure.Complex.IsNear.of_eq qz620 (Complex.mk (@HMul.hMul Real Real Real qz0 qz37 (Real.cos qz162)) (@HMul.hMul Real Real Real qz0 qz37 (@Neg.neg Real Real.instNeg (Real.sin qz162)))) Bool.true 314739194751 1099511627776 10486337134015 52911798063464448 Bool.false 41017562379 1099511627776 10442820660067 52911798063464448 (BSN.cpow_neg_s_mk qz149 130272 1000 12 qz150 rfl)

noncomputable def ep904 := @Enclosure.Real.IsNear.mulLit_ff qz149 qz555 130272 1000 0 1 11191020447815397 4503599627370496 250000000144369 48123000000000000000 45558644243056481187 140737488355328000 339250000195908733 501281250000000000000 qz151 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 250000000144369 48123000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz335) Bool.false 46938541828353910898688 18889465931478580854784 1000000000577476 192492000000000000000 11191020447815397 4503599627370496 250000000144369 48123000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 212580 524288 24973259072661432 36028797018963968 192492 1000000000000000 rfl rfl rfl rfl (ep215 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep905 := nat_lit 5998555609622013316897718466031521

noncomputable def ep906 := BSN.cos_dyadic_bound_f 278299017 2147483648 2 1 1048576 385360 ep905 ep96 ep905 ep905 ep97 ep905 1039783 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 278299017) qz15 0 1 ep905 ep96 ep905 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 278299017) qz16 0 1 ep905 ep97 ep905 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz455 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 169719175) qz17)

noncomputable def ep907 := @Enclosure.Real.IsNear.cos_image qz162 qz455 Bool.false 169719175 524288 711 1048576 Bool.true 1039783 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz162 Bool.false 45558644243056481187 140737488355328000 339250000195908733 501281250000000000000 169719175 524288 711 1048576 (ep904 rfl) rfl) (Enclosure.sfrac_false_div 169719175 524288) (BSN.cos_reduce2 qz455 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9791776170167353999360) qz19) 226375608064910080 72057594037927936 Bool.false 1039783 1048576 51 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q2 169719175 524288 226375608064910080 72057594037927936 51 9791776170167353999360 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1039783 1048576 9791776170167353999360 75557863725914323419136 278299017 2147483648 385360 384984 (ep906 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep908 := BSN.sin_dyadic_bound_f 278299017 2147483648 1 0 1048576 385360 0 1 1 0 1 1 135507 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 278299017) qz20 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 278299017) qz21 0 0 rfl) rfl rfl

noncomputable def ep909 := @Enclosure.Real.IsNear.sin_image qz162 qz455 Bool.false 169719175 524288 711 1048576 Bool.true 135507 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz162 Bool.false 45558644243056481187 140737488355328000 339250000195908733 501281250000000000000 169719175 524288 711 1048576 (ep904 rfl) rfl) (Enclosure.sfrac_false_div 169719175 524288) (BSN.sin_reduce2 qz455 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9791776170167353999360) qz19) 226375608064910080 72057594037927936 Bool.false 135507 1048576 51 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q2 169719175 524288 226375608064910080 72057594037927936 51 9791776170167353999360 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 135507 1048576 9791776170167353999360 75557863725914323419136 278299017 2147483648 385360 384984 (ep908 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep910 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz37 (Real.cos qz162)) (@HMul.hMul Real Real Real qz0 qz37 (@Neg.neg Real Real.instNeg (Real.sin qz162))) Bool.true 314739194751 1099511627776 10486337134015 52911798063464448 Bool.false 41017562379 1099511627776 10442820660067 52911798063464448 (@Enclosure.Real.IsNear.mulLit_ft qz37 (Real.cos qz162) 302697 1048576 1 1048576 1039783 1048576 34477597 50460622848 314739194751 1099511627776 10486337134015 52911798063464448 qz338 (@Enclosure.Real.IsNear.recentre' (Real.cos qz162) Bool.true 1039783 1048576 137910388 201842491392 1039783 1048576 34477597 50460622848 (ep907 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz37 (@Neg.neg Real Real.instNeg (Real.sin qz162)) 302697 1048576 1 1048576 135507 1048576 34477597 50460622848 41017562379 1099511627776 10442820660067 52911798063464448 qz338 (@Enclosure.Real.IsNear.neg (Real.sin qz162) Bool.true 135507 1048576 34477597 50460622848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz162) Bool.true 135507 1048576 137910388 201842491392 135507 1048576 34477597 50460622848 (ep909 rfl rfl) rfl)) rfl)

noncomputable def ep911 := @ep861 314739194751 1099511627776 10486337134015 52911798063464448 Bool.false 41017562379 1099511627776 10442820660067 52911798063464448 Bool.true 121709723331227103002624 27673587131 274877906944 27818653688119 8818633010577408 Bool.false 142693390005477612453888 32444720547 274877906944 27839491235857 8818633010577408 (ep862 (BSN.head_sum_c_succ qz146 11 12 rfl rfl) (ep902 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep903 ep910) rfl rfl

noncomputable abbrev qz163 := (@HMul.hMul Real Real Real qz267 qz443 qz556)

noncomputable def ep912 := @Enclosure.Complex.IsNear.of_eq qz619 (Complex.mk (@HMul.hMul Real Real Real qz0 qz39 (Real.cos qz163)) (@HMul.hMul Real Real Real qz0 qz39 (@Neg.neg Real Real.instNeg (Real.sin qz163)))) Bool.false 129549141111 1099511627776 10048349397139 52911798063464448 Bool.true 276064023573 1099511627776 10072593475801 52911798063464448 (BSN.cpow_neg_s_mk qz149 130272 1000 13 qz150 rfl)

noncomputable def ep913 := @Enclosure.Real.IsNear.mulLit_ff qz149 qz556 130272 1000 0 1 11551497052968677 4503599627370496 250000000144369 48123000000000000000 47026144502635484067 140737488355328000 339250000195908733 501281250000000000000 qz151 (BSN.isNear_log_sfrac 13 1 11551497052968677 4503599627370496 250000000144369 48123000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz339) Bool.false 48450490295254733815808 18889465931478580854784 1000000000577476 192492000000000000000 11551497052968677 4503599627370496 250000000144369 48123000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 254545 524288 24973259072661432 36028797018963968 192492 1000000000000000 rfl rfl rfl rfl (ep230 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep914 := nat_lit 1249127596588959967639811794405250974342774270199090397796179637718791854555136

noncomputable def ep915 := nat_lit 1219852923045320649894467808392855509806669601567053557545581391666237997056

noncomputable def ep916 := nat_lit 3744943083920789261619646447598967212008709471394137086273447750373043087671296

noncomputable def ep917 := BSN.cos_dyadic_bound_f 2431019452 2147483648 3 2 1048576 385360 ep914 ep57 ep915 ep916 ep60 ep915 445457 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2431019452) qz15 0 2 ep914 ep57 ep915 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2431019452) qz16 0 2 ep916 ep60 ep915 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz456 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 350372079) qz24)

noncomputable def ep918 := @Enclosure.Real.IsNear.cos_image qz163 qz456 Bool.false 350372079 1048576 711 1048576 Bool.false 445457 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz163 Bool.false 47026144502635484067 140737488355328000 339250000195908733 501281250000000000000 350372079 1048576 711 1048576 (ep913 rfl) rfl) (Enclosure.sfrac_false_div 350372079 1048576) (BSN.cos_reduce0 qz456 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 171067785932147343228928) qz25) 226375608064910080 72057594037927936 Bool.false 445457 1048576 53 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q0 350372079 1048576 226375608064910080 72057594037927936 53 171067785932147343228928 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 445457 1048576 171067785932147343228928 151115727451828646838272 2431019452 2147483648 385360 384984 (ep917 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep919 := nat_lit 2247453791521691685231745655682737469409148350677109073187086882780492347801600

noncomputable def ep920 := nat_lit 5884213501633785799316647578907866844293796786704177104968248989790972716056576

noncomputable def ep921 := BSN.sin_dyadic_bound_f 2431019452 2147483648 3 2 1048576 385360 ep919 ep64 ep915 ep920 ep66 ep915 949251 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2431019452) qz20 0 2 ep919 ep64 ep915 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2431019452) qz21 0 2 ep920 ep66 ep915 rfl rfl rfl rfl) rfl rfl

noncomputable def ep922 := @Enclosure.Real.IsNear.sin_image qz163 qz456 Bool.false 350372079 1048576 711 1048576 Bool.false 949251 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz163 Bool.false 47026144502635484067 140737488355328000 339250000195908733 501281250000000000000 350372079 1048576 711 1048576 (ep913 rfl) rfl) (Enclosure.sfrac_false_div 350372079 1048576) (BSN.sin_reduce0 qz456 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 171067785932147343228928) qz25) 226375608064910080 72057594037927936 Bool.false 949251 1048576 53 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q0 350372079 1048576 226375608064910080 72057594037927936 53 171067785932147343228928 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 949251 1048576 171067785932147343228928 151115727451828646838272 2431019452 2147483648 385360 384984 (ep921 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep923 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz39 (Real.cos qz163)) (@HMul.hMul Real Real Real qz0 qz39 (@Neg.neg Real Real.instNeg (Real.sin qz163))) Bool.false 129549141111 1099511627776 10048349397139 52911798063464448 Bool.true 276064023573 1099511627776 10072593475801 52911798063464448 (@Enclosure.Real.IsNear.mulLit_ff qz39 (Real.cos qz163) 290823 1048576 1 1048576 445457 1048576 34477597 50460622848 129549141111 1099511627776 10048349397139 52911798063464448 qz341 (@Enclosure.Real.IsNear.recentre' (Real.cos qz163) Bool.false 445457 1048576 137910388 201842491392 445457 1048576 34477597 50460622848 (ep918 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz39 (@Neg.neg Real Real.instNeg (Real.sin qz163)) 290823 1048576 1 1048576 949251 1048576 34477597 50460622848 276064023573 1099511627776 10072593475801 52911798063464448 qz341 (@Enclosure.Real.IsNear.neg (Real.sin qz163) Bool.false 949251 1048576 34477597 50460622848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz163) Bool.false 949251 1048576 137910388 201842491392 949251 1048576 34477597 50460622848 (ep922 rfl rfl) rfl)) rfl)

noncomputable def ep924 := @ep859 129549141111 1099511627776 10048349397139 52911798063464448 Bool.true 276064023573 1099511627776 10072593475801 52911798063464448 Bool.false 5182765922177807024128 18854792587 1099511627776 176960271525853 52911798063464448 Bool.true 40210553480915913277440 146285141385 1099511627776 177109540890943 52911798063464448 (ep860 (BSN.head_sum_c_succ qz146 12 13 rfl rfl) (ep911 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep912 ep923) rfl rfl

noncomputable abbrev qz164 := (@HMul.hMul Real Real Real qz267 qz443 qz557)

noncomputable def ep925 := @Enclosure.Complex.IsNear.of_eq qz618 (Complex.mk (@HMul.hMul Real Real Real qz0 qz41 (Real.cos qz164)) (@HMul.hMul Real Real Real qz0 qz41 (@Neg.neg Real Real.instNeg (Real.sin qz164)))) Bool.true 61064108971 1099511627776 9659139368987 52911798063464448 Bool.false 143720660849 549755813888 4849006299517 26455899031732224 (BSN.cpow_neg_s_mk qz149 130272 1000 14 qz150 rfl)

noncomputable def ep926 := @Enclosure.Real.IsNear.mulLit_ff qz149 qz557 130272 1000 0 1 11885250371606245 4503599627370496 250000000144369 48123000000000000000 9676970852561804679 28147497671065600 339250000195908733 501281250000000000000 qz151 (BSN.isNear_log_sfrac 14 1 11885250371606245 4503599627370496 250000000144369 48123000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz342) Bool.false 49850353174629559828480 18889465931478580854784 1000000000577476 192492000000000000000 11885250371606245 4503599627370496 250000000144369 48123000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 293399 524288 24973259072661432 36028797018963968 192492 1000000000000000 rfl rfl rfl rfl (ep241 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep927 := nat_lit 2616162510359042547484812887866848727752691374345830571441392411889185465961601

noncomputable def ep928 := nat_lit 5339460626273836594056139031831249653959816361104265542398451861198947617921

noncomputable def ep929 := nat_lit 7837808609824579969266326385536883683950154490315283183239380331945158502648961

noncomputable def ep930 := BSN.cos_dyadic_bound_f 2923729391 2147483648 3 2 1048576 385360 ep927 ep57 ep928 ep929 ep60 ep928 217897 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2923729391) qz15 0 2 ep927 ep57 ep928 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2923729391) qz16 0 2 ep929 ep60 ep928 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz457 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 45061907) (@Nat.cast Real Real.instNatCast 131072))

noncomputable def ep931 := @Enclosure.Real.IsNear.cos_image qz164 qz457 Bool.false 45061907 131072 355 524288 Bool.true 217897 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz164 Bool.false 9676970852561804679 28147497671065600 339250000195908733 501281250000000000000 45061907 131072 355 524288 (ep926 rfl) rfl) (Enclosure.sfrac_false_div 45061907 131072) (BSN.cos_reduce2 qz457 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 25717395699837356212224) qz371) 226375608064910080 72057594037927936 Bool.false 217897 1048576 54 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q2 45061907 131072 226375608064910080 72057594037927936 54 25717395699837356212224 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 217897 1048576 25717395699837356212224 18889465931478580854784 2923729391 2147483648 385360 384984 (ep930 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep932 := nat_lit 4704820950145257516197418286934862710231676620733611616160587579911574680636545

noncomputable def ep933 := nat_lit 12313505266509326330793337954968342217833694304003385421923369977707421105523841

noncomputable def ep934 := BSN.sin_dyadic_bound_f 2923729391 2147483648 3 2 1048576 385360 ep932 ep64 ep928 ep933 ep66 ep928 1025686 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2923729391) qz20 0 2 ep932 ep64 ep928 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2923729391) qz21 0 2 ep933 ep66 ep928 rfl rfl rfl rfl) rfl rfl

noncomputable def ep935 := @Enclosure.Real.IsNear.sin_image qz164 qz457 Bool.false 45061907 131072 355 524288 Bool.true 1025686 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz164 Bool.false 9676970852561804679 28147497671065600 339250000195908733 501281250000000000000 45061907 131072 355 524288 (ep926 rfl) rfl) (Enclosure.sfrac_false_div 45061907 131072) (BSN.sin_reduce2 qz457 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 25717395699837356212224) qz371) 226375608064910080 72057594037927936 Bool.false 1025686 1048576 54 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q2 45061907 131072 226375608064910080 72057594037927936 54 25717395699837356212224 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1025686 1048576 25717395699837356212224 18889465931478580854784 2923729391 2147483648 385360 384984 (ep934 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep936 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz41 (Real.cos qz164)) (@HMul.hMul Real Real Real qz0 qz41 (@Neg.neg Real Real.instNeg (Real.sin qz164))) Bool.true 61064108971 1099511627776 9659139368987 52911798063464448 Bool.false 143720660849 549755813888 4849006299517 26455899031732224 (@Enclosure.Real.IsNear.mulLit_ft qz41 (Real.cos qz164) 280243 1048576 1 1048576 217897 1048576 17214737 25230311424 61064108971 1099511627776 9659139368987 52911798063464448 qz344 (@Enclosure.Real.IsNear.recentre' (Real.cos qz164) Bool.true 217897 1048576 68858948 100921245696 217897 1048576 17214737 25230311424 (ep931 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz41 (@Neg.neg Real Real.instNeg (Real.sin qz164)) 280243 1048576 1 1048576 512843 524288 17214737 25230311424 143720660849 549755813888 4849006299517 26455899031732224 qz344 (@Enclosure.Real.IsNear.neg (Real.sin qz164) Bool.true 512843 524288 17214737 25230311424 (@Enclosure.Real.IsNear.recentre' (Real.sin qz164) Bool.true 1025686 1048576 68858948 100921245696 512843 524288 17214737 25230311424 (ep935 rfl rfl) rfl)) rfl)

noncomputable def ep937 := @ep857 61064108971 1099511627776 9659139368987 52911798063464448 Bool.false 143720660849 549755813888 4849006299517 26455899031732224 Bool.true 46409634164684026281984 1319041137 34359738368 7775808787285 2204658252644352 Bool.false 77601430793294597586944 141156180313 1099511627776 62269184496659 17637266021154816 (ep858 (BSN.head_sum_c_succ qz146 13 14 rfl rfl) (ep924 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep925 ep936) rfl rfl

noncomputable abbrev qz165 := (@HMul.hMul Real Real Real qz267 qz443 qz558)

noncomputable def ep938 := @Enclosure.Complex.IsNear.of_eq qz617 (Complex.mk (@HMul.hMul Real Real Real qz0 qz43 (Real.cos qz165)) (@HMul.hMul Real Real Real qz0 qz43 (@Neg.neg Real Real.instNeg (Real.sin qz165)))) Bool.false 42742693893 274877906944 4682461428245 26455899031732224 Bool.true 226635937395 1099511627776 9374817089659 52911798063464448 (BSN.cpow_neg_s_mk qz149 130272 1000 15 qz150 rfl)

noncomputable def ep939 := @Enclosure.Real.IsNear.mulLit_ff qz149 qz558 130272 1000 0 1 12195965485668069 4503599627370496 250000000144369 48123000000000000000 49649775492154708899 140737488355328000 339250000195908733 501281250000000000000 qz151 (BSN.isNear_log_sfrac 15 1 12195965485668069 4503599627370496 250000000144369 48123000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz345) Bool.false 51153586820399524478976 18889465931478580854784 1000000000577476 192492000000000000000 12195965485668069 4503599627370496 250000000144369 48123000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 329571 524288 24973259072661432 36028797018963968 192492 1000000000000000 rfl rfl rfl rfl (ep252 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep940 := nat_lit 555335283238623154838840769555308675371359196114930690025615656286049200800000

noncomputable def ep941 := nat_lit 241365642018538717071919053969761456795743857897712289148027084048100000000

noncomputable def ep942 := nat_lit 1665523118431832387082378470557986503200486100628996645498550914690051402400000

noncomputable def ep943 := BSN.cos_dyadic_bound_f 1985337890 2147483648 3 2 1048576 385360 ep940 ep57 ep941 ep942 ep60 ep941 631492 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1985337890) qz15 0 2 ep940 ep57 ep941 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1985337890) qz16 0 2 ep942 ep60 ep941 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz458 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 369919653) qz24)

noncomputable def ep944 := @Enclosure.Real.IsNear.cos_image qz165 qz458 Bool.false 369919653 1048576 711 1048576 Bool.false 631492 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz165 Bool.false 49649775492154708899 140737488355328000 339250000195908733 501281250000000000000 369919653 1048576 711 1048576 (ep939 rfl) rfl) (Enclosure.sfrac_false_div 369919653 1048576) (BSN.cos_reduce0 qz458 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 139705734141603789930496) qz25) 226375608064910080 72057594037927936 Bool.false 631492 1048576 56 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q0 369919653 1048576 226375608064910080 72057594037927936 56 139705734141603789930496 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 631492 1048576 139705734141603789930496 151115727451828646838272 1985337890 2147483648 385360 384984 (ep943 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep945 := nat_lit 999410417315906847736255849956379806503009957920557072214789759647650081440000

noncomputable def ep946 := nat_lit 2617112691454583157576839357131710355625452018783910321618209707607767575200000

noncomputable def ep947 := BSN.sin_dyadic_bound_f 1985337890 2147483648 3 2 1048576 385360 ep945 ep64 ep941 ep946 ep66 ep941 837095 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1985337890) qz20 0 2 ep945 ep64 ep941 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1985337890) qz21 0 2 ep946 ep66 ep941 rfl rfl rfl rfl) rfl rfl

noncomputable def ep948 := @Enclosure.Real.IsNear.sin_image qz165 qz458 Bool.false 369919653 1048576 711 1048576 Bool.false 837095 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz165 Bool.false 49649775492154708899 140737488355328000 339250000195908733 501281250000000000000 369919653 1048576 711 1048576 (ep939 rfl) rfl) (Enclosure.sfrac_false_div 369919653 1048576) (BSN.sin_reduce0 qz458 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 139705734141603789930496) qz25) 226375608064910080 72057594037927936 Bool.false 837095 1048576 56 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q0 369919653 1048576 226375608064910080 72057594037927936 56 139705734141603789930496 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 837095 1048576 139705734141603789930496 151115727451828646838272 1985337890 2147483648 385360 384984 (ep947 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep949 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz43 (Real.cos qz165)) (@HMul.hMul Real Real Real qz0 qz43 (@Neg.neg Real Real.instNeg (Real.sin qz165))) Bool.false 42742693893 274877906944 4682461428245 26455899031732224 Bool.true 226635937395 1099511627776 9374817089659 52911798063464448 (@Enclosure.Real.IsNear.mulLit_ff qz43 (Real.cos qz165) 270741 1048576 1 1048576 157873 262144 34477597 50460622848 42742693893 274877906944 4682461428245 26455899031732224 qz347 (@Enclosure.Real.IsNear.recentre' (Real.cos qz165) Bool.false 631492 1048576 137910388 201842491392 157873 262144 34477597 50460622848 (ep944 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz43 (@Neg.neg Real Real.instNeg (Real.sin qz165)) 270741 1048576 1 1048576 837095 1048576 34477597 50460622848 226635937395 1099511627776 9374817089659 52911798063464448 qz347 (@Enclosure.Real.IsNear.neg (Real.sin qz165) Bool.false 837095 1048576 34477597 50460622848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz165) Bool.false 837095 1048576 137910388 201842491392 837095 1048576 34477597 50460622848 (ep948 rfl rfl) rfl)) rfl)

noncomputable def ep950 := @ep855 42742693893 274877906944 4682461428245 26455899031732224 Bool.true 226635937395 1099511627776 9374817089659 52911798063464448 Bool.false 1106052512395397431296 32190364797 274877906944 97992166875665 26455899031732224 Bool.true 93985986851126883909632 42739878541 549755813888 49045592644909 13227949515866112 (ep856 (BSN.head_sum_c_succ qz146 14 15 rfl rfl) (ep937 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep938 ep949) rfl rfl

noncomputable abbrev qz166 := (@HMul.hMul Real Real Real qz267 qz443 qz559)

noncomputable def ep951 := @Enclosure.Complex.IsNear.of_eq qz616 (Complex.mk (@HMul.hMul Real Real Real qz0 qz45 (Real.cos qz166)) (@HMul.hMul Real Real Real qz0 qz45 (@Neg.neg Real Real.instNeg (Real.sin qz166)))) Bool.true 273702195585 1099511627776 9088340171653 52911798063464448 Bool.true 25383568833 1099511627776 9042754986181 52911798063464448 (BSN.cpow_neg_s_mk qz149 130272 1000 16 qz150 rfl)

noncomputable def ep952 := @Enclosure.Real.IsNear.mulLit_ff qz149 qz559 130272 1000 0 1 3121657384082679 1125899906842624 62500000048123 12030750000000000000 12708267210600586209 35184372088832000 84812500065302911 125320312500000000000 qz151 (BSN.isNear_log_sfrac 16 1 3121657384082679 1125899906842624 62500000048123 12030750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz348) Bool.false 52372720210750067441664 18889465931478580854784 1000000000769968 192492000000000000000 3121657384082679 1125899906842624 62500000048123 12030750000000000000 (BSN.log_rat_reduce_isNear 16 1 4 32 32 0 524288 24973259072661432 36028797018963968 192492 1000000000000000 rfl rfl rfl rfl (ep262 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep953 := nat_lit 6543023804507654185973017083520337143398342535131249149699712521464011607244800

noncomputable def ep954 := nat_lit 10317720047438563080080892971932296358547725425653015390340993027951302803456

noncomputable def ep955 := nat_lit 17119786036490860432561580439646325943367534131797452414772028329408109243006976

noncomputable def ep956 := BSN.sin_dyadic_bound_f 3174665464 2147483648 3 2 1048576 385360 ep953 ep64 ep954 ep955 ep66 ep954 1044095 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3174665464) qz20 0 2 ep953 ep64 ep954 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3174665464) qz21 0 2 ep955 ep66 ep954 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz459 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 94683969) (@Nat.cast Real Real.instNatCast 262144))

noncomputable def ep957 := @Enclosure.Real.IsNear.cos_image qz166 qz459 Bool.false 94683969 262144 711 1048576 Bool.true 1044095 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz166 Bool.false 12708267210600586209 35184372088832000 84812500065302911 125320312500000000000 94683969 262144 711 1048576 (ep952 rfl) rfl) (Enclosure.sfrac_false_div 94683969 262144) (BSN.cos_reduce1 qz459 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 55849305473483578277888) qz301) 226375608064910080 72057594037927936 Bool.false 1044095 1048576 57 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q1 94683969 262144 226375608064910080 72057594037927936 57 55849305473483578277888 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1044095 1048576 55849305473483578277888 37778931862957161709568 3174665464 2147483648 385360 384984 (ep956 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep958 := nat_lit 3639598878080891686909489887721046100269544841928761978895547397714651471937536

noncomputable def ep959 := nat_lit 10898161194147797934568307877219273708091539074934979905905960207088051810205696

noncomputable def ep960 := BSN.cos_dyadic_bound_f 3174665464 2147483648 3 2 1048576 385360 ep958 ep57 ep954 ep959 ep60 ep954 96831 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3174665464) qz15 0 2 ep958 ep57 ep954 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3174665464) qz16 0 2 ep959 ep60 ep954 rfl rfl rfl rfl) rfl rfl

noncomputable def ep961 := @Enclosure.Real.IsNear.sin_image qz166 qz459 Bool.false 94683969 262144 711 1048576 Bool.false 96831 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz166 Bool.false 12708267210600586209 35184372088832000 84812500065302911 125320312500000000000 94683969 262144 711 1048576 (ep952 rfl) rfl) (Enclosure.sfrac_false_div 94683969 262144) (BSN.sin_reduce1 qz459 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 55849305473483578277888) qz301) 226375608064910080 72057594037927936 Bool.false 96831 1048576 57 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q1 94683969 262144 226375608064910080 72057594037927936 57 55849305473483578277888 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 96831 1048576 55849305473483578277888 37778931862957161709568 3174665464 2147483648 385360 384984 (ep960 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep962 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz45 (Real.cos qz166)) (@HMul.hMul Real Real Real qz0 qz45 (@Neg.neg Real Real.instNeg (Real.sin qz166))) Bool.true 273702195585 1099511627776 9088340171653 52911798063464448 Bool.true 25383568833 1099511627776 9042754986181 52911798063464448 (@Enclosure.Real.IsNear.mulLit_ft qz45 (Real.cos qz166) 262143 1048576 1 1048576 1044095 1048576 34477597 50460622848 273702195585 1099511627776 9088340171653 52911798063464448 qz350 (@Enclosure.Real.IsNear.recentre' (Real.cos qz166) Bool.true 1044095 1048576 137910388 201842491392 1044095 1048576 34477597 50460622848 (ep957 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz45 (@Neg.neg Real Real.instNeg (Real.sin qz166)) 262143 1048576 1 1048576 96831 1048576 34477597 50460622848 25383568833 1099511627776 9042754986181 52911798063464448 qz350 (@Enclosure.Real.IsNear.neg (Real.sin qz166) Bool.false 96831 1048576 34477597 50460622848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz166) Bool.false 96831 1048576 137910388 201842491392 96831 1048576 34477597 50460622848 (ep961 rfl rfl) rfl)) rfl)

noncomputable def ep963 := @ep853 273702195585 1099511627776 9088340171653 52911798063464448 Bool.true 25383568833 1099511627776 9042754986181 52911798063464448 Bool.true 39841006251729399840768 144940736397 1099511627776 205072673922983 52911798063464448 Bool.true 60947757968731427307520 110863325915 1099511627776 205225125565817 52911798063464448 (ep854 (BSN.head_sum_c_succ qz146 15 16 rfl rfl) (ep950 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep951 ep962) rfl rfl

theorem EMRow43.d14 : Enclosure.Complex.IsNear qz158 Bool.true 144940736397 1099511627776 205072673922983 52911798063464448 Bool.true 110863325915 1099511627776 205225125565817 52911798063464448 := ep852 (BSN.head_sum_c_succ qz146 16 17 rfl rfl) (ep963 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz167 := (BSN.headSumC qz441 25)

noncomputable abbrev qz624 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 24) qz147)

noncomputable def ep964 := @Enclosure.Complex.IsNear.of_eq qz167 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 24) qz624) Bool.false 1277433911845 1099511627776 269550101905375 52911798063464448 Bool.true 128172929219 1099511627776 269615590474909 52911798063464448

noncomputable def ep965 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 24) qz624 Bool.false 1102766957817 1099511627776 262131246173099 52911798063464448 Bool.true 16819302195 68719476736 65551079647643 13227949515866112 Bool.false

noncomputable abbrev qz625 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 23) qz147)

noncomputable def ep966 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 24) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 23) qz625) Bool.false 1102766957817 1099511627776 262131246173099 52911798063464448 Bool.true 16819302195 68719476736 65551079647643 13227949515866112

noncomputable def ep967 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 23) qz625 Bool.false 873913329717 1099511627776 254553077915743 52911798063464448 Bool.true 127702364583 549755813888 127336752211961 26455899031732224 Bool.false

noncomputable abbrev qz626 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 22) qz147)

noncomputable def ep968 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 23) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 22) qz626) Bool.false 873913329717 1099511627776 254553077915743 52911798063464448 Bool.true 127702364583 549755813888 127336752211961 26455899031732224

noncomputable def ep969 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 22) qz626 Bool.false 674350702527 1099511627776 82271045202947 17637266021154816 Bool.true 132417751857 1099511627776 82316681944193 17637266021154816 Bool.false

noncomputable abbrev qz627 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 21) qz147)

noncomputable def ep970 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 22) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 21) qz627) Bool.false 674350702527 1099511627776 82271045202947 17637266021154816 Bool.true 132417751857 1099511627776 82316681944193 17637266021154816

noncomputable def ep971 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 21) qz627 Bool.false 502972427431 1099511627776 238862897809049 52911798063464448 Bool.false 35502625623 1099511627776 239001262502339 52911798063464448 Bool.false

noncomputable abbrev qz628 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 20) qz147)

noncomputable def ep972 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 21) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 20) qz628) Bool.false 502972427431 1099511627776 238862897809049 52911798063464448 Bool.false 35502625623 1099511627776 239001262502339 52911798063464448

noncomputable def ep973 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 20) qz628 Bool.false 39414248867 137438953472 12818912230933 2939544336859136 Bool.false 24293044135 137438953472 12826927736835 2939544336859136 Bool.false

noncomputable abbrev qz629 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 19) qz147)

noncomputable def ep974 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 20) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 19) qz629) Bool.false 39414248867 137438953472 12818912230933 2939544336859136 Bool.false 24293044135 137438953472 12826927736835 2939544336859136

noncomputable def ep975 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 19) qz629 Bool.false 74608971623 1099511627776 222409913680693 52911798063464448 Bool.false 269765132437 1099511627776 222587257330261 52911798063464448 Bool.false

noncomputable abbrev qz630 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 18) qz147)

noncomputable def ep976 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 19) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 18) qz630) Bool.false 74608971623 1099511627776 222409913680693 52911798063464448 Bool.false 269765132437 1099511627776 222587257330261 52911798063464448

noncomputable def ep977 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 18) qz630 Bool.true 39497753313 274877906944 106921708434287 26455899031732224 Bool.false 9717981263 68719476736 53510949802975 13227949515866112 Bool.false

noncomputable abbrev qz631 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 17) qz147)

noncomputable def ep978 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 18) (@HAdd.hAdd Complex Complex Complex qz4 qz158 qz631) Bool.true 39497753313 274877906944 106921708434287 26455899031732224 Bool.false 9717981263 68719476736 53510949802975 13227949515866112

noncomputable def ep979 := @Enclosure.Complex.IsNear.addLitP qz158 qz631 Bool.true 144940736397 1099511627776 205072673922983 52911798063464448 Bool.true 110863325915 1099511627776 205225125565817 52911798063464448 Bool.true

noncomputable abbrev qz168 := (@HMul.hMul Real Real Real qz267 qz443 qz568)

noncomputable def ep980 := @Enclosure.Complex.IsNear.of_eq qz631 (Complex.mk (@HMul.hMul Real Real Real qz0 qz48 (Real.cos qz168)) (@HMul.hMul Real Real Real qz0 qz48 (@Neg.neg Real Real.instNeg (Real.sin qz168)))) Bool.true 13050276855 1099511627776 8770742945591 52911798063464448 Bool.false 266351026123 1099511627776 8818673646083 52911798063464448 (BSN.cpow_neg_s_mk qz149 130272 1000 17 qz150 rfl)

noncomputable def ep981 := @Enclosure.Real.IsNear.mulLit_ff qz149 qz568 130272 1000 0 1 3189913004350711 1125899906842624 62500000048123 12030750000000000000 12986135840711744481 35184372088832000 84812500065302911 125320312500000000000 qz151 (BSN.isNear_log_sfrac 17 1 3189913004350711 1125899906842624 62500000048123 12030750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz351) Bool.false 53517859495200818200576 18889465931478580854784 1000000000769968 192492000000000000000 3189913004350711 1125899906842624 62500000048123 12030750000000000000 (BSN.log_rat_reduce_isNear 17 1 4 34 32 31784 524288 24973259072661432 36028797018963968 192492 1000000000000000 rfl rfl rfl rfl (ep290 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep982 := nat_lit 4088899860572209815454038182156476462591113150225466419970980350547347237488161

noncomputable def ep983 := nat_lit 13013277568713056384036523371748490048984088636580149451337751834231349954081

noncomputable def ep984 := nat_lit 12240673026579203333594041499725932407675371273403238961010265547973579012556321

noncomputable def ep985 := BSN.cos_dyadic_bound_f 3268122573 2147483648 3 2 1048576 385360 ep982 ep57 ep983 ep984 ep60 ep983 51315 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3268122573) qz15 0 2 ep982 ep57 ep983 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3268122573) qz16 0 2 ep984 ep60 ep983 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz460 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 193508503) qz17)

noncomputable def ep986 := @Enclosure.Real.IsNear.cos_image qz168 qz460 Bool.false 193508503 524288 711 1048576 Bool.true 51315 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz168 Bool.false 12986135840711744481 35184372088832000 84812500065302911 125320312500000000000 193508503 524288 711 1048576 (ep981 rfl) rfl) (Enclosure.sfrac_false_div 193508503 524288) (BSN.cos_reduce2 qz460 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 114986840656595445088256) qz19) 226375608064910080 72057594037927936 Bool.false 51315 1048576 58 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q2 193508503 524288 226375608064910080 72057594037927936 58 114986840656595445088256 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 51315 1048576 114986840656595445088256 75557863725914323419136 3268122573 2147483648 385360 384984 (ep985 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep987 := nat_lit 7349609126975007222710039509184258840624816399496575436386694429517839947515425

noncomputable def ep988 := nat_lit 19227907168870912063428330057642608932033306807555615424758224288624634819757601

noncomputable def ep989 := BSN.sin_dyadic_bound_f 3268122573 2147483648 3 2 1048576 385360 ep987 ep64 ep983 ep988 ep66 ep983 1047319 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3268122573) qz20 0 2 ep987 ep64 ep983 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3268122573) qz21 0 2 ep988 ep66 ep983 rfl rfl rfl rfl) rfl rfl

noncomputable def ep990 := @Enclosure.Real.IsNear.sin_image qz168 qz460 Bool.false 193508503 524288 711 1048576 Bool.true 1047319 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz168 Bool.false 12986135840711744481 35184372088832000 84812500065302911 125320312500000000000 193508503 524288 711 1048576 (ep981 rfl) rfl) (Enclosure.sfrac_false_div 193508503 524288) (BSN.sin_reduce2 qz460 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 114986840656595445088256) qz19) 226375608064910080 72057594037927936 Bool.false 1047319 1048576 58 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q2 193508503 524288 226375608064910080 72057594037927936 58 114986840656595445088256 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1047319 1048576 114986840656595445088256 75557863725914323419136 3268122573 2147483648 385360 384984 (ep989 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep991 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz48 (Real.cos qz168)) (@HMul.hMul Real Real Real qz0 qz48 (@Neg.neg Real Real.instNeg (Real.sin qz168))) Bool.true 13050276855 1099511627776 8770742945591 52911798063464448 Bool.false 266351026123 1099511627776 8818673646083 52911798063464448 (@Enclosure.Real.IsNear.mulLit_ft qz48 (Real.cos qz168) 254317 1048576 1 1048576 51315 1048576 34477597 50460622848 13050276855 1099511627776 8770742945591 52911798063464448 qz353 (@Enclosure.Real.IsNear.recentre' (Real.cos qz168) Bool.true 51315 1048576 137910388 201842491392 51315 1048576 34477597 50460622848 (ep986 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz48 (@Neg.neg Real Real.instNeg (Real.sin qz168)) 254317 1048576 1 1048576 1047319 1048576 34477597 50460622848 266351026123 1099511627776 8818673646083 52911798063464448 qz353 (@Enclosure.Real.IsNear.neg (Real.sin qz168) Bool.true 1047319 1048576 34477597 50460622848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz168) Bool.true 1047319 1048576 137910388 201842491392 1047319 1048576 34477597 50460622848 (ep990 rfl rfl) rfl)) rfl)

noncomputable def ep992 := @ep979 13050276855 1099511627776 8770742945591 52911798063464448 Bool.false 266351026123 1099511627776 8818673646083 52911798063464448 Bool.true 173712956154686107287552 39497753313 274877906944 106921708434287 26455899031732224 Bool.false 170960534354844773777408 9717981263 68719476736 53510949802975 13227949515866112 EMRow43.d14 (ep980 ep991) rfl rfl

noncomputable abbrev qz169 := (@HMul.hMul Real Real Real qz267 qz443 qz569)

noncomputable def ep993 := @Enclosure.Complex.IsNear.of_eq qz630 (Complex.mk (@HMul.hMul Real Real Real qz0 qz50 (Real.cos qz169)) (@HMul.hMul Real Real Real qz0 qz50 (@Neg.neg Real Real.instNeg (Real.sin qz169)))) Bool.false 232599984875 1099511627776 2855498937373 17637266021154816 Bool.false 114277432229 1099511627776 2847819372787 17637266021154816 (BSN.cpow_neg_s_mk qz149 130272 1000 18 qz150 rfl)

noncomputable def ep994 := @Enclosure.Real.IsNear.mulLit_ff qz149 qz569 130272 1000 0 1 3254268794313975 1125899906842624 62500000048123 12030750000000000000 529925130466087689 1407374883553280 84812500065302911 125320312500000000000 qz151 (BSN.isNear_log_sfrac 18 1 3254268794313975 1125899906842624 62500000048123 12030750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz354) Bool.false 54597570484265130393600 18889465931478580854784 1000000000769968 192492000000000000000 3254268794313975 1125899906842624 62500000048123 12030750000000000000 (BSN.log_rat_reduce_isNear 18 1 4 36 32 61752 524288 24973259072661432 36028797018963968 192492 1000000000000000 rfl rfl rfl rfl (ep301 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep995 := nat_lit 2108552625463728688489824922234540989549330506242653423020802666833346895970560

noncomputable def ep996 := nat_lit 1073801337959996584130945154562207778468338363894528501741039466245192581376

noncomputable def ep997 := nat_lit 5520661197857830380146662789887839969559297825665405918908807206380082987172096

noncomputable def ep998 := BSN.sin_dyadic_bound_f 2392574626 2147483648 3 2 1048576 385360 ep995 ep64 ep996 ep997 ep66 ep996 941125 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2392574626) qz20 0 2 ep995 ep64 ep996 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2392574626) qz21 0 2 ep997 ep66 ep996 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz461 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 394824989) qz24)

noncomputable def ep999 := @Enclosure.Real.IsNear.cos_image qz169 qz461 Bool.false 394824989 1048576 711 1048576 Bool.false 941125 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz169 Bool.false 529925130466087689 1407374883553280 84812500065302911 125320312500000000000 394824989 1048576 711 1048576 (ep994 rfl) rfl) (Enclosure.sfrac_false_div 394824989 1048576) (BSN.cos_reduce3 qz461 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 168362471839920488972288) qz25) 226375608064910080 72057594037927936 Bool.false 941125 1048576 59 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q3 394824989 1048576 226375608064910080 72057594037927936 59 168362471839920488972288 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 941125 1048576 168362471839920488972288 151115727451828646838272 2392574626 2147483648 385360 384984 (ep998 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1000 := nat_lit 1171895370296720380976183154643439308762280653852093914345664165781301694464256

noncomputable def ep1001 := nat_lit 3513538508214241149760287573621193510729905284828492686033510418411414698230016

noncomputable def ep1002 := BSN.cos_dyadic_bound_f 2392574626 2147483648 3 2 1048576 385360 ep1000 ep57 ep996 ep1001 ep60 ep996 462379 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2392574626) qz15 0 2 ep1000 ep57 ep996 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2392574626) qz16 0 2 ep1001 ep60 ep996 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1003 := @Enclosure.Real.IsNear.sin_image qz169 qz461 Bool.false 394824989 1048576 711 1048576 Bool.true 462379 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz169 Bool.false 529925130466087689 1407374883553280 84812500065302911 125320312500000000000 394824989 1048576 711 1048576 (ep994 rfl) rfl) (Enclosure.sfrac_false_div 394824989 1048576) (BSN.sin_reduce3 qz461 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 168362471839920488972288) qz25) 226375608064910080 72057594037927936 Bool.false 462379 1048576 59 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q3 394824989 1048576 226375608064910080 72057594037927936 59 168362471839920488972288 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 462379 1048576 168362471839920488972288 151115727451828646838272 2392574626 2147483648 385360 384984 (ep1002 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1004 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz50 (Real.cos qz169)) (@HMul.hMul Real Real Real qz0 qz50 (@Neg.neg Real Real.instNeg (Real.sin qz169))) Bool.false 232599984875 1099511627776 2855498937373 17637266021154816 Bool.false 114277432229 1099511627776 2847819372787 17637266021154816 (@Enclosure.Real.IsNear.mulLit_ff qz50 (Real.cos qz169) 247151 1048576 1 1048576 941125 1048576 34477597 50460622848 232599984875 1099511627776 2855498937373 17637266021154816 qz356 (@Enclosure.Real.IsNear.recentre' (Real.cos qz169) Bool.false 941125 1048576 137910388 201842491392 941125 1048576 34477597 50460622848 (ep999 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz50 (@Neg.neg Real Real.instNeg (Real.sin qz169)) 247151 1048576 1 1048576 462379 1048576 34477597 50460622848 114277432229 1099511627776 2847819372787 17637266021154816 qz356 (@Enclosure.Real.IsNear.neg (Real.sin qz169) Bool.true 462379 1048576 34477597 50460622848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz169) Bool.true 462379 1048576 137910388 201842491392 462379 1048576 34477597 50460622848 (ep1003 rfl rfl) rfl)) rfl)

noncomputable def ep1005 := @ep977 232599984875 1099511627776 2855498937373 17637266021154816 Bool.false 114277432229 1099511627776 2847819372787 17637266021154816 Bool.false 20508357958974530650112 74608971623 1099511627776 222409913680693 52911798063464448 Bool.false 18538118742688380485632 269765132437 1099511627776 222587257330261 52911798063464448 (ep978 (BSN.head_sum_c_succ qz146 17 18 rfl rfl) (ep992 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep993 ep1004) rfl rfl

noncomputable abbrev qz170 := (@HMul.hMul Real Real Real qz267 qz443 qz570)

noncomputable def ep1006 := @Enclosure.Complex.IsNear.of_eq qz629 (Complex.mk (@HMul.hMul Real Real Real qz0 qz52 (Real.cos qz170)) (@HMul.hMul Real Real Real qz0 qz52 (@Neg.neg Real Real.instNeg (Real.sin qz170)))) Bool.false 240705019313 1099511627776 8330506476101 52911798063464448 Bool.true 75420779357 1099511627776 8297441932769 52911798063464448 (BSN.cpow_neg_s_mk qz149 130272 1000 19 qz150 rfl)

noncomputable def ep1007 := @Enclosure.Real.IsNear.mulLit_ff qz149 qz570 130272 1000 0 1 3315143513283831 1125899906842624 62500000048123 12030750000000000000 13495949242578476001 35184372088832000 84812500065302911 125320312500000000000 qz151 (BSN.isNear_log_sfrac 19 1 3315143513283831 1125899906842624 62500000048123 12030750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz357) Bool.false 55618878793361701994496 18889465931478580854784 1000000000769968 192492000000000000000 3315143513283831 1125899906842624 62500000048123 12030750000000000000 (BSN.log_rat_reduce_isNear 19 1 4 38 32 90099 524288 24973259072661432 36028797018963968 192492 1000000000000000 rfl rfl rfl rfl (ep316 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1008 := nat_lit 180791323084856407050058031537852416

noncomputable def ep1009 := BSN.cos_dyadic_bound_f 652070264 2147483648 2 1 1048576 385360 ep1008 ep96 ep1008 ep1008 ep97 ep1008 1000607 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 652070264) qz15 0 1 ep1008 ep96 ep1008 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 652070264) qz16 0 1 ep1008 ep97 ep1008 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz462 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 201105315) qz17)

noncomputable def ep1010 := @Enclosure.Real.IsNear.cos_image qz170 qz462 Bool.false 201105315 524288 355 524288 Bool.false 1000607 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz170 Bool.false 13495949242578476001 35184372088832000 84812500065302911 125320312500000000000 201105315 524288 355 524288 (ep1007 rfl) rfl) (Enclosure.sfrac_false_div 201105315 524288) (BSN.cos_reduce0 qz462 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 22942682802158483537920) qz19) 226375608064910080 72057594037927936 Bool.false 1000607 1048576 61 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q0 201105315 524288 226375608064910080 72057594037927936 61 22942682802158483537920 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1000607 1048576 22942682802158483537920 75557863725914323419136 652070264 2147483648 385360 384984 (ep1009 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1011 := BSN.sin_dyadic_bound_f 652070264 2147483648 2 1 1048576 385360 ep1008 ep92 ep1008 ep1008 ep93 ep1008 313523 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 652070264) qz20 0 1 ep1008 ep92 ep1008 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 652070264) qz21 0 1 ep1008 ep93 ep1008 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1012 := @Enclosure.Real.IsNear.sin_image qz170 qz462 Bool.false 201105315 524288 355 524288 Bool.false 313523 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz170 Bool.false 13495949242578476001 35184372088832000 84812500065302911 125320312500000000000 201105315 524288 355 524288 (ep1007 rfl) rfl) (Enclosure.sfrac_false_div 201105315 524288) (BSN.sin_reduce0 qz462 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 22942682802158483537920) qz19) 226375608064910080 72057594037927936 Bool.false 313523 1048576 61 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q0 201105315 524288 226375608064910080 72057594037927936 61 22942682802158483537920 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 313523 1048576 22942682802158483537920 75557863725914323419136 652070264 2147483648 385360 384984 (ep1011 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1013 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz52 (Real.cos qz170)) (@HMul.hMul Real Real Real qz0 qz52 (@Neg.neg Real Real.instNeg (Real.sin qz170))) Bool.false 240705019313 1099511627776 8330506476101 52911798063464448 Bool.true 75420779357 1099511627776 8297441932769 52911798063464448 (@Enclosure.Real.IsNear.mulLit_ff qz52 (Real.cos qz170) 240559 1048576 1 1048576 1000607 1048576 17214737 25230311424 240705019313 1099511627776 8330506476101 52911798063464448 qz359 (@Enclosure.Real.IsNear.recentre' (Real.cos qz170) Bool.false 1000607 1048576 68858948 100921245696 1000607 1048576 17214737 25230311424 (ep1010 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz52 (@Neg.neg Real Real.instNeg (Real.sin qz170)) 240559 1048576 1 1048576 313523 1048576 17214737 25230311424 75420779357 1099511627776 8297441932769 52911798063464448 qz359 (@Enclosure.Real.IsNear.neg (Real.sin qz170) Bool.false 313523 1048576 17214737 25230311424 (@Enclosure.Real.IsNear.recentre' (Real.sin qz170) Bool.false 313523 1048576 68858948 100921245696 313523 1048576 17214737 25230311424 (ep1012 rfl rfl) rfl)) rfl)

noncomputable def ep1014 := @ep975 240705019313 1099511627776 8330506476101 52911798063464448 Bool.true 75420779357 1099511627776 8297441932769 52911798063464448 Bool.false 346691399434588269838336 39414248867 137438953472 12818912230933 2939544336859136 Bool.false 213683876004064479150080 24293044135 137438953472 12826927736835 2939544336859136 (ep976 (BSN.head_sum_c_succ qz146 18 19 rfl rfl) (ep1005 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1006 ep1013) rfl rfl

noncomputable abbrev qz171 := (@HMul.hMul Real Real Real qz267 qz443 qz571)

noncomputable def ep1015 := @Enclosure.Complex.IsNear.of_eq qz628 (Complex.mk (@HMul.hMul Real Real Real qz0 qz54 (Real.cos qz171)) (@HMul.hMul Real Real Real qz0 qz54 (@Neg.neg Real Real.instNeg (Real.sin qz171)))) Bool.false 187658436495 1099511627776 8122477652255 52911798063464448 Bool.true 158841727457 1099511627776 8116563239309 52911798063464448 (BSN.cpow_neg_s_mk qz149 130272 1000 20 qz150 rfl)

noncomputable def ep1016 := @Enclosure.Real.IsNear.mulLit_ff qz149 qz571 130272 1000 0 1 3372893643545847 1125899906842624 62500000048123 12030750000000000000 13731050022875143137 35184372088832000 84812500065302911 125320312500000000000 qz151 (BSN.isNear_log_sfrac 20 1 3372893643545847 1125899906842624 62500000048123 12030750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz360) Bool.false 56587765202795681021952 18889465931478580854784 1000000000769968 192492000000000000000 3372893643545847 1125899906842624 62500000048123 12030750000000000000 (BSN.log_rat_reduce_isNear 20 1 4 40 32 116991 524288 24973259072661432 36028797018963968 192492 1000000000000000 rfl rfl rfl rfl (ep327 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1017 := nat_lit 185016085700898222649050845558586009324335106597626642459843997553035132716161

noncomputable def ep1018 := nat_lit 26806223457770912199154210811146630200435090759856469133657256115566462081

noncomputable def ep1019 := nat_lit 554994644655779126122754228254135734712604449611360214441264678146874265224321

noncomputable def ep1020 := BSN.cos_dyadic_bound_f 1508444911 2147483648 3 2 1048576 385360 ep1017 ep57 ep1018 ep1019 ep60 ep1018 800355 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1508444911) qz15 0 2 ep1017 ep57 ep1018 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1508444911) qz16 0 2 ep1019 ep60 ep1018 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz463 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 409217179) qz24)

noncomputable def ep1021 := @Enclosure.Real.IsNear.cos_image qz171 qz463 Bool.false 409217179 1048576 711 1048576 Bool.false 800355 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz171 Bool.false 13731050022875143137 35184372088832000 84812500065302911 125320312500000000000 409217179 1048576 711 1048576 (ep1016 rfl) rfl) (Enclosure.sfrac_false_div 409217179 1048576) (BSN.cos_reduce0 qz463 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 106147374092932242997248) qz25) 226375608064910080 72057594037927936 Bool.false 800355 1048576 62 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q0 409217179 1048576 226375608064910080 72057594037927936 62 106147374092932242997248 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 800355 1048576 106147374092932242997248 151115727451828646838272 1508444911 2147483648 385360 384984 (ep1020 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1022 := nat_lit 5177472690200394692870321328359922241

noncomputable def ep1023 := BSN.sin_dyadic_bound_f 1508444911 2147483648 2 1 1048576 385360 ep1022 ep92 ep1022 ep1022 ep93 ep1022 677453 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1508444911) qz20 0 1 ep1022 ep92 ep1022 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1508444911) qz21 0 1 ep1022 ep93 ep1022 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1024 := @Enclosure.Real.IsNear.sin_image qz171 qz463 Bool.false 409217179 1048576 711 1048576 Bool.false 677453 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz171 Bool.false 13731050022875143137 35184372088832000 84812500065302911 125320312500000000000 409217179 1048576 711 1048576 (ep1016 rfl) rfl) (Enclosure.sfrac_false_div 409217179 1048576) (BSN.sin_reduce0 qz463 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 106147374092932242997248) qz25) 226375608064910080 72057594037927936 Bool.false 677453 1048576 62 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q0 409217179 1048576 226375608064910080 72057594037927936 62 106147374092932242997248 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 677453 1048576 106147374092932242997248 151115727451828646838272 1508444911 2147483648 385360 384984 (ep1023 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1025 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz54 (Real.cos qz171)) (@HMul.hMul Real Real Real qz0 qz54 (@Neg.neg Real Real.instNeg (Real.sin qz171))) Bool.false 187658436495 1099511627776 8122477652255 52911798063464448 Bool.true 158841727457 1099511627776 8116563239309 52911798063464448 (@Enclosure.Real.IsNear.mulLit_ff qz54 (Real.cos qz171) 234469 1048576 1 1048576 800355 1048576 34477597 50460622848 187658436495 1099511627776 8122477652255 52911798063464448 qz362 (@Enclosure.Real.IsNear.recentre' (Real.cos qz171) Bool.false 800355 1048576 137910388 201842491392 800355 1048576 34477597 50460622848 (ep1021 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz54 (@Neg.neg Real Real.instNeg (Real.sin qz171)) 234469 1048576 1 1048576 677453 1048576 34477597 50460622848 158841727457 1099511627776 8116563239309 52911798063464448 qz362 (@Enclosure.Real.IsNear.neg (Real.sin qz171) Bool.false 677453 1048576 34477597 50460622848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz171) Bool.false 677453 1048576 137910388 201842491392 677453 1048576 34477597 50460622848 (ep1024 rfl rfl) rfl)) rfl)

noncomputable def ep1026 := @ep973 187658436495 1099511627776 8122477652255 52911798063464448 Bool.true 158841727457 1099511627776 8116563239309 52911798063464448 Bool.false 69128004051388105490432 502972427431 1099511627776 238862897809049 52911798063464448 Bool.false 4879443711133332013056 35502625623 1099511627776 239001262502339 52911798063464448 (ep974 (BSN.head_sum_c_succ qz146 19 20 rfl rfl) (ep1014 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1015 ep1025) rfl rfl

noncomputable abbrev qz172 := (@HMul.hMul Real Real Real qz267 qz443 qz572)

noncomputable def ep1027 := @Enclosure.Complex.IsNear.of_eq qz627 (Complex.mk (@HMul.hMul Real Real Real qz0 qz56 (Real.cos qz172)) (@HMul.hMul Real Real Real qz0 qz56 (@Neg.neg Real Real.instNeg (Real.sin qz172)))) Bool.false 21422284387 137438953472 496889862487 3306987378966528 Bool.true 20990047185 137438953472 124199739535 826746844741632 (BSN.cpow_neg_s_mk qz149 130272 1000 21 qz150 rfl)

noncomputable def ep1028 := @Enclosure.Real.IsNear.mulLit_ff qz149 qz572 130272 1000 0 1 3427826275261687 1125899906842624 62500000048123 12030750000000000000 13954680766590327777 35184372088832000 84812500065302911 125320312500000000000 qz151 (BSN.isNear_log_sfrac 21 1 3427826275261687 1125899906842624 62500000048123 12030750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz363) Bool.false 57509381830540779323392 18889465931478580854784 1000000000769968 192492000000000000000 3427826275261687 1125899906842624 62500000048123 12030750000000000000 (BSN.log_rat_reduce_isNear 21 1 4 42 32 142571 524288 24973259072661432 36028797018963968 192492 1000000000000000 rfl rfl rfl rfl (ep341 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1029 := nat_lit 274481809300901667947431849744038461778299187283035432114874005591470587890625

noncomputable def ep1030 := nat_lit 58990619019024168686287254548422322376505990738450055165983593902587890625

noncomputable def ep1031 := nat_lit 823327446664666955504922974723018540690144549867629396234290049586606587890625

noncomputable def ep1032 := BSN.cos_dyadic_bound_f 1664745575 2147483648 3 2 1048576 385360 ep1029 ep57 ep1030 ep1031 ep60 ep1030 748972 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1664745575) qz15 0 2 ep1029 ep57 ep1030 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1664745575) qz16 0 2 ep1031 ep60 ep1030 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz464 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 415881895) qz24)

noncomputable def ep1033 := @Enclosure.Real.IsNear.cos_image qz172 qz464 Bool.false 415881895 1048576 355 524288 Bool.false 748972 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz172 Bool.false 13954680766590327777 35184372088832000 84812500065302911 125320312500000000000 415881895 1048576 355 524288 (ep1028 rfl) rfl) (Enclosure.sfrac_false_div 415881895 1048576) (BSN.cos_reduce0 qz464 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 117146055496013478625280) qz25) 226375608064910080 72057594037927936 Bool.false 748972 1048576 63 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q0 415881895 1048576 226375608064910080 72057594037927936 63 117146055496013478625280 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 748972 1048576 117146055496013478625280 151115727451828646838272 1664745575 2147483648 385360 384984 (ep1032 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1034 := nat_lit 7680535073744808353063327979000390625

noncomputable def ep1035 := BSN.sin_dyadic_bound_f 1664745575 2147483648 2 1 1048576 385360 ep1034 ep92 ep1034 ep1034 ep93 ep1034 733860 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1664745575) qz20 0 1 ep1034 ep92 ep1034 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1664745575) qz21 0 1 ep1034 ep93 ep1034 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1036 := @Enclosure.Real.IsNear.sin_image qz172 qz464 Bool.false 415881895 1048576 355 524288 Bool.false 733860 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz172 Bool.false 13954680766590327777 35184372088832000 84812500065302911 125320312500000000000 415881895 1048576 355 524288 (ep1028 rfl) rfl) (Enclosure.sfrac_false_div 415881895 1048576) (BSN.sin_reduce0 qz464 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 117146055496013478625280) qz25) 226375608064910080 72057594037927936 Bool.false 733860 1048576 63 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q0 415881895 1048576 226375608064910080 72057594037927936 63 117146055496013478625280 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 733860 1048576 117146055496013478625280 151115727451828646838272 1664745575 2147483648 385360 384984 (ep1035 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1037 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz56 (Real.cos qz172)) (@HMul.hMul Real Real Real qz0 qz56 (@Neg.neg Real Real.instNeg (Real.sin qz172))) Bool.false 21422284387 137438953472 496889862487 3306987378966528 Bool.true 20990047185 137438953472 124199739535 826746844741632 (@Enclosure.Real.IsNear.mulLit_ff qz56 (Real.cos qz172) 114409 524288 1 524288 187243 262144 17214737 25230311424 21422284387 137438953472 496889862487 3306987378966528 qz365 (@Enclosure.Real.IsNear.recentre' (Real.cos qz172) Bool.false 748972 1048576 68858948 100921245696 187243 262144 17214737 25230311424 (ep1033 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz56 (@Neg.neg Real Real.instNeg (Real.sin qz172)) 114409 524288 1 524288 183465 262144 17214737 25230311424 20990047185 137438953472 124199739535 826746844741632 qz365 (@Enclosure.Real.IsNear.neg (Real.sin qz172) Bool.false 183465 262144 17214737 25230311424 (@Enclosure.Real.IsNear.recentre' (Real.sin qz172) Bool.false 733860 1048576 68858948 100921245696 183465 262144 17214737 25230311424 (ep1036 rfl rfl) rfl)) rfl)

noncomputable def ep1038 := @ep971 21422284387 137438953472 496889862487 3306987378966528 Bool.true 20990047185 137438953472 124199739535 826746844741632 Bool.false 92682054828418865823744 674350702527 1099511627776 82271045202947 17637266021154816 Bool.true 18199357236341064597504 132417751857 1099511627776 82316681944193 17637266021154816 (ep972 (BSN.head_sum_c_succ qz146 20 21 rfl rfl) (ep1026 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1027 ep1037) rfl rfl

noncomputable abbrev qz173 := (@HMul.hMul Real Real Real qz267 qz443 qz573)

noncomputable def ep1039 := @Enclosure.Complex.IsNear.of_eq qz626 (Complex.mk (@HMul.hMul Real Real Real qz0 qz58 (Real.cos qz173)) (@HMul.hMul Real Real Real qz0 qz58 (@Neg.neg Real Real.instNeg (Real.sin qz173)))) Bool.false 99781313595 549755813888 3869971153451 26455899031732224 Bool.true 122986977309 1099511627776 7723458591343 52911798063464448 (BSN.cpow_neg_s_mk qz149 130272 1000 22 qz150 rfl)

noncomputable def ep1040 := @Enclosure.Real.IsNear.mulLit_ff qz149 qz573 130272 1000 0 1 3480203401436407 1125899906842624 62500000048123 12030750000000000000 14167908047247612897 35184372088832000 84812500065302911 125320312500000000000 qz151 (BSN.isNear_log_sfrac 22 1 3480203401436407 1125899906842624 62500000048123 12030750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz366) Bool.false 58388124189833310502912 18889465931478580854784 1000000000769968 192492000000000000000 3480203401436407 1125899906842624 62500000048123 12030750000000000000 (BSN.log_rat_reduce_isNear 22 1 4 44 32 166961 524288 24973259072661432 36028797018963968 192492 1000000000000000 rfl rfl rfl rfl (ep355 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1041 := nat_lit 1978965662372367916159123101660062736

noncomputable def ep1042 := BSN.cos_dyadic_bound_f 1186067934 2147483648 2 1 1048576 385360 ep1041 ep96 ep1041 ep1041 ep97 ep1041 892670 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1186067934) qz15 0 1 ep1041 ep96 ep1041 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1186067934) qz16 0 1 ep1041 ep97 ep1041 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz465 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 422236563) qz24)

noncomputable def ep1043 := @Enclosure.Real.IsNear.cos_image qz173 qz465 Bool.false 422236563 1048576 355 524288 Bool.false 892670 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz173 Bool.false 14167908047247612897 35184372088832000 84812500065302911 125320312500000000000 422236563 1048576 355 524288 (ep1040 rfl) rfl) (Enclosure.sfrac_false_div 422236563 1048576) (BSN.cos_reduce0 qz465 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 83462111066551752851456) qz25) 226375608064910080 72057594037927936 Bool.false 892670 1048576 64 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q0 422236563 1048576 226375608064910080 72057594037927936 64 83462111066551752851456 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 892670 1048576 83462111066551752851456 151115727451828646838272 1186067934 2147483648 385360 384984 (ep1042 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1044 := BSN.sin_dyadic_bound_f 1186067934 2147483648 2 1 1048576 385360 ep1041 ep92 ep1041 ep1041 ep93 ep1041 550137 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1186067934) qz20 0 1 ep1041 ep92 ep1041 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1186067934) qz21 0 1 ep1041 ep93 ep1041 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1045 := @Enclosure.Real.IsNear.sin_image qz173 qz465 Bool.false 422236563 1048576 355 524288 Bool.false 550137 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz173 Bool.false 14167908047247612897 35184372088832000 84812500065302911 125320312500000000000 422236563 1048576 355 524288 (ep1040 rfl) rfl) (Enclosure.sfrac_false_div 422236563 1048576) (BSN.sin_reduce0 qz465 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 83462111066551752851456) qz25) 226375608064910080 72057594037927936 Bool.false 550137 1048576 64 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q0 422236563 1048576 226375608064910080 72057594037927936 64 83462111066551752851456 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 550137 1048576 83462111066551752851456 151115727451828646838272 1186067934 2147483648 385360 384984 (ep1044 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1046 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz58 (Real.cos qz173)) (@HMul.hMul Real Real Real qz0 qz58 (@Neg.neg Real Real.instNeg (Real.sin qz173))) Bool.false 99781313595 549755813888 3869971153451 26455899031732224 Bool.true 122986977309 1099511627776 7723458591343 52911798063464448 (@Enclosure.Real.IsNear.mulLit_ff qz58 (Real.cos qz173) 223557 1048576 1 1048576 446335 524288 17214737 25230311424 99781313595 549755813888 3869971153451 26455899031732224 qz368 (@Enclosure.Real.IsNear.recentre' (Real.cos qz173) Bool.false 892670 1048576 68858948 100921245696 446335 524288 17214737 25230311424 (ep1043 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz58 (@Neg.neg Real Real.instNeg (Real.sin qz173)) 223557 1048576 1 1048576 550137 1048576 17214737 25230311424 122986977309 1099511627776 7723458591343 52911798063464448 qz368 (@Enclosure.Real.IsNear.neg (Real.sin qz173) Bool.false 550137 1048576 17214737 25230311424 (@Enclosure.Real.IsNear.recentre' (Real.sin qz173) Bool.false 550137 1048576 68858948 100921245696 550137 1048576 17214737 25230311424 (ep1045 rfl rfl) rfl)) rfl)

noncomputable def ep1047 := @ep969 99781313595 549755813888 3869971153451 26455899031732224 Bool.true 122986977309 1099511627776 7723458591343 52911798063464448 Bool.false 480438933846141431709696 873913329717 1099511627776 254553077915743 52911798063464448 Bool.true 280820469506997082914816 127702364583 549755813888 127336752211961 26455899031732224 (ep970 (BSN.head_sum_c_succ qz146 21 22 rfl rfl) (ep1038 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1039 ep1046) rfl rfl

noncomputable abbrev qz174 := (@HMul.hMul Real Real Real qz267 qz443 qz574)

noncomputable def ep1048 := @Enclosure.Complex.IsNear.of_eq qz625 (Complex.mk (@HMul.hMul Real Real Real qz0 qz60 (Real.cos qz174)) (@HMul.hMul Real Real Real qz0 qz60 (@Neg.neg Real Real.instNeg (Real.sin qz174)))) Bool.false 57213407025 274877906944 1894542064339 13227949515866112 Bool.true 6852052977 549755813888 3765407083325 26455899031732224 (BSN.cpow_neg_s_mk qz149 130272 1000 23 qz150 rfl)

noncomputable def ep1049 := @Enclosure.Real.IsNear.mulLit_ff qz149 qz574 130272 1000 0 1 3530250507853047 1125899906842624 62500000048123 12030750000000000000 14371649817469754337 35184372088832000 84812500065302911 125320312500000000000 qz151 (BSN.isNear_log_sfrac 23 1 3530250507853047 1125899906842624 62500000048123 12030750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz369) Bool.false 59227775304360265777152 18889465931478580854784 1000000000769968 192492000000000000000 3530250507853047 1125899906842624 62500000048123 12030750000000000000 (BSN.log_rat_reduce_isNear 23 1 4 46 32 190266 524288 24973259072661432 36028797018963968 192492 1000000000000000 rfl rfl rfl rfl (ep366 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1050 := BSN.cos_dyadic_bound_f 128441174 2147483648 1 0 1048576 385360 0 1 1 0 1 1 1046700 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 128441174) qz15 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 128441174) qz16 0 0 rfl) rfl rfl

noncomputable abbrev qz466 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 428308541) qz24)

noncomputable def ep1051 := @Enclosure.Real.IsNear.cos_image qz174 qz466 Bool.false 428308541 1048576 355 524288 Bool.false 1046700 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz174 Bool.false 14371649817469754337 35184372088832000 84812500065302911 125320312500000000000 428308541 1048576 355 524288 (ep1049 rfl) rfl) (Enclosure.sfrac_false_div 428308541 1048576) (BSN.cos_reduce0 qz466 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9038244119926330621952) qz25) 226375608064910080 72057594037927936 Bool.false 1046700 1048576 65 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q0 428308541 1048576 226375608064910080 72057594037927936 65 9038244119926330621952 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1046700 1048576 9038244119926330621952 151115727451828646838272 128441174 2147483648 385360 384984 (ep1050 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1052 := BSN.sin_dyadic_bound_f 128441174 2147483648 1 0 1048576 385360 0 1 1 0 1 1 62678 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 128441174) qz20 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 128441174) qz21 0 0 rfl) rfl rfl

noncomputable def ep1053 := @Enclosure.Real.IsNear.sin_image qz174 qz466 Bool.false 428308541 1048576 355 524288 Bool.false 62678 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz174 Bool.false 14371649817469754337 35184372088832000 84812500065302911 125320312500000000000 428308541 1048576 355 524288 (ep1049 rfl) rfl) (Enclosure.sfrac_false_div 428308541 1048576) (BSN.sin_reduce0 qz466 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9038244119926330621952) qz25) 226375608064910080 72057594037927936 Bool.false 62678 1048576 65 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q0 428308541 1048576 226375608064910080 72057594037927936 65 9038244119926330621952 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 62678 1048576 9038244119926330621952 151115727451828646838272 128441174 2147483648 385360 384984 (ep1052 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1054 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz60 (Real.cos qz174)) (@HMul.hMul Real Real Real qz0 qz60 (@Neg.neg Real Real.instNeg (Real.sin qz174))) Bool.false 57213407025 274877906944 1894542064339 13227949515866112 Bool.true 6852052977 549755813888 3765407083325 26455899031732224 (@Enclosure.Real.IsNear.mulLit_ff qz60 (Real.cos qz174) 218643 1048576 1 1048576 261675 262144 17214737 25230311424 57213407025 274877906944 1894542064339 13227949515866112 qz372 (@Enclosure.Real.IsNear.recentre' (Real.cos qz174) Bool.false 1046700 1048576 68858948 100921245696 261675 262144 17214737 25230311424 (ep1051 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz60 (@Neg.neg Real Real.instNeg (Real.sin qz174)) 218643 1048576 1 1048576 31339 524288 17214737 25230311424 6852052977 549755813888 3765407083325 26455899031732224 qz372 (@Enclosure.Real.IsNear.neg (Real.sin qz174) Bool.false 31339 524288 17214737 25230311424 (@Enclosure.Real.IsNear.recentre' (Real.sin qz174) Bool.false 62678 1048576 68858948 100921245696 31339 524288 17214737 25230311424 (ep1053 rfl rfl) rfl)) rfl)

noncomputable def ep1055 := @ep967 57213407025 274877906944 1894542064339 13227949515866112 Bool.true 6852052977 549755813888 3765407083325 26455899031732224 Bool.false 303126273211739299381248 1102766957817 1099511627776 262131246173099 52911798063464448 Bool.true 73972073337923599073280 16819302195 68719476736 65551079647643 13227949515866112 (ep968 (BSN.head_sum_c_succ qz146 22 23 rfl rfl) (ep1047 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1048 ep1054) rfl rfl

noncomputable abbrev qz175 := (@HMul.hMul Real Real Real qz267 qz443 qz575)

noncomputable def ep1056 := @Enclosure.Complex.IsNear.of_eq qz624 (Complex.mk (@HMul.hMul Real Real Real qz0 qz62 (Real.cos qz175)) (@HMul.hMul Real Real Real qz0 qz62 (@Neg.neg Real Real.instNeg (Real.sin qz175)))) Bool.false 43666738507 274877906944 1854713933069 13227949515866112 Bool.false 140935905901 1099511627776 7411271884337 52911798063464448 (BSN.cpow_neg_s_mk qz149 130272 1000 24 qz150 rfl)

noncomputable def ep1057 := @Enclosure.Real.IsNear.mulLit_ff qz149 qz575 130272 1000 0 1 3578169457974519 1125899906842624 62500000048123 12030750000000000000 14566727863414266849 35184372088832000 84812500065302911 125320312500000000000 qz151 (BSN.isNear_log_sfrac 24 1 3578169457974519 1125899906842624 62500000048123 12030750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz373) Bool.false 60031721881041427759104 18889465931478580854784 1000000000769968 192492000000000000000 3578169457974519 1125899906842624 62500000048123 12030750000000000000 (BSN.log_rat_reduce_isNear 24 1 4 48 32 212580 524288 24973259072661432 36028797018963968 192492 1000000000000000 rfl rfl rfl rfl (ep381 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1058 := nat_lit 865608314373261585762823615478582335116713940486233122402955630150061875101825

noncomputable def ep1059 := nat_lit 181075053698649585591769946359472212521316515725003249280298450713121226881

noncomputable def ep1060 := nat_lit 2266776225652553958621198984435514589342549617390865315318429976710912238518401

noncomputable def ep1061 := BSN.sin_dyadic_bound_f 1915280239 2147483648 3 2 1048576 385360 ep1058 ep64 ep1059 ep1060 ep66 ep1059 816052 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1915280239) qz20 0 2 ep1058 ep64 ep1059 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1915280239) qz21 0 2 ep1060 ep66 ep1059 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz467 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 434122319) qz24)

noncomputable def ep1062 := @Enclosure.Real.IsNear.cos_image qz175 qz467 Bool.false 434122319 1048576 711 1048576 Bool.false 816052 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz175 Bool.false 14566727863414266849 35184372088832000 84812500065302911 125320312500000000000 434122319 1048576 711 1048576 (ep1057 rfl) rfl) (Enclosure.sfrac_false_div 434122319 1048576) (BSN.cos_reduce3 qz467 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 134775865214386074288128) qz25) 226375608064910080 72057594037927936 Bool.false 816052 1048576 65 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q3 434122319 1048576 226375608064910080 72057594037927936 65 134775865214386074288128 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 816052 1048576 134775865214386074288128 151115727451828646838272 1915280239 2147483648 385360 384984 (ep1061 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1063 := nat_lit 480973985786789169684053906353149951603739440943785069445766593839240206712961

noncomputable def ep1064 := nat_lit 1442559807252970209880978179166730910386175689799905201838739184616294377685121

noncomputable def ep1065 := BSN.cos_dyadic_bound_f 1915280239 2147483648 3 2 1048576 385360 ep1063 ep57 ep1059 ep1064 ep60 ep1059 658459 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1915280239) qz15 0 2 ep1063 ep57 ep1059 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1915280239) qz16 0 2 ep1064 ep60 ep1059 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1066 := @Enclosure.Real.IsNear.sin_image qz175 qz467 Bool.false 434122319 1048576 711 1048576 Bool.true 658459 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz175 Bool.false 14566727863414266849 35184372088832000 84812500065302911 125320312500000000000 434122319 1048576 711 1048576 (ep1057 rfl) rfl) (Enclosure.sfrac_false_div 434122319 1048576) (BSN.sin_reduce3 qz467 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 134775865214386074288128) qz25) 226375608064910080 72057594037927936 Bool.false 658459 1048576 65 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q3 434122319 1048576 226375608064910080 72057594037927936 65 134775865214386074288128 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 658459 1048576 134775865214386074288128 151115727451828646838272 1915280239 2147483648 385360 384984 (ep1065 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1067 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz62 (Real.cos qz175)) (@HMul.hMul Real Real Real qz0 qz62 (@Neg.neg Real Real.instNeg (Real.sin qz175))) Bool.false 43666738507 274877906944 1854713933069 13227949515866112 Bool.false 140935905901 1099511627776 7411271884337 52911798063464448 (@Enclosure.Real.IsNear.mulLit_ff qz62 (Real.cos qz175) 214039 1048576 1 1048576 204013 262144 34477597 50460622848 43666738507 274877906944 1854713933069 13227949515866112 qz375 (@Enclosure.Real.IsNear.recentre' (Real.cos qz175) Bool.false 816052 1048576 137910388 201842491392 204013 262144 34477597 50460622848 (ep1062 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz62 (@Neg.neg Real Real.instNeg (Real.sin qz175)) 214039 1048576 1 1048576 658459 1048576 34477597 50460622848 140935905901 1099511627776 7411271884337 52911798063464448 qz375 (@Enclosure.Real.IsNear.neg (Real.sin qz175) Bool.true 658459 1048576 34477597 50460622848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz175) Bool.true 658459 1048576 137910388 201842491392 658459 1048576 34477597 50460622848 (ep1066 rfl rfl) rfl)) rfl)

noncomputable def ep1068 := @ep965 43666738507 274877906944 1854713933069 13227949515866112 Bool.false 140935905901 1099511627776 7411271884337 52911798063464448 Bool.false 351138359947239809351680 1277433911845 1099511627776 269550101905375 52911798063464448 Bool.true 8807976627650045149184 128172929219 1099511627776 269615590474909 52911798063464448 (ep966 (BSN.head_sum_c_succ qz146 23 24 rfl rfl) (ep1055 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1056 ep1067) rfl rfl

theorem EMRow43.d15 : Enclosure.Complex.IsNear qz167 Bool.false 1277433911845 1099511627776 269550101905375 52911798063464448 Bool.true 128172929219 1099511627776 269615590474909 52911798063464448 := ep964 (BSN.head_sum_c_succ qz146 24 25 rfl rfl) (ep1068 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz632 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 32) qz147)

noncomputable def ep1069 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 33) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 32) qz632) Bool.false 596571813335 549755813888 40509647116639 6613974757933056 Bool.false 10816593261 274877906944 162090471942145 26455899031732224

noncomputable def ep1070 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 32) qz632 Bool.false 1072474723389 1099511627776 317654944195403 52911798063464448 Bool.true 109106647031 1099511627776 317750480284907 52911798063464448 Bool.false

noncomputable def ep1071 := nat_lit 1311875291130491746385920

noncomputable abbrev qz633 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 31) qz147)

noncomputable def ep1072 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 32) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 31) qz633) Bool.false 1072474723389 1099511627776 317654944195403 52911798063464448 Bool.true 109106647031 1099511627776 317750480284907 52911798063464448

noncomputable def ep1073 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 31) qz633 Bool.false 252371316101 274877906944 51857613815533 8818633010577408 Bool.false 78055089827 1099511627776 103736496569417 17637266021154816 Bool.false

noncomputable abbrev qz634 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 30) qz147)

noncomputable def ep1074 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 31) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 30) qz634) Bool.false 252371316101 274877906944 51857613815533 8818633010577408 Bool.false 78055089827 1099511627776 103736496569417 17637266021154816

noncomputable def ep1075 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 30) qz634 Bool.false 1208879083637 1099511627776 304504245076429 52911798063464448 Bool.false 27412793825 549755813888 152306167145549 26455899031732224 Bool.true

noncomputable abbrev qz635 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 29) qz147)

noncomputable def ep1076 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 30) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 29) qz635) Bool.false 1208879083637 1099511627776 304504245076429 52911798063464448 Bool.false 27412793825 549755813888 152306167145549 26455899031732224

noncomputable def ep1077 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 29) qz635 Bool.false 1127121760007 1099511627776 33085633257499 5879088673718272 Bool.true 4133249485 34359738368 8273687669627 1469772168429568 Bool.false

noncomputable abbrev qz636 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 28) qz147)

noncomputable def ep1078 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 29) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 28) qz636) Bool.false 1127121760007 1099511627776 33085633257499 5879088673718272 Bool.true 4133249485 34359738368 8273687669627 1469772168429568

noncomputable def ep1079 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 28) qz636 Bool.false 475148971331 549755813888 145447769955419 26455899031732224 Bool.true 2891655183 137438953472 9093563614409 1653493689483264 Bool.false

noncomputable abbrev qz637 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 27) qz147)

noncomputable def ep1080 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 28) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 27) qz637) Bool.false 475148971331 549755813888 145447769955419 26455899031732224 Bool.true 2891655183 137438953472 9093563614409 1653493689483264

noncomputable def ep1081 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 27) qz637 Bool.false 528423100135 549755813888 141961131749311 26455899031732224 Bool.false 9980334487 68719476736 35500321383097 6613974757933056 Bool.true

noncomputable abbrev qz638 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 26) qz147)

noncomputable def ep1082 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 27) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 26) qz638) Bool.false 528423100135 549755813888 141961131749311 26455899031732224 Bool.false 9980334487 68719476736 35500321383097 6613974757933056

noncomputable def ep1083 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 26) qz638 Bool.false 630646179005 549755813888 138392154808507 26455899031732224 Bool.false 45567951443 549755813888 138448209345121 26455899031732224 Bool.true

noncomputable abbrev qz639 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 25) qz147)

noncomputable def ep1084 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 26) (@HAdd.hAdd Complex Complex Complex qz4 qz167 qz639) Bool.false 630646179005 549755813888 138392154808507 26455899031732224 Bool.false 45567951443 549755813888 138448209345121 26455899031732224

noncomputable def ep1085 := @Enclosure.Complex.IsNear.addLitP qz167 qz639 Bool.false 1277433911845 1099511627776 269550101905375 52911798063464448 Bool.true 128172929219 1099511627776 269615590474909 52911798063464448 Bool.true

noncomputable def ep1086 := nat_lit 1386805613657004452085760

noncomputable abbrev qz176 := (@HMul.hMul Real Real Real qz267 qz443 qz584)

noncomputable def ep1087 := @Enclosure.Complex.IsNear.of_eq qz639 (Complex.mk (@HMul.hMul Real Real Real qz0 qz64 (Real.cos qz176)) (@HMul.hMul Real Real Real qz0 qz64 (@Neg.neg Real Real.instNeg (Real.sin qz176)))) Bool.true 16141553835 1099511627776 7234207711639 52911798063464448 Bool.false 219308832105 1099511627776 7280828215333 52911798063464448 (BSN.cpow_neg_s_mk qz149 130272 1000 25 qz150 rfl)

noncomputable def ep1088 := @Enclosure.Real.IsNear.mulLit_ff qz149 qz584 130272 1000 0 1 3624129903009015 1125899906842624 62500000048123 12030750000000000000 2950766567029940013 7036874417766400 84812500065302911 125320312500000000000 qz151 (BSN.isNear_log_sfrac 25 1 3624129903009015 1125899906842624 62500000048123 12030750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz376) Bool.false 60802810194841294602240 18889465931478580854784 1000000000769968 192492000000000000000 3624129903009015 1125899906842624 62500000048123 12030750000000000000 (BSN.log_rat_reduce_isNear 25 1 4 50 32 233982 524288 24973259072661432 36028797018963968 192492 1000000000000000 rfl rfl rfl rfl (ep411 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1089 := nat_lit 3830994191859385943274474841620759230928666823144879601673086840142242934690625

noncomputable def ep1090 := nat_lit 11428009453209824877217858439490184096447467572342167400232597978240937890625

noncomputable def ep1091 := nat_lit 11470126556671738180068988807983297324593105534289954470218795324470246928290625

noncomputable def ep1092 := BSN.cos_dyadic_bound_f 3215483785 2147483648 3 2 1048576 385360 ep1089 ep57 ep1090 ep1091 ep60 ep1090 76969 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3215483785) qz15 0 2 ep1089 ep57 ep1090 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3215483785) qz16 0 2 ep1091 ep60 ep1090 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz468 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 219849241) qz17)

noncomputable def ep1093 := @Enclosure.Real.IsNear.cos_image qz176 qz468 Bool.false 219849241 524288 711 1048576 Bool.true 76969 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz176 Bool.false 2950766567029940013 7036874417766400 84812500065302911 125320312500000000000 219849241 524288 711 1048576 (ep1088 rfl) rfl) (Enclosure.sfrac_false_div 219849241 524288) (BSN.cos_reduce2 qz468 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 113134777947100662464512) qz19) 226375608064910080 72057594037927936 Bool.false 76969 1048576 66 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q2 219849241 524288 226375608064910080 72057594037927936 66 113134777947100662464512 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 76969 1048576 113134777947100662464512 75557863725914323419136 3215483785 2147483648 385360 384984 (ep1092 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1094 := nat_lit 6886647137784326837992280428165774468394442307602909549091370233873444532130625

noncomputable def ep1095 := nat_lit 18017954297939468668750000779151187119162624429557161500400831168179964637090625

noncomputable def ep1096 := BSN.sin_dyadic_bound_f 3215483785 2147483648 3 2 1048576 385360 ep1094 ep64 ep1090 ep1095 ep66 ep1090 1045747 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3215483785) qz20 0 2 ep1094 ep64 ep1090 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3215483785) qz21 0 2 ep1095 ep66 ep1090 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1097 := @Enclosure.Real.IsNear.sin_image qz176 qz468 Bool.false 219849241 524288 711 1048576 Bool.true 1045747 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz176 Bool.false 2950766567029940013 7036874417766400 84812500065302911 125320312500000000000 219849241 524288 711 1048576 (ep1088 rfl) rfl) (Enclosure.sfrac_false_div 219849241 524288) (BSN.sin_reduce2 qz468 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 113134777947100662464512) qz19) 226375608064910080 72057594037927936 Bool.false 1045747 1048576 66 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q2 219849241 524288 226375608064910080 72057594037927936 66 113134777947100662464512 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1045747 1048576 113134777947100662464512 75557863725914323419136 3215483785 2147483648 385360 384984 (ep1096 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1098 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz64 (Real.cos qz176)) (@HMul.hMul Real Real Real qz0 qz64 (@Neg.neg Real Real.instNeg (Real.sin qz176))) Bool.true 16141553835 1099511627776 7234207711639 52911798063464448 Bool.false 219308832105 1099511627776 7280828215333 52911798063464448 (@Enclosure.Real.IsNear.mulLit_ft qz64 (Real.cos qz176) 209715 1048576 1 1048576 76969 1048576 34477597 50460622848 16141553835 1099511627776 7234207711639 52911798063464448 qz378 (@Enclosure.Real.IsNear.recentre' (Real.cos qz176) Bool.true 76969 1048576 137910388 201842491392 76969 1048576 34477597 50460622848 (ep1093 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz64 (@Neg.neg Real Real.instNeg (Real.sin qz176)) 209715 1048576 1 1048576 1045747 1048576 34477597 50460622848 219308832105 1099511627776 7280828215333 52911798063464448 qz378 (@Enclosure.Real.IsNear.neg (Real.sin qz176) Bool.true 1045747 1048576 34477597 50460622848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz176) Bool.true 1045747 1048576 137910388 201842491392 1045747 1048576 34477597 50460622848 (ep1097 rfl rfl) rfl)) rfl)

noncomputable def ep1099 := @ep1085 16141553835 1099511627776 7234207711639 52911798063464448 Bool.false 219308832105 1099511627776 7280828215333 52911798063464448 Bool.false ep1086 630646179005 549755813888 138392154808507 26455899031732224 Bool.false 100204984931021316161536 45567951443 549755813888 138448209345121 26455899031732224 EMRow43.d15 (ep1087 ep1098) rfl rfl

noncomputable abbrev qz177 := (@HMul.hMul Real Real Real qz267 qz443 qz585)

noncomputable def ep1100 := @Enclosure.Complex.IsNear.of_eq qz638 (Complex.mk (@HMul.hMul Real Real Real qz0 qz66 (Real.cos qz177)) (@HMul.hMul Real Real Real qz0 qz66 (@Neg.neg Real Real.instNeg (Real.sin qz177)))) Bool.true 51111539435 274877906944 297414745067 2204658252644352 Bool.false 34274724453 549755813888 1184358729089 8818633010577408 (BSN.cpow_neg_s_mk qz149 130272 1000 26 qz150 rfl)

noncomputable def ep1101 := @Enclosure.Real.IsNear.mulLit_ff qz149 qz585 130272 1000 0 1 3668288609262839 1125899906842624 62500000048123 12030750000000000000 14933602928309017569 35184372088832000 84812500065302911 125320312500000000000 qz151 (BSN.isNear_log_sfrac 26 1 3668288609262839 1125899906842624 62500000048123 12030750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz379) Bool.false 61543670347942250676224 18889465931478580854784 1000000000769968 192492000000000000000 3668288609262839 1125899906842624 62500000048123 12030750000000000000 (BSN.log_rat_reduce_isNear 26 1 4 52 32 254545 524288 24973259072661432 36028797018963968 192492 1000000000000000 rfl rfl rfl rfl (ep426 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1102 := nat_lit 232965889971769889411905610387030016

noncomputable def ep1103 := BSN.cos_dyadic_bound_f 694741248 2147483648 2 1 1048576 385360 ep1102 ep96 ep1102 ep1102 ep97 ep1102 994180 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 694741248) qz15 0 1 ep1102 ep96 ep1102 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 694741248) qz16 0 1 ep1102 ep97 ep1102 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz469 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 27816003) (@Nat.cast Real Real.instNatCast 65536))

noncomputable def ep1104 := @Enclosure.Real.IsNear.cos_image qz177 qz469 Bool.false 27816003 65536 711 1048576 Bool.true 994180 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz177 Bool.false 14933602928309017569 35184372088832000 84812500065302911 125320312500000000000 27816003 65536 711 1048576 (ep1101 rfl) rfl) (Enclosure.sfrac_false_div 27816003 65536) (BSN.cos_reduce2 qz469 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3055504325245472342016) qz337) 226375608064910080 72057594037927936 Bool.false 994180 1048576 67 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q2 27816003 65536 226375608064910080 72057594037927936 67 3055504325245472342016 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 994180 1048576 3055504325245472342016 9444732965739290427392 694741248 2147483648 385360 384984 (ep1103 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1105 := BSN.sin_dyadic_bound_f 694741248 2147483648 2 1 1048576 385360 ep1102 ep92 ep1102 ep1102 ep93 ep1102 333342 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 694741248) qz20 0 1 ep1102 ep92 ep1102 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 694741248) qz21 0 1 ep1102 ep93 ep1102 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1106 := @Enclosure.Real.IsNear.sin_image qz177 qz469 Bool.false 27816003 65536 711 1048576 Bool.true 333342 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz177 Bool.false 14933602928309017569 35184372088832000 84812500065302911 125320312500000000000 27816003 65536 711 1048576 (ep1101 rfl) rfl) (Enclosure.sfrac_false_div 27816003 65536) (BSN.sin_reduce2 qz469 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3055504325245472342016) qz337) 226375608064910080 72057594037927936 Bool.false 333342 1048576 67 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q2 27816003 65536 226375608064910080 72057594037927936 67 3055504325245472342016 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 333342 1048576 3055504325245472342016 9444732965739290427392 694741248 2147483648 385360 384984 (ep1105 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1107 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz66 (Real.cos qz177)) (@HMul.hMul Real Real Real qz0 qz66 (@Neg.neg Real Real.instNeg (Real.sin qz177))) Bool.true 51111539435 274877906944 297414745067 2204658252644352 Bool.false 34274724453 549755813888 1184358729089 8818633010577408 (@Enclosure.Real.IsNear.mulLit_ft qz66 (Real.cos qz177) 205643 1048576 1 1048576 248545 262144 34477597 50460622848 51111539435 274877906944 297414745067 2204658252644352 qz381 (@Enclosure.Real.IsNear.recentre' (Real.cos qz177) Bool.true 994180 1048576 137910388 201842491392 248545 262144 34477597 50460622848 (ep1104 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz66 (@Neg.neg Real Real.instNeg (Real.sin qz177)) 205643 1048576 1 1048576 166671 524288 34477597 50460622848 34274724453 549755813888 1184358729089 8818633010577408 qz381 (@Enclosure.Real.IsNear.neg (Real.sin qz177) Bool.true 166671 524288 34477597 50460622848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz177) Bool.true 333342 1048576 137910388 201842491392 166671 524288 34477597 50460622848 (ep1106 rfl rfl) rfl)) rfl)

noncomputable def ep1108 := @ep1083 51111539435 274877906944 297414745067 2204658252644352 Bool.false 34274724453 549755813888 1184358729089 8818633010577408 Bool.false 145251835745968523837440 528423100135 549755813888 141961131749311 26455899031732224 Bool.false 43893975270201279643648 9980334487 68719476736 35500321383097 6613974757933056 (ep1084 (BSN.head_sum_c_succ qz146 25 26 rfl rfl) (ep1099 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1100 ep1107) rfl rfl

noncomputable abbrev qz178 := (@HMul.hMul Real Real Real qz267 qz443 qz586)

noncomputable def ep1109 := @Enclosure.Complex.IsNear.of_eq qz637 (Complex.mk (@HMul.hMul Real Real Real qz0 qz68 (Real.cos qz178)) (@HMul.hMul Real Real Real qz0 qz68 (@Neg.neg Real Real.instNeg (Real.sin qz178)))) Bool.true 13318532201 137438953472 871659551527 6613974757933056 Bool.true 22852324157 137438953472 873933074539 6613974757933056 (BSN.cpow_neg_s_mk qz149 130272 1000 27 qz150 rfl)

noncomputable def ep1110 := @Enclosure.Real.IsNear.mulLit_ff qz149 qz586 130272 1000 0 1 3710780868205815 1125899906842624 62500000048123 12030750000000000000 3021317782893174573 7036874417766400 84812500065302911 125320312500000000000 qz151 (BSN.isNear_log_sfrac 27 1 3710780868205815 1125899906842624 62500000048123 12030750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz382) Bool.false 62256572154556490711040 18889465931478580854784 1000000000769968 192492000000000000000 3710780868205815 1125899906842624 62500000048123 12030750000000000000 (BSN.log_rat_reduce_isNear 27 1 4 54 32 274332 524288 24973259072661432 36028797018963968 192492 1000000000000000 rfl rfl rfl rfl (ep441 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1111 := nat_lit 1648971525617925029883391375506250000

noncomputable def ep1112 := BSN.sin_dyadic_bound_f 1133191450 2147483648 2 1 1048576 385360 ep1111 ep92 ep1111 ep1111 ep93 ep1111 527992 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1133191450) qz20 0 1 ep1111 ep92 ep1111 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1133191450) qz21 0 1 ep1111 ep93 ep1111 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz470 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 450211433) qz24)

noncomputable def ep1113 := @Enclosure.Real.IsNear.cos_image qz178 qz470 Bool.false 450211433 1048576 355 524288 Bool.true 527992 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz178 Bool.false 3021317782893174573 7036874417766400 84812500065302911 125320312500000000000 450211433 1048576 355 524288 (ep1110 rfl) rfl) (Enclosure.sfrac_false_div 450211433 1048576) (BSN.cos_reduce1 qz470 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 79741259275560326004736) qz25) 226375608064910080 72057594037927936 Bool.false 527992 1048576 68 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q1 450211433 1048576 226375608064910080 72057594037927936 68 79741259275560326004736 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 527992 1048576 79741259275560326004736 151115727451828646838272 1133191450 2147483648 385360 384984 (ep1112 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1114 := BSN.cos_dyadic_bound_f 1133191450 2147483648 2 1 1048576 385360 ep1111 ep96 ep1111 ep1111 ep97 ep1111 905944 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1133191450) qz15 0 1 ep1111 ep96 ep1111 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1133191450) qz16 0 1 ep1111 ep97 ep1111 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1115 := @Enclosure.Real.IsNear.sin_image qz178 qz470 Bool.false 450211433 1048576 355 524288 Bool.false 905944 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz178 Bool.false 3021317782893174573 7036874417766400 84812500065302911 125320312500000000000 450211433 1048576 355 524288 (ep1110 rfl) rfl) (Enclosure.sfrac_false_div 450211433 1048576) (BSN.sin_reduce1 qz470 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 79741259275560326004736) qz25) 226375608064910080 72057594037927936 Bool.false 905944 1048576 68 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q1 450211433 1048576 226375608064910080 72057594037927936 68 79741259275560326004736 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 905944 1048576 79741259275560326004736 151115727451828646838272 1133191450 2147483648 385360 384984 (ep1114 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1116 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz68 (Real.cos qz178)) (@HMul.hMul Real Real Real qz0 qz68 (@Neg.neg Real Real.instNeg (Real.sin qz178))) Bool.true 13318532201 137438953472 871659551527 6613974757933056 Bool.true 22852324157 137438953472 873933074539 6613974757933056 (@Enclosure.Real.IsNear.mulLit_ft qz68 (Real.cos qz178) 201799 1048576 1 1048576 65999 131072 17214737 25230311424 13318532201 137438953472 871659551527 6613974757933056 qz384 (@Enclosure.Real.IsNear.recentre' (Real.cos qz178) Bool.true 527992 1048576 68858948 100921245696 65999 131072 17214737 25230311424 (ep1113 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz68 (@Neg.neg Real Real.instNeg (Real.sin qz178)) 201799 1048576 1 1048576 113243 131072 17214737 25230311424 22852324157 137438953472 873933074539 6613974757933056 qz384 (@Enclosure.Real.IsNear.neg (Real.sin qz178) Bool.false 113243 131072 17214737 25230311424 (@Enclosure.Real.IsNear.recentre' (Real.sin qz178) Bool.false 905944 1048576 68858948 100921245696 113243 131072 17214737 25230311424 (ep1115 rfl rfl) rfl)) rfl)

noncomputable def ep1117 := @ep1081 13318532201 137438953472 871659551527 6613974757933056 Bool.true 22852324157 137438953472 873933074539 6613974757933056 Bool.false 65303977363029970911232 475148971331 549755813888 145447769955419 26455899031732224 Bool.true 198713031076702322688 2891655183 137438953472 9093563614409 1653493689483264 (ep1082 (BSN.head_sum_c_succ qz146 26 27 rfl rfl) (ep1108 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1109 ep1116) rfl rfl

noncomputable abbrev qz179 := (@HMul.hMul Real Real Real qz267 qz443 qz587)

noncomputable def ep1118 := @Enclosure.Complex.IsNear.of_eq qz636 (Complex.mk (@HMul.hMul Real Real Real qz0 qz70 (Real.cos qz179)) (@HMul.hMul Real Real Real qz0 qz70 (@Neg.neg Real Real.instNeg (Real.sin qz179)))) Bool.false 176823817345 1099511627776 6875159406653 52911798063464448 Bool.true 13641342757 137438953472 1714680111371 13227949515866112 (BSN.cpow_neg_s_mk qz149 130272 1000 28 qz150 rfl)

noncomputable def ep1119 := @Enclosure.Real.IsNear.mulLit_ff qz149 qz587 130272 1000 0 1 3751726938922231 1125899906842624 62500000048123 12030750000000000000 15273280368352402401 35184372088832000 84812500065302911 125320312500000000000 qz151 (BSN.isNear_log_sfrac 28 1 3751726938922231 1125899906842624 62500000048123 12030750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz385) Bool.false 62943533227317076688896 18889465931478580854784 1000000000769968 192492000000000000000 3751726938922231 1125899906842624 62500000048123 12030750000000000000 (BSN.log_rat_reduce_isNear 28 1 4 56 32 293399 524288 24973259072661432 36028797018963968 192492 1000000000000000 rfl rfl rfl rfl (ep456 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1120 := nat_lit 1988213708277563276504446495203042961

noncomputable def ep1121 := BSN.cos_dyadic_bound_f 1187451187 2147483648 2 1 1048576 385360 ep1120 ep96 ep1120 ep1120 ep97 ep1120 892315 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1187451187) qz15 0 1 ep1120 ep96 ep1120 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1187451187) qz16 0 1 ep1120 ep97 ep1120 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz471 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 455179225) qz24)

noncomputable def ep1122 := @Enclosure.Real.IsNear.cos_image qz179 qz471 Bool.false 455179225 1048576 711 1048576 Bool.false 892315 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz179 Bool.false 15273280368352402401 35184372088832000 84812500065302911 125320312500000000000 455179225 1048576 711 1048576 (ep1119 rfl) rfl) (Enclosure.sfrac_false_div 455179225 1048576) (BSN.cos_reduce0 qz471 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 83559448870479063941120) qz25) 226375608064910080 72057594037927936 Bool.false 892315 1048576 69 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q0 455179225 1048576 226375608064910080 72057594037927936 69 83559448870479063941120 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 892315 1048576 83559448870479063941120 151115727451828646838272 1187451187 2147483648 385360 384984 (ep1121 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1123 := BSN.sin_dyadic_bound_f 1187451187 2147483648 2 1 1048576 385360 ep1120 ep92 ep1120 ep1120 ep93 ep1120 550712 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1187451187) qz20 0 1 ep1120 ep92 ep1120 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1187451187) qz21 0 1 ep1120 ep93 ep1120 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1124 := @Enclosure.Real.IsNear.sin_image qz179 qz471 Bool.false 455179225 1048576 711 1048576 Bool.false 550712 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz179 Bool.false 15273280368352402401 35184372088832000 84812500065302911 125320312500000000000 455179225 1048576 711 1048576 (ep1119 rfl) rfl) (Enclosure.sfrac_false_div 455179225 1048576) (BSN.sin_reduce0 qz471 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 83559448870479063941120) qz25) 226375608064910080 72057594037927936 Bool.false 550712 1048576 69 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q0 455179225 1048576 226375608064910080 72057594037927936 69 83559448870479063941120 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 550712 1048576 83559448870479063941120 151115727451828646838272 1187451187 2147483648 385360 384984 (ep1123 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1125 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz70 (Real.cos qz179)) (@HMul.hMul Real Real Real qz0 qz70 (@Neg.neg Real Real.instNeg (Real.sin qz179))) Bool.false 176823817345 1099511627776 6875159406653 52911798063464448 Bool.true 13641342757 137438953472 1714680111371 13227949515866112 (@Enclosure.Real.IsNear.mulLit_ff qz70 (Real.cos qz179) 198163 1048576 1 1048576 892315 1048576 34477597 50460622848 176823817345 1099511627776 6875159406653 52911798063464448 qz387 (@Enclosure.Real.IsNear.recentre' (Real.cos qz179) Bool.false 892315 1048576 137910388 201842491392 892315 1048576 34477597 50460622848 (ep1122 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz70 (@Neg.neg Real Real.instNeg (Real.sin qz179)) 198163 1048576 1 1048576 68839 131072 34477597 50460622848 13641342757 137438953472 1714680111371 13227949515866112 qz387 (@Enclosure.Real.IsNear.neg (Real.sin qz179) Bool.false 68839 131072 34477597 50460622848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz179) Bool.false 550712 1048576 137910388 201842491392 68839 131072 34477597 50460622848 (ep1124 rfl rfl) rfl)) rfl)

noncomputable def ep1126 := @ep1079 176823817345 1099511627776 6875159406653 52911798063464448 Bool.true 13641342757 137438953472 1714680111371 13227949515866112 Bool.false 619641740523523293577216 1127121760007 1099511627776 33085633257499 5879088673718272 Bool.true 2272277934628331847680 4133249485 34359738368 8273687669627 1469772168429568 (ep1080 (BSN.head_sum_c_succ qz146 27 28 rfl rfl) (ep1117 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1118 ep1125) rfl rfl

noncomputable abbrev qz180 := (@HMul.hMul Real Real Real qz267 qz443 qz588)

noncomputable def ep1127 := @Enclosure.Complex.IsNear.of_eq qz635 (Complex.mk (@HMul.hMul Real Real Real qz0 qz72 (Real.cos qz180)) (@HMul.hMul Real Real Real qz0 qz72 (@Neg.neg Real Real.instNeg (Real.sin qz180)))) Bool.false 40878661815 549755813888 3366772879469 26455899031732224 Bool.false 93544785585 549755813888 3379789092263 26455899031732224 (BSN.cpow_neg_s_mk qz149 130272 1000 29 qz150 rfl)

noncomputable def ep1128 := @Enclosure.Real.IsNear.mulLit_ff qz149 qz588 130272 1000 0 1 3791236343078135 1125899906842624 62500000048123 12030750000000000000 3086824630534217517 7036874417766400 84812500065302911 125320312500000000000 qz151 (BSN.isNear_log_sfrac 29 1 3791236343078135 1125899906842624 62500000048123 12030750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz388) Bool.false 63606391034871975772160 18889465931478580854784 1000000000769968 192492000000000000000 3791236343078135 1125899906842624 62500000048123 12030750000000000000 (BSN.log_rat_reduce_isNear 29 1 4 58 32 311797 524288 24973259072661432 36028797018963968 192492 1000000000000000 rfl rfl rfl rfl (ep471 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1129 := nat_lit 612710679785570597482045779845298321

noncomputable def ep1130 := BSN.sin_dyadic_bound_f 884736333 2147483648 2 1 1048576 385360 ep1129 ep92 ep1129 ep1129 ep93 ep1129 419882 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 884736333) qz20 0 1 ep1129 ep92 ep1129 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 884736333) qz21 0 1 ep1129 ep93 ep1129 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz472 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 459972713) qz24)

noncomputable def ep1131 := @Enclosure.Real.IsNear.cos_image qz180 qz472 Bool.false 459972713 1048576 711 1048576 Bool.false 419882 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz180 Bool.false 3086824630534217517 7036874417766400 84812500065302911 125320312500000000000 459972713 1048576 711 1048576 (ep1128 rfl) rfl) (Enclosure.sfrac_false_div 459972713 1048576) (BSN.cos_reduce3 qz472 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 62257784723023819964416) qz25) 226375608064910080 72057594037927936 Bool.false 419882 1048576 69 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q3 459972713 1048576 226375608064910080 72057594037927936 69 62257784723023819964416 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 419882 1048576 62257784723023819964416 151115727451828646838272 884736333 2147483648 385360 384984 (ep1130 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1132 := BSN.cos_dyadic_bound_f 884736333 2147483648 2 1 1048576 385360 ep1129 ep96 ep1129 ep1129 ep97 ep1129 960838 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 884736333) qz15 0 1 ep1129 ep96 ep1129 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 884736333) qz16 0 1 ep1129 ep97 ep1129 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1133 := @Enclosure.Real.IsNear.sin_image qz180 qz472 Bool.false 459972713 1048576 711 1048576 Bool.true 960838 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz180 Bool.false 3086824630534217517 7036874417766400 84812500065302911 125320312500000000000 459972713 1048576 711 1048576 (ep1128 rfl) rfl) (Enclosure.sfrac_false_div 459972713 1048576) (BSN.sin_reduce3 qz472 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 62257784723023819964416) qz25) 226375608064910080 72057594037927936 Bool.false 960838 1048576 69 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q3 459972713 1048576 226375608064910080 72057594037927936 69 62257784723023819964416 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 960838 1048576 62257784723023819964416 151115727451828646838272 884736333 2147483648 385360 384984 (ep1132 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1134 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz72 (Real.cos qz180)) (@HMul.hMul Real Real Real qz0 qz72 (@Neg.neg Real Real.instNeg (Real.sin qz180))) Bool.false 40878661815 549755813888 3366772879469 26455899031732224 Bool.false 93544785585 549755813888 3379789092263 26455899031732224 (@Enclosure.Real.IsNear.mulLit_ff qz72 (Real.cos qz180) 194715 1048576 1 1048576 209941 524288 34477597 50460622848 40878661815 549755813888 3366772879469 26455899031732224 qz390 (@Enclosure.Real.IsNear.recentre' (Real.cos qz180) Bool.false 419882 1048576 137910388 201842491392 209941 524288 34477597 50460622848 (ep1131 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz72 (@Neg.neg Real Real.instNeg (Real.sin qz180)) 194715 1048576 1 1048576 480419 524288 34477597 50460622848 93544785585 549755813888 3379789092263 26455899031732224 qz390 (@Enclosure.Real.IsNear.neg (Real.sin qz180) Bool.true 480419 524288 34477597 50460622848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz180) Bool.true 960838 1048576 137910388 201842491392 480419 524288 34477597 50460622848 (ep1133 rfl rfl) rfl)) rfl)

noncomputable def ep1135 := @ep1077 40878661815 549755813888 3366772879469 26455899031732224 Bool.false 93544785585 549755813888 3379789092263 26455899031732224 Bool.false 664588304517038558150656 1208879083637 1099511627776 304504245076429 52911798063464448 Bool.false 941896423762925977600 27412793825 549755813888 152306167145549 26455899031732224 (ep1078 (BSN.head_sum_c_succ qz146 28 29 rfl rfl) (ep1126 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1127 ep1134) rfl rfl

noncomputable abbrev qz181 := (@HMul.hMul Real Real Real qz267 qz443 qz589)

noncomputable def ep1136 := @Enclosure.Complex.IsNear.of_eq qz634 (Complex.mk (@HMul.hMul Real Real Real qz0 qz74 (Real.cos qz181)) (@HMul.hMul Real Real Real qz0 qz74 (@Neg.neg Real Real.instNeg (Real.sin qz181)))) Bool.true 199393819233 1099511627776 6641437816769 52911798063464448 Bool.false 23229502177 1099511627776 6597155417153 52911798063464448 (BSN.cpow_neg_s_mk qz149 130272 1000 30 qz150 rfl)

noncomputable def ep1137 := @Enclosure.Real.IsNear.mulLit_ff qz149 qz589 130272 1000 0 1 3829405717437687 1125899906842624 62500000048123 12030750000000000000 15589510675688823777 35184372088832000 84812500065302911 125320312500000000000 qz151 (BSN.isNear_log_sfrac 30 1 3829405717437687 1125899906842624 62500000048123 12030750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz391) Bool.false 64246766873087041339392 18889465931478580854784 1000000000769968 192492000000000000000 3829405717437687 1125899906842624 62500000048123 12030750000000000000 (BSN.log_rat_reduce_isNear 30 1 4 60 32 329571 524288 24973259072661432 36028797018963968 192492 1000000000000000 rfl rfl rfl rfl (ep486 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1138 := nat_lit 3847937740235489409660792644550625

noncomputable def ep1139 := BSN.cos_dyadic_bound_f 249061735 2147483648 2 1 1048576 385360 ep1138 ep96 ep1138 ep1138 ep97 ep1138 1041531 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 249061735) qz15 0 1 ep1138 ep96 ep1138 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 249061735) qz16 0 1 ep1138 ep97 ep1138 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz473 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 464603623) qz24)

noncomputable def ep1140 := @Enclosure.Real.IsNear.cos_image qz181 qz473 Bool.false 464603623 1048576 355 524288 Bool.true 1041531 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz181 Bool.false 15589510675688823777 35184372088832000 84812500065302911 125320312500000000000 464603623 1048576 355 524288 (ep1137 rfl) rfl) (Enclosure.sfrac_false_div 464603623 1048576) (BSN.cos_reduce2 qz473 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 17526161528572080029696) qz25) 226375608064910080 72057594037927936 Bool.false 1041531 1048576 70 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q2 464603623 1048576 226375608064910080 72057594037927936 70 17526161528572080029696 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1041531 1048576 17526161528572080029696 151115727451828646838272 249061735 2147483648 385360 384984 (ep1139 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1141 := BSN.sin_dyadic_bound_f 249061735 2147483648 1 0 1048576 385360 0 1 1 0 1 1 121339 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 249061735) qz20 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 249061735) qz21 0 0 rfl) rfl rfl

noncomputable def ep1142 := @Enclosure.Real.IsNear.sin_image qz181 qz473 Bool.false 464603623 1048576 355 524288 Bool.true 121339 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz181 Bool.false 15589510675688823777 35184372088832000 84812500065302911 125320312500000000000 464603623 1048576 355 524288 (ep1137 rfl) rfl) (Enclosure.sfrac_false_div 464603623 1048576) (BSN.sin_reduce2 qz473 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 17526161528572080029696) qz25) 226375608064910080 72057594037927936 Bool.false 121339 1048576 70 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q2 464603623 1048576 226375608064910080 72057594037927936 70 17526161528572080029696 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 121339 1048576 17526161528572080029696 151115727451828646838272 249061735 2147483648 385360 384984 (ep1141 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1143 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz74 (Real.cos qz181)) (@HMul.hMul Real Real Real qz0 qz74 (@Neg.neg Real Real.instNeg (Real.sin qz181))) Bool.true 199393819233 1099511627776 6641437816769 52911798063464448 Bool.false 23229502177 1099511627776 6597155417153 52911798063464448 (@Enclosure.Real.IsNear.mulLit_ft qz74 (Real.cos qz181) 191443 1048576 1 1048576 1041531 1048576 17214737 25230311424 199393819233 1099511627776 6641437816769 52911798063464448 qz393 (@Enclosure.Real.IsNear.recentre' (Real.cos qz181) Bool.true 1041531 1048576 68858948 100921245696 1041531 1048576 17214737 25230311424 (ep1140 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz74 (@Neg.neg Real Real.instNeg (Real.sin qz181)) 191443 1048576 1 1048576 121339 1048576 17214737 25230311424 23229502177 1099511627776 6597155417153 52911798063464448 qz393 (@Enclosure.Real.IsNear.neg (Real.sin qz181) Bool.true 121339 1048576 17214737 25230311424 (@Enclosure.Real.IsNear.recentre' (Real.sin qz181) Bool.true 121339 1048576 68858948 100921245696 121339 1048576 17214737 25230311424 (ep1142 rfl rfl) rfl)) rfl)

noncomputable def ep1144 := @ep1075 199393819233 1099511627776 6641437816769 52911798063464448 Bool.false 23229502177 1099511627776 6597155417153 52911798063464448 Bool.false 1109940786280727790485504 252371316101 274877906944 51857613815533 8818633010577408 Bool.false 42911239435943334117376 78055089827 1099511627776 103736496569417 17637266021154816 (ep1076 (BSN.head_sum_c_succ qz146 29 30 rfl rfl) (ep1135 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1136 ep1143) rfl rfl

noncomputable abbrev qz182 := (@HMul.hMul Real Real Real qz267 qz443 qz590)

noncomputable def ep1145 := @Enclosure.Complex.IsNear.of_eq qz633 (Complex.mk (@HMul.hMul Real Real Real qz0 qz76 (Real.cos qz182)) (@HMul.hMul Real Real Real qz0 qz76 (@Neg.neg Real Real.instNeg (Real.sin qz182)))) Bool.false 62989458985 1099511627776 6509261302205 52911798063464448 Bool.true 93580868429 549755813888 408811911041 3306987378966528 (BSN.cpow_neg_s_mk qz149 130272 1000 31 qz150 rfl)

noncomputable def ep1146 := @Enclosure.Real.IsNear.mulLit_ff qz149 qz590 130272 1000 0 1 3866325256314103 1125899906842624 62500000048123 12030750000000000000 15739810118454713313 35184372088832000 84812500065302911 125320312500000000000 qz151 (BSN.isNear_log_sfrac 31 1 3866325256314103 1125899906842624 62500000048123 12030750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz394) Bool.false 64866173951437069877248 18889465931478580854784 1000000000769968 192492000000000000000 3866325256314103 1125899906842624 62500000048123 12030750000000000000 (BSN.log_rat_reduce_isNear 31 1 4 62 32 346763 524288 24973259072661432 36028797018963968 192492 1000000000000000 rfl rfl rfl rfl (ep501 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1147 := nat_lit 1835083395513347303087574334040977318167029950823674676223561245806416228024576

noncomputable def ep1148 := nat_lit 2630317881673618279643705477276025619434335050579692543649526315684400496896

noncomputable def ep1149 := nat_lit 5499989550776694672703435591168379903262221182369864643583384684787879883079936

noncomputable def ep1150 := BSN.cos_dyadic_bound_f 2676091938 2147483648 3 2 1048576 385360 ep1147 ep57 ep1148 ep1149 ep60 ep1148 334465 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2676091938) qz15 0 2 ep1147 ep57 ep1148 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2676091938) qz16 0 2 ep1149 ep60 ep1148 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz474 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 469082895) qz24)

noncomputable def ep1151 := @Enclosure.Real.IsNear.cos_image qz182 qz474 Bool.false 469082895 1048576 711 1048576 Bool.false 334465 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz182 Bool.false 15739810118454713313 35184372088832000 84812500065302911 125320312500000000000 469082895 1048576 711 1048576 (ep1146 rfl) rfl) (Enclosure.sfrac_false_div 469082895 1048576) (BSN.cos_reduce0 qz474 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 188313229046944859422720) qz25) 226375608064910080 72057594037927936 Bool.false 334465 1048576 71 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q0 469082895 1048576 226375608064910080 72057594037927936 71 188313229046944859422720 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 334465 1048576 188313229046944859422720 151115727451828646838272 2676091938 2147483648 385360 384984 (ep1150 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1152 := nat_lit 3301045857618686250933918836891938352205106443442150663167490621399001690046720

noncomputable def ep1153 := nat_lit 8641337683859563846659888097277582119058099380838027472748947632486277301698816

noncomputable def ep1154 := BSN.sin_dyadic_bound_f 2676091938 2147483648 3 2 1048576 385360 ep1152 ep64 ep1148 ep1153 ep66 ep1148 993802 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2676091938) qz20 0 2 ep1152 ep64 ep1148 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2676091938) qz21 0 2 ep1153 ep66 ep1148 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1155 := @Enclosure.Real.IsNear.sin_image qz182 qz474 Bool.false 469082895 1048576 711 1048576 Bool.false 993802 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz182 Bool.false 15739810118454713313 35184372088832000 84812500065302911 125320312500000000000 469082895 1048576 711 1048576 (ep1146 rfl) rfl) (Enclosure.sfrac_false_div 469082895 1048576) (BSN.sin_reduce0 qz474 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 188313229046944859422720) qz25) 226375608064910080 72057594037927936 Bool.false 993802 1048576 71 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q0 469082895 1048576 226375608064910080 72057594037927936 71 188313229046944859422720 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 993802 1048576 188313229046944859422720 151115727451828646838272 2676091938 2147483648 385360 384984 (ep1154 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1156 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz76 (Real.cos qz182)) (@HMul.hMul Real Real Real qz0 qz76 (@Neg.neg Real Real.instNeg (Real.sin qz182))) Bool.false 62989458985 1099511627776 6509261302205 52911798063464448 Bool.true 93580868429 549755813888 408811911041 3306987378966528 (@Enclosure.Real.IsNear.mulLit_ff qz76 (Real.cos qz182) 188329 1048576 1 1048576 334465 1048576 34477597 50460622848 62989458985 1099511627776 6509261302205 52911798063464448 qz396 (@Enclosure.Real.IsNear.recentre' (Real.cos qz182) Bool.false 334465 1048576 137910388 201842491392 334465 1048576 34477597 50460622848 (ep1151 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz76 (@Neg.neg Real Real.instNeg (Real.sin qz182)) 188329 1048576 1 1048576 496901 524288 34477597 50460622848 93580868429 549755813888 408811911041 3306987378966528 qz396 (@Enclosure.Real.IsNear.neg (Real.sin qz182) Bool.false 496901 524288 34477597 50460622848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz182) Bool.false 993802 1048576 137910388 201842491392 496901 524288 34477597 50460622848 (ep1155 rfl rfl) rfl)) rfl)

noncomputable def ep1157 := @ep1073 62989458985 1099511627776 6509261302205 52911798063464448 Bool.true 93580868429 549755813888 408811911041 3306987378966528 Bool.false 294799607215513682313216 1072474723389 1099511627776 317654944195403 52911798063464448 Bool.true 59982013539118143766528 109106647031 1099511627776 317750480284907 52911798063464448 (ep1074 (BSN.head_sum_c_succ qz146 30 31 rfl rfl) (ep1144 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1145 ep1156) rfl rfl

noncomputable abbrev qz183 := (@HMul.hMul Real Real Real qz267 qz443 qz591)

noncomputable def ep1158 := @Enclosure.Complex.IsNear.of_eq qz632 (Complex.mk (@HMul.hMul Real Real Real qz0 qz78 (Real.cos qz183)) (@HMul.hMul Real Real Real qz0 qz78 (@Neg.neg Real Real.instNeg (Real.sin qz183)))) Bool.false 120668903281 1099511627776 713581415301 5879088673718272 Bool.false 152373020075 1099511627776 714495955487 5879088673718272 (BSN.cpow_neg_s_mk qz149 130272 1000 32 qz150 rfl)

noncomputable def ep1159 := @Enclosure.Real.IsNear.mulLit_ff qz149 qz591 130272 1000 0 1 15608286920413395 4503599627370496 50000000048123 9624600000000000000 12708267210600586209 28147497671065600 67850000065302911 100256250000000000000 qz151 (BSN.isNear_log_sfrac 32 1 15608286920413395 4503599627370496 50000000048123 9624600000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz397) Bool.false 65465900263437584302080 18889465931478580854784 1000000000962460 192492000000000000000 15608286920413395 4503599627370496 50000000048123 9624600000000000000 (BSN.log_rat_reduce_isNear 32 1 5 64 64 0 524288 24973259072661432 36028797018963968 192492 1000000000000000 rfl rfl rfl rfl (ep512 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1160 := nat_lit 4280586832235603651578965990617760000

noncomputable def ep1161 := BSN.sin_dyadic_bound_f 1438387260 2147483648 2 1 1048576 385360 ep1160 ep92 ep1160 ep1160 ep93 ep1160 650987 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1438387260) qz20 0 1 ep1160 ep92 ep1160 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1438387260) qz21 0 1 ep1160 ep93 ep1160 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz475 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 473419845) qz24)

noncomputable def ep1162 := @Enclosure.Real.IsNear.cos_image qz183 qz475 Bool.false 473419845 1048576 711 1048576 Bool.false 650987 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz183 Bool.false 12708267210600586209 28147497671065600 67850000065302911 100256250000000000000 473419845 1048576 711 1048576 (ep1159 rfl) rfl) (Enclosure.sfrac_false_div 473419845 1048576) (BSN.cos_reduce3 qz475 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 101217505165714527354880) qz25) 226375608064910080 72057594037927936 Bool.false 650987 1048576 71 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q3 473419845 1048576 226375608064910080 72057594037927936 71 101217505165714527354880 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 650987 1048576 101217505165714527354880 151115727451828646838272 1438387260 2147483648 385360 384984 (ep1161 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1163 := nat_lit 152962186427420309539805911803779512529883548710063986674776505161068748800000

noncomputable def ep1164 := nat_lit 18323423628308840001095584735865780806396593621175524160346427417600000000

noncomputable def ep1165 := nat_lit 458849912435004310939415544241866806028037852942949608976008822628371046400000

noncomputable def ep1166 := BSN.cos_dyadic_bound_f 1438387260 2147483648 3 2 1048576 385360 ep1163 ep57 ep1164 ep1165 ep60 ep1164 822025 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1438387260) qz15 0 2 ep1163 ep57 ep1164 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1438387260) qz16 0 2 ep1165 ep60 ep1164 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1167 := @Enclosure.Real.IsNear.sin_image qz183 qz475 Bool.false 473419845 1048576 711 1048576 Bool.true 822025 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz183 Bool.false 12708267210600586209 28147497671065600 67850000065302911 100256250000000000000 473419845 1048576 711 1048576 (ep1159 rfl) rfl) (Enclosure.sfrac_false_div 473419845 1048576) (BSN.sin_reduce3 qz475 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 101217505165714527354880) qz25) 226375608064910080 72057594037927936 Bool.false 822025 1048576 71 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q3 473419845 1048576 226375608064910080 72057594037927936 71 101217505165714527354880 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 822025 1048576 101217505165714527354880 151115727451828646838272 1438387260 2147483648 385360 384984 (ep1166 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1168 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz78 (Real.cos qz183)) (@HMul.hMul Real Real Real qz0 qz78 (@Neg.neg Real Real.instNeg (Real.sin qz183))) Bool.false 120668903281 1099511627776 713581415301 5879088673718272 Bool.false 152373020075 1099511627776 714495955487 5879088673718272 (@Enclosure.Real.IsNear.mulLit_ff qz78 (Real.cos qz183) 185363 1048576 1 1048576 650987 1048576 34477597 50460622848 120668903281 1099511627776 713581415301 5879088673718272 qz399 (@Enclosure.Real.IsNear.recentre' (Real.cos qz183) Bool.false 650987 1048576 137910388 201842491392 650987 1048576 34477597 50460622848 (ep1162 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz78 (@Neg.neg Real Real.instNeg (Real.sin qz183)) 185363 1048576 1 1048576 822025 1048576 34477597 50460622848 152373020075 1099511627776 714495955487 5879088673718272 qz399 (@Enclosure.Real.IsNear.neg (Real.sin qz183) Bool.true 822025 1048576 34477597 50460622848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz183) Bool.true 822025 1048576 137910388 201842491392 822025 1048576 34477597 50460622848 (ep1167 rfl rfl) rfl)) rfl)

noncomputable def ep1169 := @ep1070 120668903281 1099511627776 713581415301 5879088673718272 Bool.false 152373020075 1099511627776 714495955487 5879088673718272 Bool.false ep1071 596571813335 549755813888 40509647116639 6613974757933056 Bool.false 47571880253572088070144 10816593261 274877906944 162090471942145 26455899031732224 (ep1072 (BSN.head_sum_c_succ qz146 31 32 rfl rfl) (ep1157 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1158 ep1168) rfl rfl

theorem EMRow43.d16 : Enclosure.Complex.IsNear (BSN.headSumC qz146 33) Bool.false 596571813335 549755813888 40509647116639 6613974757933056 Bool.false 10816593261 274877906944 162090471942145 26455899031732224 := ep1069 (BSN.head_sum_c_succ qz146 32 33 rfl rfl) (ep1169 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep1170 := nat_lit 40297100595218266164337937798693

noncomputable def ep1171 := nat_lit 40355455727363408480585121792000

noncomputable def ep1172 := nat_lit 1838443191796945290157055274759218087531

noncomputable def ep1173 := nat_lit 280368293264291098642841317497586581504000

noncomputable abbrev qz640 := (@HAdd.hAdd Complex Complex Complex qz652 (@HAdd.hAdd Complex Complex Complex qz652 qz655 (@HMul.hMul Complex Complex Complex qz654 Complex.I (@HDiv.hDiv Complex Complex Complex qz656 (↑qz659) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz476 := qz640

noncomputable abbrev qz184 := (Complex.Stirling.logGammaStirling 1 qz476)

noncomputable abbrev qz641 := (@HAdd.hAdd Complex Complex Complex qz652 qz655 (@HMul.hMul Complex Complex Complex qz654 Complex.I (@HDiv.hDiv Complex Complex Complex qz656 (↑qz659) (2 : Complex))))

noncomputable abbrev qz477 := qz641

noncomputable abbrev qz185 := qz477

noncomputable abbrev qz186 := (@HMul.hMul Real Real Real qz267 (@HDiv.hDiv Real Real Real qz270 qz443 (2 : Real)) (Real.log Real.pi))

noncomputable def ep1174 := Complex.re (@HMul.hMul Complex Complex Complex qz80 (Complex.exp (@HMul.hMul Complex Complex Complex qz80 Complex.I ↑(@HSub.hSub Real Real Real qz404 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz184 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz185 (@Nat.cast Complex Complex.instNatCast j))))) qz186))) (zetaApproximant qz146 1 33))

noncomputable def ep1175 := @Enclosure.Real.IsNear.of_eq ep1174 (@HSub.hSub Real Real Real qz404 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz404 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz184 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz185 (@Nat.cast Complex Complex.instNatCast j))))) qz186)) (Complex.re (zetaApproximant qz146 1 33))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz404 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz184 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz185 (@Nat.cast Complex Complex.instNatCast j))))) qz186)) (Complex.im (zetaApproximant qz146 1 33))))

noncomputable def ep1176 := nat_lit 146536549868351157296915172847

noncomputable def ep1177 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz404 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz184 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz185 (@Nat.cast Complex Complex.instNatCast j))))) qz186)) (Complex.re (zetaApproximant qz146 1 33))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz404 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz184 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz185 (@Nat.cast Complex Complex.instNatCast j))))) qz186)) (Complex.im (zetaApproximant qz146 1 33))) ep1176

noncomputable def ep1178 := nat_lit 146747111735866939929400442880

noncomputable def ep1179 := nat_lit 1834732905297807028323304111227092018611

noncomputable def ep1180 := nat_lit 18775774095920513072280593

noncomputable def ep1181 := nat_lit 1681477321973475353357713408000

noncomputable def ep1182 := nat_lit 8432469316223322349434462573013793

noncomputable def ep1183 := nat_lit 637200666509752496915548448858151321600

noncomputable def ep1184 := nat_lit 246395130153248544878172095786262281617542265117423603548160

noncomputable def ep1185 := @Enclosure.Real.IsNear.mulLit_ff (Real.cos (@HSub.hSub Real Real Real qz404 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz184 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz185 (@Nat.cast Complex Complex.instNatCast j))))) qz186)) (Complex.re (zetaApproximant qz146 1 33)) 1048575 1048576 2198303

noncomputable def ep1186 := nat_lit 115292328771322704403552457

noncomputable def ep1187 := nat_lit 115457884962167954866176000

noncomputable def ep1188 := nat_lit 34414084113066137739035107303

noncomputable def ep1189 := nat_lit 5556179798034408492024987648000

noncomputable def ep1190 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz404 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz184 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz185 (@Nat.cast Complex Complex.instNatCast j))))) qz186)) Bool.false 1048575 1048576 8793212

noncomputable abbrev qz478 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8647303) (@Nat.cast Real Real.instNatCast 65536))

noncomputable def ep1191 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz404 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz184 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz185 (@Nat.cast Complex Complex.instNatCast j))))) qz186) qz478 Bool.false 8647303 65536 45

noncomputable def ep1192 := nat_lit 525631488000000000000000000

noncomputable def ep1193 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz404 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz184 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz185 (@Nat.cast Complex Complex.instNatCast j))))) qz186) Bool.false 37139883604264904367 281474976710656000 180192662501973498794833 ep1192

noncomputable def ep1194 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz184 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz185 (@Nat.cast Complex Complex.instNatCast j))))) qz186 58127532735469741743 281474976710656000 49586840501973498794833 ep1192 305410491 4096000

noncomputable def ep1195 := nat_lit 152124963243069048287232000

noncomputable def ep1196 := nat_lit 4205051904000000000000000000

noncomputable def ep1197 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz81 qz184 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz185 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 115337875166168076401 1125899906842624000 739959499806240311921347 ep1196 Bool.false 58127532735469741743 281474976710656000

noncomputable def ep1198 := nat_lit 2187110499267339067220041

noncomputable def ep1199 := @Enclosure.Complex.IsNear.subLitP qz184 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz185 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 105933068802862375401 1125899906842624000 ep1198 ep554 Bool.false 59005331348823632743 281474976710656000 140568521504343601920499

noncomputable def ep1200 := nat_lit 1576894464000000000000000000

noncomputable def ep1201 := nat_lit 129858902905014833324103927515316224

noncomputable def ep1202 := nat_lit 16361445922964239809495107956113408

noncomputable abbrev qz479 := (@HSub.hSub Complex Complex Complex qz593 qz640 qz596)

noncomputable abbrev qz480 := (Complex.log qz640)

noncomputable abbrev qz187 := (@HSub.hSub Complex Complex Complex qz401 (@HMul.hMul Complex Complex Complex qz400 qz479 qz480) qz476)

noncomputable abbrev qz188 := qz476

noncomputable def ep1203 := @Enclosure.Complex.IsNear.of_eq qz184 (@HAdd.hAdd Complex Complex Complex qz4 (@HAdd.hAdd Complex Complex Complex qz4 qz187 qz86) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz89 qz188 (@HSub.hSub Int Int Int qz411 qz91 (@HMul.hMul Int Int Int qz412 qz92 (@Nat.cast Int instNatCastInt k)))))) Bool.true 105933068802862375401

noncomputable def ep1204 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz4 qz187 qz86) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz89 qz188 (@HSub.hSub Int Int Int qz411 qz91 (@HMul.hMul Int Int Int qz412 qz92 (@Nat.cast Int instNatCastInt k))))) Bool.true 105933118501088551401 1125899906842624000

noncomputable def ep1205 := nat_lit 7279665057171388376578718171136

noncomputable def ep1206 := nat_lit 63356492108210267675774943232000

noncomputable def ep1207 := @ep1204 16686324680658794603 96246000000000000000000 Bool.false 59005691031452543847 281474976710656000 4289750018849345993 48123000000000000000000 Bool.false 3033339 68719476736 3 68719476736 Bool.true 1372080341 1073741824000 1357 1073741824000 Bool.true ep1205 105933068802862375401 1125899906842624000 ep1198 ep554 Bool.false ep1206

noncomputable def ep1208 := @Enclosure.Complex.IsNear.addLitP qz187 qz86 Bool.true 106967750352891175401 1125899906842624000 2062843750518140341 12030750000000000000000

noncomputable def ep1209 := nat_lit 13884865708174678609231872

noncomputable def ep1210 := @ep1208 Bool.false 59005691031452543847 281474976710656000 4289750018849345993 48123000000000000000000 Bool.false 120447 131072 1 524288 Bool.false 0 1 0 1 Bool.true ep1209 105933118501088551401 1125899906842624000 16686324680658794603 96246000000000000000000 Bool.false 59005691031452543847 59005691031452543847 281474976710656000

noncomputable abbrev qz189 := (@HMul.hMul Complex Complex Complex qz400 qz479 qz480)

noncomputable def ep1211 := @Enclosure.Complex.IsNear.subLitP qz189 qz188 Bool.true 104434475562495271401 1125899906842624000 2062843750518140341 12030750000000000000000 Bool.false 77339845114477833063

noncomputable def ep1212 := @ep1211 281474976710656000 4289750018849345993 48123000000000000000000 Bool.false 9000 4000 0 1 Bool.false 260544 4000 0 1 Bool.true 427871001411564701604000 106967750352891175401 1125899906842624000 2062843750518140341 12030750000000000000000 Bool.false 236022764125810175388000 59005691031452543847 281474976710656000 4289750018849345993 48123000000000000000000

noncomputable abbrev qz190 := qz479

noncomputable abbrev qz191 := qz480

noncomputable def ep1213 := @Enclosure.Complex.IsNear.mul qz190 qz191 Bool.true 104434475562495271401 1125899906842624000 2062843750518140341 12030750000000000000000 Bool.false 77339845114477833063 281474976710656000 4289750018849345993

noncomputable abbrev qz192 := (Complex.re qz479)

noncomputable abbrev qz193 := (Complex.re qz480)

noncomputable abbrev qz194 := (Complex.im qz479)

noncomputable abbrev qz195 := (Complex.im qz480)

noncomputable def ep1214 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz192 qz193) (@HMul.hMul Real Real Real qz0 qz194 qz195) 65841532787449923 9007199254740992 218750001010583 96246000000000000000 3520770848778953493 35184372088832000

noncomputable def ep1215 := nat_lit 29395691576742929683050600968749056

noncomputable def ep1216 := @Enclosure.Real.IsNear.mulLit_ff qz192 qz193 7000 4000 0 1 9405933255349989 2251799813685248 31250000144369 24061500000000000000

noncomputable def ep1217 := @Enclosure.Complex.IsNear.re_isNear qz190 Bool.false 7000 4000 0 1 Bool.false 260544 4000 0 1

noncomputable abbrev qz642 := (Enclosure.sfrac Bool.false 260544 4000)

noncomputable abbrev qz481 := qz642

noncomputable def ep1218 := @Enclosure.Complex.IsNear.of_eq qz190 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz481) Bool.false 7000 4000 0 1 Bool.false 260544 4000 0

noncomputable abbrev qz482 := (Complex.log (Complex.mk qz600 qz642))

noncomputable def ep1219 := @Enclosure.Complex.IsNear.of_eq qz191 qz482 Bool.false 9405933255349989 2251799813685248 31250000144369 24061500000000000000 Bool.false 864841770763683 562949953421312 250000000048123 96246000000000000000

noncomputable def ep1220 := BSN.log_dyadic_bound 2428175936 133500175936 2 1 53466890924828860428288 1048576 384984 5896038376169476096 5896038376169476096 38148 135928351872 131072000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 2428175936) (BSN.artanhQ 133500175936) 0 1 5896038376169476096 53466890924828860428288 5896038376169476096 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz643 := (Real.log (Enclosure.sfrac Bool.false 67964175936 16000000))

noncomputable def ep1221 := @Enclosure.Real.IsNear.mulLit_ff qz100 qz643 1 2 0 1 9405933255349989 1125899906842624 31250000144369 12030750000000000000 9405933255349989 2251799813685248 31250000144369 24061500000000000000 qz415 (BSN.isNear_log_sfrac 67964175936 16000000 9405933255349989 1125899906842624 31250000144369 12030750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 67964175936) qz602)) Bool.false 315610747813179842101248 37778931862957161709568 1000000004619808 384984000000000000000 9405933255349989 1125899906842624 31250000144369 12030750000000000000 (BSN.log_rat_reduce_isNear 67964175936 16000000 12 135928351872 131072000000 38148 1048576 24973259072661432 36028797018963968 384984 1000000000000000 rfl rfl rfl rfl (ep1220 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1222 := BSN.arctan_dyadic_bound_f 9000 260544 1 0 1048576 384984 0 1 1 0 1 1 36206 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 260544) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 260544) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz483 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 260544)))

noncomputable def ep1223 := @Enclosure.Real.IsNear.subLit_ff_p qz101 qz483 884279719003555 562949953421312 1 2000000000000000 36206 1048576 1 384984 906852324620299665408 864841770763683 562949953421312 250000000048123 96246000000000000000 qz102 (ep1222 rfl) rfl rfl

noncomputable abbrev qz484 := (Complex.mk qz600 qz642)

noncomputable abbrev qz485 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 260544) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep1224 := @Enclosure.Complex.IsNear.re_isNear qz191 Bool.false 9405933255349989 2251799813685248 31250000144369 24061500000000000000 Bool.false 864841770763683 562949953421312 250000000048123 96246000000000000000 (ep1219 (@congrArg Complex Complex qz188 qz484 Complex.log (BSN.w_shift_mk qz149 Bool.false 130272 1000 2 qz150 rfl)) (@Enclosure.Complex.IsNear.of_parts qz482 Bool.false 9405933255349989 2251799813685248 31250000144369 24061500000000000000 Bool.false 864841770763683 562949953421312 250000000048123 96246000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz482) (@HMul.hMul Real Real Real qz0 qz100 qz643) Bool.false 9405933255349989 2251799813685248 31250000144369 24061500000000000000 (Enclosure.clog_re_eq 9000 260544 4000 67964175936 16000000 rfl rfl rfl) (ep1221 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz482) qz485 Bool.false 864841770763683 562949953421312 250000000048123 96246000000000000000 (Enclosure.clog_im_eq 9000 260544 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz485 (@HSub.hSub Real Real Real qz404 qz101 qz483) Bool.false 864841770763683 562949953421312 250000000048123 96246000000000000000 (BSN.arctan_recip 260544 9000 rfl rfl) ep1223))))

noncomputable def ep1225 := @Enclosure.Real.IsNear.mulLit_ff qz194 qz195 260544 4000 0 1 864841770763683 562949953421312 250000000048123 96246000000000000000

noncomputable def ep1226 := @Enclosure.Complex.IsNear.im_isNear qz190 Bool.false 7000 4000 0 1 Bool.false 260544 4000 0 1

noncomputable def ep1227 := @Enclosure.Complex.IsNear.im_isNear qz191 Bool.false 9405933255349989 2251799813685248 31250000144369 24061500000000000000 Bool.false 864841770763683 562949953421312 250000000048123 96246000000000000000 (ep1219 (@congrArg Complex Complex qz188 qz484 Complex.log (BSN.w_shift_mk qz149 Bool.false 130272 1000 2 qz150 rfl)) (@Enclosure.Complex.IsNear.of_parts qz482 Bool.false 9405933255349989 2251799813685248 31250000144369 24061500000000000000 Bool.false 864841770763683 562949953421312 250000000048123 96246000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz482) (@HMul.hMul Real Real Real qz0 qz100 qz643) Bool.false 9405933255349989 2251799813685248 31250000144369 24061500000000000000 (Enclosure.clog_re_eq 9000 260544 4000 67964175936 16000000 rfl rfl rfl) (ep1221 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz482) qz485 Bool.false 864841770763683 562949953421312 250000000048123 96246000000000000000 (Enclosure.clog_im_eq 9000 260544 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz485 (@HSub.hSub Real Real Real qz404 qz101 qz483) Bool.false 864841770763683 562949953421312 250000000048123 96246000000000000000 (BSN.arctan_recip 260544 9000 rfl rfl) ep1223))))

noncomputable abbrev qz196 := (@ep1218 1 (BSN.w_sub_half_mk qz443 Bool.false 130272 1000 2 qz444 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz481 Bool.false 7000 4000 0 1 Bool.false 260544 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) (Enclosure.Real.IsNear.const Bool.false 260544 4000)))

noncomputable def ep1228 := @ep1214 339250000065302911 2005125000000000000000 ep1215 104434475562495271401 1125899906842624000 2062843750518140341 12030750000000000000000 (@ep1216 65841532787449923 9007199254740992 218750001010583 96246000000000000000 (ep1217 qz196) ep1224 rfl) (@ep1225 3520770848778953493 35184372088832000 339250000065302911 2005125000000000000000 (ep1226 qz196) ep1227 rfl) rfl

noncomputable def ep1229 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz192 qz195) (@HMul.hMul Real Real Real qz0 qz194 qz193) 6053892395345781 2251799813685248 1750000000336861 384984000000000000000 38291554282529805219 140737488355328000

noncomputable def ep1230 := nat_lit 87076924409613561134457161684877312

noncomputable def ep1231 := @Enclosure.Real.IsNear.mulLit_ff qz192 qz195 7000 4000 0 1 864841770763683 562949953421312 250000000048123 96246000000000000000

noncomputable def ep1232 := @Enclosure.Real.IsNear.mulLit_ff qz194 qz193 260544 4000 0 1 9405933255349989 2251799813685248 31250000144369 24061500000000000000

noncomputable def ep1233 := @ep1229 42406250195908733 501281250000000000000 ep1230 77339845114477833063 281474976710656000 4289750018849345993 48123000000000000000000 (@ep1231 6053892395345781 2251799813685248 1750000000336861 384984000000000000000 (ep1217 qz196) ep1227 rfl) (@ep1232 38291554282529805219 140737488355328000 42406250195908733 501281250000000000000 (ep1226 qz196) ep1224 rfl) rfl

noncomputable def ep1234 := @Enclosure.Complex.IsNear.of_eq qz188 qz484 Bool.false 9000 4000 0 1 Bool.false 260544 4000 0 1 (BSN.w_shift_mk qz149 Bool.false 130272 1000 2 qz150 rfl)

noncomputable abbrev qz486 := (ep1234 (@Enclosure.Complex.IsNear.mk qz600 qz642 Bool.false 9000 4000 0 1 Bool.false 260544 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 260544 4000)))

noncomputable abbrev qz197 := qz486

noncomputable def ep1235 := ep1212 (@ep1213 48123000000000000000000 (ep1228 rfl) (ep1233 rfl)) qz197 rfl rfl rfl rfl rfl rfl

noncomputable def ep1236 := @ep1210 4289750018849345993 48123000000000000000000 (ep1235 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz105 (↑qz2) Bool.false 120447 131072 1 524288 Bool.false 0 1 0 1 (@ep594 131072 1 524288 (ep596 rfl) (ep598 rfl) rfl rfl) (@ep599 1 0 1 (ep601 rfl) (ep603 rfl) rfl rfl))

noncomputable abbrev qz487 := (@HPow.hPow Complex Int Complex qz598 qz640 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz198 := qz487

noncomputable def ep1237 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz89 qz188 (@HSub.hSub Int Int Int qz411 qz91 (@HMul.hMul Int Int Int qz412 qz92 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz89 qz188 (@HSub.hSub Int Int Int qz411 qz91 (@HMul.hMul Int Int Int qz412 qz92 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108) qz198)) Bool.false 3033339 68719476736 3 68719476736

noncomputable def ep1238 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz89 qz188 (@HSub.hSub Int Int Int qz411 qz91 (@HMul.hMul Int Int Int qz412 qz92 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108) qz198) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1239 := @ep1238 0 1 0 1 Bool.false 3033339 68719476736 3 68719476736 Bool.true 1372080341 1073741824000 1357 1073741824000 Bool.false 3033339 3033339 68719476736 3 68719476736 Bool.true 1372080341 1372080341 1073741824000 1357

noncomputable def ep1240 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz89 qz188 (@HSub.hSub Int Int Int qz411 qz91 (@HMul.hMul Int Int Int qz412 qz92 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1241 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108) qz198 Bool.false 3033339 68719476736 3 68719476736 Bool.true 1372080341 1073741824000 1357 1073741824000

noncomputable abbrev qz199 := (Complex.re qz487)

noncomputable abbrev qz200 := (Complex.im qz487)

noncomputable def ep1242 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108)) qz199) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108)) qz200) 3033339 68719476736 3 68719476736 0 1 0

noncomputable def ep1243 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108)) qz199 1 12 0 1 9100017 17179869184 9 17179869184 3033339

noncomputable def ep1244 := @Enclosure.Complex.IsNear.re_isNear qz198 Bool.false 9100017 17179869184 9 17179869184 Bool.true 4116241023 268435456000 4071 268435456000

noncomputable abbrev qz488 := (@HPow.hPow Complex Nat Complex qz603 qz640 1)

noncomputable abbrev qz201 := (@Inv.inv Complex Complex.instInv qz488)

noncomputable def ep1245 := @Enclosure.Complex.IsNear.of_eq qz198 qz201 Bool.false 9100017 17179869184 9 17179869184 Bool.true 4116241023 268435456000 4071

noncomputable def ep1246 := @Enclosure.Complex.IsNear.of_parts qz201 Bool.false 9100017 17179869184 9 17179869184 Bool.true 4116241023 268435456000 4071

noncomputable abbrev qz202 := (Complex.re qz488)

noncomputable abbrev qz203 := qz488

noncomputable def ep1247 := @Enclosure.Real.IsNear.mulLit_ff qz202 (@Inv.inv Real Real.instInv (@DFunLike.coe qz114 Complex (fun (x : Complex) => Real) qz115 Complex.normSq qz203)) 9000 4000 0 1 1011113 4294967296 1 4294967296

noncomputable def ep1248 := @Enclosure.Complex.IsNear.re_isNear qz203 Bool.false 9000 4000 0 1 Bool.false 260544 4000 0 1

noncomputable def ep1249 := @Enclosure.Complex.IsNear.of_eq qz203 qz188 Bool.false 9000 4000 0 1 Bool.false 260544 4000 0

noncomputable def ep1250 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz114 Complex (fun (x : Complex) => Real) qz115 Complex.normSq qz203)) Bool.false 1011113 4294967296 1 4294967296 1011113 4294967296 1

noncomputable abbrev qz204 := (Complex.im qz488)

noncomputable def ep1251 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz114 Complex (fun (x : Complex) => Real) qz115 Complex.normSq qz203) (@HAdd.hAdd Real Real Real qz424 (@HMul.hMul Real Real Real qz0 qz202 qz202) (@HMul.hMul Real Real Real qz0 qz204 qz204)) Bool.false 1061940249 250000 0 1

noncomputable def ep1252 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz202 qz202) (@HMul.hMul Real Real Real qz0 qz204 qz204) 81 16 0 1 66292164 15625

noncomputable def ep1253 := @Enclosure.Real.IsNear.mulLit_ff qz202 qz202 9000 4000 0 1 9000 4000 0 1

noncomputable def ep1254 := @Enclosure.Real.IsNear.mulLit_ff qz204 qz204 260544 4000 0 1 260544 4000 0 1

noncomputable def ep1255 := @Enclosure.Complex.IsNear.im_isNear qz203 Bool.false 9000 4000 0 1 Bool.false 260544 4000 0 1

noncomputable abbrev qz205 := (ep1248 (@ep1249 1 (BSN.pow_one_c qz476) qz486))

noncomputable abbrev qz206 := (ep1255 (@ep1249 1 (BSN.pow_one_c qz476) qz486))

noncomputable def ep1256 := @ep1252 0 1 1061940249 1061940249 250000 0 1 (@ep1253 81 16 0 1 qz205 qz205 rfl) (@ep1254 66292164 15625 0 1 qz206 qz206 rfl)

noncomputable def ep1257 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz114 Complex (fun (x : Complex) => Real) qz115 Complex.normSq qz203) 1061940249 250000 0 1 505556 505557 2147483648 (ep1251 (Enclosure.Complex.normSq_eq_mul_add_mul qz203) (ep1256 rfl rfl)) rfl

noncomputable def ep1258 := @Enclosure.Real.IsNear.of_eq (Complex.re qz201) (@HMul.hMul Real Real Real qz0 qz202 (@Inv.inv Real Real.instInv (@DFunLike.coe qz114 Complex (fun (x : Complex) => Real) qz115 Complex.normSq qz203))) Bool.false 9100017 17179869184 9 17179869184 (Enclosure.Complex.inv_re_eq_mul qz203) (@ep1247 9100017 17179869184 9 17179869184 qz205 (@ep1250 4294967296 (ep1257 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep1259 := @Enclosure.Real.IsNear.of_eq (Complex.im qz201) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz204) (@Inv.inv Real Real.instInv (@DFunLike.coe qz114 Complex (fun (x : Complex) => Real) qz115 Complex.normSq qz203))) Bool.true 4116241023 268435456000 4071 268435456000 (Enclosure.Complex.inv_im_eq_mul qz203)

noncomputable def ep1260 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz204) (@Inv.inv Real Real.instInv (@DFunLike.coe qz114 Complex (fun (x : Complex) => Real) qz115 Complex.normSq qz203)) 260544 4000 0 1 1011113 4294967296 1

noncomputable def ep1261 := @ep1260 4294967296 4116241023 268435456000 4071 268435456000 (@Enclosure.Real.IsNear.neg qz204 Bool.false 260544 4000 0 1 qz206) (@ep1250 4294967296 (ep1257 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep1262 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108)) qz200 0 1 0 1 4116241023 268435456000 4071 268435456000 0

noncomputable def ep1263 := @Enclosure.Complex.IsNear.im_isNear qz198 Bool.false 9100017 17179869184 9 17179869184 Bool.true 4116241023 268435456000 4071 268435456000

noncomputable abbrev qz207 := (@ep1245 268435456000 (BSN.zpow_one_sub_two_mul qz476 1 1 rfl rfl) (@ep1246 268435456000 ep1258 (ep1259 ep1261)))

noncomputable def ep1264 := @ep1242 1 3033339 3033339 68719476736 3 68719476736 (@ep1243 68719476736 3 68719476736 ep613 (ep1244 qz207) rfl) (@ep1262 1 0 1 ep633 (ep1263 qz207) rfl) rfl

noncomputable def ep1265 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108)) qz200) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108)) qz199) 1372080341 1073741824000 1357 1073741824000 0 1 0

noncomputable def ep1266 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108)) qz200 1 12 0 1 4116241023 268435456000 4071 268435456000 1372080341

noncomputable def ep1267 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108)) qz199 0 1 0 1 9100017 17179869184 9 17179869184 0

noncomputable def ep1268 := @ep1265 1 1372080341 1372080341 1073741824000 1357 1073741824000 (@ep1266 1073741824000 1357 1073741824000 ep613 (ep1263 qz207) rfl) (@ep1267 1 0 1 ep633 (ep1244 qz207) rfl) rfl

noncomputable def ep1269 := @ep1239 1073741824000 (@ep1240 0 1 0 1 (BSN.stirling_sum_base qz188) qz121) (ep1241 (ep1264 rfl) (ep1268 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep1270 := @ep1207 59005331348823632743 281474976710656000 140568521504343601920499 ep1200 (ep1236 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep1237 Bool.true 1372080341 1073741824000 1357 1073741824000 (BSN.stirling_sum_succ qz188 0 1 rfl) (ep1269 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep1271 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz185 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz149 2) Bool.false 9404806363305701 1125899906842624 31250000144369 12030750000000000000 Bool.false 877798613353891 281474976710656

noncomputable abbrev qz208 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz272 qz477 qz420))

noncomputable def ep1272 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz149 2) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz149 1) qz208) Bool.false 9404806363305701 1125899906842624 31250000144369 12030750000000000000 Bool.false 877798613353891 281474976710656 250000000048123 48123000000000000000

noncomputable def ep1273 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz149 1) qz208 Bool.false 9404607184197349 2251799813685248 31250000144369 24061500000000000000 Bool.false 882119350453667 562949953421312 250000000048123 96246000000000000000 Bool.false

noncomputable def ep1274 := nat_lit 42355482433275224648952835997696

noncomputable def ep1275 := nat_lit 988313377001730400412955049984

noncomputable abbrev qz209 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz272 qz477 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep1276 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz149 1) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz149 0) qz209) Bool.false 9404607184197349 2251799813685248 31250000144369 24061500000000000000 Bool.false 882119350453667 562949953421312 250000000048123 96246000000000000000

noncomputable def ep1277 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz149 0) qz209 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz489 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz642))

noncomputable def ep1278 := @Enclosure.Complex.IsNear.of_eq qz209 qz489 Bool.false 9404607184197349 2251799813685248 31250000144369 24061500000000000000 Bool.false 882119350453667 562949953421312 250000000048123 96246000000000000000

noncomputable def ep1279 := BSN.log_dyadic_bound 2348175936 133420175936 2 1 53402830040379580428288 1048576 384984 5513930226409476096 5513930226409476096 36913 135768351872 131072000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 2348175936) (BSN.artanhQ 133420175936) 0 1 5513930226409476096 53402830040379580428288 5513930226409476096 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1280 := @Enclosure.Real.IsNear.mulLit_ff qz100 (Real.log (Enclosure.sfrac Bool.false 67884175936 16000000)) 1 2 0 1 9404607184197349 1125899906842624 31250000144369 12030750000000000000 9404607184197349 2251799813685248 31250000144369 24061500000000000000 qz415 (BSN.isNear_log_sfrac 67884175936 16000000 9404607184197349 1125899906842624 31250000144369 12030750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 67884175936) qz602)) Bool.false 315566252248861421600768 37778931862957161709568 1000000004619808 384984000000000000000 9404607184197349 1125899906842624 31250000144369 12030750000000000000 (BSN.log_rat_reduce_isNear 67884175936 16000000 12 135768351872 131072000000 36913 1048576 24973259072661432 36028797018963968 384984 1000000000000000 rfl rfl rfl rfl (ep1279 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1281 := BSN.arctan_dyadic_bound_f 1000 260544 1 0 1048576 384984 0 1 1 0 1 1 4024 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 260544) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 260544) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz490 := (@Nat.cast Real Real.instNatCast 260544)

noncomputable def ep1282 := @Enclosure.Real.IsNear.subLit_ff_p qz101 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz426 qz490)) 884279719003555 562949953421312 1 2000000000000000 4024 1048576 1 384984 924969180021304328192 882119350453667 562949953421312 250000000048123 96246000000000000000 qz102 (ep1281 rfl) rfl rfl

noncomputable abbrev qz210 := (@HAdd.hAdd Complex Complex Complex qz272 qz477 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz491 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz642)

noncomputable def ep1283 := @ep1277 9404607184197349 2251799813685248 31250000144369 24061500000000000000 Bool.false 882119350453667 562949953421312 250000000048123 96246000000000000000 Bool.false 9404607184197349 9404607184197349 2251799813685248 31250000144369 24061500000000000000 Bool.false 882119350453667 882119350453667 562949953421312 250000000048123 96246000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz149 0) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz149) qz121) (ep1278 (@congrArg Complex Complex qz210 qz491 Complex.log (BSN.w_shift_mk qz149 Bool.false 130272 1000 0 qz150 rfl)) (@Enclosure.Complex.IsNear.of_parts qz489 Bool.false 9404607184197349 2251799813685248 31250000144369 24061500000000000000 Bool.false 882119350453667 562949953421312 250000000048123 96246000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz489) (@HMul.hMul Real Real Real qz0 qz100 (Real.log (Enclosure.sfrac Bool.false 67884175936 16000000))) Bool.false 9404607184197349 2251799813685248 31250000144369 24061500000000000000 (Enclosure.clog_re_eq 1000 260544 4000 67884175936 16000000 rfl rfl rfl) (ep1280 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz489) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz490 qz426)) Bool.false 882119350453667 562949953421312 250000000048123 96246000000000000000 (Enclosure.clog_im_eq 1000 260544 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz490 qz426)) (@HSub.hSub Real Real Real qz404 qz101 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz426 qz490))) Bool.false 882119350453667 562949953421312 250000000048123 96246000000000000000 (BSN.arctan_recip 260544 1000 rfl rfl) ep1282)))) rfl rfl

noncomputable abbrev qz492 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz642))

noncomputable def ep1284 := @Enclosure.Complex.IsNear.of_eq qz208 qz492 Bool.false 9405005542414053 2251799813685248 31250000144369 24061500000000000000 Bool.false 873477876254115 562949953421312 250000000048123 96246000000000000000

noncomputable def ep1285 := BSN.log_dyadic_bound 2372175936 133444175936 2 1 53422044273714364428288 1048576 384984 5627218671337476096 5627218671337476096 37284 135816351872 131072000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 2372175936) (BSN.artanhQ 133444175936) 0 1 5627218671337476096 53422044273714364428288 5627218671337476096 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1286 := @Enclosure.Real.IsNear.mulLit_ff qz100 (Real.log (Enclosure.sfrac Bool.false 67908175936 16000000)) 1 2 0 1 9405005542414053 1125899906842624 31250000144369 12030750000000000000 9405005542414053 2251799813685248 31250000144369 24061500000000000000 qz415 (BSN.isNear_log_sfrac 67908175936 16000000 9405005542414053 1125899906842624 31250000144369 12030750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 67908175936) qz602)) Bool.false 315579618932555457232896 37778931862957161709568 1000000004619808 384984000000000000000 9405005542414053 1125899906842624 31250000144369 12030750000000000000 (BSN.log_rat_reduce_isNear 67908175936 16000000 12 135816351872 131072000000 37284 1048576 24973259072661432 36028797018963968 384984 1000000000000000 rfl rfl rfl rfl (ep1285 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1287 := BSN.arctan_dyadic_bound_f 5000 260544 1 0 1048576 384984 0 1 1 0 1 1 20120 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 260544) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 260544) 0 0 rfl) rfl rfl rfl

noncomputable def ep1288 := @Enclosure.Real.IsNear.subLit_ff_p qz101 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz430 qz490)) 884279719003555 562949953421312 1 2000000000000000 20120 1048576 1 384984 915907937571034890240 873477876254115 562949953421312 250000000048123 96246000000000000000 qz102 (ep1287 rfl) rfl rfl

noncomputable abbrev qz211 := (@HAdd.hAdd Complex Complex Complex qz272 qz477 qz420)

noncomputable abbrev qz493 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz642)

noncomputable def ep1289 := @ep1273 9405005542414053 2251799813685248 31250000144369 24061500000000000000 Bool.false 873477876254115 562949953421312 250000000048123 96246000000000000000 Bool.false ep1274 9404806363305701 1125899906842624 31250000144369 12030750000000000000 Bool.false ep1275 877798613353891 281474976710656 250000000048123 48123000000000000000 (ep1276 (BSN.log_sum_c_succ qz149 0 1 rfl) (ep1283 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1284 (@congrArg Complex Complex qz211 qz493 Complex.log (BSN.w_shift_mk qz149 Bool.false 130272 1000 1 qz150 rfl)) (@Enclosure.Complex.IsNear.of_parts qz492 Bool.false 9405005542414053 2251799813685248 31250000144369 24061500000000000000 Bool.false 873477876254115 562949953421312 250000000048123 96246000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz492) (@HMul.hMul Real Real Real qz0 qz100 (Real.log (Enclosure.sfrac Bool.false 67908175936 16000000))) Bool.false 9405005542414053 2251799813685248 31250000144369 24061500000000000000 (Enclosure.clog_re_eq 5000 260544 4000 67908175936 16000000 rfl rfl rfl) (ep1286 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz492) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz490 qz430)) Bool.false 873477876254115 562949953421312 250000000048123 96246000000000000000 (Enclosure.clog_im_eq 5000 260544 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz490 qz430)) (@HSub.hSub Real Real Real qz404 qz101 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz430 qz490))) Bool.false 873477876254115 562949953421312 250000000048123 96246000000000000000 (BSN.arctan_recip 260544 5000 rfl rfl) ep1288)))) rfl rfl

noncomputable def ep1290 := @ep1199 ep1200 Bool.false 9404806363305701 1125899906842624 31250000144369 12030750000000000000 Bool.false 877798613353891 281474976710656 250000000048123 48123000000000000000 Bool.true ep1201 115337875166168076401 1125899906842624000 739959499806240311921347 ep1196 Bool.false ep1202 58127532735469741743 281474976710656000 49586840501973498794833 ep1192 (@ep1203 1125899906842624000 ep1198 ep554 Bool.false 59005331348823632743 281474976710656000 140568521504343601920499 ep1200 (BSN.logGammaStirling_unfold 1 qz188) (ep1270 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep1271 250000000048123 48123000000000000000 (BSN.log_sum_c_eq qz149 2) (ep1272 (BSN.log_sum_c_succ qz149 1 2 rfl) (ep1289 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz212 := (@HDiv.hDiv Real Real Real qz270 qz443 (2 : Real))

noncomputable def ep1291 := @Enclosure.Real.IsNear.mulLit_ff qz212 (Real.log Real.pi) 130272 2000 0 1 75021 65536 1 262144 305410491 4096000 4071 16384000 (@Enclosure.Real.IsNear.of_eq qz212 (Enclosure.sfrac Bool.false 130272 2000) Bool.false 130272 2000 0 1 (BSN.t_half_eq qz149 Bool.false 130272 1000 qz150) (Enclosure.Real.IsNear.const Bool.false 130272 2000)) EMRow43.d5 rfl

noncomputable def ep1292 := @ep1194 4071 16384000 ep1195 37139883604264904367 281474976710656000 180192662501973498794833 ep1192 (@ep1197 49586840501973498794833 ep1192 (ep1290 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep1291 rfl rfl

noncomputable def ep1293 := BSN.cos_dyadic_bound_f 1032909 2147483648 1 0 1048576 385360 0 1 1 0 1 1 1048575 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 1032909) qz15 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 1032909) qz16 0 0 rfl) rfl rfl

noncomputable def ep1294 := @ep1191 131072 Bool.false 1048575 1048576 1 192492 (@ep1193 8647303 65536 45 131072 ep1292 rfl) (Enclosure.sfrac_false_div 8647303 65536) (BSN.cos_reduce0 qz478 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4542781989161271296) qz337) 226375608064910080 72057594037927936 Bool.false 1048575 1048576 21 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q0 8647303 65536 226375608064910080 72057594037927936 21 4542781989161271296 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1048575 1048576 4542781989161271296 9444732965739290427392 1032909 2147483648 385360 384984 (ep1293 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1295 := nat_lit 2682253442274359010325799

noncomputable def ep1296 := nat_lit 34422808150371762219012848917

noncomputable abbrev qz494 := (@HPow.hPow Complex Complex Complex qz530 qz604 qz609)

noncomputable abbrev qz213 := qz494

noncomputable abbrev qz214 := (@HAdd.hAdd Complex Complex Complex qz272 (@HDiv.hDiv Complex Complex Complex qz409 qz433 (@HSub.hSub Complex Complex Complex qz401 qz441 (1 : Complex))) qz408)

noncomputable def ep1297 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz146 1 33) (@HAdd.hAdd Complex Complex Complex qz4 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 33, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz147) (@HMul.hMul Complex Complex Complex qz80 qz213 (@HAdd.hAdd Complex Complex Complex qz4 qz214 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1))))))) Bool.false ep1186 ep1187 ep1188

noncomputable def ep1298 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 33, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz147) (@HMul.hMul Complex Complex Complex qz80 qz213 (@HAdd.hAdd Complex Complex Complex qz4 qz214 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))))) Bool.false 596571813335 549755813888 40509647116639 6613974757933056

noncomputable def ep1299 := nat_lit 9997696464748464338617543

noncomputable def ep1300 := nat_lit 383279464922575000171195303

noncomputable def ep1301 := nat_lit 1861076337464998537318201

noncomputable def ep1302 := nat_lit 381107107493186077480058917

noncomputable def ep1303 := nat_lit 63382628038721392393668222596537122816

noncomputable def ep1304 := nat_lit 737292212105714931757582912644448256

noncomputable def ep1305 := @ep1298 Bool.false 10816593261 274877906944 162090471942145 26455899031732224 Bool.true ep1299 ep1187 ep1300 ep1189 Bool.true ep1301 ep1187 ep1302 ep1189 Bool.false ep1303 ep1186 ep1187 ep1188 ep1189 Bool.false ep1304 ep1295 ep1187

noncomputable def ep1306 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 33, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz147) (BSN.headSumC qz146 33) Bool.false 596571813335 549755813888 40509647116639 6613974757933056 Bool.false 10816593261 274877906944 162090471942145

noncomputable def ep1307 := @Enclosure.Complex.IsNear.mul qz213 (@HAdd.hAdd Complex Complex Complex qz4 qz214 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1))))) Bool.true ep1299 ep1187 ep1300 ep1189 Bool.true

noncomputable def ep1308 := nat_lit 2666140375615164088162043

noncomputable abbrev qz215 := (Complex.re qz494)

noncomputable abbrev qz216 := (Complex.im qz494)

noncomputable def ep1309 := @Enclosure.Real.IsNear.subLit_tt_n (@HMul.hMul Real Real Real qz0 qz215 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz214 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz216 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz214 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1))))))) 80394542503132946787179 923663079697343638929408 ep1308

noncomputable def ep1310 := nat_lit 44449438384275267936199901184

noncomputable def ep1311 := nat_lit 4810745206756998119424000

noncomputable def ep1312 := nat_lit 2083829915444978714622497

noncomputable def ep1313 := nat_lit 231507491584767020501041152000

noncomputable def ep1314 := nat_lit 384770962771200481882022930146194127927803641856

noncomputable def ep1315 := @Enclosure.Real.IsNear.mulLit_tf qz215 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz214 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))))) 191289290543 1099511627776 6343765199231 52911798063464448 420277278853

noncomputable abbrev qz217 := (@HMul.hMul Real Real Real qz267 qz443 qz605)

noncomputable abbrev qz218 := (Real.sin (@HMul.hMul Real Real Real qz267 qz443 qz605))

noncomputable abbrev qz644 := (@Neg.neg Real Real.instNeg qz218)

noncomputable def ep1316 := @Enclosure.Complex.IsNear.of_eq qz213 (Complex.mk (@HMul.hMul Real Real Real qz0 qz134 (Real.cos qz217)) (@HMul.hMul Real Real Real qz0 qz134 qz644)) Bool.true 191289290543 1099511627776 6343765199231 52911798063464448 Bool.true 6497627201 1099511627776 6295046725229 52911798063464448 (BSN.cpow_neg_s_mk qz149 130272 1000 33 qz150 rfl)

noncomputable def ep1317 := @Enclosure.Real.IsNear.mulLit_ff qz149 qz137 130272 1000 0 1 15746868335186131 4503599627370496 50000000048123 9624600000000000000 64105500992542739301 140737488355328000 67850000065302911 100256250000000000000 qz151 (BSN.isNear_log_sfrac 33 1 15746868335186131 4503599627370496 50000000048123 9624600000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz437 Bool.false 66047152845744529997824 18889465931478580854784 1000000000962460 192492000000000000000 15746868335186131 4503599627370496 50000000048123 9624600000000000000 (BSN.log_rat_reduce_isNear 33 1 5 66 64 16133 524288 24973259072661432 36028797018963968 192492 1000000000000000 rfl rfl rfl rfl (ep691 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1318 := nat_lit 7644290618089918539272419723473172618620666113988813756198675895729479368048640

noncomputable def ep1319 := nat_lit 14075733622615629666959192369012499124268950849721472927475417422974246977536

noncomputable def ep1320 := nat_lit 19997971859608408964347927250022765193043404378118772691018714765368582897401856

noncomputable def ep1321 := BSN.sin_dyadic_bound_f 3300341496 2147483648 3 2 1048576 385360 ep1318 ep64 ep1319 ep1320 ep66 ep1319 1047971 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3300341496) qz20 0 2 ep1318 ep64 ep1319 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3300341496) qz21 0 2 ep1320 ep66 ep1319 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz495 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 477623201) qz24)

noncomputable def ep1322 := @Enclosure.Real.IsNear.cos_image qz217 qz495 Bool.false 477623201 1048576 711 1048576 Bool.true 1047971 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz217 Bool.false 64105500992542739301 140737488355328000 67850000065302911 100256250000000000000 477623201 1048576 711 1048576 (ep1317 rfl) rfl) (Enclosure.sfrac_false_div 477623201 1048576) (BSN.cos_reduce1 qz495 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 232240886450949457969152) qz25) 226375608064910080 72057594037927936 Bool.false 1047971 1048576 72 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q1 477623201 1048576 226375608064910080 72057594037927936 72 232240886450949457969152 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1047971 1048576 232240886450949457969152 151115727451828646838272 3300341496 2147483648 385360 384984 (ep1321 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1323 := nat_lit 4253084002771117246114437265204657009955600708149217185855920127593254869794816

noncomputable def ep1324 := nat_lit 12731100541068120479009393410875946031618264222748208611712809547933816115429376

noncomputable def ep1325 := BSN.cos_dyadic_bound_f 3300341496 2147483648 3 2 1048576 385360 ep1323 ep57 ep1319 ep1324 ep60 ep1319 35597 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3300341496) qz15 0 2 ep1323 ep57 ep1319 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3300341496) qz16 0 2 ep1324 ep60 ep1319 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1326 := @Enclosure.Real.IsNear.sin_image qz217 qz495 Bool.false 477623201 1048576 711 1048576 Bool.false 35597 1048576 1 192492 (@Enclosure.Real.IsNear.recentre' qz217 Bool.false 64105500992542739301 140737488355328000 67850000065302911 100256250000000000000 477623201 1048576 711 1048576 (ep1317 rfl) rfl) (Enclosure.sfrac_false_div 477623201 1048576) (BSN.sin_reduce1 qz495 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 232240886450949457969152) qz25) 226375608064910080 72057594037927936 Bool.false 35597 1048576 72 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q1 477623201 1048576 226375608064910080 72057594037927936 72 232240886450949457969152 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 35597 1048576 232240886450949457969152 151115727451828646838272 3300341496 2147483648 385360 384984 (ep1325 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1327 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz134 (Real.cos qz217)) (@HMul.hMul Real Real Real qz0 qz134 qz644) Bool.true 191289290543 1099511627776 6343765199231 52911798063464448 Bool.true 6497627201 1099511627776 6295046725229 52911798063464448 (@Enclosure.Real.IsNear.mulLit_ft qz134 (Real.cos qz217) 182533 1048576 1 1048576 1047971 1048576 34477597 50460622848 191289290543 1099511627776 6343765199231 52911798063464448 qz439 (@Enclosure.Real.IsNear.recentre' (Real.cos qz217) Bool.true 1047971 1048576 137910388 201842491392 1047971 1048576 34477597 50460622848 (ep1322 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz134 qz644 182533 1048576 1 1048576 35597 1048576 34477597 50460622848 6497627201 1099511627776 6295046725229 52911798063464448 qz439 (@Enclosure.Real.IsNear.neg qz218 Bool.false 35597 1048576 34477597 50460622848 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 35597 1048576 137910388 201842491392 35597 1048576 34477597 50460622848 (ep1326 rfl rfl) rfl)) rfl)

noncomputable def ep1328 := @ep1315 840066677208 0 1 80394542503132946787179 923663079697343638929408 ep1308 ep1310 (@Enclosure.Complex.IsNear.re_isNear qz213 Bool.true 191289290543 1099511627776 6343765199231 52911798063464448 Bool.true 6497627201 1099511627776 6295046725229 52911798063464448 (ep1316 ep1327))

noncomputable def ep1329 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz214 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1))))) Bool.false 420277278853 840066677208 0 1 Bool.false

noncomputable def ep1330 := @Enclosure.Complex.IsNear.addLitP qz214 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) Bool.false 1058627749 2121380498 0 1 Bool.true 268686000

noncomputable def ep1331 := @ep1330 1060690249 0 1 Bool.false 1 792 0 1 Bool.false 1357 4125 0 1 Bool.false 840554557706 420277278853 840066677208 0 1 Bool.false 331026917893 331026917893 4375347277125 0 1

noncomputable abbrev qz219 := (@HDiv.hDiv Complex Complex Complex qz409 qz433 (@HSub.hSub Complex Complex Complex qz401 qz441 (1 : Complex)))

noncomputable def ep1332 := @Enclosure.Complex.IsNear.addLitP qz219 qz105 Bool.true 66000000 67884175936 0 1 Bool.true 17195904000 67884175936 0 1

noncomputable def ep1333 := @Enclosure.Complex.IsNear.of_eq qz219 (Complex.mk (Enclosure.sfrac Bool.true 66000000 67884175936) (Enclosure.sfrac Bool.true 17195904000 67884175936)) Bool.true 66000000 67884175936 0 1 Bool.true 17195904000 67884175936 0 1

noncomputable def ep1334 := @ep1332 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 67752175936 1058627749 2121380498 0 1 Bool.true 17195904000 268686000 1060690249 0 1 (ep1333 (BSN.N_div_s_sub_one_mk qz149 130272 1000 33 qz150 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 66000000 67884175936) (Enclosure.sfrac Bool.true 17195904000 67884175936) Bool.true 66000000 67884175936 0 1 Bool.true 17195904000 67884175936 0 1 (Enclosure.Real.IsNear.const Bool.true 66000000 67884175936) (Enclosure.Real.IsNear.const Bool.true 17195904000 67884175936))) qz106 rfl

noncomputable def ep1335 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1))) qz140)) Bool.false 1 792 0 1

noncomputable def ep1336 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1))) qz140) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1337 := @ep1336 0 1 0 1 Bool.false 1 792 0 1 Bool.false 1357 4125 0 1 Bool.false 1 1 792 0 1 Bool.false 1357 1357 4125 0

noncomputable def ep1338 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1339 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1))) qz140 Bool.false 1 792 0 1 Bool.false 1357 4125 0 1

noncomputable def ep1340 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)))) qz141) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)))) qz142) 1 792 0 1 0 1 0

noncomputable def ep1341 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)))) qz141 1 24 0 1 1 33 0 1 1

noncomputable def ep1342 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep1343 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep1344 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)) qz146 Bool.false 1 2 0 1 Bool.false 130272 1000 0 1 (BSN.ascPochhammer_one_eval qz146)

noncomputable def ep1345 := ep1344 (@Enclosure.Complex.IsNear.of_eq qz146 (Complex.mk qz100 qz149) Bool.false 1 2 0 1 Bool.false 130272 1000 0 1 (BSN.s_crit_mk qz149 Bool.false 130272 1000 qz150) (@Enclosure.Complex.IsNear.mk qz100 qz149 Bool.false 1 2 0 1 Bool.false 130272 1000 0 1 qz415 qz151))

noncomputable def ep1346 := @ep1343 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep715) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 130272 1000 0 1 ep1345)

noncomputable def ep1347 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 130272 1000 0 1 0 1 0

noncomputable def ep1348 := @ep1347 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep715) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 130272 1000 0 1 ep1345)

noncomputable def ep1349 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)))) 1357 125 0 1 0 1 0 1 1357

noncomputable def ep1350 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 130272 1000 0 1 1357 125 0

noncomputable def ep1351 := @ep1350 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep715) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 130272 1000 0 1 ep1345)

noncomputable def ep1352 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep1353 := @ep1352 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep715) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 130272 1000 0 1 ep1345)

noncomputable def ep1354 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 1357 125 0 1 (@ep1342 1 24 0 1 (ep1346 rfl) (ep1348 rfl) rfl rfl) (@ep1349 1357 125 0 1 (ep1351 rfl) (ep1353 rfl) rfl rfl)

noncomputable def ep1355 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 1357 125 0 1 ep1354

noncomputable def ep1356 := @ep1341 792 0 1 ep1355 qz143

noncomputable def ep1357 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)))) qz142 1357 125 0 1 0 1 0 1 0

noncomputable def ep1358 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 1357 125 0 1 ep1354

noncomputable def ep1359 := @ep1357 1 0 1 ep1358 qz144

noncomputable def ep1360 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)))) qz142) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)))) qz141) 0 1 0 1 1357 4125 0

noncomputable def ep1361 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)))) qz142 1 24 0 1 0 1 0 1 0

noncomputable def ep1362 := @ep1361 1 0 1 ep1355 qz144

noncomputable def ep1363 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)))) qz141 1357 125 0 1 1 33 0 1 1357

noncomputable def ep1364 := @ep1363 4125 0 1 ep1358 qz143

noncomputable def ep1365 := @ep1337 1 (@ep1338 0 1 0 1 (BSN.bern_sum_base qz146 33) qz121) (ep1339 (@ep1340 1 1 1 792 0 1 (ep1356 rfl) (ep1359 rfl) rfl rfl) (@ep1360 1 1357 1357 4125 0 1 (ep1362 rfl) (ep1364 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep1366 := ep1331 (ep1334 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep1335 Bool.false 1357 4125 0 1 (BSN.bern_sum_succ qz146 33 0 1 1 rfl rfl) (ep1365 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep1367 := @Enclosure.Real.IsNear.mulLit_tf qz216 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz214 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))))) 6497627201 1099511627776 6295046725229 52911798063464448 331026917893

noncomputable def ep1368 := @ep1367 4375347277125 0 1 2150889505964750407493 ep1311 ep1312 ep1313 (@Enclosure.Complex.IsNear.im_isNear qz213 Bool.true 191289290543 1099511627776 6343765199231 52911798063464448 Bool.true 6497627201 1099511627776 6295046725229 52911798063464448 (ep1316 ep1327))

noncomputable def ep1369 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz214 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1))))) Bool.false 420277278853 840066677208 0 1 Bool.false

noncomputable def ep1370 := nat_lit 2099957041738311023740283

noncomputable def ep1371 := @Enclosure.Real.IsNear.addLit_tt (@HMul.hMul Real Real Real qz0 qz215 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz214 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz216 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz214 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1))))))) 63321904274387882385899 ep1311 ep1370

noncomputable def ep1372 := nat_lit 2645665107931732903282337

noncomputable def ep1373 := nat_lit 71625312558948889550128456363737558730294689792

noncomputable def ep1374 := @Enclosure.Real.IsNear.mulLit_tf qz215 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz214 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))))) 191289290543 1099511627776 6343765199231 52911798063464448 331026917893

noncomputable def ep1375 := @ep1374 4375347277125 0 1 63321904274387882385899 ep1311 ep1370 ep1313 (@Enclosure.Complex.IsNear.re_isNear qz213 Bool.true 191289290543 1099511627776 6343765199231 52911798063464448 Bool.true 6497627201 1099511627776 6295046725229 52911798063464448 (ep1316 ep1327))

noncomputable def ep1376 := @Enclosure.Real.IsNear.mulLit_tf qz216 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz214 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))))) 6497627201 1099511627776 6295046725229 52911798063464448 420277278853

noncomputable def ep1377 := @ep1376 840066677208 0 1 2730805079037514880453 923663079697343638929408 ep1372 ep1310 (@Enclosure.Complex.IsNear.im_isNear qz213 Bool.true 191289290543 1099511627776 6343765199231 52911798063464448 Bool.true 6497627201 1099511627776 6295046725229 52911798063464448 (ep1316 ep1327))

noncomputable abbrev qz645 := (ep1366 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep1378 := @ep1307 ep1301 ep1187 ep1302 ep1189 (@ep1309 ep1310 2150889505964750407493 ep1311 ep1312 ep1313 ep1314 ep1299 ep1187 ep1300 ep1189 (ep1328 (@ep1329 331026917893 4375347277125 0 1 qz645) rfl) (ep1368 (@ep1369 331026917893 4375347277125 0 1 qz645) rfl) rfl rfl) (@ep1371 ep1313 2730805079037514880453 923663079697343638929408 ep1372 ep1310 ep1373 ep1301 ep1187 ep1302 ep1189 (ep1375 (@ep1369 331026917893 4375347277125 0 1 qz645) rfl) (ep1377 (@ep1329 331026917893 4375347277125 0 1 qz645) rfl) rfl rfl)

noncomputable def ep1379 := @ep1305 ep1296 ep1189 (@ep1306 26455899031732224 (BSN.head_sum_c_eq qz146 33) EMRow43.d16) ep1378 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def ep1380 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz146 1 33) Bool.false ep1186 ep1187 ep1188 ep1189 Bool.false ep1295 ep1187 ep1296 ep1189 (@ep1297 ep1189 Bool.false ep1295 ep1187 ep1296 ep1189 (BSN.zetaApproximant_eq_folded' qz146 1 33 rfl) (ep1379 rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep1381 := @Enclosure.Real.IsNear.mulLit_ff (Real.sin (@HSub.hSub Real Real Real qz404 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz184 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz185 (@Nat.cast Complex Complex.instNatCast j))))) qz186)) (Complex.im (zetaApproximant qz146 1 33)) 63 131072 2198303

noncomputable def ep1382 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz404 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz184 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz185 (@Nat.cast Complex Complex.instNatCast j))))) qz186)) Bool.false 504 1048576 8793212

noncomputable def ep1383 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz404 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz184 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz185 (@Nat.cast Complex Complex.instNatCast j))))) qz186) qz478 Bool.false 8647303 65536 45

noncomputable def ep1384 := BSN.sin_dyadic_bound_f 1032909 2147483648 1 0 1048576 385360 0 1 1 0 1 1 504 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 1032909) qz20 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 1032909) qz21 0 0 rfl) rfl rfl

noncomputable def ep1385 := @ep1383 131072 Bool.false 504 1048576 1 192492 (@ep1193 8647303 65536 45 131072 ep1292 rfl) (Enclosure.sfrac_false_div 8647303 65536) (BSN.sin_reduce0 qz478 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4542781989161271296) qz337) 226375608064910080 72057594037927936 Bool.false 504 1048576 21 1000000000000000 384984 192492 (BSN.sin_reduce_arg_pos_rat_q0 8647303 65536 226375608064910080 72057594037927936 21 4542781989161271296 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 504 1048576 4542781989161271296 9444732965739290427392 1032909 2147483648 385360 384984 (ep1384 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1386 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz146 1 33) Bool.false ep1186 ep1187 ep1188 ep1189 Bool.false ep1295 ep1187 ep1296 ep1189 (@ep1297 ep1189 Bool.false ep1295 ep1187 ep1296 ep1189 (BSN.zetaApproximant_eq_folded' qz146 1 33 rfl) (ep1379 rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow43.d17 : Enclosure.Real.IsNear (hardyZApproximantEM 1 33 qz149) Bool.false ep1170 ep1171 ep1172 ep1173 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 33 qz149) ep1174 Bool.false ep1170 ep1171 ep1172 ep1173 (@Eq.refl Real ep1174) (@ep1175 Bool.false ep1170 ep1171 ep1172 ep1173 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz404 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz184 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz185 (@Nat.cast Complex Complex.instNatCast j))))) qz186) (zetaApproximant qz146 1 33)) (@ep1177 ep1178 ep1179 ep1173 ep1180 ep1181 ep1182 ep1183 ep1184 ep1170 ep1171 ep1172 ep1173 (@ep1185 6307577856 ep1186 ep1187 ep1188 ep1189 ep1176 ep1178 ep1179 ep1173 (@ep1190 25230311424 1048575 1048576 2198303 6307577856 (ep1294 rfl rfl) rfl) ep1380 rfl) (@ep1381 6307577856 ep1295 ep1187 ep1296 ep1189 ep1180 ep1181 ep1182 ep1183 (@ep1382 25230311424 63 131072 2198303 6307577856 (ep1385 rfl rfl) rfl) ep1386 rfl) rfl rfl))

theorem EMRow43.d18 : @Eq Nat (Nat.mul (BSN.factNat (Nat.succ (Nat.mul 2 1))) (Nat.pow 4 (Nat.mul 2 1))) 96 := @Eq.refl Nat 96

theorem EMRow43.d19 : @Eq Nat (Nat.mul (Nat.mul 2 1) (Nat.pow (Nat.succ (Nat.mul 4 2)) (Nat.mul 2 1))) 162 := @Eq.refl Nat 162

theorem EMRow43.d20 : @Eq Nat (BSN.factNat (Nat.mul 2 2)) 24 := @Eq.refl Nat 24

theorem EMRow43.d21 : @Eq Nat (Nat.pow 33 (Nat.succ (Nat.mul 2 3))) 42618442977 := @Eq.refl Nat 42618442977

noncomputable abbrev qz646 := (@HAdd.hAdd Complex Complex Complex qz652 qz651 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz496 := qz646

noncomputable abbrev qz220 := (@HDiv.hDiv Real Real Real qz270 (@Norm.norm Complex Complex.instNorm qz496) (@HAdd.hAdd Real Real Real qz424 (Complex.re qz271) qz291))

noncomputable abbrev qz221 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)

noncomputable abbrev qz222 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)))

noncomputable abbrev qz497 := (@HPow.hPow Complex Complex Complex qz530 qz604 (@HSub.hSub Complex Complex Complex qz593 qz531 qz537))

noncomputable abbrev qz223 := qz497

noncomputable def ep1387 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 33))) (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) 51385362137 1855425871872 173498575 1855425871872 2096122698368309039 4035225266123964416 423170228737

noncomputable def ep1388 := nat_lit 4096551796774861180311175168000

noncomputable def ep1389 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 33)) 26561 1769472 1 1769472 1934617 1048576 6459 1048576 51385362137 1855425871872

noncomputable abbrev qz224 := (@HMul.hMul Real Real Real qz267 (2 : Real) Real.pi)

noncomputable abbrev qz647 := (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid)))

noncomputable abbrev qz498 := (@Inv.inv Real Real.instInv (@HPow.hPow Real Nat Real qz647 qz224 2))

noncomputable def ep1390 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 96 162) qz498 96 162 0 1 26561 1048576 1 1048576 26561 1769472 1 1769472

noncomputable def ep1391 := nat_lit 781950621441006189802102638025

noncomputable def ep1392 := nat_lit 19807040628566084398385987584

noncomputable def ep1393 := nat_lit 26986075409044041160201671

noncomputable def ep1394 := nat_lit 1073741824000000000000000000000000000000

noncomputable abbrev qz499 := (@HPow.hPow Real Nat Real qz647 qz224 1)

noncomputable def ep1395 := @Enclosure.Real.IsNear.mulLit_ff qz499 qz224 884279719003555 140737488355328 1 500000000000000 884279719003555 140737488355328 1 500000000000000 ep1391 ep1392 ep1393 ep1394

noncomputable def ep1396 := ep1395 (@Enclosure.Real.IsNear.of_eq qz499 qz224 Bool.false 884279719003555 140737488355328 1 500000000000000 (BSN.pow_one_r qz224) (@Enclosure.Real.IsNear.of_eq qz224 qz268 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz269)) (@Enclosure.Real.IsNear.of_eq qz224 qz268 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz269) rfl

noncomputable abbrev qz500 := (@HPow.hPow Real Nat Real qz647 qz224 2)

noncomputable def ep1397 := @Enclosure.Real.IsNear.inv_image qz500 ep1391 ep1392 ep1393 ep1394 13280 13281 524288 (@Enclosure.Real.IsNear.of_eq qz500 (@HMul.hMul Real Real Real qz0 qz499 qz224) Bool.false ep1391 ep1392 ep1393 ep1394 (BSN.pow_succ_r qz224 1 2 rfl) ep1396) rfl rfl rfl

noncomputable def ep1398 := ep1390 (Enclosure.Real.IsNear.const Bool.false 96 162) (@Enclosure.Real.IsNear.recentre' qz498 Bool.false 26561 1048576 1 1048576 26561 1048576 1 1048576 (ep1397 rfl rfl rfl) rfl)

noncomputable def ep1399 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 33)) (Real.sqrt (@HAdd.hAdd Real Real Real qz424 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 33)) (Complex.re (zetaApproximant qz5 1 33))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 33)) (Complex.im (zetaApproximant qz5 1 33))))) Bool.false 1934617 1048576 6459 1048576

noncomputable def ep1400 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz424 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 33)) (Complex.re (zetaApproximant qz5 1 33))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 33)) (Complex.im (zetaApproximant qz5 1 33))))) Bool.false 1934617 1048576 6459 1048576

noncomputable def ep1401 := nat_lit 132567502310954678399357446457343253328424521

noncomputable def ep1402 := nat_lit 38944133249764824684986985331406615347200000

noncomputable def ep1403 := nat_lit 4678033667516418499971159718841761933465207765862091294035123

noncomputable def ep1404 := nat_lit 205852875402861707646612168056377644432207610106131513344000000

noncomputable def ep1405 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz424 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 33)) (Complex.re (zetaApproximant qz5 1 33))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 33)) (Complex.im (zetaApproximant qz5 1 33)))) ep1401 ep1402 ep1403 ep1404 964079 970538

noncomputable def ep1406 := nat_lit 2723131504725443954688224929386230600226083329284843121

noncomputable def ep1407 := nat_lit 800007502915718296558868815282222185582925185024000000

noncomputable def ep1408 := nat_lit 4638583069925120498602219237665279950546301708175409297393983

noncomputable def ep1409 := nat_lit 8024820561894847843298831832350161668588965827489

noncomputable def ep1410 := nat_lit 50000468932232393534929300955138886598932824064000000

noncomputable def ep1411 := nat_lit 1972529879564900068447024058824099145945302884334099832057

noncomputable def ep1412 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 33)) (Complex.re (zetaApproximant qz5 1 33))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 33)) (Complex.im (zetaApproximant qz5 1 33))) ep1406 ep1407 ep1408 ep1404 ep1409 ep1410 ep1411

noncomputable def ep1413 := nat_lit 10292643770143085382330608402818882221610380505306575667200000

noncomputable def ep1414 := nat_lit 136164272117066878011381215177115437974844615591840906903285447149332275666581098373182988770323988480000000

noncomputable def ep1415 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz5 1 33)) (Complex.re (zetaApproximant qz5 1 33)) ep541 ep542 ep543 ep544 ep541 ep542 ep543 ep544 ep1406

noncomputable def ep1416 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (zetaApproximant qz5 1 33)) (Complex.im (zetaApproximant qz5 1 33)) ep666 ep667 ep668 ep669 ep666 ep667 ep668 ep669 ep1409

noncomputable def ep1417 := @ep1387 4035225266123964416 ep1388 59612674475281691125 108951082185347039232 10199306335811099 108951082185347039232 (@ep1389 173498575 1855425871872 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) qz498) Bool.false 26561 1769472 1 1769472 (BSN.theta_err_eq 1 2 96 162 EMRow43.d18 EMRow43.d19 rfl) (ep1398 rfl)) (ep1399 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz5 1 33)) (@ep1400 1934617 1048576 6459 1048576 (@ep1405 524288 (@ep1412 ep1413 ep1414 ep1401 ep1402 ep1403 ep1404 (@ep1415 ep1407 ep1408 ep1404 ep754 ep754 rfl) (@ep1416 ep1410 ep1411 ep1413 ep760 ep760 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz225 := (@Norm.norm Complex Complex.instNorm qz496)

noncomputable abbrev qz648 := (Enclosure.sfrac Bool.false 2 7)

noncomputable def ep1418 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz225 qz648) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) Bool.false 2096122698368309039 4035225266123964416 423170228737 4035225266123964416 (BSN.zrb_shape_eq qz225 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) qz12 3)

noncomputable def ep1419 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz225 qz648) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) 134471243 3670016 1 3670016 15587888173 1099511627776 3031 1099511627776

noncomputable def ep1420 := @Enclosure.Real.IsNear.mulLit_ff qz225 qz648 134471243 1048576 1 1048576 2 7 0 1 134471243 3670016

noncomputable abbrev qz501 := (Complex.re qz646)

noncomputable abbrev qz502 := (Complex.im qz646)

noncomputable abbrev qz226 := (@HAdd.hAdd Real Real Real qz424 (@HMul.hMul Real Real Real qz267 qz501 qz501) (@HMul.hMul Real Real Real qz267 qz502 qz502))

noncomputable abbrev qz227 := qz496

noncomputable def ep1421 := @Enclosure.Real.IsNear.of_eq qz225 (Real.sqrt qz226) Bool.false 134471243 1048576 1 1048576 (BSN.norm_eq_sqrt_mul_add qz227)

noncomputable def ep1422 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz226) Bool.false 134471243 1048576 1 1048576 134471243

noncomputable def ep1423 := @Enclosure.Real.IsNear.sqrt_image qz226 4111487909 250000 0 1 67235621 67235622 524288

noncomputable abbrev qz228 := (@HMul.hMul Real Real Real qz267 qz501 qz501)

noncomputable abbrev qz229 := (@HMul.hMul Real Real Real qz267 qz502 qz502)

noncomputable def ep1424 := @Enclosure.Real.IsNear.addLit_ff qz228 qz229 49 4 0 1 4108425409 250000 0 1

noncomputable abbrev qz230 := qz501

noncomputable def ep1425 := @Enclosure.Real.IsNear.mulLit_ff qz230 qz230 7 2 0 1 7 2 0 1 49 4

noncomputable abbrev qz503 := (Enclosure.sfrac Bool.false 7 2)

noncomputable def ep1426 := @Enclosure.Complex.IsNear.of_eq qz227 (Complex.mk qz503 qz12) Bool.false 7 2 0 1 Bool.false 128194 1000 0 1 (BSN.s_add_nat_mk qz12 Bool.false 128194 1000 3 qz13)

noncomputable abbrev qz504 := (ep1426 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz12 Bool.false 7 2 0 1 Bool.false 128194 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz18))

noncomputable def ep1427 := @ep1425 0 1 (@Enclosure.Complex.IsNear.re_isNear qz227 Bool.false 7 2 0 1 Bool.false 128194 1000 0 1 qz504)

noncomputable def ep1428 := ep1427 (@Enclosure.Complex.IsNear.re_isNear qz227 Bool.false 7 2 0 1 Bool.false 128194 1000 0 1 qz504)

noncomputable abbrev qz231 := qz502

noncomputable def ep1429 := @Enclosure.Real.IsNear.mulLit_ff qz231 qz231 128194 1000 0 1 128194 1000 0 1 4108425409 250000

noncomputable def ep1430 := @ep1429 0 1 (@Enclosure.Complex.IsNear.im_isNear qz227 Bool.false 7 2 0 1 Bool.false 128194 1000 0 1 qz504)

noncomputable def ep1431 := ep1430 (@Enclosure.Complex.IsNear.im_isNear qz227 Bool.false 7 2 0 1 Bool.false 128194 1000 0 1 qz504)

noncomputable def ep1432 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Real.sqrt (@HAdd.hAdd Real Real Real qz424 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))))) Bool.false 15587888173 1099511627776

noncomputable def ep1433 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz424 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))))) Bool.false 15587888173 1099511627776

noncomputable def ep1434 := nat_lit 52874554504389467694159646619095545505317152861365809392143219949

noncomputable def ep1435 := nat_lit 263070294719562525276663269888930943538067857735680000000000000000000

noncomputable def ep1436 := nat_lit 602413689947381811043203968031039548823594956738936707490449219716733097342084851

noncomputable def ep1437 := nat_lit 7711364412714544111622473197632464287137668333303286742810455749353799680000000000000000000

noncomputable def ep1438 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz424 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)))) ep1434 ep1435 ep1436 ep1437

noncomputable def ep1439 := nat_lit 20297444086477803430522842994509888146528688069497696444701179289

noncomputable def ep1440 := nat_lit 146150163733090291820368483271628301965593254297600000000000000000000

noncomputable def ep1441 := nat_lit 2107746069075340207138804773025804979282032913723417707781940033468255039577241599

noncomputable def ep1442 := nat_lit 38556822063572720558112365988162321435688341666516433714052278746768998400000000000000000000

noncomputable def ep1443 := nat_lit 1276496495994486056188947596013886471997305807521090296225085721

noncomputable def ep1444 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) ep1439 ep1440 ep1441 ep1442 ep1443

noncomputable def ep1445 := nat_lit 20552366774965822287239317960072729963911551385600000000000000000000

noncomputable def ep1446 := nat_lit 14130037197837013251206485423896761950561591718301028588598532267428288236455979

noncomputable def ep1447 := nat_lit 602450344743323758720505718565036272432630338539319276782066855418265600000000000000000000

noncomputable def ep1448 := nat_lit 603720687353963086756212518209284151505915424288510768009095331942792822289553300607670345098591820991753617408000000000000000000000

noncomputable def ep1449 := nat_lit 142469098707326015815067314968517

noncomputable def ep1450 := nat_lit 12089258196146291747061760000000000

noncomputable def ep1451 := nat_lit 14401794520192828397160195646340050201

noncomputable def ep1452 := nat_lit 6209413987130566619691491858810142720000000000

noncomputable def ep1453 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) ep1449 ep1450 ep1451 ep1452 ep1449 ep1450 ep1451

noncomputable def ep1454 := nat_lit 35728091132811532507432938818939

noncomputable def ep1455 := nat_lit 4533471823554859405148160000000000

noncomputable def ep1456 := nat_lit 1154978093982658268317275084685925039

noncomputable def ep1457 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223) Bool.false ep1449 ep1450 ep1451 ep1452 Bool.true ep1454 ep1455 ep1456

noncomputable def ep1458 := nat_lit 776176748391320827461436482351267840000000000

noncomputable def ep1459 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223 Bool.false ep1449 ep1450 ep1451 ep1452 Bool.true ep1454 ep1455 ep1456 ep1458

noncomputable def ep1460 := nat_lit 6331907734611339069883486919

noncomputable def ep1461 := nat_lit 24178516392292583494123520000000

noncomputable def ep1462 := nat_lit 204714778894023889377967180888769

noncomputable def ep1463 := nat_lit 4139609324753711079794327905873428480000000

noncomputable def ep1464 := nat_lit 145635052574631685350009058428017

noncomputable def ep1465 := nat_lit 1281338395622890233008476806818808791

noncomputable abbrev qz232 := (Complex.re qz497)

noncomputable abbrev qz233 := (Complex.im qz497)

noncomputable def ep1466 := @Enclosure.Real.IsNear.subLit_tt_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz232) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz233) ep1460 ep1461 ep1462 ep1463 ep1464 ep1450 ep1465

noncomputable def ep1467 := nat_lit 564492180648233329062862896255467520000000000

noncomputable def ep1468 := nat_lit 3444691438490232190577074427726315810762828318603309219840000000

noncomputable def ep1469 := nat_lit 34496744372947592331619399215611904

noncomputable def ep1470 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz232 12324963727 120000000 0 1 1541239684318140891 604462909807314587353088 16609767251936017756847 ep1469 ep1460

noncomputable def ep1471 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) 12324963727 120000000 0 1 0 1 0 1 12324963727

noncomputable def ep1472 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 36974891181 500000 0 1 12324963727 120000000 0

noncomputable def ep1473 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (Complex.mk (Enclosure.sfrac Bool.true 1 720) qz10) Bool.true 1 720 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 2 1 30 24 Bool.true BSN.bern_real_2 EMRow43.d20 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 1 720) qz10 Bool.true 1 720 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.true 1 720) qz22)

noncomputable abbrev qz505 := (@HAdd.hAdd Complex Complex Complex qz529 qz528 qz538)

noncomputable abbrev qz234 := qz505

noncomputable def ep1474 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz80 (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) qz234) Bool.true 36974891181 500000 0 1 Bool.true 263245604003173 125000000 0 1

noncomputable abbrev qz235 := (Complex.re qz505)

noncomputable abbrev qz236 := (Complex.im qz505)

noncomputable def ep1475 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz235) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz236) 4108237909 100000 0 1 4108425409 125000 0 1

noncomputable def ep1476 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz235 4108237909 250000 0 1 5 2 0 1 4108237909 100000

noncomputable abbrev qz506 := (@HAdd.hAdd Complex Complex Complex qz529 qz528 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz237 := qz506

noncomputable def ep1477 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz80 (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz237) Bool.true 4108237909 250000 0 1 Bool.false 64097 250 0 1

noncomputable abbrev qz238 := (Complex.re qz506)

noncomputable abbrev qz239 := (Complex.im qz506)

noncomputable def ep1478 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz238) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz239) 3 4 0 1 4108425409 250000 0 1

noncomputable def ep1479 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz238 1 2 0 1 3 2 0 1 3 4

noncomputable def ep1480 := @ep1479 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 128194 1000 0 1 ep717)

noncomputable abbrev qz507 := (Enclosure.sfrac Bool.false 3 2)

noncomputable def ep1481 := @Enclosure.Complex.IsNear.of_eq qz237 (Complex.mk qz507 qz12) Bool.false 3 2 0 1 Bool.false 128194 1000 0 1 (BSN.s_add_nat_mk qz12 Bool.false 128194 1000 1 qz13)

noncomputable abbrev qz508 := (ep1481 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz12 Bool.false 3 2 0 1 Bool.false 128194 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz18))

noncomputable def ep1482 := ep1480 (@Enclosure.Complex.IsNear.re_isNear qz237 Bool.false 3 2 0 1 Bool.false 128194 1000 0 1 qz508)

noncomputable def ep1483 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz239 128194 1000 0 1 128194 1000 0 1 4108425409 250000

noncomputable def ep1484 := @ep1483 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 128194 1000 0 1 ep717)

noncomputable def ep1485 := ep1484 (@Enclosure.Complex.IsNear.im_isNear qz237 Bool.false 3 2 0 1 Bool.false 128194 1000 0 1 qz508)

noncomputable def ep1486 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz237 Bool.true 4108237909 250000 0 1 Bool.false 64097 250 0 1 (@ep1478 16432951636 4108237909 250000 0 1 (ep1482 rfl) (ep1485 rfl) rfl rfl)

noncomputable def ep1487 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz239) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz238) 64097 1000 0 1 192291 1000 0 1

noncomputable def ep1488 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz239 1 2 0 1 128194 1000 0 1 64097 1000

noncomputable def ep1489 := @ep1488 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 128194 1000 0 1 ep717)

noncomputable def ep1490 := ep1489 (@Enclosure.Complex.IsNear.im_isNear qz237 Bool.false 3 2 0 1 Bool.false 128194 1000 0 1 qz508)

noncomputable def ep1491 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz238 128194 1000 0 1 3 2 0 1 192291 1000

noncomputable def ep1492 := @ep1491 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 128194 1000 0 1 ep717)

noncomputable def ep1493 := ep1492 (@Enclosure.Complex.IsNear.re_isNear qz237 Bool.false 3 2 0 1 Bool.false 128194 1000 0 1 qz508)

noncomputable abbrev qz240 := (ep1477 (BSN.ascPochhammer_succ_eval_c 1 2 qz271 rfl) (ep1486 (@ep1487 256388000 64097 250 0 1 (ep1490 rfl) (ep1493 rfl) rfl rfl)))

noncomputable def ep1494 := @ep1476 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 4108237909 250000 0 1 Bool.false 64097 250 0 1 qz240)

noncomputable abbrev qz509 := (Enclosure.sfrac Bool.false 5 2)

noncomputable def ep1495 := @Enclosure.Complex.IsNear.of_eq qz234 (Complex.mk qz509 qz12) Bool.false 5 2 0 1 Bool.false 128194 1000 0 1 (BSN.s_add_nat_mk qz12 Bool.false 128194 1000 2 qz13)

noncomputable abbrev qz510 := (ep1495 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz12 Bool.false 5 2 0 1 Bool.false 128194 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz18))

noncomputable def ep1496 := ep1494 (@Enclosure.Complex.IsNear.re_isNear qz234 Bool.false 5 2 0 1 Bool.false 128194 1000 0 1 qz510)

noncomputable def ep1497 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz236 64097 250 0 1 128194 1000 0 1 4108425409 125000

noncomputable def ep1498 := @ep1497 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 4108237909 250000 0 1 Bool.false 64097 250 0 1 qz240)

noncomputable def ep1499 := ep1498 (@Enclosure.Complex.IsNear.im_isNear qz234 Bool.false 5 2 0 1 Bool.false 128194 1000 0 1 qz510)

noncomputable def ep1500 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) qz234 Bool.true 36974891181 500000 0 1 Bool.true 263245604003173 125000000 0 1 (@ep1475 924372279525000 36974891181 500000 0 1 (ep1496 rfl) (ep1499 rfl) rfl rfl)

noncomputable def ep1501 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz236) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz235) 263325725253173 125000000 0 1 64097 100 0 1

noncomputable def ep1502 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz236 4108237909 250000 0 1 128194 1000 0 1 263325725253173 125000000

noncomputable def ep1503 := @ep1502 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 4108237909 250000 0 1 Bool.false 64097 250 0 1 qz240)

noncomputable def ep1504 := ep1503 (@Enclosure.Complex.IsNear.im_isNear qz234 Bool.false 5 2 0 1 Bool.false 128194 1000 0 1 qz510)

noncomputable def ep1505 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz235 64097 250 0 1 5 2 0 1 64097 100

noncomputable def ep1506 := @ep1505 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 4108237909 250000 0 1 Bool.false 64097 250 0 1 qz240)

noncomputable def ep1507 := ep1506 (@Enclosure.Complex.IsNear.re_isNear qz234 Bool.false 5 2 0 1 Bool.false 128194 1000 0 1 qz510)

noncomputable abbrev qz241 := (ep1474 (BSN.ascPochhammer_succ_eval_c 2 3 qz271 rfl) (ep1500 (@ep1501 26324560400317300 263245604003173 125000000 0 1 (ep1504 rfl) (ep1507 rfl) rfl rfl)))

noncomputable def ep1508 := @ep1472 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1473) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 36974891181 500000 0 1 Bool.true 263245604003173 125000000 0 1 qz241)

noncomputable def ep1509 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 263245604003173 125000000 0 1 0 1 0

noncomputable def ep1510 := @ep1509 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1473) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 36974891181 500000 0 1 Bool.true 263245604003173 125000000 0 1 qz241)

noncomputable def ep1511 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) 263245604003173 90000000000 0 1 0 1 0 1 263245604003173

noncomputable def ep1512 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 263245604003173 125000000 0 1 263245604003173 90000000000 0

noncomputable def ep1513 := @ep1512 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1473) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 36974891181 500000 0 1 Bool.true 263245604003173 125000000 0 1 qz241)

noncomputable def ep1514 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 36974891181 500000 0 1 0 1 0

noncomputable def ep1515 := @ep1514 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1473) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 36974891181 500000 0 1 Bool.true 263245604003173 125000000 0 1 qz241)

noncomputable def ep1516 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 12324963727 120000000 0 1 Bool.false 263245604003173 90000000000 0 1 (@ep1471 12324963727 120000000 0 1 (ep1508 rfl) (ep1510 rfl) rfl rfl) (@ep1511 263245604003173 90000000000 0 1 (ep1513 rfl) (ep1515 rfl) rfl rfl)

noncomputable def ep1517 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 12324963727 120000000 0 1 Bool.false 263245604003173 90000000000 0 1 ep1516

noncomputable def ep1518 := nat_lit 1208925819614629174706176

noncomputable def ep1519 := nat_lit 68993488745895184663238798431223808

noncomputable def ep1520 := @Enclosure.Complex.IsNear.re_isNear qz223 Bool.true 1541239684318140891 604462909807314587353088 16609767251936017756847 ep1469 Bool.true 4979059301426688261 ep1518 53542099611592767494137 ep1519

noncomputable abbrev qz649 := (@Nat.cast Real Real.instNatCast 42618442977)

noncomputable abbrev qz242 := (@Inv.inv Real Real.instInv (Real.sqrt qz649))

noncomputable def ep1521 := @Enclosure.Complex.IsNear.of_eq qz223 (Complex.mk (@HMul.hMul Real Real Real qz0 qz242 (Real.cos qz135)) (@HMul.hMul Real Real Real qz0 qz242 qz606)) Bool.true 1541239684318140891 604462909807314587353088 16609767251936017756847 ep1469 Bool.true 4979059301426688261 ep1518 53542099611592767494137

noncomputable def ep1522 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz649) 226985761902963997 1099511627776 1 1099511627776 2662999 2663000 549755813888 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz649) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz649 qz14)) Bool.false 226985761902963997 1099511627776 1 1099511627776 (BSN.sqrt_natCast_div_one 42618442977) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz649 qz14)) Bool.false 226985761902963997 1099511627776 1 1099511627776 226985761902963997 1099511627776 1 1099511627776 (BSN.sqrt_enclosure 42618442977 1 113492880951481998 113492880951481999 549755813888 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep1523 := nat_lit 518818875300000000000000000

noncomputable def ep1524 := nat_lit 11414015256600000000000000

noncomputable def ep1525 := nat_lit 69255467328018160352285949952

noncomputable def ep1526 := nat_lit 228280305132000000000000000

noncomputable def ep1527 := BSN.log_dyadic_bound 1 65 3 2 267759375 549755813888 228280305132 21128 3 16916898254 66 64 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 1) (BSN.artanhQ 65) 0 2 21128 267759375 3 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1528 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz137 128194 1000 0 1 15746870150910163 4503599627370496 50057070076283 ep1524 1009327136062888717811 2251799813685248000 291682547334501041 ep1523 qz18 (BSN.isNear_log_sfrac 33 1 15746870150910163 4503599627370496 50057070076283 ep1524 Bool.false (@Enclosure.Real.IsNear.recentre' qz437 Bool.false ep1525 ep1392 1001141401525660 ep1526 15746870150910163 4503599627370496 50057070076283 ep1524 (BSN.log_rat_reduce_isNear 33 1 5 66 64 16916898254 549755813888 24973259072661432 36028797018963968 228280305132 1000000000000000 rfl rfl rfl rfl (ep1527 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1529 := nat_lit 87838235197768845106247368704

noncomputable def ep1530 := nat_lit 158456325028528675187087900672

noncomputable def ep1531 := nat_lit 188768561957330355754704169014596646764665236738317710055813288812271137692356519328300226804319568650929489632934652505292800

noncomputable def ep1532 := nat_lit 239883989954605411587671026978931954932931491354078368854013354829176373523832661173044660684363882565493899019640476261448417280

noncomputable def ep1533 := nat_lit 5894275189783908627426994884178510256326436818126697191607609783103596499833698182276722797003742468017898960688534061056

noncomputable def ep1534 := nat_lit 494384309633176995886447465617940642986089186750269416445962677425823192895172105586586431698213245169390920059368689411096576

noncomputable def ep1535 := nat_lit 4397873149167765879107302161280419173770410674824770095656911505201566847936932121505818779213337847034054815360075398126554316800

noncomputable def ep1536 := BSN.sin_dyadic_bound_f 1248256398835236 2251799813685248 3 2 1099511627776 457006470235 ep1531 ep1532 ep1533 ep1534 ep1535 ep1533 578760786218 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1248256398835236) (BSN.sinEvenQ 2251799813685248) 0 2 ep1531 ep1532 ep1533 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1248256398835236) (BSN.sinOddQ 2251799813685248) 0 2 ep1534 ep1535 ep1533 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz511 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 492835515655707) (@Nat.cast Real Real.instNatCast 1099511627776))

noncomputable def ep1537 := @Enclosure.Real.IsNear.cos_image qz135 qz511 Bool.false 492835515655707 1099511627776 619 1099511627776 Bool.true 578760786218 1099511627776 1 228280305132 (@Enclosure.Real.IsNear.recentre' qz135 Bool.false 1009327136062888717811 2251799813685248000 291682547334501041 ep1523 492835515655707 1099511627776 619 1099511627776 (ep1528 rfl) rfl) (Enclosure.sfrac_false_div 492835515655707 1099511627776) (BSN.cos_reduce1 qz511 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1529) (@Nat.cast Real Real.instNatCast ep1530)) 226375608064910080 72057594037927936 Bool.false 578760786218 1099511627776 71 1000000000000000 456560610264 228280305132 (BSN.sin_reduce_arg_pos_rat_q1 492835515655707 1099511627776 226375608064910080 72057594037927936 71 ep1529 ep1530 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 578760786218 1099511627776 ep1529 ep1530 1248256398835236 2251799813685248 457006470235 456560610264 (ep1536 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1538 := nat_lit 32033439112524362391192102282338759673214874186675920165548308788590427206850274646738837782477263613515611731871921695972561343349975868482019327439410085629368313589566279235273275448754176

noncomputable def ep1539 := nat_lit 8141310348160638307189460936952414606101722583687572942835547561875661626209408052340711079841550470472161889498856063384084353832402784384279780001957163779867465243525974033451143170464153600

noncomputable def ep1540 := nat_lit 14310196992760524774755686270441784648880943044488894593369614485084681591817803994080614791103972216759386469821403011461081486658968185787386389140393026842971435166788160162103296

noncomputable def ep1541 := nat_lit 194328915643335114185135783307535407115385721414479692283475700332172023442371957950473504324368811507606980559457937181700224482624106364231542980532620332024997149127459737221750152191016960

noncomputable def ep1542 := nat_lit 740859241682618085954240945262669729155256755115569137798034828130685207985056132763004708265581092812966731944395901767951676198748653378969459980178101903967939337160863637044054028512237977600

noncomputable def ep1543 := BSN.cos_dyadic_bound_f 1248256398835236 2251799813685248 4 3 1099511627776 457006470235 ep1538 ep1539 ep1540 ep1541 ep1542 ep1540 934859225739 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 1248256398835236) (BSN.cosEvenQ 2251799813685248) 0 3 ep1538 ep1539 ep1540 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 1248256398835236) (BSN.cosOddQ 2251799813685248) 0 3 ep1541 ep1542 ep1540 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1544 := @Enclosure.Real.IsNear.sin_image qz135 qz511 Bool.false 492835515655707 1099511627776 619 1099511627776 Bool.false 934859225739 1099511627776 1 228280305132 (@Enclosure.Real.IsNear.recentre' qz135 Bool.false 1009327136062888717811 2251799813685248000 291682547334501041 ep1523 492835515655707 1099511627776 619 1099511627776 (ep1528 rfl) rfl) (Enclosure.sfrac_false_div 492835515655707 1099511627776) (BSN.sin_reduce1 qz511 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1529) (@Nat.cast Real Real.instNatCast ep1530)) 226375608064910080 72057594037927936 Bool.false 934859225739 1099511627776 71 1000000000000000 456560610264 228280305132 (BSN.sin_reduce_arg_pos_rat_q1 492835515655707 1099511627776 226375608064910080 72057594037927936 71 ep1529 ep1530 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 934859225739 1099511627776 ep1529 ep1530 1248256398835236 2251799813685248 457006470235 456560610264 (ep1543 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz512 := (@Enclosure.Real.IsNear.recentre' qz242 Bool.false 5325999 1099511627776 1 1099511627776 5325999 1099511627776 1 1099511627776 (ep1522 rfl rfl) rfl)

noncomputable def ep1545 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz242 (Real.cos qz135)) (@HMul.hMul Real Real Real qz0 qz242 qz606) Bool.true 1541239684318140891 604462909807314587353088 16609767251936017756847 ep1469 Bool.true 4979059301426688261 ep1518 53542099611592767494137 ep1519 (@Enclosure.Real.IsNear.mulLit_ft qz242 (Real.cos qz135) 5325999 1099511627776 1 1099511627776 289380393109 549755813888 35601255126121 62749212471221821636608 1541239684318140891 604462909807314587353088 16609767251936017756847 ep1469 qz512 (@Enclosure.Real.IsNear.recentre' (Real.cos qz135) Bool.true 578760786218 1099511627776 142405020504484 250996849884887286546432 289380393109 549755813888 35601255126121 62749212471221821636608 (ep1537 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz242 qz606 5325999 1099511627776 1 1099511627776 934859225739 1099511627776 35601255126121 62749212471221821636608 4979059301426688261 ep1518 53542099611592767494137 ep1519 qz512 (@Enclosure.Real.IsNear.neg qz136 Bool.false 934859225739 1099511627776 35601255126121 62749212471221821636608 (@Enclosure.Real.IsNear.recentre' qz136 Bool.false 934859225739 1099511627776 142405020504484 250996849884887286546432 934859225739 1099511627776 35601255126121 62749212471221821636608 (ep1544 rfl rfl) rfl)) rfl)

noncomputable def ep1546 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz233 263245604003173 90000000000 0 1 4979059301426688261 ep1518 53542099611592767494137 ep1519 ep1464

noncomputable def ep1547 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 12324963727 120000000 0 1 Bool.false 263245604003173 90000000000 0 1 ep1516

noncomputable def ep1548 := @Enclosure.Complex.IsNear.im_isNear qz223 Bool.true 1541239684318140891 604462909807314587353088 16609767251936017756847 ep1469 Bool.true 4979059301426688261 ep1518 53542099611592767494137 ep1519

noncomputable def ep1549 := nat_lit 20455575094888630722187236249

noncomputable def ep1550 := nat_lit 48357032784585166988247040000000

noncomputable def ep1551 := nat_lit 659904435580301648060783210168599

noncomputable def ep1552 := nat_lit 8279218649507422159588655811746856960000000

noncomputable def ep1553 := nat_lit 135241523870662893508911541682381

noncomputable def ep1554 := nat_lit 18133887294219437620592640000000000

noncomputable def ep1555 := nat_lit 397495292053456359567846057720952321

noncomputable def ep1556 := @Enclosure.Real.IsNear.addLit_tt (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz233) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz232) ep1549 ep1550 ep1551 ep1552 ep1553 ep1554 ep1555

noncomputable def ep1557 := nat_lit 282246090324116664531431448127733760000000000

noncomputable def ep1558 := nat_lit 6910817896960055500156877784925551378029916180766250762240000000

noncomputable def ep1559 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz233 12324963727 120000000 0 1 4979059301426688261 ep1518 53542099611592767494137 ep1519 ep1549

noncomputable def ep1560 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz232 263245604003173 90000000000 0 1 1541239684318140891 604462909807314587353088 16609767251936017756847 ep1469 ep1553

noncomputable abbrev qz513 := (@ep1521 ep1519 (BSN.cpow_neg_s_sub_mk qz12 128194 1000 33 3 42618442977 qz13 rfl EMRow43.d21) ep1545)

noncomputable def ep1561 := ep1459 (@ep1466 ep1467 ep1468 ep1449 ep1450 ep1451 ep1452 (@ep1470 ep1461 ep1462 ep1463 ep1517 (ep1520 qz513) rfl) (@ep1546 ep1450 ep1465 ep1467 ep1547 (ep1548 qz513) rfl) rfl rfl) (@ep1556 ep1557 ep1558 ep1454 ep1455 ep1456 ep1458 (@ep1559 ep1550 ep1551 ep1552 ep1517 (ep1548 qz513) rfl) (@ep1560 ep1554 ep1555 ep1557 ep1547 (ep1520 qz513) rfl) rfl rfl)

noncomputable def ep1562 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) ep1454 ep1455 ep1456 ep1458 ep1454 ep1455 ep1456

noncomputable def ep1563 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223) Bool.false ep1449 ep1450 ep1451 ep1452 Bool.true ep1454 ep1455 ep1456

noncomputable def ep1564 := @ep1419 2096122698368309039 4035225266123964416 423170228737 4035225266123964416 (@ep1420 1 3670016 (ep1421 (@ep1422 1048576 1 1048576 (ep1423 (@ep1424 16445951636 4111487909 250000 0 1 (ep1428 rfl) (ep1431 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep1432 3031 1099511627776 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (@ep1433 3031 1099511627776 15587888173 1099511627776 3031 1099511627776 (@ep1438 7793942571 7793945602 549755813888 (@ep1444 ep1445 ep1446 ep1447 ep1448 ep1434 ep1435 ep1436 ep1437 (@ep1453 ep1452 ep1439 ep1440 ep1441 ep1442 (@ep1457 ep1458 ep1561) (@ep1457 ep1458 ep1561) rfl) (@ep1562 ep1458 ep1443 ep1445 ep1446 ep1447 (@ep1563 ep1458 ep1561) (@ep1563 ep1458 ep1561) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow43.d22 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz424 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 33))) (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)))) Bool.false 59612674475281691125 108951082185347039232 10199306335811099 108951082185347039232 := ep1417 (ep1418 ep1564) rfl rfl

noncomputable abbrev qz650 := (@HAdd.hAdd Complex Complex Complex qz652 qz658 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz514 := qz650

noncomputable abbrev qz243 := (@HDiv.hDiv Real Real Real qz270 (@Norm.norm Complex Complex.instNorm qz514) (@HAdd.hAdd Real Real Real qz424 (Complex.re qz441) qz291))

noncomputable abbrev qz515 := (@HPow.hPow Complex Complex Complex qz530 qz604 (@HSub.hSub Complex Complex Complex qz593 qz609 qz537))

noncomputable abbrev qz244 := qz515

noncomputable def ep1565 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz146 1 33))) (@HMul.hMul Real Real Real qz0 qz243 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) 13909119187 927712935936 89320433 927712935936 279416123638677225 504403158265495552 109377885483

noncomputable def ep1566 := nat_lit 266233756055307621470593613824

noncomputable def ep1567 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz146 1 33)) 26561 1769472 1 1769472 523667 524288 3343 524288 13909119187 927712935936

noncomputable def ep1568 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz146 1 33)) (Real.sqrt (@HAdd.hAdd Real Real Real qz424 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz146 1 33)) (Complex.re (zetaApproximant qz146 1 33))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz146 1 33)) (Complex.im (zetaApproximant qz146 1 33))))) Bool.false 523667 524288 3343 524288

noncomputable def ep1569 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz424 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz146 1 33)) (Complex.re (zetaApproximant qz146 1 33))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz146 1 33)) (Complex.im (zetaApproximant qz146 1 33))))) Bool.false 1047334 1048576 6686 1048576

noncomputable def ep1570 := nat_lit 50154191837181139969111560117282081694349

noncomputable def ep1571 := nat_lit 50271125665593666332194373305783812096000

noncomputable def ep1572 := nat_lit 196564519344325430883489246413439044929828077956566035583291

noncomputable def ep1573 := nat_lit 15435566974042840170269472453178851923286619007276285952000000

noncomputable def ep1574 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz424 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz146 1 33)) (Complex.re (zetaApproximant qz146 1 33))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz146 1 33)) (Complex.im (zetaApproximant qz146 1 33)))) ep1570 ep1571 ep1572 ep1573 520324 527010

noncomputable def ep1575 := nat_lit 13292321073514765054821542803709752841022041550736849

noncomputable def ep1576 := nat_lit 13330523199937209168679541634527696198068862976000000

noncomputable def ep1577 := nat_lit 15322305953350821695920947387988755517712672812516057333747

noncomputable def ep1578 := nat_lit 1234845357923427213621557796254308153862929520582102876160000

noncomputable def ep1579 := nat_lit 7194483528592648163655448684847267882304124988401

noncomputable def ep1580 := nat_lit 10071389854880319368954808127159201916839335600230637822907

noncomputable def ep1581 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz146 1 33)) (Complex.re (zetaApproximant qz146 1 33))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz146 1 33)) (Complex.im (zetaApproximant qz146 1 33))) ep1575 ep1576 ep1577 ep1578 ep1579 ep1576 ep1580

noncomputable def ep1582 := nat_lit 30871133948085680340538944906357703846573238014552571904000000

noncomputable def ep1583 := nat_lit 177289500681092315627556773209961390122461628177811504188712006068084270968645532660162671673344000000000

noncomputable def ep1584 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz146 1 33)) (Complex.re (zetaApproximant qz146 1 33)) ep1186 ep1187 ep1188 ep1189 ep1186 ep1187 ep1188 ep1189 ep1575

noncomputable def ep1585 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (zetaApproximant qz146 1 33)) (Complex.im (zetaApproximant qz146 1 33)) ep1295 ep1187 ep1296 ep1189 ep1295 ep1187 ep1296 ep1189 ep1579

noncomputable def ep1586 := @ep1565 1008806316530991104 ep1566 7748422098093073043 13618885273168379904 2625412548803465 27237770546336759808 (@ep1567 89320433 927712935936 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) qz498) Bool.false 26561 1769472 1 1769472 (BSN.theta_err_eq 1 2 96 162 EMRow43.d18 EMRow43.d19 rfl) (ep1398 rfl)) (ep1568 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz146 1 33)) (@ep1569 523667 524288 3343 524288 (@ep1574 524288 (@ep1581 ep1582 ep1583 ep1570 ep1571 ep1572 ep1573 (@ep1584 ep1576 ep1577 ep1578 ep1380 ep1380 rfl) (@ep1585 ep1576 ep1580 ep1582 ep1386 ep1386 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz245 := (@Norm.norm Complex Complex.instNorm qz514)

noncomputable def ep1587 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz243 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz245 qz648) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) Bool.false 279416123638677225 504403158265495552 109377885483 1008806316530991104 (BSN.zrb_shape_eq qz245 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) qz149 3)

noncomputable def ep1588 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz245 qz648) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) 136649385 3670016 1 3670016 2044766785 137438953472 1541 549755813888

noncomputable def ep1589 := @Enclosure.Real.IsNear.mulLit_ff qz245 qz648 136649385 1048576 1 1048576 2 7 0 1 136649385 3670016

noncomputable abbrev qz516 := (Complex.re qz650)

noncomputable abbrev qz517 := (Complex.im qz650)

noncomputable abbrev qz246 := (@HAdd.hAdd Real Real Real qz424 (@HMul.hMul Real Real Real qz267 qz516 qz516) (@HMul.hMul Real Real Real qz267 qz517 qz517))

noncomputable abbrev qz247 := qz514

noncomputable def ep1590 := @Enclosure.Real.IsNear.of_eq qz245 (Real.sqrt qz246) Bool.false 136649385 1048576 1 1048576 (BSN.norm_eq_sqrt_mul_add qz247)

noncomputable def ep1591 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz246) Bool.false 136649385 1048576 1 1048576 136649385

noncomputable def ep1592 := @Enclosure.Real.IsNear.sqrt_image qz246 1061440249 62500 0 1 68324692 68324693 524288

noncomputable abbrev qz248 := (@HMul.hMul Real Real Real qz267 qz516 qz516)

noncomputable abbrev qz249 := (@HMul.hMul Real Real Real qz267 qz517 qz517)

noncomputable def ep1593 := @Enclosure.Real.IsNear.addLit_ff qz248 qz249 49 4 0 1 265168656 15625 0 1

noncomputable abbrev qz250 := qz516

noncomputable def ep1594 := @Enclosure.Real.IsNear.mulLit_ff qz250 qz250 7 2 0 1 7 2 0 1 49 4

noncomputable def ep1595 := @Enclosure.Complex.IsNear.of_eq qz247 (Complex.mk qz503 qz149) Bool.false 7 2 0 1 Bool.false 130272 1000 0 1 (BSN.s_add_nat_mk qz149 Bool.false 130272 1000 3 qz150)

noncomputable abbrev qz518 := (ep1595 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz149 Bool.false 7 2 0 1 Bool.false 130272 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz151))

noncomputable def ep1596 := @ep1594 0 1 (@Enclosure.Complex.IsNear.re_isNear qz247 Bool.false 7 2 0 1 Bool.false 130272 1000 0 1 qz518)

noncomputable def ep1597 := ep1596 (@Enclosure.Complex.IsNear.re_isNear qz247 Bool.false 7 2 0 1 Bool.false 130272 1000 0 1 qz518)

noncomputable abbrev qz251 := qz517

noncomputable def ep1598 := @Enclosure.Real.IsNear.mulLit_ff qz251 qz251 130272 1000 0 1 130272 1000 0 1 265168656 15625

noncomputable def ep1599 := @ep1598 0 1 (@Enclosure.Complex.IsNear.im_isNear qz247 Bool.false 7 2 0 1 Bool.false 130272 1000 0 1 qz518)

noncomputable def ep1600 := ep1599 (@Enclosure.Complex.IsNear.im_isNear qz247 Bool.false 7 2 0 1 Bool.false 130272 1000 0 1 qz518)

noncomputable def ep1601 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Real.sqrt (@HAdd.hAdd Real Real Real qz424 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))))) Bool.false 2044766785 137438953472

noncomputable def ep1602 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz424 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))))) Bool.false 16358134280 1099511627776

noncomputable def ep1603 := nat_lit 25273024666232406324787666562272356117822583650270594947357193

noncomputable def ep1604 := nat_lit 114179815416476790484662877555959610910619729920000000000000000000

noncomputable def ep1605 := nat_lit 1395441497371373495487242193002079006377609283991198784604147175351225603587059

noncomputable def ep1606 := nat_lit 16734731798425659964458492182362118678684176070536646577279634872729600000000000000000000

noncomputable def ep1607 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz424 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)))) ep1603 ep1604 ep1605 ep1606

noncomputable def ep1608 := nat_lit 12879340430988794702537328010283480019070025087202507489

noncomputable def ep1609 := nat_lit 142724769270595988105828596944949513638274662400000000000000000000

noncomputable def ep1610 := nat_lit 15889539628854109965875675952452884572551260319444539522973167258981231567

noncomputable def ep1611 := nat_lit 4183682949606414991114623045590529669671044017634161644319908718182400000000000000000000

noncomputable def ep1612 := nat_lit 126365071813800307668759522662049739455192841971252625926756009

noncomputable def ep1613 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) ep1608 ep1609 ep1610 ep1611 ep1612

noncomputable def ep1614 := nat_lit 570899077082383952423314387779798054553098649600000000000000000000

noncomputable def ep1615 := nat_lit 1395377939212858079047378690298269194839319078949921006446055282682189678660791

noncomputable def ep1616 := nat_lit 18035433071290506875007978261025951016064233508760555368960174784796072153929674309443459105342835671433216000000000000000000000

noncomputable def ep1617 := nat_lit 3588779796948928810459239183

noncomputable def ep1618 := nat_lit 377789318629571617095680000000000

noncomputable def ep1619 := nat_lit 12930050768244585713202629383804117

noncomputable def ep1620 := nat_lit 64681395699276735621786373529272320000000000

noncomputable def ep1621 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) ep1617 ep1618 ep1619 ep1620 ep1617 ep1618 ep1619

noncomputable def ep1622 := nat_lit 11241221989347968910999789717747

noncomputable def ep1623 := nat_lit 755578637259143234191360000000000

noncomputable def ep1624 := nat_lit 362508825292143831552287294549385797

noncomputable def ep1625 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244) Bool.true ep1617 ep1618 ep1619 ep1620 Bool.true ep1622 ep1623 ep1624

noncomputable def ep1626 := nat_lit 129362791398553471243572747058544640000000000

noncomputable def ep1627 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244 Bool.true ep1617 ep1618 ep1619 ep1620 Bool.true ep1622 ep1623 ep1624 ep1626

noncomputable def ep1628 := nat_lit 1551896703585398769576198543

noncomputable def ep1629 := nat_lit 3022314549036572936765440000000

noncomputable def ep1630 := nat_lit 50040717123987513955711068456493

noncomputable def ep1631 := nat_lit 517451165594213884974290988234178560000000

noncomputable def ep1632 := nat_lit 47599577037806479346641394673

noncomputable def ep1633 := nat_lit 94447329657392904273920000000000

noncomputable def ep1634 := nat_lit 1668740281936536617184686456685623

noncomputable abbrev qz252 := (Complex.re qz515)

noncomputable abbrev qz253 := (Complex.im qz515)

noncomputable def ep1635 := @Enclosure.Real.IsNear.subLit_tt_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3)))) qz252) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253) ep1628 ep1629 ep1630 ep1631 ep1632 ep1633 ep1634

noncomputable def ep1636 := nat_lit 16170348924819183905446593382318080000000000

noncomputable def ep1637 := nat_lit 2711605348401816392598780932670460855231617832058880000000

noncomputable def ep1638 := nat_lit 17248372186473796165809699607805952

noncomputable def ep1639 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3)))) qz252 3181945747 30000000 0 1 1463158231137558207 302231454903657293676544 15726452021115341145919 ep1638 ep1628

noncomputable def ep1640 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3)))) 3181945747 30000000 0 1 0 1 0 1 3181945747

noncomputable def ep1641 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 9545837241 125000 0 1 3181945747 30000000 0

noncomputable abbrev qz519 := (@HAdd.hAdd Complex Complex Complex qz529 qz608 qz538)

noncomputable abbrev qz254 := qz519

noncomputable def ep1642 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz80 (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 2)) qz254) Bool.true 9545837241 125000 0 1 Bool.true 4316543378679 1953125 0 1

noncomputable abbrev qz255 := (Complex.re qz519)

noncomputable abbrev qz256 := (Complex.im qz519)

noncomputable def ep1643 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 2))) qz255) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 2))) qz256) 1060627749 25000 0 1 530337312 15625 0 1

noncomputable def ep1644 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 2))) qz255 1060627749 62500 0 1 5 2 0 1 1060627749 25000

noncomputable abbrev qz520 := (@HAdd.hAdd Complex Complex Complex qz529 qz608 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz257 := qz520

noncomputable def ep1645 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz80 (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)) qz257) Bool.true 1060627749 62500 0 1 Bool.false 32568 125 0 1

noncomputable abbrev qz258 := (Complex.re qz520)

noncomputable abbrev qz259 := (Complex.im qz520)

noncomputable def ep1646 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1))) qz258) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1))) qz259) 3 4 0 1 265168656 15625 0 1

noncomputable def ep1647 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1))) qz258 1 2 0 1 3 2 0 1 3 4

noncomputable def ep1648 := @ep1647 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 130272 1000 0 1 ep1345)

noncomputable def ep1649 := @Enclosure.Complex.IsNear.of_eq qz257 (Complex.mk qz507 qz149) Bool.false 3 2 0 1 Bool.false 130272 1000 0 1 (BSN.s_add_nat_mk qz149 Bool.false 130272 1000 1 qz150)

noncomputable abbrev qz521 := (ep1649 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz149 Bool.false 3 2 0 1 Bool.false 130272 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz151))

noncomputable def ep1650 := ep1648 (@Enclosure.Complex.IsNear.re_isNear qz257 Bool.false 3 2 0 1 Bool.false 130272 1000 0 1 qz521)

noncomputable def ep1651 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1))) qz259 130272 1000 0 1 130272 1000 0 1 265168656 15625

noncomputable def ep1652 := @ep1651 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 130272 1000 0 1 ep1345)

noncomputable def ep1653 := ep1652 (@Enclosure.Complex.IsNear.im_isNear qz257 Bool.false 3 2 0 1 Bool.false 130272 1000 0 1 qz521)

noncomputable def ep1654 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)) qz257 Bool.true 1060627749 62500 0 1 Bool.false 32568 125 0 1 (@ep1646 1060627749 1060627749 62500 0 1 (ep1650 rfl) (ep1653 rfl) rfl rfl)

noncomputable def ep1655 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1))) qz259) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1))) qz258) 8142 125 0 1 24426 125 0 1

noncomputable def ep1656 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1))) qz259 1 2 0 1 130272 1000 0 1 8142 125

noncomputable def ep1657 := @ep1656 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 130272 1000 0 1 ep1345)

noncomputable def ep1658 := ep1657 (@Enclosure.Complex.IsNear.im_isNear qz257 Bool.false 3 2 0 1 Bool.false 130272 1000 0 1 qz521)

noncomputable def ep1659 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1))) qz258 130272 1000 0 1 3 2 0 1 24426 125

noncomputable def ep1660 := @ep1659 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 130272 1000 0 1 ep1345)

noncomputable def ep1661 := ep1660 (@Enclosure.Complex.IsNear.re_isNear qz257 Bool.false 3 2 0 1 Bool.false 130272 1000 0 1 qz521)

noncomputable abbrev qz260 := (ep1645 (BSN.ascPochhammer_succ_eval_c 1 2 qz441 rfl) (ep1654 (@ep1655 4071000 32568 125 0 1 (ep1658 rfl) (ep1661 rfl) rfl rfl)))

noncomputable def ep1662 := @ep1644 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 1060627749 62500 0 1 Bool.false 32568 125 0 1 qz260)

noncomputable def ep1663 := @Enclosure.Complex.IsNear.of_eq qz254 (Complex.mk qz509 qz149) Bool.false 5 2 0 1 Bool.false 130272 1000 0 1 (BSN.s_add_nat_mk qz149 Bool.false 130272 1000 2 qz150)

noncomputable abbrev qz522 := (ep1663 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz149 Bool.false 5 2 0 1 Bool.false 130272 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz151))

noncomputable def ep1664 := ep1662 (@Enclosure.Complex.IsNear.re_isNear qz254 Bool.false 5 2 0 1 Bool.false 130272 1000 0 1 qz522)

noncomputable def ep1665 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 2))) qz256 32568 125 0 1 130272 1000 0 1 530337312 15625

noncomputable def ep1666 := @ep1665 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 1060627749 62500 0 1 Bool.false 32568 125 0 1 qz260)

noncomputable def ep1667 := ep1666 (@Enclosure.Complex.IsNear.im_isNear qz254 Bool.false 5 2 0 1 Bool.false 130272 1000 0 1 qz522)

noncomputable def ep1668 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 2)) qz254 Bool.true 9545837241 125000 0 1 Bool.true 4316543378679 1953125 0 1 (@ep1643 29830741378125 9545837241 125000 0 1 (ep1664 rfl) (ep1667 rfl) rfl rfl)

noncomputable def ep1669 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 2))) qz256) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 2))) qz255) 4317815566179 1953125 0 1 16284 25 0 1

noncomputable def ep1670 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 2))) qz256 1060627749 62500 0 1 130272 1000 0 1 4317815566179 1953125

noncomputable def ep1671 := @ep1670 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 1060627749 62500 0 1 Bool.false 32568 125 0 1 qz260)

noncomputable def ep1672 := ep1671 (@Enclosure.Complex.IsNear.im_isNear qz254 Bool.false 5 2 0 1 Bool.false 130272 1000 0 1 qz522)

noncomputable def ep1673 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 2))) qz255 32568 125 0 1 5 2 0 1 16284 25

noncomputable def ep1674 := @ep1673 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 1060627749 62500 0 1 Bool.false 32568 125 0 1 qz260)

noncomputable def ep1675 := ep1674 (@Enclosure.Complex.IsNear.re_isNear qz254 Bool.false 5 2 0 1 Bool.false 130272 1000 0 1 qz522)

noncomputable abbrev qz261 := (ep1642 (BSN.ascPochhammer_succ_eval_c 2 3 qz441 rfl) (ep1668 (@ep1669 107913584466975 4316543378679 1953125 0 1 (ep1672 rfl) (ep1675 rfl) rfl rfl)))

noncomputable def ep1676 := @ep1641 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1473) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 9545837241 125000 0 1 Bool.true 4316543378679 1953125 0 1 qz261)

noncomputable def ep1677 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 4316543378679 1953125 0 1 0 1 0

noncomputable def ep1678 := @ep1677 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1473) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 9545837241 125000 0 1 Bool.true 4316543378679 1953125 0 1 qz261)

noncomputable def ep1679 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3)))) 1438847792893 468750000 0 1 0 1 0 1 1438847792893

noncomputable def ep1680 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 4316543378679 1953125 0 1 1438847792893 468750000 0

noncomputable def ep1681 := @ep1680 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1473) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 9545837241 125000 0 1 Bool.true 4316543378679 1953125 0 1 qz261)

noncomputable def ep1682 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 9545837241 125000 0 1 0 1 0

noncomputable def ep1683 := @ep1682 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1473) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 9545837241 125000 0 1 Bool.true 4316543378679 1953125 0 1 qz261)

noncomputable def ep1684 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 3181945747 30000000 0 1 Bool.false 1438847792893 468750000 0 1 (@ep1640 3181945747 30000000 0 1 (ep1676 rfl) (ep1678 rfl) rfl rfl) (@ep1679 1438847792893 468750000 0 1 (ep1681 rfl) (ep1683 rfl) rfl rfl)

noncomputable def ep1685 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 3181945747 30000000 0 1 Bool.false 1438847792893 468750000 0 1 ep1684

noncomputable def ep1686 := @Enclosure.Complex.IsNear.re_isNear qz244 Bool.true 1463158231137558207 302231454903657293676544 15726452021115341145919 ep1638 Bool.true 99245195926042383 604462909807314587353088 1159775405139487596611 ep1469

noncomputable def ep1687 := @Enclosure.Complex.IsNear.of_eq qz244 (Complex.mk (@HMul.hMul Real Real Real qz0 qz242 (Real.cos qz217)) (@HMul.hMul Real Real Real qz0 qz242 qz644)) Bool.true 1463158231137558207 302231454903657293676544 15726452021115341145919 ep1638 Bool.true 99245195926042383 604462909807314587353088 1159775405139487596611

noncomputable def ep1688 := nat_lit 118895992256250000000000000

noncomputable def ep1689 := @Enclosure.Real.IsNear.mulLit_ff qz149 qz137 130272 1000 0 1 15746870150910163 4503599627370496 50057070076283 ep1524 64105508384355273573 140737488355328000 67927444093516031 ep1688 qz151 (BSN.isNear_log_sfrac 33 1 15746870150910163 4503599627370496 50057070076283 ep1524 Bool.false (@Enclosure.Real.IsNear.recentre' qz437 Bool.false ep1525 ep1392 1001141401525660 ep1526 15746870150910163 4503599627370496 50057070076283 ep1524 (BSN.log_rat_reduce_isNear 33 1 5 66 64 16916898254 549755813888 24973259072661432 36028797018963968 228280305132 1000000000000000 rfl rfl rfl rfl (ep1527 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1690 := nat_lit 243530670809790619915575623680

noncomputable def ep1691 := nat_lit 7240038326307631179018638304477333938429280593393601913693153859407293437526632686123795995201101790311842601963523478599103282956833474453493391911618751650418201533569131187553447242786307296909333698700090055414698316757518624578225836011149326286848000000

noncomputable def ep1692 := nat_lit 155433625461590811300248653684703508738906887282493828366197298645519518790118634907255632381243555533316827446940106385055636004350275585915152922536618788469110716965662258357051938969424840669115718701241640255984264744212126888020762883150876583925907456000

noncomputable def ep1693 := nat_lit 423430202173217892228079486230209860711313465080026788661143295392282609375659427926554669550389009024302109435469790843980946044483969489417801710220354858927452255167216532603340633995951144490282108690803322812238111733099319132160000000000000000

noncomputable def ep1694 := nat_lit 58887453308842257930338145444905283085479740602834837810985133143106674848215804442524400273715273114739565229172268065974324549323474115443392086540074350348914331799043975018251627372901805082684498390372575006377031235166184599552835570617436023554048000000

noncomputable def ep1695 := nat_lit 8859716651310676244114173260028099998117692575102148216873246022794612571036762189713571045730882665399059164475586063948171252247965708397163716584587270942739310867042748726351960521257215918139595965970773494591103090420091232617183484339599965283776724992000

noncomputable def ep1696 := BSN.sin_dyadic_bound_f 3460778981573620 2251799813685248 5 4 1099511627776 457006470235 ep1691 ep1692 ep1693 ep1694 ep1695 ep1693 1098879839172 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.sinEvenP 3460778981573620) (BSN.sinEvenQ 2251799813685248) 0 4 ep1691 ep1692 ep1693 rfl rfl rfl rfl) (@BSN.binarySplit_of_base4 (BSN.sinOddP 3460778981573620) (BSN.sinOddQ 2251799813685248) 0 4 ep1694 ep1695 ep1693 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz523 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 500824284252775) (@Nat.cast Real Real.instNatCast 1099511627776))

noncomputable def ep1697 := @Enclosure.Real.IsNear.cos_image qz217 qz523 Bool.false 500824284252775 1099511627776 629 1099511627776 Bool.true 1098879839172 1099511627776 1 228280305132 (@Enclosure.Real.IsNear.recentre' qz217 Bool.false 64105508384355273573 140737488355328000 67927444093516031 ep1688 500824284252775 1099511627776 629 1099511627776 (ep1689 rfl) rfl) (Enclosure.sfrac_false_div 500824284252775 1099511627776) (BSN.cos_reduce1 qz523 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1690) (@Nat.cast Real Real.instNatCast ep1530)) 226375608064910080 72057594037927936 Bool.false 1098879839172 1099511627776 72 1000000000000000 456560610264 228280305132 (BSN.sin_reduce_arg_pos_rat_q1 500824284252775 1099511627776 226375608064910080 72057594037927936 72 ep1690 ep1530 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1098879839172 1099511627776 ep1690 ep1530 3460778981573620 2251799813685248 457006470235 456560610264 (ep1696 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1698 := nat_lit 2132562302700225523226175182538506660350198380924033125294855310017683994421356896440666160234057090832975925188667086203899308370896001810973689283885584204575489074286323259228711863822853725646167399392220161380349240975229177407688549284061087006720000000

noncomputable def ep1699 := nat_lit 9143154438917106547073450216747265219935699251911401668599841096795265811183449112191507787131973854900989849820006257944449176726486799171479583678624634615830042174450721079826584645260284745242101100073037662116721455541889816942397816655933916701523968000

noncomputable def ep1700 := nat_lit 21704107697893498715433470367943150037000813113502658159783797642808705831341248624367593883312854449979637474729848300327634813437163472010366061111849610004613120091936931556759812648110728317349705491889916192546732463739181503444165593073809352556544000000

noncomputable def ep1701 := nat_lit 1398902629154317301702237883162331578650161985542444455295775687809675669111067714165300691431191999799851447022460957465500724039152480273236376302829569096221996452690960325213467450724823566022041468311174762303858382697909141992186865948357889255333167104000

noncomputable def ep1702 := BSN.cos_dyadic_bound_f 3460778981573620 2251799813685248 5 4 1099511627776 457006470235 ep1698 ep1699 ep1693 ep1700 ep1701 ep1693 37268199234 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.cosEvenP 3460778981573620) (BSN.cosEvenQ 2251799813685248) 0 4 ep1698 ep1699 ep1693 rfl rfl rfl rfl) (@BSN.binarySplit_of_base4 (BSN.cosOddP 3460778981573620) (BSN.cosOddQ 2251799813685248) 0 4 ep1700 ep1701 ep1693 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1703 := @Enclosure.Real.IsNear.sin_image qz217 qz523 Bool.false 500824284252775 1099511627776 629 1099511627776 Bool.false 37268199234 1099511627776 1 228280305132 (@Enclosure.Real.IsNear.recentre' qz217 Bool.false 64105508384355273573 140737488355328000 67927444093516031 ep1688 500824284252775 1099511627776 629 1099511627776 (ep1689 rfl) rfl) (Enclosure.sfrac_false_div 500824284252775 1099511627776) (BSN.sin_reduce1 qz523 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1690) (@Nat.cast Real Real.instNatCast ep1530)) 226375608064910080 72057594037927936 Bool.false 37268199234 1099511627776 72 1000000000000000 456560610264 228280305132 (BSN.sin_reduce_arg_pos_rat_q1 500824284252775 1099511627776 226375608064910080 72057594037927936 72 ep1690 ep1530 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 37268199234 1099511627776 ep1690 ep1530 3460778981573620 2251799813685248 457006470235 456560610264 (ep1702 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1704 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz242 (Real.cos qz217)) (@HMul.hMul Real Real Real qz0 qz242 qz644) Bool.true 1463158231137558207 302231454903657293676544 15726452021115341145919 ep1638 Bool.true 99245195926042383 604462909807314587353088 1159775405139487596611 ep1469 (@Enclosure.Real.IsNear.mulLit_ft qz242 (Real.cos qz217) 5325999 1099511627776 1 1099511627776 274719959793 274877906944 36171955888951 62749212471221821636608 1463158231137558207 302231454903657293676544 15726452021115341145919 ep1638 qz512 (@Enclosure.Real.IsNear.recentre' (Real.cos qz217) Bool.true 1098879839172 1099511627776 144687823555804 250996849884887286546432 274719959793 274877906944 36171955888951 62749212471221821636608 (ep1697 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz242 qz644 5325999 1099511627776 1 1099511627776 18634099617 549755813888 36171955888951 62749212471221821636608 99245195926042383 604462909807314587353088 1159775405139487596611 ep1469 qz512 (@Enclosure.Real.IsNear.neg qz218 Bool.false 18634099617 549755813888 36171955888951 62749212471221821636608 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 37268199234 1099511627776 144687823555804 250996849884887286546432 18634099617 549755813888 36171955888951 62749212471221821636608 (ep1703 rfl rfl) rfl)) rfl)

noncomputable def ep1705 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253 1438847792893 468750000 0 1 99245195926042383 604462909807314587353088 1159775405139487596611 ep1469 ep1632

noncomputable def ep1706 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 3181945747 30000000 0 1 Bool.false 1438847792893 468750000 0 1 ep1684

noncomputable def ep1707 := @Enclosure.Complex.IsNear.im_isNear qz244 Bool.true 1463158231137558207 302231454903657293676544 15726452021115341145919 ep1638 Bool.true 99245195926042383 604462909807314587353088 1159775405139487596611 ep1469

noncomputable def ep1708 := nat_lit 105264276362350762376198367

noncomputable def ep1709 := nat_lit 6044629098073145873530880000000

noncomputable def ep1710 := nat_lit 3690342417858794499795623063417

noncomputable def ep1711 := nat_lit 1034902331188427769948581976468357120000000

noncomputable def ep1712 := nat_lit 701753997175167191606422807617

noncomputable def ep1713 := nat_lit 47223664828696452136960000000000

noncomputable def ep1714 := nat_lit 22627970780619467639988302604153667

noncomputable def ep1715 := @Enclosure.Real.IsNear.addLit_tt (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3)))) qz252) ep1708 ep1709 ep1710 ep1711 ep1712 ep1713 ep1714

noncomputable def ep1716 := nat_lit 8085174462409591952723296691159040000000000

noncomputable def ep1717 := nat_lit 4246813595919526745537130938515731991212412267093032960000000

noncomputable def ep1718 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253 3181945747 30000000 0 1 99245195926042383 604462909807314587353088 1159775405139487596611 ep1469 ep1708

noncomputable def ep1719 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3)))) qz252 1438847792893 468750000 0 1 1463158231137558207 302231454903657293676544 15726452021115341145919 ep1638 ep1712

noncomputable abbrev qz524 := (@ep1687 ep1469 (BSN.cpow_neg_s_sub_mk qz149 130272 1000 33 3 42618442977 qz150 rfl EMRow43.d21) ep1704)

noncomputable def ep1720 := ep1627 (@ep1635 ep1636 ep1637 ep1617 ep1618 ep1619 ep1620 (@ep1639 ep1629 ep1630 ep1631 ep1685 (ep1686 qz524) rfl) (@ep1705 ep1633 ep1634 ep1636 ep1706 (ep1707 qz524) rfl) rfl rfl) (@ep1715 ep1716 ep1717 ep1622 ep1623 ep1624 ep1626 (@ep1718 ep1709 ep1710 ep1711 ep1685 (ep1707 qz524) rfl) (@ep1719 ep1713 ep1714 ep1716 ep1706 (ep1686 qz524) rfl) rfl rfl)

noncomputable def ep1721 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) ep1622 ep1623 ep1624 ep1626 ep1622 ep1623 ep1624

noncomputable def ep1722 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244) Bool.true ep1617 ep1618 ep1619 ep1620 Bool.true ep1622 ep1623 ep1624

noncomputable def ep1723 := @ep1588 279416123638677225 504403158265495552 109377885483 1008806316530991104 (@ep1589 1 3670016 (ep1590 (@ep1591 1048576 1 1048576 (ep1592 (@ep1593 1061440249 1061440249 62500 0 1 (ep1597 rfl) (ep1600 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep1601 1541 549755813888 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (@ep1602 3082 1099511627776 2044766785 137438953472 1541 549755813888 (@ep1607 8179065599 8179068681 549755813888 (@ep1613 ep1614 ep1615 ep1606 ep1616 ep1603 ep1604 ep1605 ep1606 (@ep1621 ep1620 ep1608 ep1609 ep1610 ep1611 (@ep1625 ep1626 ep1720) (@ep1625 ep1626 ep1720) rfl) (@ep1721 ep1626 ep1612 ep1614 ep1615 ep1606 (@ep1722 ep1626 ep1720) (@ep1722 ep1626 ep1720) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow43.d23 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz424 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz146 1 33))) (@HMul.hMul Real Real Real qz0 qz243 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)))) Bool.false 7748422098093073043 13618885273168379904 2625412548803465 27237770546336759808 := ep1586 (ep1587 ep1723) rfl rfl

noncomputable def EMRow43.d24 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J))

noncomputable abbrev qz525 := (EMRow43.d3 qz539 qz615 (@Enclosure.dec_le_dec qz539 qz615 128194 1000 130272 1000 (@Eq.refl Real qz539) (@Eq.refl Real qz615) rfl rfl rfl) 33 33 1 1)

noncomputable abbrev qz262 := qz525

noncomputable def ep1724 := @Zeta.Certificates.ZIntervalEM.Certificate.mk qz262 (@Enclosure.dec_nonneg qz12 128194 1000 qz13) (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 33 rfl)

noncomputable abbrev qz263 := (Zeta.Certificates.ZIntervalEM.fstVal qz525)

noncomputable def ep1725 := @Enclosure.Real.IsNear.neg_val qz263 ep525 ep526

noncomputable def ep1726 := @Enclosure.Real.IsNear.of_eq qz263 (hardyZApproximantEM 1 33 qz12) Bool.true

noncomputable abbrev qz264 := (Zeta.Certificates.ZIntervalEM.sndVal qz525)

noncomputable def ep1727 := BSN.mul_neg_of_neg_pos_r qz263 qz264 (@ep1725 ep527 ep528 (@ep1726 ep525 ep526 ep527 ep528 (@Eq.refl Real (hardyZApproximantEM 1 33 qz12)) EMRow43.d12) rfl rfl rfl)

noncomputable def ep1728 := @Enclosure.Real.IsNear.pos_val qz264 ep1170 ep1171

noncomputable def ep1729 := @Enclosure.Real.IsNear.of_eq qz264 (hardyZApproximantEM 1 33 qz149) Bool.false

noncomputable def ep1730 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz263) (BSN.hardyZErrorBoundStrong 1 33 qz12)

noncomputable def ep1731 := @Enclosure.norm_gt_of_isNear qz263 (BSN.hardyZErrorBoundStrong 1 33 qz12) Bool.true

noncomputable def ep1732 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 33 qz12) (@HAdd.hAdd Real Real Real qz424 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 33))) (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)))) Bool.false 59612674475281691125 108951082185347039232 10199306335811099 108951082185347039232 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz424 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 33))) (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)))))

noncomputable def ep1733 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz264) (BSN.hardyZErrorBoundStrong 1 33 qz149)

noncomputable def ep1734 := @Enclosure.norm_gt_of_isNear qz264 (BSN.hardyZErrorBoundStrong 1 33 qz149) Bool.false

noncomputable def ep1735 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 33 qz149) (@HAdd.hAdd Real Real Real qz424 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz146 1 33))) (@HMul.hMul Real Real Real qz0 qz243 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)))) Bool.false 7748422098093073043 13618885273168379904 2625412548803465 27237770546336759808 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz424 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz146 1 33))) (@HMul.hMul Real Real Real qz0 qz243 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)))))

noncomputable def ep1736 := @List.cons EMRow43.d0 (@PSigma.mk Zeta.Certificates.ZIntervalEM Zeta.Certificates.ZIntervalEM.Certificate qz262 (ep1724 (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 33 rfl) (ep1727 (@ep1728 ep1172 ep1173 (@ep1729 ep1170 ep1171 ep1172 ep1173 (@Eq.refl Real (hardyZApproximantEM 1 33 qz149)) EMRow43.d17) rfl rfl rfl)) (ep1730 (hardyZErrorBoundEM 1 33 qz12) (BSN.hardyZErrorBoundEM_le_strong 1 33 qz12 rfl) (@ep1731 Bool.false ep525 ep526 ep527 ep528 59612674475281691125 108951082185347039232 10199306335811099 108951082185347039232 (@ep1726 ep525 ep526 ep527 ep528 (@Eq.refl Real (hardyZApproximantEM 1 33 qz12)) EMRow43.d12) (ep1732 EMRow43.d22) rfl rfl rfl rfl rfl)) (ep1733 (hardyZErrorBoundEM 1 33 qz149) (BSN.hardyZErrorBoundEM_le_strong 1 33 qz149 rfl) (@ep1734 Bool.false ep1170 ep1171 ep1172 ep1173 7748422098093073043 13618885273168379904 2625412548803465 27237770546336759808 (@ep1729 ep1170 ep1171 ep1172 ep1173 (@Eq.refl Real (hardyZApproximantEM 1 33 qz149)) EMRow43.d17) (ep1735 EMRow43.d23) rfl rfl rfl rfl rfl)))) (@List.nil EMRow43.d0)

noncomputable abbrev qz526 := (@Enclosure.dec_le_dec qz539 qz615 128194 1000 130272 1000 (@Eq.refl Real qz539) (@Eq.refl Real qz615) rfl rfl rfl)

noncomputable abbrev qz265 := (Zeta.Certificates.CertifiedZeroIntervals.intervals (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1736 (@List.IsChain.singleton EMRow43.d1 EMRow43.d24 (EMRow43.d2 qz278 qz443 qz526))))

noncomputable abbrev qz527 := (@NonemptyInterval Real Real.instLE)

noncomputable def ep1737 := And (@Eq (Option Real) (@Option.map qz527 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz527 qz265)) (@Option.some Real qz12))

noncomputable def ep1738 := ep1737 (@Eq (Option Real) (@Option.map qz527 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz527 qz265)) (@Option.some Real qz149))

noncomputable def ep1739 := @And.intro (@Eq Nat (@List.length qz527 qz265) 1) ep1738

noncomputable def ep1740 := @And.intro (@Eq (Option Real) (@Option.map qz527 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz527 qz265)) (@Option.some Real qz12))

noncomputable def ep1741 := @ep1740 (@Eq (Option Real) (@Option.map qz527 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz527 qz265)) (@Option.some Real qz149))

noncomputable abbrev qz266 := (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1736 (@List.IsChain.singleton EMRow43.d1 EMRow43.d24 (EMRow43.d2 qz278 qz443 qz526)))

theorem EMRow43.d25 : Zeta.Certificates.BatchSpec 1 128194 1000 130272 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz527 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 1) (And (@Eq (Option Real) (@Option.map qz527 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz527 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz12)) (@Eq (Option Real) (@Option.map qz527 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz527 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz149)))) qz266 (ep1739 (@Eq.refl Nat 1) (ep1741 (@Eq.refl (Option Real) (@Option.some Real qz12)) (@Eq.refl (Option Real) (@Option.some Real qz149))))

theorem solution : Zeta.Certificates.BatchSpec 1 128194 1000 130272 1000 := EMRow43.d25
#print axioms solution
#check solution
