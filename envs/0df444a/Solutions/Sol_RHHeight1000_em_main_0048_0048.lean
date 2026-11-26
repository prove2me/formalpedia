-- Prove2me | solution 1 for RHHeight1000.em_main_0048_0048
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T07:45:37.43273+00:00
-- url     : https://prove2.me/submissions/b125b6ff-84b8-4bd1-b353-616ded37e9f3

import Definitions.Def_RHT1000_Support_20261118_S005
/- Copyright (c) 2026 Salvatore Mercuri, Bhavik Mehta.
Apache 2.0 license; see the source project LICENSE. -/
set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def EMRow48.d0 := @PSigma Zeta.Certificates.ZIntervalEM fun (I : Zeta.Certificates.ZIntervalEM) => Zeta.Certificates.ZIntervalEM.Certificate I

noncomputable def EMRow48.d1 := @NonemptyInterval Real Real.instLE

noncomputable def EMRow48.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h

noncomputable def EMRow48.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) (fc sc fb sb : Nat) => Zeta.Certificates.ZIntervalEM.mk (EMRow48.d2 a b h) fc sc fb sb

noncomputable def ep0 := nat_lit 26986075409044028275299783

noncomputable def ep1 := nat_lit 4294967296000000000000000

noncomputable def ep2 := nat_lit 26986075409044045455168967

noncomputable abbrev qz269 := (@instHMul Real Real.instMul)

noncomputable abbrev qz0 := qz269

noncomputable abbrev qz270 := (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 2 1) Real.pi)

noncomputable def ep3 := @BSN.isNear_log_image_fff qz270 884279719003555 140737488355328 1 500000000000000 ep0 ep1 ep2 ep1 4138529546116343 2251799813685248 50000000039467 19733500000000000000 4138529546116343 2251799813685248 50000000039467 19733500000000000000 963576 524288

noncomputable abbrev qz271 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 2 1) Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) BSN.pi_near_15 rfl)

noncomputable def ep4 := @ep3 2 524288 qz271 rfl rfl rfl rfl

noncomputable def ep5 := nat_lit 53972150818088056550599566

noncomputable def ep6 := nat_lit 34359738368000000000000000

noncomputable def ep7 := nat_lit 9806206225044028275299783

noncomputable def ep8 := nat_lit 44165944593044028275299783

noncomputable def ep9 := nat_lit 13681445815609410487519367394620474863599256634174726093703677122907123617368241606644861540940610176751640793056574796245399519365549113997355475306157239709119582688278313060810592403844863400465080549957745

noncomputable def ep10 := nat_lit 231714499556395493334623298703961145503103241611736774613091488581016477543539392410113701224645713379230392133956226737605624599560350113120270717249177907454870984269546186598262646369758174842349131395304

noncomputable def ep11 := nat_lit 8978369550011295664474073352761810093897501552430546263638635096022803738134167562509900960712119243631997923545019968443113540909076206607473711060286601587364321108377403290080403445693385008949995305

noncomputable def ep12 := BSN.log_dyadic_bound ep7 ep8 5 4 ep9 1048576 394670 ep10 ep11 473518 ep5 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep7) (BSN.artanhQ ep8) 0 4 ep10 ep9 ep11 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz272 := (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))

noncomputable abbrev qz1 := qz272

noncomputable def ep13 := ep4 rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep1 4138529546116343 2251799813685248 50000000039467 19733500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep0) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 69433004117575847641088 37778931862957161709568 1000000000789340 394670000000000000000 4138529546116343 2251799813685248 50000000039467 19733500000000000000 (BSN.log_rat_reduce_isNear ep0 ep1 2 ep5 ep6 473518 1048576 24973259072661432 36028797018963968 394670 1000000000000000 rfl rfl rfl rfl (ep12 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep14 := nat_lit 53972150818088090910337934

noncomputable def ep15 := nat_lit 9806206225044045455168967

noncomputable def ep16 := nat_lit 44165944593044045455168967

noncomputable def ep17 := nat_lit 13681445815609453062485491347592146866046743284321690683909457683007658987562290830600045658905080811372395010565947827677605470036294121079488508864180301737865471494204890974265645509835068840465080549957745

noncomputable def ep18 := nat_lit 231714499556396865510889920206523150079811393376960301632499817942333196803513131357563499488546302200815366867712007119763002650772307103678175657719139104636874731038771518520299266622696414842349131395304

noncomputable def ep19 := nat_lit 8978369550011421500876706511871067098718760264493934208903156435737864998391937547068187824077011975074541700434630537294838404525415248443919841847024664017658842168336182958576672102333385008949995305

noncomputable def ep20 := BSN.log_dyadic_bound ep15 ep16 5 4 ep17 1048576 394670 ep18 ep19 473518 ep14 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep15) (BSN.artanhQ ep16) 0 4 ep18 ep17 ep19 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep21 := ep13 (BSN.isNear_log_sfrac ep2 ep1 4138529546116343 2251799813685248 50000000039467 19733500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep2) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 69433004117575847641088 37778931862957161709568 1000000000789340 394670000000000000000 4138529546116343 2251799813685248 50000000039467 19733500000000000000 (BSN.log_rat_reduce_isNear ep2 ep1 2 ep14 ep6 473518 1048576 24973259072661432 36028797018963968 394670 1000000000000000 rfl rfl rfl rfl (ep20 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable abbrev qz2 := (Real.log (@HMul.hMul Real Real Real qz269 (2 : Real) Real.pi))

theorem EMRow48.d4 : Enclosure.Real.IsNear qz2 Bool.false 120447 65536 1 262144 := @Enclosure.Real.IsNear.of_eq qz2 (Real.log qz270) Bool.false 120447 65536 1 262144 BSN.log_two_pi_eq (@Enclosure.Real.IsNear.recentre' (Real.log qz270) Bool.false 963576 524288 2 524288 120447 65536 1 262144 (ep21 rfl rfl rfl rfl rfl rfl rfl rfl) rfl)

noncomputable def ep22 := nat_lit 8589934592000000000000000

noncomputable def ep23 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 ep0 ep22 ep2 ep22 1200336 1048576 1 394670 1200336 1048576 1 394670 600168 524288 2 524288 BSN.pi_near_15 rfl rfl rfl

noncomputable def ep24 := nat_lit 17179869184000000000000000

noncomputable def ep25 := nat_lit 18396140817044028275299783

noncomputable def ep26 := nat_lit 35576010001044028275299783

noncomputable def ep27 := nat_lit 145019262663961446558303139663424756232419223153299357158415217874016130572233056993847515999529612750616182853355499335896178729185698845314776375864537073527142908641610750276034469165612529925303649396973267518946591078603565291376312767403717761600170009932259137778521478520425507632472584532570900560707662248426541531715360699177249902784721815296292248142738824858695953661559845440650653128788875447728828657762006237171740033404723254477174341920697506370253193455781322964835857351124092897592956162654178130575

noncomputable def ep28 := nat_lit 15500762873619990602332184736899274490522931101512051618692838888825382235673431503644115344741331161500627469184702974962114537943617674254904297224139410345221262767191485292268260077615645253784097850065864022184521411511133693085443040736512010941548648374196772723338837137976260321103066698629790037694560548409922339907589559883712609967105556007429010014773911317423638534096849366294542840133852248768895750397896505791271178551667935288585787166713880920071720072716082683081155281219708172458141800988558163320

noncomputable def ep29 := nat_lit 12900190794487083783367107939442176642390171280542213571554777169279725287102813254708993369099729304728646904879886535518616983985412662170766446331701281703998252143668221340329975389245922410714088123244705567402747658401492589451585970559635763980329972215329212888079422466283203384882259392047898400615815810081169907384366653346471604103896809335921621947903075223769953790093549808584241881353287841076643853121427928248525828402335494512605306631304432120211393210317325496757155861061354331245840675149075

noncomputable def ep30 := BSN.log_dyadic_bound ep25 ep26 11 10 ep27 1048576 394670 ep28 ep29 1200336 ep5 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep25) (BSN.artanhQ ep26) 0 10 ep28 ep27 ep29 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep31 := nat_lit 18396140817044045455168967

noncomputable def ep32 := nat_lit 35576010001044045455168967

noncomputable def ep33 := nat_lit 145019262663962847171784895425483977818796535899227200426399035286881207006285364467913811844950531107314785650583974625982406238691319033447632878979985852280879486690814033867010958364699188952871572448188560932645032521756218245629809291975913196623825614492380080480004685076434733043183791438169545293975334857826316990371107134320667652578346815517853870648072772035977941843998949310557583393428557296298890786965786350523173236912472938174255438182435383147950274229549088258679583524155427309880956162654178130575

noncomputable def ep34 := nat_lit 15500762873620157189619721156942591192100275120160672416764593300158228469749443299607348495591439275767946573253526107895503597951484257520435868240203420954375895980141891044871083424251900562230440202302413072793440172565998181227591194192658878334739610458454844032013325963992941389843551995646587189684848765634635122388286241104146031552341815777883628509454807838726994150833304950745987647656768534710890974432620160470644835720379148964170536679305861738540146791997074363921127776563807649880221800988558163320

noncomputable def ep35 := nat_lit 12900190794487324729109480814509220959173684627296055849229843377126536688487849343376525559792931631054411655715865486295286288812423905434305314401904993536755333953308594664509631000767632482919425633906965368325056855874260596615770736441041599390097968820060635361729170158825410327022636428624381203910573184452046894301676992229743752846881064485858738985580654099214803581683226335297196686880535448467637789069028262446657986458573827723305156755787640135484017403116612632808333639900906331245840675149075

noncomputable def ep36 := BSN.log_dyadic_bound ep31 ep32 11 10 ep33 1048576 394670 ep34 ep35 1200336 ep14 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep31) (BSN.artanhQ ep32) 0 10 ep34 ep33 ep35 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep37 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 600168 524288 2 524288 75021 65536 1 262144 (ep23 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep22 1200336 1048576 1 394670 Bool.false (BSN.logfrac_isNear ep5 ep24 1 ep0 ep22 1200336 1048576 394670 rfl rfl rfl (ep30 rfl))) (BSN.isNear_log_sfrac ep2 ep22 1200336 1048576 1 394670 Bool.false (BSN.logfrac_isNear ep14 ep24 1 ep2 ep22 1200336 1048576 394670 rfl rfl rfl (ep36 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl

theorem EMRow48.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 75021 65536 1 262144 := ep37

noncomputable abbrev qz719 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 138478 1000)))

noncomputable abbrev qz536 := qz719

noncomputable abbrev qz273 := qz536

noncomputable abbrev qz3 := (BSN.headSumC qz273 9)

noncomputable abbrev qz720 := (@instHAdd Complex Complex.instAdd)

noncomputable abbrev qz537 := qz720

noncomputable abbrev qz274 := qz537

noncomputable abbrev qz4 := qz274

noncomputable abbrev qz5 := qz273

noncomputable abbrev qz538 := (@instHPow Complex Complex Complex.instPow)

noncomputable abbrev qz275 := qz538

noncomputable abbrev qz6 := qz275

noncomputable abbrev qz539 := (@Neg.neg Complex Complex.instNeg qz719)

noncomputable abbrev qz276 := qz539

noncomputable abbrev qz7 := qz276

noncomputable abbrev qz540 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 8) qz7)

noncomputable def ep38 := @Enclosure.Complex.IsNear.of_eq qz3 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 8) qz540) Bool.false 168028019309 1099511627776 518547772728577 216972127067176960 Bool.true 177612284051 274877906944 129611198315373 54243031766794240

noncomputable def ep39 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 8) qz540 Bool.true 9371565555 549755813888 232071230491347 108486063533588480 Bool.true 1051376729217 1099511627776 463957425281239 216972127067176960 Bool.false

noncomputable abbrev qz541 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 7) qz7)

noncomputable def ep40 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 8) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 7) qz541) Bool.true 9371565555 549755813888 232071230491347 108486063533588480 Bool.true 1051376729217 1099511627776 463957425281239 216972127067176960

noncomputable def ep41 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 7) qz541 Bool.true 333508805685 1099511627776 405930130901463 216972127067176960 Bool.true 661359329421 549755813888 202883358203309 108486063533588480 Bool.false

noncomputable abbrev qz542 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 6) qz7)

noncomputable def ep42 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 7) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 6) qz542) Bool.true 333508805685 1099511627776 405930130901463 216972127067176960 Bool.true 661359329421 549755813888 202883358203309 108486063533588480

noncomputable def ep43 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 6) qz542 Bool.false 57183353835 549755813888 85754149449677 54243031766794240 Bool.true 646404817635 549755813888 171522928329579 108486063533588480 Bool.true

noncomputable abbrev qz543 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 5) qz7)

noncomputable def ep44 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 6) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 5) qz543) Bool.false 57183353835 549755813888 85754149449677 54243031766794240 Bool.true 646404817635 549755813888 171522928329579 108486063533588480

noncomputable def ep45 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 5) qz543 Bool.false 149499344907 274877906944 13706047232101 10848606353358848 Bool.true 1204006566643 1099511627776 54863270454215 43394425413435392 Bool.true

noncomputable def ep46 := nat_lit 1421459226480214561259520

noncomputable abbrev qz544 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 4) qz7)

noncomputable def ep47 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 5) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 4) qz544) Bool.false 149499344907 274877906944 13706047232101 10848606353358848 Bool.true 1204006566643 1099511627776 54863270454215 43394425413435392

noncomputable def ep48 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 4) qz544 Bool.false 558686953793 549755813888 98614433961231 108486063533588480 Bool.true 1384222882875 1099511627776 197551931168347 216972127067176960 Bool.true

noncomputable abbrev qz545 := (@Nat.cast Complex Complex.instNatCast 3)

noncomputable abbrev qz277 := qz545

noncomputable abbrev qz8 := qz277

noncomputable def ep49 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 4) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz7)) Bool.false 558686953793 549755813888 98614433961231 108486063533588480 Bool.true 1384222882875 1099511627776 197551931168347 216972127067176960

noncomputable def ep50 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz7) Bool.false 242595697699 274877906944 27124960446069 54243031766794240 Bool.true 191668341865 274877906944 27167380367009 54243031766794240 Bool.false

noncomputable abbrev qz546 := (@Nat.cast Complex Complex.instNatCast 2)

noncomputable abbrev qz278 := qz546

noncomputable abbrev qz9 := qz278

noncomputable def ep51 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 3) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz7)) Bool.false 242595697699 274877906944 27124960446069 54243031766794240 Bool.true 191668341865 274877906944 27167380367009 54243031766794240

noncomputable def ep52 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz7) Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.true

noncomputable abbrev qz547 := (Enclosure.sfrac Bool.false 0 1)

noncomputable abbrev qz10 := qz547

noncomputable def ep53 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz10) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz5)

noncomputable abbrev qz721 := (Enclosure.sfrac Bool.false 138478 1000)

noncomputable abbrev qz548 := qz721

noncomputable abbrev qz279 := qz548

noncomputable abbrev qz280 := (Enclosure.sfrac Bool.false 2 1)

noncomputable abbrev qz11 := (@HMul.hMul Real Real Real qz269 qz279 (Real.log qz280))

noncomputable abbrev qz12 := qz279

noncomputable abbrev qz281 := (@Eq.refl Real qz548)

noncomputable abbrev qz13 := qz281

noncomputable abbrev qz282 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2)))

noncomputable def ep54 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz9 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz282 (Real.cos qz11)) (@HMul.hMul Real Real Real qz0 qz282 (@Neg.neg Real Real.instNeg (Real.sin qz11)))) Bool.true 32282209245 274877906944 27124960446069 54243031766794240 Bool.true 191668341865 274877906944 27167380367009 54243031766794240 (BSN.cpow_neg_s_mk qz12 138478 1000 2 qz13 rfl)

noncomputable abbrev qz14 := (@Nat.cast Real Real.instNatCast 1)

noncomputable abbrev qz283 := (Real.sqrt (@Nat.cast Real Real.instNatCast 2))

noncomputable abbrev qz284 := (@Nat.cast Real Real.instNatCast 2)

noncomputable def ep55 := @Enclosure.Real.IsNear.inv_image qz283 1482911 1048576 1 1048576 370727 370728 524288 (@Enclosure.Real.IsNear.of_eq qz283 (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz284 qz14)) Bool.false 1482911 1048576 1 1048576 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz284 qz14)) Bool.false 1482911 1048576 1 1048576 1482911 1048576 1 1048576 (BSN.sqrt_enclosure 2 1 741455 741456 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep56 := BSN.log_dyadic_bound 1 3 6 5 613814355 524288 197335 24381081 945 363408 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 1) (BSN.artanhQ 3) 0 5 24381081 613814355 945 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep57 := nat_lit 16487074697142873510533551335306256

noncomputable def ep58 := nat_lit 2552117751907038475975309555738261585920

noncomputable def ep59 := nat_lit 17864824263349269331827166890167831101440

noncomputable abbrev qz15 := (BSN.sinEvenQ 2147483648)

noncomputable abbrev qz16 := (BSN.sinOddQ 2147483648)

noncomputable def ep60 := BSN.sin_dyadic_bound_f 358332254 2147483648 2 1 1048576 395056 ep57 ep58 ep57 ep57 ep59 ep57 174156 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 358332254) qz15 0 1 ep57 ep58 ep57 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 358332254) qz16 0 1 ep57 ep59 ep57 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz17 := (@Nat.cast Real Real.instNatCast 524288)

noncomputable abbrev qz18 := (Enclosure.Real.IsNear.const Bool.false 138478 1000)

noncomputable abbrev qz19 := (@Nat.cast Real Real.instNatCast 75557863725914323419136)

noncomputable abbrev qz285 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 50324013) qz17)

noncomputable abbrev qz286 := (BSN.isNear_log_sfrac 2 1 363408 524288 1 197335 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 363408 524288 197335 rfl rfl rfl (ep56 rfl)))

noncomputable def ep61 := @Enclosure.Real.IsNear.cos_image qz11 qz285 Bool.false 50324013 524288 23 32768 Bool.true 174156 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz11 Bool.false 1572625407 16384000 69239 98667500 50324013 524288 23 32768 (@Enclosure.Real.IsNear.mulLit_ff qz12 (Real.log qz280) 138478 1000 0 1 363408 524288 1 197335 1572625407 16384000 69239 98667500 qz18 qz286 rfl) rfl) (Enclosure.sfrac_false_div 50324013 524288) (BSN.cos_reduce1 qz285 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 12607695357545751248896) qz19) 226375608064910080 72057594037927936 Bool.false 174156 1048576 15 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q1 50324013 524288 226375608064910080 72057594037927936 15 12607695357545751248896 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 174156 1048576 12607695357545751248896 75557863725914323419136 358332254 2147483648 395056 394670 (ep60 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep62 := nat_lit 510423550381407695195061911147652317184

noncomputable def ep63 := nat_lit 7656353255721115427925928667214784757760

noncomputable abbrev qz20 := (BSN.cosEvenQ 2147483648)

noncomputable abbrev qz21 := (BSN.cosOddQ 2147483648)

noncomputable def ep64 := BSN.cos_dyadic_bound_f 358332254 2147483648 2 1 1048576 395056 ep57 ep62 ep57 ep57 ep63 ep57 1034012 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 358332254) qz20 0 1 ep57 ep62 ep57 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 358332254) qz21 0 1 ep57 ep63 ep57 rfl rfl rfl rfl) rfl rfl

noncomputable def ep65 := @Enclosure.Real.IsNear.sin_image qz11 qz285 Bool.false 50324013 524288 23 32768 Bool.false 1034012 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz11 Bool.false 1572625407 16384000 69239 98667500 50324013 524288 23 32768 (@Enclosure.Real.IsNear.mulLit_ff qz12 (Real.log qz280) 138478 1000 0 1 363408 524288 1 197335 1572625407 16384000 69239 98667500 qz18 qz286 rfl) rfl) (Enclosure.sfrac_false_div 50324013 524288) (BSN.sin_reduce1 qz285 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 12607695357545751248896) qz19) 226375608064910080 72057594037927936 Bool.false 1034012 1048576 15 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q1 50324013 524288 226375608064910080 72057594037927936 15 12607695357545751248896 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1034012 1048576 12607695357545751248896 75557863725914323419136 358332254 2147483648 395056 394670 (ep64 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz287 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2))) Bool.false 741455 1048576 1 1048576 741455 1048576 1 1048576 (ep55 rfl rfl) rfl)

noncomputable def ep66 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz282 (Real.cos qz11)) (@HMul.hMul Real Real Real qz0 qz282 (@Neg.neg Real Real.instNeg (Real.sin qz11))) Bool.true 32282209245 274877906944 27124960446069 54243031766794240 Bool.true 191668341865 274877906944 27167380367009 54243031766794240 (@Enclosure.Real.IsNear.mulLit_ft qz282 (Real.cos qz11) 741455 1048576 1 1048576 43539 262144 4571473 6466273280 32282209245 274877906944 27124960446069 54243031766794240 qz287 (@Enclosure.Real.IsNear.recentre' (Real.cos qz11) Bool.true 174156 1048576 4571473 6466273280 43539 262144 4571473 6466273280 (ep61 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz282 (@Neg.neg Real Real.instNeg (Real.sin qz11)) 741455 1048576 1 1048576 258503 262144 4571473 6466273280 191668341865 274877906944 27167380367009 54243031766794240 qz287 (@Enclosure.Real.IsNear.neg (Real.sin qz11) Bool.false 258503 262144 4571473 6466273280 (@Enclosure.Real.IsNear.recentre' (Real.sin qz11) Bool.false 1034012 1048576 4571473 6466273280 258503 262144 4571473 6466273280 (ep65 rfl rfl) rfl)) rfl)

noncomputable abbrev qz549 := (Enclosure.Real.IsNear.const Bool.false 0 1)

noncomputable abbrev qz22 := qz549

noncomputable def ep67 := @ep52 32282209245 274877906944 27124960446069 54243031766794240 Bool.true 191668341865 274877906944 27167380367009 54243031766794240 Bool.false 242595697699 242595697699 274877906944 27124960446069 54243031766794240 Bool.true 191668341865 191668341865 274877906944 27167380367009 54243031766794240 (ep53 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz10 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz22)) (ep54 ep66) rfl rfl

noncomputable abbrev qz550 := (Real.log (Enclosure.sfrac Bool.false 3 1))

noncomputable abbrev qz23 := (@HMul.hMul Real Real Real qz269 qz279 qz550)

noncomputable abbrev qz288 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 3)))

noncomputable def ep68 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz8 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz288 (Real.cos qz23)) (@HMul.hMul Real Real Real qz0 qz288 (@Neg.neg Real Real.instNeg (Real.sin qz23)))) Bool.false 73495558395 549755813888 44364513069093 108486063533588480 Bool.true 617549515415 1099511627776 88882409700311 216972127067176960 (BSN.cpow_neg_s_mk qz12 138478 1000 3 qz13 rfl)

noncomputable abbrev qz289 := (Real.sqrt (@Nat.cast Real Real.instNatCast 3))

noncomputable abbrev qz290 := (@Nat.cast Real Real.instNatCast 3)

noncomputable def ep69 := @Enclosure.Real.IsNear.inv_image qz289 1816187 1048576 1 1048576 302697 302698 524288 (@Enclosure.Real.IsNear.of_eq qz289 (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz290 qz14)) Bool.false 1816187 1048576 1 1048576 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz290 qz14)) Bool.false 1816187 1048576 1 1048576 1816187 1048576 1 1048576 (BSN.sqrt_enclosure 3 1 908093 908094 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep70 := BSN.log_dyadic_bound 1 2 10 9 171633298636800 524288 197335 16925142283965 34459425 575989 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP 1) (BSN.artanhQ 2) 0 9 16925142283965 171633298636800 34459425 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep71 := nat_lit 2433644327504810277852847123540029795409192183458304763315065424286659981168161

noncomputable def ep72 := nat_lit 18237254054877300779212430138868345486890022584838388836214569481246317918289920

noncomputable def ep73 := nat_lit 4621741148463991199090852980745755149189750055809302032193309035281770434081

noncomputable def ep74 := nat_lit 7291689500217502851160359664658597875929197050263295685880809654789416402636321

noncomputable def ep75 := nat_lit 820676432469478535064559356249075546910051016317727497629655626656084306323046400

noncomputable def ep76 := BSN.cos_dyadic_bound_f 2871446323 2147483648 3 2 1048576 395056 ep71 ep72 ep73 ep74 ep75 ep73 242802 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2871446323) qz20 0 2 ep71 ep72 ep73 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2871446323) qz21 0 2 ep74 ep75 ep73 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz24 := (@Nat.cast Real Real.instNatCast 1048576)

noncomputable abbrev qz25 := (@Nat.cast Real Real.instNatCast 151115727451828646838272)

noncomputable abbrev qz291 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 159523609) qz24)

noncomputable abbrev qz292 := (BSN.isNear_log_sfrac 3 1 575989 524288 1 197335 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 575989 524288 197335 rfl rfl rfl (ep70 rfl)))

noncomputable def ep77 := @Enclosure.Real.IsNear.cos_image qz23 qz291 Bool.false 159523609 1048576 737 1048576 Bool.false 242802 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz23 Bool.false 39880902371 262144000 69239 98667500 159523609 1048576 737 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz12 qz550 138478 1000 0 1 575989 524288 1 197335 39880902371 262144000 69239 98667500 qz18 qz292 rfl) rfl) (Enclosure.sfrac_false_div 159523609 1048576) (BSN.cos_reduce0 qz291 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 202060071756263868858368) qz25) 226375608064910080 72057594037927936 Bool.false 242802 1048576 24 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q0 159523609 1048576 226375608064910080 72057594037927936 24 202060071756263868858368 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 242802 1048576 202060071756263868858368 151115727451828646838272 2871446323 2147483648 395056 394670 (ep76 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep78 := nat_lit 4376862396589887307175852139987457027617194130180301132341363116487762549755425

noncomputable def ep79 := nat_lit 164135286493895707012911871249815109382010203263545499525931125331216861264609280

noncomputable def ep80 := nat_lit 11455728219685525056852513271331656230660629793239002190937161852363207621037601

noncomputable def ep81 := nat_lit 3009146919054754628570050972913277005336853726498334157975403964405642456517836800

noncomputable def ep82 := BSN.sin_dyadic_bound_f 2871446323 2147483648 3 2 1048576 395056 ep78 ep79 ep73 ep80 ep81 ep73 1020077 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2871446323) qz15 0 2 ep78 ep79 ep73 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2871446323) qz16 0 2 ep80 ep81 ep73 rfl rfl rfl rfl) rfl rfl

noncomputable def ep83 := @Enclosure.Real.IsNear.sin_image qz23 qz291 Bool.false 159523609 1048576 737 1048576 Bool.false 1020077 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz23 Bool.false 39880902371 262144000 69239 98667500 159523609 1048576 737 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz12 qz550 138478 1000 0 1 575989 524288 1 197335 39880902371 262144000 69239 98667500 qz18 qz292 rfl) rfl) (Enclosure.sfrac_false_div 159523609 1048576) (BSN.sin_reduce0 qz291 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 202060071756263868858368) qz25) 226375608064910080 72057594037927936 Bool.false 1020077 1048576 24 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q0 159523609 1048576 226375608064910080 72057594037927936 24 202060071756263868858368 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1020077 1048576 202060071756263868858368 151115727451828646838272 2871446323 2147483648 395056 394670 (ep82 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz293 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 3))) Bool.false 605395 1048576 1 1048576 605395 1048576 1 1048576 (ep69 rfl rfl) rfl)

noncomputable def ep84 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz288 (Real.cos qz23)) (@HMul.hMul Real Real Real qz0 qz288 (@Neg.neg Real Real.instNeg (Real.sin qz23))) Bool.false 73495558395 549755813888 44364513069093 108486063533588480 Bool.true 617549515415 1099511627776 88882409700311 216972127067176960 (@Enclosure.Real.IsNear.mulLit_ff qz288 (Real.cos qz23) 605395 1048576 1 1048576 121401 524288 146484471 206920744960 73495558395 549755813888 44364513069093 108486063533588480 qz293 (@Enclosure.Real.IsNear.recentre' (Real.cos qz23) Bool.false 242802 1048576 146484471 206920744960 121401 524288 146484471 206920744960 (ep77 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz288 (@Neg.neg Real Real.instNeg (Real.sin qz23)) 605395 1048576 1 1048576 1020077 1048576 146484471 206920744960 617549515415 1099511627776 88882409700311 216972127067176960 qz293 (@Enclosure.Real.IsNear.neg (Real.sin qz23) Bool.false 1020077 1048576 146484471 206920744960 (@Enclosure.Real.IsNear.recentre' (Real.sin qz23) Bool.false 1020077 1048576 146484471 206920744960 1020077 1048576 146484471 206920744960 (ep83 rfl rfl) rfl)) rfl)

noncomputable def ep85 := @ep50 73495558395 549755813888 44364513069093 108486063533588480 Bool.true 617549515415 1099511627776 88882409700311 216972127067176960 Bool.false 153570700495539081838592 558686953793 549755813888 98614433961231 108486063533588480 Bool.true 380492288788669661184000 1384222882875 1099511627776 197551931168347 216972127067176960 (ep51 (BSN.head_sum_c_succ qz5 2 3 rfl rfl) (ep67 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep68 ep84) rfl rfl

noncomputable abbrev qz551 := (Real.log (Enclosure.sfrac Bool.false 4 1))

noncomputable abbrev qz26 := (@HMul.hMul Real Real Real qz269 qz279 qz551)

noncomputable abbrev qz294 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 4)))

noncomputable def ep86 := @Enclosure.Complex.IsNear.of_eq qz544 (Complex.mk (@HMul.hMul Real Real Real qz0 qz294 (Real.cos qz26)) (@HMul.hMul Real Real Real qz0 qz294 (@Neg.neg Real Real.instNeg (Real.sin qz26)))) Bool.true 259688263979 549755813888 38446038359779 108486063533588480 Bool.false 22527039529 137438953472 9595552637841 27121515883397120 (BSN.cpow_neg_s_mk qz12 138478 1000 4 qz13 rfl)

noncomputable abbrev qz295 := (Real.sqrt (@Nat.cast Real Real.instNatCast 4))

noncomputable abbrev qz296 := (@Nat.cast Real Real.instNatCast 4)

noncomputable def ep87 := @Enclosure.Real.IsNear.inv_image qz295 2097153 1048576 1 1048576 262143 262144 524288 (@Enclosure.Real.IsNear.of_eq qz295 (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz296 qz14)) Bool.false 2097153 1048576 1 1048576 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz296 qz14)) Bool.false 2097153 1048576 1 1048576 2097153 1048576 1 1048576 (BSN.sqrt_enclosure 4 1 1048576 1048577 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep88 := nat_lit 318077276165597140789031982421875

noncomputable def ep89 := nat_lit 49379992292270016474244603430625

noncomputable def ep90 := nat_lit 20095619060363156210525625

noncomputable def ep91 := BSN.log_dyadic_bound 3 5 14 13 ep88 524288 197335 ep89 ep90 726817 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base13 (BSN.artanhP 3) (BSN.artanhQ 5) 0 13 ep89 ep88 ep90 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep92 := nat_lit 264629439196924653160822057522381056

noncomputable def ep93 := BSN.cos_dyadic_bound_f 717231804 2147483648 2 1 1048576 395056 ep92 ep62 ep92 ep92 ep63 ep92 990634 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 717231804) qz20 0 1 ep92 ep62 ep92 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 717231804) qz21 0 1 ep92 ep63 ep92 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz297 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 201296329) qz24)

noncomputable abbrev qz298 := (BSN.isNear_log_sfrac 4 1 726817 524288 1 197335 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 726817 524288 197335 rfl rfl rfl (ep91 rfl)))

noncomputable def ep94 := @Enclosure.Real.IsNear.cos_image qz26 qz297 Bool.false 201296329 1048576 23 32768 Bool.true 990634 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz26 Bool.false 50324082263 262144000 69239 98667500 201296329 1048576 23 32768 (@Enclosure.Real.IsNear.mulLit_ff qz12 qz551 138478 1000 0 1 726817 524288 1 197335 50324082263 262144000 69239 98667500 qz18 qz298 rfl) rfl) (Enclosure.sfrac_false_div 201296329 1048576) (BSN.cos_reduce2 qz297 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 50470701337280017072128) qz25) 226375608064910080 72057594037927936 Bool.false 990634 1048576 30 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q2 201296329 1048576 226375608064910080 72057594037927936 30 50470701337280017072128 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 990634 1048576 50470701337280017072128 151115727451828646838272 717231804 2147483648 395056 394670 (ep93 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep95 := BSN.sin_dyadic_bound_f 717231804 2147483648 2 1 1048576 395056 ep92 ep58 ep92 ep92 ep59 ep92 343736 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 717231804) qz15 0 1 ep92 ep58 ep92 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 717231804) qz16 0 1 ep92 ep59 ep92 rfl rfl rfl rfl) rfl rfl

noncomputable def ep96 := @Enclosure.Real.IsNear.sin_image qz26 qz297 Bool.false 201296329 1048576 23 32768 Bool.true 343736 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz26 Bool.false 50324082263 262144000 69239 98667500 201296329 1048576 23 32768 (@Enclosure.Real.IsNear.mulLit_ff qz12 qz551 138478 1000 0 1 726817 524288 1 197335 50324082263 262144000 69239 98667500 qz18 qz298 rfl) rfl) (Enclosure.sfrac_false_div 201296329 1048576) (BSN.sin_reduce2 qz297 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 50470701337280017072128) qz25) 226375608064910080 72057594037927936 Bool.false 343736 1048576 30 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q2 201296329 1048576 226375608064910080 72057594037927936 30 50470701337280017072128 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 343736 1048576 50470701337280017072128 151115727451828646838272 717231804 2147483648 395056 394670 (ep95 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz299 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 4))) Bool.false 524287 1048576 1 1048576 524287 1048576 1 1048576 (ep87 rfl rfl) rfl)

noncomputable def ep97 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz294 (Real.cos qz26)) (@HMul.hMul Real Real Real qz0 qz294 (@Neg.neg Real Real.instNeg (Real.sin qz26))) Bool.true 259688263979 549755813888 38446038359779 108486063533588480 Bool.false 22527039529 137438953472 9595552637841 27121515883397120 (@Enclosure.Real.IsNear.mulLit_ft qz294 (Real.cos qz26) 524287 1048576 1 1048576 495317 524288 4571473 6466273280 259688263979 549755813888 38446038359779 108486063533588480 qz299 (@Enclosure.Real.IsNear.recentre' (Real.cos qz26) Bool.true 990634 1048576 4571473 6466273280 495317 524288 4571473 6466273280 (ep94 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz294 (@Neg.neg Real Real.instNeg (Real.sin qz26)) 524287 1048576 1 1048576 42967 131072 4571473 6466273280 22527039529 137438953472 9595552637841 27121515883397120 qz299 (@Enclosure.Real.IsNear.neg (Real.sin qz26) Bool.true 42967 131072 4571473 6466273280 (@Enclosure.Real.IsNear.recentre' (Real.sin qz26) Bool.true 343736 1048576 4571473 6466273280 42967 131072 4571473 6466273280 (ep96 rfl rfl) rfl)) rfl)

noncomputable def ep98 := @ep48 259688263979 549755813888 38446038359779 108486063533588480 Bool.false 22527039529 137438953472 9595552637841 27121515883397120 Bool.false 164376268070141225336832 149499344907 274877906944 13706047232101 10848606353358848 Bool.true 165477402492829744234496 1204006566643 1099511627776 54863270454215 43394425413435392 (ep49 (BSN.head_sum_c_succ qz5 3 4 rfl rfl) (ep85 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep86 ep97) rfl rfl

noncomputable abbrev qz552 := (Real.log (Enclosure.sfrac Bool.false 5 1))

noncomputable abbrev qz27 := (@HMul.hMul Real Real Real qz269 qz279 qz552)

noncomputable abbrev qz300 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 5)))

noncomputable def ep99 := @Enclosure.Complex.IsNear.of_eq qz543 (Complex.mk (@HMul.hMul Real Real Real qz0 qz300 (Real.cos qz27)) (@HMul.hMul Real Real Real qz0 qz300 (@Neg.neg Real Real.instNeg (Real.sin qz27)))) Bool.true 241815335979 549755813888 4305978322293 13560757941698560 Bool.true 88803068627 1099511627776 68729504388083 216972127067176960 (BSN.cpow_neg_s_mk qz12 138478 1000 5 qz13 rfl)

noncomputable abbrev qz301 := (Real.sqrt (@Nat.cast Real Real.instNatCast 5))

noncomputable abbrev qz302 := (@Nat.cast Real Real.instNatCast 5)

noncomputable def ep100 := @Enclosure.Real.IsNear.inv_image qz301 2344687 1048576 1 1048576 234468 234469 524288 (@Enclosure.Real.IsNear.of_eq qz301 (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz302 qz14)) Bool.false 2344687 1048576 1 1048576 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz302 qz14)) Bool.false 2344687 1048576 1 1048576 2344687 1048576 1 1048576 (BSN.sqrt_enclosure 5 1 1172343 1172344 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep101 := nat_lit 3696382175741467532940033205863946875

noncomputable def ep102 := nat_lit 765440954430599474856563326857688500

noncomputable def ep103 := nat_lit 108794268166472120024432640000

noncomputable def ep104 := BSN.log_dyadic_bound 2 3 18 17 ep101 524288 197335 ep102 ep103 843808 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.artanhP 2) (BSN.artanhQ 3) 0 17 8 307084260767580 1483365253795425 132843110400 1663129201793174588340 2491889415829100854875 818968088287641600 ep102 ep101 ep103 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.artanhP 2) (BSN.artanhQ 3) 0 8 307084260767580 1483365253795425 132843110400 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.artanhP 2) (BSN.artanhQ 3) 8 17 1663129201793174588340 2491889415829100854875 818968088287641600 rfl rfl rfl rfl)) rfl rfl

noncomputable def ep105 := nat_lit 5100530306677361663330384026289878491557587146732591032060181264767072919573025

noncomputable def ep106 := nat_lit 6274209983247690312210809927629579254158935686435124208175542208071320949281

noncomputable def ep107 := nat_lit 13348373510848784286312188281352567206715518536045414882868190529862599317344801

noncomputable def ep108 := BSN.sin_dyadic_bound_f 2983285939 2147483648 3 2 1048576 395056 ep105 ep79 ep106 ep107 ep81 ep106 1031334 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2983285939) qz15 0 2 ep105 ep79 ep106 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2983285939) qz16 0 2 ep107 ep81 ep106 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz553 := (@Nat.cast Real Real.instNatCast 131072)

noncomputable abbrev qz303 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 29212211) qz553)

noncomputable abbrev qz304 := (BSN.isNear_log_sfrac 5 1 843808 524288 1 197335 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 843808 524288 197335 rfl rfl rfl (ep104 rfl rfl)))

noncomputable abbrev qz305 := (@Nat.cast Real Real.instNatCast 18889465931478580854784)

noncomputable def ep109 := @Enclosure.Real.IsNear.cos_image qz27 qz303 Bool.false 29212211 131072 737 1048576 Bool.true 1031334 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz27 Bool.false 1825763191 8192000 69239 98667500 29212211 131072 737 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz12 qz552 138478 1000 0 1 843808 524288 1 197335 1825763191 8192000 69239 98667500 qz18 qz304 rfl) rfl) (Enclosure.sfrac_false_div 29212211 131072) (BSN.cos_reduce1 qz303 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26241260636556683640832) qz305) 226375608064910080 72057594037927936 Bool.false 1031334 1048576 35 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q1 29212211 131072 226375608064910080 72057594037927936 35 26241260636556683640832 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1031334 1048576 26241260636556683640832 18889465931478580854784 2983285939 2147483648 395056 394670 (ep108 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep110 := nat_lit 2836416485924422119766751485684434530533841275156521739681512054740849986851361

noncomputable def ep111 := nat_lit 8496701037806770978675832837198044433093205954096694970628185079806407318655521

noncomputable def ep112 := BSN.cos_dyadic_bound_f 2983285939 2147483648 3 2 1048576 395056 ep110 ep72 ep106 ep111 ep75 ep106 189371 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2983285939) qz20 0 2 ep110 ep72 ep106 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2983285939) qz21 0 2 ep111 ep75 ep106 rfl rfl rfl rfl) rfl rfl

noncomputable def ep113 := @Enclosure.Real.IsNear.sin_image qz27 qz303 Bool.false 29212211 131072 737 1048576 Bool.false 189371 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz27 Bool.false 1825763191 8192000 69239 98667500 29212211 131072 737 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz12 qz552 138478 1000 0 1 843808 524288 1 197335 1825763191 8192000 69239 98667500 qz18 qz304 rfl) rfl) (Enclosure.sfrac_false_div 29212211 131072) (BSN.sin_reduce1 qz303 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26241260636556683640832) qz305) 226375608064910080 72057594037927936 Bool.false 189371 1048576 35 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q1 29212211 131072 226375608064910080 72057594037927936 35 26241260636556683640832 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 189371 1048576 26241260636556683640832 18889465931478580854784 2983285939 2147483648 395056 394670 (ep112 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz306 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 5))) Bool.false 468937 1048576 1 1048576 468937 1048576 1 1048576 (ep100 rfl rfl) rfl)

noncomputable def ep114 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz300 (Real.cos qz27)) (@HMul.hMul Real Real Real qz0 qz300 (@Neg.neg Real Real.instNeg (Real.sin qz27))) Bool.true 241815335979 549755813888 4305978322293 13560757941698560 Bool.true 88803068627 1099511627776 68729504388083 216972127067176960 (@Enclosure.Real.IsNear.mulLit_ft qz300 (Real.cos qz27) 468937 1048576 1 1048576 515667 524288 146484471 206920744960 241815335979 549755813888 4305978322293 13560757941698560 qz306 (@Enclosure.Real.IsNear.recentre' (Real.cos qz27) Bool.true 1031334 1048576 146484471 206920744960 515667 524288 146484471 206920744960 (ep109 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz300 (@Neg.neg Real Real.instNeg (Real.sin qz27)) 468937 1048576 1 1048576 189371 1048576 146484471 206920744960 88803068627 1099511627776 68729504388083 216972127067176960 qz306 (@Enclosure.Real.IsNear.neg (Real.sin qz27) Bool.false 189371 1048576 146484471 206920744960 (@Enclosure.Real.IsNear.recentre' (Real.sin qz27) Bool.false 189371 1048576 146484471 206920744960 189371 1048576 146484471 206920744960 (ep113 rfl rfl) rfl)) rfl)

noncomputable def ep115 := @ep45 241815335979 549755813888 4305978322293 13560757941698560 Bool.true 88803068627 1099511627776 68729504388083 216972127067176960 Bool.false 15718440614202955530240 57183353835 549755813888 85754149449677 54243031766794240 Bool.true ep46 646404817635 549755813888 171522928329579 108486063533588480 (ep47 (BSN.head_sum_c_succ qz5 4 5 rfl rfl) (ep98 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep99 ep114) rfl rfl

noncomputable abbrev qz554 := (Real.log (Enclosure.sfrac Bool.false 6 1))

noncomputable abbrev qz28 := (@HMul.hMul Real Real Real qz269 qz279 qz554)

noncomputable abbrev qz307 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 6)))

noncomputable def ep116 := @Enclosure.Complex.IsNear.of_eq qz542 (Complex.mk (@HMul.hMul Real Real Real qz0 qz307 (Real.cos qz28)) (@HMul.hMul Real Real Real qz0 qz307 (@Neg.neg Real Real.instNeg (Real.sin qz28)))) Bool.true 447875513355 1099511627776 12582706620551 43394425413435392 Bool.true 7477255893 274877906944 3136042987373 10848606353358848 (BSN.cpow_neg_s_mk qz12 138478 1000 6 qz13 rfl)

noncomputable abbrev qz308 := (Real.sqrt (@Nat.cast Real Real.instNatCast 6))

noncomputable abbrev qz309 := (@Nat.cast Real Real.instNatCast 6)

noncomputable abbrev qz555 := (@HDiv.hDiv Real Real Real qz1 qz309 qz14)

noncomputable def ep117 := @Enclosure.Real.IsNear.inv_image qz308 2568477 1048576 1 1048576 214039 214040 524288 (@Enclosure.Real.IsNear.of_eq qz308 (Real.sqrt qz555) Bool.false 2568477 1048576 1 1048576 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz555) Bool.false 2568477 1048576 1 1048576 2568477 1048576 1 1048576 (BSN.sqrt_enclosure 6 1 1284238 1284239 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep118 := BSN.log_dyadic_bound 2 10 4 3 105000000 524288 197335 1434560 960 212580 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 2) (BSN.artanhQ 10) 0 3 1434560 105000000 960 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep119 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz554 138478 1000 0 1 4034681531866359 2251799813685248 100000000039467 19733500000000000000 279357314584894830801 1125899906842624000 6923900002732655613 9866750000000000000000 qz18 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 100000000039467 19733500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz555) Bool.false 33845361775666394038272 18889465931478580854784 1000000000394670 197335000000000000000 4034681531866359 2251799813685248 100000000039467 19733500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 212580 524288 24973259072661432 36028797018963968 197335 1000000000000000 rfl rfl rfl rfl (ep118 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep120 := nat_lit 7012594033229707390347160474741189823952194591356035449101898258055791203577985

noncomputable def ep121 := nat_lit 11849117578777819353163366496023027190104861970029523528853859701430680809601

noncomputable def ep122 := nat_lit 18347133420474069552908870078566697971090816057980997423839208236343803478536321

noncomputable def ep123 := BSN.sin_dyadic_bound_f 3230061201 2147483648 3 2 1048576 395056 ep120 ep79 ep121 ep122 ep81 ep121 1046245 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3230061201) qz15 0 2 ep120 ep79 ep121 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3230061201) qz16 0 2 ep122 ep81 ep121 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz310 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 260171773) qz24)

noncomputable def ep124 := @Enclosure.Real.IsNear.cos_image qz28 qz310 Bool.false 260171773 1048576 737 1048576 Bool.true 1046245 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz28 Bool.false 279357314584894830801 1125899906842624000 6923900002732655613 9866750000000000000000 260171773 1048576 737 1048576 (ep119 rfl) rfl) (Enclosure.sfrac_false_div 260171773 1048576) (BSN.cos_reduce1 qz310 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 227295350367309839466496) qz25) 226375608064910080 72057594037927936 Bool.false 1046245 1048576 39 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q1 260171773 1048576 226375608064910080 72057594037927936 39 227295350367309839466496 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1046245 1048576 227295350367309839466496 151115727451828646838272 3230061201 2147483648 395056 394670 (ep123 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep125 := nat_lit 3901151848495960914349828426632226803169043600517810593291656303231630971236481

noncomputable def ep126 := nat_lit 11679757310330327104343158546904634355126921077613372732817261190292031552090241

noncomputable def ep127 := BSN.cos_dyadic_bound_f 3230061201 2147483648 3 2 1048576 395056 ep125 ep72 ep121 ep126 ep75 ep121 69868 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3230061201) qz20 0 2 ep125 ep72 ep121 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3230061201) qz21 0 2 ep126 ep75 ep121 rfl rfl rfl rfl) rfl rfl

noncomputable def ep128 := @Enclosure.Real.IsNear.sin_image qz28 qz310 Bool.false 260171773 1048576 737 1048576 Bool.false 69868 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz28 Bool.false 279357314584894830801 1125899906842624000 6923900002732655613 9866750000000000000000 260171773 1048576 737 1048576 (ep119 rfl) rfl) (Enclosure.sfrac_false_div 260171773 1048576) (BSN.sin_reduce1 qz310 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 227295350367309839466496) qz25) 226375608064910080 72057594037927936 Bool.false 69868 1048576 39 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q1 260171773 1048576 226375608064910080 72057594037927936 39 227295350367309839466496 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 69868 1048576 227295350367309839466496 151115727451828646838272 3230061201 2147483648 395056 394670 (ep127 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz311 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 6))) Bool.false 428079 1048576 1 1048576 428079 1048576 1 1048576 (ep117 rfl rfl) rfl)

noncomputable def ep129 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz307 (Real.cos qz28)) (@HMul.hMul Real Real Real qz0 qz307 (@Neg.neg Real Real.instNeg (Real.sin qz28))) Bool.true 447875513355 1099511627776 12582706620551 43394425413435392 Bool.true 7477255893 274877906944 3136042987373 10848606353358848 (@Enclosure.Real.IsNear.mulLit_ft qz307 (Real.cos qz28) 428079 1048576 1 1048576 1046245 1048576 146484471 206920744960 447875513355 1099511627776 12582706620551 43394425413435392 qz311 (@Enclosure.Real.IsNear.recentre' (Real.cos qz28) Bool.true 1046245 1048576 146484471 206920744960 1046245 1048576 146484471 206920744960 (ep124 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz307 (@Neg.neg Real Real.instNeg (Real.sin qz28)) 428079 1048576 1 1048576 17467 262144 146484471 206920744960 7477255893 274877906944 3136042987373 10848606353358848 qz311 (@Enclosure.Real.IsNear.neg (Real.sin qz28) Bool.false 17467 262144 146484471 206920744960 (@Enclosure.Real.IsNear.recentre' (Real.sin qz28) Bool.false 69868 1048576 146484471 206920744960 17467 262144 146484471 206920744960 (ep128 rfl rfl) rfl)) rfl)

noncomputable def ep130 := @ep43 447875513355 1099511627776 12582706620551 43394425413435392 Bool.true 7477255893 274877906944 3136042987373 10848606353358848 Bool.true 183348404908172016353280 333508805685 1099511627776 405930130901463 216972127067176960 Bool.true 181793068209131879399424 661359329421 549755813888 202883358203309 108486063533588480 (ep44 (BSN.head_sum_c_succ qz5 5 6 rfl rfl) (ep115 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep116 ep129) rfl rfl

noncomputable abbrev qz556 := (Real.log (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz29 := (@HMul.hMul Real Real Real qz269 qz279 qz556)

noncomputable abbrev qz312 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 7)))

noncomputable def ep131 := @Enclosure.Complex.IsNear.of_eq qz541 (Complex.mk (@HMul.hMul Real Real Real qz0 qz312 (Real.cos qz29)) (@HMul.hMul Real Real Real qz0 qz312 (@Neg.neg Real Real.instNeg (Real.sin qz29)))) Bool.false 314765674575 1099511627776 58212330081231 216972127067176960 Bool.false 271341929625 1099511627776 58190708874621 216972127067176960 (BSN.cpow_neg_s_mk qz12 138478 1000 7 qz13 rfl)

noncomputable abbrev qz313 := (Real.sqrt (@Nat.cast Real Real.instNatCast 7))

noncomputable abbrev qz314 := (@Nat.cast Real Real.instNatCast 7)

noncomputable abbrev qz557 := (@HDiv.hDiv Real Real Real qz1 qz314 qz14)

noncomputable def ep132 := @Enclosure.Real.IsNear.inv_image qz313 2774271 1048576 1 1048576 198162 198163 524288 (@Enclosure.Real.IsNear.of_eq qz313 (Real.sqrt qz557) Bool.false 2774271 1048576 1 1048576 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz557) Bool.false 2774271 1048576 1 1048576 2774271 1048576 1 1048576 (BSN.sqrt_enclosure 7 1 1387135 1387136 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep133 := BSN.log_dyadic_bound 3 11 5 4 202569142545 524288 197335 5259111624 688905 293399 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 3) (BSN.artanhQ 11) 0 4 5259111624 202569142545 688905 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep134 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz556 138478 1000 0 1 4381796493761783 2251799813685248 100000000039467 19733500000000000000 303391207431572093137 1125899906842624000 6923900002732655613 9866750000000000000000 qz18 (BSN.isNear_log_sfrac 7 1 4381796493761783 2251799813685248 100000000039467 19733500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz557) Bool.false 36757173121942042968064 18889465931478580854784 1000000000394670 197335000000000000000 4381796493761783 2251799813685248 100000000039467 19733500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 293399 524288 24973259072661432 36028797018963968 197335 1000000000000000 rfl rfl rfl rfl (ep133 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep135 := nat_lit 746072682486292815157632969337597667303761795231833925794660036937741038725665

noncomputable def ep136 := nat_lit 134525045803488391945306372525149247190447703226741281073962613332409788961

noncomputable def ep137 := nat_lit 1953782080247085058492555852233429363204877310278150319769037490605831199861281

noncomputable def ep138 := BSN.sin_dyadic_bound_f 1845441971 2147483648 3 2 1048576 395056 ep135 ep79 ep136 ep137 ep81 ep136 794211 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1845441971) qz15 0 2 ep135 ep79 ep136 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1845441971) qz16 0 2 ep137 ep81 ep136 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz315 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 35319385) qz553)

noncomputable def ep139 := @Enclosure.Real.IsNear.cos_image qz29 qz315 Bool.false 35319385 131072 737 1048576 Bool.false 794211 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz29 Bool.false 303391207431572093137 1125899906842624000 6923900002732655613 9866750000000000000000 35319385 131072 737 1048576 (ep134 rfl) rfl) (Enclosure.sfrac_false_div 35319385 131072) (BSN.cos_reduce3 qz315 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16232679250016872693760) qz305) 226375608064910080 72057594037927936 Bool.false 794211 1048576 42 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q3 35319385 131072 226375608064910080 72057594037927936 42 16232679250016872693760 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 794211 1048576 16232679250016872693760 18889465931478580854784 1845441971 2147483648 395056 394670 (ep138 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep140 := nat_lit 414544612512742003261771785797565437056396751885786288233066226126892759198241

noncomputable def ep141 := nat_lit 1243364787446619033001424744647646012674809360250905382137050753154013458016801

noncomputable def ep142 := BSN.cos_dyadic_bound_f 1845441971 2147483648 3 2 1048576 395056 ep140 ep72 ep136 ep141 ep75 ep136 684645 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1845441971) qz20 0 2 ep140 ep72 ep136 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1845441971) qz21 0 2 ep141 ep75 ep136 rfl rfl rfl rfl) rfl rfl

noncomputable def ep143 := @Enclosure.Real.IsNear.sin_image qz29 qz315 Bool.false 35319385 131072 737 1048576 Bool.true 684645 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz29 Bool.false 303391207431572093137 1125899906842624000 6923900002732655613 9866750000000000000000 35319385 131072 737 1048576 (ep134 rfl) rfl) (Enclosure.sfrac_false_div 35319385 131072) (BSN.sin_reduce3 qz315 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16232679250016872693760) qz305) 226375608064910080 72057594037927936 Bool.false 684645 1048576 42 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q3 35319385 131072 226375608064910080 72057594037927936 42 16232679250016872693760 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 684645 1048576 16232679250016872693760 18889465931478580854784 1845441971 2147483648 395056 394670 (ep142 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz316 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 7))) Bool.false 396325 1048576 1 1048576 396325 1048576 1 1048576 (ep132 rfl rfl) rfl)

noncomputable def ep144 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz312 (Real.cos qz29)) (@HMul.hMul Real Real Real qz0 qz312 (@Neg.neg Real Real.instNeg (Real.sin qz29))) Bool.false 314765674575 1099511627776 58212330081231 216972127067176960 Bool.false 271341929625 1099511627776 58190708874621 216972127067176960 (@Enclosure.Real.IsNear.mulLit_ff qz312 (Real.cos qz29) 396325 1048576 1 1048576 794211 1048576 146484471 206920744960 314765674575 1099511627776 58212330081231 216972127067176960 qz316 (@Enclosure.Real.IsNear.recentre' (Real.cos qz29) Bool.false 794211 1048576 146484471 206920744960 794211 1048576 146484471 206920744960 (ep139 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz312 (@Neg.neg Real Real.instNeg (Real.sin qz29)) 396325 1048576 1 1048576 684645 1048576 146484471 206920744960 271341929625 1099511627776 58190708874621 216972127067176960 qz316 (@Enclosure.Real.IsNear.neg (Real.sin qz29) Bool.true 684645 1048576 146484471 206920744960 (@Enclosure.Real.IsNear.recentre' (Real.sin qz29) Bool.true 684645 1048576 146484471 206920744960 684645 1048576 146484471 206920744960 (ep143 rfl rfl) rfl)) rfl)

noncomputable def ep145 := @ep41 314765674575 1099511627776 58212330081231 216972127067176960 Bool.false 271341929625 1099511627776 58190708874621 216972127067176960 Bool.true 20608290596375085711360 9371565555 549755813888 232071230491347 108486063533588480 Bool.true 578000469473595223965696 1051376729217 1099511627776 463957425281239 216972127067176960 (ep42 (BSN.head_sum_c_succ qz5 6 7 rfl rfl) (ep130 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep131 ep144) rfl rfl

noncomputable abbrev qz558 := (Real.log (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz30 := (@HMul.hMul Real Real Real qz269 qz279 qz558)

noncomputable abbrev qz317 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 8)))

noncomputable def ep146 := @Enclosure.Complex.IsNear.of_eq qz540 (Complex.mk (@HMul.hMul Real Real Real qz0 qz317 (Real.cos qz30)) (@HMul.hMul Real Real Real qz0 qz317 (@Neg.neg Real Real.instNeg (Real.sin qz30)))) Bool.false 186771150419 1099511627776 54405311745883 216972127067176960 Bool.false 340927593013 1099511627776 54487367980253 216972127067176960 (BSN.cpow_neg_s_mk qz12 138478 1000 8 qz13 rfl)

noncomputable abbrev qz318 := (Real.sqrt (@Nat.cast Real Real.instNatCast 8))

noncomputable abbrev qz319 := (@Nat.cast Real Real.instNatCast 8)

noncomputable abbrev qz559 := (@HDiv.hDiv Real Real Real qz1 qz319 qz14)

noncomputable def ep147 := @Enclosure.Real.IsNear.inv_image qz318 2965821 1048576 1 1048576 185363 185364 524288 (@Enclosure.Real.IsNear.of_eq qz318 (Real.sqrt qz559) Bool.false 2965821 1048576 1 1048576 (BSN.sqrt_natCast_div_one 8) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz559) Bool.false 2965821 1048576 1 1048576 2965821 1048576 1 1048576 (BSN.sqrt_enclosure 8 1 1482910 1482911 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep148 := BSN.log_dyadic_bound 0 16 1 0 1 524288 197335 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl

noncomputable def ep149 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz558 138478 1000 0 1 9364972152248037 4503599627370496 200000000118401 39467000000000000000 648421306849501833843 2251799813685248000 13847800008197966839 19733500000000000000000 qz18 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 200000000118401 39467000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz559) Bool.false 39279540158062550581248 18889465931478580854784 1000000000592005 197335000000000000000 9364972152248037 4503599627370496 200000000118401 39467000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 524288 24973259072661432 36028797018963968 197335 1000000000000000 rfl rfl rfl rfl (ep148 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep150 := nat_lit 1341794282863462248700823328548501776

noncomputable def ep151 := BSN.sin_dyadic_bound_f 1076270618 2147483648 2 1 1048576 395056 ep150 ep58 ep150 ep150 ep59 ep150 503797 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1076270618) qz15 0 1 ep150 ep58 ep150 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1076270618) qz16 0 1 ep150 ep59 ep150 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz31 := (@Nat.cast Real Real.instNatCast 262144)

noncomputable abbrev qz320 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 75486175) qz31)

noncomputable abbrev qz321 := (@Nat.cast Real Real.instNatCast 37778931862957161709568)

noncomputable def ep152 := @Enclosure.Real.IsNear.cos_image qz30 qz320 Bool.false 75486175 262144 737 1048576 Bool.false 503797 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz30 Bool.false 648421306849501833843 2251799813685248000 13847800008197966839 19733500000000000000000 75486175 262144 737 1048576 (ep149 rfl) rfl) (Enclosure.sfrac_false_div 75486175 262144) (BSN.cos_reduce3 qz320 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 18933952948064422461440) qz321) 226375608064910080 72057594037927936 Bool.false 503797 1048576 45 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q3 75486175 262144 226375608064910080 72057594037927936 45 18933952948064422461440 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 503797 1048576 18933952948064422461440 37778931862957161709568 1076270618 2147483648 395056 394670 (ep151 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep153 := BSN.cos_dyadic_bound_f 1076270618 2147483648 2 1 1048576 395056 ep150 ep62 ep150 ep150 ep63 ep150 919619 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1076270618) qz20 0 1 ep150 ep62 ep150 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1076270618) qz21 0 1 ep150 ep63 ep150 rfl rfl rfl rfl) rfl rfl

noncomputable def ep154 := @Enclosure.Real.IsNear.sin_image qz30 qz320 Bool.false 75486175 262144 737 1048576 Bool.true 919619 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz30 Bool.false 648421306849501833843 2251799813685248000 13847800008197966839 19733500000000000000000 75486175 262144 737 1048576 (ep149 rfl) rfl) (Enclosure.sfrac_false_div 75486175 262144) (BSN.sin_reduce3 qz320 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 18933952948064422461440) qz321) 226375608064910080 72057594037927936 Bool.false 919619 1048576 45 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q3 75486175 262144 226375608064910080 72057594037927936 45 18933952948064422461440 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 919619 1048576 18933952948064422461440 37778931862957161709568 1076270618 2147483648 395056 394670 (ep153 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz322 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 8))) Bool.false 370727 1048576 1 1048576 370727 1048576 1 1048576 (ep147 rfl rfl) rfl)

noncomputable def ep155 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz317 (Real.cos qz30)) (@HMul.hMul Real Real Real qz0 qz317 (@Neg.neg Real Real.instNeg (Real.sin qz30))) Bool.false 186771150419 1099511627776 54405311745883 216972127067176960 Bool.false 340927593013 1099511627776 54487367980253 216972127067176960 (@Enclosure.Real.IsNear.mulLit_ff qz317 (Real.cos qz30) 370727 1048576 1 1048576 503797 1048576 146484471 206920744960 186771150419 1099511627776 54405311745883 216972127067176960 qz322 (@Enclosure.Real.IsNear.recentre' (Real.cos qz30) Bool.false 503797 1048576 146484471 206920744960 503797 1048576 146484471 206920744960 (ep152 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz317 (@Neg.neg Real Real.instNeg (Real.sin qz30)) 370727 1048576 1 1048576 919619 1048576 146484471 206920744960 340927593013 1099511627776 54487367980253 216972127067176960 qz322 (@Enclosure.Real.IsNear.neg (Real.sin qz30) Bool.true 919619 1048576 146484471 206920744960 (@Enclosure.Real.IsNear.recentre' (Real.sin qz30) Bool.true 919619 1048576 146484471 206920744960 919619 1048576 146484471 206920744960 (ep154 rfl rfl) rfl)) rfl)

noncomputable def ep156 := @ep39 186771150419 1099511627776 54405311745883 216972127067176960 Bool.false 340927593013 1099511627776 54487367980253 216972127067176960 Bool.false 92374380511207874363392 168028019309 1099511627776 518547772728577 216972127067176960 Bool.true 781147086199713173602304 177612284051 274877906944 129611198315373 54243031766794240 (ep40 (BSN.head_sum_c_succ qz5 7 8 rfl rfl) (ep145 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep146 ep155) rfl rfl

theorem EMRow48.d6 : Enclosure.Complex.IsNear qz3 Bool.false 168028019309 1099511627776 518547772728577 216972127067176960 Bool.true 177612284051 274877906944 129611198315373 54243031766794240 := ep38 (BSN.head_sum_c_succ qz5 8 9 rfl rfl) (ep156 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz32 := (BSN.headSumC qz273 17)

noncomputable abbrev qz560 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 16) qz7)

noncomputable def ep157 := @Enclosure.Complex.IsNear.of_eq qz32 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 16) qz560) Bool.false 421317563 34359738368 217892540946157 54243031766794240 Bool.true 46481820595 1099511627776 871790707945983 216972127067176960

noncomputable def ep158 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 16) qz560 Bool.true 202272799133 1099511627776 833007723428399 216972127067176960 Bool.false 123832486505 1099511627776 833262474230659 216972127067176960 Bool.false

noncomputable abbrev qz561 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 15) qz7)

noncomputable def ep159 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 16) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 15) qz561) Bool.true 202272799133 1099511627776 833007723428399 216972127067176960 Bool.false 123832486505 1099511627776 833262474230659 216972127067176960

noncomputable def ep160 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 15) qz561 Bool.true 43878603811 549755813888 99158094724829 27121515883397120 Bool.true 135938629657 1099511627776 793413636202707 216972127067176960 Bool.true

noncomputable abbrev qz562 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 14) qz7)

noncomputable def ep161 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 15) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 14) qz562) Bool.true 43878603811 549755813888 99158094724829 27121515883397120 Bool.true 135938629657 1099511627776 793413636202707 216972127067176960

noncomputable def ep162 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 14) qz562 Bool.true 59985792193 274877906944 376053100467979 108486063533588480 Bool.false 28859765275 274877906944 376092616407059 108486063533588480 Bool.false

noncomputable abbrev qz563 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 13) qz7)

noncomputable def ep163 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 14) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 13) qz563) Bool.true 59985792193 274877906944 376053100467979 108486063533588480 Bool.false 28859765275 274877906944 376092616407059 108486063533588480

noncomputable def ep164 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 13) qz563 Bool.false 29792663455 549755813888 177325439778991 54243031766794240 Bool.false 58193170957 1099511627776 709545189401279 216972127067176960 Bool.true

noncomputable abbrev qz564 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 12) qz7)

noncomputable def ep165 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 13) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 12) qz564) Bool.false 29792663455 549755813888 177325439778991 54243031766794240 Bool.false 58193170957 1099511627776 709545189401279 216972127067176960

noncomputable def ep166 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 12) qz564 Bool.false 13889568469 549755813888 332470233770373 108486063533588480 Bool.true 64402425263 274877906944 332499376992513 108486063533588480 Bool.false

noncomputable abbrev qz565 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 11) qz7)

noncomputable def ep167 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 12) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 11) qz565) Bool.false 13889568469 549755813888 332470233770373 108486063533588480 Bool.true 64402425263 274877906944 332499376992513 108486063533588480

noncomputable def ep168 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 11) qz565 Bool.true 164192341933 1099511627776 618508407754323 216972127067176960 Bool.true 527885048741 1099511627776 618517819449813 216972127067176960 Bool.false

noncomputable abbrev qz566 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 10) qz7)

noncomputable def ep169 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 11) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 10) qz566) Bool.true 164192341933 1099511627776 618508407754323 216972127067176960 Bool.true 527885048741 1099511627776 618517819449813 216972127067176960

noncomputable def ep170 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 10) qz566 Bool.true 79592176633 549755813888 17810395052029 6780378970849280 Bool.true 218886293201 274877906944 284869067237739 108486063533588480 Bool.true

noncomputable abbrev qz567 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 9) qz7)

noncomputable def ep171 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 10) (@HAdd.hAdd Complex Complex Complex qz4 qz3 qz567) Bool.true 79592176633 549755813888 17810395052029 6780378970849280 Bool.true 218886293201 274877906944 284869067237739 108486063533588480

noncomputable def ep172 := @Enclosure.Complex.IsNear.addLitP qz3 qz567 Bool.false 168028019309 1099511627776 518547772728577 216972127067176960 Bool.true 177612284051 274877906944 129611198315373 54243031766794240 Bool.true

noncomputable abbrev qz568 := (Real.log (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz33 := (@HMul.hMul Real Real Real qz269 qz279 qz568)

noncomputable abbrev qz323 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 9)))

noncomputable def ep173 := @Enclosure.Complex.IsNear.of_eq qz567 (Complex.mk (@HMul.hMul Real Real Real qz0 qz323 (Real.cos qz33)) (@HMul.hMul Real Real Real qz0 qz323 (@Neg.neg Real Real.instNeg (Real.sin qz33)))) Bool.true 327212372575 1099511627776 51384868936351 216972127067176960 Bool.true 20637004575 137438953472 25646670606993 108486063533588480 (BSN.cpow_neg_s_mk qz12 138478 1000 9 qz13 rfl)

noncomputable abbrev qz324 := (Real.sqrt (@Nat.cast Real Real.instNatCast 9))

noncomputable abbrev qz325 := (@Nat.cast Real Real.instNatCast 9)

noncomputable abbrev qz569 := (@HDiv.hDiv Real Real Real qz1 qz325 qz14)

noncomputable def ep174 := @Enclosure.Real.IsNear.inv_image qz324 3145729 1048576 1 1048576 174762 174763 524288 (@Enclosure.Real.IsNear.of_eq qz324 (Real.sqrt qz569) Bool.false 3145729 1048576 1 1048576 (BSN.sqrt_natCast_div_one 9) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz569) Bool.false 3145729 1048576 1 1048576 3145729 1048576 1 1048576 (BSN.sqrt_enclosure 9 1 1572864 1572865 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep175 := BSN.log_dyadic_bound 1 17 3 2 1252815 524288 197335 1448 3 61752 18 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 1) (BSN.artanhQ 17) 0 2 1448 1252815 3 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep176 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz568 138478 1000 0 1 9895417793173221 4503599627370496 200000000118401 39467000000000000000 685148832581520648819 2251799813685248000 13847800008197966839 19733500000000000000000 qz18 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 200000000118401 39467000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz569) Bool.false 41504390431577613533184 18889465931478580854784 1000000000592005 197335000000000000000 9895417793173221 4503599627370496 200000000118401 39467000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 61752 524288 24973259072661432 36028797018963968 197335 1000000000000000 rfl rfl rfl rfl (ep175 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep177 := nat_lit 2029281399354671669204065944662386540736915816064226669025917628268516133109760

noncomputable def ep178 := nat_lit 994617788852217199126816910762094717481873167044238985159745308728743755776

noncomputable def ep179 := nat_lit 5313174283794569829593015008641207072387427914088236317663335153060552858730496

noncomputable def ep180 := BSN.sin_dyadic_bound_f 2369774532 2147483648 3 2 1048576 395056 ep177 ep79 ep178 ep179 ep81 ep178 936163 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2369774532) qz15 0 2 ep177 ep79 ep178 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2369774532) qz16 0 2 ep179 ep81 ep178 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz326 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 319047287) qz24)

noncomputable def ep181 := @Enclosure.Real.IsNear.cos_image qz33 qz326 Bool.false 319047287 1048576 737 1048576 Bool.true 936163 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz33 Bool.false 685148832581520648819 2251799813685248000 13847800008197966839 19733500000000000000000 319047287 1048576 737 1048576 (ep176 rfl) rfl) (Enclosure.sfrac_false_div 319047287 1048576) (BSN.cos_reduce1 qz326 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 166758057858233819725824) qz25) 226375608064910080 72057594037927936 Bool.false 936163 1048576 48 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q1 319047287 1048576 226375608064910080 72057594037927936 48 166758057858233819725824 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 936163 1048576 166758057858233819725824 151115727451828646838272 2369774532 2147483648 395056 394670 (ep180 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep182 := nat_lit 1127820607547640801646315221217220120283834063665478922341136346953055071174656

noncomputable def ep183 := nat_lit 3381472587065217970540692029830136171416538444662348289053089550241707726012416

noncomputable def ep184 := BSN.cos_dyadic_bound_f 2369774532 2147483648 3 2 1048576 395056 ep182 ep72 ep178 ep183 ep75 ep178 472344 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2369774532) qz20 0 2 ep182 ep72 ep178 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2369774532) qz21 0 2 ep183 ep75 ep178 rfl rfl rfl rfl) rfl rfl

noncomputable def ep185 := @Enclosure.Real.IsNear.sin_image qz33 qz326 Bool.false 319047287 1048576 737 1048576 Bool.false 472344 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz33 Bool.false 685148832581520648819 2251799813685248000 13847800008197966839 19733500000000000000000 319047287 1048576 737 1048576 (ep176 rfl) rfl) (Enclosure.sfrac_false_div 319047287 1048576) (BSN.sin_reduce1 qz326 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 166758057858233819725824) qz25) 226375608064910080 72057594037927936 Bool.false 472344 1048576 48 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q1 319047287 1048576 226375608064910080 72057594037927936 48 166758057858233819725824 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 472344 1048576 166758057858233819725824 151115727451828646838272 2369774532 2147483648 395056 394670 (ep184 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz327 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 9))) Bool.false 349525 1048576 1 1048576 349525 1048576 1 1048576 (ep174 rfl rfl) rfl)

noncomputable def ep186 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz323 (Real.cos qz33)) (@HMul.hMul Real Real Real qz0 qz323 (@Neg.neg Real Real.instNeg (Real.sin qz33))) Bool.true 327212372575 1099511627776 51384868936351 216972127067176960 Bool.true 20637004575 137438953472 25646670606993 108486063533588480 (@Enclosure.Real.IsNear.mulLit_ft qz323 (Real.cos qz33) 349525 1048576 1 1048576 936163 1048576 146484471 206920744960 327212372575 1099511627776 51384868936351 216972127067176960 qz327 (@Enclosure.Real.IsNear.recentre' (Real.cos qz33) Bool.true 936163 1048576 146484471 206920744960 936163 1048576 146484471 206920744960 (ep181 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz323 (@Neg.neg Real Real.instNeg (Real.sin qz33)) 349525 1048576 1 1048576 59043 131072 146484471 206920744960 20637004575 137438953472 25646670606993 108486063533588480 qz327 (@Enclosure.Real.IsNear.neg (Real.sin qz33) Bool.false 59043 131072 146484471 206920744960 (@Enclosure.Real.IsNear.recentre' (Real.sin qz33) Bool.false 472344 1048576 146484471 206920744960 59043 131072 146484471 206920744960 (ep185 rfl rfl) rfl)) rfl)

noncomputable def ep187 := @ep172 327212372575 1099511627776 51384868936351 216972127067176960 Bool.true 20637004575 137438953472 25646670606993 108486063533588480 Bool.true 175025047375969481916416 79592176633 549755813888 17810395052029 6780378970849280 Bool.true 30083503066910788943872 218886293201 274877906944 284869067237739 108486063533588480 EMRow48.d6 (ep173 ep186) rfl rfl

noncomputable abbrev qz570 := (@Nat.cast Real Real.instNatCast 10)

noncomputable abbrev qz34 := (@Inv.inv Real Real.instInv (Real.sqrt qz570))

noncomputable abbrev qz571 := (Real.log (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz35 := (@HMul.hMul Real Real Real qz269 qz279 qz571)

noncomputable def ep188 := @Enclosure.Complex.IsNear.of_eq qz566 (Complex.mk (@HMul.hMul Real Real Real qz0 qz34 (Real.cos qz35)) (@HMul.hMul Real Real Real qz0 qz34 (@Neg.neg Real Real.instNeg (Real.sin qz35)))) Bool.true 5007988667 1099511627776 9715153217879 43394425413435392 Bool.false 347660124063 1099511627776 9755936994867 43394425413435392 (BSN.cpow_neg_s_mk qz12 138478 1000 10 qz13 rfl)

noncomputable abbrev qz572 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 10) qz14)

noncomputable def ep189 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz570) 3315889 1048576 1 1048576 165794 165795 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz570) (Real.sqrt qz572) Bool.false 3315889 1048576 1 1048576 (BSN.sqrt_natCast_div_one 10) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz572) Bool.false 3315889 1048576 1 1048576 3315889 1048576 1 1048576 (BSN.sqrt_enclosure 10 1 1657944 1657945 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep190 := BSN.log_dyadic_bound 2 18 3 2 1574640 524288 197335 6528 48 116991 20 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 2) (BSN.artanhQ 18) 0 2 6528 1574640 48 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep191 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz571 138478 1000 0 1 10369917190100709 4503599627370496 200000000118401 39467000000000000000 718002696325382990451 2251799813685248000 13847800008197966839 19733500000000000000000 qz18 (BSN.isNear_log_sfrac 10 1 10369917190100709 4503599627370496 200000000118401 39467000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz572) Bool.false 43494585150108164161536 18889465931478580854784 1000000000592005 197335000000000000000 10369917190100709 4503599627370496 200000000118401 39467000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 116991 524288 24973259072661432 36028797018963968 197335 1000000000000000 rfl rfl rfl rfl (ep190 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep192 := nat_lit 4474428356779040574864732354153977835657540867142046050113871295046891600755841

noncomputable def ep193 := nat_lit 15573605258253152388774709699413632268018948831754151159511442859062952082561

noncomputable def ep194 := nat_lit 13392137859820615419816647643063106242436584703762629848022590999422548898102401

noncomputable def ep195 := BSN.cos_dyadic_bound_f 3342324753 2147483648 3 2 1048576 395056 ep192 ep72 ep193 ep194 ep75 ep193 15103 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3342324753) qz20 0 2 ep192 ep72 ep193 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3342324753) qz21 0 2 ep194 ep75 ep193 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz328 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 334346059) qz24)

noncomputable def ep196 := @Enclosure.Real.IsNear.cos_image qz35 qz328 Bool.false 334346059 1048576 737 1048576 Bool.true 15103 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz35 Bool.false 718002696325382990451 2251799813685248000 13847800008197966839 19733500000000000000000 334346059 1048576 737 1048576 (ep191 rfl) rfl) (Enclosure.sfrac_false_div 334346059 1048576) (BSN.cos_reduce2 qz328 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 235195195547431141900288) qz25) 226375608064910080 72057594037927936 Bool.false 15103 1048576 50 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q2 334346059 1048576 226375608064910080 72057594037927936 50 235195195547431141900288 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 15103 1048576 235195195547431141900288 151115727451828646838272 3342324753 2147483648 395056 394670 (ep195 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep197 := nat_lit 8041512157995670512845498469717629198369158401790279569277359176797154519694465

noncomputable def ep198 := nat_lit 21035888862427679572632575033556644876818622278008844531944350746030255152970881

noncomputable def ep199 := BSN.sin_dyadic_bound_f 3342324753 2147483648 3 2 1048576 395056 ep197 ep79 ep193 ep198 ep81 ep193 1048467 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3342324753) qz15 0 2 ep197 ep79 ep193 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3342324753) qz16 0 2 ep198 ep81 ep193 rfl rfl rfl rfl) rfl rfl

noncomputable def ep200 := @Enclosure.Real.IsNear.sin_image qz35 qz328 Bool.false 334346059 1048576 737 1048576 Bool.true 1048467 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz35 Bool.false 718002696325382990451 2251799813685248000 13847800008197966839 19733500000000000000000 334346059 1048576 737 1048576 (ep191 rfl) rfl) (Enclosure.sfrac_false_div 334346059 1048576) (BSN.sin_reduce2 qz328 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 235195195547431141900288) qz25) 226375608064910080 72057594037927936 Bool.false 1048467 1048576 50 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q2 334346059 1048576 226375608064910080 72057594037927936 50 235195195547431141900288 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1048467 1048576 235195195547431141900288 151115727451828646838272 3342324753 2147483648 395056 394670 (ep199 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz329 := (@Enclosure.Real.IsNear.recentre' qz34 Bool.false 331589 1048576 1 1048576 331589 1048576 1 1048576 (ep189 rfl rfl) rfl)

noncomputable def ep201 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz34 (Real.cos qz35)) (@HMul.hMul Real Real Real qz0 qz34 (@Neg.neg Real Real.instNeg (Real.sin qz35))) Bool.true 5007988667 1099511627776 9715153217879 43394425413435392 Bool.false 347660124063 1099511627776 9755936994867 43394425413435392 (@Enclosure.Real.IsNear.mulLit_ft qz34 (Real.cos qz35) 331589 1048576 1 1048576 15103 1048576 146484471 206920744960 5007988667 1099511627776 9715153217879 43394425413435392 qz329 (@Enclosure.Real.IsNear.recentre' (Real.cos qz35) Bool.true 15103 1048576 146484471 206920744960 15103 1048576 146484471 206920744960 (ep196 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz34 (@Neg.neg Real Real.instNeg (Real.sin qz35)) 331589 1048576 1 1048576 1048467 1048576 146484471 206920744960 347660124063 1099511627776 9755936994867 43394425413435392 qz329 (@Enclosure.Real.IsNear.neg (Real.sin qz35) Bool.true 1048467 1048576 146484471 206920744960 (@Enclosure.Real.IsNear.recentre' (Real.sin qz35) Bool.true 1048467 1048576 146484471 206920744960 1048467 1048576 146484471 206920744960 (ep200 rfl rfl) rfl)) rfl)

noncomputable def ep202 := @ep170 5007988667 1099511627776 9715153217879 43394425413435392 Bool.false 347660124063 1099511627776 9755936994867 43394425413435392 Bool.true 90265694573553206165504 164192341933 1099511627776 618508407754323 216972127067176960 Bool.true 145103937304957502357504 527885048741 1099511627776 618517819449813 216972127067176960 (ep171 (BSN.head_sum_c_succ qz5 9 10 rfl rfl) (ep187 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep188 ep201) rfl rfl

noncomputable abbrev qz573 := (@Nat.cast Real Real.instNatCast 11)

noncomputable abbrev qz36 := (@Inv.inv Real Real.instInv (Real.sqrt qz573))

noncomputable abbrev qz574 := (Real.log (Enclosure.sfrac Bool.false 11 1))

noncomputable abbrev qz37 := (@HMul.hMul Real Real Real qz269 qz279 qz574)

noncomputable def ep203 := @Enclosure.Complex.IsNear.of_eq qz565 (Complex.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz37)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz37)))) Bool.false 191971478871 1099511627776 46432059786423 216972127067176960 Bool.false 270275347689 1099511627776 46480934535213 216972127067176960 (BSN.cpow_neg_s_mk qz12 138478 1000 11 qz13 rfl)

noncomputable abbrev qz575 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11) qz14)

noncomputable def ep204 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz573) 3477733 1048576 1 1048576 158078 158079 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz573) (Real.sqrt qz575) Bool.false 3477733 1048576 1 1048576 (BSN.sqrt_natCast_div_one 11) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz575) Bool.false 3477733 1048576 1 1048576 3477733 1048576 1 1048576 (BSN.sqrt_enclosure 11 1 1738866 1738867 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep205 := BSN.log_dyadic_bound 3 19 4 3 4939817505 524288 197335 41676111 10935 166961 22 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 3) (BSN.artanhQ 19) 0 3 41676111 4939817505 10935 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep206 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz574 138478 1000 0 1 10799156221662949 4503599627370496 200000000118401 39467000000000000000 747722777631720925811 2251799813685248000 13847800008197966839 19733500000000000000000 qz18 (BSN.isNear_log_sfrac 11 1 10799156221662949 4503599627370496 200000000118401 39467000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz575) Bool.false 45294944137145793642496 18889465931478580854784 1000000000592005 197335000000000000000 10799156221662949 4503599627370496 200000000118401 39467000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 166961 524288 24973259072661432 36028797018963968 197335 1000000000000000 rfl rfl rfl rfl (ep205 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep207 := nat_lit 3094048904723950910574855563701048336

noncomputable def ep208 := BSN.sin_dyadic_bound_f 1326269534 2147483648 2 1 1048576 395056 ep207 ep58 ep207 ep207 ep59 ep207 607203 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1326269534) qz15 0 1 ep207 ep58 ep207 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1326269534) qz16 0 1 ep207 ep59 ep207 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz330 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 348185551) qz24)

noncomputable def ep209 := @Enclosure.Real.IsNear.cos_image qz37 qz330 Bool.false 348185551 1048576 737 1048576 Bool.false 607203 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz37 Bool.false 747722777631720925811 2251799813685248000 13847800008197966839 19733500000000000000000 348185551 1048576 737 1048576 (ep206 rfl) rfl) (Enclosure.sfrac_false_div 348185551 1048576) (BSN.cos_reduce3 qz330 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 93327921581293507182592) qz25) 226375608064910080 72057594037927936 Bool.false 607203 1048576 52 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q3 348185551 1048576 226375608064910080 72057594037927936 52 93327921581293507182592 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 607203 1048576 93327921581293507182592 151115727451828646838272 1326269534 2147483648 395056 394670 (ep208 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep210 := BSN.cos_dyadic_bound_f 1326269534 2147483648 2 1 1048576 395056 ep207 ep62 ep207 ep207 ep63 ep207 854877 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1326269534) qz20 0 1 ep207 ep62 ep207 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1326269534) qz21 0 1 ep207 ep63 ep207 rfl rfl rfl rfl) rfl rfl

noncomputable def ep211 := @Enclosure.Real.IsNear.sin_image qz37 qz330 Bool.false 348185551 1048576 737 1048576 Bool.true 854877 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz37 Bool.false 747722777631720925811 2251799813685248000 13847800008197966839 19733500000000000000000 348185551 1048576 737 1048576 (ep206 rfl) rfl) (Enclosure.sfrac_false_div 348185551 1048576) (BSN.sin_reduce3 qz330 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 93327921581293507182592) qz25) 226375608064910080 72057594037927936 Bool.false 854877 1048576 52 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q3 348185551 1048576 226375608064910080 72057594037927936 52 93327921581293507182592 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 854877 1048576 93327921581293507182592 151115727451828646838272 1326269534 2147483648 395056 394670 (ep210 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz331 := (@Enclosure.Real.IsNear.recentre' qz36 Bool.false 316157 1048576 1 1048576 316157 1048576 1 1048576 (ep204 rfl rfl) rfl)

noncomputable def ep212 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz37)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz37))) Bool.false 191971478871 1099511627776 46432059786423 216972127067176960 Bool.false 270275347689 1099511627776 46480934535213 216972127067176960 (@Enclosure.Real.IsNear.mulLit_ff qz36 (Real.cos qz37) 316157 1048576 1 1048576 607203 1048576 146484471 206920744960 191971478871 1099511627776 46432059786423 216972127067176960 qz331 (@Enclosure.Real.IsNear.recentre' (Real.cos qz37) Bool.false 607203 1048576 146484471 206920744960 607203 1048576 146484471 206920744960 (ep209 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz36 (@Neg.neg Real Real.instNeg (Real.sin qz37)) 316157 1048576 1 1048576 854877 1048576 146484471 206920744960 270275347689 1099511627776 46480934535213 216972127067176960 qz331 (@Enclosure.Real.IsNear.neg (Real.sin qz37) Bool.true 854877 1048576 146484471 206920744960 (@Enclosure.Real.IsNear.recentre' (Real.sin qz37) Bool.true 854877 1048576 146484471 206920744960 854877 1048576 146484471 206920744960 (ep211 rfl rfl) rfl)) rfl)

noncomputable def ep213 := @ep168 191971478871 1099511627776 46432059786423 216972127067176960 Bool.false 270275347689 1099511627776 46480934535213 216972127067176960 Bool.false 30543484072912788389888 13889568469 549755813888 332470233770373 108486063533588480 Bool.true 283244861734573259620352 64402425263 274877906944 332499376992513 108486063533588480 (ep169 (BSN.head_sum_c_succ qz5 10 11 rfl rfl) (ep202 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep203 ep212) rfl rfl

noncomputable abbrev qz576 := (@Nat.cast Real Real.instNatCast 12)

noncomputable abbrev qz38 := (@Inv.inv Real Real.instInv (Real.sqrt qz576))

noncomputable abbrev qz577 := (Real.log (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz39 := (@HMul.hMul Real Real Real qz269 qz279 qz577)

noncomputable def ep214 := @Enclosure.Complex.IsNear.of_eq qz564 (Complex.mk (@HMul.hMul Real Real Real qz0 qz38 (Real.cos qz39)) (@HMul.hMul Real Real Real qz0 qz38 (@Neg.neg Real Real.instNeg (Real.sin qz39)))) Bool.false 7951547493 274877906944 22180645787609 108486063533588480 Bool.false 315802872009 1099511627776 44546435416253 216972127067176960 (BSN.cpow_neg_s_mk qz12 138478 1000 12 qz13 rfl)

noncomputable abbrev qz578 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 12) qz14)

noncomputable def ep215 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz576) 3632373 1048576 1 1048576 151348 151349 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz576) (Real.sqrt qz578) Bool.false 3632373 1048576 1 1048576 (BSN.sqrt_natCast_div_one 12) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz578) Bool.false 3632373 1048576 1 1048576 3632373 1048576 1 1048576 (BSN.sqrt_enclosure 12 1 1816186 1816187 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep216 := BSN.log_dyadic_bound 4 20 4 3 6720000000 524288 197335 91811840 61440 212580 24 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 4) (BSN.artanhQ 20) 0 3 91811840 6720000000 61440 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep217 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz577 138478 1000 0 1 11191020447815397 4503599627370496 200000000118401 39467000000000000000 774855064786290272883 2251799813685248000 13847800008197966839 19733500000000000000000 qz18 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 200000000118401 39467000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz578) Bool.false 46938541828353910898688 18889465931478580854784 1000000000592005 197335000000000000000 11191020447815397 4503599627370496 200000000118401 39467000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 212580 524288 24973259072661432 36028797018963968 197335 1000000000000000 rfl rfl rfl rfl (ep216 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep218 := BSN.sin_dyadic_bound_f 215557965 2147483648 1 0 1048576 395056 0 1 1 0 1 1 105076 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 215557965) qz15 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 215557965) qz16 0 0 rfl) rfl rfl

noncomputable abbrev qz332 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 180410003) qz17)

noncomputable def ep219 := @Enclosure.Real.IsNear.cos_image qz39 qz332 Bool.false 180410003 524288 737 1048576 Bool.false 105076 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz39 Bool.false 774855064786290272883 2251799813685248000 13847800008197966839 19733500000000000000000 180410003 524288 737 1048576 (ep217 rfl) rfl) (Enclosure.sfrac_false_div 180410003 524288) (BSN.cos_reduce3 qz332 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 7584271662030946041856) qz19) 226375608064910080 72057594037927936 Bool.false 105076 1048576 54 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q3 180410003 524288 226375608064910080 72057594037927936 54 7584271662030946041856 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 105076 1048576 7584271662030946041856 75557863725914323419136 215557965 2147483648 395056 394670 (ep218 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep220 := nat_lit 2159018182086113887100877204500625

noncomputable def ep221 := BSN.cos_dyadic_bound_f 215557965 2147483648 2 1 1048576 395056 ep220 ep62 ep220 ep220 ep63 ep220 1043297 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 215557965) qz20 0 1 ep220 ep62 ep220 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 215557965) qz21 0 1 ep220 ep63 ep220 rfl rfl rfl rfl) rfl rfl

noncomputable def ep222 := @Enclosure.Real.IsNear.sin_image qz39 qz332 Bool.false 180410003 524288 737 1048576 Bool.true 1043297 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz39 Bool.false 774855064786290272883 2251799813685248000 13847800008197966839 19733500000000000000000 180410003 524288 737 1048576 (ep217 rfl) rfl) (Enclosure.sfrac_false_div 180410003 524288) (BSN.sin_reduce3 qz332 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 7584271662030946041856) qz19) 226375608064910080 72057594037927936 Bool.false 1043297 1048576 54 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q3 180410003 524288 226375608064910080 72057594037927936 54 7584271662030946041856 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1043297 1048576 7584271662030946041856 75557863725914323419136 215557965 2147483648 395056 394670 (ep221 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz333 := (@Enclosure.Real.IsNear.recentre' qz38 Bool.false 302697 1048576 1 1048576 302697 1048576 1 1048576 (ep215 rfl rfl) rfl)

noncomputable def ep223 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz38 (Real.cos qz39)) (@HMul.hMul Real Real Real qz0 qz38 (@Neg.neg Real Real.instNeg (Real.sin qz39))) Bool.false 7951547493 274877906944 22180645787609 108486063533588480 Bool.false 315802872009 1099511627776 44546435416253 216972127067176960 (@Enclosure.Real.IsNear.mulLit_ff qz38 (Real.cos qz39) 302697 1048576 1 1048576 26269 262144 146484471 206920744960 7951547493 274877906944 22180645787609 108486063533588480 qz333 (@Enclosure.Real.IsNear.recentre' (Real.cos qz39) Bool.false 105076 1048576 146484471 206920744960 26269 262144 146484471 206920744960 (ep219 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz38 (@Neg.neg Real Real.instNeg (Real.sin qz39)) 302697 1048576 1 1048576 1043297 1048576 146484471 206920744960 315802872009 1099511627776 44546435416253 216972127067176960 qz333 (@Enclosure.Real.IsNear.neg (Real.sin qz39) Bool.true 1043297 1048576 146484471 206920744960 (@Enclosure.Real.IsNear.recentre' (Real.sin qz39) Bool.true 1043297 1048576 146484471 206920744960 1043297 1048576 146484471 206920744960 (ep222 rfl rfl) rfl)) rfl)

noncomputable def ep224 := @ep166 7951547493 274877906944 22180645787609 108486063533588480 Bool.false 315802872009 1099511627776 44546435416253 216972127067176960 Bool.false 8189344972797399531520 29792663455 549755813888 177325439778991 54243031766794240 Bool.false 15996017031094529425408 58193170957 1099511627776 709545189401279 216972127067176960 (ep167 (BSN.head_sum_c_succ qz5 11 12 rfl rfl) (ep213 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep214 ep223) rfl rfl

noncomputable abbrev qz579 := (@Nat.cast Real Real.instNatCast 13)

noncomputable abbrev qz40 := (@Inv.inv Real Real.instInv (Real.sqrt qz579))

noncomputable abbrev qz580 := (Real.log (Enclosure.sfrac Bool.false 13 1))

noncomputable abbrev qz41 := (@HMul.hMul Real Real Real qz269 qz279 qz580)

noncomputable def ep225 := @Enclosure.Complex.IsNear.of_eq qz563 (Complex.mk (@HMul.hMul Real Real Real qz0 qz40 (Real.cos qz41)) (@HMul.hMul Real Real Real qz0 qz40 (@Neg.neg Real Real.instNeg (Real.sin qz41)))) Bool.true 149764247841 549755813888 21402220909997 108486063533588480 Bool.false 57245890143 1099511627776 42640043412839 216972127067176960 (BSN.cpow_neg_s_mk qz12 138478 1000 13 qz13 rfl)

noncomputable abbrev qz581 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13) qz14)

noncomputable def ep226 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz579) 3780695 1048576 1 1048576 145411 145412 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz579) (Real.sqrt qz581) Bool.false 3780695 1048576 1 1048576 (BSN.sqrt_natCast_div_one 13) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz581) Bool.false 3780695 1048576 1 1048576 3780695 1048576 1 1048576 (BSN.sqrt_enclosure 13 1 1890347 1890348 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep227 := BSN.log_dyadic_bound 5 21 5 4 35742602096145 524288 197335 699352521000 41015625 254545 26 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 5) (BSN.artanhQ 21) 0 4 699352521000 35742602096145 41015625 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep228 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz580 138478 1000 0 1 11551497052968677 4503599627370496 200000000118401 39467000000000000000 799814104450498226803 2251799813685248000 13847800008197966839 19733500000000000000000 qz18 (BSN.isNear_log_sfrac 13 1 11551497052968677 4503599627370496 200000000118401 39467000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz581) Bool.false 48450490295254733815808 18889465931478580854784 1000000000592005 197335000000000000000 11551497052968677 4503599627370496 200000000118401 39467000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 254545 524288 24973259072661432 36028797018963968 197335 1000000000000000 rfl rfl rfl rfl (ep227 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep229 := nat_lit 27047447097596321965486949329126416

noncomputable def ep230 := BSN.cos_dyadic_bound_f 405538014 2147483648 2 1 1048576 395056 ep229 ep62 ep229 ep229 ep63 ep229 1029934 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 405538014) qz20 0 1 ep229 ep62 ep229 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 405538014) qz21 0 1 ep229 ep63 ep229 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz334 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 372442465) qz24)

noncomputable def ep231 := @Enclosure.Real.IsNear.cos_image qz41 qz334 Bool.false 372442465 1048576 737 1048576 Bool.true 1029934 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz41 Bool.false 799814104450498226803 2251799813685248000 13847800008197966839 19733500000000000000000 372442465 1048576 737 1048576 (ep228 rfl) rfl) (Enclosure.sfrac_false_div 372442465 1048576) (BSN.cos_reduce2 qz334 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 28537200797087589990400) qz25) 226375608064910080 72057594037927936 Bool.false 1029934 1048576 56 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q2 372442465 1048576 226375608064910080 72057594037927936 56 28537200797087589990400 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1029934 1048576 28537200797087589990400 151115727451828646838272 405538014 2147483648 395056 394670 (ep230 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep232 := BSN.sin_dyadic_bound_f 405538014 2147483648 2 1 1048576 395056 ep229 ep58 ep229 ep229 ep59 ep229 196841 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 405538014) qz15 0 1 ep229 ep58 ep229 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 405538014) qz16 0 1 ep229 ep59 ep229 rfl rfl rfl rfl) rfl rfl

noncomputable def ep233 := @Enclosure.Real.IsNear.sin_image qz41 qz334 Bool.false 372442465 1048576 737 1048576 Bool.true 196841 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz41 Bool.false 799814104450498226803 2251799813685248000 13847800008197966839 19733500000000000000000 372442465 1048576 737 1048576 (ep228 rfl) rfl) (Enclosure.sfrac_false_div 372442465 1048576) (BSN.sin_reduce2 qz334 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 28537200797087589990400) qz25) 226375608064910080 72057594037927936 Bool.false 196841 1048576 56 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q2 372442465 1048576 226375608064910080 72057594037927936 56 28537200797087589990400 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 196841 1048576 28537200797087589990400 151115727451828646838272 405538014 2147483648 395056 394670 (ep232 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz335 := (@Enclosure.Real.IsNear.recentre' qz40 Bool.false 290823 1048576 1 1048576 290823 1048576 1 1048576 (ep226 rfl rfl) rfl)

noncomputable def ep234 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz40 (Real.cos qz41)) (@HMul.hMul Real Real Real qz0 qz40 (@Neg.neg Real Real.instNeg (Real.sin qz41))) Bool.true 149764247841 549755813888 21402220909997 108486063533588480 Bool.false 57245890143 1099511627776 42640043412839 216972127067176960 (@Enclosure.Real.IsNear.mulLit_ft qz40 (Real.cos qz41) 290823 1048576 1 1048576 514967 524288 146484471 206920744960 149764247841 549755813888 21402220909997 108486063533588480 qz335 (@Enclosure.Real.IsNear.recentre' (Real.cos qz41) Bool.true 1029934 1048576 146484471 206920744960 514967 524288 146484471 206920744960 (ep231 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz40 (@Neg.neg Real Real.instNeg (Real.sin qz41)) 290823 1048576 1 1048576 196841 1048576 146484471 206920744960 57245890143 1099511627776 42640043412839 216972127067176960 qz335 (@Enclosure.Real.IsNear.neg (Real.sin qz41) Bool.true 196841 1048576 146484471 206920744960 (@Enclosure.Real.IsNear.recentre' (Real.sin qz41) Bool.true 196841 1048576 146484471 206920744960 196841 1048576 146484471 206920744960 (ep233 rfl rfl) rfl)) rfl)

noncomputable def ep235 := @ep164 149764247841 549755813888 21402220909997 108486063533588480 Bool.false 57245890143 1099511627776 42640043412839 216972127067176960 Bool.true 65955076017558302752768 59985792193 274877906944 376053100467979 108486063533588480 Bool.false 126926589978994121113600 28859765275 274877906944 376092616407059 108486063533588480 (ep165 (BSN.head_sum_c_succ qz5 12 13 rfl rfl) (ep224 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep225 ep234) rfl rfl

noncomputable abbrev qz582 := (@Nat.cast Real Real.instNatCast 14)

noncomputable abbrev qz42 := (@Inv.inv Real Real.instInv (Real.sqrt qz582))

noncomputable abbrev qz583 := (Real.log (Enclosure.sfrac Bool.false 14 1))

noncomputable abbrev qz43 := (@HMul.hMul Real Real Real qz269 qz279 qz583)

noncomputable def ep236 := @Enclosure.Complex.IsNear.of_eq qz562 (Complex.mk (@HMul.hMul Real Real Real qz0 qz42 (Real.cos qz43)) (@HMul.hMul Real Real Real qz0 qz42 (@Neg.neg Real Real.instNeg (Real.sin qz43)))) Bool.false 76092980575 549755813888 20579278431337 108486063533588480 Bool.true 251377690757 1099511627776 41228403388589 216972127067176960 (BSN.cpow_neg_s_mk qz12 138478 1000 14 qz13 rfl)

noncomputable abbrev qz584 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14) qz14)

noncomputable def ep237 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz582) 3923413 1048576 1 1048576 140121 140122 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz582) (Real.sqrt qz584) Bool.false 3923413 1048576 1 1048576 (BSN.sqrt_natCast_div_one 14) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz584) Bool.false 3923413 1048576 1 1048576 3923413 1048576 1 1048576 (BSN.sqrt_enclosure 14 1 1961706 1961707 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep238 := BSN.log_dyadic_bound 6 22 5 4 51857700491520 524288 197335 1346332575744 176359680 293399 28 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 6) (BSN.artanhQ 22) 0 4 1346332575744 51857700491520 176359680 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep239 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz583 138478 1000 0 1 11885250371606245 4503599627370496 200000000118401 39467000000000000000 164584570095928959511 450359962737049600 13847800008197966839 19733500000000000000000 qz18 (BSN.isNear_log_sfrac 14 1 11885250371606245 4503599627370496 200000000118401 39467000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz584) Bool.false 49850353174629559828480 18889465931478580854784 1000000000592005 197335000000000000000 11885250371606245 4503599627370496 200000000118401 39467000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 293399 524288 24973259072661432 36028797018963968 197335 1000000000000000 rfl rfl rfl rfl (ep238 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep240 := nat_lit 843952706734408117825547094423239563323188968397474158830198517874491223852161

noncomputable def ep241 := nat_lit 557192273786622107584406250772126337599978211807709067791408693016536958081

noncomputable def ep242 := nat_lit 2530743735655651109261472470768174437294366948768807058355012736237440597640321

noncomputable def ep243 := BSN.cos_dyadic_bound_f 2204198161 2147483648 3 2 1048576 395056 ep240 ep72 ep241 ep242 ep75 ep241 543050 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2204198161) qz20 0 2 ep240 ep72 ep241 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2204198161) qz21 0 2 ep242 ep75 ep241 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz336 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 383203313) qz24)

noncomputable def ep244 := @Enclosure.Real.IsNear.cos_image qz43 qz336 Bool.false 383203313 1048576 737 1048576 Bool.false 543050 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz43 Bool.false 164584570095928959511 450359962737049600 13847800008197966839 19733500000000000000000 383203313 1048576 737 1048576 (ep239 rfl) rfl) (Enclosure.sfrac_false_div 383203313 1048576) (BSN.cos_reduce0 qz336 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 155106656559158186213376) qz25) 226375608064910080 72057594037927936 Bool.false 543050 1048576 58 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q0 383203313 1048576 226375608064910080 72057594037927936 58 155106656559158186213376 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 543050 1048576 155106656559158186213376 151115727451828646838272 2204198161 2147483648 395056 394670 (ep243 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep245 := nat_lit 1518669118302905314399917244961213512911660160546007318640124205219670973367425

noncomputable def ep246 := nat_lit 3976564617588145101920837079063832900698233789087092400804853494834254346601601

noncomputable def ep247 := BSN.sin_dyadic_bound_f 2204198161 2147483648 3 2 1048576 395056 ep245 ep79 ep241 ep246 ep81 ep241 896999 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2204198161) qz15 0 2 ep245 ep79 ep241 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2204198161) qz16 0 2 ep246 ep81 ep241 rfl rfl rfl rfl) rfl rfl

noncomputable def ep248 := @Enclosure.Real.IsNear.sin_image qz43 qz336 Bool.false 383203313 1048576 737 1048576 Bool.false 896999 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz43 Bool.false 164584570095928959511 450359962737049600 13847800008197966839 19733500000000000000000 383203313 1048576 737 1048576 (ep239 rfl) rfl) (Enclosure.sfrac_false_div 383203313 1048576) (BSN.sin_reduce0 qz336 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 155106656559158186213376) qz25) 226375608064910080 72057594037927936 Bool.false 896999 1048576 58 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q0 383203313 1048576 226375608064910080 72057594037927936 58 155106656559158186213376 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 896999 1048576 155106656559158186213376 151115727451828646838272 2204198161 2147483648 395056 394670 (ep247 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz337 := (@Enclosure.Real.IsNear.recentre' qz42 Bool.false 280243 1048576 1 1048576 280243 1048576 1 1048576 (ep237 rfl rfl) rfl)

noncomputable def ep249 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz42 (Real.cos qz43)) (@HMul.hMul Real Real Real qz0 qz42 (@Neg.neg Real Real.instNeg (Real.sin qz43))) Bool.false 76092980575 549755813888 20579278431337 108486063533588480 Bool.true 251377690757 1099511627776 41228403388589 216972127067176960 (@Enclosure.Real.IsNear.mulLit_ff qz42 (Real.cos qz43) 280243 1048576 1 1048576 271525 524288 146484471 206920744960 76092980575 549755813888 20579278431337 108486063533588480 qz337 (@Enclosure.Real.IsNear.recentre' (Real.cos qz43) Bool.false 543050 1048576 146484471 206920744960 271525 524288 146484471 206920744960 (ep244 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz42 (@Neg.neg Real Real.instNeg (Real.sin qz43)) 280243 1048576 1 1048576 896999 1048576 146484471 206920744960 251377690757 1099511627776 41228403388589 216972127067176960 qz337 (@Enclosure.Real.IsNear.neg (Real.sin qz43) Bool.false 896999 1048576 146484471 206920744960 (@Enclosure.Real.IsNear.recentre' (Real.sin qz43) Bool.false 896999 1048576 146484471 206920744960 896999 1048576 146484471 206920744960 (ep248 rfl rfl) rfl)) rfl)

noncomputable def ep250 := @ep162 76092980575 549755813888 20579278431337 108486063533588480 Bool.true 251377690757 1099511627776 41228403388589 216972127067176960 Bool.true 12061258775192701763584 43878603811 549755813888 99158094724829 27121515883397120 Bool.true 37366525992951724638208 135938629657 1099511627776 793413636202707 216972127067176960 (ep163 (BSN.head_sum_c_succ qz5 13 14 rfl rfl) (ep235 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep236 ep249) rfl rfl

noncomputable abbrev qz585 := (@Nat.cast Real Real.instNatCast 15)

noncomputable abbrev qz44 := (@Inv.inv Real Real.instInv (Real.sqrt qz585))

noncomputable abbrev qz586 := (Real.log (Enclosure.sfrac Bool.false 15 1))

noncomputable abbrev qz45 := (@HMul.hMul Real Real Real qz269 qz279 qz586)

noncomputable def ep251 := @Enclosure.Complex.IsNear.of_eq qz561 (Complex.mk (@HMul.hMul Real Real Real qz0 qz44 (Real.cos qz45)) (@HMul.hMul Real Real Real qz0 qz44 (@Neg.neg Real Real.instNeg (Real.sin qz45)))) Bool.true 114515591511 1099511627776 39742965629767 216972127067176960 Bool.false 129885558081 549755813888 2490552376747 13560757941698560 (BSN.cpow_neg_s_mk qz12 138478 1000 15 qz13 rfl)

noncomputable abbrev qz587 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 15) qz14)

noncomputable def ep252 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz585) 4061117 1048576 1 1048576 135370 135371 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz585) (Real.sqrt qz587) Bool.false 4061117 1048576 1 1048576 (BSN.sqrt_natCast_div_one 15) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz587) Bool.false 4061117 1048576 1 1048576 4061117 1048576 1 1048576 (BSN.sqrt_enclosure 15 1 2030558 2030559 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep253 := BSN.log_dyadic_bound 7 23 6 5 430628584065881355 524288 197335 14087658153505881 266939110305 329571 30 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 7) (BSN.artanhQ 23) 0 5 14087658153505881 430628584065881355 266939110305 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep254 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz586 138478 1000 0 1 12195965485668069 4503599627370496 200000000118401 39467000000000000000 844436454262171429491 2251799813685248000 13847800008197966839 19733500000000000000000 qz18 (BSN.isNear_log_sfrac 15 1 12195965485668069 4503599627370496 200000000118401 39467000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz587) Bool.false 51153586820399524478976 18889465931478580854784 1000000000592005 197335000000000000000 12195965485668069 4503599627370496 200000000118401 39467000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 329571 524288 24973259072661432 36028797018963968 197335 1000000000000000 rfl rfl rfl rfl (ep253 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep255 := nat_lit 1356520984812236138597870855944000388359393995733603058319198886811960292212736

noncomputable def ep256 := nat_lit 1438381377095433872590256024872323996512887800548408037035366641288997830656

noncomputable def ep257 := nat_lit 4066686191682517548048432055782256517085156211599712358883525927153302880976896

noncomputable def ep258 := BSN.cos_dyadic_bound_f 2481614148 2147483648 3 2 1048576 395056 ep255 ep72 ep256 ep257 ep75 ep256 422971 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2481614148) qz20 0 2 ep255 ep72 ep256 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2481614148) qz21 0 2 ep257 ep75 ep256 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz338 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 196610683) qz17)

noncomputable def ep259 := @Enclosure.Real.IsNear.cos_image qz45 qz338 Bool.false 196610683 524288 737 1048576 Bool.true 422971 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz45 Bool.false 844436454262171429491 2251799813685248000 13847800008197966839 19733500000000000000000 196610683 524288 737 1048576 (ep254 rfl) rfl) (Enclosure.sfrac_false_div 196610683 524288) (BSN.cos_reduce2 qz338 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 87314035597211709997056) qz19) 226375608064910080 72057594037927936 Bool.false 422971 1048576 59 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q2 196610683 524288 226375608064910080 72057594037927936 59 87314035597211709997056 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 422971 1048576 87314035597211709997056 75557863725914323419136 2481614148 2147483648 395056 394670 (ep258 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep260 := nat_lit 2440587067560348702378095335879302839849698882080046778544929702948497327718400

noncomputable def ep261 := nat_lit 6389684940428473041863198798500761770278666682342091759367234818874453671346176

noncomputable def ep262 := BSN.sin_dyadic_bound_f 2481614148 2147483648 3 2 1048576 395056 ep260 ep79 ep256 ep261 ep81 ep256 959482 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2481614148) qz15 0 2 ep260 ep79 ep256 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2481614148) qz16 0 2 ep261 ep81 ep256 rfl rfl rfl rfl) rfl rfl

noncomputable def ep263 := @Enclosure.Real.IsNear.sin_image qz45 qz338 Bool.false 196610683 524288 737 1048576 Bool.true 959482 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz45 Bool.false 844436454262171429491 2251799813685248000 13847800008197966839 19733500000000000000000 196610683 524288 737 1048576 (ep254 rfl) rfl) (Enclosure.sfrac_false_div 196610683 524288) (BSN.sin_reduce2 qz338 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 87314035597211709997056) qz19) 226375608064910080 72057594037927936 Bool.false 959482 1048576 59 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q2 196610683 524288 226375608064910080 72057594037927936 59 87314035597211709997056 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 959482 1048576 87314035597211709997056 75557863725914323419136 2481614148 2147483648 395056 394670 (ep262 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz339 := (@Enclosure.Real.IsNear.recentre' qz44 Bool.false 270741 1048576 1 1048576 270741 1048576 1 1048576 (ep252 rfl rfl) rfl)

noncomputable def ep264 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz44 (Real.cos qz45)) (@HMul.hMul Real Real Real qz0 qz44 (@Neg.neg Real Real.instNeg (Real.sin qz45))) Bool.true 114515591511 1099511627776 39742965629767 216972127067176960 Bool.false 129885558081 549755813888 2490552376747 13560757941698560 (@Enclosure.Real.IsNear.mulLit_ft qz44 (Real.cos qz45) 270741 1048576 1 1048576 422971 1048576 146484471 206920744960 114515591511 1099511627776 39742965629767 216972127067176960 qz339 (@Enclosure.Real.IsNear.recentre' (Real.cos qz45) Bool.true 422971 1048576 146484471 206920744960 422971 1048576 146484471 206920744960 (ep259 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz44 (@Neg.neg Real Real.instNeg (Real.sin qz45)) 270741 1048576 1 1048576 479741 524288 146484471 206920744960 129885558081 549755813888 2490552376747 13560757941698560 qz339 (@Enclosure.Real.IsNear.neg (Real.sin qz45) Bool.true 479741 524288 146484471 206920744960 (@Enclosure.Real.IsNear.recentre' (Real.sin qz45) Bool.true 959482 1048576 146484471 206920744960 479741 524288 146484471 206920744960 (ep263 rfl rfl) rfl)) rfl)

noncomputable def ep265 := @ep160 114515591511 1099511627776 39742965629767 216972127067176960 Bool.false 129885558081 549755813888 2490552376747 13560757941698560 Bool.true 111200647314766355759104 202272799133 1099511627776 833007723428399 216972127067176960 Bool.false 68077629404331051581440 123832486505 1099511627776 833262474230659 216972127067176960 (ep161 (BSN.head_sum_c_succ qz5 14 15 rfl rfl) (ep250 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep251 ep264) rfl rfl

noncomputable abbrev qz588 := (@Nat.cast Real Real.instNatCast 16)

noncomputable abbrev qz46 := (@Inv.inv Real Real.instInv (Real.sqrt qz588))

noncomputable abbrev qz589 := (Real.log (Enclosure.sfrac Bool.false 16 1))

noncomputable abbrev qz47 := (@HMul.hMul Real Real Real qz269 qz279 qz589)

noncomputable def ep266 := @Enclosure.Complex.IsNear.of_eq qz560 (Complex.mk (@HMul.hMul Real Real Real qz0 qz46 (Real.cos qz47)) (@HMul.hMul Real Real Real qz0 qz46 (@Neg.neg Real Real.instNeg (Real.sin qz47)))) Bool.false 215754961149 1099511627776 38562440356229 216972127067176960 Bool.true 42578576775 274877906944 9632058428831 54243031766794240 (BSN.cpow_neg_s_mk qz12 138478 1000 16 qz13 rfl)

noncomputable abbrev qz590 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16) qz14)

noncomputable def ep267 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz588) 4194305 1048576 1 1048576 131071 131072 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz588) (Real.sqrt qz590) Bool.false 4194305 1048576 1 1048576 (BSN.sqrt_natCast_div_one 16) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz590) Bool.false 4194305 1048576 1 1048576 4194305 1048576 1 1048576 (BSN.sqrt_enclosure 16 1 2097152 2097153 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep268 := BSN.log_dyadic_bound 0 32 1 0 1 524288 197335 0 1 0 32 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 32) 0 0 rfl) rfl rfl rfl

noncomputable def ep269 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz589 138478 1000 0 1 3121657384082679 1125899906842624 50000000039467 9866750000000000000 216140435616500611281 562949953421312000 3461950002732655613 4933375000000000000000 qz18 (BSN.isNear_log_sfrac 16 1 3121657384082679 1125899906842624 50000000039467 9866750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz590) Bool.false 52372720210750067441664 18889465931478580854784 1000000000789340 197335000000000000000 3121657384082679 1125899906842624 50000000039467 9866750000000000000 (BSN.log_rat_reduce_isNear 16 1 4 32 32 0 524288 24973259072661432 36028797018963968 197335 1000000000000000 rfl rfl rfl rfl (ep268 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep270 := nat_lit 151537578868921088952823708336930840260169608394610771678754583178925882474496

noncomputable def ep271 := nat_lit 17983744104790980864576928442579656970276866142550067756172516113845846016

noncomputable def ep272 := nat_lit 454576769118553684896741971153907361466568271451547214900751404504549955731456

noncomputable def ep273 := BSN.cos_dyadic_bound_f 1435026808 2147483648 3 2 1048576 395056 ep270 ep72 ep271 ep272 ep75 ep271 823043 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1435026808) qz20 0 2 ep270 ep72 ep271 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1435026808) qz21 0 2 ep272 ep75 ep271 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz340 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 402592933) qz24)

noncomputable def ep274 := @Enclosure.Real.IsNear.cos_image qz47 qz340 Bool.false 402592933 1048576 737 1048576 Bool.false 823043 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz47 Bool.false 216140435616500611281 562949953421312000 3461950002732655613 4933375000000000000000 402592933 1048576 737 1048576 (ep269 rfl) rfl) (Enclosure.sfrac_false_div 402592933 1048576) (BSN.cos_reduce0 qz340 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 100981034351280894509056) qz25) 226375608064910080 72057594037927936 Bool.false 823043 1048576 61 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q0 402592933 1048576 226375608064910080 72057594037927936 61 100981034351280894509056 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 823043 1048576 100981034351280894509056 151115727451828646838272 1435026808 2147483648 395056 394670 (ep273 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep275 := nat_lit 4240724478764327936608846018963050496

noncomputable def ep276 := BSN.sin_dyadic_bound_f 1435026808 2147483648 2 1 1048576 395056 ep275 ep58 ep275 ep275 ep59 ep275 649700 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1435026808) qz15 0 1 ep275 ep58 ep275 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1435026808) qz16 0 1 ep275 ep59 ep275 rfl rfl rfl rfl) rfl rfl

noncomputable def ep277 := @Enclosure.Real.IsNear.sin_image qz47 qz340 Bool.false 402592933 1048576 737 1048576 Bool.false 649700 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz47 Bool.false 216140435616500611281 562949953421312000 3461950002732655613 4933375000000000000000 402592933 1048576 737 1048576 (ep269 rfl) rfl) (Enclosure.sfrac_false_div 402592933 1048576) (BSN.sin_reduce0 qz340 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 100981034351280894509056) qz25) 226375608064910080 72057594037927936 Bool.false 649700 1048576 61 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q0 402592933 1048576 226375608064910080 72057594037927936 61 100981034351280894509056 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 649700 1048576 100981034351280894509056 151115727451828646838272 1435026808 2147483648 395056 394670 (ep276 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz341 := (@Enclosure.Real.IsNear.recentre' qz46 Bool.false 262143 1048576 1 1048576 262143 1048576 1 1048576 (ep267 rfl rfl) rfl)

noncomputable def ep278 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz46 (Real.cos qz47)) (@HMul.hMul Real Real Real qz0 qz46 (@Neg.neg Real Real.instNeg (Real.sin qz47))) Bool.false 215754961149 1099511627776 38562440356229 216972127067176960 Bool.true 42578576775 274877906944 9632058428831 54243031766794240 (@Enclosure.Real.IsNear.mulLit_ff qz46 (Real.cos qz47) 262143 1048576 1 1048576 823043 1048576 146484471 206920744960 215754961149 1099511627776 38562440356229 216972127067176960 qz341 (@Enclosure.Real.IsNear.recentre' (Real.cos qz47) Bool.false 823043 1048576 146484471 206920744960 823043 1048576 146484471 206920744960 (ep274 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz46 (@Neg.neg Real Real.instNeg (Real.sin qz47)) 262143 1048576 1 1048576 162425 262144 146484471 206920744960 42578576775 274877906944 9632058428831 54243031766794240 qz341 (@Enclosure.Real.IsNear.neg (Real.sin qz47) Bool.false 162425 262144 146484471 206920744960 (@Enclosure.Real.IsNear.recentre' (Real.sin qz47) Bool.false 649700 1048576 146484471 206920744960 162425 262144 146484471 206920744960 (ep277 rfl rfl) rfl)) rfl)

noncomputable def ep279 := @ep158 215754961149 1099511627776 38562440356229 216972127067176960 Bool.true 42578576775 274877906944 9632058428831 54243031766794240 Bool.false 14823793904151917756416 421317563 34359738368 217892540946157 54243031766794240 Bool.true 12776825556100112711680 46481820595 1099511627776 871790707945983 216972127067176960 (ep159 (BSN.head_sum_c_succ qz5 15 16 rfl rfl) (ep265 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep266 ep278) rfl rfl

theorem EMRow48.d7 : Enclosure.Complex.IsNear qz32 Bool.false 421317563 34359738368 217892540946157 54243031766794240 Bool.true 46481820595 1099511627776 871790707945983 216972127067176960 := ep157 (BSN.head_sum_c_succ qz5 16 17 rfl rfl) (ep279 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz48 := (BSN.headSumC qz273 25)

noncomputable abbrev qz591 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 24) qz7)

noncomputable def ep280 := @Enclosure.Complex.IsNear.of_eq qz48 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 24) qz591) Bool.false 443470136011 549755813888 114572716696309 21697212706717696 Bool.true 280073031981 1099511627776 229096125651371 43394425413435392

noncomputable def ep281 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 24) qz591 Bool.false 335241315661 549755813888 111417406590475 21697212706717696 Bool.true 220763681237 1099511627776 222814482268971 43394425413435392 Bool.false

noncomputable abbrev qz592 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 23) qz7)

noncomputable def ep282 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 24) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 23) qz592) Bool.false 335241315661 549755813888 111417406590475 21697212706717696 Bool.true 220763681237 1099511627776 222814482268971 43394425413435392

noncomputable def ep283 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 23) qz592 Bool.false 488933946773 1099511627776 1081982259491521 216972127067176960 Bool.true 80756948045 1099511627776 1081918098384291 216972127067176960 Bool.false

noncomputable abbrev qz593 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 22) qz7)

noncomputable def ep284 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 23) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 22) qz593) Bool.false 488933946773 1099511627776 1081982259491521 216972127067176960 Bool.true 80756948045 1099511627776 1081918098384291 216972127067176960

noncomputable def ep285 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 22) qz593 Bool.false 323052864317 1099511627776 1049088059975023 216972127067176960 Bool.false 84876433255 1099511627776 1049024117514973 216972127067176960 Bool.false

noncomputable abbrev qz594 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 21) qz7)

noncomputable def ep286 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 22) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 21) qz594) Bool.false 323052864317 1099511627776 1049088059975023 216972127067176960 Bool.false 84876433255 1099511627776 1049024117514973 216972127067176960

noncomputable def ep287 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 21) qz594 Bool.false 128589598837 1099511627776 1015234069074603 216972127067176960 Bool.false 225417592945 1099511627776 1015263132573403 216972127067176960 Bool.false

noncomputable abbrev qz595 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 20) qz7)

noncomputable def ep288 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 21) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 20) qz595) Bool.false 128589598837 1099511627776 1015234069074603 216972127067176960 Bool.false 225417592945 1099511627776 1015263132573403 216972127067176960

noncomputable def ep289 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 20) qz595 Bool.true 28602404463 274877906944 490341670457299 108486063533588480 Bool.false 131401720263 549755813888 490442726894809 108486063533588480 Bool.false

noncomputable abbrev qz596 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 19) qz7)

noncomputable def ep290 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 20) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 19) qz596) Bool.true 28602404463 274877906944 490341670457299 108486063533588480 Bool.false 131401720263 549755813888 490442726894809 108486063533588480

noncomputable def ep291 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 19) qz596 Bool.true 312588136027 1099511627776 945282467064463 216972127067176960 Bool.false 53375446377 549755813888 472759568326339 108486063533588480 Bool.false

noncomputable abbrev qz597 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 18) qz7)

noncomputable def ep292 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 19) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 18) qz597) Bool.true 312588136027 1099511627776 945282467064463 216972127067176960 Bool.false 53375446377 549755813888 472759568326339 108486063533588480

noncomputable def ep293 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 18) qz597 Bool.true 235946610927 1099511627776 909017343504371 216972127067176960 Bool.true 140813590869 1099511627776 909117541534631 216972127067176960 Bool.true

noncomputable abbrev qz598 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 17) qz7)

noncomputable def ep294 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 18) (@HAdd.hAdd Complex Complex Complex qz4 qz32 qz598) Bool.true 235946610927 1099511627776 909017343504371 216972127067176960 Bool.true 140813590869 1099511627776 909117541534631 216972127067176960

noncomputable def ep295 := @Enclosure.Complex.IsNear.addLitP qz32 qz598 Bool.false 421317563 34359738368 217892540946157 54243031766794240 Bool.true 46481820595 1099511627776 871790707945983 216972127067176960 Bool.true

noncomputable abbrev qz599 := (@Nat.cast Real Real.instNatCast 17)

noncomputable abbrev qz49 := (@Inv.inv Real Real.instInv (Real.sqrt qz599))

noncomputable abbrev qz600 := (Real.log (Enclosure.sfrac Bool.false 17 1))

noncomputable abbrev qz50 := (@HMul.hMul Real Real Real qz269 qz279 qz600)

noncomputable def ep296 := @Enclosure.Complex.IsNear.of_eq qz598 (Complex.mk (@HMul.hMul Real Real Real qz0 qz49 (Real.cos qz50)) (@HMul.hMul Real Real Real qz0 qz49 (@Neg.neg Real Real.instNeg (Real.sin qz50)))) Bool.true 249428772943 1099511627776 37447179719743 216972127067176960 Bool.true 47165885137 549755813888 4665854198581 27121515883397120 (BSN.cpow_neg_s_mk qz12 138478 1000 17 qz13 rfl)

noncomputable abbrev qz601 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 17) qz14)

noncomputable def ep297 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz599) 4323389 1048576 1 1048576 127158 127159 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz599) (Real.sqrt qz601) Bool.false 4323389 1048576 1 1048576 (BSN.sqrt_natCast_div_one 17) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz601) Bool.false 4323389 1048576 1 1048576 4323389 1048576 1 1048576 (BSN.sqrt_enclosure 17 1 2161694 2161695 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep298 := BSN.log_dyadic_bound 1 33 2 1 3267 524288 197335 1 1 31784 34 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1) (BSN.artanhQ 33) 0 1 1 3267 1 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep299 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz600 138478 1000 0 1 3189913004350711 1125899906842624 50000000039467 9866750000000000000 220866386508238878929 562949953421312000 3461950002732655613 4933375000000000000000 qz18 (BSN.isNear_log_sfrac 17 1 3189913004350711 1125899906842624 50000000039467 9866750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz601) Bool.false 53517859495200818200576 18889465931478580854784 1000000000789340 197335000000000000000 3189913004350711 1125899906842624 50000000039467 9866750000000000000 (BSN.log_rat_reduce_isNear 17 1 4 34 32 31784 524288 24973259072661432 36028797018963968 197335 1000000000000000 rfl rfl rfl rfl (ep298 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep300 := nat_lit 2926604160612591147742954810157685539611536389702977394387690336566459773491745

noncomputable def ep301 := nat_lit 2067814364877697529338413603327650431391592384328239131576555121081726540321

noncomputable def ep302 := nat_lit 7661567768823174829041190880769503074474627966314123645754731697001833754270241

noncomputable def ep303 := BSN.sin_dyadic_bound_f 2596802637 2147483648 3 2 1048576 395056 ep300 ep79 ep301 ep302 ep81 ep301 980779 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2596802637) qz15 0 2 ep300 ep79 ep301 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2596802637) qz16 0 2 ep302 ep81 ep301 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz342 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 411395703) qz24)

noncomputable def ep304 := @Enclosure.Real.IsNear.cos_image qz50 qz342 Bool.false 411395703 1048576 737 1048576 Bool.true 980779 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz50 Bool.false 220866386508238878929 562949953421312000 3461950002732655613 4933375000000000000000 411395703 1048576 737 1048576 (ep299 rfl) rfl) (Enclosure.sfrac_false_div 411395703 1048576) (BSN.cos_reduce1 qz342 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 182733740478426928644096) qz25) 226375608064910080 72057594037927936 Bool.false 980779 1048576 62 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q1 411395703 1048576 226375608064910080 72057594037927936 62 182733740478426928644096 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 980779 1048576 182733740478426928644096 151115727451828646838272 2596802637 2147483648 395056 394670 (ep303 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep305 := nat_lit 1626810228946940725425791967244637588864805368672466658718306433701847308180001

noncomputable def ep306 := nat_lit 4876295058111066781218699074527257465731632921248743497891766190863378471459361

noncomputable def ep307 := BSN.cos_dyadic_bound_f 2596802637 2147483648 3 2 1048576 395056 ep305 ep72 ep301 ep306 ep75 ep301 370922 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2596802637) qz20 0 2 ep305 ep72 ep301 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2596802637) qz21 0 2 ep306 ep75 ep301 rfl rfl rfl rfl) rfl rfl

noncomputable def ep308 := @Enclosure.Real.IsNear.sin_image qz50 qz342 Bool.false 411395703 1048576 737 1048576 Bool.false 370922 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz50 Bool.false 220866386508238878929 562949953421312000 3461950002732655613 4933375000000000000000 411395703 1048576 737 1048576 (ep299 rfl) rfl) (Enclosure.sfrac_false_div 411395703 1048576) (BSN.sin_reduce1 qz342 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 182733740478426928644096) qz25) 226375608064910080 72057594037927936 Bool.false 370922 1048576 62 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q1 411395703 1048576 226375608064910080 72057594037927936 62 182733740478426928644096 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 370922 1048576 182733740478426928644096 151115727451828646838272 2596802637 2147483648 395056 394670 (ep307 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz343 := (@Enclosure.Real.IsNear.recentre' qz49 Bool.false 254317 1048576 1 1048576 254317 1048576 1 1048576 (ep297 rfl rfl) rfl)

noncomputable def ep309 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz49 (Real.cos qz50)) (@HMul.hMul Real Real Real qz0 qz49 (@Neg.neg Real Real.instNeg (Real.sin qz50))) Bool.true 249428772943 1099511627776 37447179719743 216972127067176960 Bool.true 47165885137 549755813888 4665854198581 27121515883397120 (@Enclosure.Real.IsNear.mulLit_ft qz49 (Real.cos qz50) 254317 1048576 1 1048576 980779 1048576 146484471 206920744960 249428772943 1099511627776 37447179719743 216972127067176960 qz343 (@Enclosure.Real.IsNear.recentre' (Real.cos qz50) Bool.true 980779 1048576 146484471 206920744960 980779 1048576 146484471 206920744960 (ep304 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz49 (@Neg.neg Real Real.instNeg (Real.sin qz50)) 254317 1048576 1 1048576 185461 524288 146484471 206920744960 47165885137 549755813888 4665854198581 27121515883397120 qz343 (@Enclosure.Real.IsNear.neg (Real.sin qz50) Bool.false 185461 524288 146484471 206920744960 (@Enclosure.Real.IsNear.recentre' (Real.sin qz50) Bool.false 370922 1048576 146484471 206920744960 185461 524288 146484471 206920744960 (ep308 rfl rfl) rfl)) rfl)

noncomputable def ep310 := @ep295 249428772943 1099511627776 37447179719743 216972127067176960 Bool.true 47165885137 549755813888 4665854198581 27121515883397120 Bool.true 8107063820268009947136 235946610927 1099511627776 909017343504371 216972127067176960 Bool.true 77413090254678940188672 140813590869 1099511627776 909117541534631 216972127067176960 EMRow48.d7 (ep296 ep309) rfl rfl

noncomputable abbrev qz602 := (@Nat.cast Real Real.instNatCast 18)

noncomputable abbrev qz51 := (@Inv.inv Real Real.instInv (Real.sqrt qz602))

noncomputable abbrev qz603 := (Real.log (Enclosure.sfrac Bool.false 18 1))

noncomputable abbrev qz52 := (@HMul.hMul Real Real Real qz269 qz279 qz603)

noncomputable def ep311 := @Enclosure.Complex.IsNear.of_eq qz597 (Complex.mk (@HMul.hMul Real Real Real qz0 qz51 (Real.cos qz52)) (@HMul.hMul Real Real Real qz0 qz51 (@Neg.neg Real Real.instNeg (Real.sin qz52)))) Bool.true 19160381275 274877906944 9066280890023 54243031766794240 Bool.false 247564483623 1099511627776 36401595118047 216972127067176960 (BSN.cpow_neg_s_mk qz12 138478 1000 18 qz13 rfl)

noncomputable abbrev qz604 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 18) qz14)

noncomputable def ep312 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz602) 4448731 1048576 1 1048576 123575 123576 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz602) (Real.sqrt qz604) Bool.false 4448731 1048576 1 1048576 (BSN.sqrt_natCast_div_one 18) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz604) Bool.false 4448731 1048576 1 1048576 4448731 1048576 1 1048576 (BSN.sqrt_enclosure 18 1 2224365 2224366 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep313 := BSN.log_dyadic_bound 2 34 3 2 20045040 524288 197335 23168 48 61752 36 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 2) (BSN.artanhQ 34) 0 2 23168 20045040 48 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep314 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz603 138478 1000 0 1 3254268794313975 1125899906842624 50000000039467 9866750000000000000 9012892681980212601 22517998136852480 3461950002732655613 4933375000000000000000 qz18 (BSN.isNear_log_sfrac 18 1 3254268794313975 1125899906842624 50000000039467 9866750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz604) Bool.false 54597570484265130393600 18889465931478580854784 1000000000789340 197335000000000000000 3254268794313975 1125899906842624 50000000039467 9866750000000000000 (BSN.log_rat_reduce_isNear 18 1 4 36 32 61752 524288 24973259072661432 36028797018963968 197335 1000000000000000 rfl rfl rfl rfl (ep313 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep315 := nat_lit 1983432025553671949451249265619236670669733931185702414417092651152197816975616

noncomputable def ep316 := nat_lit 3072067719024688211037240340867649576483664193860975095940156811420080046336

noncomputable def ep317 := nat_lit 5944151941222966471931673316175974712856234465169385293059397639833753290834176

noncomputable def ep318 := BSN.cos_dyadic_bound_f 2728530722 2147483648 3 2 1048576 395056 ep315 ep72 ep316 ep317 ep75 ep316 310100 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2728530722) qz20 0 2 ep315 ep72 ep316 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2728530722) qz21 0 2 ep317 ep75 ep316 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz344 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13115485) (@Nat.cast Real Real.instNatCast 32768))

noncomputable abbrev qz345 := (@Nat.cast Real Real.instNatCast 4722366482869645213696)

noncomputable def ep319 := @Enclosure.Real.IsNear.cos_image qz52 qz344 Bool.false 13115485 32768 737 1048576 Bool.true 310100 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz52 Bool.false 9012892681980212601 22517998136852480 3461950002732655613 4933375000000000000000 13115485 32768 737 1048576 (ep314 rfl) rfl) (Enclosure.sfrac_false_div 13115485 32768) (BSN.cos_reduce2 qz344 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6000102513039282012160) qz345) 226375608064910080 72057594037927936 Bool.false 310100 1048576 63 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q2 13115485 32768 226375608064910080 72057594037927936 63 6000102513039282012160 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 310100 1048576 6000102513039282012160 4722366482869645213696 2728530722 2147483648 395056 394670 (ep318 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep320 := nat_lit 3567719991821389758443418885841931887544334144779175565874014646624820006519040

noncomputable def ep321 := nat_lit 9339054726082361776914893930938893034730377780012542046181373344417943696998656

noncomputable def ep322 := BSN.sin_dyadic_bound_f 2728530722 2147483648 3 2 1048576 395056 ep320 ep79 ep316 ep321 ep81 ep316 1001673 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2728530722) qz15 0 2 ep320 ep79 ep316 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2728530722) qz16 0 2 ep321 ep81 ep316 rfl rfl rfl rfl) rfl rfl

noncomputable def ep323 := @Enclosure.Real.IsNear.sin_image qz52 qz344 Bool.false 13115485 32768 737 1048576 Bool.true 1001673 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz52 Bool.false 9012892681980212601 22517998136852480 3461950002732655613 4933375000000000000000 13115485 32768 737 1048576 (ep314 rfl) rfl) (Enclosure.sfrac_false_div 13115485 32768) (BSN.sin_reduce2 qz344 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6000102513039282012160) qz345) 226375608064910080 72057594037927936 Bool.false 1001673 1048576 63 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q2 13115485 32768 226375608064910080 72057594037927936 63 6000102513039282012160 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1001673 1048576 6000102513039282012160 4722366482869645213696 2728530722 2147483648 395056 394670 (ep322 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz346 := (@Enclosure.Real.IsNear.recentre' qz51 Bool.false 247151 1048576 1 1048576 247151 1048576 1 1048576 (ep312 rfl rfl) rfl)

noncomputable def ep324 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz51 (Real.cos qz52)) (@HMul.hMul Real Real Real qz0 qz51 (@Neg.neg Real Real.instNeg (Real.sin qz52))) Bool.true 19160381275 274877906944 9066280890023 54243031766794240 Bool.false 247564483623 1099511627776 36401595118047 216972127067176960 (@Enclosure.Real.IsNear.mulLit_ft qz51 (Real.cos qz52) 247151 1048576 1 1048576 77525 262144 146484471 206920744960 19160381275 274877906944 9066280890023 54243031766794240 qz346 (@Enclosure.Real.IsNear.recentre' (Real.cos qz52) Bool.true 310100 1048576 146484471 206920744960 77525 262144 146484471 206920744960 (ep319 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz51 (@Neg.neg Real Real.instNeg (Real.sin qz52)) 247151 1048576 1 1048576 1001673 1048576 146484471 206920744960 247564483623 1099511627776 36401595118047 216972127067176960 qz346 (@Enclosure.Real.IsNear.neg (Real.sin qz52) Bool.true 1001673 1048576 146484471 206920744960 (@Enclosure.Real.IsNear.recentre' (Real.sin qz52) Bool.true 1001673 1048576 146484471 206920744960 1001673 1048576 146484471 206920744960 (ep323 rfl rfl) rfl)) rfl)

noncomputable def ep325 := @ep293 19160381275 274877906944 9066280890023 54243031766794240 Bool.false 247564483623 1099511627776 36401595118047 216972127067176960 Bool.true 85923572566628119871488 312588136027 1099511627776 945282467064463 216972127067176960 Bool.false 117373847858491743535104 53375446377 549755813888 472759568326339 108486063533588480 (ep294 (BSN.head_sum_c_succ qz5 17 18 rfl rfl) (ep310 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep311 ep324) rfl rfl

noncomputable abbrev qz605 := (@Nat.cast Real Real.instNatCast 19)

noncomputable abbrev qz53 := (@Inv.inv Real Real.instInv (Real.sqrt qz605))

noncomputable abbrev qz606 := (Real.log (Enclosure.sfrac Bool.false 19 1))

noncomputable abbrev qz54 := (@HMul.hMul Real Real Real qz269 qz279 qz606)

noncomputable def ep326 := @Enclosure.Complex.IsNear.of_eq qz596 (Complex.mk (@HMul.hMul Real Real Real qz0 qz53 (Real.cos qz54)) (@HMul.hMul Real Real Real qz0 qz53 (@Neg.neg Real Real.instNeg (Real.sin qz54)))) Bool.false 198178518175 1099511627776 7080174770027 43394425413435392 Bool.false 39013136943 274877906944 1768315856847 10848606353358848 (BSN.cpow_neg_s_mk qz12 138478 1000 19 qz13 rfl)

noncomputable abbrev qz607 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 19) qz14)

noncomputable def ep327 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz605) 4570637 1048576 1 1048576 120279 120280 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz605) (Real.sqrt qz607) Bool.false 4570637 1048576 1 1048576 (BSN.sqrt_natCast_div_one 19) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz607) Bool.false 4570637 1048576 1 1048576 4570637 1048576 1 1048576 (BSN.sqrt_enclosure 19 1 2285318 2285319 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep328 := BSN.log_dyadic_bound 3 35 3 2 22509375 524288 197335 55368 243 90099 38 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 3) (BSN.artanhQ 35) 0 2 55368 22509375 243 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep329 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz606 138478 1000 0 1 3315143513283831 1125899906842624 50000000039467 9866750000000000000 229537221716259174609 562949953421312000 3461950002732655613 4933375000000000000000 qz18 (BSN.isNear_log_sfrac 19 1 3315143513283831 1125899906842624 50000000039467 9866750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz607) Bool.false 55618878793361701994496 18889465931478580854784 1000000000789340 197335000000000000000 3315143513283831 1125899906842624 50000000039467 9866750000000000000 (BSN.log_rat_reduce_isNear 19 1 4 38 32 90099 524288 24973259072661432 36028797018963968 197335 1000000000000000 rfl rfl rfl rfl (ep328 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep330 := nat_lit 912720054376009165190055008522382353190903424846100296541140902842114821324800

noncomputable def ep331 := nat_lit 201317293518787459169582775555843113983181220767657323246741894650402963456

noncomputable def ep332 := nat_lit 2390131342985755491040059983541053845696393343096638855274874306280866736766976

noncomputable def ep333 := BSN.sin_dyadic_bound_f 1940819448 2147483648 3 2 1048576 395056 ep330 ep79 ep331 ep332 ep81 ep331 823825 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1940819448) qz15 0 2 ep330 ep79 ep331 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1940819448) qz16 0 2 ep332 ep81 ep331 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz347 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 53443299) qz553)

noncomputable def ep334 := @Enclosure.Real.IsNear.cos_image qz54 qz347 Bool.false 53443299 131072 737 1048576 Bool.false 823825 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz54 Bool.false 229537221716259174609 562949953421312000 3461950002732655613 4933375000000000000000 53443299 131072 737 1048576 (ep329 rfl) rfl) (Enclosure.sfrac_false_div 53443299 131072) (BSN.cos_reduce3 qz347 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 17071628405671500709888) qz305) 226375608064910080 72057594037927936 Bool.false 823825 1048576 64 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q3 53443299 131072 226375608064910080 72057594037927936 64 17071628405671500709888 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 823825 1048576 17071628405671500709888 18889465931478580854784 1940819448 2147483648 395056 394670 (ep333 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep335 := nat_lit 507156171228235663976328152634903904267827761012619123555410164643241746497536

noncomputable def ep336 := nat_lit 1521065879097669417010645292353600026575516920596322056019737010140424433565696

noncomputable def ep337 := BSN.cos_dyadic_bound_f 1940819448 2147483648 3 2 1048576 395056 ep335 ep72 ep331 ep336 ep75 ep331 648708 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1940819448) qz20 0 2 ep335 ep72 ep331 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1940819448) qz21 0 2 ep336 ep75 ep331 rfl rfl rfl rfl) rfl rfl

noncomputable def ep338 := @Enclosure.Real.IsNear.sin_image qz54 qz347 Bool.false 53443299 131072 737 1048576 Bool.true 648708 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz54 Bool.false 229537221716259174609 562949953421312000 3461950002732655613 4933375000000000000000 53443299 131072 737 1048576 (ep329 rfl) rfl) (Enclosure.sfrac_false_div 53443299 131072) (BSN.sin_reduce3 qz347 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 17071628405671500709888) qz305) 226375608064910080 72057594037927936 Bool.false 648708 1048576 64 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q3 53443299 131072 226375608064910080 72057594037927936 64 17071628405671500709888 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 648708 1048576 17071628405671500709888 18889465931478580854784 1940819448 2147483648 395056 394670 (ep337 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz348 := (@Enclosure.Real.IsNear.recentre' qz53 Bool.false 240559 1048576 1 1048576 240559 1048576 1 1048576 (ep327 rfl rfl) rfl)

noncomputable def ep339 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz53 (Real.cos qz54)) (@HMul.hMul Real Real Real qz0 qz53 (@Neg.neg Real Real.instNeg (Real.sin qz54))) Bool.false 198178518175 1099511627776 7080174770027 43394425413435392 Bool.false 39013136943 274877906944 1768315856847 10848606353358848 (@Enclosure.Real.IsNear.mulLit_ff qz53 (Real.cos qz54) 240559 1048576 1 1048576 823825 1048576 146484471 206920744960 198178518175 1099511627776 7080174770027 43394425413435392 qz348 (@Enclosure.Real.IsNear.recentre' (Real.cos qz54) Bool.false 823825 1048576 146484471 206920744960 823825 1048576 146484471 206920744960 (ep334 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz53 (@Neg.neg Real Real.instNeg (Real.sin qz54)) 240559 1048576 1 1048576 162177 262144 146484471 206920744960 39013136943 274877906944 1768315856847 10848606353358848 qz348 (@Enclosure.Real.IsNear.neg (Real.sin qz54) Bool.true 162177 262144 146484471 206920744960 (@Enclosure.Real.IsNear.recentre' (Real.sin qz54) Bool.true 648708 1048576 146484471 206920744960 162177 262144 146484471 206920744960 (ep338 rfl rfl) rfl)) rfl)

noncomputable def ep340 := @ep291 198178518175 1099511627776 7080174770027 43394425413435392 Bool.false 39013136943 274877906944 1768315856847 10848606353358848 Bool.true 125794705157682628657152 28602404463 274877906944 490341670457299 108486063533588480 Bool.false 36119429834734433206272 131401720263 549755813888 490442726894809 108486063533588480 (ep292 (BSN.head_sum_c_succ qz5 18 19 rfl rfl) (ep325 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep326 ep339) rfl rfl

noncomputable abbrev qz608 := (@Nat.cast Real Real.instNatCast 20)

noncomputable abbrev qz55 := (@Inv.inv Real Real.instInv (Real.sqrt qz608))

noncomputable abbrev qz609 := (Real.log (Enclosure.sfrac Bool.false 20 1))

noncomputable abbrev qz56 := (@HMul.hMul Real Real Real qz269 qz279 qz609)

noncomputable def ep341 := @Enclosure.Complex.IsNear.of_eq qz595 (Complex.mk (@HMul.hMul Real Real Real qz0 qz55 (Real.cos qz56)) (@HMul.hMul Real Real Real qz0 qz55 (@Neg.neg Real Real.instNeg (Real.sin qz56)))) Bool.false 242999216689 1099511627776 6910145632001 43394425413435392 Bool.true 37385847581 1099511627776 6875535756757 43394425413435392 (BSN.cpow_neg_s_mk qz12 138478 1000 20 qz13 rfl)

noncomputable abbrev qz610 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 20) qz14)

noncomputable def ep342 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz608) 4689375 1048576 1 1048576 117234 117235 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz608) (Real.sqrt qz610) Bool.false 4689375 1048576 1 1048576 (BSN.sqrt_natCast_div_one 20) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz610) Bool.false 4689375 1048576 1 1048576 4689375 1048576 1 1048576 (BSN.sqrt_enclosure 20 1 2344687 2344688 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep343 := BSN.log_dyadic_bound 4 36 3 2 25194240 524288 197335 104448 768 116991 40 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 4) (BSN.artanhQ 36) 0 2 104448 25194240 768 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep344 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz609 138478 1000 0 1 3372893643545847 1125899906842624 50000000039467 9866750000000000000 233535782985470900433 562949953421312000 3461950002732655613 4933375000000000000000 qz18 (BSN.isNear_log_sfrac 20 1 3372893643545847 1125899906842624 50000000039467 9866750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz610) Bool.false 56587765202795681021952 18889465931478580854784 1000000000789340 197335000000000000000 3372893643545847 1125899906842624 50000000039467 9866750000000000000 (BSN.log_rat_reduce_isNear 20 1 4 40 32 116991 524288 24973259072661432 36028797018963968 197335 1000000000000000 rfl rfl rfl rfl (ep343 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep345 := nat_lit 11549433305940213837168733670100625

noncomputable def ep346 := BSN.cos_dyadic_bound_f 327823565 2147483648 2 1 1048576 395056 ep345 ep62 ep345 ep345 ep63 ep345 1036381 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 327823565) qz20 0 1 ep345 ep62 ep345 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 327823565) qz21 0 1 ep345 ep63 ep345 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz349 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 434994293) qz24)

noncomputable def ep347 := @Enclosure.Real.IsNear.cos_image qz56 qz349 Bool.false 434994293 1048576 737 1048576 Bool.false 1036381 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz56 Bool.false 233535782985470900433 562949953421312000 3461950002732655613 4933375000000000000000 434994293 1048576 737 1048576 (ep344 rfl) rfl) (Enclosure.sfrac_false_div 434994293 1048576) (BSN.cos_reduce0 qz349 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 23068532619371270373376) qz25) 226375608064910080 72057594037927936 Bool.false 1036381 1048576 66 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q0 434994293 1048576 226375608064910080 72057594037927936 66 23068532619371270373376 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1036381 1048576 23068532619371270373376 151115727451828646838272 327823565 2147483648 395056 394670 (ep346 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep348 := BSN.sin_dyadic_bound_f 327823565 2147483648 2 1 1048576 395056 ep345 ep58 ep345 ep345 ep59 ep345 159449 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 327823565) qz15 0 1 ep345 ep58 ep345 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 327823565) qz16 0 1 ep345 ep59 ep345 rfl rfl rfl rfl) rfl rfl

noncomputable def ep349 := @Enclosure.Real.IsNear.sin_image qz56 qz349 Bool.false 434994293 1048576 737 1048576 Bool.false 159449 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz56 Bool.false 233535782985470900433 562949953421312000 3461950002732655613 4933375000000000000000 434994293 1048576 737 1048576 (ep344 rfl) rfl) (Enclosure.sfrac_false_div 434994293 1048576) (BSN.sin_reduce0 qz349 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 23068532619371270373376) qz25) 226375608064910080 72057594037927936 Bool.false 159449 1048576 66 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q0 434994293 1048576 226375608064910080 72057594037927936 66 23068532619371270373376 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 159449 1048576 23068532619371270373376 151115727451828646838272 327823565 2147483648 395056 394670 (ep348 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz350 := (@Enclosure.Real.IsNear.recentre' qz55 Bool.false 234469 1048576 1 1048576 234469 1048576 1 1048576 (ep342 rfl rfl) rfl)

noncomputable def ep350 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz55 (Real.cos qz56)) (@HMul.hMul Real Real Real qz0 qz55 (@Neg.neg Real Real.instNeg (Real.sin qz56))) Bool.false 242999216689 1099511627776 6910145632001 43394425413435392 Bool.true 37385847581 1099511627776 6875535756757 43394425413435392 (@Enclosure.Real.IsNear.mulLit_ff qz55 (Real.cos qz56) 234469 1048576 1 1048576 1036381 1048576 146484471 206920744960 242999216689 1099511627776 6910145632001 43394425413435392 qz350 (@Enclosure.Real.IsNear.recentre' (Real.cos qz56) Bool.false 1036381 1048576 146484471 206920744960 1036381 1048576 146484471 206920744960 (ep347 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz55 (@Neg.neg Real Real.instNeg (Real.sin qz56)) 234469 1048576 1 1048576 159449 1048576 146484471 206920744960 37385847581 1099511627776 6875535756757 43394425413435392 qz350 (@Enclosure.Real.IsNear.neg (Real.sin qz56) Bool.false 159449 1048576 146484471 206920744960 (@Enclosure.Real.IsNear.recentre' (Real.sin qz56) Bool.false 159449 1048576 146484471 206920744960 159449 1048576 146484471 206920744960 (ep349 rfl rfl) rfl)) rfl)

noncomputable def ep351 := @ep289 242999216689 1099511627776 6910145632001 43394425413435392 Bool.true 37385847581 1099511627776 6875535756757 43394425413435392 Bool.false 35346439783083176624128 128589598837 1099511627776 1015234069074603 216972127067176960 Bool.false 123924632274152361820160 225417592945 1099511627776 1015263132573403 216972127067176960 (ep290 (BSN.head_sum_c_succ qz5 19 20 rfl rfl) (ep340 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep341 ep350) rfl rfl

noncomputable abbrev qz611 := (@Nat.cast Real Real.instNatCast 21)

noncomputable abbrev qz57 := (@Inv.inv Real Real.instInv (Real.sqrt qz611))

noncomputable abbrev qz612 := (Real.log (Enclosure.sfrac Bool.false 21 1))

noncomputable abbrev qz58 := (@HMul.hMul Real Real Real qz269 qz279 qz612)

noncomputable def ep352 := @Enclosure.Complex.IsNear.of_eq qz594 (Complex.mk (@HMul.hMul Real Real Real qz0 qz57 (Real.cos qz58)) (@HMul.hMul Real Real Real qz0 qz57 (@Neg.neg Real Real.instNeg (Real.sin qz58)))) Bool.false 24307908185 137438953472 1692699545021 10848606353358848 Bool.true 70270579845 549755813888 3376098494157 21697212706717696 (BSN.cpow_neg_s_mk qz12 138478 1000 21 qz13 rfl)

noncomputable abbrev qz613 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 21) qz14)

noncomputable def ep353 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz611) 4805179 1048576 1 1048576 114408 114410 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz611) (Real.sqrt qz613) Bool.false 4805179 1048576 1 1048576 (BSN.sqrt_natCast_div_one 21) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz613) Bool.false 4805179 1048576 1 1048576 4805179 1048576 1 1048576 (BSN.sqrt_enclosure 21 1 2402589 2402590 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep354 := BSN.log_dyadic_bound 5 37 4 3 269401272945 524288 197335 1658093375 234375 142571 42 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 5) (BSN.artanhQ 37) 0 3 1658093375 269401272945 234375 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep355 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz612 138478 1000 0 1 3427826275261687 1125899906842624 50000000039467 9866750000000000000 237339263472843946193 562949953421312000 3461950002732655613 4933375000000000000000 qz18 (BSN.isNear_log_sfrac 21 1 3427826275261687 1125899906842624 50000000039467 9866750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz613) Bool.false 57509381830540779323392 18889465931478580854784 1000000000789340 197335000000000000000 3427826275261687 1125899906842624 50000000039467 9866750000000000000 (BSN.log_rat_reduce_isNear 21 1 4 42 32 142571 524288 24973259072661432 36028797018963968 197335 1000000000000000 rfl rfl rfl rfl (ep354 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep356 := nat_lit 3261990350498980077374697764834924401

noncomputable def ep357 := BSN.cos_dyadic_bound_f 1343911493 2147483648 2 1 1048576 395056 ep356 ep62 ep356 ep356 ep63 ep356 849860 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1343911493) qz20 0 1 ep356 ep62 ep356 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1343911493) qz21 0 1 ep356 ep63 ep356 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz351 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 442078827) qz24)

noncomputable def ep358 := @Enclosure.Real.IsNear.cos_image qz58 qz351 Bool.false 442078827 1048576 737 1048576 Bool.false 849860 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz58 Bool.false 237339263472843946193 562949953421312000 3461950002732655613 4933375000000000000000 442078827 1048576 737 1048576 (ep355 rfl) rfl) (Enclosure.sfrac_false_div 442078827 1048576) (BSN.cos_reduce0 qz351 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 94569364050082166472704) qz25) 226375608064910080 72057594037927936 Bool.false 849860 1048576 67 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q0 442078827 1048576 226375608064910080 72057594037927936 67 94569364050082166472704 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 849860 1048576 94569364050082166472704 151115727451828646838272 1343911493 2147483648 395056 394670 (ep357 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep359 := BSN.sin_dyadic_bound_f 1343911493 2147483648 2 1 1048576 395056 ep356 ep58 ep356 ep356 ep59 ep356 614205 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1343911493) qz15 0 1 ep356 ep58 ep356 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1343911493) qz16 0 1 ep356 ep59 ep356 rfl rfl rfl rfl) rfl rfl

noncomputable def ep360 := @Enclosure.Real.IsNear.sin_image qz58 qz351 Bool.false 442078827 1048576 737 1048576 Bool.false 614205 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz58 Bool.false 237339263472843946193 562949953421312000 3461950002732655613 4933375000000000000000 442078827 1048576 737 1048576 (ep355 rfl) rfl) (Enclosure.sfrac_false_div 442078827 1048576) (BSN.sin_reduce0 qz351 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 94569364050082166472704) qz25) 226375608064910080 72057594037927936 Bool.false 614205 1048576 67 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q0 442078827 1048576 226375608064910080 72057594037927936 67 94569364050082166472704 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 614205 1048576 94569364050082166472704 151115727451828646838272 1343911493 2147483648 395056 394670 (ep359 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz352 := (@Enclosure.Real.IsNear.recentre' qz57 Bool.false 228818 1048576 2 1048576 114409 524288 1 524288 (ep353 rfl rfl) rfl)

noncomputable def ep361 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz57 (Real.cos qz58)) (@HMul.hMul Real Real Real qz0 qz57 (@Neg.neg Real Real.instNeg (Real.sin qz58))) Bool.false 24307908185 137438953472 1692699545021 10848606353358848 Bool.true 70270579845 549755813888 3376098494157 21697212706717696 (@Enclosure.Real.IsNear.mulLit_ff qz57 (Real.cos qz58) 114409 524288 1 524288 212465 262144 146484471 206920744960 24307908185 137438953472 1692699545021 10848606353358848 qz352 (@Enclosure.Real.IsNear.recentre' (Real.cos qz58) Bool.false 849860 1048576 146484471 206920744960 212465 262144 146484471 206920744960 (ep358 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz57 (@Neg.neg Real Real.instNeg (Real.sin qz58)) 114409 524288 1 524288 614205 1048576 146484471 206920744960 70270579845 549755813888 3376098494157 21697212706717696 qz352 (@Enclosure.Real.IsNear.neg (Real.sin qz58) Bool.false 614205 1048576 146484471 206920744960 (@Enclosure.Real.IsNear.recentre' (Real.sin qz58) Bool.false 614205 1048576 146484471 206920744960 614205 1048576 146484471 206920744960 (ep360 rfl rfl) rfl)) rfl)

noncomputable def ep362 := @ep287 24307908185 137438953472 1692699545021 10848606353358848 Bool.true 70270579845 549755813888 3376098494157 21697212706717696 Bool.false 44400047587860492058624 323052864317 1099511627776 1049088059975023 216972127067176960 Bool.false 46661312644013034045440 84876433255 1099511627776 1049024117514973 216972127067176960 (ep288 (BSN.head_sum_c_succ qz5 20 21 rfl rfl) (ep351 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep352 ep361) rfl rfl

noncomputable abbrev qz614 := (@Nat.cast Real Real.instNatCast 22)

noncomputable abbrev qz59 := (@Inv.inv Real Real.instInv (Real.sqrt qz614))

noncomputable abbrev qz615 := (Real.log (Enclosure.sfrac Bool.false 22 1))

noncomputable abbrev qz60 := (@HMul.hMul Real Real Real qz269 qz279 qz615)

noncomputable def ep363 := @Enclosure.Complex.IsNear.of_eq qz593 (Complex.mk (@HMul.hMul Real Real Real qz0 qz59 (Real.cos qz60)) (@HMul.hMul Real Real Real qz0 qz59 (@Neg.neg Real Real.instNeg (Real.sin qz60)))) Bool.false 20735135307 137438953472 16447099758249 108486063533588480 Bool.true 41408345325 274877906944 16446990434659 108486063533588480 (BSN.cpow_neg_s_mk qz12 138478 1000 22 qz13 rfl)

noncomputable abbrev qz616 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 22) qz14)

noncomputable def ep364 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz614) 4918257 1048576 1 1048576 111778 111779 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz614) (Real.sqrt qz616) Bool.false 4918257 1048576 1 1048576 (BSN.sqrt_natCast_div_one 22) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz616) Bool.false 4918257 1048576 1 1048576 4918257 1048576 1 1048576 (BSN.sqrt_enclosure 22 1 2459128 2459129 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep365 := BSN.log_dyadic_bound 6 38 4 3 316148320320 524288 197335 2667271104 699840 166961 44 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 6) (BSN.artanhQ 38) 0 3 2667271104 316148320320 699840 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep366 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz615 138478 1000 0 1 3480203401436407 1125899906842624 50000000039467 9866750000000000000 240965803312055384273 562949953421312000 3461950002732655613 4933375000000000000000 qz18 (BSN.isNear_log_sfrac 22 1 3480203401436407 1125899906842624 50000000039467 9866750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz616) Bool.false 58388124189833310502912 18889465931478580854784 1000000000789340 197335000000000000000 3480203401436407 1125899906842624 50000000039467 9866750000000000000 (BSN.log_rat_reduce_isNear 22 1 4 44 32 166961 524288 24973259072661432 36028797018963968 197335 1000000000000000 rfl rfl rfl rfl (ep365 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep367 := nat_lit 288106372391829241142742908721666753249780587966506845248633312786414221459456

noncomputable def ep368 := nat_lit 64990859780937893179396965519938774024145138181796994471927357951222808576

noncomputable def ep369 := nat_lit 864189135455925847641869932233960382201293473623156941756956083643340218761216

noncomputable def ep370 := BSN.cos_dyadic_bound_f 1685025724 2147483648 3 2 1048576 395056 ep367 ep72 ep368 ep369 ep75 ep368 742008 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1685025724) qz20 0 2 ep367 ep72 ep368 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1685025724) qz21 0 2 ep369 ep75 ep368 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz353 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 56104223) qz553)

noncomputable def ep371 := @Enclosure.Real.IsNear.cos_image qz60 qz353 Bool.false 56104223 131072 737 1048576 Bool.false 742008 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz60 Bool.false 240965803312055384273 562949953421312000 3461950002732655613 4933375000000000000000 56104223 131072 737 1048576 (ep366 rfl) rfl) (Enclosure.sfrac_false_div 56104223 131072) (BSN.cos_reduce0 qz353 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14821643017539588980736) qz305) 226375608064910080 72057594037927936 Bool.false 742008 1048576 68 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q0 56104223 131072 226375608064910080 72057594037927936 68 14821643017539588980736 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 742008 1048576 14821643017539588980736 18889465931478580854784 1685025724 2147483648 395056 394670 (ep370 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep372 := nat_lit 8061690876046903671638299962862878976

noncomputable def ep373 := BSN.sin_dyadic_bound_f 1685025724 2147483648 2 1 1048576 395056 ep372 ep58 ep372 ep372 ep59 ep372 740900 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1685025724) qz15 0 1 ep372 ep58 ep372 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1685025724) qz16 0 1 ep372 ep59 ep372 rfl rfl rfl rfl) rfl rfl

noncomputable def ep374 := @Enclosure.Real.IsNear.sin_image qz60 qz353 Bool.false 56104223 131072 737 1048576 Bool.false 740900 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz60 Bool.false 240965803312055384273 562949953421312000 3461950002732655613 4933375000000000000000 56104223 131072 737 1048576 (ep366 rfl) rfl) (Enclosure.sfrac_false_div 56104223 131072) (BSN.sin_reduce0 qz353 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14821643017539588980736) qz305) 226375608064910080 72057594037927936 Bool.false 740900 1048576 68 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q0 56104223 131072 226375608064910080 72057594037927936 68 14821643017539588980736 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 740900 1048576 14821643017539588980736 18889465931478580854784 1685025724 2147483648 395056 394670 (ep373 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz354 := (@Enclosure.Real.IsNear.recentre' qz59 Bool.false 223557 1048576 1 1048576 223557 1048576 1 1048576 (ep364 rfl rfl) rfl)

noncomputable def ep375 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz59 (Real.cos qz60)) (@HMul.hMul Real Real Real qz0 qz59 (@Neg.neg Real Real.instNeg (Real.sin qz60))) Bool.false 20735135307 137438953472 16447099758249 108486063533588480 Bool.true 41408345325 274877906944 16446990434659 108486063533588480 (@Enclosure.Real.IsNear.mulLit_ff qz59 (Real.cos qz60) 223557 1048576 1 1048576 92751 131072 146484471 206920744960 20735135307 137438953472 16447099758249 108486063533588480 qz354 (@Enclosure.Real.IsNear.recentre' (Real.cos qz60) Bool.false 742008 1048576 146484471 206920744960 92751 131072 146484471 206920744960 (ep371 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz59 (@Neg.neg Real Real.instNeg (Real.sin qz60)) 223557 1048576 1 1048576 185225 262144 146484471 206920744960 41408345325 274877906944 16446990434659 108486063533588480 qz354 (@Enclosure.Real.IsNear.neg (Real.sin qz60) Bool.false 185225 262144 146484471 206920744960 (@Enclosure.Real.IsNear.recentre' (Real.sin qz60) Bool.false 740900 1048576 146484471 206920744960 185225 262144 146484471 206920744960 (ep374 rfl rfl) rfl)) rfl)

noncomputable def ep376 := @ep285 20735135307 137438953472 16447099758249 108486063533588480 Bool.true 41408345325 274877906944 16446990434659 108486063533588480 Bool.false 67198569961415671545856 488933946773 1099511627776 1081982259491521 216972127067176960 Bool.true 22198300849794952724480 80756948045 1099511627776 1081918098384291 216972127067176960 (ep286 (BSN.head_sum_c_succ qz5 21 22 rfl rfl) (ep362 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep363 ep375) rfl rfl

noncomputable abbrev qz617 := (@Nat.cast Real Real.instNatCast 23)

noncomputable abbrev qz61 := (@Inv.inv Real Real.instInv (Real.sqrt qz617))

noncomputable abbrev qz618 := (Real.log (Enclosure.sfrac Bool.false 23 1))

noncomputable abbrev qz62 := (@HMul.hMul Real Real Real qz269 qz279 qz618)

noncomputable def ep377 := @Enclosure.Complex.IsNear.of_eq qz592 (Complex.mk (@HMul.hMul Real Real Real qz0 qz61 (Real.cos qz62)) (@HMul.hMul Real Real Real qz0 qz61 (@Neg.neg Real Real.instNeg (Real.sin qz62)))) Bool.false 181548684549 1099511627776 32191806413229 216972127067176960 Bool.true 17500841649 137438953472 8038578240141 54243031766794240 (BSN.cpow_neg_s_mk qz12 138478 1000 23 qz13 rfl)

noncomputable abbrev qz619 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 23) qz14)

noncomputable def ep378 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz617) 5028793 1048576 1 1048576 109321 109322 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz617) (Real.sqrt qz619) Bool.false 5028793 1048576 1 1048576 (BSN.sqrt_natCast_div_one 23) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz619) Bool.false 5028793 1048576 1 1048576 5028793 1048576 1 1048576 (BSN.sqrt_enclosure 23 1 2514396 2514397 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep379 := BSN.log_dyadic_bound 7 39 4 3 369468094905 524288 197335 4046006391 1764735 190266 46 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 7) (BSN.artanhQ 39) 0 3 4046006391 369468094905 1764735 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep380 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz618 138478 1000 0 1 3530250507853047 1125899906842624 50000000039467 9866750000000000000 244431014913237121233 562949953421312000 3461950002732655613 4933375000000000000000 qz18 (BSN.isNear_log_sfrac 23 1 3530250507853047 1125899906842624 50000000039467 9866750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz619) Bool.false 59227775304360265777152 18889465931478580854784 1000000000789340 197335000000000000000 3530250507853047 1125899906842624 50000000039467 9866750000000000000 (BSN.log_rat_reduce_isNear 23 1 4 46 32 190266 524288 24973259072661432 36028797018963968 197335 1000000000000000 rfl rfl rfl rfl (ep379 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep381 := nat_lit 141528127787456317213331400349179111568439618323197218972695242326309362114081

noncomputable def ep382 := nat_lit 15686705998747645254568744689669867807267079535858320371822547739493703201

noncomputable def ep383 := nat_lit 424553009950371456349485063558157994969704320810519940277342081883449098935841

noncomputable def ep384 := BSN.cos_dyadic_bound_f 1410722099 2147483648 3 2 1048576 395056 ep381 ep72 ep382 ep383 ep75 ep382 830343 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1410722099) qz20 0 2 ep381 ep72 ep382 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1410722099) qz21 0 2 ep383 ep75 ep382 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz355 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 113822061) qz31)

noncomputable def ep385 := @Enclosure.Real.IsNear.cos_image qz62 qz355 Bool.false 113822061 262144 737 1048576 Bool.false 830343 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz62 Bool.false 244431014913237121233 562949953421312000 3461950002732655613 4933375000000000000000 113822061 262144 737 1048576 (ep380 rfl) rfl) (Enclosure.sfrac_false_div 113822061 262144) (BSN.cos_reduce0 qz355 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 24817685639830198812672) qz321) 226375608064910080 72057594037927936 Bool.false 830343 1048576 69 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q0 113822061 262144 226375608064910080 72057594037927936 69 24817685639830198812672 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 830343 1048576 24817685639830198812672 37778931862957161709568 1410722099 2147483648 395056 394670 (ep384 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep386 := nat_lit 3960644644341075602748825163583571601

noncomputable def ep387 := BSN.sin_dyadic_bound_f 1410722099 2147483648 2 1 1048576 395056 ep386 ep58 ep386 ep386 ep59 ep386 640344 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1410722099) qz15 0 1 ep386 ep58 ep386 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1410722099) qz16 0 1 ep386 ep59 ep386 rfl rfl rfl rfl) rfl rfl

noncomputable def ep388 := @Enclosure.Real.IsNear.sin_image qz62 qz355 Bool.false 113822061 262144 737 1048576 Bool.false 640344 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz62 Bool.false 244431014913237121233 562949953421312000 3461950002732655613 4933375000000000000000 113822061 262144 737 1048576 (ep380 rfl) rfl) (Enclosure.sfrac_false_div 113822061 262144) (BSN.sin_reduce0 qz355 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 24817685639830198812672) qz321) 226375608064910080 72057594037927936 Bool.false 640344 1048576 69 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q0 113822061 262144 226375608064910080 72057594037927936 69 24817685639830198812672 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 640344 1048576 24817685639830198812672 37778931862957161709568 1410722099 2147483648 395056 394670 (ep387 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz356 := (@Enclosure.Real.IsNear.recentre' qz61 Bool.false 218643 1048576 1 1048576 218643 1048576 1 1048576 (ep378 rfl rfl) rfl)

noncomputable def ep389 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz61 (Real.cos qz62)) (@HMul.hMul Real Real Real qz0 qz61 (@Neg.neg Real Real.instNeg (Real.sin qz62))) Bool.false 181548684549 1099511627776 32191806413229 216972127067176960 Bool.true 17500841649 137438953472 8038578240141 54243031766794240 (@Enclosure.Real.IsNear.mulLit_ff qz61 (Real.cos qz62) 218643 1048576 1 1048576 830343 1048576 146484471 206920744960 181548684549 1099511627776 32191806413229 216972127067176960 qz356 (@Enclosure.Real.IsNear.recentre' (Real.cos qz62) Bool.false 830343 1048576 146484471 206920744960 830343 1048576 146484471 206920744960 (ep385 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz61 (@Neg.neg Real Real.instNeg (Real.sin qz62)) 218643 1048576 1 1048576 80043 131072 146484471 206920744960 17500841649 137438953472 8038578240141 54243031766794240 qz356 (@Enclosure.Real.IsNear.neg (Real.sin qz62) Bool.false 80043 131072 146484471 206920744960 (@Enclosure.Real.IsNear.recentre' (Real.sin qz62) Bool.false 640344 1048576 146484471 206920744960 80043 131072 146484471 206920744960 (ep388 rfl rfl) rfl)) rfl)

noncomputable def ep390 := @ep283 181548684549 1099511627776 32191806413229 216972127067176960 Bool.true 17500841649 137438953472 8038578240141 54243031766794240 Bool.false 737203449360387902799872 335241315661 549755813888 111417406590475 21697212706717696 Bool.true 30341529313839482404864 220763681237 1099511627776 222814482268971 43394425413435392 (ep284 (BSN.head_sum_c_succ qz5 22 23 rfl rfl) (ep376 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep377 ep389) rfl rfl

noncomputable abbrev qz620 := (@Nat.cast Real Real.instNatCast 24)

noncomputable abbrev qz63 := (@Inv.inv Real Real.instInv (Real.sqrt qz620))

noncomputable abbrev qz621 := (Real.log (Enclosure.sfrac Bool.false 24 1))

noncomputable abbrev qz64 := (@HMul.hMul Real Real Real qz269 qz279 qz621)

noncomputable def ep391 := @Enclosure.Complex.IsNear.of_eq qz591 (Complex.mk (@HMul.hMul Real Real Real qz0 qz63 (Real.cos qz64)) (@HMul.hMul Real Real Real qz0 qz63 (@Neg.neg Real Real.instNeg (Real.sin qz64)))) Bool.false 54114410175 274877906944 1577655052917 10848606353358848 Bool.true 7413668843 137438953472 49075338925 339018948542464 (BSN.cpow_neg_s_mk qz12 138478 1000 24 qz13 rfl)

noncomputable abbrev qz622 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 24) qz14)

noncomputable def ep392 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz620) 5136953 1048576 1 1048576 107019 107020 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz620) (Real.sqrt qz622) Bool.false 5136953 1048576 1 1048576 (BSN.sqrt_natCast_div_one 24) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz622) Bool.false 5136953 1048576 1 1048576 5136953 1048576 1 1048576 (BSN.sqrt_enclosure 24 1 2568476 2568477 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep393 := BSN.log_dyadic_bound 8 40 4 3 430080000000 524288 197335 5875957760 3932160 212580 48 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 8) (BSN.artanhQ 40) 0 3 5875957760 430080000000 3932160 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep394 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz621 138478 1000 0 1 3578169457974519 1125899906842624 50000000039467 9866750000000000000 247748875100697721041 562949953421312000 3461950002732655613 4933375000000000000000 qz18 (BSN.isNear_log_sfrac 24 1 3578169457974519 1125899906842624 50000000039467 9866750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz622) Bool.false 60031721881041427759104 18889465931478580854784 1000000000789340 197335000000000000000 3578169457974519 1125899906842624 50000000039467 9866750000000000000 (BSN.log_rat_reduce_isNear 24 1 4 48 32 212580 524288 24973259072661432 36028797018963968 197335 1000000000000000 rfl rfl rfl rfl (ep393 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep395 := nat_lit 108793832567181640083621215413909681

noncomputable def ep396 := BSN.cos_dyadic_bound_f 574316203 2147483648 2 1 1048576 395056 ep395 ep62 ep395 ep395 ep63 ep395 1011300 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 574316203) qz20 0 1 ep395 ep62 ep395 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 574316203) qz21 0 1 ep395 ep63 ep395 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz357 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 28841765) (@Nat.cast Real Real.instNatCast 65536))

noncomputable abbrev qz623 := (@Nat.cast Real Real.instNatCast 9444732965739290427392)

noncomputable def ep397 := @Enclosure.Real.IsNear.cos_image qz64 qz357 Bool.false 28841765 65536 737 1048576 Bool.false 1011300 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz64 Bool.false 247748875100697721041 562949953421312000 3461950002732655613 4933375000000000000000 28841765 65536 737 1048576 (ep394 rfl) rfl) (Enclosure.sfrac_false_div 28841765 65536) (BSN.cos_reduce0 qz357 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2525869374892073287680) qz623) 226375608064910080 72057594037927936 Bool.false 1011300 1048576 70 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q0 28841765 65536 226375608064910080 72057594037927936 70 2525869374892073287680 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1011300 1048576 2525869374892073287680 9444732965739290427392 574316203 2147483648 395056 394670 (ep396 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep398 := BSN.sin_dyadic_bound_f 574316203 2147483648 2 1 1048576 395056 ep395 ep58 ep395 ep395 ep59 ep395 277096 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 574316203) qz15 0 1 ep395 ep58 ep395 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 574316203) qz16 0 1 ep395 ep59 ep395 rfl rfl rfl rfl) rfl rfl

noncomputable def ep399 := @Enclosure.Real.IsNear.sin_image qz64 qz357 Bool.false 28841765 65536 737 1048576 Bool.false 277096 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz64 Bool.false 247748875100697721041 562949953421312000 3461950002732655613 4933375000000000000000 28841765 65536 737 1048576 (ep394 rfl) rfl) (Enclosure.sfrac_false_div 28841765 65536) (BSN.sin_reduce0 qz357 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2525869374892073287680) qz623) 226375608064910080 72057594037927936 Bool.false 277096 1048576 70 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q0 28841765 65536 226375608064910080 72057594037927936 70 2525869374892073287680 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 277096 1048576 2525869374892073287680 9444732965739290427392 574316203 2147483648 395056 394670 (ep398 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz358 := (@Enclosure.Real.IsNear.recentre' qz63 Bool.false 214039 1048576 1 1048576 214039 1048576 1 1048576 (ep392 rfl rfl) rfl)

noncomputable def ep400 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz63 (Real.cos qz64)) (@HMul.hMul Real Real Real qz0 qz63 (@Neg.neg Real Real.instNeg (Real.sin qz64))) Bool.false 54114410175 274877906944 1577655052917 10848606353358848 Bool.true 7413668843 137438953472 49075338925 339018948542464 (@Enclosure.Real.IsNear.mulLit_ff qz63 (Real.cos qz64) 214039 1048576 1 1048576 252825 262144 146484471 206920744960 54114410175 274877906944 1577655052917 10848606353358848 qz358 (@Enclosure.Real.IsNear.recentre' (Real.cos qz64) Bool.false 1011300 1048576 146484471 206920744960 252825 262144 146484471 206920744960 (ep397 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz63 (@Neg.neg Real Real.instNeg (Real.sin qz64)) 214039 1048576 1 1048576 34637 131072 146484471 206920744960 7413668843 137438953472 49075338925 339018948542464 qz358 (@Enclosure.Real.IsNear.neg (Real.sin qz64) Bool.false 34637 131072 146484471 206920744960 (@Enclosure.Real.IsNear.recentre' (Real.sin qz64) Bool.false 277096 1048576 146484471 206920744960 34637 131072 146484471 206920744960 (ep399 rfl rfl) rfl)) rfl)

noncomputable def ep401 := @ep281 54114410175 274877906944 1577655052917 10848606353358848 Bool.true 7413668843 137438953472 49075338925 339018948542464 Bool.false 121900142778874681360384 443470136011 549755813888 114572716696309 21697212706717696 Bool.true 38492944411198626988032 280073031981 1099511627776 229096125651371 43394425413435392 (ep282 (BSN.head_sum_c_succ qz5 23 24 rfl rfl) (ep390 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep391 ep400) rfl rfl

theorem EMRow48.d8 : Enclosure.Complex.IsNear qz48 Bool.false 443470136011 549755813888 114572716696309 21697212706717696 Bool.true 280073031981 1099511627776 229096125651371 43394425413435392 := ep280 (BSN.head_sum_c_succ qz5 24 25 rfl rfl) (ep401 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz65 := (BSN.headSumC qz273 33)

noncomputable abbrev qz624 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 32) qz7)

noncomputable def ep402 := @Enclosure.Complex.IsNear.of_eq qz65 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 32) qz624) Bool.false 106826879495 137438953472 688771609329129 108486063533588480 Bool.true 14291011597 1099511627776 1377301595172203 216972127067176960

noncomputable def ep403 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 32) qz624 Bool.false 998737178179 1099511627776 1350236840647959 216972127067176960 Bool.false 116121127053 1099511627776 1350009812650509 216972127067176960 Bool.true

noncomputable abbrev qz625 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 31) qz7)

noncomputable def ep404 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 32) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 31) qz625) Bool.false 998737178179 1099511627776 1350236840647959 216972127067176960 Bool.false 116121127053 1099511627776 1350009812650509 216972127067176960

noncomputable def ep405 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 31) qz625 Bool.false 1079203380035 1099511627776 1322565106083089 216972127067176960 Bool.true 64218580109 1099511627776 1322233428572449 216972127067176960 Bool.true

noncomputable abbrev qz626 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 30) qz7)

noncomputable def ep406 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 31) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 30) qz626) Bool.false 1079203380035 1099511627776 1322565106083089 216972127067176960 Bool.true 64218580109 1099511627776 1322233428572449 216972127067176960

noncomputable def ep407 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 30) qz626 Bool.false 110576225323 137438953472 129432095047487 21697212706717696 Bool.true 3547569875 34359738368 129413903444243 21697212706717696 Bool.false

noncomputable abbrev qz627 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 29) qz7)

noncomputable def ep408 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 30) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 29) qz627) Bool.false 110576225323 137438953472 129432095047487 21697212706717696 Bool.true 3547569875 34359738368 129413903444243 21697212706717696

noncomputable def ep409 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 29) qz627 Bool.false 837997562879 1099511627776 1265750840785989 216972127067176960 Bool.false 21314798015 274877906944 632707354021527 108486063533588480 Bool.false

noncomputable abbrev qz628 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 28) qz7)

noncomputable def ep410 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 29) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 28) qz628) Bool.false 837997562879 1099511627776 1265750840785989 216972127067176960 Bool.false 21314798015 274877906944 632707354021527 108486063533588480

noncomputable def ep411 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 28) qz628 Bool.false 16112016173 17179869184 61826526387303 10848606353358848 Bool.false 161816098339 1099511627776 247262104461851 43394425413435392 Bool.true

noncomputable abbrev qz629 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 27) qz7)

noncomputable def ep412 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 28) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 27) qz629) Bool.false 16112016173 17179869184 61826526387303 10848606353358848 Bool.false 161816098339 1099511627776 247262104461851 43394425413435392

noncomputable def ep413 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 27) qz629 Bool.false 291913039085 274877906944 7542728109519 1356075794169856 Bool.false 114156041 1099511627776 241318366226257 43394425413435392 Bool.true

noncomputable abbrev qz630 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 26) qz7)

noncomputable def ep414 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 27) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 26) qz630) Bool.false 291913039085 274877906944 7542728109519 1356075794169856 Bool.false 114156041 1099511627776 241318366226257 43394425413435392

noncomputable def ep415 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 26) qz630 Bool.false 1092518224217 1099511627776 1176640746455781 216972127067176960 Bool.true 202004945511 1099511627776 1176274225109521 216972127067176960 Bool.false

noncomputable def ep416 := nat_lit 1283847123093549838499840

noncomputable abbrev qz631 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 25) qz7)

noncomputable def ep417 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 26) (@HAdd.hAdd Complex Complex Complex qz4 qz48 qz631) Bool.false 1092518224217 1099511627776 1176640746455781 216972127067176960 Bool.true 202004945511 1099511627776 1176274225109521 216972127067176960

noncomputable def ep418 := @Enclosure.Complex.IsNear.addLitP qz48 qz631 Bool.false 443470136011 549755813888 114572716696309 21697212706717696 Bool.true 280073031981 1099511627776 229096125651371 43394425413435392 Bool.false

noncomputable abbrev qz632 := (@Nat.cast Real Real.instNatCast 25)

noncomputable abbrev qz66 := (@Inv.inv Real Real.instInv (Real.sqrt qz632))

noncomputable abbrev qz633 := (Real.log (Enclosure.sfrac Bool.false 25 1))

noncomputable abbrev qz67 := (@HMul.hMul Real Real Real qz269 qz279 qz633)

noncomputable def ep419 := @Enclosure.Complex.IsNear.of_eq qz631 (Complex.mk (@HMul.hMul Real Real Real qz0 qz66 (Real.cos qz67)) (@HMul.hMul Real Real Real qz0 qz66 (@Neg.neg Real Real.instNeg (Real.sin qz67)))) Bool.false 205577952195 1099511627776 30913579492691 216972127067176960 Bool.false 39034043235 549755813888 15396798426333 108486063533588480 (BSN.cpow_neg_s_mk qz12 138478 1000 25 qz13 rfl)

noncomputable abbrev qz634 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 25) qz14)

noncomputable def ep420 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz632) 5242881 1048576 1 1048576 104857 104858 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz632) (Real.sqrt qz634) Bool.false 5242881 1048576 1 1048576 (BSN.sqrt_natCast_div_one 25) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz634) Bool.false 5242881 1048576 1 1048576 5242881 1048576 1 1048576 (BSN.sqrt_enclosure 25 1 2621440 2621441 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep421 := BSN.log_dyadic_bound 9 41 5 4 7545754341519345 524288 197335 124828057765224 4519905705 233982 50 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 9) (BSN.artanhQ 41) 0 4 124828057765224 7545754341519345 4519905705 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep422 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz633 138478 1000 0 1 3624129903009015 1125899906842624 50000000039467 9866750000000000000 50186226070888237917 112589990684262400 3461950002732655613 4933375000000000000000 qz18 (BSN.isNear_log_sfrac 25 1 3624129903009015 1125899906842624 50000000039467 9866750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz634) Bool.false 60802810194841294602240 18889465931478580854784 1000000000789340 197335000000000000000 3624129903009015 1125899906842624 50000000039467 9866750000000000000 (BSN.log_rat_reduce_isNear 25 1 4 50 32 233982 524288 24973259072661432 36028797018963968 197335 1000000000000000 rfl rfl rfl rfl (ep421 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep423 := nat_lit 2913431517040315854295641807853674580291599231618502894473903490164369047253985

noncomputable def ep424 := nat_lit 2049254819247405061725790377915724886888481373836641914392977356851603141601

noncomputable def ep425 := nat_lit 7627098036826807629245791550433474631899226160586057779570253844233683004388321

noncomputable def ep426 := BSN.sin_dyadic_bound_f 2593877701 2147483648 3 2 1048576 395056 ep423 ep79 ep424 ep425 ep81 ep424 980273 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2593877701) qz15 0 2 ep423 ep79 ep424 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2593877701) qz16 0 2 ep425 ep81 ep424 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz359 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 116848913) qz31)

noncomputable def ep427 := @Enclosure.Real.IsNear.cos_image qz67 qz359 Bool.false 116848913 262144 737 1048576 Bool.false 980273 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz67 Bool.false 50186226070888237917 112589990684262400 3461950002732655613 4933375000000000000000 116848913 262144 737 1048576 (ep422 rfl) rfl) (Enclosure.sfrac_false_div 116848913 262144) (BSN.cos_reduce3 qz359 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 45631979093636180606976) qz321) 226375608064910080 72057594037927936 Bool.false 980273 1048576 70 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q3 116848913 262144 226375608064910080 72057594037927936 70 45631979093636180606976 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 980273 1048576 45631979093636180606976 37778931862957161709568 2593877701 2147483648 395056 394670 (ep426 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep428 := nat_lit 1619483844942063210191679133420003977889505564843095671114121040027694627648481

noncomputable def ep429 := nat_lit 4854353025187694820451585819504180483894739731781613729513577165369380676662241

noncomputable def ep430 := BSN.cos_dyadic_bound_f 2593877701 2147483648 3 2 1048576 395056 ep428 ep72 ep424 ep429 ep75 ep424 372258 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2593877701) qz20 0 2 ep428 ep72 ep424 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2593877701) qz21 0 2 ep429 ep75 ep424 rfl rfl rfl rfl) rfl rfl

noncomputable def ep431 := @Enclosure.Real.IsNear.sin_image qz67 qz359 Bool.false 116848913 262144 737 1048576 Bool.true 372258 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz67 Bool.false 50186226070888237917 112589990684262400 3461950002732655613 4933375000000000000000 116848913 262144 737 1048576 (ep422 rfl) rfl) (Enclosure.sfrac_false_div 116848913 262144) (BSN.sin_reduce3 qz359 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 45631979093636180606976) qz321) 226375608064910080 72057594037927936 Bool.false 372258 1048576 70 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q3 116848913 262144 226375608064910080 72057594037927936 70 45631979093636180606976 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 372258 1048576 45631979093636180606976 37778931862957161709568 2593877701 2147483648 395056 394670 (ep430 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz360 := (@Enclosure.Real.IsNear.recentre' qz66 Bool.false 209715 1048576 1 1048576 209715 1048576 1 1048576 (ep420 rfl rfl) rfl)

noncomputable def ep432 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz66 (Real.cos qz67)) (@HMul.hMul Real Real Real qz0 qz66 (@Neg.neg Real Real.instNeg (Real.sin qz67))) Bool.false 205577952195 1099511627776 30913579492691 216972127067176960 Bool.false 39034043235 549755813888 15396798426333 108486063533588480 (@Enclosure.Real.IsNear.mulLit_ff qz66 (Real.cos qz67) 209715 1048576 1 1048576 980273 1048576 146484471 206920744960 205577952195 1099511627776 30913579492691 216972127067176960 qz360 (@Enclosure.Real.IsNear.recentre' (Real.cos qz67) Bool.false 980273 1048576 146484471 206920744960 980273 1048576 146484471 206920744960 (ep427 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz66 (@Neg.neg Real Real.instNeg (Real.sin qz67)) 209715 1048576 1 1048576 186129 524288 146484471 206920744960 39034043235 549755813888 15396798426333 108486063533588480 qz360 (@Enclosure.Real.IsNear.neg (Real.sin qz67) Bool.true 186129 524288 146484471 206920744960 (@Enclosure.Real.IsNear.recentre' (Real.sin qz67) Bool.true 372258 1048576 146484471 206920744960 186129 524288 146484471 206920744960 (ep431 rfl rfl) rfl)) rfl)

noncomputable def ep433 := @ep418 205577952195 1099511627776 30913579492691 216972127067176960 Bool.false 39034043235 549755813888 15396798426333 108486063533588480 Bool.false 600618245541889306525696 1092518224217 1099511627776 1176640746455781 216972127067176960 Bool.true 111053393228800897056768 202004945511 1099511627776 1176274225109521 216972127067176960 EMRow48.d8 (ep419 ep432) rfl rfl

noncomputable abbrev qz635 := (@Nat.cast Real Real.instNatCast 26)

noncomputable abbrev qz68 := (@Inv.inv Real Real.instInv (Real.sqrt qz635))

noncomputable abbrev qz636 := (Real.log (Enclosure.sfrac Bool.false 26 1))

noncomputable abbrev qz69 := (@HMul.hMul Real Real Real qz269 qz279 qz636)

noncomputable def ep434 := @Enclosure.Complex.IsNear.of_eq qz630 (Complex.mk (@HMul.hMul Real Real Real qz0 qz68 (Real.cos qz69)) (@HMul.hMul Real Real Real qz0 qz68 (@Neg.neg Real Real.instNeg (Real.sin qz69)))) Bool.false 75133932123 1099511627776 30195751067259 216972127067176960 Bool.false 12632443847 68719476736 7579401505441 54243031766794240 (BSN.cpow_neg_s_mk qz12 138478 1000 26 qz13 rfl)

noncomputable abbrev qz637 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26) qz14)

noncomputable def ep435 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz635) 5346709 1048576 1 1048576 102821 102822 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz635) (Real.sqrt qz637) Bool.false 5346709 1048576 1 1048576 (BSN.sqrt_natCast_div_one 26) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz637) Bool.false 5346709 1048576 1 1048576 5346709 1048576 1 1048576 (BSN.sqrt_enclosure 26 1 2673354 2673355 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep436 := BSN.log_dyadic_bound 10 42 5 4 9150106136613120 524288 197335 179034245376000 10500000000 254545 52 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 10) (BSN.artanhQ 42) 0 4 179034245376000 9150106136613120 10500000000 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep437 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz636 138478 1000 0 1 3668288609262839 1125899906842624 50000000039467 9866750000000000000 253988635016749709521 562949953421312000 3461950002732655613 4933375000000000000000 qz18 (BSN.isNear_log_sfrac 26 1 3668288609262839 1125899906842624 50000000039467 9866750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz637) Bool.false 61543670347942250676224 18889465931478580854784 1000000000789340 197335000000000000000 3668288609262839 1125899906842624 50000000039467 9866750000000000000 (BSN.log_rat_reduce_isNear 26 1 4 52 32 254545 524288 24973259072661432 36028797018963968 197335 1000000000000000 rfl rfl rfl rfl (ep436 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep438 := nat_lit 341226117361191499380416738216755456

noncomputable def ep439 := BSN.sin_dyadic_bound_f 764294204 2147483648 2 1 1048576 395056 ep438 ep58 ep438 ep438 ep59 ep438 365361 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 764294204) qz15 0 1 ep438 ep58 ep438 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 764294204) qz16 0 1 ep438 ep59 ep438 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz361 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 236545349) qz17)

noncomputable def ep440 := @Enclosure.Real.IsNear.cos_image qz69 qz361 Bool.false 236545349 524288 737 1048576 Bool.false 365361 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz69 Bool.false 253988635016749709521 562949953421312000 3461950002732655613 4933375000000000000000 236545349 524288 737 1048576 (ep437 rfl) rfl) (Enclosure.sfrac_false_div 236545349 524288) (BSN.cos_reduce3 qz361 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26891211678055397326848) qz19) 226375608064910080 72057594037927936 Bool.false 365361 1048576 71 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q3 236545349 524288 226375608064910080 72057594037927936 71 26891211678055397326848 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 365361 1048576 26891211678055397326848 75557863725914323419136 764294204 2147483648 395056 394670 (ep439 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep441 := BSN.cos_dyadic_bound_f 764294204 2147483648 2 1 1048576 395056 ep438 ep62 ep438 ep438 ep63 ep438 982864 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 764294204) qz20 0 1 ep438 ep62 ep438 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 764294204) qz21 0 1 ep438 ep63 ep438 rfl rfl rfl rfl) rfl rfl

noncomputable def ep442 := @Enclosure.Real.IsNear.sin_image qz69 qz361 Bool.false 236545349 524288 737 1048576 Bool.true 982864 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz69 Bool.false 253988635016749709521 562949953421312000 3461950002732655613 4933375000000000000000 236545349 524288 737 1048576 (ep437 rfl) rfl) (Enclosure.sfrac_false_div 236545349 524288) (BSN.sin_reduce3 qz361 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26891211678055397326848) qz19) 226375608064910080 72057594037927936 Bool.false 982864 1048576 71 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q3 236545349 524288 226375608064910080 72057594037927936 71 26891211678055397326848 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 982864 1048576 26891211678055397326848 75557863725914323419136 764294204 2147483648 395056 394670 (ep441 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz362 := (@Enclosure.Real.IsNear.recentre' qz68 Bool.false 205643 1048576 1 1048576 205643 1048576 1 1048576 (ep435 rfl rfl) rfl)

noncomputable def ep443 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz68 (Real.cos qz69)) (@HMul.hMul Real Real Real qz0 qz68 (@Neg.neg Real Real.instNeg (Real.sin qz69))) Bool.false 75133932123 1099511627776 30195751067259 216972127067176960 Bool.false 12632443847 68719476736 7579401505441 54243031766794240 (@Enclosure.Real.IsNear.mulLit_ff qz68 (Real.cos qz69) 205643 1048576 1 1048576 365361 1048576 146484471 206920744960 75133932123 1099511627776 30195751067259 216972127067176960 qz362 (@Enclosure.Real.IsNear.recentre' (Real.cos qz69) Bool.false 365361 1048576 146484471 206920744960 365361 1048576 146484471 206920744960 (ep440 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz68 (@Neg.neg Real Real.instNeg (Real.sin qz69)) 205643 1048576 1 1048576 61429 65536 146484471 206920744960 12632443847 68719476736 7579401505441 54243031766794240 qz362 (@Enclosure.Real.IsNear.neg (Real.sin qz69) Bool.true 61429 65536 146484471 206920744960 (@Enclosure.Real.IsNear.recentre' (Real.sin qz69) Bool.true 982864 1048576 146484471 206920744960 61429 65536 146484471 206920744960 (ep442 rfl rfl) rfl)) rfl)

noncomputable def ep444 := @ep415 75133932123 1099511627776 30195751067259 216972127067176960 Bool.false 12632443847 68719476736 7579401505441 54243031766794240 Bool.false ep416 291913039085 274877906944 7542728109519 1356075794169856 Bool.false 7844743403773362176 114156041 1099511627776 241318366226257 43394425413435392 (ep417 (BSN.head_sum_c_succ qz5 25 26 rfl rfl) (ep433 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep434 ep443) rfl rfl

noncomputable abbrev qz638 := (@Nat.cast Real Real.instNatCast 27)

noncomputable abbrev qz70 := (@Inv.inv Real Real.instInv (Real.sqrt qz638))

noncomputable abbrev qz639 := (Real.log (Enclosure.sfrac Bool.false 27 1))

noncomputable abbrev qz71 := (@HMul.hMul Real Real Real qz269 qz279 qz639)

noncomputable def ep445 := @Enclosure.Complex.IsNear.of_eq qz629 (Complex.mk (@HMul.hMul Real Real Real qz0 qz70 (Real.cos qz71)) (@HMul.hMul Real Real Real qz0 qz70 (@Neg.neg Real Real.instNeg (Real.sin qz71)))) Bool.true 34120780317 274877906944 1484701511151 10848606353358848 Bool.false 80850971149 549755813888 2971869117797 21697212706717696 (BSN.cpow_neg_s_mk qz12 138478 1000 27 qz13 rfl)

noncomputable abbrev qz640 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 27) qz14)

noncomputable def ep446 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz638) 5448561 1048576 1 1048576 100899 100900 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz638) (Real.sqrt qz640) Bool.false 5448561 1048576 1 1048576 (BSN.sqrt_natCast_div_one 27) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz640) Bool.false 5448561 1048576 1 1048576 5448561 1048576 1 1048576 (BSN.sqrt_enclosure 27 1 2724280 2724281 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep447 := BSN.log_dyadic_bound 11 43 5 4 11045349262332945 524288 197335 250863800262504 22507682505 274332 54 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 11) (BSN.artanhQ 43) 0 4 250863800262504 11045349262332945 22507682505 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep448 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz639 138478 1000 0 1 3710780868205815 1125899906842624 50000000039467 9866750000000000000 51386151306740484957 112589990684262400 3461950002732655613 4933375000000000000000 qz18 (BSN.isNear_log_sfrac 27 1 3710780868205815 1125899906842624 50000000039467 9866750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz640) Bool.false 62256572154556490711040 18889465931478580854784 1000000000789340 197335000000000000000 3710780868205815 1125899906842624 50000000039467 9866750000000000000 (BSN.log_rat_reduce_isNear 27 1 4 54 32 274332 524288 24973259072661432 36028797018963968 197335 1000000000000000 rfl rfl rfl rfl (ep447 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep449 := nat_lit 435027646323698915559678553330028137868395457230221898893192990308350396621056

noncomputable def ep450 := nat_lit 148142745975533645650522503750462085146386293027084123370715225020396626176

noncomputable def ep451 := nat_lit 1304786653479145679387734614982583489434893599104611528432837540475010396610816

noncomputable def ep452 := BSN.cos_dyadic_bound_f 1867820118 2147483648 3 2 1048576 395056 ep449 ep72 ep450 ep451 ep75 ep450 676332 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1867820118) qz20 0 2 ep449 ep72 ep450 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1867820118) qz21 0 2 ep451 ep75 ep450 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz363 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 478570827) qz24)

noncomputable def ep453 := @Enclosure.Real.IsNear.cos_image qz71 qz363 Bool.false 478570827 1048576 737 1048576 Bool.true 676332 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz71 Bool.false 51386151306740484957 112589990684262400 3461950002732655613 4933375000000000000000 478570827 1048576 737 1048576 (ep448 rfl) rfl) (Enclosure.sfrac_false_div 478570827 1048576) (BSN.cos_reduce2 qz363 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 131436156064249302482944) qz25) 226375608064910080 72057594037927936 Bool.false 676332 1048576 72 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q2 478570827 1048576 226375608064910080 72057594037927936 72 131436156064249302482944 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 676332 1048576 131436156064249302482944 151115727451828646838272 1867820118 2147483648 395056 394670 (ep452 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep454 := nat_lit 782931249185877621090900977991050278494994713979977750709050810375014396616960

noncomputable def ep455 := nat_lit 2050294373898100048383211239256202362206177720711231210895390012046433253744896

noncomputable def ep456 := BSN.sin_dyadic_bound_f 1867820118 2147483648 3 2 1048576 395056 ep454 ep79 ep450 ep455 ep81 ep450 801302 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1867820118) qz15 0 2 ep454 ep79 ep450 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1867820118) qz16 0 2 ep455 ep81 ep450 rfl rfl rfl rfl) rfl rfl

noncomputable def ep457 := @Enclosure.Real.IsNear.sin_image qz71 qz363 Bool.false 478570827 1048576 737 1048576 Bool.true 801302 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz71 Bool.false 51386151306740484957 112589990684262400 3461950002732655613 4933375000000000000000 478570827 1048576 737 1048576 (ep448 rfl) rfl) (Enclosure.sfrac_false_div 478570827 1048576) (BSN.sin_reduce2 qz363 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 131436156064249302482944) qz25) 226375608064910080 72057594037927936 Bool.false 801302 1048576 72 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q2 478570827 1048576 226375608064910080 72057594037927936 72 131436156064249302482944 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 801302 1048576 131436156064249302482944 151115727451828646838272 1867820118 2147483648 395056 394670 (ep456 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz364 := (@Enclosure.Real.IsNear.recentre' qz70 Bool.false 201799 1048576 1 1048576 201799 1048576 1 1048576 (ep446 rfl rfl) rfl)

noncomputable def ep458 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz70 (Real.cos qz71)) (@HMul.hMul Real Real Real qz0 qz70 (@Neg.neg Real Real.instNeg (Real.sin qz71))) Bool.true 34120780317 274877906944 1484701511151 10848606353358848 Bool.false 80850971149 549755813888 2971869117797 21697212706717696 (@Enclosure.Real.IsNear.mulLit_ft qz70 (Real.cos qz71) 201799 1048576 1 1048576 169083 262144 146484471 206920744960 34120780317 274877906944 1484701511151 10848606353358848 qz364 (@Enclosure.Real.IsNear.recentre' (Real.cos qz71) Bool.true 676332 1048576 146484471 206920744960 169083 262144 146484471 206920744960 (ep453 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz70 (@Neg.neg Real Real.instNeg (Real.sin qz71)) 201799 1048576 1 1048576 400651 524288 146484471 206920744960 80850971149 549755813888 2971869117797 21697212706717696 qz364 (@Enclosure.Real.IsNear.neg (Real.sin qz71) Bool.true 400651 524288 146484471 206920744960 (@Enclosure.Real.IsNear.recentre' (Real.sin qz71) Bool.true 801302 1048576 146484471 206920744960 400651 524288 146484471 206920744960 (ep457 rfl rfl) rfl)) rfl)

noncomputable def ep459 := @ep413 34120780317 274877906944 1484701511151 10848606353358848 Bool.false 80850971149 549755813888 2971869117797 21697212706717696 Bool.false 70861396516513872084992 16112016173 17179869184 61826526387303 10848606353358848 Bool.false 88959340842537589932032 161816098339 1099511627776 247262104461851 43394425413435392 (ep414 (BSN.head_sum_c_succ qz5 26 27 rfl rfl) (ep444 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep445 ep458) rfl rfl

noncomputable abbrev qz641 := (@Nat.cast Real Real.instNatCast 28)

noncomputable abbrev qz72 := (@Inv.inv Real Real.instInv (Real.sqrt qz641))

noncomputable abbrev qz642 := (Real.log (Enclosure.sfrac Bool.false 28 1))

noncomputable abbrev qz73 := (@HMul.hMul Real Real Real qz269 qz279 qz642)

noncomputable def ep460 := @Enclosure.Complex.IsNear.of_eq qz628 (Complex.mk (@HMul.hMul Real Real Real qz0 qz72 (Real.cos qz73)) (@HMul.hMul Real Real Real qz0 qz72 (@Neg.neg Real Real.instNeg (Real.sin qz73)))) Bool.true 193171472193 1099511627776 29220313039929 216972127067176960 Bool.true 76556906279 1099511627776 29104185733799 216972127067176960 (BSN.cpow_neg_s_mk qz12 138478 1000 28 qz13 rfl)

noncomputable abbrev qz643 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 28) qz14)

noncomputable def ep461 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz641) 5548543 1048576 1 1048576 99081 99082 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz641) (Real.sqrt qz643) Bool.false 5548543 1048576 1 1048576 (BSN.sqrt_natCast_div_one 28) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz643) Bool.false 5548543 1048576 1 1048576 5548543 1048576 1 1048576 (BSN.sqrt_enclosure 28 1 2774271 2774272 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep462 := BSN.log_dyadic_bound 12 44 5 4 13275571325829120 524288 197335 344661139390464 45148078080 293399 56 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 12) (BSN.artanhQ 44) 0 4 344661139390464 13275571325829120 45148078080 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep463 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz642 138478 1000 0 1 3751726938922231 1125899906842624 50000000039467 9866750000000000000 259765821524036352209 562949953421312000 3461950002732655613 4933375000000000000000 qz18 (BSN.isNear_log_sfrac 28 1 3751726938922231 1125899906842624 50000000039467 9866750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz643) Bool.false 62943533227317076688896 18889465931478580854784 1000000000789340 197335000000000000000 3751726938922231 1125899906842624 50000000039467 9866750000000000000 (BSN.log_rat_reduce_isNear 28 1 4 56 32 293399 524288 24973259072661432 36028797018963968 197335 1000000000000000 rfl rfl rfl rfl (ep462 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep464 := nat_lit 2776881810162673198757458670528589221606741945894373574201334598265467487123585

noncomputable def ep465 := nat_lit 1861785931501483666863570013104365902018798012542973439319105726027859228801

noncomputable def ep466 := nat_lit 7269771373203617880332707880886993273700103232941146927816026348091226884667521

noncomputable def ep467 := BSN.sin_dyadic_bound_f 2562956399 2147483648 3 2 1048576 395056 ep464 ep79 ep465 ep466 ep81 ep465 974811 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2562956399) qz15 0 2 ep464 ep79 ep465 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2562956399) qz16 0 2 ep466 ep81 ep465 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz365 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 483851547) qz24)

noncomputable def ep468 := @Enclosure.Real.IsNear.cos_image qz73 qz365 Bool.false 483851547 1048576 737 1048576 Bool.true 974811 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz73 Bool.false 259765821524036352209 562949953421312000 3461950002732655613 4933375000000000000000 483851547 1048576 737 1048576 (ep463 rfl) rfl) (Enclosure.sfrac_false_div 483851547 1048576) (BSN.cos_reduce1 qz365 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 180352023233369466732544) qz25) 226375608064910080 72057594037927936 Bool.false 974811 1048576 73 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q1 483851547 1048576 226375608064910080 72057594037927936 73 180352023233369466732544 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 974811 1048576 180352023233369466732544 151115727451828646838272 2562956399 2147483648 395056 394670 (ep467 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep469 := nat_lit 1543539577171041325383860848077262619071309435724671084973772157136827652503681

noncomputable def ep470 := nat_lit 4626895159650121008817855404205579125409890711148927308042678259958427239053441

noncomputable def ep471 := BSN.cos_dyadic_bound_f 2562956399 2147483648 3 2 1048576 395056 ep469 ep72 ep465 ep470 ep75 ep465 386333 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2562956399) qz20 0 2 ep469 ep72 ep465 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2562956399) qz21 0 2 ep470 ep75 ep465 rfl rfl rfl rfl) rfl rfl

noncomputable def ep472 := @Enclosure.Real.IsNear.sin_image qz73 qz365 Bool.false 483851547 1048576 737 1048576 Bool.false 386333 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz73 Bool.false 259765821524036352209 562949953421312000 3461950002732655613 4933375000000000000000 483851547 1048576 737 1048576 (ep463 rfl) rfl) (Enclosure.sfrac_false_div 483851547 1048576) (BSN.sin_reduce1 qz365 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 180352023233369466732544) qz25) 226375608064910080 72057594037927936 Bool.false 386333 1048576 73 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q1 483851547 1048576 226375608064910080 72057594037927936 73 180352023233369466732544 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 386333 1048576 180352023233369466732544 151115727451828646838272 2562956399 2147483648 395056 394670 (ep471 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz366 := (@Enclosure.Real.IsNear.recentre' qz72 Bool.false 198163 1048576 1 1048576 198163 1048576 1 1048576 (ep461 rfl rfl) rfl)

noncomputable def ep473 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz72 (Real.cos qz73)) (@HMul.hMul Real Real Real qz0 qz72 (@Neg.neg Real Real.instNeg (Real.sin qz73))) Bool.true 193171472193 1099511627776 29220313039929 216972127067176960 Bool.true 76556906279 1099511627776 29104185733799 216972127067176960 (@Enclosure.Real.IsNear.mulLit_ft qz72 (Real.cos qz73) 198163 1048576 1 1048576 974811 1048576 146484471 206920744960 193171472193 1099511627776 29220313039929 216972127067176960 qz366 (@Enclosure.Real.IsNear.recentre' (Real.cos qz73) Bool.true 974811 1048576 146484471 206920744960 974811 1048576 146484471 206920744960 (ep468 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz72 (@Neg.neg Real Real.instNeg (Real.sin qz73)) 198163 1048576 1 1048576 386333 1048576 146484471 206920744960 76556906279 1099511627776 29104185733799 216972127067176960 qz366 (@Enclosure.Real.IsNear.neg (Real.sin qz73) Bool.false 386333 1048576 146484471 206920744960 (@Enclosure.Real.IsNear.recentre' (Real.sin qz73) Bool.false 386333 1048576 146484471 206920744960 386333 1048576 146484471 206920744960 (ep472 rfl rfl) rfl)) rfl)

noncomputable def ep474 := @ep411 193171472193 1099511627776 29220313039929 216972127067176960 Bool.true 76556906279 1099511627776 29104185733799 216972127067176960 Bool.false 14396688506772034420736 837997562879 1099511627776 1265750840785989 216972127067176960 Bool.false 93743473044757214658560 21314798015 274877906944 632707354021527 108486063533588480 (ep412 (BSN.head_sum_c_succ qz5 27 28 rfl rfl) (ep459 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep460 ep473) rfl rfl

noncomputable abbrev qz644 := (Real.log (Enclosure.sfrac Bool.false 29 1))

noncomputable abbrev qz74 := (@HMul.hMul Real Real Real qz269 qz279 qz644)

noncomputable abbrev qz367 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 29)))

noncomputable def ep475 := @Enclosure.Complex.IsNear.of_eq qz627 (Complex.mk (@HMul.hMul Real Real Real qz0 qz367 (Real.cos qz74)) (@HMul.hMul Real Real Real qz0 qz367 (@Neg.neg Real Real.instNeg (Real.sin qz74)))) Bool.false 46612239705 1099511627776 28570109688881 216972127067176960 Bool.true 49695357015 274877906944 1795270399961 13560757941698560 (BSN.cpow_neg_s_mk qz12 138478 1000 29 qz13 rfl)

noncomputable abbrev qz368 := (Real.sqrt (@Nat.cast Real Real.instNatCast 29))

noncomputable abbrev qz369 := (@Nat.cast Real Real.instNatCast 29)

noncomputable abbrev qz645 := (@HDiv.hDiv Real Real Real qz1 qz369 qz14)

noncomputable def ep476 := @Enclosure.Real.IsNear.inv_image qz368 5646755 1048576 1 1048576 97357 97358 524288 (@Enclosure.Real.IsNear.of_eq qz368 (Real.sqrt qz645) Bool.false 5646755 1048576 1 1048576 (BSN.sqrt_natCast_div_one 29) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz645) Bool.false 5646755 1048576 1 1048576 5646755 1048576 1 1048576 (BSN.sqrt_enclosure 29 1 2823377 2823378 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep477 := BSN.log_dyadic_bound 13 45 6 5 353956287581982421875 524288 197335 10371179520995104305 130276274797305 311797 58 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 13) (BSN.artanhQ 45) 0 5 10371179520995104305 353956287581982421875 130276274797305 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep478 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz644 138478 1000 0 1 3791236343078135 1125899906842624 50000000039467 9866750000000000000 52500282631677397853 112589990684262400 3461950002732655613 4933375000000000000000 qz18 (BSN.isNear_log_sfrac 29 1 3791236343078135 1125899906842624 50000000039467 9866750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz645) Bool.false 63606391034871975772160 18889465931478580854784 1000000000789340 197335000000000000000 3791236343078135 1125899906842624 50000000039467 9866750000000000000 (BSN.log_rat_reduce_isNear 29 1 4 58 32 311797 524288 24973259072661432 36028797018963968 197335 1000000000000000 rfl rfl rfl rfl (ep477 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep479 := nat_lit 2458139951900893484885533986616055767822696708288279209221030433279876400028481

noncomputable def ep480 := nat_lit 4715068898001886327984263418153105464631138714263024713731818152738156321601

noncomputable def ep481 := nat_lit 7364989717906676682000633433011861092538827847436311578235627663534152887442241

noncomputable def ep482 := BSN.cos_dyadic_bound_f 2878631049 2147483648 3 2 1048576 395056 ep479 ep72 ep480 ep481 ep75 ep480 239387 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2878631049) qz20 0 2 ep479 ep72 ep480 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2878631049) qz21 0 2 ep481 ep75 ep480 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz370 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 488946983) qz24)

noncomputable def ep483 := @Enclosure.Real.IsNear.cos_image qz74 qz370 Bool.false 488946983 1048576 737 1048576 Bool.false 239387 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz74 Bool.false 52500282631677397853 112589990684262400 3461950002732655613 4933375000000000000000 488946983 1048576 737 1048576 (ep478 rfl) rfl) (Enclosure.sfrac_false_div 488946983 1048576) (BSN.cos_reduce0 qz370 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 202565651895042751594496) qz25) 226375608064910080 72057594037927936 Bool.false 239387 1048576 74 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q0 488946983 1048576 226375608064910080 72057594037927936 74 202565651895042751594496 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 239387 1048576 202565651895042751594496 151115727451828646838272 2878631049 2147483648 395056 394670 (ep482 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep484 := nat_lit 4420879858303206763731573765174377897709149163947492156826869325381586994993985

noncomputable def ep485 := nat_lit 11570860945911633708099290101351122799438368823848910751676711003752104162368321

noncomputable def ep486 := BSN.sin_dyadic_bound_f 2878631049 2147483648 3 2 1048576 395056 ep484 ep79 ep480 ep485 ep81 ep480 1020884 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2878631049) qz15 0 2 ep484 ep79 ep480 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2878631049) qz16 0 2 ep485 ep81 ep480 rfl rfl rfl rfl) rfl rfl

noncomputable def ep487 := @Enclosure.Real.IsNear.sin_image qz74 qz370 Bool.false 488946983 1048576 737 1048576 Bool.false 1020884 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz74 Bool.false 52500282631677397853 112589990684262400 3461950002732655613 4933375000000000000000 488946983 1048576 737 1048576 (ep478 rfl) rfl) (Enclosure.sfrac_false_div 488946983 1048576) (BSN.sin_reduce0 qz370 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 202565651895042751594496) qz25) 226375608064910080 72057594037927936 Bool.false 1020884 1048576 74 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q0 488946983 1048576 226375608064910080 72057594037927936 74 202565651895042751594496 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1020884 1048576 202565651895042751594496 151115727451828646838272 2878631049 2147483648 395056 394670 (ep486 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz371 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 29))) Bool.false 194715 1048576 1 1048576 194715 1048576 1 1048576 (ep476 rfl rfl) rfl)

noncomputable def ep488 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz367 (Real.cos qz74)) (@HMul.hMul Real Real Real qz0 qz367 (@Neg.neg Real Real.instNeg (Real.sin qz74))) Bool.false 46612239705 1099511627776 28570109688881 216972127067176960 Bool.true 49695357015 274877906944 1795270399961 13560757941698560 (@Enclosure.Real.IsNear.mulLit_ff qz367 (Real.cos qz74) 194715 1048576 1 1048576 239387 1048576 146484471 206920744960 46612239705 1099511627776 28570109688881 216972127067176960 qz371 (@Enclosure.Real.IsNear.recentre' (Real.cos qz74) Bool.false 239387 1048576 146484471 206920744960 239387 1048576 146484471 206920744960 (ep483 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz367 (@Neg.neg Real Real.instNeg (Real.sin qz74)) 194715 1048576 1 1048576 255221 262144 146484471 206920744960 49695357015 274877906944 1795270399961 13560757941698560 qz371 (@Enclosure.Real.IsNear.neg (Real.sin qz74) Bool.false 255221 262144 146484471 206920744960 (@Enclosure.Real.IsNear.recentre' (Real.sin qz74) Bool.false 1020884 1048576 146484471 206920744960 255221 262144 146484471 206920744960 (ep487 rfl rfl) rfl)) rfl)

noncomputable def ep489 := @ep409 46612239705 1099511627776 28570109688881 216972127067176960 Bool.true 49695357015 274877906944 1795270399961 13560757941698560 Bool.false 972638763985739850973184 110576225323 137438953472 129432095047487 21697212706717696 Bool.true 7801188655820701696000 3547569875 34359738368 129413903444243 21697212706717696 (ep410 (BSN.head_sum_c_succ qz5 28 29 rfl rfl) (ep474 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep475 ep488) rfl rfl

noncomputable abbrev qz646 := (Real.log (Enclosure.sfrac Bool.false 30 1))

noncomputable abbrev qz75 := (@HMul.hMul Real Real Real qz269 qz279 qz646)

noncomputable abbrev qz372 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 30)))

noncomputable def ep490 := @Enclosure.Complex.IsNear.of_eq qz626 (Complex.mk (@HMul.hMul Real Real Real qz0 qz372 (Real.cos qz75)) (@HMul.hMul Real Real Real qz0 qz372 (@Neg.neg Real Real.instNeg (Real.sin qz75)))) Bool.false 194593577451 1099511627776 28244155608219 216972127067176960 Bool.false 49303655891 1099511627776 28094394130019 216972127067176960 (BSN.cpow_neg_s_mk qz12 138478 1000 30 qz13 rfl)

noncomputable abbrev qz373 := (Real.sqrt (@Nat.cast Real Real.instNatCast 30))

noncomputable abbrev qz374 := (@Nat.cast Real Real.instNatCast 30)

noncomputable abbrev qz647 := (@HDiv.hDiv Real Real Real qz1 qz374 qz14)

noncomputable def ep491 := @Enclosure.Real.IsNear.inv_image qz373 5743287 1048576 1 1048576 95721 95722 524288 (@Enclosure.Real.IsNear.of_eq qz373 (Real.sqrt qz647) Bool.false 5743287 1048576 1 1048576 (BSN.sqrt_natCast_div_one 30) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz647) Bool.false 5743287 1048576 1 1048576 5743287 1048576 1 1048576 (BSN.sqrt_enclosure 30 1 2871643 2871644 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep492 := BSN.log_dyadic_bound 14 46 6 5 440963670083462507520 524288 197335 14425761949190022144 273345648952320 329571 60 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 14) (BSN.artanhQ 46) 0 5 14425761949190022144 440963670083462507520 273345648952320 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep493 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz646 138478 1000 0 1 3829405717437687 1125899906842624 50000000039467 9866750000000000000 265144222469668010193 562949953421312000 3461950002732655613 4933375000000000000000 qz18 (BSN.isNear_log_sfrac 30 1 3829405717437687 1125899906842624 50000000039467 9866750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz647) Bool.false 64246766873087041339392 18889465931478580854784 1000000000789340 197335000000000000000 3829405717437687 1125899906842624 50000000039467 9866750000000000000 (BSN.log_rat_reduce_isNear 30 1 4 60 32 329571 524288 24973259072661432 36028797018963968 197335 1000000000000000 rfl rfl rfl rfl (ep492 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep494 := nat_lit 4190254738755142704231849022853341567663213895862957421547296143275826864881920

noncomputable def ep495 := nat_lit 4236427214880912521146040880445675247577550072125440855458329884024550359296

noncomputable def ep496 := nat_lit 10967617719344137986049177660333268250621863217619542533143604984005411564585216

noncomputable def ep497 := BSN.sin_dyadic_bound_f 2840370338 2147483648 3 2 1048576 395056 ep494 ep79 ep495 ep496 ep81 ep495 1016457 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2840370338) qz15 0 2 ep494 ep79 ep495 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2840370338) qz16 0 2 ep496 ep81 ep495 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz375 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 493869599) qz24)

noncomputable def ep498 := @Enclosure.Real.IsNear.cos_image qz75 qz375 Bool.false 493869599 1048576 737 1048576 Bool.false 1016457 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz75 Bool.false 265144222469668010193 562949953421312000 3461950002732655613 4933375000000000000000 493869599 1048576 737 1048576 (ep493 rfl) rfl) (Enclosure.sfrac_false_div 493869599 1048576) (BSN.cos_reduce3 qz375 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 199873293753446624657408) qz25) 226375608064910080 72057594037927936 Bool.false 1016457 1048576 74 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q3 493869599 1048576 226375608064910080 72057594037927936 74 199873293753446624657408 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1016457 1048576 199873293753446624657408 151115727451828646838272 2840370338 2147483648 395056 394670 (ep497 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep499 := nat_lit 2329802155848359685693758808643165615478486631067032096795368226212803613982976

noncomputable def ep500 := nat_lit 6980933613115317232038984344168605495940304793056845408675188018870361741230336

noncomputable def ep501 := BSN.cos_dyadic_bound_f 2840370338 2147483648 3 2 1048576 395056 ep499 ep72 ep495 ep500 ep75 ep495 257537 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2840370338) qz20 0 2 ep499 ep72 ep495 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2840370338) qz21 0 2 ep500 ep75 ep495 rfl rfl rfl rfl) rfl rfl

noncomputable def ep502 := @Enclosure.Real.IsNear.sin_image qz75 qz375 Bool.false 493869599 1048576 737 1048576 Bool.true 257537 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz75 Bool.false 265144222469668010193 562949953421312000 3461950002732655613 4933375000000000000000 493869599 1048576 737 1048576 (ep493 rfl) rfl) (Enclosure.sfrac_false_div 493869599 1048576) (BSN.sin_reduce3 qz375 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 199873293753446624657408) qz25) 226375608064910080 72057594037927936 Bool.false 257537 1048576 74 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q3 493869599 1048576 226375608064910080 72057594037927936 74 199873293753446624657408 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 257537 1048576 199873293753446624657408 151115727451828646838272 2840370338 2147483648 395056 394670 (ep501 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz376 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 30))) Bool.false 191443 1048576 1 1048576 191443 1048576 1 1048576 (ep491 rfl rfl) rfl)

noncomputable def ep503 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz372 (Real.cos qz75)) (@HMul.hMul Real Real Real qz0 qz372 (@Neg.neg Real Real.instNeg (Real.sin qz75))) Bool.false 194593577451 1099511627776 28244155608219 216972127067176960 Bool.false 49303655891 1099511627776 28094394130019 216972127067176960 (@Enclosure.Real.IsNear.mulLit_ff qz372 (Real.cos qz75) 191443 1048576 1 1048576 1016457 1048576 146484471 206920744960 194593577451 1099511627776 28244155608219 216972127067176960 qz376 (@Enclosure.Real.IsNear.recentre' (Real.cos qz75) Bool.false 1016457 1048576 146484471 206920744960 1016457 1048576 146484471 206920744960 (ep498 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz372 (@Neg.neg Real Real.instNeg (Real.sin qz75)) 191443 1048576 1 1048576 257537 1048576 146484471 206920744960 49303655891 1099511627776 28094394130019 216972127067176960 qz376 (@Enclosure.Real.IsNear.neg (Real.sin qz75) Bool.true 257537 1048576 146484471 206920744960 (@Enclosure.Real.IsNear.recentre' (Real.sin qz75) Bool.true 257537 1048576 146484471 206920744960 257537 1048576 146484471 206920744960 (ep502 rfl rfl) rfl)) rfl)

noncomputable def ep504 := @ep407 194593577451 1099511627776 28244155608219 216972127067176960 Bool.false 49303655891 1099511627776 28094394130019 216972127067176960 Bool.false 148324583135455498731520 1079203380035 1099511627776 1322565106083089 216972127067176960 Bool.true 2206533610909688922112 64218580109 1099511627776 1322233428572449 216972127067176960 (ep408 (BSN.head_sum_c_succ qz5 29 30 rfl rfl) (ep489 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep490 ep503) rfl rfl

noncomputable abbrev qz648 := (Real.log (Enclosure.sfrac Bool.false 31 1))

noncomputable abbrev qz76 := (@HMul.hMul Real Real Real qz269 qz279 qz648)

noncomputable abbrev qz377 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 31)))

noncomputable def ep505 := @Enclosure.Complex.IsNear.of_eq qz625 (Complex.mk (@HMul.hMul Real Real Real qz0 qz377 (Real.cos qz76)) (@HMul.hMul Real Real Real qz0 qz377 (@Neg.neg Real Real.instNeg (Real.sin qz76)))) Bool.true 314321101 4294967296 2767173456487 21697212706717696 Bool.false 90169853581 549755813888 1388819203903 10848606353358848 (BSN.cpow_neg_s_mk qz12 138478 1000 31 qz13 rfl)

noncomputable abbrev qz378 := (Real.sqrt (@Nat.cast Real Real.instNatCast 31))

noncomputable abbrev qz379 := (@Nat.cast Real Real.instNatCast 31)

noncomputable abbrev qz649 := (@HDiv.hDiv Real Real Real qz1 qz379 qz14)

noncomputable def ep506 := @Enclosure.Real.IsNear.inv_image qz378 5838225 1048576 1 1048576 94164 94165 524288 (@Enclosure.Real.IsNear.of_eq qz378 (Real.sqrt qz649) Bool.false 5838225 1048576 1 1048576 (BSN.sqrt_natCast_div_one 31) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz649) Bool.false 5838225 1048576 1 1048576 5838225 1048576 1 1048576 (BSN.sqrt_enclosure 31 1 2919112 2919113 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep507 := BSN.log_dyadic_bound 15 47 6 5 546767979591453359355 524288 197335 19788004106328479625 544934619140625 346763 62 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 15) (BSN.artanhQ 47) 0 5 19788004106328479625 546767979591453359355 544934619140625 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep508 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz648 138478 1000 0 1 3866325256314103 1125899906842624 50000000039467 9866750000000000000 267700494421932177617 562949953421312000 3461950002732655613 4933375000000000000000 qz18 (BSN.isNear_log_sfrac 31 1 3866325256314103 1125899906842624 50000000039467 9866750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz649) Bool.false 64866173951437069877248 18889465931478580854784 1000000000789340 197335000000000000000 3866325256314103 1125899906842624 50000000039467 9866750000000000000 (BSN.log_rat_reduce_isNear 31 1 4 62 32 346763 524288 24973259072661432 36028797018963968 197335 1000000000000000 rfl rfl rfl rfl (ep507 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep509 := nat_lit 1335592195093853519713635885944220202837832199902887190892629415228478041686016

noncomputable def ep510 := nat_lit 1394385822173933474613858111760290499660797756546523715578998732273955700736

noncomputable def ep511 := nat_lit 4003987813637212692191679941609140027514175004195568525246730248220886213656576

noncomputable def ep512 := BSN.cos_dyadic_bound_f 2471996604 2147483648 3 2 1048576 395056 ep509 ep72 ep510 ep511 ep75 ep510 427264 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2471996604) qz20 0 2 ep509 ep72 ep510 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2471996604) qz21 0 2 ep511 ep75 ep510 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz380 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 498631027) qz24)

noncomputable def ep513 := @Enclosure.Real.IsNear.cos_image qz76 qz380 Bool.false 498631027 1048576 737 1048576 Bool.true 427264 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz76 Bool.false 267700494421932177617 562949953421312000 3461950002732655613 4933375000000000000000 498631027 1048576 737 1048576 (ep508 rfl) rfl) (Enclosure.sfrac_false_div 498631027 1048576) (BSN.cos_reduce2 qz380 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 173951296676279441424384) qz25) 226375608064910080 72057594037927936 Bool.false 427264 1048576 75 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q2 498631027 1048576 226375608064910080 72057594037927936 75 173951296676279441424384 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 427264 1048576 173951296676279441424384 151115727451828646838272 2471996604 2147483648 395056 394670 (ep512 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep514 := nat_lit 2402950442511197188704853508210188132708369321619959724634269748425441310474240

noncomputable def ep515 := nat_lit 6291184058102949125744289132179071305808183122160723954693102390785807503917056

noncomputable def ep516 := BSN.sin_dyadic_bound_f 2471996604 2147483648 3 2 1048576 395056 ep514 ep79 ep510 ep515 ep81 ep510 957578 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2471996604) qz15 0 2 ep514 ep79 ep510 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2471996604) qz16 0 2 ep515 ep81 ep510 rfl rfl rfl rfl) rfl rfl

noncomputable def ep517 := @Enclosure.Real.IsNear.sin_image qz76 qz380 Bool.false 498631027 1048576 737 1048576 Bool.true 957578 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz76 Bool.false 267700494421932177617 562949953421312000 3461950002732655613 4933375000000000000000 498631027 1048576 737 1048576 (ep508 rfl) rfl) (Enclosure.sfrac_false_div 498631027 1048576) (BSN.sin_reduce2 qz380 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 173951296676279441424384) qz25) 226375608064910080 72057594037927936 Bool.false 957578 1048576 75 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q2 498631027 1048576 226375608064910080 72057594037927936 75 173951296676279441424384 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 957578 1048576 173951296676279441424384 151115727451828646838272 2471996604 2147483648 395056 394670 (ep516 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz381 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 31))) Bool.false 188329 1048576 1 1048576 188329 1048576 1 1048576 (ep506 rfl rfl) rfl)

noncomputable def ep518 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz377 (Real.cos qz76)) (@HMul.hMul Real Real Real qz0 qz377 (@Neg.neg Real Real.instNeg (Real.sin qz76))) Bool.true 314321101 4294967296 2767173456487 21697212706717696 Bool.false 90169853581 549755813888 1388819203903 10848606353358848 (@Enclosure.Real.IsNear.mulLit_ft qz377 (Real.cos qz76) 188329 1048576 1 1048576 1669 4096 146484471 206920744960 314321101 4294967296 2767173456487 21697212706717696 qz381 (@Enclosure.Real.IsNear.recentre' (Real.cos qz76) Bool.true 427264 1048576 146484471 206920744960 1669 4096 146484471 206920744960 (ep513 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz377 (@Neg.neg Real Real.instNeg (Real.sin qz76)) 188329 1048576 1 1048576 478789 524288 146484471 206920744960 90169853581 549755813888 1388819203903 10848606353358848 qz381 (@Enclosure.Real.IsNear.neg (Real.sin qz76) Bool.true 478789 524288 146484471 206920744960 (@Enclosure.Real.IsNear.recentre' (Real.sin qz76) Bool.true 957578 1048576 146484471 206920744960 478789 524288 146484471 206920744960 (ep517 rfl rfl) rfl)) rfl)

noncomputable def ep519 := @ep405 314321101 4294967296 2767173456487 21697212706717696 Bool.false 90169853581 549755813888 1388819203903 10848606353358848 Bool.false 4289543517578129833984 998737178179 1099511627776 1350236840647959 216972127067176960 Bool.false 63838264712613869912064 116121127053 1099511627776 1350009812650509 216972127067176960 (ep406 (BSN.head_sum_c_succ qz5 30 31 rfl rfl) (ep504 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep505 ep518) rfl rfl

noncomputable abbrev qz650 := (Real.log (Enclosure.sfrac Bool.false 32 1))

noncomputable abbrev qz77 := (@HMul.hMul Real Real Real qz269 qz279 qz650)

noncomputable abbrev qz382 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 32)))

noncomputable def ep520 := @Enclosure.Complex.IsNear.of_eq qz624 (Complex.mk (@HMul.hMul Real Real Real qz0 qz382 (Real.cos qz77)) (@HMul.hMul Real Real Real qz0 qz382 (@Neg.neg Real Real.instNeg (Real.sin qz77)))) Bool.true 144122142219 1099511627776 27306378010299 216972127067176960 Bool.true 65206069325 549755813888 13645891260847 108486063533588480 (BSN.cpow_neg_s_mk qz12 138478 1000 32 qz13 rfl)

noncomputable abbrev qz383 := (Real.sqrt (@Nat.cast Real Real.instNatCast 32))

noncomputable abbrev qz384 := (@Nat.cast Real Real.instNatCast 32)

noncomputable abbrev qz651 := (@HDiv.hDiv Real Real Real qz1 qz384 qz14)

noncomputable def ep521 := @Enclosure.Real.IsNear.inv_image qz383 5931641 1048576 1 1048576 92681 92682 524288 (@Enclosure.Real.IsNear.of_eq qz383 (Real.sqrt qz651) Bool.false 5931641 1048576 1 1048576 (BSN.sqrt_natCast_div_one 32) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz651) Bool.false 5931641 1048576 1 1048576 5931641 1048576 1 1048576 (BSN.sqrt_enclosure 32 1 2965820 2965821 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep522 := BSN.log_dyadic_bound 0 64 1 0 1 524288 197335 0 1 0 64 64 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 64) 0 0 rfl) rfl rfl rfl

noncomputable def ep523 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz650 138478 1000 0 1 15608286920413395 4503599627370496 40000000039467 7893400000000000000 216140435616500611281 450359962737049600 2769560002732655613 3946700000000000000000 qz18 (BSN.isNear_log_sfrac 32 1 15608286920413395 4503599627370496 40000000039467 7893400000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz651) Bool.false 65465900263437584302080 18889465931478580854784 1000000000986675 197335000000000000000 15608286920413395 4503599627370496 40000000039467 7893400000000000000 (BSN.log_rat_reduce_isNear 32 1 5 64 64 0 524288 24973259072661432 36028797018963968 197335 1000000000000000 rfl rfl rfl rfl (ep522 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep524 := nat_lit 10353366708870641454975556952031517456

noncomputable def ep525 := BSN.sin_dyadic_bound_f 1793785046 2147483648 2 1 1048576 395056 ep524 ep58 ep524 ep524 ep59 ep524 777513 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1793785046) qz15 0 1 ep524 ep58 ep524 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1793785046) qz16 0 1 ep524 ep59 ep524 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz385 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 503241167) qz24)

noncomputable def ep526 := @Enclosure.Real.IsNear.cos_image qz77 qz385 Bool.false 503241167 1048576 737 1048576 Bool.true 777513 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz77 Bool.false 216140435616500611281 450359962737049600 2769560002732655613 3946700000000000000000 503241167 1048576 737 1048576 (ep523 rfl) rfl) (Enclosure.sfrac_false_div 503241167 1048576) (BSN.cos_reduce1 qz385 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 126226401025492175028224) qz25) 226375608064910080 72057594037927936 Bool.false 777513 1048576 76 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q1 503241167 1048576 226375608064910080 72057594037927936 76 126226401025492175028224 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 777513 1048576 126226401025492175028224 151115727451828646838272 1793785046 2147483648 395056 394670 (ep525 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep527 := nat_lit 370029345778177963429353524758054644945603599607625300073692882622044166185216

noncomputable def ep528 := nat_lit 107192202208350897773855241144964086354647278286093466498621301574032711936

noncomputable def ep529 := nat_lit 1109873652930117188492512863791874006664101504266303713288081405262984433131776

noncomputable def ep530 := BSN.cos_dyadic_bound_f 1793785046 2147483648 3 2 1048576 395056 ep527 ep72 ep528 ep529 ep75 ep528 703550 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1793785046) qz20 0 2 ep527 ep72 ep528 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1793785046) qz21 0 2 ep529 ep75 ep528 rfl rfl rfl rfl) rfl rfl

noncomputable def ep531 := @Enclosure.Real.IsNear.sin_image qz77 qz385 Bool.false 503241167 1048576 737 1048576 Bool.false 703550 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz77 Bool.false 216140435616500611281 450359962737049600 2769560002732655613 3946700000000000000000 503241167 1048576 737 1048576 (ep523 rfl) rfl) (Enclosure.sfrac_false_div 503241167 1048576) (BSN.sin_reduce1 qz385 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 126226401025492175028224) qz25) 226375608064910080 72057594037927936 Bool.false 703550 1048576 76 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q1 503241167 1048576 226375608064910080 72057594037927936 76 126226401025492175028224 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 703550 1048576 126226401025492175028224 151115727451828646838272 1793785046 2147483648 395056 394670 (ep530 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz386 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 32))) Bool.false 185363 1048576 1 1048576 185363 1048576 1 1048576 (ep521 rfl rfl) rfl)

noncomputable def ep532 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz382 (Real.cos qz77)) (@HMul.hMul Real Real Real qz0 qz382 (@Neg.neg Real Real.instNeg (Real.sin qz77))) Bool.true 144122142219 1099511627776 27306378010299 216972127067176960 Bool.true 65206069325 549755813888 13645891260847 108486063533588480 (@Enclosure.Real.IsNear.mulLit_ft qz382 (Real.cos qz77) 185363 1048576 1 1048576 777513 1048576 146484471 206920744960 144122142219 1099511627776 27306378010299 216972127067176960 qz386 (@Enclosure.Real.IsNear.recentre' (Real.cos qz77) Bool.true 777513 1048576 146484471 206920744960 777513 1048576 146484471 206920744960 (ep526 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz382 (@Neg.neg Real Real.instNeg (Real.sin qz77)) 185363 1048576 1 1048576 351775 524288 146484471 206920744960 65206069325 549755813888 13645891260847 108486063533588480 qz386 (@Enclosure.Real.IsNear.neg (Real.sin qz77) Bool.false 351775 524288 146484471 206920744960 (@Enclosure.Real.IsNear.recentre' (Real.sin qz77) Bool.false 703550 1048576 146484471 206920744960 351775 524288 146484471 206920744960 (ep531 rfl rfl) rfl)) rfl)

noncomputable def ep533 := @ep403 144122142219 1099511627776 27306378010299 216972127067176960 Bool.true 65206069325 549755813888 13645891260847 108486063533588480 Bool.false 939659169310224374824960 106826879495 137438953472 688771609329129 108486063533588480 Bool.true 7856566711791581659136 14291011597 1099511627776 1377301595172203 216972127067176960 (ep404 (BSN.head_sum_c_succ qz5 31 32 rfl rfl) (ep519 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep520 ep532) rfl rfl

theorem EMRow48.d9 : Enclosure.Complex.IsNear qz65 Bool.false 106826879495 137438953472 688771609329129 108486063533588480 Bool.true 14291011597 1099511627776 1377301595172203 216972127067176960 := ep402 (BSN.head_sum_c_succ qz5 32 33 rfl rfl) (ep533 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

theorem EMRow48.d10 : @Eq Nat (BSN.factNat (Nat.mul 2 1)) 2 := @Eq.refl Nat 2

theorem EMRow48.d11 : @Eq Nat (Nat.pow 35 1) 35 := @Eq.refl Nat 35

noncomputable def ep534 := nat_lit 333745458961880063974343388101423

noncomputable def ep535 := nat_lit 386905599788501083873838366720000

noncomputable def ep536 := nat_lit 105346193639210908061821831540575089352457

noncomputable def ep537 := nat_lit 15066530512788959086654438841570557952000000

noncomputable abbrev qz722 := (@instHMul Complex Complex.instMul)

noncomputable abbrev qz652 := qz722

noncomputable abbrev qz387 := qz652

noncomputable abbrev qz78 := qz387

noncomputable abbrev qz653 := (@instHSub Complex Complex.instSub)

noncomputable abbrev qz388 := qz653

noncomputable abbrev qz79 := qz388

noncomputable abbrev qz723 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (4 : Complex))

noncomputable abbrev qz724 := (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid))

noncomputable abbrev qz654 := (@HAdd.hAdd Complex Complex Complex qz720 (@HAdd.hAdd Complex Complex Complex qz720 qz723 (@HMul.hMul Complex Complex Complex qz722 Complex.I (@HDiv.hDiv Complex Complex Complex qz724 (↑qz721) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz389 := qz654

noncomputable abbrev qz80 := (Complex.Stirling.logGammaStirling 1 qz389)

noncomputable abbrev qz655 := (@HAdd.hAdd Complex Complex Complex qz720 qz723 (@HMul.hMul Complex Complex Complex qz722 Complex.I (@HDiv.hDiv Complex Complex Complex qz724 (↑qz721) (2 : Complex))))

noncomputable abbrev qz390 := qz655

noncomputable abbrev qz81 := qz390

noncomputable abbrev qz82 := (@HMul.hMul Real Real Real qz269 (@HDiv.hDiv Real Real Real qz272 qz279 (2 : Real)) (Real.log Real.pi))

noncomputable abbrev qz391 := (@instHSub Real Real.instSub)

noncomputable def ep538 := Complex.re (@HMul.hMul Complex Complex Complex qz78 (Complex.exp (@HMul.hMul Complex Complex Complex qz78 Complex.I ↑(@HSub.hSub Real Real Real qz391 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz80 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz81 (@Nat.cast Complex Complex.instNatCast j))))) qz82))) (zetaApproximant qz5 1 35))

noncomputable def ep539 := @Enclosure.Real.IsNear.of_eq ep538 (@HSub.hSub Real Real Real qz391 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz391 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz80 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz81 (@Nat.cast Complex Complex.instNatCast j))))) qz82)) (Complex.re (zetaApproximant qz5 1 35))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz391 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz80 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz81 (@Nat.cast Complex Complex.instNatCast j))))) qz82)) (Complex.im (zetaApproximant qz5 1 35))))

noncomputable def ep540 := nat_lit 2669961968401520549575764654379

noncomputable def ep541 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz391 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz80 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz81 (@Nat.cast Complex Complex.instNatCast j))))) qz82)) (Complex.re (zetaApproximant qz5 1 35))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz391 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz80 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz81 (@Nat.cast Complex Complex.instNatCast j))))) qz82)) (Complex.im (zetaApproximant qz5 1 35))) ep540

noncomputable def ep542 := nat_lit 3095244798308008670990706933760

noncomputable def ep543 := nat_lit 105217116427113294968467573241670404855161

noncomputable def ep544 := nat_lit 13306980624704835800394003

noncomputable def ep545 := nat_lit 24181599986781317742114897920000

noncomputable def ep546 := nat_lit 8067325756100818334641143681542781081

noncomputable def ep547 := nat_lit 941658157049309942915902427598159872000000

noncomputable def ep548 := nat_lit 64563993488167390223782861062207823071553843792043778013921280

noncomputable def ep549 := @Enclosure.Real.IsNear.mulLit_ff (Real.cos (@HSub.hSub Real Real Real qz391 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz80 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz81 (@Nat.cast Complex Complex.instNatCast j))))) qz82)) (Complex.re (zetaApproximant qz5 1 35)) 1048575 1048576 19008969

noncomputable def ep550 := nat_lit 190970743752343934595219559

noncomputable def ep551 := nat_lit 221389160035229349445632000

noncomputable def ep552 := nat_lit 1455696532564393784076905899283

noncomputable def ep553 := nat_lit 218439149477759918364268953600000

noncomputable def ep554 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz391 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz80 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz81 (@Nat.cast Complex Complex.instNatCast j))))) qz82)) Bool.false 1048575 1048576 19008969

noncomputable abbrev qz392 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 151533101) qz24)

noncomputable def ep555 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz391 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz80 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz81 (@Nat.cast Complex Complex.instNatCast j))))) qz82) qz392 Bool.false 151533101 1048576 95

noncomputable def ep556 := nat_lit 22431017622736125194819417

noncomputable def ep557 := nat_lit 62076223488000000000000000000

noncomputable def ep558 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz391 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz80 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz81 (@Nat.cast Complex Complex.instNatCast j))))) qz82) Bool.false 976244572639205568817 6755399441055744000 ep556 ep557

noncomputable def ep559 := nat_lit 6035083944736125194819417

noncomputable def ep560 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz80 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz81 (@Nat.cast Complex Complex.instNatCast j))))) qz82 1511677084870411071793 6755399441055744000 ep559 ep557 5194379019 65536000

noncomputable def ep561 := nat_lit 63979164312482976157990912000

noncomputable def ep562 := nat_lit 1883944793854931421852761

noncomputable def ep563 := nat_lit 10346037248000000000000000000

noncomputable def ep564 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz79 qz80 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz81 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 122611472276970241883 1125899906842624000 ep562 ep563 Bool.false 1511677084870411071793 6755399441055744000

noncomputable def ep565 := nat_lit 1857730393730778974876761

noncomputable def ep566 := nat_lit 5720511144674048971331417

noncomputable def ep567 := @Enclosure.Complex.IsNear.subLitP qz80 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz81 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 113069135155266588883 1125899906842624000 ep565 ep563 Bool.false 1532753464295754375793 6755399441055744000 ep566

noncomputable def ep568 := nat_lit 138048245214477770516776736094420992

noncomputable def ep569 := nat_lit 425499272257931309968735802604126208

noncomputable abbrev qz725 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex))

noncomputable abbrev qz656 := qz725

noncomputable abbrev qz393 := (@HSub.hSub Complex Complex Complex qz653 qz654 qz656)

noncomputable abbrev qz394 := (Complex.log qz654)

noncomputable abbrev qz83 := (@HSub.hSub Complex Complex Complex qz388 (@HMul.hMul Complex Complex Complex qz387 qz393 qz394) qz389)

noncomputable abbrev qz395 := qz656

noncomputable abbrev qz84 := (@HMul.hMul Complex Complex Complex qz387 qz395 ↑(Real.log (@HMul.hMul Real Real Real qz269 (2 : Real) Real.pi)))

noncomputable abbrev qz657 := qz724

noncomputable abbrev qz396 := qz657

noncomputable abbrev qz85 := qz396

noncomputable abbrev qz86 := (@instHMul Nat instMulNat)

noncomputable abbrev qz658 := (@instHPow Complex Int (@ZPow.toPow Complex (@DivInvMonoid.toZPow Complex Complex.instDivInvMonoid)))

noncomputable abbrev qz397 := qz658

noncomputable abbrev qz87 := qz397

noncomputable abbrev qz88 := qz389

noncomputable abbrev qz89 := (@OfNat.ofNat Int 1 (@instOfNat 1))

noncomputable abbrev qz90 := (@OfNat.ofNat Int 2 (@instOfNat 2))

noncomputable abbrev qz398 := (@instHSub Int Int.instSub)

noncomputable abbrev qz399 := (@instHMul Int Int.instMul)

noncomputable def ep570 := @Enclosure.Complex.IsNear.of_eq qz80 (@HAdd.hAdd Complex Complex Complex qz4 (@HAdd.hAdd Complex Complex Complex qz4 qz83 qz84) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz79 (@HMul.hMul Complex Complex Complex qz78 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz87 qz88 (@HSub.hSub Int Int Int qz398 qz89 (@HMul.hMul Int Int Int qz399 qz90 (@Nat.cast Int instNatCastInt k)))))) Bool.true 113069135155266588883

noncomputable def ep571 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz4 qz83 qz84) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz79 (@HMul.hMul Complex Complex Complex qz78 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz87 qz88 (@HSub.hSub Int Int Int qz398 qz89 (@HMul.hMul Int Int Int qz399 qz90 (@Nat.cast Int instNatCastInt k))))) Bool.true 113069179143996444883 1125899906842624000

noncomputable def ep572 := nat_lit 7770051802861982102623394725888

noncomputable def ep573 := nat_lit 26332504007923874862719316262912000

noncomputable def ep574 := @ep571 1771669332567985561 9866750000000000000000 Bool.false 510920528752510569339 2251799813685248000 3636950016430467303 39467000000000000000000 Bool.false 2684859 68719476736 3 68719476736 Bool.true 61965650767 51539607552000 69239 51539607552000 Bool.true ep572 113069135155266588883 1125899906842624000 ep565 ep563 Bool.false ep573

noncomputable def ep575 := @Enclosure.Complex.IsNear.addLitP qz83 qz84 Bool.true 114103810995799068883 1125899906842624000 14022800003561462613 78934000000000000000000

noncomputable def ep576 := nat_lit 14820203448761902023704576

noncomputable def ep577 := @ep575 Bool.false 510920528752510569339 2251799813685248000 3636950016430467303 39467000000000000000000 Bool.false 120447 131072 1 524288 Bool.false 0 1 0 1 Bool.true ep576 113069179143996444883 1125899906842624000 1771669332567985561 9866750000000000000000 Bool.false 510920528752510569339 510920528752510569339 2251799813685248000

noncomputable abbrev qz91 := (@HMul.hMul Complex Complex Complex qz387 qz393 qz394)

noncomputable def ep578 := @Enclosure.Complex.IsNear.subLitP qz91 qz88 Bool.true 111570536205403164883 1125899906842624000 14022800003561462613 78934000000000000000000 Bool.false 666832896052263455611

noncomputable def ep579 := nat_lit 2043682115010042277356000

noncomputable def ep580 := @ep578 2251799813685248000 3636950016430467303 39467000000000000000000 Bool.false 9000 4000 0 1 Bool.false 276956 4000 0 1 Bool.true 456415243983196275532000 114103810995799068883 1125899906842624000 14022800003561462613 78934000000000000000000 Bool.false ep579 510920528752510569339 2251799813685248000 3636950016430467303 39467000000000000000000

noncomputable abbrev qz92 := qz393

noncomputable abbrev qz93 := qz394

noncomputable def ep581 := @Enclosure.Complex.IsNear.mul qz92 qz93 Bool.true 111570536205403164883 1125899906842624000 14022800003561462613 78934000000000000000000 Bool.false 666832896052263455611 2251799813685248000 3636950016430467303

noncomputable abbrev qz94 := (Complex.re qz393)

noncomputable abbrev qz95 := (Complex.re qz394)

noncomputable abbrev qz96 := (Complex.im qz393)

noncomputable abbrev qz97 := (Complex.im qz394)

noncomputable def ep582 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz94 qz95) (@HMul.hMul Real Real Real qz0 qz96 qz97) 66803342395007043 9007199254740992 175000000828807 78934000000000000000 59960477002389522629 562949953421312000

noncomputable def ep583 := nat_lit 502469025280180126133655349617491968

noncomputable def ep584 := @Enclosure.Real.IsNear.mulLit_ff qz94 qz95 7000 4000 0 1 9543334627858149 2251799813685248 25000000118401 19733500000000000000

noncomputable def ep585 := @Enclosure.Complex.IsNear.re_isNear qz92 Bool.false 7000 4000 0 1 Bool.false 276956 4000 0 1

noncomputable abbrev qz659 := (Enclosure.sfrac Bool.false 276956 4000)

noncomputable abbrev qz400 := qz659

noncomputable def ep586 := @Enclosure.Complex.IsNear.of_eq qz92 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz400) Bool.false 7000 4000 0 1 Bool.false 276956 4000 0

noncomputable abbrev qz660 := (Enclosure.sfrac Bool.false 9000 4000)

noncomputable abbrev qz401 := (Complex.log (Complex.mk qz660 qz659))

noncomputable def ep587 := @Enclosure.Complex.IsNear.of_eq qz93 qz401 Bool.false 9543334627858149 2251799813685248 25000000118401 19733500000000000000 Bool.false 865992821999011 562949953421312 200000000039467 78934000000000000000

noncomputable def ep588 := nat_lit 6154245909262551737093205413832918589323018240

noncomputable def ep589 := nat_lit 12865094350140633133666140492971966401609728

noncomputable def ep590 := nat_lit 48047808303382014324489696795746280603648

noncomputable def ep591 := BSN.log_dyadic_bound 11249625936 142321625936 3 2 ep588 1048576 394670 ep589 ep590 166113 153571251872 131072000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 11249625936) (BSN.artanhQ 142321625936) 0 2 ep589 ep588 ep590 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz98 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz402 := (Enclosure.Real.IsNear.const Bool.false 1 2)

noncomputable abbrev qz661 := (Real.log (Enclosure.sfrac Bool.false 76785625936 16000000))

noncomputable abbrev qz662 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable def ep592 := @Enclosure.Real.IsNear.mulLit_ff qz98 qz661 1 2 0 1 9543334627858149 1125899906842624 25000000118401 9866750000000000000 9543334627858149 2251799813685248 25000000118401 19733500000000000000 qz402 (BSN.isNear_log_sfrac 76785625936 16000000 9543334627858149 1125899906842624 25000000118401 9866750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 76785625936) qz662)) Bool.false 320221172823711566266368 37778931862957161709568 1000000004736040 394670000000000000000 9543334627858149 1125899906842624 25000000118401 9866750000000000000 (BSN.log_rat_reduce_isNear 76785625936 16000000 12 153571251872 131072000000 166113 1048576 24973259072661432 36028797018963968 394670 1000000000000000 rfl rfl rfl rfl (ep591 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep593 := BSN.arctan_dyadic_bound_f 9000 276956 1 0 1048576 394670 0 1 1 0 1 1 34062 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 276956) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 276956) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz99 := (@HMul.hMul Real Real Real qz269 (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz100 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 2) Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 qz402 BSN.pi_near_15 rfl)

noncomputable abbrev qz403 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 276956)))

noncomputable def ep594 := @Enclosure.Real.IsNear.subLit_ff_p qz99 qz403 884279719003555 562949953421312 1 2000000000000000 34062 1048576 1 394670 908059289320434958336 865992821999011 562949953421312 200000000039467 78934000000000000000 qz100 (ep593 rfl) rfl rfl

noncomputable abbrev qz404 := (Complex.mk qz660 qz659)

noncomputable abbrev qz405 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 276956) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep595 := @Enclosure.Complex.IsNear.re_isNear qz93 Bool.false 9543334627858149 2251799813685248 25000000118401 19733500000000000000 Bool.false 865992821999011 562949953421312 200000000039467 78934000000000000000 (ep587 (@congrArg Complex Complex qz88 qz404 Complex.log (BSN.w_shift_mk qz12 Bool.false 138478 1000 2 qz13 rfl)) (@Enclosure.Complex.IsNear.of_parts qz401 Bool.false 9543334627858149 2251799813685248 25000000118401 19733500000000000000 Bool.false 865992821999011 562949953421312 200000000039467 78934000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz401) (@HMul.hMul Real Real Real qz0 qz98 qz661) Bool.false 9543334627858149 2251799813685248 25000000118401 19733500000000000000 (Enclosure.clog_re_eq 9000 276956 4000 76785625936 16000000 rfl rfl rfl) (ep592 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz401) qz405 Bool.false 865992821999011 562949953421312 200000000039467 78934000000000000000 (Enclosure.clog_im_eq 9000 276956 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz405 (@HSub.hSub Real Real Real qz391 qz99 qz403) Bool.false 865992821999011 562949953421312 200000000039467 78934000000000000000 (BSN.arctan_recip 276956 9000 rfl rfl) ep594))))

noncomputable def ep596 := @Enclosure.Real.IsNear.mulLit_ff qz96 qz97 276956 4000 0 1 865992821999011 562949953421312 200000000039467 78934000000000000000

noncomputable def ep597 := @Enclosure.Complex.IsNear.im_isNear qz92 Bool.false 7000 4000 0 1 Bool.false 276956 4000 0 1

noncomputable def ep598 := @Enclosure.Complex.IsNear.im_isNear qz93 Bool.false 9543334627858149 2251799813685248 25000000118401 19733500000000000000 Bool.false 865992821999011 562949953421312 200000000039467 78934000000000000000 (ep587 (@congrArg Complex Complex qz88 qz404 Complex.log (BSN.w_shift_mk qz12 Bool.false 138478 1000 2 qz13 rfl)) (@Enclosure.Complex.IsNear.of_parts qz401 Bool.false 9543334627858149 2251799813685248 25000000118401 19733500000000000000 Bool.false 865992821999011 562949953421312 200000000039467 78934000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz401) (@HMul.hMul Real Real Real qz0 qz98 qz661) Bool.false 9543334627858149 2251799813685248 25000000118401 19733500000000000000 (Enclosure.clog_re_eq 9000 276956 4000 76785625936 16000000 rfl rfl rfl) (ep592 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz401) qz405 Bool.false 865992821999011 562949953421312 200000000039467 78934000000000000000 (Enclosure.clog_im_eq 9000 276956 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz405 (@HSub.hSub Real Real Real qz391 qz99 qz403) Bool.false 865992821999011 562949953421312 200000000039467 78934000000000000000 (BSN.arctan_recip 276956 9000 rfl rfl) ep594))))

noncomputable abbrev qz101 := (@ep586 1 (BSN.w_sub_half_mk qz279 Bool.false 138478 1000 2 qz281 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz400 Bool.false 7000 4000 0 1 Bool.false 276956 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) (Enclosure.Real.IsNear.const Bool.false 276956 4000)))

noncomputable def ep599 := @ep582 13847800002732655613 78934000000000000000000 ep583 111570536205403164883 1125899906842624000 14022800003561462613 78934000000000000000000 (@ep584 66803342395007043 9007199254740992 175000000828807 78934000000000000000 (ep585 qz101) ep595 rfl) (@ep596 59960477002389522629 562949953421312000 13847800002732655613 78934000000000000000000 (ep597 qz101) ep598 rfl) rfl

noncomputable def ep600 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz94 qz97) (@HMul.hMul Real Real Real qz0 qz96 qz95) 6061949753993077 2251799813685248 1400000000276269 315736000000000000000 660770946298270378611 2251799813685248000

noncomputable def ep601 := nat_lit 1501574191089681195925605029173526528

noncomputable def ep602 := @Enclosure.Real.IsNear.mulLit_ff qz94 qz97 7000 4000 0 1 865992821999011 562949953421312 200000000039467 78934000000000000000

noncomputable def ep603 := @Enclosure.Real.IsNear.mulLit_ff qz96 qz95 276956 4000 0 1 9543334627858149 2251799813685248 25000000118401 19733500000000000000

noncomputable def ep604 := @ep600 1730975008197966839 19733500000000000000000 ep601 666832896052263455611 2251799813685248000 3636950016430467303 39467000000000000000000 (@ep602 6061949753993077 2251799813685248 1400000000276269 315736000000000000000 (ep585 qz101) ep598 rfl) (@ep603 660770946298270378611 2251799813685248000 1730975008197966839 19733500000000000000000 (ep597 qz101) ep595 rfl) rfl

noncomputable def ep605 := @Enclosure.Complex.IsNear.of_eq qz88 qz404 Bool.false 9000 4000 0 1 Bool.false 276956 4000 0 1 (BSN.w_shift_mk qz12 Bool.false 138478 1000 2 qz13 rfl)

noncomputable abbrev qz406 := (ep605 (@Enclosure.Complex.IsNear.mk qz660 qz659 Bool.false 9000 4000 0 1 Bool.false 276956 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 276956 4000)))

noncomputable abbrev qz102 := qz406

noncomputable def ep606 := ep580 (@ep581 39467000000000000000000 (ep599 rfl) (ep604 rfl)) qz102 rfl rfl rfl rfl rfl rfl

noncomputable abbrev qz103 := qz395

noncomputable def ep607 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re qz103) (Complex.re ↑qz2)) (@HMul.hMul Real Real Real qz0 (Complex.im qz103) (Complex.im ↑qz2)) 120447 131072 1 524288 0 1 0 1 120447 120447

noncomputable def ep608 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz103) (Complex.re ↑qz2) 1 2 0 1 120447 65536 1 262144 120447 131072 1 524288

noncomputable abbrev qz104 := (@Enclosure.Complex.IsNear.of_eq qz395 (Complex.mk (Enclosure.sfrac Bool.false 1 2) qz547) Bool.false 1 2 0 1 Bool.false 0 1 0 1 BSN.half_c_mk (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 2) qz547 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz402 qz549))

noncomputable def ep609 := ep608 (@Enclosure.Complex.IsNear.re_isNear qz103 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz104) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz2) qz2 Bool.false 120447 65536 1 262144 (Complex.ofReal_re qz2) EMRow48.d4)

noncomputable def ep610 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz103) (Complex.im ↑qz2) 0 1 0 1 0 1 0 1 0 1 0 1

noncomputable def ep611 := ep610 (@Enclosure.Complex.IsNear.im_isNear qz103 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz104) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz2) qz10 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz2) (0 : Real) qz10 (Complex.ofReal_im qz2) Enclosure.sfrac_zero_eq) qz22)

noncomputable def ep612 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re qz103) (Complex.im ↑qz2)) (@HMul.hMul Real Real Real qz0 (Complex.im qz103) (Complex.re ↑qz2)) 0 1 0 1 0 1 0 1 0 0

noncomputable def ep613 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz103) (Complex.im ↑qz2) 1 2 0 1 0 1 0 1 0 1 0 1

noncomputable def ep614 := ep613 (@Enclosure.Complex.IsNear.re_isNear qz103 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz104) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz2) qz10 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz2) (0 : Real) qz10 (Complex.ofReal_im qz2) Enclosure.sfrac_zero_eq) qz22)

noncomputable def ep615 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz103) (Complex.re ↑qz2) 0 1 0 1 120447 65536 1 262144 0 1 0 1

noncomputable def ep616 := ep615 (@Enclosure.Complex.IsNear.im_isNear qz103 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz104) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz2) qz2 Bool.false 120447 65536 1 262144 (Complex.ofReal_re qz2) EMRow48.d4)

noncomputable def ep617 := @ep577 3636950016430467303 39467000000000000000000 (ep606 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz103 (↑qz2) Bool.false 120447 131072 1 524288 Bool.false 0 1 0 1 (@ep607 131072 1 524288 (ep609 rfl) (ep611 rfl) rfl rfl) (@ep612 1 0 1 (ep614 rfl) (ep616 rfl) rfl rfl))

noncomputable abbrev qz105 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)

noncomputable abbrev qz407 := (@Nat.cast Complex Complex.instNatCast 1)

noncomputable abbrev qz106 := (@HMul.hMul Complex Complex Complex qz387 (@HMul.hMul Complex Complex Complex qz387 (2 : Complex) qz407) (@HSub.hSub Complex Complex Complex qz388 (@HMul.hMul Complex Complex Complex qz387 (2 : Complex) qz407) (1 : Complex)))

noncomputable abbrev qz408 := (@HPow.hPow Complex Int Complex qz658 qz654 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz107 := qz408

noncomputable def ep618 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz79 (@HMul.hMul Complex Complex Complex qz78 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz87 qz88 (@HSub.hSub Int Int Int qz398 qz89 (@HMul.hMul Int Int Int qz399 qz90 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz79 (@HMul.hMul Complex Complex Complex qz78 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz87 qz88 (@HSub.hSub Int Int Int qz398 qz89 (@HMul.hMul Int Int Int qz399 qz90 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli qz105)) qz106) qz107)) Bool.false 2684859 68719476736 3 68719476736

noncomputable def ep619 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz79 (@HMul.hMul Complex Complex Complex qz78 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz87 qz88 (@HSub.hSub Int Int Int qz398 qz89 (@HMul.hMul Int Int Int qz399 qz90 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli qz105)) qz106) qz107) Bool.false 0 1 0 1 Bool.false

noncomputable def ep620 := @ep619 0 1 0 1 Bool.false 2684859 68719476736 3 68719476736 Bool.true 61965650767 51539607552000 69239 51539607552000 Bool.false 2684859 2684859 68719476736 3 68719476736 Bool.true 61965650767 61965650767 51539607552000 69239

noncomputable def ep621 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz79 (@HMul.hMul Complex Complex Complex qz78 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz87 qz88 (@HSub.hSub Int Int Int qz398 qz89 (@HMul.hMul Int Int Int qz399 qz90 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep622 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli qz105)) qz106) qz107 Bool.false 2684859 68719476736 3 68719476736 Bool.true 61965650767 51539607552000 69239 51539607552000

noncomputable abbrev qz108 := (Complex.re qz408)

noncomputable abbrev qz109 := (Complex.im qz408)

noncomputable def ep623 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli qz105)) qz106)) qz108) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli qz105)) qz106)) qz109) 2684859 68719476736 3 68719476736 0 1 0

noncomputable def ep624 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli qz105)) qz106)) qz108 1 12 0 1 8054577 17179869184 9 17179869184 2684859

noncomputable def ep625 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli qz105)) qz106) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz10) Bool.false 1 12 0 1 Bool.false 0 1 0 1

noncomputable abbrev qz409 := (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 12) qz10 Bool.false 1 12 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 12) qz22)

noncomputable def ep626 := @Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli qz105)) qz106) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep625 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz409)

noncomputable def ep627 := @Enclosure.Complex.IsNear.re_isNear qz107 Bool.false 8054577 17179869184 9 17179869184 Bool.true 61965650767 4294967296000 69239 4294967296000

noncomputable abbrev qz663 := (@instHPow Complex Nat (@NPow.toPow Complex (@Monoid.toNPow Complex (@Semiring.toMonoid Complex Complex.instSemiring))))

noncomputable abbrev qz410 := (@HPow.hPow Complex Nat Complex qz663 qz654 1)

noncomputable abbrev qz110 := (@Inv.inv Complex Complex.instInv qz410)

noncomputable def ep628 := @Enclosure.Complex.IsNear.of_eq qz107 qz110 Bool.false 8054577 17179869184 9 17179869184 Bool.true 61965650767 4294967296000 69239

noncomputable def ep629 := @Enclosure.Complex.IsNear.of_parts qz110 Bool.false 8054577 17179869184 9 17179869184 Bool.true 61965650767 4294967296000 69239

noncomputable abbrev qz111 := (Complex.re qz410)

noncomputable abbrev qz112 := (@MonoidWithZeroHom Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz113 := (@MonoidWithZeroHom.funLike Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz114 := qz410

noncomputable def ep630 := @Enclosure.Real.IsNear.mulLit_ff qz111 (@Inv.inv Real Real.instInv (@DFunLike.coe qz112 Complex (fun (x : Complex) => Real) qz113 Complex.normSq qz114)) 9000 4000 0 1 894953 4294967296 1 4294967296

noncomputable def ep631 := @Enclosure.Complex.IsNear.re_isNear qz114 Bool.false 9000 4000 0 1 Bool.false 276956 4000 0 1

noncomputable def ep632 := @Enclosure.Complex.IsNear.of_eq qz114 qz88 Bool.false 9000 4000 0 1 Bool.false 276956 4000 0

noncomputable def ep633 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz112 Complex (fun (x : Complex) => Real) qz113 Complex.normSq qz114)) Bool.false 894953 4294967296 1 4294967296 894953 4294967296 1

noncomputable abbrev qz115 := (Complex.im qz410)

noncomputable abbrev qz411 := (@instHAdd Real Real.instAdd)

noncomputable def ep634 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz112 Complex (fun (x : Complex) => Real) qz113 Complex.normSq qz114) (@HAdd.hAdd Real Real Real qz411 (@HMul.hMul Real Real Real qz0 qz111 qz111) (@HMul.hMul Real Real Real qz0 qz115 qz115)) Bool.false 4799101621 1000000 0 1

noncomputable def ep635 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz111 qz111) (@HMul.hMul Real Real Real qz0 qz115 qz115) 81 16 0 1 4794039121 1000000

noncomputable def ep636 := @Enclosure.Real.IsNear.mulLit_ff qz111 qz111 9000 4000 0 1 9000 4000 0 1

noncomputable def ep637 := @Enclosure.Real.IsNear.mulLit_ff qz115 qz115 276956 4000 0 1 276956 4000 0 1

noncomputable def ep638 := @Enclosure.Complex.IsNear.im_isNear qz114 Bool.false 9000 4000 0 1 Bool.false 276956 4000 0 1

noncomputable abbrev qz116 := (ep631 (@ep632 1 (BSN.pow_one_c qz389) qz406))

noncomputable abbrev qz117 := (ep638 (@ep632 1 (BSN.pow_one_c qz389) qz406))

noncomputable def ep639 := @ep635 0 1 76785625936 4799101621 1000000 0 1 (@ep636 81 16 0 1 qz116 qz116 rfl) (@ep637 4794039121 1000000 0 1 qz117 qz117 rfl)

noncomputable def ep640 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz112 Complex (fun (x : Complex) => Real) qz113 Complex.normSq qz114) 4799101621 1000000 0 1 447476 447477 2147483648 (ep634 (Enclosure.Complex.normSq_eq_mul_add_mul qz114) (ep639 rfl rfl)) rfl

noncomputable def ep641 := @Enclosure.Real.IsNear.of_eq (Complex.re qz110) (@HMul.hMul Real Real Real qz0 qz111 (@Inv.inv Real Real.instInv (@DFunLike.coe qz112 Complex (fun (x : Complex) => Real) qz113 Complex.normSq qz114))) Bool.false 8054577 17179869184 9 17179869184 (Enclosure.Complex.inv_re_eq_mul qz114) (@ep630 8054577 17179869184 9 17179869184 qz116 (@ep633 4294967296 (ep640 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep642 := @Enclosure.Real.IsNear.of_eq (Complex.im qz110) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz115) (@Inv.inv Real Real.instInv (@DFunLike.coe qz112 Complex (fun (x : Complex) => Real) qz113 Complex.normSq qz114))) Bool.true 61965650767 4294967296000 69239 4294967296000 (Enclosure.Complex.inv_im_eq_mul qz114)

noncomputable def ep643 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz115) (@Inv.inv Real Real.instInv (@DFunLike.coe qz112 Complex (fun (x : Complex) => Real) qz113 Complex.normSq qz114)) 276956 4000 0 1 894953 4294967296 1

noncomputable def ep644 := @ep643 4294967296 61965650767 4294967296000 69239 4294967296000 (@Enclosure.Real.IsNear.neg qz115 Bool.false 276956 4000 0 1 qz117) (@ep633 4294967296 (ep640 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep645 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli qz105)) qz106)) qz109 0 1 0 1 61965650767 4294967296000 69239 4294967296000 0

noncomputable def ep646 := @Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli qz105)) qz106) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep625 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz409)

noncomputable def ep647 := @Enclosure.Complex.IsNear.im_isNear qz107 Bool.false 8054577 17179869184 9 17179869184 Bool.true 61965650767 4294967296000 69239 4294967296000

noncomputable abbrev qz118 := (@ep628 4294967296000 (BSN.zpow_one_sub_two_mul qz389 1 1 rfl rfl) (@ep629 4294967296000 ep641 (ep642 ep644)))

noncomputable def ep648 := @ep623 1 2684859 2684859 68719476736 3 68719476736 (@ep624 68719476736 3 68719476736 ep626 (ep627 qz118) rfl) (@ep645 1 0 1 ep646 (ep647 qz118) rfl) rfl

noncomputable def ep649 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli qz105)) qz106)) qz109) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli qz105)) qz106)) qz108) 61965650767 51539607552000 69239 51539607552000 0 1 0

noncomputable def ep650 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli qz105)) qz106)) qz109 1 12 0 1 61965650767 4294967296000 69239 4294967296000 61965650767

noncomputable def ep651 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli qz105)) qz106)) qz108 0 1 0 1 8054577 17179869184 9 17179869184 0

noncomputable def ep652 := @ep649 1 61965650767 61965650767 51539607552000 69239 51539607552000 (@ep650 51539607552000 69239 51539607552000 ep626 (ep647 qz118) rfl) (@ep651 1 0 1 ep646 (ep627 qz118) rfl) rfl

noncomputable abbrev qz119 := (@Enclosure.Complex.IsNear.mk qz547 qz547 Bool.false 0 1 0 1 Bool.false 0 1 0 1 qz549 qz549)

noncomputable def ep653 := @ep620 51539607552000 (@ep621 0 1 0 1 (BSN.stirling_sum_base qz88) qz119) (ep622 (ep648 rfl) (ep652 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep654 := @ep574 1532753464295754375793 6755399441055744000 ep566 ep557 (ep617 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep618 Bool.true 61965650767 51539607552000 69239 51539607552000 (BSN.stirling_sum_succ qz88 0 1 rfl) (ep653 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep655 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz81 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz12 2) Bool.false 9542337121703653 1125899906842624 25000000118401 9866750000000000000 Bool.false 878182476055971 281474976710656

noncomputable abbrev qz120 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz274 qz390 qz407))

noncomputable def ep656 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz12 2) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz12 1) qz120) Bool.false 9542337121703653 1125899906842624 25000000118401 9866750000000000000 Bool.false 878182476055971 281474976710656 200000000039467 39467000000000000000

noncomputable def ep657 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz12 1) qz120 Bool.false 9542161028044517 2251799813685248 25000000118401 19733500000000000000 Bool.false 882247125730723 562949953421312 200000000039467 78934000000000000000 Bool.false

noncomputable def ep658 := nat_lit 42974865905548222989580147621888

noncomputable def ep659 := nat_lit 988745567982242630342912507904

noncomputable abbrev qz121 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz274 qz390 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep660 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz12 1) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz12 0) qz121) Bool.false 9542161028044517 2251799813685248 25000000118401 19733500000000000000 Bool.false 882247125730723 562949953421312 200000000039467 78934000000000000000

noncomputable def ep661 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz12 0) qz121 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz412 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz659))

noncomputable def ep662 := @Enclosure.Complex.IsNear.of_eq qz121 qz412 Bool.false 9542161028044517 2251799813685248 25000000118401 19733500000000000000 Bool.false 882247125730723 562949953421312 200000000039467 78934000000000000000

noncomputable def ep663 := nat_lit 6140420190125668921255760989378394480523018240

noncomputable def ep664 := nat_lit 12667896443958242078748252052585775041609728

noncomputable def ep665 := nat_lit 46695579680797011432370952450924520603648

noncomputable def ep666 := BSN.log_dyadic_bound 11169625936 142241625936 3 2 ep663 1048576 394670 ep664 ep665 165020 153411251872 131072000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 11169625936) (BSN.artanhQ 142241625936) 0 2 ep664 ep663 ep665 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep667 := @Enclosure.Real.IsNear.mulLit_ff qz98 (Real.log (Enclosure.sfrac Bool.false 76705625936 16000000)) 1 2 0 1 9542161028044517 1125899906842624 25000000118401 9866750000000000000 9542161028044517 2251799813685248 25000000118401 19733500000000000000 qz402 (BSN.isNear_log_sfrac 76705625936 16000000 9542161028044517 1125899906842624 25000000118401 9866750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 76705625936) qz662)) Bool.false 320181793348569838649344 37778931862957161709568 1000000004736040 394670000000000000000 9542161028044517 1125899906842624 25000000118401 9866750000000000000 (BSN.log_rat_reduce_isNear 76705625936 16000000 12 153411251872 131072000000 165020 1048576 24973259072661432 36028797018963968 394670 1000000000000000 rfl rfl rfl rfl (ep666 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep668 := BSN.arctan_dyadic_bound_f 1000 276956 1 0 1048576 394670 0 1 1 0 1 1 3786 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 276956) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 276956) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz413 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable abbrev qz414 := (@Nat.cast Real Real.instNatCast 276956)

noncomputable def ep669 := @Enclosure.Real.IsNear.subLit_ff_p qz99 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz413 qz414)) 884279719003555 562949953421312 1 2000000000000000 3786 1048576 1 394670 925103162110218600448 882247125730723 562949953421312 200000000039467 78934000000000000000 qz100 (ep668 rfl) rfl rfl

noncomputable abbrev qz122 := (@HAdd.hAdd Complex Complex Complex qz274 qz390 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz415 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz659)

noncomputable def ep670 := @ep661 9542161028044517 2251799813685248 25000000118401 19733500000000000000 Bool.false 882247125730723 562949953421312 200000000039467 78934000000000000000 Bool.false 9542161028044517 9542161028044517 2251799813685248 25000000118401 19733500000000000000 Bool.false 882247125730723 882247125730723 562949953421312 200000000039467 78934000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz12 0) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz12) qz119) (ep662 (@congrArg Complex Complex qz122 qz415 Complex.log (BSN.w_shift_mk qz12 Bool.false 138478 1000 0 qz13 rfl)) (@Enclosure.Complex.IsNear.of_parts qz412 Bool.false 9542161028044517 2251799813685248 25000000118401 19733500000000000000 Bool.false 882247125730723 562949953421312 200000000039467 78934000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz412) (@HMul.hMul Real Real Real qz0 qz98 (Real.log (Enclosure.sfrac Bool.false 76705625936 16000000))) Bool.false 9542161028044517 2251799813685248 25000000118401 19733500000000000000 (Enclosure.clog_re_eq 1000 276956 4000 76705625936 16000000 rfl rfl rfl) (ep667 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz412) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz414 qz413)) Bool.false 882247125730723 562949953421312 200000000039467 78934000000000000000 (Enclosure.clog_im_eq 1000 276956 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz414 qz413)) (@HSub.hSub Real Real Real qz391 qz99 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz413 qz414))) Bool.false 882247125730723 562949953421312 200000000039467 78934000000000000000 (BSN.arctan_recip 276956 1000 rfl rfl) ep669)))) rfl rfl

noncomputable abbrev qz416 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz659))

noncomputable def ep671 := @Enclosure.Complex.IsNear.of_eq qz120 qz416 Bool.false 9542513215362789 2251799813685248 25000000118401 19733500000000000000 Bool.false 874117826381219 562949953421312 200000000039467 78934000000000000000

noncomputable def ep672 := nat_lit 6144565457328645679243159064142591713163018240

noncomputable def ep673 := nat_lit 12726873055780653826115451879549632449609728

noncomputable def ep674 := nat_lit 47098211289686656771484061322371048603648

noncomputable def ep675 := BSN.log_dyadic_bound 11193625936 142265625936 3 2 ep672 1048576 394670 ep673 ep674 165348 153459251872 131072000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 11193625936) (BSN.artanhQ 142265625936) 0 2 ep673 ep672 ep674 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep676 := @Enclosure.Real.IsNear.mulLit_ff qz98 (Real.log (Enclosure.sfrac Bool.false 76729625936 16000000)) 1 2 0 1 9542513215362789 1125899906842624 25000000118401 9866750000000000000 9542513215362789 2251799813685248 25000000118401 19733500000000000000 qz402 (BSN.isNear_log_sfrac 76729625936 16000000 9542513215362789 1125899906842624 25000000118401 9866750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 76729625936) qz662)) Bool.false 320193610793992058830848 37778931862957161709568 1000000004736040 394670000000000000000 9542513215362789 1125899906842624 25000000118401 9866750000000000000 (BSN.log_rat_reduce_isNear 76729625936 16000000 12 153459251872 131072000000 165348 1048576 24973259072661432 36028797018963968 394670 1000000000000000 rfl rfl rfl rfl (ep675 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep677 := BSN.arctan_dyadic_bound_f 5000 276956 1 0 1048576 394670 0 1 1 0 1 1 18928 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 276956) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 276956) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz417 := (@Nat.cast Real Real.instNatCast 5000)

noncomputable def ep678 := @Enclosure.Real.IsNear.subLit_ff_p qz99 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz417 qz414)) 884279719003555 562949953421312 1 2000000000000000 18928 1048576 1 394670 916578973915513094144 874117826381219 562949953421312 200000000039467 78934000000000000000 qz100 (ep677 rfl) rfl rfl

noncomputable abbrev qz123 := (@HAdd.hAdd Complex Complex Complex qz274 qz390 qz407)

noncomputable abbrev qz418 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz659)

noncomputable def ep679 := @ep657 9542513215362789 2251799813685248 25000000118401 19733500000000000000 Bool.false 874117826381219 562949953421312 200000000039467 78934000000000000000 Bool.false ep658 9542337121703653 1125899906842624 25000000118401 9866750000000000000 Bool.false ep659 878182476055971 281474976710656 200000000039467 39467000000000000000 (ep660 (BSN.log_sum_c_succ qz12 0 1 rfl) (ep670 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep671 (@congrArg Complex Complex qz123 qz418 Complex.log (BSN.w_shift_mk qz12 Bool.false 138478 1000 1 qz13 rfl)) (@Enclosure.Complex.IsNear.of_parts qz416 Bool.false 9542513215362789 2251799813685248 25000000118401 19733500000000000000 Bool.false 874117826381219 562949953421312 200000000039467 78934000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz416) (@HMul.hMul Real Real Real qz0 qz98 (Real.log (Enclosure.sfrac Bool.false 76729625936 16000000))) Bool.false 9542513215362789 2251799813685248 25000000118401 19733500000000000000 (Enclosure.clog_re_eq 5000 276956 4000 76729625936 16000000 rfl rfl rfl) (ep676 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz416) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz414 qz417)) Bool.false 874117826381219 562949953421312 200000000039467 78934000000000000000 (Enclosure.clog_im_eq 5000 276956 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz414 qz417)) (@HSub.hSub Real Real Real qz391 qz99 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz417 qz414))) Bool.false 874117826381219 562949953421312 200000000039467 78934000000000000000 (BSN.arctan_recip 276956 5000 rfl rfl) ep678)))) rfl rfl

noncomputable def ep680 := @ep567 ep557 Bool.false 9542337121703653 1125899906842624 25000000118401 9866750000000000000 Bool.false 878182476055971 281474976710656 200000000039467 39467000000000000000 Bool.true ep568 122611472276970241883 1125899906842624000 ep562 ep563 Bool.false ep569 1511677084870411071793 6755399441055744000 ep559 ep557 (@ep570 1125899906842624000 ep565 ep563 Bool.false 1532753464295754375793 6755399441055744000 ep566 ep557 (BSN.logGammaStirling_unfold 1 qz88) (ep654 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep655 200000000039467 39467000000000000000 (BSN.log_sum_c_eq qz12 2) (ep656 (BSN.log_sum_c_succ qz12 1 2 rfl) (ep679 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz124 := (@HDiv.hDiv Real Real Real qz272 qz279 (2 : Real))

noncomputable def ep681 := @Enclosure.Real.IsNear.mulLit_ff qz124 (Real.log Real.pi) 138478 2000 0 1 75021 65536 1 262144 5194379019 65536000 69239 262144000 (@Enclosure.Real.IsNear.of_eq qz124 (Enclosure.sfrac Bool.false 138478 2000) Bool.false 138478 2000 0 1 (BSN.t_half_eq qz12 Bool.false 138478 1000 qz13) (Enclosure.Real.IsNear.const Bool.false 138478 2000)) EMRow48.d5 rfl

noncomputable def ep682 := @ep560 69239 262144000 ep561 976244572639205568817 6755399441055744000 ep556 ep557 (@ep564 ep559 ep557 (ep680 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep681 rfl rfl

noncomputable def ep683 := nat_lit 8343231273428118467932459542611816567149722528482396249785251209208860551840000

noncomputable def ep684 := nat_lit 16761747552813805560721483816730768297692462794698407414442072874000100000000

noncomputable def ep685 := nat_lit 21824181934369087921296225923518145955767295015786287994576085048989110807200000

noncomputable def ep686 := BSN.sin_dyadic_bound_f 3373183070 2147483648 3 2 1048576 395056 ep683 ep79 ep684 ep685 ep81 ep684 1048575 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3373183070) qz15 0 2 ep683 ep79 ep684 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3373183070) qz16 0 2 ep685 ep81 ep684 rfl rfl rfl rfl) rfl rfl

noncomputable def ep687 := @ep555 262144 Bool.false 1048575 1048576 1 197335 (@ep558 151533101 1048576 95 262144 ep682 rfl) (Enclosure.sfrac_false_div 151533101 1048576) (BSN.cos_reduce3 qz392 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 237366656525988677025792) qz25) 226375608064910080 72057594037927936 Bool.false 1048575 1048576 22 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q3 151533101 1048576 226375608064910080 72057594037927936 22 237366656525988677025792 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1048575 1048576 237366656525988677025792 151115727451828646838272 3373183070 2147483648 395056 394670 (ep686 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep688 := nat_lit 4435660208234945266798001

noncomputable def ep689 := nat_lit 276736450044036686807040000

noncomputable def ep690 := nat_lit 727757833946866065491124044609

noncomputable def ep691 := nat_lit 109219574738879959182134476800000

noncomputable abbrev qz419 := (@HPow.hPow Complex Complex Complex qz538 (@Nat.cast Complex Complex.instNatCast 35) qz539)

noncomputable abbrev qz125 := qz419

noncomputable abbrev qz420 := (@Nat.cast Complex Complex.instNatCast 35)

noncomputable abbrev qz126 := (@HAdd.hAdd Complex Complex Complex qz274 (@HDiv.hDiv Complex Complex Complex qz396 qz420 (@HSub.hSub Complex Complex Complex qz388 qz273 (1 : Complex))) qz395)

noncomputable abbrev qz127 := (@instHSub Nat instSubNat)

noncomputable abbrev qz421 := qz663

noncomputable abbrev qz128 := qz421

noncomputable abbrev qz129 := qz420

noncomputable def ep692 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz5 1 35) (@HAdd.hAdd Complex Complex Complex qz4 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 35, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz7) (@HMul.hMul Complex Complex Complex qz78 qz125 (@HAdd.hAdd Complex Complex Complex qz4 qz126 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1))))))) Bool.false ep550 ep551 ep552

noncomputable def ep693 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 35, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz7) (@HMul.hMul Complex Complex Complex qz78 qz125 (@HAdd.hAdd Complex Complex Complex qz4 qz126 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))))) Bool.false 995626035037 1099511627776 1430855759097807 216972127067176960

noncomputable def ep694 := nat_lit 9500816563844814193814441

noncomputable def ep695 := nat_lit 15166270601717556465425029283

noncomputable def ep696 := nat_lit 20482837130446027177224499

noncomputable def ep697 := nat_lit 7589814083846818396522409609

noncomputable def ep698 := nat_lit 209974553320733061742190336984202870784

noncomputable def ep699 := nat_lit 4877059975817635790143336686892875776

noncomputable def ep700 := @ep693 Bool.false 99004585649 1099511627776 1430662841244447 216972127067176960 Bool.true ep694 ep551 ep695 ep553 Bool.true ep696 ep689 ep697 ep691 Bool.false ep698 ep550 ep551 ep552 ep553 Bool.false ep699 ep688 ep689

noncomputable def ep701 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 35, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz7) (BSN.headSumC qz5 35) Bool.false 995626035037 1099511627776 1430855759097807 216972127067176960 Bool.false 99004585649 1099511627776 1430662841244447

noncomputable abbrev qz664 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 34) qz7)

noncomputable def ep702 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 35) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 34) qz664) Bool.false 995626035037 1099511627776 1430855759097807 216972127067176960 Bool.false 99004585649 1099511627776 1430662841244447 216972127067176960

noncomputable def ep703 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 34) qz664 Bool.false 129009019787 137438953472 351118365649023 54243031766794240 Bool.true 43002014519 549755813888 10969668124879 1695094742712320 Bool.true

noncomputable abbrev qz665 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 33) qz7)

noncomputable def ep704 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 34) (@HAdd.hAdd Complex Complex Complex qz4 qz65 qz665) Bool.false 129009019787 137438953472 351118365649023 54243031766794240 Bool.true 43002014519 549755813888 10969668124879 1695094742712320

noncomputable def ep705 := @Enclosure.Complex.IsNear.addLitP qz65 qz665 Bool.false 106826879495 137438953472 688771609329129 108486063533588480 Bool.true 14291011597 1099511627776 1377301595172203 216972127067176960 Bool.false

noncomputable abbrev qz666 := (Real.log (Enclosure.sfrac Bool.false 33 1))

noncomputable abbrev qz130 := (@HMul.hMul Real Real Real qz269 qz279 qz666)

noncomputable abbrev qz422 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 33)))

noncomputable def ep706 := @Enclosure.Complex.IsNear.of_eq qz665 (Complex.mk (@HMul.hMul Real Real Real qz0 qz422 (Real.cos qz130)) (@HMul.hMul Real Real Real qz0 qz422 (@Neg.neg Real Real.instNeg (Real.sin qz130)))) Bool.false 5545535073 34359738368 13465121968917 108486063533588480 Bool.true 71713017441 1099511627776 26815924812309 216972127067176960 (BSN.cpow_neg_s_mk qz12 138478 1000 33 qz13 rfl)

noncomputable abbrev qz423 := (Real.sqrt (@Nat.cast Real Real.instNatCast 33))

noncomputable abbrev qz424 := (@Nat.cast Real Real.instNatCast 33)

noncomputable abbrev qz667 := (@HDiv.hDiv Real Real Real qz1 qz424 qz14)

noncomputable def ep707 := @Enclosure.Real.IsNear.inv_image qz423 6023611 1048576 1 1048576 91266 91267 524288 (@Enclosure.Real.IsNear.of_eq qz423 (Real.sqrt qz667) Bool.false 6023611 1048576 1 1048576 (BSN.sqrt_natCast_div_one 33) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz667) Bool.false 6023611 1048576 1 1048576 6023611 1048576 1 1048576 (BSN.sqrt_enclosure 33 1 3011805 3011806 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep708 := BSN.log_dyadic_bound 1 65 2 1 12675 524288 197335 1 1 16133 66 64 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1) (BSN.artanhQ 65) 0 1 1 12675 1 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep709 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz666 138478 1000 0 1 15746868335186131 4503599627370496 40000000039467 7893400000000000000 1090297416659952524309 2251799813685248000 2769560002732655613 3946700000000000000000 qz18 (BSN.isNear_log_sfrac 33 1 15746868335186131 4503599627370496 40000000039467 7893400000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz667) Bool.false 66047152845744529997824 18889465931478580854784 1000000000986675 197335000000000000000 15746868335186131 4503599627370496 40000000039467 7893400000000000000 (BSN.log_rat_reduce_isNear 33 1 5 66 64 16133 524288 24973259072661432 36028797018963968 197335 1000000000000000 rfl rfl rfl rfl (ep708 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep710 := nat_lit 462664569859208244172870939963650625

noncomputable def ep711 := BSN.cos_dyadic_bound_f 824739055 2147483648 2 1 1048576 395056 ep710 ep62 ep710 ep710 ep63 ep710 972192 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 824739055) qz20 0 1 ep710 ep62 ep710 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 824739055) qz21 0 1 ep710 ep63 ep710 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz425 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 253854649) qz17)

noncomputable def ep712 := @Enclosure.Real.IsNear.cos_image qz130 qz425 Bool.false 253854649 524288 737 1048576 Bool.false 972192 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz130 Bool.false 1090297416659952524309 2251799813685248000 2769560002732655613 3946700000000000000000 253854649 524288 737 1048576 (ep709 rfl) rfl) (Enclosure.sfrac_false_div 253854649 524288) (BSN.cos_reduce0 qz425 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 29017925815620346052608) qz19) 226375608064910080 72057594037927936 Bool.false 972192 1048576 77 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q0 253854649 524288 226375608064910080 72057594037927936 77 29017925815620346052608 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 972192 1048576 29017925815620346052608 75557863725914323419136 824739055 2147483648 395056 394670 (ep711 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep713 := BSN.sin_dyadic_bound_f 824739055 2147483648 2 1 1048576 395056 ep710 ep58 ep710 ep710 ep59 ep710 392877 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 824739055) qz15 0 1 ep710 ep58 ep710 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 824739055) qz16 0 1 ep710 ep59 ep710 rfl rfl rfl rfl) rfl rfl

noncomputable def ep714 := @Enclosure.Real.IsNear.sin_image qz130 qz425 Bool.false 253854649 524288 737 1048576 Bool.false 392877 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz130 Bool.false 1090297416659952524309 2251799813685248000 2769560002732655613 3946700000000000000000 253854649 524288 737 1048576 (ep709 rfl) rfl) (Enclosure.sfrac_false_div 253854649 524288) (BSN.sin_reduce0 qz425 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 29017925815620346052608) qz19) 226375608064910080 72057594037927936 Bool.false 392877 1048576 77 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q0 253854649 524288 226375608064910080 72057594037927936 77 29017925815620346052608 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 392877 1048576 29017925815620346052608 75557863725914323419136 824739055 2147483648 395056 394670 (ep713 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz426 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 33))) Bool.false 182533 1048576 1 1048576 182533 1048576 1 1048576 (ep707 rfl rfl) rfl)

noncomputable def ep715 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz422 (Real.cos qz130)) (@HMul.hMul Real Real Real qz0 qz422 (@Neg.neg Real Real.instNeg (Real.sin qz130))) Bool.false 5545535073 34359738368 13465121968917 108486063533588480 Bool.true 71713017441 1099511627776 26815924812309 216972127067176960 (@Enclosure.Real.IsNear.mulLit_ff qz422 (Real.cos qz130) 182533 1048576 1 1048576 30381 32768 146484471 206920744960 5545535073 34359738368 13465121968917 108486063533588480 qz426 (@Enclosure.Real.IsNear.recentre' (Real.cos qz130) Bool.false 972192 1048576 146484471 206920744960 30381 32768 146484471 206920744960 (ep712 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz422 (@Neg.neg Real Real.instNeg (Real.sin qz130)) 182533 1048576 1 1048576 392877 1048576 146484471 206920744960 71713017441 1099511627776 26815924812309 216972127067176960 qz426 (@Enclosure.Real.IsNear.neg (Real.sin qz130) Bool.false 392877 1048576 146484471 206920744960 (@Enclosure.Real.IsNear.recentre' (Real.sin qz130) Bool.false 392877 1048576 146484471 206920744960 392877 1048576 146484471 206920744960 (ep714 rfl rfl) rfl)) rfl)

noncomputable def ep716 := @ep705 5545535073 34359738368 13465121968917 108486063533588480 Bool.true 71713017441 1099511627776 26815924812309 216972127067176960 Bool.false 4432716166993455087616 129009019787 137438953472 351118365649023 54243031766794240 Bool.true 94562429962865751359488 43002014519 549755813888 10969668124879 1695094742712320 EMRow48.d9 (ep706 ep715) rfl rfl

noncomputable abbrev qz668 := (Real.log (Enclosure.sfrac Bool.false 34 1))

noncomputable abbrev qz131 := (@HMul.hMul Real Real Real qz269 qz279 qz668)

noncomputable abbrev qz427 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 34)))

noncomputable def ep717 := @Enclosure.Complex.IsNear.of_eq qz664 (Complex.mk (@HMul.hMul Real Real Real qz0 qz427 (Real.cos qz131)) (@HMul.hMul Real Real Real qz0 qz427 (@Neg.neg Real Real.instNeg (Real.sin qz131)))) Bool.true 36446123259 1099511627776 5276459300343 43394425413435392 Bool.false 185008614687 1099511627776 5309064251987 43394425413435392 (BSN.cpow_neg_s_mk qz12 138478 1000 34 qz13 rfl)

noncomputable abbrev qz428 := (Real.sqrt (@Nat.cast Real Real.instNatCast 34))

noncomputable abbrev qz429 := (@Nat.cast Real Real.instNatCast 34)

noncomputable abbrev qz669 := (@HDiv.hDiv Real Real Real qz1 qz429 qz14)

noncomputable def ep718 := @Enclosure.Real.IsNear.inv_image qz428 6114197 1048576 1 1048576 89914 89915 524288 (@Enclosure.Real.IsNear.of_eq qz428 (Real.sqrt qz669) Bool.false 6114197 1048576 1 1048576 (BSN.sqrt_natCast_div_one 34) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz669) Bool.false 6114197 1048576 1 1048576 6114197 1048576 1 1048576 (BSN.sqrt_enclosure 34 1 3057098 3057099 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep719 := BSN.log_dyadic_bound 2 66 2 1 13068 524288 197335 4 4 31784 68 64 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 2) (BSN.artanhQ 66) 0 1 4 13068 4 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep720 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz668 138478 1000 0 1 15881309401485523 4503599627370496 40000000039467 7893400000000000000 1099605981649456126997 2251799813685248000 2769560002732655613 3946700000000000000000 qz18 (BSN.isNear_log_sfrac 34 1 15881309401485523 4503599627370496 40000000039467 7893400000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz669) Bool.false 66611039547888335060992 18889465931478580854784 1000000000986675 197335000000000000000 15881309401485523 4503599627370496 40000000039467 7893400000000000000 (BSN.log_rat_reduce_isNear 34 1 5 68 64 31784 524288 24973259072661432 36028797018963968 197335 1000000000000000 rfl rfl rfl rfl (ep719 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep721 := nat_lit 2732207548387064564019424342318660766216419327570822032107118132885886806065761

noncomputable def ep722 := nat_lit 5822598755594298064797207192885076286421089850038273729142801077989400707681

noncomputable def ep723 := nat_lit 8184977447650005095928678612570212146076415803012389548863068796501681616781921

noncomputable def ep724 := BSN.cos_dyadic_bound_f 2955558827 2147483648 3 2 1048576 395056 ep721 ep72 ep722 ep723 ep75 ep722 202671 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2955558827) qz20 0 2 ep721 ep72 ep722 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2955558827) qz21 0 2 ep723 ep75 ep722 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz430 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16001373) (@Nat.cast Real Real.instNatCast 32768))

noncomputable def ep725 := @Enclosure.Real.IsNear.cos_image qz131 qz430 Bool.false 16001373 32768 737 1048576 Bool.true 202671 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz131 Bool.false 1099605981649456126997 2251799813685248000 2769560002732655613 3946700000000000000000 16001373 32768 737 1048576 (ep720 rfl) rfl) (Enclosure.sfrac_false_div 16001373 32768) (BSN.cos_reduce2 qz430 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6499342594920316665856) qz345) 226375608064910080 72057594037927936 Bool.false 202671 1048576 77 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q2 16001373 32768 226375608064910080 72057594037927936 77 6499342594920316665856 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 202671 1048576 6499342594920316665856 4722366482869645213696 2955558827 2147483648 395056 394670 (ep724 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep726 := nat_lit 4913315508092240776783126050419281318160417917747449038809498398332204730352225

noncomputable def ep727 := nat_lit 12858780218446811266136610844214399043099269924819447420368169365315220025967201

noncomputable def ep728 := BSN.sin_dyadic_bound_f 2955558827 2147483648 3 2 1048576 395056 ep726 ep79 ep722 ep727 ep81 ep722 1028803 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2955558827) qz15 0 2 ep726 ep79 ep722 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2955558827) qz16 0 2 ep727 ep81 ep722 rfl rfl rfl rfl) rfl rfl

noncomputable def ep729 := @Enclosure.Real.IsNear.sin_image qz131 qz430 Bool.false 16001373 32768 737 1048576 Bool.true 1028803 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz131 Bool.false 1099605981649456126997 2251799813685248000 2769560002732655613 3946700000000000000000 16001373 32768 737 1048576 (ep720 rfl) rfl) (Enclosure.sfrac_false_div 16001373 32768) (BSN.sin_reduce2 qz430 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6499342594920316665856) qz345) 226375608064910080 72057594037927936 Bool.false 1028803 1048576 77 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q2 16001373 32768 226375608064910080 72057594037927936 77 6499342594920316665856 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1028803 1048576 6499342594920316665856 4722366482869645213696 2955558827 2147483648 395056 394670 (ep728 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz431 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 34))) Bool.false 179829 1048576 1 1048576 179829 1048576 1 1048576 (ep718 rfl rfl) rfl)

noncomputable def ep730 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz427 (Real.cos qz131)) (@HMul.hMul Real Real Real qz0 qz427 (@Neg.neg Real Real.instNeg (Real.sin qz131))) Bool.true 36446123259 1099511627776 5276459300343 43394425413435392 Bool.false 185008614687 1099511627776 5309064251987 43394425413435392 (@Enclosure.Real.IsNear.mulLit_ft qz427 (Real.cos qz131) 179829 1048576 1 1048576 202671 1048576 146484471 206920744960 36446123259 1099511627776 5276459300343 43394425413435392 qz431 (@Enclosure.Real.IsNear.recentre' (Real.cos qz131) Bool.true 202671 1048576 146484471 206920744960 202671 1048576 146484471 206920744960 (ep725 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz427 (@Neg.neg Real Real.instNeg (Real.sin qz131)) 179829 1048576 1 1048576 1028803 1048576 146484471 206920744960 185008614687 1099511627776 5309064251987 43394425413435392 qz431 (@Enclosure.Real.IsNear.neg (Real.sin qz131) Bool.true 1028803 1048576 146484471 206920744960 (@Enclosure.Real.IsNear.recentre' (Real.sin qz131) Bool.true 1028803 1048576 146484471 206920744960 1028803 1048576 146484471 206920744960 (ep729 rfl rfl) rfl)) rfl)

noncomputable def ep731 := @ep703 36446123259 1099511627776 5276459300343 43394425413435392 Bool.false 185008614687 1099511627776 5309064251987 43394425413435392 Bool.false 136837800304962084798464 995626035037 1099511627776 1430855759097807 216972127067176960 Bool.false 54428346562110199693312 99004585649 1099511627776 1430662841244447 216972127067176960 (ep704 (BSN.head_sum_c_succ qz5 33 34 rfl rfl) (ep716 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep717 ep730) rfl rfl

noncomputable def ep732 := @Enclosure.Complex.IsNear.mul qz125 (@HAdd.hAdd Complex Complex Complex qz4 qz126 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1))))) Bool.true ep694 ep551 ep695 ep553 Bool.true

noncomputable def ep733 := nat_lit 2190335539480066104304373

noncomputable abbrev qz132 := (Complex.re qz419)

noncomputable abbrev qz133 := (Complex.im qz419)

noncomputable def ep734 := @Enclosure.Real.IsNear.subLit_tt_n (@HMul.hMul Real Real Real qz0 qz132 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz126 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz133 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz126 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1))))))) 39146008044714817930749 737963866784097831485440 ep733

noncomputable def ep735 := nat_lit 36406524912959986394044825600

noncomputable def ep736 := nat_lit 2242985849569631185410259

noncomputable def ep737 := nat_lit 2024257364837159839598791283

noncomputable def ep738 := nat_lit 7011259329061324571570646389709649406822753239040

noncomputable def ep739 := @Enclosure.Real.IsNear.mulLit_tf qz132 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz126 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))))) 58292260767 549755813888 3261625305159 27121515883397120 2014641782441

noncomputable abbrev qz670 := (Real.log (Enclosure.sfrac Bool.false 35 1))

noncomputable abbrev qz134 := (@HMul.hMul Real Real Real qz269 qz279 qz670)

noncomputable abbrev qz135 := (Real.sin (@HMul.hMul Real Real Real qz269 qz279 qz670))

noncomputable abbrev qz432 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 35)))

noncomputable abbrev qz671 := (@Neg.neg Real Real.instNeg qz135)

noncomputable def ep740 := @Enclosure.Complex.IsNear.of_eq qz125 (Complex.mk (@HMul.hMul Real Real Real qz0 qz432 (Real.cos qz134)) (@HMul.hMul Real Real Real qz0 qz432 qz671)) Bool.true 58292260767 549755813888 3261625305159 27121515883397120 Bool.true 144735886805 1099511627776 26124345356657 216972127067176960 (BSN.cpow_neg_s_mk qz12 138478 1000 35 qz13 rfl)

noncomputable abbrev qz433 := (Real.sqrt (@Nat.cast Real Real.instNatCast 35))

noncomputable abbrev qz434 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 35) qz14)

noncomputable def ep741 := @Enclosure.Real.IsNear.inv_image qz433 6203459 1048576 1 1048576 88620 88621 524288 (@Enclosure.Real.IsNear.of_eq qz433 (Real.sqrt qz434) Bool.false 6203459 1048576 1 1048576 (BSN.sqrt_natCast_div_one 35) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz434) Bool.false 6203459 1048576 1 1048576 6203459 1048576 1 1048576 (BSN.sqrt_enclosure 35 1 3101729 3101730 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep742 := BSN.log_dyadic_bound 3 67 2 1 13467 524288 197335 9 9 46982 70 64 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 3) (BSN.artanhQ 67) 0 1 9 13467 9 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz136 := qz670

noncomputable def ep743 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz136 138478 1000 0 1 16011859227414739 4503599627370496 40000000039467 7893400000000000000 1108645121046969113621 2251799813685248000 2769560002732655613 3946700000000000000000 qz18 (BSN.isNear_log_sfrac 35 1 16011859227414739 4503599627370496 40000000039467 7893400000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz434) Bool.false 67158605204982549446656 18889465931478580854784 1000000000986675 197335000000000000000 16011859227414739 4503599627370496 40000000039467 7893400000000000000 (BSN.log_rat_reduce_isNear 35 1 5 70 64 46982 524288 24973259072661432 36028797018963968 197335 1000000000000000 rfl rfl rfl rfl (ep742 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep744 := nat_lit 4496315523050965779592359663853561201

noncomputable def ep745 := BSN.sin_dyadic_bound_f 1456177093 2147483648 2 1 1048576 395056 ep744 ep58 ep744 ep744 ep59 ep744 657774 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1456177093) qz15 0 1 ep744 ep58 ep744 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1456177093) qz16 0 1 ep744 ep59 ep744 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz435 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 258126557) qz17)

noncomputable def ep746 := @Enclosure.Real.IsNear.cos_image qz134 qz435 Bool.false 258126557 524288 737 1048576 Bool.true 657774 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz134 Bool.false 1108645121046969113621 2251799813685248000 2769560002732655613 3946700000000000000000 258126557 524288 737 1048576 (ep743 rfl) rfl) (Enclosure.sfrac_false_div 258126557 524288) (BSN.cos_reduce1 qz435 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 51234676672695772381184) qz19) 226375608064910080 72057594037927936 Bool.false 657774 1048576 78 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q1 258126557 524288 226375608064910080 72057594037927936 78 51234676672695772381184 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 657774 1048576 51234676672695772381184 75557863725914323419136 1456177093 2147483648 395056 394670 (ep745 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep747 := nat_lit 160671990157032537806509701239030563909724535431187939308476489479710411021281

noncomputable def ep748 := nat_lit 20216853282829079980848444248257115438557485994426985178477037249852562401

noncomputable def ep749 := nat_lit 481975536764531955259567406828595177498296491321574963955072514364631527939041

noncomputable def ep750 := BSN.cos_dyadic_bound_f 1456177093 2147483648 3 2 1048576 395056 ep747 ep72 ep748 ep749 ep75 ep748 816605 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1456177093) qz20 0 2 ep747 ep72 ep748 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1456177093) qz21 0 2 ep749 ep75 ep748 rfl rfl rfl rfl) rfl rfl

noncomputable def ep751 := @Enclosure.Real.IsNear.sin_image qz134 qz435 Bool.false 258126557 524288 737 1048576 Bool.false 816605 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz134 Bool.false 1108645121046969113621 2251799813685248000 2769560002732655613 3946700000000000000000 258126557 524288 737 1048576 (ep743 rfl) rfl) (Enclosure.sfrac_false_div 258126557 524288) (BSN.sin_reduce1 qz435 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 51234676672695772381184) qz19) 226375608064910080 72057594037927936 Bool.false 816605 1048576 78 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q1 258126557 524288 226375608064910080 72057594037927936 78 51234676672695772381184 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 816605 1048576 51234676672695772381184 75557863725914323419136 1456177093 2147483648 395056 394670 (ep750 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz436 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 35))) Bool.false 177241 1048576 1 1048576 177241 1048576 1 1048576 (ep741 rfl rfl) rfl)

noncomputable def ep752 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz432 (Real.cos qz134)) (@HMul.hMul Real Real Real qz0 qz432 qz671) Bool.true 58292260767 549755813888 3261625305159 27121515883397120 Bool.true 144735886805 1099511627776 26124345356657 216972127067176960 (@Enclosure.Real.IsNear.mulLit_ft qz432 (Real.cos qz134) 177241 1048576 1 1048576 328887 524288 146484471 206920744960 58292260767 549755813888 3261625305159 27121515883397120 qz436 (@Enclosure.Real.IsNear.recentre' (Real.cos qz134) Bool.true 657774 1048576 146484471 206920744960 328887 524288 146484471 206920744960 (ep746 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz432 qz671 177241 1048576 1 1048576 816605 1048576 146484471 206920744960 144735886805 1099511627776 26124345356657 216972127067176960 qz436 (@Enclosure.Real.IsNear.neg qz135 Bool.false 816605 1048576 146484471 206920744960 (@Enclosure.Real.IsNear.recentre' qz135 Bool.false 816605 1048576 146484471 206920744960 816605 1048576 146484471 206920744960 (ep751 rfl rfl) rfl)) rfl)

noncomputable def ep753 := @ep739 4027045361640 0 1 39146008044714817930749 737963866784097831485440 ep733 ep735 (@Enclosure.Complex.IsNear.re_isNear qz125 Bool.true 58292260767 549755813888 3261625305159 27121515883397120 Bool.true 144735886805 1099511627776 26124345356657 216972127067176960 (ep740 ep752))

noncomputable def ep754 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz126 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1))))) Bool.false 2014641782441 4027045361640 0 1 Bool.false

noncomputable def ep755 := @Enclosure.Complex.IsNear.addLitP qz126 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) Bool.false 4785351621 9588203242 0 1 Bool.true 1211682500

noncomputable def ep756 := @ep755 4794101621 0 1 Bool.false 1 840 0 1 Bool.false 69239 210000 0 1 Bool.false 4029283564882 2014641782441 4027045361640 0 1 Bool.false 77485477136419 77485477136419 1006761340410000 0 1

noncomputable abbrev qz137 := (@HDiv.hDiv Complex Complex Complex qz396 qz420 (@HSub.hSub Complex Complex Complex qz388 qz273 (1 : Complex)))

noncomputable def ep757 := @Enclosure.Complex.IsNear.addLitP qz137 qz103 Bool.true 70000000 76705625936 0 1 Bool.true 19386920000 76705625936 0 1

noncomputable def ep758 := @Enclosure.Complex.IsNear.of_eq qz137 (Complex.mk (Enclosure.sfrac Bool.true 70000000 76705625936) (Enclosure.sfrac Bool.true 19386920000 76705625936)) Bool.true 70000000 76705625936 0 1 Bool.true 19386920000 76705625936 0 1

noncomputable def ep759 := @ep757 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 76565625936 4785351621 9588203242 0 1 Bool.true 19386920000 1211682500 4794101621 0 1 (ep758 (BSN.N_div_s_sub_one_mk qz12 138478 1000 35 qz13 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 70000000 76705625936) (Enclosure.sfrac Bool.true 19386920000 76705625936) Bool.true 70000000 76705625936 0 1 Bool.true 19386920000 76705625936 0 1 (Enclosure.Real.IsNear.const Bool.true 70000000 76705625936) (Enclosure.Real.IsNear.const Bool.true 19386920000 76705625936))) qz104 rfl

noncomputable abbrev qz138 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)))

noncomputable abbrev qz139 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz421 qz420 1))

noncomputable def ep760 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz139)) Bool.false 1 840 0 1

noncomputable def ep761 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz139) Bool.false 0 1 0 1 Bool.false

noncomputable def ep762 := @ep761 0 1 0 1 Bool.false 1 840 0 1 Bool.false 69239 210000 0 1 Bool.false 1 1 840 0 1 Bool.false 69239 69239 210000 0

noncomputable def ep763 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep764 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz139 Bool.false 1 840 0 1 Bool.false 69239 210000 0 1

noncomputable def ep765 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz139)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz139)) 1 840 0 1 0 1 0

noncomputable def ep766 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz139) 1 24 0 1 1 35 0 1 1

noncomputable def ep767 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz138)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz138)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep768 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz138)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep769 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz138) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz10) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 1 1 6 2 Bool.false BSN.bern_real_1 EMRow48.d10 rfl) qz409

noncomputable def ep770 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz5 Bool.false 1 2 0 1 Bool.false 138478 1000 0 1 (BSN.ascPochhammer_one_eval qz5)

noncomputable def ep771 := ep770 (@Enclosure.Complex.IsNear.of_eq qz5 (Complex.mk qz98 qz12) Bool.false 1 2 0 1 Bool.false 138478 1000 0 1 (BSN.s_crit_mk qz12 Bool.false 138478 1000 qz13) (@Enclosure.Complex.IsNear.mk qz98 qz12 Bool.false 1 2 0 1 Bool.false 138478 1000 0 1 qz402 qz18))

noncomputable def ep772 := @ep768 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz138) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep769) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 138478 1000 0 1 ep771)

noncomputable def ep773 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz138)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 138478 1000 0 1 0 1 0

noncomputable def ep774 := @ep773 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz138) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep769) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 138478 1000 0 1 ep771)

noncomputable def ep775 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz138)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz138)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) 69239 6000 0 1 0 1 0 1 69239

noncomputable def ep776 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz138)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 138478 1000 0 1 69239 6000 0

noncomputable def ep777 := @ep776 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz138) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep769) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 138478 1000 0 1 ep771)

noncomputable def ep778 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz138)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep779 := @ep778 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz138) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep769) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 138478 1000 0 1 ep771)

noncomputable def ep780 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 69239 6000 0 1 (@ep767 1 24 0 1 (ep772 rfl) (ep774 rfl) rfl rfl) (@ep775 69239 6000 0 1 (ep777 rfl) (ep779 rfl) rfl rfl)

noncomputable def ep781 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 69239 6000 0 1 ep780

noncomputable abbrev qz140 := (@Enclosure.Complex.IsNear.of_eq (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz421 qz420 1)) (Complex.mk (Enclosure.sfrac Bool.false 1 35) qz547) Bool.false 1 35 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 35 1 35 EMRow48.d11 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 35) qz547 Bool.false 1 35 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 35) qz549))

noncomputable def ep782 := @ep766 840 0 1 ep781 (@Enclosure.Complex.IsNear.re_isNear qz139 Bool.false 1 35 0 1 Bool.false 0 1 0 1 qz140)

noncomputable def ep783 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz139) 69239 6000 0 1 0 1 0 1 0

noncomputable def ep784 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 69239 6000 0 1 ep780

noncomputable def ep785 := @ep783 1 0 1 ep784 (@Enclosure.Complex.IsNear.im_isNear qz139 Bool.false 1 35 0 1 Bool.false 0 1 0 1 qz140)

noncomputable def ep786 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz139)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz139)) 0 1 0 1 69239 210000 0

noncomputable def ep787 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz139) 1 24 0 1 0 1 0 1 0

noncomputable def ep788 := @ep787 1 0 1 ep781 (@Enclosure.Complex.IsNear.im_isNear qz139 Bool.false 1 35 0 1 Bool.false 0 1 0 1 qz140)

noncomputable def ep789 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz139) 69239 6000 0 1 1 35 0 1 69239

noncomputable def ep790 := @ep789 210000 0 1 ep784 (@Enclosure.Complex.IsNear.re_isNear qz139 Bool.false 1 35 0 1 Bool.false 0 1 0 1 qz140)

noncomputable def ep791 := @ep762 1 (@ep763 0 1 0 1 (BSN.bern_sum_base qz5 35) qz119) (ep764 (@ep765 1 1 1 840 0 1 (ep782 rfl) (ep785 rfl) rfl rfl) (@ep786 1 69239 69239 210000 0 1 (ep788 rfl) (ep790 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep792 := ep756 (ep759 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep760 Bool.false 69239 210000 0 1 (BSN.bern_sum_succ qz5 35 0 1 1 rfl rfl) (ep791 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep793 := @Enclosure.Real.IsNear.mulLit_tf qz133 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz126 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))))) 144735886805 1099511627776 26124345356657 216972127067176960 77485477136419

noncomputable def ep794 := @ep793 1006761340410000 0 1 ep736 ep551 ep737 ep553 (@Enclosure.Complex.IsNear.im_isNear qz125 Bool.true 58292260767 549755813888 3261625305159 27121515883397120 Bool.true 144735886805 1099511627776 26124345356657 216972127067176960 (ep740 ep752))

noncomputable def ep795 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz126 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1))))) Bool.false 2014641782441 4027045361640 0 1 Bool.false

noncomputable def ep796 := nat_lit 1505601212963850926857791

noncomputable def ep797 := nat_lit 184490966696024457871360000

noncomputable def ep798 := nat_lit 84242864336821112782495207

noncomputable def ep799 := @Enclosure.Real.IsNear.addLit_tt (@HMul.hMul Real Real Real qz0 qz132 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz126 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz133 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz126 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1))))))) ep796 ep797 ep798

noncomputable def ep800 := nat_lit 9101631228239996598511206400000

noncomputable def ep801 := nat_lit 52631197694439720345059737

noncomputable def ep802 := nat_lit 873756597911039673457075814400

noncomputable def ep803 := nat_lit 12092474953194275757358272688628508559098823835648

noncomputable def ep804 := @Enclosure.Real.IsNear.mulLit_tf qz132 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz126 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))))) 58292260767 549755813888 3261625305159 27121515883397120 77485477136419

noncomputable def ep805 := @ep804 1006761340410000 0 1 ep796 ep797 ep798 ep800 (@Enclosure.Complex.IsNear.re_isNear qz125 Bool.true 58292260767 549755813888 3261625305159 27121515883397120 Bool.true 144735886805 1099511627776 26124345356657 216972127067176960 (ep740 ep752))

noncomputable def ep806 := @Enclosure.Real.IsNear.mulLit_tf qz133 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz126 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))))) 144735886805 1099511627776 26124345356657 216972127067176960 2014641782441

noncomputable def ep807 := @ep806 4027045361640 0 1 58318192995200802518201 885556640140917397782528 ep801 ep802 (@Enclosure.Complex.IsNear.im_isNear qz125 Bool.true 58292260767 549755813888 3261625305159 27121515883397120 Bool.true 144735886805 1099511627776 26124345356657 216972127067176960 (ep740 ep752))

noncomputable abbrev qz672 := (ep792 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep808 := @ep732 ep696 ep689 ep697 ep691 (@ep734 ep735 ep736 ep551 ep737 ep553 ep738 ep694 ep551 ep695 ep553 (ep753 (@ep754 77485477136419 1006761340410000 0 1 qz672) rfl) (ep794 (@ep795 77485477136419 1006761340410000 0 1 qz672) rfl) rfl rfl) (@ep799 ep800 58318192995200802518201 885556640140917397782528 ep801 ep802 ep803 ep696 ep689 ep697 ep691 (ep805 (@ep795 77485477136419 1006761340410000 0 1 qz672) rfl) (ep807 (@ep754 77485477136419 1006761340410000 0 1 qz672) rfl) rfl rfl)

noncomputable def ep809 := @ep700 ep690 ep691 (@ep701 216972127067176960 (BSN.head_sum_c_eq qz5 35) (ep702 (BSN.head_sum_c_succ qz5 34 35 rfl rfl) (ep731 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep808 rfl rfl rfl

noncomputable def ep810 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz5 1 35) Bool.false ep550 ep551 ep552 ep553 Bool.false ep688 ep689 ep690 ep691 (@ep692 ep553 Bool.false ep688 ep689 ep690 ep691 (BSN.zetaApproximant_eq_folded' qz5 1 35 rfl) (ep809 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep811 := @Enclosure.Real.IsNear.mulLit_tf (Real.sin (@HSub.hSub Real Real Real qz391 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz80 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz81 (@Nat.cast Complex Complex.instNatCast j))))) qz82)) (Complex.im (zetaApproximant qz5 1 35)) 9 262144 19008969

noncomputable def ep812 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz391 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz80 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz81 (@Nat.cast Complex Complex.instNatCast j))))) qz82)) Bool.true 36 1048576 19008969

noncomputable def ep813 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz391 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz80 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz81 (@Nat.cast Complex Complex.instNatCast j))))) qz82) qz392 Bool.false 151533101 1048576 95

noncomputable def ep814 := nat_lit 4642578150816871951322798183147333989882153610398974986509336037504478128800000

noncomputable def ep815 := nat_lit 13894210957344988242846951581808540433051075905607528144699123966765434186400000

noncomputable def ep816 := BSN.cos_dyadic_bound_f 3373183070 2147483648 3 2 1048576 395056 ep814 ep72 ep684 ep815 ep75 ep684 36 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3373183070) qz20 0 2 ep814 ep72 ep684 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3373183070) qz21 0 2 ep815 ep75 ep684 rfl rfl rfl rfl) rfl rfl

noncomputable def ep817 := @ep813 262144 Bool.true 36 1048576 1 197335 (@ep558 151533101 1048576 95 262144 ep682 rfl) (Enclosure.sfrac_false_div 151533101 1048576) (BSN.sin_reduce3 qz392 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 237366656525988677025792) qz25) 226375608064910080 72057594037927936 Bool.false 36 1048576 22 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q3 151533101 1048576 226375608064910080 72057594037927936 22 237366656525988677025792 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 36 1048576 237366656525988677025792 151115727451828646838272 3373183070 2147483648 395056 394670 (ep816 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep818 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz5 1 35) Bool.false ep550 ep551 ep552 ep553 Bool.false ep688 ep689 ep690 ep691 (@ep692 ep553 Bool.false ep688 ep689 ep690 ep691 (BSN.zetaApproximant_eq_folded' qz5 1 35 rfl) (ep809 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow48.d12 : Enclosure.Real.IsNear (hardyZApproximantEM 1 35 qz12) Bool.false ep534 ep535 ep536 ep537 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 35 qz12) ep538 Bool.false ep534 ep535 ep536 ep537 (@Eq.refl Real ep538) (@ep539 Bool.false ep534 ep535 ep536 ep537 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz391 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz80 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz81 (@Nat.cast Complex Complex.instNatCast j))))) qz82) (zetaApproximant qz5 1 35)) (@ep541 ep542 ep543 ep537 ep544 ep545 ep546 ep547 ep548 ep534 ep535 ep536 ep537 (@ep549 51730186240 ep550 ep551 ep552 ep553 ep540 ep542 ep543 ep537 (@ep554 51730186240 1048575 1048576 19008969 51730186240 (ep687 rfl rfl) rfl) ep810 rfl) (@ep811 51730186240 ep688 ep689 ep690 ep691 ep544 ep545 ep546 ep547 (@ep812 51730186240 9 262144 19008969 51730186240 (ep817 rfl rfl) rfl) ep818 rfl) rfl rfl))

noncomputable abbrev qz726 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 140505 1000)))

noncomputable abbrev qz673 := qz726

noncomputable abbrev qz437 := qz673

noncomputable abbrev qz141 := (BSN.headSumC qz437 9)

noncomputable abbrev qz142 := qz437

noncomputable abbrev qz674 := (@Neg.neg Complex Complex.instNeg qz726)

noncomputable abbrev qz438 := qz674

noncomputable abbrev qz143 := qz438

noncomputable abbrev qz675 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 8) qz143)

noncomputable def ep819 := @Enclosure.Complex.IsNear.of_eq qz141 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz142 8) qz675) Bool.false 390213106953 1099511627776 526517687401477 216972127067176960 Bool.false 72263011735 549755813888 262654910490661 108486063533588480

noncomputable def ep820 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 8) qz675 Bool.false 778945575889 1099511627776 471200139561629 216972127067176960 Bool.false 143042744743 1099511627776 470198402770419 216972127067176960 Bool.true

noncomputable abbrev qz676 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 7) qz143)

noncomputable def ep821 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 8) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz142 7) qz676) Bool.false 778945575889 1099511627776 471200139561629 216972127067176960 Bool.false 143042744743 1099511627776 470198402770419 216972127067176960

noncomputable def ep822 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 7) qz676 Bool.false 1192790518839 1099511627776 412156386804973 216972127067176960 Bool.false 52572875959 549755813888 205670919517369 108486063533588480 Bool.true

noncomputable abbrev qz677 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 6) qz143)

noncomputable def ep823 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 7) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz142 6) qz677) Bool.false 1192790518839 1099511627776 412156386804973 216972127067176960 Bool.false 52572875959 549755813888 205670919517369 108486063533588480

noncomputable def ep824 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 6) qz677 Bool.false 97949313951 137438953472 174165728634339 108486063533588480 Bool.false 36207580411 137438953472 43452560318651 27121515883397120 Bool.false

noncomputable abbrev qz678 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 5) qz143)

noncomputable def ep825 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 6) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz142 5) qz678) Bool.false 97949313951 137438953472 174165728634339 108486063533588480 Bool.false 36207580411 137438953472 43452560318651 27121515883397120

noncomputable def ep826 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 5) qz678 Bool.false 146394551775 549755813888 27850740608419 21697212706717696 Bool.false 259753248239 1099511627776 55598076690163 43394425413435392 Bool.false

noncomputable abbrev qz679 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 4) qz143)

noncomputable def ep827 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 5) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz142 4) qz679) Bool.false 146394551775 549755813888 27850740608419 21697212706717696 Bool.false 259753248239 1099511627776 55598076690163 43394425413435392

noncomputable def ep828 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 4) qz679 Bool.true 128481782307 549755813888 100232916036061 108486063533588480 Bool.false 261078645775 1099511627776 200155230531487 216972127067176960 Bool.false

noncomputable def ep829 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 4) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz142 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz143)) Bool.true 128481782307 549755813888 100232916036061 108486063533588480 Bool.false 261078645775 1099511627776 200155230531487 216972127067176960

noncomputable def ep830 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz143) Bool.false 322040451151 1099511627776 110281862675001 216972127067176960 Bool.false 832653965 1099511627776 110075163734581 216972127067176960 Bool.true

noncomputable def ep831 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 3) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz142 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz143)) Bool.false 322040451151 1099511627776 110281862675001 216972127067176960 Bool.false 832653965 1099511627776 110075163734581 216972127067176960

noncomputable def ep832 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz143) Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.true

noncomputable def ep833 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz10) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz142)

noncomputable abbrev qz727 := (Enclosure.sfrac Bool.false 140505 1000)

noncomputable abbrev qz680 := qz727

noncomputable abbrev qz439 := qz680

noncomputable abbrev qz144 := (@HMul.hMul Real Real Real qz269 qz439 (Real.log qz280))

noncomputable abbrev qz145 := qz439

noncomputable abbrev qz440 := (@Eq.refl Real qz680)

noncomputable abbrev qz146 := qz440

noncomputable def ep834 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz9 qz143) (Complex.mk (@HMul.hMul Real Real Real qz0 qz282 (Real.cos qz144)) (@HMul.hMul Real Real Real qz0 qz282 (@Neg.neg Real Real.instNeg (Real.sin qz144)))) Bool.true 777471176625 1099511627776 110281862675001 216972127067176960 Bool.false 832653965 1099511627776 110075163734581 216972127067176960 (BSN.cpow_neg_s_mk qz145 140505 1000 2 qz146 rfl)

noncomputable def ep835 := BSN.cos_dyadic_bound_f 2301115 2147483648 1 0 1048576 395056 0 1 1 0 1 1 1048575 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 2301115) qz20 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 2301115) qz21 0 0 rfl) rfl rfl

noncomputable abbrev qz147 := (Enclosure.Real.IsNear.const Bool.false 140505 1000)

noncomputable abbrev qz441 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 51060641) qz17)

noncomputable def ep836 := @Enclosure.Real.IsNear.cos_image qz144 qz441 Bool.false 51060641 524288 747 1048576 Bool.true 1048575 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz144 Bool.false 638258013 6553600 28101 39467000 51060641 524288 747 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz145 (Real.log qz280) 140505 1000 0 1 363408 524288 1 197335 638258013 6553600 28101 39467000 qz147 qz286 rfl) rfl) (Enclosure.sfrac_false_div 51060641 524288) (BSN.cos_reduce2 qz441 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 80963318351734505472) qz19) 226375608064910080 72057594037927936 Bool.false 1048575 1048576 15 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q2 51060641 524288 226375608064910080 72057594037927936 15 80963318351734505472 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1048575 1048576 80963318351734505472 75557863725914323419136 2301115 2147483648 395056 394670 (ep835 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep837 := BSN.sin_dyadic_bound_f 2301115 2147483648 1 0 1048576 395056 0 1 1 0 1 1 1123 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 2301115) qz15 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 2301115) qz16 0 0 rfl) rfl rfl

noncomputable def ep838 := @Enclosure.Real.IsNear.sin_image qz144 qz441 Bool.false 51060641 524288 747 1048576 Bool.true 1123 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz144 Bool.false 638258013 6553600 28101 39467000 51060641 524288 747 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz145 (Real.log qz280) 140505 1000 0 1 363408 524288 1 197335 638258013 6553600 28101 39467000 qz147 qz286 rfl) rfl) (Enclosure.sfrac_false_div 51060641 524288) (BSN.sin_reduce2 qz441 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 80963318351734505472) qz19) 226375608064910080 72057594037927936 Bool.false 1123 1048576 15 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q2 51060641 524288 226375608064910080 72057594037927936 15 80963318351734505472 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1123 1048576 80963318351734505472 75557863725914323419136 2301115 2147483648 395056 394670 (ep837 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep839 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz282 (Real.cos qz144)) (@HMul.hMul Real Real Real qz0 qz282 (@Neg.neg Real Real.instNeg (Real.sin qz144))) Bool.true 777471176625 1099511627776 110281862675001 216972127067176960 Bool.false 832653965 1099511627776 110075163734581 216972127067176960 (@Enclosure.Real.IsNear.mulLit_ft qz282 (Real.cos qz144) 741455 1048576 1 1048576 1048575 1048576 148457821 206920744960 777471176625 1099511627776 110281862675001 216972127067176960 qz287 (@Enclosure.Real.IsNear.recentre' (Real.cos qz144) Bool.true 1048575 1048576 148457821 206920744960 1048575 1048576 148457821 206920744960 (ep836 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz282 (@Neg.neg Real Real.instNeg (Real.sin qz144)) 741455 1048576 1 1048576 1123 1048576 148457821 206920744960 832653965 1099511627776 110075163734581 216972127067176960 qz287 (@Enclosure.Real.IsNear.neg (Real.sin qz144) Bool.true 1123 1048576 148457821 206920744960 (@Enclosure.Real.IsNear.recentre' (Real.sin qz144) Bool.true 1123 1048576 148457821 206920744960 1123 1048576 148457821 206920744960 (ep838 rfl rfl) rfl)) rfl)

noncomputable def ep840 := @ep832 777471176625 1099511627776 110281862675001 216972127067176960 Bool.false 832653965 1099511627776 110075163734581 216972127067176960 Bool.false 322040451151 322040451151 1099511627776 110281862675001 216972127067176960 Bool.false 832653965 832653965 1099511627776 110075163734581 216972127067176960 (ep833 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz10 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz22)) (ep834 ep839) rfl rfl

noncomputable abbrev qz148 := (@HMul.hMul Real Real Real qz269 qz439 qz550)

noncomputable def ep841 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz8 qz143) (Complex.mk (@HMul.hMul Real Real Real qz0 qz288 (Real.cos qz148)) (@HMul.hMul Real Real Real qz0 qz288 (@Neg.neg Real Real.instNeg (Real.sin qz148)))) Bool.true 579004015765 1099511627776 90183969397121 216972127067176960 Bool.false 130122995905 549755813888 45040033398453 108486063533588480 (BSN.cpow_neg_s_mk qz145 140505 1000 3 qz146 rfl)

noncomputable def ep842 := nat_lit 677134387819770095738473800001916481

noncomputable def ep843 := BSN.cos_dyadic_bound_f 907128303 2147483648 2 1 1048576 395056 ep842 ep62 ep842 ep842 ep63 ep842 956407 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 907128303) qz20 0 1 ep842 ep62 ep842 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 907128303) qz21 0 1 ep842 ep63 ep842 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz442 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 40464667) qz31)

noncomputable def ep844 := @Enclosure.Real.IsNear.cos_image qz148 qz442 Bool.false 40464667 262144 187 262144 Bool.true 956407 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz148 Bool.false 16185866889 104857600 28101 39467000 40464667 262144 187 262144 (@Enclosure.Real.IsNear.mulLit_ff qz145 qz550 140505 1000 0 1 575989 524288 1 197335 16185866889 104857600 28101 39467000 qz147 qz292 rfl) rfl) (Enclosure.sfrac_false_div 40464667 262144) (BSN.cos_reduce2 qz442 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 15958369876235375345664) qz321) 226375608064910080 72057594037927936 Bool.false 956407 1048576 24 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q2 40464667 262144 226375608064910080 72057594037927936 24 15958369876235375345664 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 956407 1048576 15958369876235375345664 37778931862957161709568 907128303 2147483648 395056 394670 (ep843 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep845 := BSN.sin_dyadic_bound_f 907128303 2147483648 2 1 1048576 395056 ep842 ep58 ep842 ep842 ep59 ep842 429878 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 907128303) qz15 0 1 ep842 ep58 ep842 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 907128303) qz16 0 1 ep842 ep59 ep842 rfl rfl rfl rfl) rfl rfl

noncomputable def ep846 := @Enclosure.Real.IsNear.sin_image qz148 qz442 Bool.false 40464667 262144 187 262144 Bool.true 429878 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz148 Bool.false 16185866889 104857600 28101 39467000 40464667 262144 187 262144 (@Enclosure.Real.IsNear.mulLit_ff qz145 qz550 140505 1000 0 1 575989 524288 1 197335 16185866889 104857600 28101 39467000 qz147 qz292 rfl) rfl) (Enclosure.sfrac_false_div 40464667 262144) (BSN.sin_reduce2 qz442 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 15958369876235375345664) qz321) 226375608064910080 72057594037927936 Bool.false 429878 1048576 24 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q2 40464667 262144 226375608064910080 72057594037927936 24 15958369876235375345664 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 429878 1048576 15958369876235375345664 37778931862957161709568 907128303 2147483648 395056 394670 (ep845 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep847 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz288 (Real.cos qz148)) (@HMul.hMul Real Real Real qz0 qz288 (@Neg.neg Real Real.instNeg (Real.sin qz148))) Bool.true 579004015765 1099511627776 90183969397121 216972127067176960 Bool.false 130122995905 549755813888 45040033398453 108486063533588480 (@Enclosure.Real.IsNear.mulLit_ft qz288 (Real.cos qz148) 605395 1048576 1 1048576 956407 1048576 37163789 51730186240 579004015765 1099511627776 90183969397121 216972127067176960 qz293 (@Enclosure.Real.IsNear.recentre' (Real.cos qz148) Bool.true 956407 1048576 37163789 51730186240 956407 1048576 37163789 51730186240 (ep844 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz288 (@Neg.neg Real Real.instNeg (Real.sin qz148)) 605395 1048576 1 1048576 214939 524288 37163789 51730186240 130122995905 549755813888 45040033398453 108486063533588480 qz293 (@Enclosure.Real.IsNear.neg (Real.sin qz148) Bool.true 214939 524288 37163789 51730186240 (@Enclosure.Real.IsNear.recentre' (Real.sin qz148) Bool.true 429878 1048576 37163789 51730186240 214939 524288 37163789 51730186240 (ep846 rfl rfl) rfl)) rfl)

noncomputable def ep848 := @ep830 579004015765 1099511627776 90183969397121 216972127067176960 Bool.false 130122995905 549755813888 45040033398453 108486063533588480 Bool.true 282534427207862493118464 128481782307 549755813888 100232916036061 108486063533588480 Bool.false 143529503396811977523200 261078645775 1099511627776 200155230531487 216972127067176960 (ep831 (BSN.head_sum_c_succ qz142 2 3 rfl rfl) (ep840 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep841 ep847) rfl rfl

noncomputable abbrev qz149 := (@HMul.hMul Real Real Real qz269 qz439 qz551)

noncomputable def ep849 := @Enclosure.Complex.IsNear.of_eq qz679 (Complex.mk (@HMul.hMul Real Real Real qz0 qz294 (Real.cos qz149)) (@HMul.hMul Real Real Real qz0 qz294 (@Neg.neg Real Real.instNeg (Real.sin qz149)))) Bool.false 137438167041 274877906944 19510393503017 54243031766794240 Bool.true 41418673 34359738368 2432348528729 6780378970849280 (BSN.cpow_neg_s_mk qz145 140505 1000 4 qz146 rfl)

noncomputable def ep850 := BSN.cos_dyadic_bound_f 5177719 2147483648 1 0 1048576 395056 0 1 1 0 1 1 1048572 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 5177719) qz20 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 5177719) qz21 0 0 rfl) rfl rfl

noncomputable abbrev qz443 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 204242845) qz24)

noncomputable def ep851 := @Enclosure.Real.IsNear.cos_image qz149 qz443 Bool.false 204242845 1048576 747 1048576 Bool.false 1048572 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz149 Bool.false 20424284517 104857600 28101 39467000 204242845 1048576 747 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz145 qz551 140505 1000 0 1 726817 524288 1 197335 20424284517 104857600 28101 39467000 qz147 qz298 rfl) rfl) (Enclosure.sfrac_false_div 204242845 1048576) (BSN.cos_reduce0 qz443 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 364349641256253521920) qz25) 226375608064910080 72057594037927936 Bool.false 1048572 1048576 31 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q0 204242845 1048576 226375608064910080 72057594037927936 31 364349641256253521920 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1048572 1048576 364349641256253521920 151115727451828646838272 5177719 2147483648 395056 394670 (ep850 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep852 := BSN.sin_dyadic_bound_f 5177719 2147483648 1 0 1048576 395056 0 1 1 0 1 1 2528 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 5177719) qz15 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 5177719) qz16 0 0 rfl) rfl rfl

noncomputable def ep853 := @Enclosure.Real.IsNear.sin_image qz149 qz443 Bool.false 204242845 1048576 747 1048576 Bool.false 2528 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz149 Bool.false 20424284517 104857600 28101 39467000 204242845 1048576 747 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz145 qz551 140505 1000 0 1 726817 524288 1 197335 20424284517 104857600 28101 39467000 qz147 qz298 rfl) rfl) (Enclosure.sfrac_false_div 204242845 1048576) (BSN.sin_reduce0 qz443 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 364349641256253521920) qz25) 226375608064910080 72057594037927936 Bool.false 2528 1048576 31 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q0 204242845 1048576 226375608064910080 72057594037927936 31 364349641256253521920 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 2528 1048576 364349641256253521920 151115727451828646838272 5177719 2147483648 395056 394670 (ep852 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep854 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz294 (Real.cos qz149)) (@HMul.hMul Real Real Real qz0 qz294 (@Neg.neg Real Real.instNeg (Real.sin qz149))) Bool.false 137438167041 274877906944 19510393503017 54243031766794240 Bool.true 41418673 34359738368 2432348528729 6780378970849280 (@Enclosure.Real.IsNear.mulLit_ff qz294 (Real.cos qz149) 524287 1048576 1 1048576 262143 262144 148457821 206920744960 137438167041 274877906944 19510393503017 54243031766794240 qz299 (@Enclosure.Real.IsNear.recentre' (Real.cos qz149) Bool.false 1048572 1048576 148457821 206920744960 262143 262144 148457821 206920744960 (ep851 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz294 (@Neg.neg Real Real.instNeg (Real.sin qz149)) 524287 1048576 1 1048576 79 32768 148457821 206920744960 41418673 34359738368 2432348528729 6780378970849280 qz299 (@Enclosure.Real.IsNear.neg (Real.sin qz149) Bool.false 79 32768 148457821 206920744960 (@Enclosure.Real.IsNear.recentre' (Real.sin qz149) Bool.false 2528 1048576 148457821 206920744960 79 32768 148457821 206920744960 (ep853 rfl rfl) rfl)) rfl)

noncomputable def ep855 := @ep828 137438167041 274877906944 19510393503017 54243031766794240 Bool.true 41418673 34359738368 2432348528729 6780378970849280 Bool.false 40240627979917040025600 146394551775 549755813888 27850740608419 21697212706717696 Bool.false 8925053649730196733952 259753248239 1099511627776 55598076690163 43394425413435392 (ep829 (BSN.head_sum_c_succ qz142 3 4 rfl rfl) (ep848 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep849 ep854) rfl rfl

noncomputable abbrev qz150 := (@HMul.hMul Real Real Real qz269 qz439 qz552)

noncomputable def ep856 := @Enclosure.Complex.IsNear.of_eq qz678 (Complex.mk (@HMul.hMul Real Real Real qz0 qz300 (Real.cos qz150)) (@HMul.hMul Real Real Real qz0 qz300 (@Neg.neg Real Real.instNeg (Real.sin qz150)))) Bool.false 245402704029 549755813888 8728006398061 27121515883397120 Bool.false 29907395049 1099511627776 69630099098393 216972127067176960 (BSN.cpow_neg_s_mk qz145 140505 1000 5 qz146 rfl)

noncomputable def ep857 := nat_lit 7121966849833608328090002514318347255273988292278607329757487837488901349564545

noncomputable def ep858 := nat_lit 12220969443139861517700977113707149712840908528037961776475926972246798753921

noncomputable def ep859 := nat_lit 18632983989513414416826109765030621711896798342160481544583888073563484908019841

noncomputable def ep860 := BSN.sin_dyadic_bound_f 3242561391 2147483648 3 2 1048576 395056 ep857 ep79 ep858 ep859 ep81 ep858 1046634 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3242561391) qz15 0 2 ep857 ep79 ep858 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3242561391) qz16 0 2 ep859 ep81 ep858 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz444 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 118559243) qz17)

noncomputable def ep861 := @Enclosure.Real.IsNear.cos_image qz150 qz444 Bool.false 118559243 524288 747 1048576 Bool.false 1046634 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz150 Bool.false 740995269 3276800 28101 39467000 118559243 524288 747 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz145 qz552 140505 1000 0 1 843808 524288 1 197335 740995269 3276800 28101 39467000 qz147 qz304 rfl) rfl) (Enclosure.sfrac_false_div 118559243 524288) (BSN.cos_reduce3 qz444 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 114087486513711390130176) qz19) 226375608064910080 72057594037927936 Bool.false 1046634 1048576 35 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q3 118559243 524288 226375608064910080 72057594037927936 35 114087486513711390130176 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1046634 1048576 114087486513711390130176 75557863725914323419136 3242561391 2147483648 395056 394670 (ep860 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep862 := nat_lit 3962079791882289009613424053338507208357922788389465388432593655037054882537601

noncomputable def ep863 := nat_lit 11861797436760587305804870205788107325648086548112320241744829111166671050104961

noncomputable def ep864 := BSN.cos_dyadic_bound_f 3242561391 2147483648 3 2 1048576 395056 ep862 ep72 ep858 ep863 ep75 ep858 63777 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3242561391) qz20 0 2 ep862 ep72 ep858 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3242561391) qz21 0 2 ep863 ep75 ep858 rfl rfl rfl rfl) rfl rfl

noncomputable def ep865 := @Enclosure.Real.IsNear.sin_image qz150 qz444 Bool.false 118559243 524288 747 1048576 Bool.true 63777 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz150 Bool.false 740995269 3276800 28101 39467000 118559243 524288 747 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz145 qz552 140505 1000 0 1 843808 524288 1 197335 740995269 3276800 28101 39467000 qz147 qz304 rfl) rfl) (Enclosure.sfrac_false_div 118559243 524288) (BSN.sin_reduce3 qz444 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 114087486513711390130176) qz19) 226375608064910080 72057594037927936 Bool.false 63777 1048576 35 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q3 118559243 524288 226375608064910080 72057594037927936 35 114087486513711390130176 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 63777 1048576 114087486513711390130176 75557863725914323419136 3242561391 2147483648 395056 394670 (ep864 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep866 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz300 (Real.cos qz150)) (@HMul.hMul Real Real Real qz0 qz300 (@Neg.neg Real Real.instNeg (Real.sin qz150))) Bool.false 245402704029 549755813888 8728006398061 27121515883397120 Bool.false 29907395049 1099511627776 69630099098393 216972127067176960 (@Enclosure.Real.IsNear.mulLit_ff qz300 (Real.cos qz150) 468937 1048576 1 1048576 523317 524288 148457821 206920744960 245402704029 549755813888 8728006398061 27121515883397120 qz306 (@Enclosure.Real.IsNear.recentre' (Real.cos qz150) Bool.false 1046634 1048576 148457821 206920744960 523317 524288 148457821 206920744960 (ep861 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz300 (@Neg.neg Real Real.instNeg (Real.sin qz150)) 468937 1048576 1 1048576 63777 1048576 148457821 206920744960 29907395049 1099511627776 69630099098393 216972127067176960 qz306 (@Enclosure.Real.IsNear.neg (Real.sin qz150) Bool.true 63777 1048576 148457821 206920744960 (@Enclosure.Real.IsNear.recentre' (Real.sin qz150) Bool.true 63777 1048576 148457821 206920744960 63777 1048576 148457821 206920744960 (ep865 rfl rfl) rfl)) rfl)

noncomputable def ep867 := @ep826 245402704029 549755813888 8728006398061 27121515883397120 Bool.false 29907395049 1099511627776 69630099098393 216972127067176960 Bool.false 215392819243612951805952 97949313951 137438953472 174165728634339 108486063533588480 Bool.false 318485245404232168767488 36207580411 137438953472 43452560318651 27121515883397120 (ep827 (BSN.head_sum_c_succ qz142 4 5 rfl rfl) (ep855 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep856 ep866) rfl rfl

noncomputable abbrev qz151 := (@HMul.hMul Real Real Real qz269 qz439 qz554)

noncomputable def ep868 := @Enclosure.Complex.IsNear.of_eq qz677 (Complex.mk (@HMul.hMul Real Real Real qz0 qz307 (Real.cos qz151)) (@HMul.hMul Real Real Real qz0 qz307 (@Neg.neg Real Real.instNeg (Real.sin qz151)))) Bool.false 409196007231 1099511627776 12764985907259 43394425413435392 Bool.true 92257445685 549755813888 6372135648553 21697212706717696 (BSN.cpow_neg_s_mk qz145 140505 1000 6 qz146 rfl)

noncomputable def ep869 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz554 140505 1000 0 1 4034681531866359 2251799813685248 100000000039467 19733500000000000000 113378585726976554259 450359962737049600 2810100001109062167 3946700000000000000000 qz147 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 100000000039467 19733500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz555) Bool.false 33845361775666394038272 18889465931478580854784 1000000000394670 197335000000000000000 4034681531866359 2251799813685248 100000000039467 19733500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 212580 524288 24973259072661432 36028797018963968 197335 1000000000000000 rfl rfl rfl rfl (ep118 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep870 := nat_lit 684894372601442603443602826126117041

noncomputable def ep871 := BSN.cos_dyadic_bound_f 909716139 2147483648 2 1 1048576 395056 ep870 ep62 ep870 ep870 ep63 ep870 955889 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 909716139) qz20 0 1 ep870 ep62 ep870 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 909716139) qz21 0 1 ep870 ep63 ep870 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz445 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 131990045) qz17)

noncomputable def ep872 := @Enclosure.Real.IsNear.cos_image qz151 qz445 Bool.false 131990045 524288 187 262144 Bool.false 955889 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz151 Bool.false 113378585726976554259 450359962737049600 2810100001109062167 3946700000000000000000 131990045 524288 187 262144 (ep869 rfl) rfl) (Enclosure.sfrac_false_div 131990045 524288) (BSN.cos_reduce0 qz445 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 32007791133987795107840) qz19) 226375608064910080 72057594037927936 Bool.false 955889 1048576 40 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q0 131990045 524288 226375608064910080 72057594037927936 40 32007791133987795107840 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 955889 1048576 32007791133987795107840 75557863725914323419136 909716139 2147483648 395056 394670 (ep871 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep873 := BSN.sin_dyadic_bound_f 909716139 2147483648 2 1 1048576 395056 ep870 ep58 ep870 ep870 ep59 ep870 431030 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 909716139) qz15 0 1 ep870 ep58 ep870 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 909716139) qz16 0 1 ep870 ep59 ep870 rfl rfl rfl rfl) rfl rfl

noncomputable def ep874 := @Enclosure.Real.IsNear.sin_image qz151 qz445 Bool.false 131990045 524288 187 262144 Bool.false 431030 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz151 Bool.false 113378585726976554259 450359962737049600 2810100001109062167 3946700000000000000000 131990045 524288 187 262144 (ep869 rfl) rfl) (Enclosure.sfrac_false_div 131990045 524288) (BSN.sin_reduce0 qz445 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 32007791133987795107840) qz19) 226375608064910080 72057594037927936 Bool.false 431030 1048576 40 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q0 131990045 524288 226375608064910080 72057594037927936 40 32007791133987795107840 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 431030 1048576 32007791133987795107840 75557863725914323419136 909716139 2147483648 395056 394670 (ep873 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep875 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz307 (Real.cos qz151)) (@HMul.hMul Real Real Real qz0 qz307 (@Neg.neg Real Real.instNeg (Real.sin qz151))) Bool.false 409196007231 1099511627776 12764985907259 43394425413435392 Bool.true 92257445685 549755813888 6372135648553 21697212706717696 (@Enclosure.Real.IsNear.mulLit_ff qz307 (Real.cos qz151) 428079 1048576 1 1048576 955889 1048576 37163789 51730186240 409196007231 1099511627776 12764985907259 43394425413435392 qz311 (@Enclosure.Real.IsNear.recentre' (Real.cos qz151) Bool.false 955889 1048576 37163789 51730186240 955889 1048576 37163789 51730186240 (ep872 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz307 (@Neg.neg Real Real.instNeg (Real.sin qz151)) 428079 1048576 1 1048576 215515 524288 37163789 51730186240 92257445685 549755813888 6372135648553 21697212706717696 qz311 (@Enclosure.Real.IsNear.neg (Real.sin qz151) Bool.false 215515 524288 37163789 51730186240 (@Enclosure.Real.IsNear.recentre' (Real.sin qz151) Bool.false 431030 1048576 37163789 51730186240 215515 524288 37163789 51730186240 (ep874 rfl rfl) rfl)) rfl)

noncomputable def ep876 := @ep824 409196007231 1099511627776 12764985907259 43394425413435392 Bool.true 92257445685 549755813888 6372135648553 21697212706717696 Bool.false 163935880620556060459008 1192790518839 1099511627776 412156386804973 216972127067176960 Bool.false 7225561052818228379648 52572875959 549755813888 205670919517369 108486063533588480 (ep825 (BSN.head_sum_c_succ qz142 5 6 rfl rfl) (ep867 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep868 ep875) rfl rfl

noncomputable abbrev qz152 := (@HMul.hMul Real Real Real qz269 qz439 qz556)

noncomputable def ep877 := @Enclosure.Complex.IsNear.of_eq qz676 (Complex.mk (@HMul.hMul Real Real Real qz0 qz312 (Real.cos qz152)) (@HMul.hMul Real Real Real qz0 qz312 (@Neg.neg Real Real.instNeg (Real.sin qz152)))) Bool.true 206922471475 549755813888 3690234547291 13560757941698560 Bool.false 37896992825 1099511627776 58856563735681 216972127067176960 (BSN.cpow_neg_s_mk qz145 140505 1000 7 qz146 rfl)

noncomputable def ep878 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz556 140505 1000 0 1 4381796493761783 2251799813685248 100000000039467 19733500000000000000 123132863271199864083 450359962737049600 2810100001109062167 3946700000000000000000 qz147 (BSN.isNear_log_sfrac 7 1 4381796493761783 2251799813685248 100000000039467 19733500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz557) Bool.false 36757173121942042968064 18889465931478580854784 1000000000394670 197335000000000000000 4381796493761783 2251799813685248 100000000039467 19733500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 293399 524288 24973259072661432 36028797018963968 197335 1000000000000000 rfl rfl rfl rfl (ep133 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep879 := nat_lit 1478974426122518620902701355332241

noncomputable def ep880 := BSN.cos_dyadic_bound_f 196105677 2147483648 2 1 1048576 395056 ep879 ep62 ep879 ep879 ep63 ep879 1044206 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 196105677) qz20 0 1 ep879 ep62 ep879 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 196105677) qz21 0 1 ep879 ep63 ep879 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz446 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 143345519) qz17)

noncomputable def ep881 := @Enclosure.Real.IsNear.cos_image qz152 qz446 Bool.false 143345519 524288 747 1048576 Bool.true 1044206 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz152 Bool.false 123132863271199864083 450359962737049600 2810100001109062167 3946700000000000000000 143345519 524288 747 1048576 (ep878 rfl) rfl) (Enclosure.sfrac_false_div 143345519 524288) (BSN.cos_reduce2 qz446 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6899855118581113028608) qz19) 226375608064910080 72057594037927936 Bool.false 1044206 1048576 43 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q2 143345519 524288 226375608064910080 72057594037927936 43 6899855118581113028608 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1044206 1048576 6899855118581113028608 75557863725914323419136 196105677 2147483648 395056 394670 (ep880 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep882 := BSN.sin_dyadic_bound_f 196105677 2147483648 1 0 1048576 395056 0 1 1 0 1 1 95621 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 196105677) qz15 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 196105677) qz16 0 0 rfl) rfl rfl

noncomputable def ep883 := @Enclosure.Real.IsNear.sin_image qz152 qz446 Bool.false 143345519 524288 747 1048576 Bool.true 95621 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz152 Bool.false 123132863271199864083 450359962737049600 2810100001109062167 3946700000000000000000 143345519 524288 747 1048576 (ep878 rfl) rfl) (Enclosure.sfrac_false_div 143345519 524288) (BSN.sin_reduce2 qz446 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6899855118581113028608) qz19) 226375608064910080 72057594037927936 Bool.false 95621 1048576 43 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q2 143345519 524288 226375608064910080 72057594037927936 43 6899855118581113028608 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 95621 1048576 6899855118581113028608 75557863725914323419136 196105677 2147483648 395056 394670 (ep882 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep884 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz312 (Real.cos qz152)) (@HMul.hMul Real Real Real qz0 qz312 (@Neg.neg Real Real.instNeg (Real.sin qz152))) Bool.true 206922471475 549755813888 3690234547291 13560757941698560 Bool.false 37896992825 1099511627776 58856563735681 216972127067176960 (@Enclosure.Real.IsNear.mulLit_ft qz312 (Real.cos qz152) 396325 1048576 1 1048576 522103 524288 148457821 206920744960 206922471475 549755813888 3690234547291 13560757941698560 qz316 (@Enclosure.Real.IsNear.recentre' (Real.cos qz152) Bool.true 1044206 1048576 148457821 206920744960 522103 524288 148457821 206920744960 (ep881 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz312 (@Neg.neg Real Real.instNeg (Real.sin qz152)) 396325 1048576 1 1048576 95621 1048576 148457821 206920744960 37896992825 1099511627776 58856563735681 216972127067176960 qz316 (@Enclosure.Real.IsNear.neg (Real.sin qz152) Bool.true 95621 1048576 148457821 206920744960 (@Enclosure.Real.IsNear.recentre' (Real.sin qz152) Bool.true 95621 1048576 148457821 206920744960 95621 1048576 148457821 206920744960 (ep883 rfl rfl) rfl)) rfl)

noncomputable def ep885 := @ep822 206922471475 549755813888 3690234547291 13560757941698560 Bool.false 37896992825 1099511627776 58856563735681 216972127067176960 Bool.false 428229859047314064146432 778945575889 1099511627776 471200139561629 216972127067176960 Bool.false 78638580556961398390784 143042744743 1099511627776 470198402770419 216972127067176960 (ep823 (BSN.head_sum_c_succ qz142 6 7 rfl rfl) (ep876 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep877 ep884) rfl rfl

noncomputable abbrev qz153 := (@HMul.hMul Real Real Real qz269 qz439 qz558)

noncomputable def ep886 := @Enclosure.Complex.IsNear.of_eq qz675 (Complex.mk (@HMul.hMul Real Real Real qz0 qz317 (Real.cos qz153)) (@HMul.hMul Real Real Real qz0 qz317 (@Neg.neg Real Real.instNeg (Real.sin qz153)))) Bool.true 48591558617 137438953472 6914693479981 27121515883397120 Bool.false 1483278727 1099511627776 55111418210903 216972127067176960 (BSN.cpow_neg_s_mk qz145 140505 1000 8 qz146 rfl)

noncomputable def ep887 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz558 140505 1000 0 1 9364972152248037 4503599627370496 200000000118401 39467000000000000000 263165082450322087737 900719925474099200 5620200003327186501 7893400000000000000000 qz147 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 200000000118401 39467000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz559) Bool.false 39279540158062550581248 18889465931478580854784 1000000000592005 197335000000000000000 9364972152248037 4503599627370496 200000000118401 39467000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 524288 24973259072661432 36028797018963968 197335 1000000000000000 rfl rfl rfl rfl (ep148 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep888 := BSN.cos_dyadic_bound_f 8195635 2147483648 1 0 1048576 395056 0 1 1 0 1 1 1048568 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 8195635) qz20 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 8195635) qz21 0 0 rfl) rfl rfl

noncomputable abbrev qz447 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 306364477) qz24)

noncomputable def ep889 := @Enclosure.Real.IsNear.cos_image qz153 qz447 Bool.false 306364477 1048576 187 262144 Bool.true 1048568 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz153 Bool.false 263165082450322087737 900719925474099200 5620200003327186501 7893400000000000000000 306364477 1048576 187 262144 (ep887 rfl) rfl) (Enclosure.sfrac_false_div 306364477 1048576) (BSN.cos_reduce2 qz447 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 576716593786272088064) qz25) 226375608064910080 72057594037927936 Bool.false 1048568 1048576 46 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q2 306364477 1048576 226375608064910080 72057594037927936 46 576716593786272088064 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1048568 1048576 576716593786272088064 151115727451828646838272 8195635 2147483648 395056 394670 (ep888 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep890 := BSN.sin_dyadic_bound_f 8195635 2147483648 1 0 1048576 395056 0 1 1 0 1 1 4001 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 8195635) qz15 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 8195635) qz16 0 0 rfl) rfl rfl

noncomputable def ep891 := @Enclosure.Real.IsNear.sin_image qz153 qz447 Bool.false 306364477 1048576 187 262144 Bool.true 4001 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz153 Bool.false 263165082450322087737 900719925474099200 5620200003327186501 7893400000000000000000 306364477 1048576 187 262144 (ep887 rfl) rfl) (Enclosure.sfrac_false_div 306364477 1048576) (BSN.sin_reduce2 qz447 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 576716593786272088064) qz25) 226375608064910080 72057594037927936 Bool.false 4001 1048576 46 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q2 306364477 1048576 226375608064910080 72057594037927936 46 576716593786272088064 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 4001 1048576 576716593786272088064 151115727451828646838272 8195635 2147483648 395056 394670 (ep890 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep892 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz317 (Real.cos qz153)) (@HMul.hMul Real Real Real qz0 qz317 (@Neg.neg Real Real.instNeg (Real.sin qz153))) Bool.true 48591558617 137438953472 6914693479981 27121515883397120 Bool.false 1483278727 1099511627776 55111418210903 216972127067176960 (@Enclosure.Real.IsNear.mulLit_ft qz317 (Real.cos qz153) 370727 1048576 1 1048576 131071 131072 37163789 51730186240 48591558617 137438953472 6914693479981 27121515883397120 qz322 (@Enclosure.Real.IsNear.recentre' (Real.cos qz153) Bool.true 1048568 1048576 37163789 51730186240 131071 131072 37163789 51730186240 (ep889 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz317 (@Neg.neg Real Real.instNeg (Real.sin qz153)) 370727 1048576 1 1048576 4001 1048576 37163789 51730186240 1483278727 1099511627776 55111418210903 216972127067176960 qz322 (@Enclosure.Real.IsNear.neg (Real.sin qz153) Bool.true 4001 1048576 37163789 51730186240 (@Enclosure.Real.IsNear.recentre' (Real.sin qz153) Bool.true 4001 1048576 37163789 51730186240 4001 1048576 37163789 51730186240 (ep891 rfl rfl) rfl)) rfl)

noncomputable def ep893 := @ep820 48591558617 137438953472 6914693479981 27121515883397120 Bool.false 1483278727 1099511627776 55111418210903 216972127067176960 Bool.false 53630481050677926690816 390213106953 1099511627776 526517687401477 216972127067176960 Bool.false 158908043321492079902720 72263011735 549755813888 262654910490661 108486063533588480 (ep821 (BSN.head_sum_c_succ qz142 7 8 rfl rfl) (ep885 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep886 ep892) rfl rfl

theorem EMRow48.d13 : Enclosure.Complex.IsNear qz141 Bool.false 390213106953 1099511627776 526517687401477 216972127067176960 Bool.false 72263011735 549755813888 262654910490661 108486063533588480 := ep819 (BSN.head_sum_c_succ qz142 8 9 rfl rfl) (ep893 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz154 := (BSN.headSumC qz437 17)

noncomputable abbrev qz681 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 16) qz143)

noncomputable def ep894 := @Enclosure.Complex.IsNear.of_eq qz154 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz142 16) qz681) Bool.true 130506235681 1099511627776 884997260468203 216972127067176960 Bool.false 44267444217 1099511627776 883022521624473 216972127067176960

noncomputable def ep895 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 16) qz681 Bool.true 405379424047 1099511627776 845873015457709 216972127067176960 Bool.false 45666239265 1099511627776 844104141616689 216972127067176960 Bool.false

noncomputable abbrev qz682 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 15) qz143)

noncomputable def ep896 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 16) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz142 15) qz682) Bool.true 405379424047 1099511627776 845873015457709 216972127067176960 Bool.false 45666239265 1099511627776 844104141616689 216972127067176960

noncomputable def ep897 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 15) qz682 Bool.true 34961937907 274877906944 402742855003631 108486063533588480 Bool.true 27385951605 549755813888 401918583945941 108486063533588480 Bool.true

noncomputable abbrev qz683 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 14) qz143)

noncomputable def ep898 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 15) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz142 14) qz683) Bool.true 34961937907 274877906944 402742855003631 108486063533588480 Bool.true 27385951605 549755813888 401918583945941 108486063533588480

noncomputable def ep899 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 14) qz683 Bool.true 54055623005 137438953472 381809980076529 108486063533588480 Bool.true 27602624603 1099511627776 762158320922903 216972127067176960 Bool.false

noncomputable abbrev qz684 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 13) qz143)

noncomputable def ep900 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 14) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz142 13) qz684) Bool.true 54055623005 137438953472 381809980076529 108486063533588480 Bool.true 27602624603 1099511627776 762158320922903 216972127067176960

noncomputable def ep901 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 13) qz684 Bool.true 120869482541 549755813888 180078865295411 54243031766794240 Bool.false 210358641979 1099511627776 718821757382009 216972127067176960 Bool.true

noncomputable abbrev qz685 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 12) qz143)

noncomputable def ep902 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 13) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz142 12) qz685) Bool.true 120869482541 549755813888 180078865295411 54243031766794240 Bool.false 210358641979 1099511627776 718821757382009 216972127067176960

noncomputable def ep903 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 12) qz685 Bool.false 47439284201 1099511627776 675129320949191 216972127067176960 Bool.false 79519074517 1099511627776 673738841706711 216972127067176960 Bool.true

noncomputable abbrev qz686 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 11) qz143)

noncomputable def ep904 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 12) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz142 11) qz686) Bool.false 47439284201 1099511627776 675129320949191 216972127067176960 Bool.false 79519074517 1099511627776 673738841706711 216972127067176960

noncomputable def ep905 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 11) qz686 Bool.false 286419198931 1099511627776 628044029624323 216972127067176960 Bool.true 37560662641 274877906944 313329652039219 108486063533588480 Bool.true

noncomputable abbrev qz687 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 10) qz143)

noncomputable def ep906 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 11) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz142 10) qz687) Bool.false 286419198931 1099511627776 628044029624323 216972127067176960 Bool.true 37560662641 274877906944 313329652039219 108486063533588480

noncomputable def ep907 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 10) qz687 Bool.false 316750515889 549755813888 289272455681539 108486063533588480 Bool.true 64791333165 549755813888 18042326429559 6780378970849280 Bool.true

noncomputable abbrev qz688 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 9) qz143)

noncomputable def ep908 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 10) (@HAdd.hAdd Complex Complex Complex qz4 qz141 qz688) Bool.false 316750515889 549755813888 289272455681539 108486063533588480 Bool.true 64791333165 549755813888 18042326429559 6780378970849280

noncomputable def ep909 := @Enclosure.Complex.IsNear.addLitP qz141 qz688 Bool.false 390213106953 1099511627776 526517687401477 216972127067176960 Bool.false 72263011735 549755813888 262654910490661 108486063533588480 Bool.false

noncomputable abbrev qz155 := (@HMul.hMul Real Real Real qz269 qz439 qz568)

noncomputable def ep910 := @Enclosure.Complex.IsNear.of_eq qz688 (Complex.mk (@HMul.hMul Real Real Real qz0 qz323 (Real.cos qz155)) (@HMul.hMul Real Real Real qz0 qz323 (@Neg.neg Real Real.instNeg (Real.sin qz155)))) Bool.false 243287924825 1099511627776 52027223961601 216972127067176960 Bool.true 34263586225 137438953472 26022312382283 108486063533588480 (BSN.cpow_neg_s_mk qz145 140505 1000 9 qz146 rfl)

noncomputable def ep911 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz568 140505 1000 0 1 9895417793173221 4503599627370496 200000000118401 39467000000000000000 278071135405960683321 900719925474099200 5620200003327186501 7893400000000000000000 qz147 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 200000000118401 39467000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz569) Bool.false 41504390431577613533184 18889465931478580854784 1000000000592005 197335000000000000000 9895417793173221 4503599627370496 200000000118401 39467000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 61752 524288 24973259072661432 36028797018963968 197335 1000000000000000 rfl rfl rfl rfl (ep175 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep912 := nat_lit 387341948325605225621175613405735590398455435318103163575628203427195184251136

noncomputable def ep913 := nat_lit 117454092660136126482648732417711564496262112698360724848363723582184653056

noncomputable def ep914 := nat_lit 1161790936791495404610561542752371348066373781728912769277187882834421183447296

noncomputable def ep915 := BSN.cos_dyadic_bound_f 1814402014 2147483648 3 2 1048576 395056 ep912 ep72 ep913 ep914 ep75 ep913 696053 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1814402014) qz20 0 2 ep912 ep72 ep913 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1814402014) qz21 0 2 ep914 ep75 ep913 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz448 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 323717407) qz24)

noncomputable def ep916 := @Enclosure.Real.IsNear.cos_image qz155 qz448 Bool.false 323717407 1048576 747 1048576 Bool.false 696053 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz155 Bool.false 278071135405960683321 900719925474099200 5620200003327186501 7893400000000000000000 323717407 1048576 747 1048576 (ep911 rfl) rfl) (Enclosure.sfrac_false_div 323717407 1048576) (BSN.cos_reduce0 qz448 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 127677191188236388532224) qz25) 226375608064910080 72057594037927936 Bool.false 696053 1048576 49 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q0 323717407 1048576 226375608064910080 72057594037927936 49 127677191188236388532224 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 696053 1048576 127677191188236388532224 151115727451828646838272 1814402014 2147483648 395056 394670 (ep915 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep917 := nat_lit 10837623939782009546393303465180390416

noncomputable def ep918 := BSN.sin_dyadic_bound_f 1814402014 2147483648 2 1 1048576 395056 ep917 ep58 ep917 ep917 ep59 ep917 784232 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1814402014) qz15 0 1 ep917 ep58 ep917 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1814402014) qz16 0 1 ep917 ep59 ep917 rfl rfl rfl rfl) rfl rfl

noncomputable def ep919 := @Enclosure.Real.IsNear.sin_image qz155 qz448 Bool.false 323717407 1048576 747 1048576 Bool.false 784232 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz155 Bool.false 278071135405960683321 900719925474099200 5620200003327186501 7893400000000000000000 323717407 1048576 747 1048576 (ep911 rfl) rfl) (Enclosure.sfrac_false_div 323717407 1048576) (BSN.sin_reduce0 qz448 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 127677191188236388532224) qz25) 226375608064910080 72057594037927936 Bool.false 784232 1048576 49 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q0 323717407 1048576 226375608064910080 72057594037927936 49 127677191188236388532224 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 784232 1048576 127677191188236388532224 151115727451828646838272 1814402014 2147483648 395056 394670 (ep918 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep920 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz323 (Real.cos qz155)) (@HMul.hMul Real Real Real qz0 qz323 (@Neg.neg Real Real.instNeg (Real.sin qz155))) Bool.false 243287924825 1099511627776 52027223961601 216972127067176960 Bool.true 34263586225 137438953472 26022312382283 108486063533588480 (@Enclosure.Real.IsNear.mulLit_ff qz323 (Real.cos qz155) 349525 1048576 1 1048576 696053 1048576 148457821 206920744960 243287924825 1099511627776 52027223961601 216972127067176960 qz327 (@Enclosure.Real.IsNear.recentre' (Real.cos qz155) Bool.false 696053 1048576 148457821 206920744960 696053 1048576 148457821 206920744960 (ep916 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz323 (@Neg.neg Real Real.instNeg (Real.sin qz155)) 349525 1048576 1 1048576 98029 131072 148457821 206920744960 34263586225 137438953472 26022312382283 108486063533588480 qz327 (@Enclosure.Real.IsNear.neg (Real.sin qz155) Bool.false 98029 131072 148457821 206920744960 (@Enclosure.Real.IsNear.recentre' (Real.sin qz155) Bool.false 784232 1048576 148457821 206920744960 98029 131072 148457821 206920744960 (ep919 rfl rfl) rfl)) rfl)

noncomputable def ep921 := @ep909 243287924825 1099511627776 52027223961601 216972127067176960 Bool.true 34263586225 137438953472 26022312382283 108486063533588480 Bool.false 696541750648004283465728 316750515889 549755813888 289272455681539 108486063533588480 Bool.true 8904853024253285498880 64791333165 549755813888 18042326429559 6780378970849280 EMRow48.d13 (ep910 ep920) rfl rfl

noncomputable abbrev qz156 := (@HMul.hMul Real Real Real qz269 qz439 qz571)

noncomputable def ep922 := @Enclosure.Complex.IsNear.of_eq qz687 (Complex.mk (@HMul.hMul Real Real Real qz0 qz34 (Real.cos qz156)) (@HMul.hMul Real Real Real qz0 qz34 (@Neg.neg Real Real.instNeg (Real.sin qz156)))) Bool.true 347081832847 1099511627776 9899823652249 43394425413435392 Bool.true 10329992117 549755813888 4930485833255 21697212706717696 (BSN.cpow_neg_s_mk qz145 140505 1000 10 qz146 rfl)

noncomputable def ep923 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz571 140505 1000 0 1 10369917190100709 4503599627370496 200000000118401 39467000000000000000 291405042959020023609 900719925474099200 5620200003327186501 7893400000000000000000 qz147 (BSN.isNear_log_sfrac 10 1 10369917190100709 4503599627370496 200000000118401 39467000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz572) Bool.false 43494585150108164161536 18889465931478580854784 1000000000592005 197335000000000000000 10369917190100709 4503599627370496 200000000118401 39467000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 116991 524288 24973259072661432 36028797018963968 197335 1000000000000000 rfl rfl rfl rfl (ep190 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep924 := nat_lit 7148563840838301694513845912881194253049568766532277998265476822923802982297185

noncomputable def ep925 := nat_lit 12312260794687606127261522421001444671012359566905336521983480281841537724001

noncomputable def ep926 := nat_lit 18702494970432724504282601592673887371376755330190500402993037472915550083034721

noncomputable def ep927 := BSN.sin_dyadic_bound_f 3245579307 2147483648 3 2 1048576 395056 ep924 ep79 ep925 ep926 ep81 ep925 1046723 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3245579307) qz15 0 2 ep924 ep79 ep925 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3245579307) qz16 0 2 ep926 ep81 ep925 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz449 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 169620059) qz17)

noncomputable def ep928 := @Enclosure.Real.IsNear.cos_image qz156 qz449 Bool.false 169620059 524288 187 262144 Bool.true 1046723 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz156 Bool.false 291405042959020023609 900719925474099200 5620200003327186501 7893400000000000000000 169620059 524288 187 262144 (ep923 rfl) rfl) (Enclosure.sfrac_false_div 169620059 524288) (BSN.cos_reduce1 qz449 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 114193669989976399413248) qz19) 226375608064910080 72057594037927936 Bool.false 1046723 1048576 51 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q1 169620059 524288 226375608064910080 72057594037927936 51 114193669989976399413248 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1046723 1048576 114193669989976399413248 75557863725914323419136 3245579307 2147483648 395056 394670 (ep927 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep929 := nat_lit 3976896471930028766342030628232219671547988141214334593046146448416264562486881

noncomputable def ep930 := nat_lit 11906064894200711086771568839854656125301939704509193106094472384685110612012641

noncomputable def ep931 := BSN.cos_dyadic_bound_f 3245579307 2147483648 3 2 1048576 395056 ep929 ep72 ep925 ep930 ep75 ep925 62306 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3245579307) qz20 0 2 ep929 ep72 ep925 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3245579307) qz21 0 2 ep930 ep75 ep925 rfl rfl rfl rfl) rfl rfl

noncomputable def ep932 := @Enclosure.Real.IsNear.sin_image qz156 qz449 Bool.false 169620059 524288 187 262144 Bool.false 62306 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz156 Bool.false 291405042959020023609 900719925474099200 5620200003327186501 7893400000000000000000 169620059 524288 187 262144 (ep923 rfl) rfl) (Enclosure.sfrac_false_div 169620059 524288) (BSN.sin_reduce1 qz449 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 114193669989976399413248) qz19) 226375608064910080 72057594037927936 Bool.false 62306 1048576 51 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q1 169620059 524288 226375608064910080 72057594037927936 51 114193669989976399413248 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 62306 1048576 114193669989976399413248 75557863725914323419136 3245579307 2147483648 395056 394670 (ep931 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep933 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz34 (Real.cos qz156)) (@HMul.hMul Real Real Real qz0 qz34 (@Neg.neg Real Real.instNeg (Real.sin qz156))) Bool.true 347081832847 1099511627776 9899823652249 43394425413435392 Bool.true 10329992117 549755813888 4930485833255 21697212706717696 (@Enclosure.Real.IsNear.mulLit_ft qz34 (Real.cos qz156) 331589 1048576 1 1048576 1046723 1048576 37163789 51730186240 347081832847 1099511627776 9899823652249 43394425413435392 qz329 (@Enclosure.Real.IsNear.recentre' (Real.cos qz156) Bool.true 1046723 1048576 37163789 51730186240 1046723 1048576 37163789 51730186240 (ep928 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz34 (@Neg.neg Real Real.instNeg (Real.sin qz156)) 331589 1048576 1 1048576 31153 524288 37163789 51730186240 10329992117 549755813888 4930485833255 21697212706717696 qz329 (@Enclosure.Real.IsNear.neg (Real.sin qz156) Bool.false 31153 524288 37163789 51730186240 (@Enclosure.Real.IsNear.recentre' (Real.sin qz156) Bool.false 62306 1048576 37163789 51730186240 31153 524288 37163789 51730186240 (ep932 rfl rfl) rfl)) rfl)

noncomputable def ep934 := @ep907 347081832847 1099511627776 9899823652249 43394425413435392 Bool.true 10329992117 549755813888 4930485833255 21697212706717696 Bool.false 157460619821460884553728 286419198931 1099511627776 628044029624323 216972127067176960 Bool.true 41298385320751101116416 37560662641 274877906944 313329652039219 108486063533588480 (ep908 (BSN.head_sum_c_succ qz142 9 10 rfl rfl) (ep921 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep922 ep933) rfl rfl

noncomputable abbrev qz157 := (@HMul.hMul Real Real Real qz269 qz439 qz574)

noncomputable def ep935 := @Enclosure.Complex.IsNear.of_eq qz686 (Complex.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz157)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz157)))) Bool.true 119489957365 549755813888 11771322831217 54243031766794240 Bool.false 229761725081 1099511627776 47079537628273 216972127067176960 (BSN.cpow_neg_s_mk qz145 140505 1000 11 qz146 rfl)

noncomputable def ep936 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz574 140505 1000 0 1 10799156221662949 4503599627370496 200000000118401 39467000000000000000 303467088984950529849 900719925474099200 5620200003327186501 7893400000000000000000 qz147 (BSN.isNear_log_sfrac 11 1 10799156221662949 4503599627370496 200000000118401 39467000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz575) Bool.false 45294944137145793642496 18889465931478580854784 1000000000592005 197335000000000000000 10799156221662949 4503599627370496 200000000118401 39467000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 166961 524288 24973259072661432 36028797018963968 197335 1000000000000000 rfl rfl rfl rfl (ep205 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep937 := nat_lit 261307294027465847800207803165383731147215867971873991569471830589803495161856

noncomputable def ep938 := nat_lit 53464787036944863436599479218579017325875759598243520424500867603655294976

noncomputable def ep939 := nat_lit 783814952508323653673750210537714035406995852396425487667566490034203174895616

noncomputable def ep940 := BSN.cos_dyadic_bound_f 1644403832 2147483648 3 2 1048576 395056 ep937 ep72 ep938 ep939 ep75 ep938 755890 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1644403832) qz20 0 2 ep937 ep72 ep938 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1644403832) qz21 0 2 ep939 ep75 ep938 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz450 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 88320547) qz31)

noncomputable def ep941 := @Enclosure.Real.IsNear.cos_image qz157 qz450 Bool.false 88320547 262144 747 1048576 Bool.true 755890 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz157 Bool.false 303467088984950529849 900719925474099200 5620200003327186501 7893400000000000000000 88320547 262144 747 1048576 (ep936 rfl) rfl) (Enclosure.sfrac_false_div 88320547 262144) (BSN.cos_reduce2 qz450 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 28928658145961473736704) qz321) 226375608064910080 72057594037927936 Bool.false 755890 1048576 53 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q2 88320547 262144 226375608064910080 72057594037927936 53 28928658145961473736704 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 755890 1048576 28928658145961473736704 37778931862957161709568 1644403832 2147483648 395056 394670 (ep940 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep942 := nat_lit 7311961914352731599339882696591282176

noncomputable def ep943 := BSN.sin_dyadic_bound_f 1644403832 2147483648 2 1 1048576 395056 ep942 ep58 ep942 ep942 ep59 ep942 726733 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1644403832) qz15 0 1 ep942 ep58 ep942 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1644403832) qz16 0 1 ep942 ep59 ep942 rfl rfl rfl rfl) rfl rfl

noncomputable def ep944 := @Enclosure.Real.IsNear.sin_image qz157 qz450 Bool.false 88320547 262144 747 1048576 Bool.true 726733 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz157 Bool.false 303467088984950529849 900719925474099200 5620200003327186501 7893400000000000000000 88320547 262144 747 1048576 (ep936 rfl) rfl) (Enclosure.sfrac_false_div 88320547 262144) (BSN.sin_reduce2 qz450 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 28928658145961473736704) qz321) 226375608064910080 72057594037927936 Bool.false 726733 1048576 53 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q2 88320547 262144 226375608064910080 72057594037927936 53 28928658145961473736704 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 726733 1048576 28928658145961473736704 37778931862957161709568 1644403832 2147483648 395056 394670 (ep943 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep945 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz157)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz157))) Bool.true 119489957365 549755813888 11771322831217 54243031766794240 Bool.false 229761725081 1099511627776 47079537628273 216972127067176960 (@Enclosure.Real.IsNear.mulLit_ft qz36 (Real.cos qz157) 316157 1048576 1 1048576 377945 524288 148457821 206920744960 119489957365 549755813888 11771322831217 54243031766794240 qz331 (@Enclosure.Real.IsNear.recentre' (Real.cos qz157) Bool.true 755890 1048576 148457821 206920744960 377945 524288 148457821 206920744960 (ep941 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz36 (@Neg.neg Real Real.instNeg (Real.sin qz157)) 316157 1048576 1 1048576 726733 1048576 148457821 206920744960 229761725081 1099511627776 47079537628273 216972127067176960 qz331 (@Enclosure.Real.IsNear.neg (Real.sin qz157) Bool.true 726733 1048576 148457821 206920744960 (@Enclosure.Real.IsNear.recentre' (Real.sin qz157) Bool.true 726733 1048576 148457821 206920744960 726733 1048576 148457821 206920744960 (ep944 rfl rfl) rfl)) rfl)

noncomputable def ep946 := @ep905 119489957365 549755813888 11771322831217 54243031766794240 Bool.false 229761725081 1099511627776 47079537628273 216972127067176960 Bool.false 26080022296184894783488 47439284201 1099511627776 675129320949191 216972127067176960 Bool.false 21858036765356927746048 79519074517 1099511627776 673738841706711 216972127067176960 (ep906 (BSN.head_sum_c_succ qz142 10 11 rfl rfl) (ep934 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep935 ep945) rfl rfl

noncomputable abbrev qz158 := (@HMul.hMul Real Real Real qz269 qz439 qz577)

noncomputable def ep947 := @Enclosure.Complex.IsNear.of_eq qz685 (Complex.mk (@HMul.hMul Real Real Real qz0 qz38 (Real.cos qz158)) (@HMul.hMul Real Real Real qz0 qz38 (@Neg.neg Real Real.instNeg (Real.sin qz158)))) Bool.true 289178249283 1099511627776 45186140232453 216972127067176960 Bool.false 65419783731 549755813888 22541457837649 108486063533588480 (BSN.cpow_neg_s_mk qz145 140505 1000 12 qz146 rfl)

noncomputable def ep948 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz577 140505 1000 0 1 11191020447815397 4503599627370496 200000000118401 39467000000000000000 314478865604060471097 900719925474099200 5620200003327186501 7893400000000000000000 qz147 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 200000000118401 39467000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz578) Bool.false 46938541828353910898688 18889465931478580854784 1000000000592005 197335000000000000000 11191020447815397 4503599627370496 200000000118401 39467000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 212580 524288 24973259072661432 36028797018963968 197335 1000000000000000 rfl rfl rfl rfl (ep216 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep949 := nat_lit 693162608514451336605636794496714721

noncomputable def ep950 := BSN.cos_dyadic_bound_f 912449383 2147483648 2 1 1048576 395056 ep949 ep62 ep949 ep949 ep63 ep949 955339 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 912449383) qz20 0 1 ep949 ep62 ep949 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 912449383) qz21 0 1 ep949 ep63 ep949 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz451 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 366101583) qz24)

noncomputable def ep951 := @Enclosure.Real.IsNear.cos_image qz158 qz451 Bool.false 366101583 1048576 187 262144 Bool.true 955339 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz158 Bool.false 314478865604060471097 900719925474099200 5620200003327186501 7893400000000000000000 366101583 1048576 187 262144 (ep948 rfl) rfl) (Enclosure.sfrac_false_div 366101583 1048576) (BSN.cos_reduce2 qz451 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 64207917209363064815616) qz25) 226375608064910080 72057594037927936 Bool.false 955339 1048576 55 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q2 366101583 1048576 226375608064910080 72057594037927936 55 64207917209363064815616 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 955339 1048576 64207917209363064815616 151115727451828646838272 912449383 2147483648 395056 394670 (ep950 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep952 := BSN.sin_dyadic_bound_f 912449383 2147483648 2 1 1048576 395056 ep949 ep58 ep949 ep949 ep59 ep949 432246 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 912449383) qz15 0 1 ep949 ep58 ep949 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 912449383) qz16 0 1 ep949 ep59 ep949 rfl rfl rfl rfl) rfl rfl

noncomputable def ep953 := @Enclosure.Real.IsNear.sin_image qz158 qz451 Bool.false 366101583 1048576 187 262144 Bool.true 432246 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz158 Bool.false 314478865604060471097 900719925474099200 5620200003327186501 7893400000000000000000 366101583 1048576 187 262144 (ep948 rfl) rfl) (Enclosure.sfrac_false_div 366101583 1048576) (BSN.sin_reduce2 qz451 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 64207917209363064815616) qz25) 226375608064910080 72057594037927936 Bool.false 432246 1048576 55 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q2 366101583 1048576 226375608064910080 72057594037927936 55 64207917209363064815616 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 432246 1048576 64207917209363064815616 151115727451828646838272 912449383 2147483648 395056 394670 (ep952 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep954 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz38 (Real.cos qz158)) (@HMul.hMul Real Real Real qz0 qz38 (@Neg.neg Real Real.instNeg (Real.sin qz158))) Bool.true 289178249283 1099511627776 45186140232453 216972127067176960 Bool.false 65419783731 549755813888 22541457837649 108486063533588480 (@Enclosure.Real.IsNear.mulLit_ft qz38 (Real.cos qz158) 302697 1048576 1 1048576 955339 1048576 37163789 51730186240 289178249283 1099511627776 45186140232453 216972127067176960 qz333 (@Enclosure.Real.IsNear.recentre' (Real.cos qz158) Bool.true 955339 1048576 37163789 51730186240 955339 1048576 37163789 51730186240 (ep951 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz38 (@Neg.neg Real Real.instNeg (Real.sin qz158)) 302697 1048576 1 1048576 216123 524288 37163789 51730186240 65419783731 549755813888 22541457837649 108486063533588480 qz333 (@Enclosure.Real.IsNear.neg (Real.sin qz158) Bool.true 216123 524288 37163789 51730186240 (@Enclosure.Real.IsNear.recentre' (Real.sin qz158) Bool.true 432246 1048576 37163789 51730186240 216123 524288 37163789 51730186240 (ep953 rfl rfl) rfl)) rfl)

noncomputable def ep955 := @ep903 289178249283 1099511627776 45186140232453 216972127067176960 Bool.false 65419783731 549755813888 22541457837649 108486063533588480 Bool.true 265794802994195445317632 120869482541 549755813888 180078865295411 54243031766794240 Bool.false 115645886429539548004352 210358641979 1099511627776 718821757382009 216972127067176960 (ep904 (BSN.head_sum_c_succ qz142 11 12 rfl rfl) (ep946 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep947 ep954) rfl rfl

noncomputable abbrev qz159 := (@HMul.hMul Real Real Real qz269 qz439 qz580)

noncomputable def ep956 := @Enclosure.Complex.IsNear.of_eq qz684 (Complex.mk (@HMul.hMul Real Real Real qz0 qz40 (Real.cos qz159)) (@HMul.hMul Real Real Real qz0 qz40 (@Neg.neg Real Real.instNeg (Real.sin qz159)))) Bool.true 95353009479 549755813888 21652249485707 108486063533588480 Bool.true 118980633291 549755813888 21668281770447 108486063533588480 (BSN.cpow_neg_s_mk qz145 140505 1000 13 qz146 rfl)

noncomputable def ep957 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz580 140505 1000 0 1 11551497052968677 4503599627370496 200000000118401 39467000000000000000 324608618685472792377 900719925474099200 5620200003327186501 7893400000000000000000 qz147 (BSN.isNear_log_sfrac 13 1 11551497052968677 4503599627370496 200000000118401 39467000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz581) Bool.false 48450490295254733815808 18889465931478580854784 1000000000592005 197335000000000000000 11551497052968677 4503599627370496 200000000118401 39467000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 254545 524288 24973259072661432 36028797018963968 197335 1000000000000000 rfl rfl rfl rfl (ep227 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep958 := nat_lit 4430849908765804788943167700380160000

noncomputable def ep959 := BSN.sin_dyadic_bound_f 1450847480 2147483648 2 1 1048576 395056 ep958 ep58 ep958 ep958 ep59 ep958 655746 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1450847480) qz15 0 1 ep958 ep58 ep958 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1450847480) qz16 0 1 ep958 ep59 ep958 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz452 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 47236771) qz553)

noncomputable def ep960 := @Enclosure.Real.IsNear.cos_image qz159 qz452 Bool.false 47236771 131072 747 1048576 Bool.true 655746 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz159 Bool.false 324608618685472792377 900719925474099200 5620200003327186501 7893400000000000000000 47236771 131072 747 1048576 (ep957 rfl) rfl) (Enclosure.sfrac_false_div 47236771 131072) (BSN.cos_reduce1 qz452 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 12761789396122727350272) qz305) 226375608064910080 72057594037927936 Bool.false 655746 1048576 57 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q1 47236771 131072 226375608064910080 72057594037927936 57 12761789396122727350272 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 655746 1048576 12761789396122727350272 18889465931478580854784 1450847480 2147483648 395056 394670 (ep959 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep961 := nat_lit 158332342345670501471211040996968488251979380019369907226505476840672460800000

noncomputable def ep962 := nat_lit 19632430914009940621856045019684296628616277207452559265808521625600000000

noncomputable def ep963 := nat_lit 474957762175183484532389410900866096162680907503694816560984813478766182400000

noncomputable def ep964 := BSN.cos_dyadic_bound_f 1450847480 2147483648 3 2 1048576 395056 ep961 ep72 ep962 ep963 ep75 ep962 818234 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1450847480) qz20 0 2 ep961 ep72 ep962 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1450847480) qz21 0 2 ep963 ep75 ep962 rfl rfl rfl rfl) rfl rfl

noncomputable def ep965 := @Enclosure.Real.IsNear.sin_image qz159 qz452 Bool.false 47236771 131072 747 1048576 Bool.false 818234 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz159 Bool.false 324608618685472792377 900719925474099200 5620200003327186501 7893400000000000000000 47236771 131072 747 1048576 (ep957 rfl) rfl) (Enclosure.sfrac_false_div 47236771 131072) (BSN.sin_reduce1 qz452 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 12761789396122727350272) qz305) 226375608064910080 72057594037927936 Bool.false 818234 1048576 57 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q1 47236771 131072 226375608064910080 72057594037927936 57 12761789396122727350272 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 818234 1048576 12761789396122727350272 18889465931478580854784 1450847480 2147483648 395056 394670 (ep964 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep966 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz40 (Real.cos qz159)) (@HMul.hMul Real Real Real qz0 qz40 (@Neg.neg Real Real.instNeg (Real.sin qz159))) Bool.true 95353009479 549755813888 21652249485707 108486063533588480 Bool.true 118980633291 549755813888 21668281770447 108486063533588480 (@Enclosure.Real.IsNear.mulLit_ft qz40 (Real.cos qz159) 290823 1048576 1 1048576 327873 524288 148457821 206920744960 95353009479 549755813888 21652249485707 108486063533588480 qz335 (@Enclosure.Real.IsNear.recentre' (Real.cos qz159) Bool.true 655746 1048576 148457821 206920744960 327873 524288 148457821 206920744960 (ep960 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz40 (@Neg.neg Real Real.instNeg (Real.sin qz159)) 290823 1048576 1 1048576 409117 524288 148457821 206920744960 118980633291 549755813888 21668281770447 108486063533588480 qz335 (@Enclosure.Real.IsNear.neg (Real.sin qz159) Bool.false 409117 524288 148457821 206920744960 (@Enclosure.Real.IsNear.recentre' (Real.sin qz159) Bool.false 818234 1048576 148457821 206920744960 409117 524288 148457821 206920744960 (ep965 rfl rfl) rfl)) rfl)

noncomputable def ep967 := @ep901 95353009479 549755813888 21652249485707 108486063533588480 Bool.true 118980633291 549755813888 21668281770447 108486063533588480 Bool.true 118869572081346685173760 54055623005 137438953472 381809980076529 108486063533588480 Bool.true 15174703354067197886464 27602624603 1099511627776 762158320922903 216972127067176960 (ep902 (BSN.head_sum_c_succ qz142 12 13 rfl rfl) (ep955 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep956 ep966) rfl rfl

noncomputable abbrev qz160 := (@HMul.hMul Real Real Real qz269 qz439 qz583)

noncomputable def ep968 := @Enclosure.Complex.IsNear.of_eq qz683 (Complex.mk (@HMul.hMul Real Real Real qz0 qz42 (Real.cos qz160)) (@HMul.hMul Real Real Real qz0 qz42 (@Neg.neg Real Real.instNeg (Real.sin qz160)))) Bool.false 73149308103 274877906944 10466437463551 54243031766794240 Bool.true 27169278607 1099511627776 41678846968979 216972127067176960 (BSN.cpow_neg_s_mk qz145 140505 1000 14 qz146 rfl)

noncomputable def ep969 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz583 140505 1000 0 1 11885250371606245 4503599627370496 200000000118401 39467000000000000000 66797484138501418149 180143985094819840 5620200003327186501 7893400000000000000000 qz147 (BSN.isNear_log_sfrac 14 1 11885250371606245 4503599627370496 200000000118401 39467000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz584) Bool.false 49850353174629559828480 18889465931478580854784 1000000000592005 197335000000000000000 11885250371606245 4503599627370496 200000000118401 39467000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 293399 524288 24973259072661432 36028797018963968 197335 1000000000000000 rfl rfl rfl rfl (ep238 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep970 := nat_lit 1563103366448087441736011343860641

noncomputable def ep971 := BSN.cos_dyadic_bound_f 198836873 2147483648 2 1 1048576 395056 ep970 ep62 ep970 ep970 ep63 ep970 1044084 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 198836873) qz20 0 1 ep970 ep62 ep970 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 198836873) qz21 0 1 ep970 ep63 ep970 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz453 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 194406265) qz17)

noncomputable def ep972 := @Enclosure.Real.IsNear.cos_image qz160 qz453 Bool.false 194406265 524288 187 262144 Bool.false 1044084 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz160 Bool.false 66797484138501418149 180143985094819840 5620200003327186501 7893400000000000000000 194406265 524288 187 262144 (ep969 rfl) rfl) (Enclosure.sfrac_false_div 194406265 524288) (BSN.cos_reduce0 qz453 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6995950531680812400640) qz19) 226375608064910080 72057594037927936 Bool.false 1044084 1048576 59 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q0 194406265 524288 226375608064910080 72057594037927936 59 6995950531680812400640 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1044084 1048576 6995950531680812400640 75557863725914323419136 198836873 2147483648 395056 394670 (ep971 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep973 := BSN.sin_dyadic_bound_f 198836873 2147483648 1 0 1048576 395056 0 1 1 0 1 1 96949 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 198836873) qz15 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 198836873) qz16 0 0 rfl) rfl rfl

noncomputable def ep974 := @Enclosure.Real.IsNear.sin_image qz160 qz453 Bool.false 194406265 524288 187 262144 Bool.false 96949 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz160 Bool.false 66797484138501418149 180143985094819840 5620200003327186501 7893400000000000000000 194406265 524288 187 262144 (ep969 rfl) rfl) (Enclosure.sfrac_false_div 194406265 524288) (BSN.sin_reduce0 qz453 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6995950531680812400640) qz19) 226375608064910080 72057594037927936 Bool.false 96949 1048576 59 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q0 194406265 524288 226375608064910080 72057594037927936 59 6995950531680812400640 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 96949 1048576 6995950531680812400640 75557863725914323419136 198836873 2147483648 395056 394670 (ep973 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep975 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz42 (Real.cos qz160)) (@HMul.hMul Real Real Real qz0 qz42 (@Neg.neg Real Real.instNeg (Real.sin qz160))) Bool.false 73149308103 274877906944 10466437463551 54243031766794240 Bool.true 27169278607 1099511627776 41678846968979 216972127067176960 (@Enclosure.Real.IsNear.mulLit_ff qz42 (Real.cos qz160) 280243 1048576 1 1048576 261021 262144 37163789 51730186240 73149308103 274877906944 10466437463551 54243031766794240 qz337 (@Enclosure.Real.IsNear.recentre' (Real.cos qz160) Bool.false 1044084 1048576 37163789 51730186240 261021 262144 37163789 51730186240 (ep972 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz42 (@Neg.neg Real Real.instNeg (Real.sin qz160)) 280243 1048576 1 1048576 96949 1048576 37163789 51730186240 27169278607 1099511627776 41678846968979 216972127067176960 qz337 (@Enclosure.Real.IsNear.neg (Real.sin qz160) Bool.false 96949 1048576 37163789 51730186240 (@Enclosure.Real.IsNear.recentre' (Real.sin qz160) Bool.false 96949 1048576 37163789 51730186240 96949 1048576 37163789 51730186240 (ep974 rfl rfl) rfl)) rfl)

noncomputable def ep976 := @ep899 73149308103 274877906944 10466437463551 54243031766794240 Bool.true 27169278607 1099511627776 41678846968979 216972127067176960 Bool.true 4805132157291126063104 34961937907 274877906944 402742855003631 108486063533588480 Bool.true 60222344454816619560960 27385951605 549755813888 401918583945941 108486063533588480 (ep900 (BSN.head_sum_c_succ qz142 13 14 rfl rfl) (ep967 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep968 ep975) rfl rfl

noncomputable abbrev qz161 := (@HMul.hMul Real Real Real qz269 qz439 qz586)

noncomputable def ep977 := @Enclosure.Complex.IsNear.of_eq qz682 (Complex.mk (@HMul.hMul Real Real Real qz0 qz44 (Real.cos qz161)) (@HMul.hMul Real Real Real qz0 qz44 (@Neg.neg Real Real.instNeg (Real.sin qz161)))) Bool.true 265531672419 1099511627776 40387305450447 216972127067176960 Bool.false 100438142475 1099511627776 40266973724807 216972127067176960 (BSN.cpow_neg_s_mk qz145 140505 1000 15 qz146 rfl)

noncomputable def ep978 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz586 140505 1000 0 1 12195965485668069 4503599627370496 200000000118401 39467000000000000000 342718826112758406969 900719925474099200 5620200003327186501 7893400000000000000000 qz147 (BSN.isNear_log_sfrac 15 1 12195965485668069 4503599627370496 200000000118401 39467000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz587) Bool.false 51153586820399524478976 18889465931478580854784 1000000000592005 197335000000000000000 12195965485668069 4503599627370496 200000000118401 39467000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 329571 524288 24973259072661432 36028797018963968 197335 1000000000000000 rfl rfl rfl rfl (ep253 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep979 := nat_lit 363689323679850072164525200227123456

noncomputable def ep980 := BSN.cos_dyadic_bound_f 776573628 2147483648 2 1 1048576 395056 ep979 ep62 ep979 ep979 ep63 ep979 980759 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 776573628) qz20 0 1 ep979 ep62 ep979 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 776573628) qz21 0 1 ep979 ep63 ep979 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz454 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 49872153) qz553)

noncomputable def ep981 := @Enclosure.Real.IsNear.cos_image qz161 qz454 Bool.false 49872153 131072 747 1048576 Bool.true 980759 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz161 Bool.false 342718826112758406969 900719925474099200 5620200003327186501 7893400000000000000000 49872153 131072 747 1048576 (ep978 rfl) rfl) (Enclosure.sfrac_false_div 49872153 131072) (BSN.cos_reduce2 qz454 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6830813874157304938496) qz305) 226375608064910080 72057594037927936 Bool.false 980759 1048576 60 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q2 49872153 131072 226375608064910080 72057594037927936 60 6830813874157304938496 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 980759 1048576 6830813874157304938496 18889465931478580854784 776573628 2147483648 395056 394670 (ep980 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep982 := BSN.sin_dyadic_bound_f 776573628 2147483648 2 1 1048576 395056 ep979 ep58 ep979 ep979 ep59 ep979 370975 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 776573628) qz15 0 1 ep979 ep58 ep979 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 776573628) qz16 0 1 ep979 ep59 ep979 rfl rfl rfl rfl) rfl rfl

noncomputable def ep983 := @Enclosure.Real.IsNear.sin_image qz161 qz454 Bool.false 49872153 131072 747 1048576 Bool.true 370975 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz161 Bool.false 342718826112758406969 900719925474099200 5620200003327186501 7893400000000000000000 49872153 131072 747 1048576 (ep978 rfl) rfl) (Enclosure.sfrac_false_div 49872153 131072) (BSN.sin_reduce2 qz454 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6830813874157304938496) qz305) 226375608064910080 72057594037927936 Bool.false 370975 1048576 60 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q2 49872153 131072 226375608064910080 72057594037927936 60 6830813874157304938496 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 370975 1048576 6830813874157304938496 18889465931478580854784 776573628 2147483648 395056 394670 (ep982 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep984 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz44 (Real.cos qz161)) (@HMul.hMul Real Real Real qz0 qz44 (@Neg.neg Real Real.instNeg (Real.sin qz161))) Bool.true 265531672419 1099511627776 40387305450447 216972127067176960 Bool.false 100438142475 1099511627776 40266973724807 216972127067176960 (@Enclosure.Real.IsNear.mulLit_ft qz44 (Real.cos qz161) 270741 1048576 1 1048576 980759 1048576 148457821 206920744960 265531672419 1099511627776 40387305450447 216972127067176960 qz339 (@Enclosure.Real.IsNear.recentre' (Real.cos qz161) Bool.true 980759 1048576 148457821 206920744960 980759 1048576 148457821 206920744960 (ep981 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz44 (@Neg.neg Real Real.instNeg (Real.sin qz161)) 270741 1048576 1 1048576 370975 1048576 148457821 206920744960 100438142475 1099511627776 40266973724807 216972127067176960 qz339 (@Enclosure.Real.IsNear.neg (Real.sin qz161) Bool.true 370975 1048576 148457821 206920744960 (@Enclosure.Real.IsNear.recentre' (Real.sin qz161) Bool.true 370975 1048576 148457821 206920744960 370975 1048576 148457821 206920744960 (ep983 rfl rfl) rfl)) rfl)

noncomputable def ep985 := @ep897 265531672419 1099511627776 40387305450447 216972127067176960 Bool.false 100438142475 1099511627776 40266973724807 216972127067176960 Bool.true 111429847600203581882368 405379424047 1099511627776 845873015457709 216972127067176960 Bool.false 25105280534334217912320 45666239265 1099511627776 844104141616689 216972127067176960 (ep898 (BSN.head_sum_c_succ qz142 14 15 rfl rfl) (ep976 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep977 ep984) rfl rfl

noncomputable abbrev qz162 := (@HMul.hMul Real Real Real qz269 qz439 qz589)

noncomputable def ep986 := @Enclosure.Complex.IsNear.of_eq qz681 (Complex.mk (@HMul.hMul Real Real Real qz0 qz46 (Real.cos qz162)) (@HMul.hMul Real Real Real qz0 qz46 (@Neg.neg Real Real.instNeg (Real.sin qz162)))) Bool.false 137436594183 549755813888 19562122505247 108486063533588480 Bool.true 174849381 137438953472 4864797500973 27121515883397120 (BSN.cpow_neg_s_mk qz145 140505 1000 16 qz146 rfl)

noncomputable def ep987 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz589 140505 1000 0 1 3121657384082679 1125899906842624 50000000039467 9866750000000000000 87721694150107362579 225179981368524800 1405050001109062167 1973350000000000000000 qz147 (BSN.isNear_log_sfrac 16 1 3121657384082679 1125899906842624 50000000039467 9866750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz590) Bool.false 52372720210750067441664 18889465931478580854784 1000000000789340 197335000000000000000 3121657384082679 1125899906842624 50000000039467 9866750000000000000 (BSN.log_rat_reduce_isNear 16 1 4 32 32 0 524288 24973259072661432 36028797018963968 197335 1000000000000000 rfl rfl rfl rfl (ep268 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep988 := BSN.cos_dyadic_bound_f 10928879 2147483648 1 0 1048576 395056 0 1 1 0 1 1 1048562 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 10928879) qz20 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 10928879) qz21 0 0 rfl) rfl rfl

noncomputable abbrev qz455 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 204242985) qz17)

noncomputable def ep989 := @Enclosure.Real.IsNear.cos_image qz162 qz455 Bool.false 204242985 524288 747 1048576 Bool.false 1048562 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz162 Bool.false 87721694150107362579 225179981368524800 1405050001109062167 1973350000000000000000 204242985 524288 747 1048576 (ep987 rfl) rfl) (Enclosure.sfrac_false_div 204242985 524288) (BSN.cos_reduce0 qz455 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 384525767586873344000) qz19) 226375608064910080 72057594037927936 Bool.false 1048562 1048576 62 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q0 204242985 524288 226375608064910080 72057594037927936 62 384525767586873344000 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1048562 1048576 384525767586873344000 75557863725914323419136 10928879 2147483648 395056 394670 (ep988 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep990 := BSN.sin_dyadic_bound_f 10928879 2147483648 1 0 1048576 395056 0 1 1 0 1 1 5336 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 10928879) qz15 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 10928879) qz16 0 0 rfl) rfl rfl

noncomputable def ep991 := @Enclosure.Real.IsNear.sin_image qz162 qz455 Bool.false 204242985 524288 747 1048576 Bool.false 5336 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz162 Bool.false 87721694150107362579 225179981368524800 1405050001109062167 1973350000000000000000 204242985 524288 747 1048576 (ep987 rfl) rfl) (Enclosure.sfrac_false_div 204242985 524288) (BSN.sin_reduce0 qz455 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 384525767586873344000) qz19) 226375608064910080 72057594037927936 Bool.false 5336 1048576 62 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q0 204242985 524288 226375608064910080 72057594037927936 62 384525767586873344000 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 5336 1048576 384525767586873344000 75557863725914323419136 10928879 2147483648 395056 394670 (ep990 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep992 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz46 (Real.cos qz162)) (@HMul.hMul Real Real Real qz0 qz46 (@Neg.neg Real Real.instNeg (Real.sin qz162))) Bool.false 137436594183 549755813888 19562122505247 108486063533588480 Bool.true 174849381 137438953472 4864797500973 27121515883397120 (@Enclosure.Real.IsNear.mulLit_ff qz46 (Real.cos qz162) 262143 1048576 1 1048576 524281 524288 148457821 206920744960 137436594183 549755813888 19562122505247 108486063533588480 qz341 (@Enclosure.Real.IsNear.recentre' (Real.cos qz162) Bool.false 1048562 1048576 148457821 206920744960 524281 524288 148457821 206920744960 (ep989 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz46 (@Neg.neg Real Real.instNeg (Real.sin qz162)) 262143 1048576 1 1048576 667 131072 148457821 206920744960 174849381 137438953472 4864797500973 27121515883397120 qz341 (@Enclosure.Real.IsNear.neg (Real.sin qz162) Bool.false 667 131072 148457821 206920744960 (@Enclosure.Real.IsNear.recentre' (Real.sin qz162) Bool.false 5336 1048576 148457821 206920744960 667 131072 148457821 206920744960 (ep991 rfl rfl) rfl)) rfl)

noncomputable def ep993 := @ep895 137436594183 549755813888 19562122505247 108486063533588480 Bool.true 174849381 137438953472 4864797500973 27121515883397120 Bool.true 71746561814267300937728 130506235681 1099511627776 884997260468203 216972127067176960 Bool.false 6084071206064618471424 44267444217 1099511627776 883022521624473 216972127067176960 (ep896 (BSN.head_sum_c_succ qz142 15 16 rfl rfl) (ep985 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep986 ep992) rfl rfl

theorem EMRow48.d14 : Enclosure.Complex.IsNear qz154 Bool.true 130506235681 1099511627776 884997260468203 216972127067176960 Bool.false 44267444217 1099511627776 883022521624473 216972127067176960 := ep894 (BSN.head_sum_c_succ qz142 16 17 rfl rfl) (ep993 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz163 := (BSN.headSumC qz437 25)

noncomputable abbrev qz689 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 24) qz143)

noncomputable def ep994 := @Enclosure.Complex.IsNear.of_eq qz163 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz142 24) qz689) Bool.false 670912389343 1099511627776 232596190320745 43394425413435392 Bool.true 17063795071 68719476736 116063894331675 21697212706717696

noncomputable def ep995 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 24) qz689 Bool.false 466550520611 1099511627776 226203325301381 43394425413435392 Bool.true 90121474059 549755813888 56438874704307 10848606353358848 Bool.false

noncomputable abbrev qz690 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 23) qz143)

noncomputable def ep996 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 24) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz142 23) qz690) Bool.false 466550520611 1099511627776 226203325301381 43394425413435392 Bool.true 90121474059 549755813888 56438874704307 10848606353358848

noncomputable def ep997 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 23) qz690 Bool.false 295613674067 1099511627776 1098359790496761 216972127067176960 Bool.true 27460685793 1099511627776 1096137043393051 216972127067176960 Bool.false

noncomputable abbrev qz691 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 22) qz143)

noncomputable def ep998 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 23) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz142 22) qz691) Bool.false 295613674067 1099511627776 1098359790496761 216972127067176960 Bool.true 27460685793 1099511627776 1096137043393051 216972127067176960

noncomputable def ep999 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 22) qz691 Bool.false 63417981781 549755813888 532488880056719 108486063533588480 Bool.false 135220401765 1099511627776 1062760394532513 216972127067176960 Bool.false

noncomputable abbrev qz692 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 21) qz143)

noncomputable def ep1000 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 22) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz142 21) qz692) Bool.false 63417981781 549755813888 532488880056719 108486063533588480 Bool.false 135220401765 1099511627776 1062760394532513 216972127067176960

noncomputable def ep1001 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 21) qz692 Bool.true 41054825387 549755813888 515301046808839 108486063533588480 Bool.false 253158919415 1099511627776 1028541698951843 216972127067176960 Bool.false

noncomputable abbrev qz693 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 20) qz143)

noncomputable def ep1002 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 21) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz142 20) qz693) Bool.true 41054825387 549755813888 515301046808839 108486063533588480 Bool.false 253158919415 1099511627776 1028541698951843 216972127067176960

noncomputable def ep1003 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 20) qz693 Bool.true 327552034443 1099511627776 995586617852473 216972127067176960 Bool.false 238862406609 1099511627776 993720761357683 216972127067176960 Bool.false

noncomputable abbrev qz694 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 19) qz143)

noncomputable def ep1004 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 20) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz142 19) qz694) Bool.true 327552034443 1099511627776 995586617852473 216972127067176960 Bool.false 238862406609 1099511627776 993720761357683 216972127067176960

noncomputable def ep1005 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 19) qz694 Bool.true 233836059543 549755813888 479879330666959 108486063533588480 Bool.false 3639546045 137438953472 478917844690369 108486063533588480 Bool.false

noncomputable abbrev qz695 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 18) qz143)

noncomputable def ep1006 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 19) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz142 18) qz695) Bool.true 233836059543 549755813888 479879330666959 108486063533588480 Bool.false 3639546045 137438953472 478917844690369 108486063533588480

noncomputable def ep1007 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 18) qz695 Bool.true 295888580781 1099511627776 922881083539781 216972127067176960 Bool.true 41231459039 274877906944 460470169699583 108486063533588480 Bool.true

noncomputable abbrev qz696 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 17) qz143)

noncomputable def ep1008 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 18) (@HAdd.hAdd Complex Complex Complex qz4 qz154 qz696) Bool.true 295888580781 1099511627776 922881083539781 216972127067176960 Bool.true 41231459039 274877906944 460470169699583 108486063533588480

noncomputable def ep1009 := @Enclosure.Complex.IsNear.addLitP qz154 qz696 Bool.true 130506235681 1099511627776 884997260468203 216972127067176960 Bool.false 44267444217 1099511627776 883022521624473 216972127067176960 Bool.true

noncomputable abbrev qz164 := (@HMul.hMul Real Real Real qz269 qz439 qz600)

noncomputable def ep1010 := @Enclosure.Complex.IsNear.of_eq qz696 (Complex.mk (@HMul.hMul Real Real Real qz0 qz49 (Real.cos qz164)) (@HMul.hMul Real Real Real qz0 qz49 (@Neg.neg Real Real.instNeg (Real.sin qz164)))) Bool.true 41345586275 274877906944 18941911535789 108486063533588480 Bool.true 209193280373 1099511627776 37917817774693 216972127067176960 (BSN.cpow_neg_s_mk qz145 140505 1000 17 qz146 rfl)

noncomputable def ep1011 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz600 140505 1000 0 1 3189913004350711 1125899906842624 50000000039467 9866750000000000000 89639745335259329811 225179981368524800 1405050001109062167 1973350000000000000000 qz147 (BSN.isNear_log_sfrac 17 1 3189913004350711 1125899906842624 50000000039467 9866750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz601) Bool.false 53517859495200818200576 18889465931478580854784 1000000000789340 197335000000000000000 3189913004350711 1125899906842624 50000000039467 9866750000000000000 (BSN.log_rat_reduce_isNear 17 1 4 34 32 31784 524288 24973259072661432 36028797018963968 197335 1000000000000000 rfl rfl rfl rfl (ep298 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1012 := nat_lit 4259275323173888124999543292916121856

noncomputable def ep1013 := BSN.sin_dyadic_bound_f 1436593604 2147483648 2 1 1048576 395056 ep1012 ep58 ep1012 ep1012 ep59 ep1012 650300 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1436593604) qz15 0 1 ep1012 ep58 ep1012 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1436593604) qz16 0 1 ep1012 ep59 ep1012 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz456 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 52177199) qz553)

noncomputable def ep1014 := @Enclosure.Real.IsNear.cos_image qz164 qz456 Bool.false 52177199 131072 747 1048576 Bool.true 650300 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz164 Bool.false 89639745335259329811 225179981368524800 1405050001109062167 1973350000000000000000 52177199 131072 747 1048576 (ep1011 rfl) rfl) (Enclosure.sfrac_false_div 52177199 131072) (BSN.cos_reduce1 qz456 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 12636410984533745205248) qz305) 226375608064910080 72057594037927936 Bool.false 650300 1048576 63 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q1 52177199 131072 226375608064910080 72057594037927936 63 12636410984533745205248 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 650300 1048576 12636410984533745205248 18889465931478580854784 1436593604 2147483648 395056 394670 (ep1013 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1015 := nat_lit 152200551701721952008593181042812818366941430790502995346135728300410515030016

noncomputable def ep1016 := nat_lit 18141426278598029128576825347591453853366539608204080464478059159040884736

noncomputable def ep1017 := nat_lit 456565372252608659967522389477743272193117559292292577877478228782913463320576

noncomputable def ep1018 := BSN.cos_dyadic_bound_f 1436593604 2147483648 3 2 1048576 395056 ep1015 ep72 ep1016 ep1017 ep75 ep1016 822569 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1436593604) qz20 0 2 ep1015 ep72 ep1016 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1436593604) qz21 0 2 ep1017 ep75 ep1016 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1019 := @Enclosure.Real.IsNear.sin_image qz164 qz456 Bool.false 52177199 131072 747 1048576 Bool.false 822569 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz164 Bool.false 89639745335259329811 225179981368524800 1405050001109062167 1973350000000000000000 52177199 131072 747 1048576 (ep1011 rfl) rfl) (Enclosure.sfrac_false_div 52177199 131072) (BSN.sin_reduce1 qz456 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 12636410984533745205248) qz305) 226375608064910080 72057594037927936 Bool.false 822569 1048576 63 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q1 52177199 131072 226375608064910080 72057594037927936 63 12636410984533745205248 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 822569 1048576 12636410984533745205248 18889465931478580854784 1436593604 2147483648 395056 394670 (ep1018 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1020 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz49 (Real.cos qz164)) (@HMul.hMul Real Real Real qz0 qz49 (@Neg.neg Real Real.instNeg (Real.sin qz164))) Bool.true 41345586275 274877906944 18941911535789 108486063533588480 Bool.true 209193280373 1099511627776 37917817774693 216972127067176960 (@Enclosure.Real.IsNear.mulLit_ft qz49 (Real.cos qz164) 254317 1048576 1 1048576 162575 262144 148457821 206920744960 41345586275 274877906944 18941911535789 108486063533588480 qz343 (@Enclosure.Real.IsNear.recentre' (Real.cos qz164) Bool.true 650300 1048576 148457821 206920744960 162575 262144 148457821 206920744960 (ep1014 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz49 (@Neg.neg Real Real.instNeg (Real.sin qz164)) 254317 1048576 1 1048576 822569 1048576 148457821 206920744960 209193280373 1099511627776 37917817774693 216972127067176960 qz343 (@Enclosure.Real.IsNear.neg (Real.sin qz164) Bool.false 822569 1048576 148457821 206920744960 (@Enclosure.Real.IsNear.recentre' (Real.sin qz164) Bool.false 822569 1048576 148457821 206920744960 822569 1048576 148457821 206920744960 (ep1019 rfl rfl) rfl)) rfl)

noncomputable def ep1021 := @ep1009 41345586275 274877906944 18941911535789 108486063533588480 Bool.true 209193280373 1099511627776 37917817774693 216972127067176960 Bool.true 81333233773711944843264 295888580781 1099511627776 922881083539781 216972127067176960 Bool.true 181337874574201434669056 41231459039 274877906944 460470169699583 108486063533588480 EMRow48.d14 (ep1010 ep1020) rfl rfl

noncomputable abbrev qz165 := (@HMul.hMul Real Real Real qz269 qz439 qz603)

noncomputable def ep1022 := @Enclosure.Complex.IsNear.of_eq qz695 (Complex.mk (@HMul.hMul Real Real Real qz0 qz51 (Real.cos qz165)) (@HMul.hMul Real Real Real qz0 qz51 (@Neg.neg Real Real.instNeg (Real.sin qz165)))) Bool.true 171783538305 1099511627776 36877577794137 216972127067176960 Bool.false 48510551129 274877906944 9223837495393 54243031766794240 (BSN.cpow_neg_s_mk qz145 140505 1000 18 qz146 rfl)

noncomputable def ep1023 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz603 140505 1000 0 1 3254268794313975 1125899906842624 50000000039467 9866750000000000000 3657928295560680459 9007199254740992 1405050001109062167 1973350000000000000000 qz147 (BSN.isNear_log_sfrac 18 1 3254268794313975 1125899906842624 50000000039467 9866750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz604) Bool.false 54597570484265130393600 18889465931478580854784 1000000000789340 197335000000000000000 3254268794313975 1125899906842624 50000000039467 9866750000000000000 (BSN.log_rat_reduce_isNear 18 1 4 36 32 61752 524288 24973259072661432 36028797018963968 197335 1000000000000000 rfl rfl rfl rfl (ep313 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1024 := nat_lit 389680176139223068501802932826923287860842808047028376978417120530404912800000

noncomputable def ep1025 := nat_lit 118875984072351423998187379189704749114427869523756984477609654176100000000

noncomputable def ep1026 := nat_lit 1168802776449524502657412423722390454084299568402037616966296142282862538400000

noncomputable def ep1027 := BSN.cos_dyadic_bound_f 1817133210 2147483648 3 2 1048576 395056 ep1024 ep72 ep1025 ep1026 ep75 ep1025 695055 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1817133210) qz20 0 2 ep1024 ep72 ep1025 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1817133210) qz21 0 2 ep1026 ep75 ep1025 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz457 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 425838899) qz24)

noncomputable def ep1028 := @Enclosure.Real.IsNear.cos_image qz165 qz457 Bool.false 425838899 1048576 187 262144 Bool.true 695055 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz165 Bool.false 3657928295560680459 9007199254740992 1405050001109062167 1973350000000000000000 425838899 1048576 187 262144 (ep1023 rfl) rfl) (Enclosure.sfrac_false_div 425838899 1048576) (BSN.cos_reduce2 qz457 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 127869382014435787276288) qz25) 226375608064910080 72057594037927936 Bool.false 695055 1048576 64 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q2 425838899 1048576 226375608064910080 72057594037927936 64 127869382014435787276288 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 695055 1048576 127869382014435787276288 151115727451828646838272 1817133210 2147483648 395056 394670 (ep1027 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1029 := nat_lit 10903026372175361476882091666196810000

noncomputable def ep1030 := BSN.sin_dyadic_bound_f 1817133210 2147483648 2 1 1048576 395056 ep1029 ep58 ep1029 ep1029 ep59 ep1029 785116 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1817133210) qz15 0 1 ep1029 ep58 ep1029 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1817133210) qz16 0 1 ep1029 ep59 ep1029 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1031 := @Enclosure.Real.IsNear.sin_image qz165 qz457 Bool.false 425838899 1048576 187 262144 Bool.true 785116 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz165 Bool.false 3657928295560680459 9007199254740992 1405050001109062167 1973350000000000000000 425838899 1048576 187 262144 (ep1023 rfl) rfl) (Enclosure.sfrac_false_div 425838899 1048576) (BSN.sin_reduce2 qz457 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 127869382014435787276288) qz25) 226375608064910080 72057594037927936 Bool.false 785116 1048576 64 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q2 425838899 1048576 226375608064910080 72057594037927936 64 127869382014435787276288 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 785116 1048576 127869382014435787276288 151115727451828646838272 1817133210 2147483648 395056 394670 (ep1030 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1032 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz51 (Real.cos qz165)) (@HMul.hMul Real Real Real qz0 qz51 (@Neg.neg Real Real.instNeg (Real.sin qz165))) Bool.true 171783538305 1099511627776 36877577794137 216972127067176960 Bool.false 48510551129 274877906944 9223837495393 54243031766794240 (@Enclosure.Real.IsNear.mulLit_ft qz51 (Real.cos qz165) 247151 1048576 1 1048576 695055 1048576 37163789 51730186240 171783538305 1099511627776 36877577794137 216972127067176960 qz346 (@Enclosure.Real.IsNear.recentre' (Real.cos qz165) Bool.true 695055 1048576 37163789 51730186240 695055 1048576 37163789 51730186240 (ep1028 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz51 (@Neg.neg Real Real.instNeg (Real.sin qz165)) 247151 1048576 1 1048576 196279 262144 37163789 51730186240 48510551129 274877906944 9223837495393 54243031766794240 qz346 (@Enclosure.Real.IsNear.neg (Real.sin qz165) Bool.true 196279 262144 37163789 51730186240 (@Enclosure.Real.IsNear.recentre' (Real.sin qz165) Bool.true 785116 1048576 37163789 51730186240 196279 262144 37163789 51730186240 (ep1031 rfl rfl) rfl)) rfl)

noncomputable def ep1033 := @ep1007 171783538305 1099511627776 36877577794137 216972127067176960 Bool.false 48510551129 274877906944 9223837495393 54243031766794240 Bool.true 514210932921699177332736 233836059543 549755813888 479879330666959 108486063533588480 Bool.false 2000861598151826472960 3639546045 137438953472 478917844690369 108486063533588480 (ep1008 (BSN.head_sum_c_succ qz142 17 18 rfl rfl) (ep1021 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1022 ep1032) rfl rfl

noncomputable abbrev qz166 := (@HMul.hMul Real Real Real qz269 qz439 qz606)

noncomputable def ep1034 := @Enclosure.Complex.IsNear.of_eq qz694 (Complex.mk (@HMul.hMul Real Real Real qz0 qz53 (Real.cos qz166)) (@HMul.hMul Real Real Real qz0 qz53 (@Neg.neg Real Real.instNeg (Real.sin qz166)))) Bool.false 140120084643 1099511627776 7165591303711 43394425413435392 Bool.false 209746038249 1099511627776 7177014395389 43394425413435392 (BSN.cpow_neg_s_mk qz145 140505 1000 19 qz146 rfl)

noncomputable def ep1035 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz606 140505 1000 0 1 3315143513283831 1125899906842624 50000000039467 9866750000000000000 93158847866788934931 225179981368524800 1405050001109062167 1973350000000000000000 qz147 (BSN.isNear_log_sfrac 19 1 3315143513283831 1125899906842624 50000000039467 9866750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz607) Bool.false 55618878793361701994496 18889465931478580854784 1000000000789340 197335000000000000000 3315143513283831 1125899906842624 50000000039467 9866750000000000000 (BSN.log_rat_reduce_isNear 19 1 4 38 32 90099 524288 24973259072661432 36028797018963968 197335 1000000000000000 rfl rfl rfl rfl (ep328 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1036 := nat_lit 2558907153664869104918957692063471681

noncomputable def ep1037 := BSN.sin_dyadic_bound_f 1264776047 2147483648 2 1 1048576 395056 ep1036 ep58 ep1036 ep1036 ep59 ep1036 582477 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1264776047) qz15 0 1 ep1036 ep58 ep1036 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1264776047) qz16 0 1 ep1036 ep59 ep1036 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz458 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 216902345) qz17)

noncomputable def ep1038 := @Enclosure.Real.IsNear.cos_image qz166 qz458 Bool.false 216902345 524288 747 1048576 Bool.false 582477 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz166 Bool.false 93158847866788934931 225179981368524800 1405050001109062167 1973350000000000000000 216902345 524288 747 1048576 (ep1035 rfl) rfl) (Enclosure.sfrac_false_div 216902345 524288) (BSN.cos_reduce3 qz458 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 44500351070520024760320) qz19) 226375608064910080 72057594037927936 Bool.false 582477 1048576 65 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q3 216902345 524288 226375608064910080 72057594037927936 65 44500351070520024760320 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 582477 1048576 44500351070520024760320 75557863725914323419136 1264776047 2147483648 395056 394670 (ep1037 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1039 := BSN.cos_dyadic_bound_f 1264776047 2147483648 2 1 1048576 395056 ep1036 ep62 ep1036 ep1036 ep63 ep1036 871911 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1264776047) qz20 0 1 ep1036 ep62 ep1036 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1264776047) qz21 0 1 ep1036 ep63 ep1036 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1040 := @Enclosure.Real.IsNear.sin_image qz166 qz458 Bool.false 216902345 524288 747 1048576 Bool.true 871911 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz166 Bool.false 93158847866788934931 225179981368524800 1405050001109062167 1973350000000000000000 216902345 524288 747 1048576 (ep1035 rfl) rfl) (Enclosure.sfrac_false_div 216902345 524288) (BSN.sin_reduce3 qz458 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 44500351070520024760320) qz19) 226375608064910080 72057594037927936 Bool.false 871911 1048576 65 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q3 216902345 524288 226375608064910080 72057594037927936 65 44500351070520024760320 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 871911 1048576 44500351070520024760320 75557863725914323419136 1264776047 2147483648 395056 394670 (ep1039 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1041 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz53 (Real.cos qz166)) (@HMul.hMul Real Real Real qz0 qz53 (@Neg.neg Real Real.instNeg (Real.sin qz166))) Bool.false 140120084643 1099511627776 7165591303711 43394425413435392 Bool.false 209746038249 1099511627776 7177014395389 43394425413435392 (@Enclosure.Real.IsNear.mulLit_ff qz53 (Real.cos qz166) 240559 1048576 1 1048576 582477 1048576 148457821 206920744960 140120084643 1099511627776 7165591303711 43394425413435392 qz348 (@Enclosure.Real.IsNear.recentre' (Real.cos qz166) Bool.false 582477 1048576 148457821 206920744960 582477 1048576 148457821 206920744960 (ep1038 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz53 (@Neg.neg Real Real.instNeg (Real.sin qz166)) 240559 1048576 1 1048576 871911 1048576 148457821 206920744960 209746038249 1099511627776 7177014395389 43394425413435392 qz348 (@Enclosure.Real.IsNear.neg (Real.sin qz166) Bool.true 871911 1048576 148457821 206920744960 (@Enclosure.Real.IsNear.recentre' (Real.sin qz166) Bool.true 871911 1048576 148457821 206920744960 871911 1048576 148457821 206920744960 (ep1040 rfl rfl) rfl)) rfl)

noncomputable def ep1042 := @ep1005 140120084643 1099511627776 7165591303711 43394425413435392 Bool.false 209746038249 1099511627776 7177014395389 43394425413435392 Bool.true 180073635285881673744384 327552034443 1099511627776 995586617852473 216972127067176960 Bool.false 32828999188144296296448 238862406609 1099511627776 993720761357683 216972127067176960 (ep1006 (BSN.head_sum_c_succ qz142 18 19 rfl rfl) (ep1033 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1034 ep1041) rfl rfl

noncomputable abbrev qz167 := (@HMul.hMul Real Real Real qz269 qz439 qz609)

noncomputable def ep1043 := @Enclosure.Complex.IsNear.of_eq qz693 (Complex.mk (@HMul.hMul Real Real Real qz0 qz55 (Real.cos qz167)) (@HMul.hMul Real Real Real qz0 qz55 (@Neg.neg Real Real.instNeg (Real.sin qz167)))) Bool.false 245442383669 1099511627776 7003095153041 43394425413435392 Bool.false 7148256403 549755813888 435261719927 2712151588339712 (BSN.cpow_neg_s_mk qz145 140505 1000 20 qz146 rfl)

noncomputable def ep1044 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz609 140505 1000 0 1 3372893643545847 1125899906842624 50000000039467 9866750000000000000 94781684277281846547 225179981368524800 1405050001109062167 1973350000000000000000 qz147 (BSN.isNear_log_sfrac 20 1 3372893643545847 1125899906842624 50000000039467 9866750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz610) Bool.false 56587765202795681021952 18889465931478580854784 1000000000789340 197335000000000000000 3372893643545847 1125899906842624 50000000039467 9866750000000000000 (BSN.log_rat_reduce_isNear 20 1 4 40 32 116991 524288 24973259072661432 36028797018963968 197335 1000000000000000 rfl rfl rfl rfl (ep343 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1045 := nat_lit 7172716414542885200532000075562619334760889055225125007932691305465427593832385

noncomputable def ep1046 := nat_lit 12395455238755035770433249842068875244140714959142035934496714071102331070401

noncomputable def ep1047 := nat_lit 18765617015321000705384060650538748650168957796608145057834530167722906590685121

noncomputable def ep1048 := BSN.sin_dyadic_bound_f 3248312551 2147483648 3 2 1048576 395056 ep1045 ep79 ep1046 ep1047 ep81 ep1046 1046801 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3248312551) qz15 0 2 ep1045 ep79 ep1046 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3248312551) qz16 0 2 ep1047 ep81 ep1046 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz459 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 441361611) qz24)

noncomputable def ep1049 := @Enclosure.Real.IsNear.cos_image qz167 qz459 Bool.false 441361611 1048576 747 1048576 Bool.false 1046801 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz167 Bool.false 94781684277281846547 225179981368524800 1405050001109062167 1973350000000000000000 441361611 1048576 747 1048576 (ep1044 rfl) rfl) (Enclosure.sfrac_false_div 441361611 1048576) (BSN.cos_reduce3 qz459 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 228579674921340273426432) qz25) 226375608064910080 72057594037927936 Bool.false 1046801 1048576 66 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q3 441361611 1048576 226375608064910080 72057594037927936 66 228579674921340273426432 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1046801 1048576 228579674921340273426432 151115727451828646838272 3248312551 2147483648 395056 394670 (ep1048 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1050 := nat_lit 3990351543741049571749081486353485797197889792884688131489049264845727477049281

noncomputable def ep1051 := nat_lit 11946263720745638643706377959376319641105387948735780322598154366394977769007041

noncomputable def ep1052 := BSN.cos_dyadic_bound_f 3248312551 2147483648 3 2 1048576 395056 ep1050 ep72 ep1046 ep1051 ep75 ep1046 60974 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3248312551) qz20 0 2 ep1050 ep72 ep1046 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3248312551) qz21 0 2 ep1051 ep75 ep1046 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1053 := @Enclosure.Real.IsNear.sin_image qz167 qz459 Bool.false 441361611 1048576 747 1048576 Bool.true 60974 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz167 Bool.false 94781684277281846547 225179981368524800 1405050001109062167 1973350000000000000000 441361611 1048576 747 1048576 (ep1044 rfl) rfl) (Enclosure.sfrac_false_div 441361611 1048576) (BSN.sin_reduce3 qz459 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 228579674921340273426432) qz25) 226375608064910080 72057594037927936 Bool.false 60974 1048576 66 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q3 441361611 1048576 226375608064910080 72057594037927936 66 228579674921340273426432 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 60974 1048576 228579674921340273426432 151115727451828646838272 3248312551 2147483648 395056 394670 (ep1052 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1054 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz55 (Real.cos qz167)) (@HMul.hMul Real Real Real qz0 qz55 (@Neg.neg Real Real.instNeg (Real.sin qz167))) Bool.false 245442383669 1099511627776 7003095153041 43394425413435392 Bool.false 7148256403 549755813888 435261719927 2712151588339712 (@Enclosure.Real.IsNear.mulLit_ff qz55 (Real.cos qz167) 234469 1048576 1 1048576 1046801 1048576 148457821 206920744960 245442383669 1099511627776 7003095153041 43394425413435392 qz350 (@Enclosure.Real.IsNear.recentre' (Real.cos qz167) Bool.false 1046801 1048576 148457821 206920744960 1046801 1048576 148457821 206920744960 (ep1049 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz55 (@Neg.neg Real Real.instNeg (Real.sin qz167)) 234469 1048576 1 1048576 30487 524288 148457821 206920744960 7148256403 549755813888 435261719927 2712151588339712 qz350 (@Enclosure.Real.IsNear.neg (Real.sin qz167) Bool.true 30487 524288 148457821 206920744960 (@Enclosure.Real.IsNear.recentre' (Real.sin qz167) Bool.true 60974 1048576 148457821 206920744960 30487 524288 148457821 206920744960 (ep1053 rfl rfl) rfl)) rfl)

noncomputable def ep1055 := @ep1003 245442383669 1099511627776 7003095153041 43394425413435392 Bool.false 7148256403 549755813888 435261719927 2712151588339712 Bool.true 90280515778639638298624 41054825387 549755813888 515301046808839 108486063533588480 Bool.false 139175587785999929835520 253158919415 1099511627776 1028541698951843 216972127067176960 (ep1004 (BSN.head_sum_c_succ qz142 19 20 rfl rfl) (ep1042 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1043 ep1054) rfl rfl

noncomputable abbrev qz168 := (@HMul.hMul Real Real Real qz269 qz439 qz612)

noncomputable def ep1056 := @Enclosure.Complex.IsNear.of_eq qz692 (Complex.mk (@HMul.hMul Real Real Real qz0 qz57 (Real.cos qz168)) (@HMul.hMul Real Real Real qz0 qz57 (@Neg.neg Real Real.instNeg (Real.sin qz168)))) Bool.false 408096903 2147483648 429695831197 2712151588339712 Bool.true 58969258825 549755813888 3421869558067 21697212706717696 (BSN.cpow_neg_s_mk qz145 140505 1000 21 qz146 rfl)

noncomputable def ep1057 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz612 140505 1000 0 1 3427826275261687 1125899906842624 50000000039467 9866750000000000000 96325346161128666387 225179981368524800 1405050001109062167 1973350000000000000000 qz147 (BSN.isNear_log_sfrac 21 1 3427826275261687 1125899906842624 50000000039467 9866750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz613) Bool.false 57509381830540779323392 18889465931478580854784 1000000000789340 197335000000000000000 3427826275261687 1125899906842624 50000000039467 9866750000000000000 (BSN.log_rat_reduce_isNear 21 1 4 42 32 142571 524288 24973259072661432 36028797018963968 197335 1000000000000000 rfl rfl rfl rfl (ep354 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1058 := nat_lit 1482934389055506833244205680100000000

noncomputable def ep1059 := BSN.cos_dyadic_bound_f 1103520700 2147483648 2 1 1048576 395056 ep1058 ep62 ep1058 ep1058 ep63 ep1058 913152 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1103520700) qz20 0 1 ep1058 ep62 ep1058 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1103520700) qz21 0 1 ep1058 ep63 ep1058 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz460 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 224274923) qz17)

noncomputable def ep1060 := @Enclosure.Real.IsNear.cos_image qz168 qz460 Bool.false 224274923 524288 187 262144 Bool.false 913152 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz168 Bool.false 96325346161128666387 225179981368524800 1405050001109062167 1973350000000000000000 224274923 524288 187 262144 (ep1057 rfl) rfl) (Enclosure.sfrac_false_div 224274923 524288) (BSN.cos_reduce0 qz460 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 38826682934217173630976) qz19) 226375608064910080 72057594037927936 Bool.false 913152 1048576 68 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q0 224274923 524288 226375608064910080 72057594037927936 68 38826682934217173630976 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 913152 1048576 38826682934217173630976 75557863725914323419136 1103520700 2147483648 395056 394670 (ep1059 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1061 := BSN.sin_dyadic_bound_f 1103520700 2147483648 2 1 1048576 395056 ep1058 ep58 ep1058 ep1058 ep59 ep1058 515425 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1103520700) qz15 0 1 ep1058 ep58 ep1058 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1103520700) qz16 0 1 ep1058 ep59 ep1058 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1062 := @Enclosure.Real.IsNear.sin_image qz168 qz460 Bool.false 224274923 524288 187 262144 Bool.false 515425 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz168 Bool.false 96325346161128666387 225179981368524800 1405050001109062167 1973350000000000000000 224274923 524288 187 262144 (ep1057 rfl) rfl) (Enclosure.sfrac_false_div 224274923 524288) (BSN.sin_reduce0 qz460 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 38826682934217173630976) qz19) 226375608064910080 72057594037927936 Bool.false 515425 1048576 68 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q0 224274923 524288 226375608064910080 72057594037927936 68 38826682934217173630976 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 515425 1048576 38826682934217173630976 75557863725914323419136 1103520700 2147483648 395056 394670 (ep1061 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1063 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz57 (Real.cos qz168)) (@HMul.hMul Real Real Real qz0 qz57 (@Neg.neg Real Real.instNeg (Real.sin qz168))) Bool.false 408096903 2147483648 429695831197 2712151588339712 Bool.true 58969258825 549755813888 3421869558067 21697212706717696 (@Enclosure.Real.IsNear.mulLit_ff qz57 (Real.cos qz168) 114409 524288 1 524288 3567 4096 37163789 51730186240 408096903 2147483648 429695831197 2712151588339712 qz352 (@Enclosure.Real.IsNear.recentre' (Real.cos qz168) Bool.false 913152 1048576 37163789 51730186240 3567 4096 37163789 51730186240 (ep1060 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz57 (@Neg.neg Real Real.instNeg (Real.sin qz168)) 114409 524288 1 524288 515425 1048576 37163789 51730186240 58969258825 549755813888 3421869558067 21697212706717696 qz352 (@Enclosure.Real.IsNear.neg (Real.sin qz168) Bool.false 515425 1048576 37163789 51730186240 (@Enclosure.Real.IsNear.recentre' (Real.sin qz168) Bool.false 515425 1048576 37163789 51730186240 515425 1048576 37163789 51730186240 (ep1062 rfl rfl) rfl)) rfl)

noncomputable def ep1064 := @ep1001 408096903 2147483648 429695831197 2712151588339712 Bool.true 58969258825 549755813888 3421869558067 21697212706717696 Bool.false 136189078863859417088 63417981781 549755813888 532488880056719 108486063533588480 Bool.false 74338202026579926712320 135220401765 1099511627776 1062760394532513 216972127067176960 (ep1002 (BSN.head_sum_c_succ qz142 20 21 rfl rfl) (ep1055 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1056 ep1063) rfl rfl

noncomputable abbrev qz169 := (@HMul.hMul Real Real Real qz269 qz439 qz615)

noncomputable def ep1065 := @Enclosure.Complex.IsNear.of_eq qz691 (Complex.mk (@HMul.hMul Real Real Real qz0 qz59 (Real.cos qz169)) (@HMul.hMul Real Real Real qz0 qz59 (@Neg.neg Real Real.instNeg (Real.sin qz169)))) Bool.false 168777710505 1099511627776 33382030383323 216972127067176960 Bool.true 81340543779 549755813888 16688324430269 108486063533588480 (BSN.cpow_neg_s_mk qz145 140505 1000 22 qz146 rfl)

noncomputable def ep1066 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz615 140505 1000 0 1 3480203401436407 1125899906842624 50000000039467 9866750000000000000 97797195783764473107 225179981368524800 1405050001109062167 1973350000000000000000 qz147 (BSN.isNear_log_sfrac 22 1 3480203401436407 1125899906842624 50000000039467 9866750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz616) Bool.false 58388124189833310502912 18889465931478580854784 1000000000789340 197335000000000000000 3480203401436407 1125899906842624 50000000039467 9866750000000000000 (BSN.log_rat_reduce_isNear 22 1 4 44 32 166961 524288 24973259072661432 36028797018963968 197335 1000000000000000 rfl rfl rfl rfl (ep365 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1067 := nat_lit 263048006436721388238920449185204815924248074223745880309679657075486599126561

noncomputable def ep1068 := nat_lit 54179328978123948583171358581473117541198499062099066051974427283316776481

noncomputable def ep1069 := nat_lit 789035660652207916819595004838451501537661825673113442796935022371893163826721

noncomputable def ep1070 := BSN.cos_dyadic_bound_f 1647135027 2147483648 3 2 1048576 395056 ep1067 ep72 ep1068 ep1069 ep75 ep1068 754965 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1647135027) qz20 0 2 ep1067 ep72 ep1068 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1647135027) qz21 0 2 ep1069 ep75 ep1068 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz461 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14231365) (@Nat.cast Real Real.instNatCast 32768))

noncomputable def ep1071 := @Enclosure.Real.IsNear.cos_image qz169 qz461 Bool.false 14231365 32768 187 262144 Bool.false 754965 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz169 Bool.false 97797195783764473107 225179981368524800 1405050001109062167 1973350000000000000000 14231365 32768 187 262144 (ep1066 rfl) rfl) (Enclosure.sfrac_false_div 14231365 32768) (BSN.cos_reduce0 qz461 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3622088231563915427840) qz345) 226375608064910080 72057594037927936 Bool.false 754965 1048576 69 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q0 14231365 32768 226375608064910080 72057594037927936 69 3622088231563915427840 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 754965 1048576 3622088231563915427840 4722366482869645213696 1647135027 2147483648 395056 394670 (ep1070 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1072 := nat_lit 7360660906340133026843694958383351441

noncomputable def ep1073 := BSN.sin_dyadic_bound_f 1647135027 2147483648 2 1 1048576 395056 ep1072 ep58 ep1072 ep1072 ep59 ep1072 727694 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1647135027) qz15 0 1 ep1072 ep58 ep1072 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1647135027) qz16 0 1 ep1072 ep59 ep1072 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1074 := @Enclosure.Real.IsNear.sin_image qz169 qz461 Bool.false 14231365 32768 187 262144 Bool.false 727694 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz169 Bool.false 97797195783764473107 225179981368524800 1405050001109062167 1973350000000000000000 14231365 32768 187 262144 (ep1066 rfl) rfl) (Enclosure.sfrac_false_div 14231365 32768) (BSN.sin_reduce0 qz461 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3622088231563915427840) qz345) 226375608064910080 72057594037927936 Bool.false 727694 1048576 69 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q0 14231365 32768 226375608064910080 72057594037927936 69 3622088231563915427840 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 727694 1048576 3622088231563915427840 4722366482869645213696 1647135027 2147483648 395056 394670 (ep1073 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1075 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz59 (Real.cos qz169)) (@HMul.hMul Real Real Real qz0 qz59 (@Neg.neg Real Real.instNeg (Real.sin qz169))) Bool.false 168777710505 1099511627776 33382030383323 216972127067176960 Bool.true 81340543779 549755813888 16688324430269 108486063533588480 (@Enclosure.Real.IsNear.mulLit_ff qz59 (Real.cos qz169) 223557 1048576 1 1048576 754965 1048576 37163789 51730186240 168777710505 1099511627776 33382030383323 216972127067176960 qz354 (@Enclosure.Real.IsNear.recentre' (Real.cos qz169) Bool.false 754965 1048576 37163789 51730186240 754965 1048576 37163789 51730186240 (ep1071 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz59 (@Neg.neg Real Real.instNeg (Real.sin qz169)) 223557 1048576 1 1048576 363847 524288 37163789 51730186240 81340543779 549755813888 16688324430269 108486063533588480 qz354 (@Enclosure.Real.IsNear.neg (Real.sin qz169) Bool.false 363847 524288 37163789 51730186240 (@Enclosure.Real.IsNear.recentre' (Real.sin qz169) Bool.false 727694 1048576 37163789 51730186240 363847 524288 37163789 51730186240 (ep1074 rfl rfl) rfl)) rfl)

noncomputable def ep1076 := @ep999 168777710505 1099511627776 33382030383323 216972127067176960 Bool.true 81340543779 549755813888 16688324430269 108486063533588480 Bool.false 162515335983125544042496 295613674067 1099511627776 1098359790496761 216972127067176960 Bool.true 15096671668053353693184 27460685793 1099511627776 1096137043393051 216972127067176960 (ep1000 (BSN.head_sum_c_succ qz142 21 22 rfl rfl) (ep1064 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1065 ep1075) rfl rfl

noncomputable abbrev qz170 := (@HMul.hMul Real Real Real qz269 qz439 qz618)

noncomputable def ep1077 := @Enclosure.Complex.IsNear.of_eq qz690 (Complex.mk (@HMul.hMul Real Real Real qz0 qz61 (Real.cos qz170)) (@HMul.hMul Real Real Real qz0 qz61 (@Neg.neg Real Real.instNeg (Real.sin qz170)))) Bool.false 10683552909 68719476736 1020526125317 6780378970849280 Bool.true 152782262325 1099511627776 32640450693089 216972127067176960 (BSN.cpow_neg_s_mk qz145 140505 1000 23 qz146 rfl)

noncomputable def ep1078 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz618 140505 1000 0 1 3530250507853047 1125899906842624 50000000039467 9866750000000000000 99203569521178473747 225179981368524800 1405050001109062167 1973350000000000000000 qz147 (BSN.isNear_log_sfrac 23 1 3530250507853047 1125899906842624 50000000039467 9866750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz619) Bool.false 59227775304360265777152 18889465931478580854784 1000000000789340 197335000000000000000 3530250507853047 1125899906842624 50000000039467 9866750000000000000 (BSN.log_rat_reduce_isNear 23 1 4 46 32 190266 524288 24973259072661432 36028797018963968 197335 1000000000000000 rfl rfl rfl rfl (ep379 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1079 := nat_lit 215093098359888846170665982022919493632974564510473086813909535577025365830241

noncomputable def ep1080 := nat_lit 36228399906678075206828632676150818062382420096379700597019130341411940961

noncomputable def ep1081 := nat_lit 645206838279853182361584288803406179262798928691226501040534568470393273608801

noncomputable def ep1082 := BSN.cos_dyadic_bound_f 1566322347 2147483648 3 2 1048576 395056 ep1079 ep72 ep1080 ep1081 ep75 ep1080 781808 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1566322347) qz20 0 2 ep1079 ep72 ep1080 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1566322347) qz21 0 2 ep1081 ep75 ep1080 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz462 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 230976309) qz17)

noncomputable def ep1083 := @Enclosure.Real.IsNear.cos_image qz170 qz462 Bool.false 230976309 524288 187 262144 Bool.false 781808 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz170 Bool.false 99203569521178473747 225179981368524800 1405050001109062167 1973350000000000000000 230976309 524288 187 262144 (ep1078 rfl) rfl) (Enclosure.sfrac_false_div 230976309 524288) (BSN.cos_reduce0 qz462 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 55110068284040044085248) qz19) 226375608064910080 72057594037927936 Bool.false 781808 1048576 70 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q0 230976309 524288 226375608064910080 72057594037927936 70 55110068284040044085248 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 781808 1048576 55110068284040044085248 75557863725914323419136 1566322347 2147483648 395056 394670 (ep1082 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1084 := nat_lit 6019003231987674818283639755823151281

noncomputable def ep1085 := BSN.sin_dyadic_bound_f 1566322347 2147483648 2 1 1048576 395056 ep1084 ep58 ep1084 ep1084 ep59 ep1084 698775 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1566322347) qz15 0 1 ep1084 ep58 ep1084 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1566322347) qz16 0 1 ep1084 ep59 ep1084 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1086 := @Enclosure.Real.IsNear.sin_image qz170 qz462 Bool.false 230976309 524288 187 262144 Bool.false 698775 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz170 Bool.false 99203569521178473747 225179981368524800 1405050001109062167 1973350000000000000000 230976309 524288 187 262144 (ep1078 rfl) rfl) (Enclosure.sfrac_false_div 230976309 524288) (BSN.sin_reduce0 qz462 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 55110068284040044085248) qz19) 226375608064910080 72057594037927936 Bool.false 698775 1048576 70 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q0 230976309 524288 226375608064910080 72057594037927936 70 55110068284040044085248 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 698775 1048576 55110068284040044085248 75557863725914323419136 1566322347 2147483648 395056 394670 (ep1085 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1087 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz61 (Real.cos qz170)) (@HMul.hMul Real Real Real qz0 qz61 (@Neg.neg Real Real.instNeg (Real.sin qz170))) Bool.false 10683552909 68719476736 1020526125317 6780378970849280 Bool.true 152782262325 1099511627776 32640450693089 216972127067176960 (@Enclosure.Real.IsNear.mulLit_ff qz61 (Real.cos qz170) 218643 1048576 1 1048576 48863 65536 37163789 51730186240 10683552909 68719476736 1020526125317 6780378970849280 qz356 (@Enclosure.Real.IsNear.recentre' (Real.cos qz170) Bool.false 781808 1048576 37163789 51730186240 48863 65536 37163789 51730186240 (ep1083 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz61 (@Neg.neg Real Real.instNeg (Real.sin qz170)) 218643 1048576 1 1048576 698775 1048576 37163789 51730186240 152782262325 1099511627776 32640450693089 216972127067176960 qz356 (@Enclosure.Real.IsNear.neg (Real.sin qz170) Bool.false 698775 1048576 37163789 51730186240 (@Enclosure.Real.IsNear.recentre' (Real.sin qz170) Bool.false 698775 1048576 37163789 51730186240 698775 1048576 37163789 51730186240 (ep1086 rfl rfl) rfl)) rfl)

noncomputable def ep1088 := @ep997 10683552909 68719476736 1020526125317 6780378970849280 Bool.true 152782262325 1099511627776 32640450693089 216972127067176960 Bool.false 32061107647296303005696 466550520611 1099511627776 226203325301381 43394425413435392 Bool.true 198179217280367295725568 90121474059 549755813888 56438874704307 10848606353358848 (ep998 (BSN.head_sum_c_succ qz142 22 23 rfl rfl) (ep1076 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1077 ep1087) rfl rfl

noncomputable abbrev qz171 := (@HMul.hMul Real Real Real qz269 qz439 qz621)

noncomputable def ep1089 := @Enclosure.Complex.IsNear.of_eq qz689 (Complex.mk (@HMul.hMul Real Real Real qz0 qz63 (Real.cos qz171)) (@HMul.hMul Real Real Real qz0 qz63 (@Neg.neg Real Real.instNeg (Real.sin qz171)))) Bool.false 51090467183 274877906944 1598216254841 10848606353358848 Bool.true 46388886509 549755813888 3186144923061 21697212706717696 (BSN.cpow_neg_s_mk qz145 140505 1000 24 qz146 rfl)

noncomputable def ep1090 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz621 140505 1000 0 1 3578169457974519 1125899906842624 50000000039467 9866750000000000000 100550139938541958419 225179981368524800 1405050001109062167 1973350000000000000000 qz147 (BSN.isNear_log_sfrac 24 1 3578169457974519 1125899906842624 50000000039467 9866750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz622) Bool.false 60031721881041427759104 18889465931478580854784 1000000000789340 197335000000000000000 3578169457974519 1125899906842624 50000000039467 9866750000000000000 (BSN.log_rat_reduce_isNear 24 1 4 48 32 212580 524288 24973259072661432 36028797018963968 197335 1000000000000000 rfl rfl rfl rfl (ep393 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1091 := nat_lit 701505478720779687116265994336527376

noncomputable def ep1092 := BSN.cos_dyadic_bound_f 915182626 2147483648 2 1 1048576 395056 ep1091 ep62 ep1091 ep1091 ep63 ep1091 954788 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 915182626) qz20 0 1 ep1091 ep62 ep1091 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 915182626) qz21 0 1 ep1091 ep63 ep1091 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz463 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 117055769) qz31)

noncomputable def ep1093 := @Enclosure.Real.IsNear.cos_image qz171 qz463 Bool.false 117055769 262144 747 1048576 Bool.false 954788 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz171 Bool.false 100550139938541958419 225179981368524800 1405050001109062167 1973350000000000000000 117055769 262144 747 1048576 (ep1090 rfl) rfl) (Enclosure.sfrac_false_div 117055769 262144) (BSN.cos_reduce0 qz463 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16100063037687634853888) qz321) 226375608064910080 72057594037927936 Bool.false 954788 1048576 71 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q0 117055769 262144 226375608064910080 72057594037927936 71 16100063037687634853888 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 954788 1048576 16100063037687634853888 37778931862957161709568 915182626 2147483648 395056 394670 (ep1092 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1094 := BSN.sin_dyadic_bound_f 915182626 2147483648 2 1 1048576 395056 ep1091 ep58 ep1091 ep1091 ep59 ep1091 433462 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 915182626) qz15 0 1 ep1091 ep58 ep1091 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 915182626) qz16 0 1 ep1091 ep59 ep1091 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1095 := @Enclosure.Real.IsNear.sin_image qz171 qz463 Bool.false 117055769 262144 747 1048576 Bool.false 433462 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz171 Bool.false 100550139938541958419 225179981368524800 1405050001109062167 1973350000000000000000 117055769 262144 747 1048576 (ep1090 rfl) rfl) (Enclosure.sfrac_false_div 117055769 262144) (BSN.sin_reduce0 qz463 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16100063037687634853888) qz321) 226375608064910080 72057594037927936 Bool.false 433462 1048576 71 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q0 117055769 262144 226375608064910080 72057594037927936 71 16100063037687634853888 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 433462 1048576 16100063037687634853888 37778931862957161709568 915182626 2147483648 395056 394670 (ep1094 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1096 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz63 (Real.cos qz171)) (@HMul.hMul Real Real Real qz0 qz63 (@Neg.neg Real Real.instNeg (Real.sin qz171))) Bool.false 51090467183 274877906944 1598216254841 10848606353358848 Bool.true 46388886509 549755813888 3186144923061 21697212706717696 (@Enclosure.Real.IsNear.mulLit_ff qz63 (Real.cos qz171) 214039 1048576 1 1048576 238697 262144 148457821 206920744960 51090467183 274877906944 1598216254841 10848606353358848 qz358 (@Enclosure.Real.IsNear.recentre' (Real.cos qz171) Bool.false 954788 1048576 148457821 206920744960 238697 262144 148457821 206920744960 (ep1093 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz63 (@Neg.neg Real Real.instNeg (Real.sin qz171)) 214039 1048576 1 1048576 216731 524288 148457821 206920744960 46388886509 549755813888 3186144923061 21697212706717696 qz358 (@Enclosure.Real.IsNear.neg (Real.sin qz171) Bool.false 216731 524288 148457821 206920744960 (@Enclosure.Real.IsNear.recentre' (Real.sin qz171) Bool.false 433462 1048576 148457821 206920744960 216731 524288 148457821 206920744960 (ep1095 rfl rfl) rfl)) rfl)

noncomputable def ep1097 := @ep995 51090467183 274877906944 1598216254841 10848606353358848 Bool.true 46388886509 549755813888 3186144923061 21697212706717696 Bool.false 184418993325401851297792 670912389343 1099511627776 232596190320745 43394425413435392 Bool.true 75047364378205181968384 17063795071 68719476736 116063894331675 21697212706717696 (ep996 (BSN.head_sum_c_succ qz142 23 24 rfl rfl) (ep1088 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1089 ep1096) rfl rfl

theorem EMRow48.d15 : Enclosure.Complex.IsNear qz163 Bool.false 670912389343 1099511627776 232596190320745 43394425413435392 Bool.true 17063795071 68719476736 116063894331675 21697212706717696 := ep994 (BSN.head_sum_c_succ qz142 24 25 rfl rfl) (ep1097 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz172 := (BSN.headSumC qz437 33)

noncomputable abbrev qz697 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 32) qz143)

noncomputable def ep1098 := @Enclosure.Complex.IsNear.of_eq qz172 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz142 32) qz697) Bool.false 367559533959 549755813888 349534967361747 54243031766794240 Bool.false 17431680189 274877906944 348888342007097 54243031766794240

noncomputable def ep1099 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 32) qz697 Bool.false 232370545755 274877906944 685188819353307 108486063533588480 Bool.false 68490534909 1099511627776 1367996737664489 216972127067176960 Bool.true

noncomputable abbrev qz698 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 31) qz143)

noncomputable def ep1100 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 32) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz142 31) qz698) Bool.false 232370545755 274877906944 685188819353307 108486063533588480 Bool.false 68490534909 1099511627776 1367996737664489 216972127067176960

noncomputable def ep1101 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 31) qz698 Bool.false 219782635395 274877906944 671164326845767 108486063533588480 Bool.true 122459628113 1099511627776 1339800430626479 216972127067176960 Bool.false

noncomputable abbrev qz699 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 30) qz143)

noncomputable def ep1102 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 31) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz142 30) qz699) Bool.false 219782635395 274877906944 671164326845767 108486063533588480 Bool.true 122459628113 1099511627776 1339800430626479 216972127067176960

noncomputable def ep1103 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 30) qz699 Bool.false 345730824441 549755813888 65683803563423 10848606353358848 Bool.true 51200331767 1099511627776 262253568102569 43394425413435392 Bool.false

noncomputable abbrev qz700 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 29) qz143)

noncomputable def ep1104 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 30) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz142 29) qz700) Bool.false 345730824441 549755813888 65683803563423 10848606353358848 Bool.true 51200331767 1099511627776 262253568102569 43394425413435392

noncomputable def ep1105 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 29) qz700 Bool.false 754133592357 1099511627776 1284705442964849 216972127067176960 Bool.false 71558238029 549755813888 320540948997271 54243031766794240 Bool.true

noncomputable abbrev qz701 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 28) qz143)

noncomputable def ep1106 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 29) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz142 28) qz701) Bool.false 754133592357 1099511627776 1284705442964849 216972127067176960 Bool.false 71558238029 549755813888 320540948997271 54243031766794240

noncomputable def ep1107 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 28) qz701 Bool.false 961007837837 1099511627776 251016087495521 43394425413435392 Bool.false 15455176593 137438953472 125272540665931 21697212706717696 Bool.true

noncomputable abbrev qz702 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 27) qz143)

noncomputable def ep1108 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 28) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz142 27) qz702) Bool.false 961007837837 1099511627776 251016087495521 43394425413435392 Bool.false 15455176593 137438953472 125272540665931 21697212706717696

noncomputable def ep1109 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 27) qz702 Bool.false 512128950103 549755813888 61250998804521 10848606353358848 Bool.true 78285729621 1099511627776 244505867174157 43394425413435392 Bool.true

noncomputable abbrev qz703 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 26) qz143)

noncomputable def ep1110 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 27) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz142 26) qz703) Bool.false 512128950103 549755813888 61250998804521 10848606353358848 Bool.true 78285729621 1099511627776 244505867174157 43394425413435392

noncomputable def ep1111 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 26) qz703 Bool.false 111149307101 137438953472 597160164162323 108486063533588480 Bool.true 246378317821 1099511627776 1191797993341321 216972127067176960 Bool.false

noncomputable abbrev qz704 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 25) qz143)

noncomputable def ep1112 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 26) (@HAdd.hAdd Complex Complex Complex qz4 qz163 qz704) Bool.false 111149307101 137438953472 597160164162323 108486063533588480 Bool.true 246378317821 1099511627776 1191797993341321 216972127067176960

noncomputable def ep1113 := @Enclosure.Complex.IsNear.addLitP qz163 qz704 Bool.false 670912389343 1099511627776 232596190320745 43394425413435392 Bool.true 17063795071 68719476736 116063894331675 21697212706717696 Bool.false

noncomputable abbrev qz173 := (@HMul.hMul Real Real Real qz269 qz439 qz633)

noncomputable def ep1114 := @Enclosure.Complex.IsNear.of_eq qz704 (Complex.mk (@HMul.hMul Real Real Real qz0 qz66 (Real.cos qz173)) (@HMul.hMul Real Real Real qz0 qz66 (@Neg.neg Real Real.instNeg (Real.sin qz173)))) Bool.false 218282067465 1099511627776 31339376720921 216972127067176960 Bool.false 26642403315 1099511627776 31159050024571 216972127067176960 (BSN.cpow_neg_s_mk qz145 140505 1000 25 qz146 rfl)

noncomputable def ep1115 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz633 140505 1000 0 1 3624129903009015 1125899906842624 50000000039467 9866750000000000000 20368334880891266103 45035996273704960 1405050001109062167 1973350000000000000000 qz147 (BSN.isNear_log_sfrac 25 1 3624129903009015 1125899906842624 50000000039467 9866750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz634) Bool.false 60802810194841294602240 18889465931478580854784 1000000000789340 197335000000000000000 3624129903009015 1125899906842624 50000000039467 9866750000000000000 (BSN.log_rat_reduce_isNear 25 1 4 50 32 233982 524288 24973259072661432 36028797018963968 197335 1000000000000000 rfl rfl rfl rfl (ep421 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1116 := nat_lit 6044169758001053161852265203409059492914460437164013623744757951062300168355840

noncomputable def ep1117 := nat_lit 8806520047638094490213897043884464743768799987245993766669712538799072935936

noncomputable def ep1118 := nat_lit 15815710238497058509009872080381247633762246897354970738947377003909873370464256

noncomputable def ep1119 := BSN.sin_dyadic_bound_f 3112436796 2147483648 3 2 1048576 395056 ep1116 ep79 ep1117 ep1118 ep81 ep1117 1040851 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3112436796) qz15 0 2 ep1116 ep79 ep1117 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3112436796) qz16 0 2 ep1118 ep81 ep1117 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz464 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 118559313) qz31)

noncomputable def ep1120 := @Enclosure.Real.IsNear.cos_image qz173 qz464 Bool.false 118559313 262144 747 1048576 Bool.false 1040851 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz173 Bool.false 20368334880891266103 45035996273704960 1405050001109062167 1973350000000000000000 118559313 262144 747 1048576 (ep1115 rfl) rfl) (Enclosure.sfrac_false_div 118559313 262144) (BSN.cos_reduce3 qz464 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 54754567176308912029696) qz321) 226375608064910080 72057594037927936 Bool.false 1040851 1048576 71 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q3 118559313 262144 226375608064910080 72057594037927936 71 54754567176308912029696 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1040851 1048576 54754567176308912029696 37778931862957161709568 3112436796 2147483648 395056 394670 (ep1119 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1121 := nat_lit 3361786096688424243024686845024537258171930820641005788198940956162966348169216

noncomputable def ep1122 := nat_lit 10067745249969996540093632740985842845028254861948525377063483443411300898635776

noncomputable def ep1123 := BSN.cos_dyadic_bound_f 3112436796 2147483648 3 2 1048576 395056 ep1121 ep72 ep1117 ep1122 ep75 ep1117 127041 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3112436796) qz20 0 2 ep1121 ep72 ep1117 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3112436796) qz21 0 2 ep1122 ep75 ep1117 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1124 := @Enclosure.Real.IsNear.sin_image qz173 qz464 Bool.false 118559313 262144 747 1048576 Bool.true 127041 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz173 Bool.false 20368334880891266103 45035996273704960 1405050001109062167 1973350000000000000000 118559313 262144 747 1048576 (ep1115 rfl) rfl) (Enclosure.sfrac_false_div 118559313 262144) (BSN.sin_reduce3 qz464 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 54754567176308912029696) qz321) 226375608064910080 72057594037927936 Bool.false 127041 1048576 71 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q3 118559313 262144 226375608064910080 72057594037927936 71 54754567176308912029696 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 127041 1048576 54754567176308912029696 37778931862957161709568 3112436796 2147483648 395056 394670 (ep1123 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1125 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz66 (Real.cos qz173)) (@HMul.hMul Real Real Real qz0 qz66 (@Neg.neg Real Real.instNeg (Real.sin qz173))) Bool.false 218282067465 1099511627776 31339376720921 216972127067176960 Bool.false 26642403315 1099511627776 31159050024571 216972127067176960 (@Enclosure.Real.IsNear.mulLit_ff qz66 (Real.cos qz173) 209715 1048576 1 1048576 1040851 1048576 148457821 206920744960 218282067465 1099511627776 31339376720921 216972127067176960 qz360 (@Enclosure.Real.IsNear.recentre' (Real.cos qz173) Bool.false 1040851 1048576 148457821 206920744960 1040851 1048576 148457821 206920744960 (ep1120 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz66 (@Neg.neg Real Real.instNeg (Real.sin qz173)) 209715 1048576 1 1048576 127041 1048576 148457821 206920744960 26642403315 1099511627776 31159050024571 216972127067176960 qz360 (@Enclosure.Real.IsNear.neg (Real.sin qz173) Bool.true 127041 1048576 148457821 206920744960 (@Enclosure.Real.IsNear.recentre' (Real.sin qz173) Bool.true 127041 1048576 148457821 206920744960 127041 1048576 148457821 206920744960 (ep1124 rfl rfl) rfl)) rfl)

noncomputable def ep1126 := @ep1113 218282067465 1099511627776 31339376720921 216972127067176960 Bool.false 26642403315 1099511627776 31159050024571 216972127067176960 Bool.false 977679644614360205099008 111149307101 137438953472 597160164162323 108486063533588480 Bool.true 16930989079755023712256 246378317821 1099511627776 1191797993341321 216972127067176960 EMRow48.d15 (ep1114 ep1125) rfl rfl

noncomputable abbrev qz174 := (@HMul.hMul Real Real Real qz269 qz439 qz636)

noncomputable def ep1127 := @Enclosure.Complex.IsNear.of_eq qz703 (Complex.mk (@HMul.hMul Real Real Real qz0 qz68 (Real.cos qz174)) (@HMul.hMul Real Real Real qz0 qz68 (@Neg.neg Real Real.instNeg (Real.sin qz174)))) Bool.false 67531721699 549755813888 15349823882887 108486063533588480 Bool.false 21011573525 137438953472 3841417816183 27121515883397120 (BSN.cpow_neg_s_mk qz145 140505 1000 26 qz146 rfl)

noncomputable def ep1128 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz636 140505 1000 0 1 3668288609262839 1125899906842624 50000000039467 9866750000000000000 103082578208895038739 225179981368524800 1405050001109062167 1973350000000000000000 qz147 (BSN.isNear_log_sfrac 26 1 3668288609262839 1125899906842624 50000000039467 9866750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz637) Bool.false 61543670347942250676224 18889465931478580854784 1000000000789340 197335000000000000000 3668288609262839 1125899906842624 50000000039467 9866750000000000000 (BSN.log_rat_reduce_isNear 26 1 4 52 32 254545 524288 24973259072661432 36028797018963968 197335 1000000000000000 rfl rfl rfl rfl (ep436 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1129 := nat_lit 4464308239790529127404603548117176576

noncomputable def ep1130 := BSN.sin_dyadic_bound_f 1453578676 2147483648 2 1 1048576 395056 ep1129 ep58 ep1129 ep1129 ep59 ep1129 656786 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1453578676) qz15 0 1 ep1129 ep58 ep1129 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1453578676) qz16 0 1 ep1129 ep59 ep1129 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz465 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 120003915) qz31)

noncomputable def ep1131 := @Enclosure.Real.IsNear.cos_image qz174 qz465 Bool.false 120003915 262144 187 262144 Bool.false 656786 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz174 Bool.false 103082578208895038739 225179981368524800 1405050001109062167 1973350000000000000000 120003915 262144 187 262144 (ep1128 rfl) rfl) (Enclosure.sfrac_false_div 120003915 262144) (BSN.cos_reduce3 qz465 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 25571626498795304386560) qz321) 226375608064910080 72057594037927936 Bool.false 656786 1048576 72 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q3 120003915 262144 226375608064910080 72057594037927936 72 25571626498795304386560 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 656786 1048576 25571626498795304386560 37778931862957161709568 1453578676 2147483648 395056 394670 (ep1130 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1132 := nat_lit 159528094370619687110211175313358850789304957045984124590640410759512058822656

noncomputable def ep1133 := nat_lit 19930048059861612514908640914051372559821271543809266724797913645963083776

noncomputable def ep1134 := nat_lit 478544423015739338105603708658248449622795228594864755238471636451244250300416

noncomputable def ep1135 := BSN.cos_dyadic_bound_f 1453578676 2147483648 3 2 1048576 395056 ep1132 ep72 ep1133 ep1134 ep75 ep1133 817400 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1453578676) qz20 0 2 ep1132 ep72 ep1133 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1453578676) qz21 0 2 ep1134 ep75 ep1133 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1136 := @Enclosure.Real.IsNear.sin_image qz174 qz465 Bool.false 120003915 262144 187 262144 Bool.true 817400 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz174 Bool.false 103082578208895038739 225179981368524800 1405050001109062167 1973350000000000000000 120003915 262144 187 262144 (ep1128 rfl) rfl) (Enclosure.sfrac_false_div 120003915 262144) (BSN.sin_reduce3 qz465 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 25571626498795304386560) qz321) 226375608064910080 72057594037927936 Bool.false 817400 1048576 72 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q3 120003915 262144 226375608064910080 72057594037927936 72 25571626498795304386560 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 817400 1048576 25571626498795304386560 37778931862957161709568 1453578676 2147483648 395056 394670 (ep1135 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1137 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz68 (Real.cos qz174)) (@HMul.hMul Real Real Real qz0 qz68 (@Neg.neg Real Real.instNeg (Real.sin qz174))) Bool.false 67531721699 549755813888 15349823882887 108486063533588480 Bool.false 21011573525 137438953472 3841417816183 27121515883397120 (@Enclosure.Real.IsNear.mulLit_ff qz68 (Real.cos qz174) 205643 1048576 1 1048576 328393 524288 37163789 51730186240 67531721699 549755813888 15349823882887 108486063533588480 qz362 (@Enclosure.Real.IsNear.recentre' (Real.cos qz174) Bool.false 656786 1048576 37163789 51730186240 328393 524288 37163789 51730186240 (ep1131 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz68 (@Neg.neg Real Real.instNeg (Real.sin qz174)) 205643 1048576 1 1048576 102175 131072 37163789 51730186240 21011573525 137438953472 3841417816183 27121515883397120 qz362 (@Enclosure.Real.IsNear.neg (Real.sin qz174) Bool.true 102175 131072 37163789 51730186240 (@Enclosure.Real.IsNear.recentre' (Real.sin qz174) Bool.true 817400 1048576 37163789 51730186240 102175 131072 37163789 51730186240 (ep1136 rfl rfl) rfl)) rfl)

noncomputable def ep1138 := @ep1111 67531721699 549755813888 15349823882887 108486063533588480 Bool.false 21011573525 137438953472 3841417816183 27121515883397120 Bool.false 70386466944870426607616 512128950103 549755813888 61250998804521 10848606353358848 Bool.true 10759508750902191194112 78285729621 1099511627776 244505867174157 43394425413435392 (ep1112 (BSN.head_sum_c_succ qz142 25 26 rfl rfl) (ep1126 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1127 ep1137) rfl rfl

noncomputable abbrev qz175 := (@HMul.hMul Real Real Real qz269 qz439 qz639)

noncomputable def ep1139 := @Enclosure.Complex.IsNear.of_eq qz702 (Complex.mk (@HMul.hMul Real Real Real qz0 qz70 (Real.cos qz175)) (@HMul.hMul Real Real Real qz0 qz70 (@Neg.neg Real Real.instNeg (Real.sin qz175)))) Bool.true 63250062369 1099511627776 6012092277437 43394425413435392 Bool.false 201927142365 1099511627776 6039214157705 43394425413435392 (BSN.cpow_neg_s_mk qz145 140505 1000 27 qz146 rfl)

noncomputable def ep1140 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz639 140505 1000 0 1 3710780868205815 1125899906842624 50000000039467 9866750000000000000 20855330635490321463 45035996273704960 1405050001109062167 1973350000000000000000 qz147 (BSN.isNear_log_sfrac 27 1 3710780868205815 1125899906842624 50000000039467 9866750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz640) Bool.false 62256572154556490711040 18889465931478580854784 1000000000789340 197335000000000000000 3710780868205815 1125899906842624 50000000039467 9866750000000000000 (BSN.log_rat_reduce_isNear 27 1 4 54 32 274332 524288 24973259072661432 36028797018963968 197335 1000000000000000 rfl rfl rfl rfl (ep447 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1141 := nat_lit 1962709876044456214007412570768098239930428587868629641661055236075890725672481

noncomputable def ep1142 := nat_lit 3008308645674313869031611515833893006933474806399987504105607489154105005601

noncomputable def ep1143 := nat_lit 5882113010842020014284174489272626933777418813993088949974954493249363967006241

noncomputable def ep1144 := BSN.cos_dyadic_bound_f 2721386957 2147483648 3 2 1048576 395056 ep1141 ep72 ep1142 ep1143 ep75 ep1142 313431 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2721386957) qz20 0 2 ep1141 ep72 ep1142 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2721386957) qz21 0 2 ep1143 ep75 ep1142 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz466 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 485576005) qz24)

noncomputable def ep1145 := @Enclosure.Real.IsNear.cos_image qz175 qz466 Bool.false 485576005 1048576 187 262144 Bool.true 313431 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz175 Bool.false 20855330635490321463 45035996273704960 1405050001109062167 1973350000000000000000 485576005 1048576 187 262144 (ep1140 rfl) rfl) (Enclosure.sfrac_false_div 485576005 1048576) (BSN.cos_reduce2 qz466 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 191500582630012580003840) qz25) 226375608064910080 72057594037927936 Bool.false 313431 1048576 73 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q2 485576005 1048576 226375608064910080 72057594037927936 73 191500582630012580003840 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 313431 1048576 191500582630012580003840 151115727451828646838272 2721386957 2147483648 395056 394670 (ep1144 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1146 := nat_lit 3530471129963481734118117338169909717469224678318413364986614938945280022205985

noncomputable def ep1147 := nat_lit 9241601412097074700235684705133651528503410436385482642815439570826626745292321

noncomputable def ep1148 := BSN.sin_dyadic_bound_f 2721386957 2147483648 3 2 1048576 395056 ep1146 ep79 ep1142 ep1147 ep81 ep1142 1000635 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2721386957) qz15 0 2 ep1146 ep79 ep1142 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2721386957) qz16 0 2 ep1147 ep81 ep1142 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1149 := @Enclosure.Real.IsNear.sin_image qz175 qz466 Bool.false 485576005 1048576 187 262144 Bool.true 1000635 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz175 Bool.false 20855330635490321463 45035996273704960 1405050001109062167 1973350000000000000000 485576005 1048576 187 262144 (ep1140 rfl) rfl) (Enclosure.sfrac_false_div 485576005 1048576) (BSN.sin_reduce2 qz466 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 191500582630012580003840) qz25) 226375608064910080 72057594037927936 Bool.false 1000635 1048576 73 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q2 485576005 1048576 226375608064910080 72057594037927936 73 191500582630012580003840 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1000635 1048576 191500582630012580003840 151115727451828646838272 2721386957 2147483648 395056 394670 (ep1148 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1150 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz70 (Real.cos qz175)) (@HMul.hMul Real Real Real qz0 qz70 (@Neg.neg Real Real.instNeg (Real.sin qz175))) Bool.true 63250062369 1099511627776 6012092277437 43394425413435392 Bool.false 201927142365 1099511627776 6039214157705 43394425413435392 (@Enclosure.Real.IsNear.mulLit_ft qz70 (Real.cos qz175) 201799 1048576 1 1048576 313431 1048576 37163789 51730186240 63250062369 1099511627776 6012092277437 43394425413435392 qz364 (@Enclosure.Real.IsNear.recentre' (Real.cos qz175) Bool.true 313431 1048576 37163789 51730186240 313431 1048576 37163789 51730186240 (ep1145 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz70 (@Neg.neg Real Real.instNeg (Real.sin qz175)) 201799 1048576 1 1048576 1000635 1048576 37163789 51730186240 201927142365 1099511627776 6039214157705 43394425413435392 qz364 (@Enclosure.Real.IsNear.neg (Real.sin qz175) Bool.true 1000635 1048576 37163789 51730186240 (@Enclosure.Real.IsNear.recentre' (Real.sin qz175) Bool.true 1000635 1048576 37163789 51730186240 1000635 1048576 37163789 51730186240 (ep1149 rfl rfl) rfl)) rfl)

noncomputable def ep1151 := @ep1109 63250062369 1099511627776 6012092277437 43394425413435392 Bool.false 201927142365 1099511627776 6039214157705 43394425413435392 Bool.false 528319646042827056480256 961007837837 1099511627776 251016087495521 43394425413435392 Bool.false 135945170986679710777344 15455176593 137438953472 125272540665931 21697212706717696 (ep1110 (BSN.head_sum_c_succ qz142 26 27 rfl rfl) (ep1138 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1139 ep1150) rfl rfl

noncomputable abbrev qz176 := (@HMul.hMul Real Real Real qz269 qz439 qz642)

noncomputable def ep1152 := @Enclosure.Complex.IsNear.of_eq qz701 (Complex.mk (@HMul.hMul Real Real Real qz0 qz72 (Real.cos qz176)) (@HMul.hMul Real Real Real qz0 qz72 (@Neg.neg Real Real.instNeg (Real.sin qz176)))) Bool.true 25859280685 137438953472 7406251371811 54243031766794240 Bool.false 9737531657 549755813888 14719194664887 108486063533588480 (BSN.cpow_neg_s_mk qz145 140505 1000 28 qz146 rfl)

noncomputable def ep1153 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz642 140505 1000 0 1 3751726938922231 1125899906842624 50000000039467 9866750000000000000 105427278710653613331 225179981368524800 1405050001109062167 1973350000000000000000 qz147 (BSN.isNear_log_sfrac 28 1 3751726938922231 1125899906842624 50000000039467 9866750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz643) Bool.false 62943533227317076688896 18889465931478580854784 1000000000789340 197335000000000000000 3751726938922231 1125899906842624 50000000039467 9866750000000000000 (BSN.log_rat_reduce_isNear 28 1 4 56 32 293399 524288 24973259072661432 36028797018963968 197335 1000000000000000 rfl rfl rfl rfl (ep462 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1154 := nat_lit 1650838510858624183819445317028721

noncomputable def ep1155 := BSN.cos_dyadic_bound_f 201570117 2147483648 2 1 1048576 395056 ep1154 ep62 ep1154 ep1154 ep63 ep1154 1043960 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 201570117) qz20 0 1 ep1154 ep62 ep1154 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 201570117) qz21 0 1 ep1154 ep63 ep1154 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz467 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 490934023) qz24)

noncomputable def ep1156 := @Enclosure.Real.IsNear.cos_image qz176 qz467 Bool.false 490934023 1048576 747 1048576 Bool.true 1043960 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz176 Bool.false 105427278710653613331 225179981368524800 1405050001109062167 1973350000000000000000 490934023 1048576 747 1048576 (ep1153 rfl) rfl) (Enclosure.sfrac_false_div 490934023 1048576) (BSN.cos_reduce2 qz467 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14184236004749099401216) qz25) 226375608064910080 72057594037927936 Bool.false 1043960 1048576 74 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q2 490934023 1048576 226375608064910080 72057594037927936 74 14184236004749099401216 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1043960 1048576 14184236004749099401216 151115727451828646838272 201570117 2147483648 395056 394670 (ep1155 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1157 := BSN.sin_dyadic_bound_f 201570117 2147483648 1 0 1048576 395056 0 1 1 0 1 1 98278 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 201570117) qz15 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 201570117) qz16 0 0 rfl) rfl rfl

noncomputable def ep1158 := @Enclosure.Real.IsNear.sin_image qz176 qz467 Bool.false 490934023 1048576 747 1048576 Bool.true 98278 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz176 Bool.false 105427278710653613331 225179981368524800 1405050001109062167 1973350000000000000000 490934023 1048576 747 1048576 (ep1153 rfl) rfl) (Enclosure.sfrac_false_div 490934023 1048576) (BSN.sin_reduce2 qz467 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14184236004749099401216) qz25) 226375608064910080 72057594037927936 Bool.false 98278 1048576 74 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q2 490934023 1048576 226375608064910080 72057594037927936 74 14184236004749099401216 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 98278 1048576 14184236004749099401216 151115727451828646838272 201570117 2147483648 395056 394670 (ep1157 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1159 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz72 (Real.cos qz176)) (@HMul.hMul Real Real Real qz0 qz72 (@Neg.neg Real Real.instNeg (Real.sin qz176))) Bool.true 25859280685 137438953472 7406251371811 54243031766794240 Bool.false 9737531657 549755813888 14719194664887 108486063533588480 (@Enclosure.Real.IsNear.mulLit_ft qz72 (Real.cos qz176) 198163 1048576 1 1048576 130495 131072 148457821 206920744960 25859280685 137438953472 7406251371811 54243031766794240 qz366 (@Enclosure.Real.IsNear.recentre' (Real.cos qz176) Bool.true 1043960 1048576 148457821 206920744960 130495 131072 148457821 206920744960 (ep1156 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz72 (@Neg.neg Real Real.instNeg (Real.sin qz176)) 198163 1048576 1 1048576 49139 524288 148457821 206920744960 9737531657 549755813888 14719194664887 108486063533588480 qz366 (@Enclosure.Real.IsNear.neg (Real.sin qz176) Bool.true 49139 524288 148457821 206920744960 (@Enclosure.Real.IsNear.recentre' (Real.sin qz176) Bool.true 98278 1048576 148457821 206920744960 49139 524288 148457821 206920744960 (ep1158 rfl rfl) rfl)) rfl)

noncomputable def ep1160 := @ep1107 25859280685 137438953472 7406251371811 54243031766794240 Bool.false 9737531657 549755813888 14719194664887 108486063533588480 Bool.false 103647331711625937813504 754133592357 1099511627776 1284705442964849 216972127067176960 Bool.false 9834889347006031986688 71558238029 549755813888 320540948997271 54243031766794240 (ep1108 (BSN.head_sum_c_succ qz142 27 28 rfl rfl) (ep1151 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1152 ep1159) rfl rfl

noncomputable abbrev qz177 := (@HMul.hMul Real Real Real qz269 qz439 qz644)

noncomputable def ep1161 := @Enclosure.Complex.IsNear.of_eq qz700 (Complex.mk (@HMul.hMul Real Real Real qz0 qz367 (Real.cos qz177)) (@HMul.hMul Real Real Real qz0 qz367 (@Neg.neg Real Real.instNeg (Real.sin qz177)))) Bool.true 62671943475 1099511627776 28970628303611 216972127067176960 Bool.true 194316807825 1099511627776 29104044523761 216972127067176960 (BSN.cpow_neg_s_mk qz145 140505 1000 29 qz146 rfl)

noncomputable def ep1162 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz644 140505 1000 0 1 3791236343078135 1125899906842624 50000000039467 9866750000000000000 21307506495367734327 45035996273704960 1405050001109062167 1973350000000000000000 qz147 (BSN.isNear_log_sfrac 29 1 3791236343078135 1125899906842624 50000000039467 9866750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz645) Bool.false 63606391034871975772160 18889465931478580854784 1000000000789340 197335000000000000000 3791236343078135 1125899906842624 50000000039467 9866750000000000000 (BSN.log_rat_reduce_isNear 29 1 4 58 32 311797 524288 24973259072661432 36028797018963968 197335 1000000000000000 rfl rfl rfl rfl (ep477 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1163 := nat_lit 201507473346471785138128826282439696

noncomputable def ep1164 := BSN.sin_dyadic_bound_f 669996894 2147483648 2 1 1048576 395056 ep1163 ep58 ep1163 ep1163 ep59 ep1163 321865 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 669996894) qz15 0 1 ep1163 ep58 ep1163 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 669996894) qz16 0 1 ep1163 ep59 ep1163 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz468 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 496104045) qz24)

noncomputable def ep1165 := @Enclosure.Real.IsNear.cos_image qz177 qz468 Bool.false 496104045 1048576 747 1048576 Bool.true 321865 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz177 Bool.false 21307506495367734327 45035996273704960 1405050001109062167 1973350000000000000000 496104045 1048576 747 1048576 (ep1162 rfl) rfl) (Enclosure.sfrac_false_div 496104045 1048576) (BSN.cos_reduce1 qz468 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 47146840084248170332160) qz25) 226375608064910080 72057594037927936 Bool.false 321865 1048576 75 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q1 496104045 1048576 226375608064910080 72057594037927936 75 47146840084248170332160 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 321865 1048576 47146840084248170332160 151115727451828646838272 669996894 2147483648 395056 394670 (ep1164 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1166 := BSN.cos_dyadic_bound_f 669996894 2147483648 2 1 1048576 395056 ep1163 ep62 ep1163 ep1163 ep63 ep1163 997955 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 669996894) qz20 0 1 ep1163 ep62 ep1163 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 669996894) qz21 0 1 ep1163 ep63 ep1163 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1167 := @Enclosure.Real.IsNear.sin_image qz177 qz468 Bool.false 496104045 1048576 747 1048576 Bool.false 997955 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz177 Bool.false 21307506495367734327 45035996273704960 1405050001109062167 1973350000000000000000 496104045 1048576 747 1048576 (ep1162 rfl) rfl) (Enclosure.sfrac_false_div 496104045 1048576) (BSN.sin_reduce1 qz468 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 47146840084248170332160) qz25) 226375608064910080 72057594037927936 Bool.false 997955 1048576 75 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q1 496104045 1048576 226375608064910080 72057594037927936 75 47146840084248170332160 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 997955 1048576 47146840084248170332160 151115727451828646838272 669996894 2147483648 395056 394670 (ep1166 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1168 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz367 (Real.cos qz177)) (@HMul.hMul Real Real Real qz0 qz367 (@Neg.neg Real Real.instNeg (Real.sin qz177))) Bool.true 62671943475 1099511627776 28970628303611 216972127067176960 Bool.true 194316807825 1099511627776 29104044523761 216972127067176960 (@Enclosure.Real.IsNear.mulLit_ft qz367 (Real.cos qz177) 194715 1048576 1 1048576 321865 1048576 148457821 206920744960 62671943475 1099511627776 28970628303611 216972127067176960 qz371 (@Enclosure.Real.IsNear.recentre' (Real.cos qz177) Bool.true 321865 1048576 148457821 206920744960 321865 1048576 148457821 206920744960 (ep1165 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz367 (@Neg.neg Real Real.instNeg (Real.sin qz177)) 194715 1048576 1 1048576 997955 1048576 148457821 206920744960 194316807825 1099511627776 29104044523761 216972127067176960 qz371 (@Enclosure.Real.IsNear.neg (Real.sin qz177) Bool.false 997955 1048576 148457821 206920744960 (@Enclosure.Real.IsNear.recentre' (Real.sin qz177) Bool.false 997955 1048576 148457821 206920744960 997955 1048576 148457821 206920744960 (ep1167 rfl rfl) rfl)) rfl)

noncomputable def ep1169 := @ep1105 62671943475 1099511627776 28970628303611 216972127067176960 Bool.true 194316807825 1099511627776 29104044523761 216972127067176960 Bool.false 760270123106924790546432 345730824441 549755813888 65683803563423 10848606353358848 Bool.true 28147680061902706180096 51200331767 1099511627776 262253568102569 43394425413435392 (ep1106 (BSN.head_sum_c_succ qz142 28 29 rfl rfl) (ep1160 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1161 ep1168) rfl rfl

noncomputable abbrev qz178 := (@HMul.hMul Real Real Real qz269 qz439 qz646)

noncomputable def ep1170 := @Enclosure.Complex.IsNear.of_eq qz699 (Complex.mk (@HMul.hMul Real Real Real qz0 qz372 (Real.cos qz178)) (@HMul.hMul Real Real Real qz0 qz372 (@Neg.neg Real Real.instNeg (Real.sin qz178)))) Bool.false 93834446349 549755813888 14326291211537 108486063533588480 Bool.true 35629648173 549755813888 14266295056817 108486063533588480 (BSN.cpow_neg_s_mk qz145 140505 1000 30 qz146 rfl)

noncomputable def ep1171 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz646 140505 1000 0 1 3829405717437687 1125899906842624 50000000039467 9866750000000000000 107610130065716442387 225179981368524800 1405050001109062167 1973350000000000000000 qz147 (BSN.isNear_log_sfrac 30 1 3829405717437687 1125899906842624 50000000039467 9866750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz647) Bool.false 64246766873087041339392 18889465931478580854784 1000000000789340 197335000000000000000 3829405717437687 1125899906842624 50000000039467 9866750000000000000 (BSN.log_rat_reduce_isNear 30 1 4 60 32 329571 524288 24973259072661432 36028797018963968 197335 1000000000000000 rfl rfl rfl rfl (ep492 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1172 := nat_lit 368832734435045152779200510176792576

noncomputable def ep1173 := BSN.cos_dyadic_bound_f 779304824 2147483648 2 1 1048576 395056 ep1172 ep62 ep1172 ep1172 ep63 ep1172 980286 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 779304824) qz20 0 1 ep1172 ep62 ep1172 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 779304824) qz21 0 1 ep1172 ep63 ep1172 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz469 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 125274679) qz31)

noncomputable def ep1174 := @Enclosure.Real.IsNear.cos_image qz178 qz469 Bool.false 125274679 262144 187 262144 Bool.false 980286 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz178 Bool.false 107610130065716442387 225179981368524800 1405050001109062167 1973350000000000000000 125274679 262144 187 262144 (ep1171 rfl) rfl) (Enclosure.sfrac_false_div 125274679 262144) (BSN.cos_reduce0 qz469 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13709675454864459563008) qz321) 226375608064910080 72057594037927936 Bool.false 980286 1048576 76 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q0 125274679 262144 226375608064910080 72057594037927936 76 13709675454864459563008 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 980286 1048576 13709675454864459563008 37778931862957161709568 779304824 2147483648 395056 394670 (ep1173 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1175 := BSN.sin_dyadic_bound_f 779304824 2147483648 2 1 1048576 395056 ep1172 ep58 ep1172 ep1172 ep59 ep1172 372222 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 779304824) qz15 0 1 ep1172 ep58 ep1172 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 779304824) qz16 0 1 ep1172 ep59 ep1172 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1176 := @Enclosure.Real.IsNear.sin_image qz178 qz469 Bool.false 125274679 262144 187 262144 Bool.false 372222 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz178 Bool.false 107610130065716442387 225179981368524800 1405050001109062167 1973350000000000000000 125274679 262144 187 262144 (ep1171 rfl) rfl) (Enclosure.sfrac_false_div 125274679 262144) (BSN.sin_reduce0 qz469 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13709675454864459563008) qz321) 226375608064910080 72057594037927936 Bool.false 372222 1048576 76 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q0 125274679 262144 226375608064910080 72057594037927936 76 13709675454864459563008 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 372222 1048576 13709675454864459563008 37778931862957161709568 779304824 2147483648 395056 394670 (ep1175 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1177 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz372 (Real.cos qz178)) (@HMul.hMul Real Real Real qz0 qz372 (@Neg.neg Real Real.instNeg (Real.sin qz178))) Bool.false 93834446349 549755813888 14326291211537 108486063533588480 Bool.true 35629648173 549755813888 14266295056817 108486063533588480 (@Enclosure.Real.IsNear.mulLit_ff qz372 (Real.cos qz178) 191443 1048576 1 1048576 490143 524288 37163789 51730186240 93834446349 549755813888 14326291211537 108486063533588480 qz376 (@Enclosure.Real.IsNear.recentre' (Real.cos qz178) Bool.false 980286 1048576 37163789 51730186240 490143 524288 37163789 51730186240 (ep1174 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz372 (@Neg.neg Real Real.instNeg (Real.sin qz178)) 191443 1048576 1 1048576 186111 524288 37163789 51730186240 35629648173 549755813888 14266295056817 108486063533588480 qz376 (@Enclosure.Real.IsNear.neg (Real.sin qz178) Bool.false 186111 524288 37163789 51730186240 (@Enclosure.Real.IsNear.recentre' (Real.sin qz178) Bool.false 372222 1048576 37163789 51730186240 186111 524288 37163789 51730186240 (ep1176 rfl rfl) rfl)) rfl)

noncomputable def ep1178 := @ep1103 93834446349 549755813888 14326291211537 108486063533588480 Bool.true 35629648173 549755813888 14266295056817 108486063533588480 Bool.false 241653563200055562731520 219782635395 274877906944 671164326845767 108486063533588480 Bool.true 67322892521684120633344 122459628113 1099511627776 1339800430626479 216972127067176960 (ep1104 (BSN.head_sum_c_succ qz142 29 30 rfl rfl) (ep1169 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1170 ep1177) rfl rfl

noncomputable abbrev qz179 := (@HMul.hMul Real Real Real qz269 qz439 qz648)

noncomputable def ep1179 := @Enclosure.Complex.IsNear.of_eq qz698 (Complex.mk (@HMul.hMul Real Real Real qz0 qz377 (Real.cos qz179)) (@HMul.hMul Real Real Real qz0 qz377 (@Neg.neg Real Real.instNeg (Real.sin qz179)))) Bool.false 1573488795 34359738368 701224625377 5424303176679424 Bool.false 95475081511 549755813888 2819630703801 21697212706717696 (BSN.cpow_neg_s_mk qz145 140505 1000 31 qz146 rfl)

noncomputable def ep1180 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz648 140505 1000 0 1 3866325256314103 1125899906842624 50000000039467 9866750000000000000 108647606027682608403 225179981368524800 1405050001109062167 1973350000000000000000 qz147 (BSN.isNear_log_sfrac 31 1 3866325256314103 1125899906842624 50000000039467 9866750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz649) Bool.false 64866173951437069877248 18889465931478580854784 1000000000789340 197335000000000000000 3866325256314103 1125899906842624 50000000039467 9866750000000000000 (BSN.log_rat_reduce_isNear 31 1 4 62 32 346763 524288 24973259072661432 36028797018963968 197335 1000000000000000 rfl rfl rfl rfl (ep507 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1181 := nat_lit 93972169583442588731362999385302081

noncomputable def ep1182 := BSN.sin_dyadic_bound_f 553668497 2147483648 2 1 1048576 395056 ep1181 ep58 ep1181 ep1181 ep59 ep1181 267360 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 553668497) qz15 0 1 ep1181 ep58 ep1181 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 553668497) qz16 0 1 ep1181 ep59 ep1181 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz470 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 31620615) (@Nat.cast Real Real.instNatCast 65536))

noncomputable def ep1183 := @Enclosure.Real.IsNear.cos_image qz179 qz470 Bool.false 31620615 65536 187 262144 Bool.false 267360 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz179 Bool.false 108647606027682608403 225179981368524800 1405050001109062167 1973350000000000000000 31620615 65536 187 262144 (ep1180 rfl) rfl) (Enclosure.sfrac_false_div 31620615 65536) (BSN.cos_reduce3 qz470 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2435059805651594117120) qz623) 226375608064910080 72057594037927936 Bool.false 267360 1048576 76 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q3 31620615 65536 226375608064910080 72057594037927936 76 2435059805651594117120 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 267360 1048576 2435059805651594117120 9444732965739290427392 553668497 2147483648 395056 394670 (ep1182 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1184 := BSN.cos_dyadic_bound_f 553668497 2147483648 2 1 1048576 395056 ep1181 ep62 ep1181 ep1181 ep63 ep1181 1013918 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 553668497) qz20 0 1 ep1181 ep62 ep1181 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 553668497) qz21 0 1 ep1181 ep63 ep1181 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1185 := @Enclosure.Real.IsNear.sin_image qz179 qz470 Bool.false 31620615 65536 187 262144 Bool.true 1013918 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz179 Bool.false 108647606027682608403 225179981368524800 1405050001109062167 1973350000000000000000 31620615 65536 187 262144 (ep1180 rfl) rfl) (Enclosure.sfrac_false_div 31620615 65536) (BSN.sin_reduce3 qz470 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2435059805651594117120) qz623) 226375608064910080 72057594037927936 Bool.false 1013918 1048576 76 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q3 31620615 65536 226375608064910080 72057594037927936 76 2435059805651594117120 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1013918 1048576 2435059805651594117120 9444732965739290427392 553668497 2147483648 395056 394670 (ep1184 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1186 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz377 (Real.cos qz179)) (@HMul.hMul Real Real Real qz0 qz377 (@Neg.neg Real Real.instNeg (Real.sin qz179))) Bool.false 1573488795 34359738368 701224625377 5424303176679424 Bool.false 95475081511 549755813888 2819630703801 21697212706717696 (@Enclosure.Real.IsNear.mulLit_ff qz377 (Real.cos qz179) 188329 1048576 1 1048576 8355 32768 37163789 51730186240 1573488795 34359738368 701224625377 5424303176679424 qz381 (@Enclosure.Real.IsNear.recentre' (Real.cos qz179) Bool.false 267360 1048576 37163789 51730186240 8355 32768 37163789 51730186240 (ep1183 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz377 (@Neg.neg Real Real.instNeg (Real.sin qz179)) 188329 1048576 1 1048576 506959 524288 37163789 51730186240 95475081511 549755813888 2819630703801 21697212706717696 qz381 (@Enclosure.Real.IsNear.neg (Real.sin qz179) Bool.true 506959 524288 37163789 51730186240 (@Enclosure.Real.IsNear.recentre' (Real.sin qz179) Bool.true 1013918 1048576 37163789 51730186240 506959 524288 37163789 51730186240 (ep1185 rfl rfl) rfl)) rfl)

noncomputable def ep1187 := @ep1101 1573488795 34359738368 701224625377 5424303176679424 Bool.false 95475081511 549755813888 2819630703801 21697212706717696 Bool.false 7984191156571173027840 232370545755 274877906944 685188819353307 108486063533588480 Bool.false 37653069762521771016192 68490534909 1099511627776 1367996737664489 216972127067176960 (ep1102 (BSN.head_sum_c_succ qz142 30 31 rfl rfl) (ep1178 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1179 ep1186) rfl rfl

noncomputable abbrev qz180 := (@HMul.hMul Real Real Real qz269 qz439 qz650)

noncomputable def ep1188 := @Enclosure.Complex.IsNear.of_eq qz697 (Complex.mk (@HMul.hMul Real Real Real qz0 qz382 (Real.cos qz180)) (@HMul.hMul Real Real Real qz0 qz382 (@Neg.neg Real Real.instNeg (Real.sin qz180)))) Bool.true 97181557551 549755813888 13881115370187 108486063533588480 Bool.false 1236185847 1099511627776 27556630363899 216972127067176960 (BSN.cpow_neg_s_mk qz145 140505 1000 32 qz146 rfl)

noncomputable def ep1189 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz650 140505 1000 0 1 15608286920413395 4503599627370496 40000000039467 7893400000000000000 87721694150107362579 180143985094819840 1124040001109062167 1578680000000000000000 qz147 (BSN.isNear_log_sfrac 32 1 15608286920413395 4503599627370496 40000000039467 7893400000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz651) Bool.false 65465900263437584302080 18889465931478580854784 1000000000986675 197335000000000000000 15608286920413395 4503599627370496 40000000039467 7893400000000000000 (BSN.log_rat_reduce_isNear 32 1 5 64 64 0 524288 24973259072661432 36028797018963968 197335 1000000000000000 rfl rfl rfl rfl (ep522 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1190 := BSN.cos_dyadic_bound_f 13660075 2147483648 1 0 1048576 395056 0 1 1 0 1 1 1048554 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 13660075) qz20 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 13660075) qz21 0 0 rfl) rfl rfl

noncomputable abbrev qz471 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 255303731) qz17)

noncomputable def ep1191 := @Enclosure.Real.IsNear.cos_image qz180 qz471 Bool.false 255303731 524288 187 262144 Bool.true 1048554 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz180 Bool.false 87721694150107362579 180143985094819840 1124040001109062167 1578680000000000000000 255303731 524288 187 262144 (ep1189 rfl) rfl) (Enclosure.sfrac_false_div 255303731 524288) (BSN.cos_reduce2 qz471 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 480621180686572716032) qz19) 226375608064910080 72057594037927936 Bool.false 1048554 1048576 77 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q2 255303731 524288 226375608064910080 72057594037927936 77 480621180686572716032 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1048554 1048576 480621180686572716032 75557863725914323419136 13660075 2147483648 395056 394670 (ep1190 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1192 := BSN.sin_dyadic_bound_f 13660075 2147483648 1 0 1048576 395056 0 1 1 0 1 1 6669 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 13660075) qz15 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 13660075) qz16 0 0 rfl) rfl rfl

noncomputable def ep1193 := @Enclosure.Real.IsNear.sin_image qz180 qz471 Bool.false 255303731 524288 187 262144 Bool.true 6669 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz180 Bool.false 87721694150107362579 180143985094819840 1124040001109062167 1578680000000000000000 255303731 524288 187 262144 (ep1189 rfl) rfl) (Enclosure.sfrac_false_div 255303731 524288) (BSN.sin_reduce2 qz471 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 480621180686572716032) qz19) 226375608064910080 72057594037927936 Bool.false 6669 1048576 77 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q2 255303731 524288 226375608064910080 72057594037927936 77 480621180686572716032 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 6669 1048576 480621180686572716032 75557863725914323419136 13660075 2147483648 395056 394670 (ep1192 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1194 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz382 (Real.cos qz180)) (@HMul.hMul Real Real Real qz0 qz382 (@Neg.neg Real Real.instNeg (Real.sin qz180))) Bool.true 97181557551 549755813888 13881115370187 108486063533588480 Bool.false 1236185847 1099511627776 27556630363899 216972127067176960 (@Enclosure.Real.IsNear.mulLit_ft qz382 (Real.cos qz180) 185363 1048576 1 1048576 524277 524288 37163789 51730186240 97181557551 549755813888 13881115370187 108486063533588480 qz386 (@Enclosure.Real.IsNear.recentre' (Real.cos qz180) Bool.true 1048554 1048576 37163789 51730186240 524277 524288 37163789 51730186240 (ep1191 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz382 (@Neg.neg Real Real.instNeg (Real.sin qz180)) 185363 1048576 1 1048576 6669 1048576 37163789 51730186240 1236185847 1099511627776 27556630363899 216972127067176960 qz386 (@Enclosure.Real.IsNear.neg (Real.sin qz180) Bool.true 6669 1048576 37163789 51730186240 (@Enclosure.Real.IsNear.recentre' (Real.sin qz180) Bool.true 6669 1048576 37163789 51730186240 6669 1048576 37163789 51730186240 (ep1193 rfl rfl) rfl)) rfl)

noncomputable def ep1195 := @ep1099 97181557551 549755813888 13881115370187 108486063533588480 Bool.false 1236185847 1099511627776 27556630363899 216972127067176960 Bool.false 101033995371962009911296 367559533959 549755813888 349534967361747 54243031766794240 Bool.false 76665340237912165318656 17431680189 274877906944 348888342007097 54243031766794240 (ep1100 (BSN.head_sum_c_succ qz142 31 32 rfl rfl) (ep1187 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1188 ep1194) rfl rfl

theorem EMRow48.d16 : Enclosure.Complex.IsNear qz172 Bool.false 367559533959 549755813888 349534967361747 54243031766794240 Bool.false 17431680189 274877906944 348888342007097 54243031766794240 := ep1098 (BSN.head_sum_c_succ qz142 32 33 rfl rfl) (ep1195 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

theorem EMRow48.d17 : @Eq Nat (Nat.pow 36 1) 36 := @Eq.refl Nat 36

noncomputable def ep1196 := nat_lit 321181538900509585412618878613

noncomputable def ep1197 := nat_lit 437008643428386680926088724480

noncomputable def ep1198 := nat_lit 5491022539163751649137420400096482869707

noncomputable def ep1199 := nat_lit 765791921562902109394707541022799298560000

noncomputable abbrev qz705 := (@HAdd.hAdd Complex Complex Complex qz720 (@HAdd.hAdd Complex Complex Complex qz720 qz723 (@HMul.hMul Complex Complex Complex qz722 Complex.I (@HDiv.hDiv Complex Complex Complex qz724 (↑qz727) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz472 := qz705

noncomputable abbrev qz181 := (Complex.Stirling.logGammaStirling 1 qz472)

noncomputable abbrev qz706 := (@HAdd.hAdd Complex Complex Complex qz720 qz723 (@HMul.hMul Complex Complex Complex qz722 Complex.I (@HDiv.hDiv Complex Complex Complex qz724 (↑qz727) (2 : Complex))))

noncomputable abbrev qz473 := qz706

noncomputable abbrev qz182 := qz473

noncomputable abbrev qz183 := (@HMul.hMul Real Real Real qz269 (@HDiv.hDiv Real Real Real qz272 qz439 (2 : Real)) (Real.log Real.pi))

noncomputable def ep1200 := Complex.re (@HMul.hMul Complex Complex Complex qz78 (Complex.exp (@HMul.hMul Complex Complex Complex qz78 Complex.I ↑(@HSub.hSub Real Real Real qz391 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz181 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz182 (@Nat.cast Complex Complex.instNatCast j))))) qz183))) (zetaApproximant qz142 1 36))

noncomputable def ep1201 := @Enclosure.Real.IsNear.of_eq ep1200 (@HSub.hSub Real Real Real qz391 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz391 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz181 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz182 (@Nat.cast Complex Complex.instNatCast j))))) qz183)) (Complex.re (zetaApproximant qz142 1 36))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz391 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz181 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz182 (@Nat.cast Complex Complex.instNatCast j))))) qz183)) (Complex.im (zetaApproximant qz142 1 36))))

noncomputable def ep1202 := nat_lit 192707774165386888721197105925

noncomputable def ep1203 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz391 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz181 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz182 (@Nat.cast Complex Complex.instNatCast j))))) qz183)) (Complex.re (zetaApproximant qz142 1 36))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz391 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz181 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz182 (@Nat.cast Complex Complex.instNatCast j))))) qz183)) (Complex.im (zetaApproximant qz142 1 36))) ep1202

noncomputable def ep1204 := nat_lit 262205186057032008555653234688

noncomputable def ep1205 := nat_lit 913919086881330571984541079520794634841

noncomputable def ep1206 := nat_lit 127631986927150351565784590170466549760000

noncomputable def ep1207 := nat_lit 2872937297156315935553107

noncomputable def ep1208 := nat_lit 655512965142580021389133086720

noncomputable def ep1209 := nat_lit 7508017875768217230173922971715060661

noncomputable def ep1210 := nat_lit 126323197748237969418585532057950156525118715967973009391616

noncomputable def ep1211 := @Enclosure.Real.IsNear.mulLit_tf (Real.cos (@HSub.hSub Real Real Real qz391 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz181 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz182 (@Nat.cast Complex Complex.instNatCast j))))) qz183)) (Complex.re (zetaApproximant qz142 1 36)) 1048575 1048576 38609943

noncomputable def ep1212 := nat_lit 6369003788162135343005441359

noncomputable def ep1213 := nat_lit 925223715136606897264656384000

noncomputable def ep1214 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz391 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz181 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz182 (@Nat.cast Complex Complex.instNatCast j))))) qz183)) Bool.true 1048575 1048576 38609943

noncomputable abbrev qz474 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 154827681) qz24)

noncomputable def ep1215 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz391 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz181 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz182 (@Nat.cast Complex Complex.instNatCast j))))) qz183) qz474 Bool.false 154827681 1048576 193

noncomputable def ep1216 := nat_lit 3033429673868102603110201

noncomputable def ep1217 := nat_lit 8276829798400000000000000000

noncomputable def ep1218 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz391 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz181 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz182 (@Nat.cast Complex Complex.instNatCast j))))) qz183) Bool.false 132995966106258804873 900719925474099200 ep1216 ep1217

noncomputable def ep1219 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz181 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz182 (@Nat.cast Complex Complex.instNatCast j))))) qz183 205431968100361867401 900719925474099200 815305339868102603110201 ep1217 2108165121 26214400

noncomputable def ep1220 := nat_lit 3486409453895910814462771200

noncomputable def ep1221 := nat_lit 2069207449600000000000000000

noncomputable def ep1222 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz79 qz181 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz182 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 6220399652835733107 56294995342131200 382102617652034855245637 ep1221 Bool.false 205431968100361867401 900719925474099200

noncomputable def ep1223 := @Enclosure.Complex.IsNear.subLitP qz181 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz182 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 5741646977925232057 56294995342131200 376859737627204365850437 ep1221 Bool.false 208242433773595592201 900719925474099200 773362299859825773311801

noncomputable def ep1224 := nat_lit 7003547389651642575683444715552768

noncomputable def ep1225 := nat_lit 57823958436673582940342420615725056

noncomputable abbrev qz475 := (@HSub.hSub Complex Complex Complex qz653 qz705 qz656)

noncomputable abbrev qz476 := (Complex.log qz705)

noncomputable abbrev qz184 := (@HSub.hSub Complex Complex Complex qz388 (@HMul.hMul Complex Complex Complex qz387 qz475 qz476) qz472)

noncomputable abbrev qz185 := qz472

noncomputable def ep1226 := @Enclosure.Complex.IsNear.of_eq qz181 (@HAdd.hAdd Complex Complex Complex qz4 (@HAdd.hAdd Complex Complex Complex qz4 qz184 qz84) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz79 (@HMul.hMul Complex Complex Complex qz78 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz87 qz185 (@HSub.hSub Int Int Int qz398 qz89 (@HMul.hMul Int Int Int qz399 qz90 (@Nat.cast Int instNatCastInt k)))))) Bool.true 5741646977925232057

noncomputable def ep1227 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz4 qz184 qz84) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz79 (@HMul.hMul Complex Complex Complex qz78 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz87 qz185 (@HSub.hSub Int Int Int qz398 qz89 (@HMul.hMul Int Int Int qz399 qz90 (@Nat.cast Int instNatCastInt k))))) Bool.true 5741649114422588857 56294995342131200

noncomputable def ep1228 := nat_lit 394562975925857689888412925952

noncomputable def ep1229 := nat_lit 1431031108315262298932876253593600

noncomputable def ep1230 := @ep1227 5750421864233553717 31573600000000000000000 Bool.false 208243501110701786633 900719925474099200 368762501667046613 3946700000000000000000 Bool.false 2608029 68719476736 3 68719476736 Bool.true 8143135881 6871947673600 9367 6871947673600 Bool.true ep1228 5741646977925232057 56294995342131200 376859737627204365850437 ep1221 Bool.false ep1229

noncomputable def ep1231 := @Enclosure.Complex.IsNear.addLitP qz184 qz84 Bool.true 5793380707012720057 56294995342131200 5690200001440584967 31573600000000000000000

noncomputable def ep1232 := @ep1231 Bool.false 208243501110701786633 900719925474099200 368762501667046613 3946700000000000000000 Bool.false 120447 131072 1 524288 Bool.false 0 1 0 1 Bool.true 752569432725597566664704 5741649114422588857 56294995342131200 5750421864233553717 31573600000000000000000 Bool.false 208243501110701786633 208243501110701786633 900719925474099200

noncomputable abbrev qz186 := (@HMul.hMul Complex Complex Complex qz387 qz475 qz476)

noncomputable def ep1233 := @Enclosure.Complex.IsNear.subLitP qz186 qz185 Bool.true 5666716967492924857 56294995342131200 5690200001440584967 31573600000000000000000 Bool.false 271521327675070940681

noncomputable def ep1234 := @ep1233 900719925474099200 368762501667046613 3946700000000000000000 Bool.false 9000 4000 0 1 Bool.false 281010 4000 0 1 Bool.true 23173522828050880228000 5793380707012720057 56294995342131200 5690200001440584967 31573600000000000000000 Bool.false 832974004442807146532000 208243501110701786633 900719925474099200 368762501667046613 3946700000000000000000

noncomputable abbrev qz187 := qz475

noncomputable abbrev qz188 := qz476

noncomputable def ep1235 := @Enclosure.Complex.IsNear.mul qz187 qz188 Bool.true 5666716967492924857 56294995342131200 5690200001440584967 31573600000000000000000 Bool.false 271521327675070940681 900719925474099200 368762501667046613

noncomputable abbrev qz189 := (Complex.re qz475)

noncomputable abbrev qz190 := (Complex.re qz476)

noncomputable abbrev qz191 := (Complex.im qz475)

noncomputable abbrev qz192 := (Complex.im qz476)

noncomputable def ep1236 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz189 qz190) (@HMul.hMul Real Real Real qz0 qz191 qz192) 67032157851443267 9007199254740992 175000000828807 78934000000000000000 24342671816257781103 225179981368524800

noncomputable def ep1237 := nat_lit 204164995385721627845699896214552576

noncomputable def ep1238 := @Enclosure.Real.IsNear.mulLit_ff qz189 qz190 7000 4000 0 1 9576022550206181 2251799813685248 25000000118401 19733500000000000000

noncomputable def ep1239 := @Enclosure.Complex.IsNear.re_isNear qz187 Bool.false 7000 4000 0 1 Bool.false 281010 4000 0 1

noncomputable abbrev qz707 := (Enclosure.sfrac Bool.false 281010 4000)

noncomputable abbrev qz477 := qz707

noncomputable def ep1240 := @Enclosure.Complex.IsNear.of_eq qz187 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz477) Bool.false 7000 4000 0 1 Bool.false 281010 4000 0

noncomputable abbrev qz478 := (Complex.log (Complex.mk qz660 qz707))

noncomputable def ep1241 := @Enclosure.Complex.IsNear.of_eq qz188 qz478 Bool.false 9576022550206181 2251799813685248 25000000118401 19733500000000000000 Bool.false 866256425616803 562949953421312 200000000039467 78934000000000000000

noncomputable def ep1242 := nat_lit 6554923640636280392563998117716977201500000000

noncomputable def ep1243 := nat_lit 19181951514628983650691098516403840800000000

noncomputable def ep1244 := nat_lit 99988708351854705231903980131440300000000

noncomputable def ep1245 := BSN.log_dyadic_bound 13511620100 144583620100 3 2 ep1242 1048576 394670 ep1243 ep1244 196556 158095240200 131072000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 13511620100) (BSN.artanhQ 144583620100) 0 2 ep1243 ep1242 ep1244 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz708 := (Real.log (Enclosure.sfrac Bool.false 79047620100 16000000))

noncomputable def ep1246 := @Enclosure.Real.IsNear.mulLit_ff qz98 qz708 1 2 0 1 9576022550206181 1125899906842624 25000000118401 9866750000000000000 9576022550206181 2251799813685248 25000000118401 19733500000000000000 qz402 (BSN.isNear_log_sfrac 79047620100 16000000 9576022550206181 1125899906842624 25000000118401 9866750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 79047620100) qz662)) Bool.false 321317997491359886344192 37778931862957161709568 1000000004736040 394670000000000000000 9576022550206181 1125899906842624 25000000118401 9866750000000000000 (BSN.log_rat_reduce_isNear 79047620100 16000000 12 158095240200 131072000000 196556 1048576 24973259072661432 36028797018963968 394670 1000000000000000 rfl rfl rfl rfl (ep1245 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1247 := BSN.arctan_dyadic_bound_f 9000 281010 1 0 1048576 394670 0 1 1 0 1 1 33571 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 281010) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 281010) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz479 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 281010)))

noncomputable def ep1248 := @Enclosure.Real.IsNear.subLit_ff_p qz99 qz479 884279719003555 562949953421312 1 2000000000000000 33571 1048576 1 394670 908335697747564822528 866256425616803 562949953421312 200000000039467 78934000000000000000 qz100 (ep1247 rfl) rfl rfl

noncomputable abbrev qz480 := (Complex.mk qz660 qz707)

noncomputable abbrev qz481 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 281010) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep1249 := @Enclosure.Complex.IsNear.re_isNear qz188 Bool.false 9576022550206181 2251799813685248 25000000118401 19733500000000000000 Bool.false 866256425616803 562949953421312 200000000039467 78934000000000000000 (ep1241 (@congrArg Complex Complex qz185 qz480 Complex.log (BSN.w_shift_mk qz145 Bool.false 140505 1000 2 qz146 rfl)) (@Enclosure.Complex.IsNear.of_parts qz478 Bool.false 9576022550206181 2251799813685248 25000000118401 19733500000000000000 Bool.false 866256425616803 562949953421312 200000000039467 78934000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz478) (@HMul.hMul Real Real Real qz0 qz98 qz708) Bool.false 9576022550206181 2251799813685248 25000000118401 19733500000000000000 (Enclosure.clog_re_eq 9000 281010 4000 79047620100 16000000 rfl rfl rfl) (ep1246 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz478) qz481 Bool.false 866256425616803 562949953421312 200000000039467 78934000000000000000 (Enclosure.clog_im_eq 9000 281010 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz481 (@HSub.hSub Real Real Real qz391 qz99 qz479) Bool.false 866256425616803 562949953421312 200000000039467 78934000000000000000 (BSN.arctan_recip 281010 9000 rfl rfl) ep1248))))

noncomputable def ep1250 := @Enclosure.Real.IsNear.mulLit_ff qz191 qz192 281010 4000 0 1 866256425616803 562949953421312 200000000039467 78934000000000000000

noncomputable def ep1251 := @Enclosure.Complex.IsNear.im_isNear qz187 Bool.false 7000 4000 0 1 Bool.false 281010 4000 0 1

noncomputable def ep1252 := @Enclosure.Complex.IsNear.im_isNear qz188 Bool.false 9576022550206181 2251799813685248 25000000118401 19733500000000000000 Bool.false 866256425616803 562949953421312 200000000039467 78934000000000000000 (ep1241 (@congrArg Complex Complex qz185 qz480 Complex.log (BSN.w_shift_mk qz145 Bool.false 140505 1000 2 qz146 rfl)) (@Enclosure.Complex.IsNear.of_parts qz478 Bool.false 9576022550206181 2251799813685248 25000000118401 19733500000000000000 Bool.false 866256425616803 562949953421312 200000000039467 78934000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz478) (@HMul.hMul Real Real Real qz0 qz98 qz708) Bool.false 9576022550206181 2251799813685248 25000000118401 19733500000000000000 (Enclosure.clog_re_eq 9000 281010 4000 79047620100 16000000 rfl rfl rfl) (ep1246 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz478) qz481 Bool.false 866256425616803 562949953421312 200000000039467 78934000000000000000 (Enclosure.clog_im_eq 9000 281010 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz481 (@HSub.hSub Real Real Real qz391 qz99 qz479) Bool.false 866256425616803 562949953421312 200000000039467 78934000000000000000 (BSN.arctan_recip 281010 9000 rfl rfl) ep1248))))

noncomputable abbrev qz193 := (@ep1240 1 (BSN.w_sub_half_mk qz439 Bool.false 140505 1000 2 qz440 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz477 Bool.false 7000 4000 0 1 Bool.false 281010 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) (Enclosure.Real.IsNear.const Bool.false 281010 4000)))

noncomputable def ep1253 := @ep1236 5620200001109062167 31573600000000000000000 ep1237 5666716967492924857 56294995342131200 5690200001440584967 31573600000000000000000 (@ep1238 67032157851443267 9007199254740992 175000000828807 78934000000000000000 (ep1239 qz193) ep1249 rfl) (@ep1250 24342671816257781103 225179981368524800 5620200001109062167 31573600000000000000000 (ep1251 qz193) ep1252 rfl) rfl

noncomputable def ep1254 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz189 qz192) (@HMul.hMul Real Real Real qz0 qz191 qz190) 6063794979317621 2251799813685248 1400000000276269 315736000000000000000 269095809683343892281 900719925474099200

noncomputable def ep1255 := nat_lit 611411675070295915733896904612773888

noncomputable def ep1256 := @Enclosure.Real.IsNear.mulLit_ff qz189 qz192 7000 4000 0 1 866256425616803 562949953421312 200000000039467 78934000000000000000

noncomputable def ep1257 := @Enclosure.Real.IsNear.mulLit_ff qz191 qz190 281010 4000 0 1 9576022550206181 2251799813685248 25000000118401 19733500000000000000

noncomputable def ep1258 := @ep1254 702525003327186501 7893400000000000000000 ep1255 271521327675070940681 900719925474099200 368762501667046613 3946700000000000000000 (@ep1256 6063794979317621 2251799813685248 1400000000276269 315736000000000000000 (ep1239 qz193) ep1252 rfl) (@ep1257 269095809683343892281 900719925474099200 702525003327186501 7893400000000000000000 (ep1251 qz193) ep1249 rfl) rfl

noncomputable def ep1259 := @Enclosure.Complex.IsNear.of_eq qz185 qz480 Bool.false 9000 4000 0 1 Bool.false 281010 4000 0 1 (BSN.w_shift_mk qz145 Bool.false 140505 1000 2 qz146 rfl)

noncomputable abbrev qz482 := (ep1259 (@Enclosure.Complex.IsNear.mk qz660 qz707 Bool.false 9000 4000 0 1 Bool.false 281010 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 281010 4000)))

noncomputable abbrev qz194 := qz482

noncomputable def ep1260 := ep1234 (@ep1235 3946700000000000000000 (ep1253 rfl) (ep1258 rfl)) qz194 rfl rfl rfl rfl rfl rfl

noncomputable def ep1261 := @ep1232 368762501667046613 3946700000000000000000 (ep1260 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz103 (↑qz2) Bool.false 120447 131072 1 524288 Bool.false 0 1 0 1 (@ep607 131072 1 524288 (ep609 rfl) (ep611 rfl) rfl rfl) (@ep612 1 0 1 (ep614 rfl) (ep616 rfl) rfl rfl))

noncomputable abbrev qz483 := (@HPow.hPow Complex Int Complex qz658 qz705 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz195 := qz483

noncomputable def ep1262 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz79 (@HMul.hMul Complex Complex Complex qz78 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz87 qz185 (@HSub.hSub Int Int Int qz398 qz89 (@HMul.hMul Int Int Int qz399 qz90 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz79 (@HMul.hMul Complex Complex Complex qz78 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz87 qz185 (@HSub.hSub Int Int Int qz398 qz89 (@HMul.hMul Int Int Int qz399 qz90 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli qz105)) qz106) qz195)) Bool.false 2608029 68719476736 3 68719476736

noncomputable def ep1263 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz79 (@HMul.hMul Complex Complex Complex qz78 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz87 qz185 (@HSub.hSub Int Int Int qz398 qz89 (@HMul.hMul Int Int Int qz399 qz90 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli qz105)) qz106) qz195) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1264 := @ep1263 0 1 0 1 Bool.false 2608029 68719476736 3 68719476736 Bool.true 8143135881 6871947673600 9367 6871947673600 Bool.false 2608029 2608029 68719476736 3 68719476736 Bool.true 8143135881 8143135881 6871947673600 9367

noncomputable def ep1265 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz79 (@HMul.hMul Complex Complex Complex qz78 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz87 qz185 (@HSub.hSub Int Int Int qz398 qz89 (@HMul.hMul Int Int Int qz399 qz90 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1266 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli qz105)) qz106) qz195 Bool.false 2608029 68719476736 3 68719476736 Bool.true 8143135881 6871947673600 9367 6871947673600

noncomputable abbrev qz196 := (Complex.re qz483)

noncomputable abbrev qz197 := (Complex.im qz483)

noncomputable def ep1267 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli qz105)) qz106)) qz196) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli qz105)) qz106)) qz197) 2608029 68719476736 3 68719476736 0 1 0

noncomputable def ep1268 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli qz105)) qz106)) qz196 1 12 0 1 7824087 17179869184 9 17179869184 2608029

noncomputable def ep1269 := @Enclosure.Complex.IsNear.re_isNear qz195 Bool.false 7824087 17179869184 9 17179869184 Bool.true 24429407643 1717986918400 28101 1717986918400

noncomputable abbrev qz484 := (@HPow.hPow Complex Nat Complex qz663 qz705 1)

noncomputable abbrev qz198 := (@Inv.inv Complex Complex.instInv qz484)

noncomputable def ep1270 := @Enclosure.Complex.IsNear.of_eq qz195 qz198 Bool.false 7824087 17179869184 9 17179869184 Bool.true 24429407643 1717986918400 28101

noncomputable def ep1271 := @Enclosure.Complex.IsNear.of_parts qz198 Bool.false 7824087 17179869184 9 17179869184 Bool.true 24429407643 1717986918400 28101

noncomputable abbrev qz199 := (Complex.re qz484)

noncomputable abbrev qz200 := qz484

noncomputable def ep1272 := @Enclosure.Real.IsNear.mulLit_ff qz199 (@Inv.inv Real Real.instInv (@DFunLike.coe qz112 Complex (fun (x : Complex) => Real) qz113 Complex.normSq qz200)) 9000 4000 0 1 869343 4294967296 1 4294967296

noncomputable def ep1273 := @Enclosure.Complex.IsNear.re_isNear qz200 Bool.false 9000 4000 0 1 Bool.false 281010 4000 0 1

noncomputable def ep1274 := @Enclosure.Complex.IsNear.of_eq qz200 qz185 Bool.false 9000 4000 0 1 Bool.false 281010 4000 0

noncomputable def ep1275 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz112 Complex (fun (x : Complex) => Real) qz113 Complex.normSq qz200)) Bool.false 869343 4294967296 1 4294967296 869343 4294967296 1

noncomputable abbrev qz201 := (Complex.im qz484)

noncomputable def ep1276 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz112 Complex (fun (x : Complex) => Real) qz113 Complex.normSq qz200) (@HAdd.hAdd Real Real Real qz411 (@HMul.hMul Real Real Real qz0 qz199 qz199) (@HMul.hMul Real Real Real qz0 qz201 qz201)) Bool.false 790476201 160000 0 1

noncomputable def ep1277 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz199 qz199) (@HMul.hMul Real Real Real qz0 qz201 qz201) 81 16 0 1 789666201 160000

noncomputable def ep1278 := @Enclosure.Real.IsNear.mulLit_ff qz199 qz199 9000 4000 0 1 9000 4000 0 1

noncomputable def ep1279 := @Enclosure.Real.IsNear.mulLit_ff qz201 qz201 281010 4000 0 1 281010 4000 0 1

noncomputable def ep1280 := @Enclosure.Complex.IsNear.im_isNear qz200 Bool.false 9000 4000 0 1 Bool.false 281010 4000 0 1

noncomputable abbrev qz202 := (ep1273 (@ep1274 1 (BSN.pow_one_c qz472) qz482))

noncomputable abbrev qz203 := (ep1280 (@ep1274 1 (BSN.pow_one_c qz472) qz482))

noncomputable def ep1281 := @ep1277 0 1 12647619216 790476201 160000 0 1 (@ep1278 81 16 0 1 qz202 qz202 rfl) (@ep1279 789666201 160000 0 1 qz203 qz203 rfl)

noncomputable def ep1282 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz112 Complex (fun (x : Complex) => Real) qz113 Complex.normSq qz200) 790476201 160000 0 1 434671 434672 2147483648 (ep1276 (Enclosure.Complex.normSq_eq_mul_add_mul qz200) (ep1281 rfl rfl)) rfl

noncomputable def ep1283 := @Enclosure.Real.IsNear.of_eq (Complex.re qz198) (@HMul.hMul Real Real Real qz0 qz199 (@Inv.inv Real Real.instInv (@DFunLike.coe qz112 Complex (fun (x : Complex) => Real) qz113 Complex.normSq qz200))) Bool.false 7824087 17179869184 9 17179869184 (Enclosure.Complex.inv_re_eq_mul qz200) (@ep1272 7824087 17179869184 9 17179869184 qz202 (@ep1275 4294967296 (ep1282 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep1284 := @Enclosure.Real.IsNear.of_eq (Complex.im qz198) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz201) (@Inv.inv Real Real.instInv (@DFunLike.coe qz112 Complex (fun (x : Complex) => Real) qz113 Complex.normSq qz200))) Bool.true 24429407643 1717986918400 28101 1717986918400 (Enclosure.Complex.inv_im_eq_mul qz200)

noncomputable def ep1285 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz201) (@Inv.inv Real Real.instInv (@DFunLike.coe qz112 Complex (fun (x : Complex) => Real) qz113 Complex.normSq qz200)) 281010 4000 0 1 869343 4294967296 1

noncomputable def ep1286 := @ep1285 4294967296 24429407643 1717986918400 28101 1717986918400 (@Enclosure.Real.IsNear.neg qz201 Bool.false 281010 4000 0 1 qz203) (@ep1275 4294967296 (ep1282 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep1287 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli qz105)) qz106)) qz197 0 1 0 1 24429407643 1717986918400 28101 1717986918400 0

noncomputable def ep1288 := @Enclosure.Complex.IsNear.im_isNear qz195 Bool.false 7824087 17179869184 9 17179869184 Bool.true 24429407643 1717986918400 28101 1717986918400

noncomputable abbrev qz204 := (@ep1270 1717986918400 (BSN.zpow_one_sub_two_mul qz472 1 1 rfl rfl) (@ep1271 1717986918400 ep1283 (ep1284 ep1286)))

noncomputable def ep1289 := @ep1267 1 2608029 2608029 68719476736 3 68719476736 (@ep1268 68719476736 3 68719476736 ep626 (ep1269 qz204) rfl) (@ep1287 1 0 1 ep646 (ep1288 qz204) rfl) rfl

noncomputable def ep1290 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli qz105)) qz106)) qz197) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli qz105)) qz106)) qz196) 8143135881 6871947673600 9367 6871947673600 0 1 0

noncomputable def ep1291 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli qz105)) qz106)) qz197 1 12 0 1 24429407643 1717986918400 28101 1717986918400 8143135881

noncomputable def ep1292 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli qz105)) qz106)) qz196 0 1 0 1 7824087 17179869184 9 17179869184 0

noncomputable def ep1293 := @ep1290 1 8143135881 8143135881 6871947673600 9367 6871947673600 (@ep1291 6871947673600 9367 6871947673600 ep626 (ep1288 qz204) rfl) (@ep1292 1 0 1 ep646 (ep1269 qz204) rfl) rfl

noncomputable def ep1294 := @ep1264 6871947673600 (@ep1265 0 1 0 1 (BSN.stirling_sum_base qz185) qz119) (ep1266 (ep1289 rfl) (ep1293 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep1295 := @ep1230 208242433773595592201 900719925474099200 773362299859825773311801 ep1217 (ep1261 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep1262 Bool.true 8143135881 6871947673600 9367 6871947673600 (BSN.stirling_sum_succ qz185 0 1 rfl) (ep1294 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep1296 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz182 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz145 2) Bool.false 9575053498210021 1125899906842624 25000000118401 9866750000000000000 Bool.false 878270522885539 281474976710656

noncomputable abbrev qz205 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz274 qz473 qz407))

noncomputable def ep1297 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz145 2) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz145 1) qz205) Bool.false 9575053498210021 1125899906842624 25000000118401 9866750000000000000 Bool.false 878270522885539 281474976710656 200000000039467 39467000000000000000

noncomputable def ep1298 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz145 1) qz205 Bool.false 9574882236389093 2251799813685248 25000000118401 19733500000000000000 Bool.false 882276653630883 562949953421312 200000000039467 78934000000000000000 Bool.false

noncomputable def ep1299 := nat_lit 43122207366591214764134986940416

noncomputable def ep1300 := nat_lit 988844699899451029935238414336

noncomputable abbrev qz206 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz274 qz473 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep1301 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz145 1) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz145 0) qz206) Bool.false 9574882236389093 2251799813685248 25000000118401 19733500000000000000 Bool.false 882276653630883 562949953421312 200000000039467 78934000000000000000

noncomputable def ep1302 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz145 0) qz206 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz485 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz707))

noncomputable def ep1303 := @Enclosure.Complex.IsNear.of_eq qz206 qz485 Bool.false 9574882236389093 2251799813685248 25000000118401 19733500000000000000 Bool.false 882276653630883 562949953421312 200000000039467 78934000000000000000

noncomputable def ep1304 := nat_lit 6540427978666881978379635100432177201500000000

noncomputable def ep1305 := nat_lit 18933449731738124392045930897843840800000000

noncomputable def ep1306 := nat_lit 97641592408621636854814123171440300000000

noncomputable def ep1307 := BSN.log_dyadic_bound 13431620100 144503620100 3 2 ep1304 1048576 394670 ep1305 ep1306 195494 157935240200 131072000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 13431620100) (BSN.artanhQ 144503620100) 0 2 ep1305 ep1304 ep1306 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1308 := @Enclosure.Real.IsNear.mulLit_ff qz98 (Real.log (Enclosure.sfrac Bool.false 78967620100 16000000)) 1 2 0 1 9574882236389093 1125899906842624 25000000118401 9866750000000000000 9574882236389093 2251799813685248 25000000118401 19733500000000000000 qz402 (BSN.isNear_log_sfrac 78967620100 16000000 9574882236389093 1125899906842624 25000000118401 9866750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 78967620100) qz662)) Bool.false 321279734908925746610176 37778931862957161709568 1000000004736040 394670000000000000000 9574882236389093 1125899906842624 25000000118401 9866750000000000000 (BSN.log_rat_reduce_isNear 78967620100 16000000 12 157935240200 131072000000 195494 1048576 24973259072661432 36028797018963968 394670 1000000000000000 rfl rfl rfl rfl (ep1307 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1309 := BSN.arctan_dyadic_bound_f 1000 281010 1 0 1048576 394670 0 1 1 0 1 1 3731 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 281010) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 281010) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz486 := (@Nat.cast Real Real.instNatCast 281010)

noncomputable def ep1310 := @Enclosure.Real.IsNear.subLit_ff_p qz99 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz413 qz486)) 884279719003555 562949953421312 1 2000000000000000 3731 1048576 1 394670 925134124357656772608 882276653630883 562949953421312 200000000039467 78934000000000000000 qz100 (ep1309 rfl) rfl rfl

noncomputable abbrev qz207 := (@HAdd.hAdd Complex Complex Complex qz274 qz473 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz487 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz707)

noncomputable def ep1311 := @ep1302 9574882236389093 2251799813685248 25000000118401 19733500000000000000 Bool.false 882276653630883 562949953421312 200000000039467 78934000000000000000 Bool.false 9574882236389093 9574882236389093 2251799813685248 25000000118401 19733500000000000000 Bool.false 882276653630883 882276653630883 562949953421312 200000000039467 78934000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz145 0) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz145) qz119) (ep1303 (@congrArg Complex Complex qz207 qz487 Complex.log (BSN.w_shift_mk qz145 Bool.false 140505 1000 0 qz146 rfl)) (@Enclosure.Complex.IsNear.of_parts qz485 Bool.false 9574882236389093 2251799813685248 25000000118401 19733500000000000000 Bool.false 882276653630883 562949953421312 200000000039467 78934000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz485) (@HMul.hMul Real Real Real qz0 qz98 (Real.log (Enclosure.sfrac Bool.false 78967620100 16000000))) Bool.false 9574882236389093 2251799813685248 25000000118401 19733500000000000000 (Enclosure.clog_re_eq 1000 281010 4000 78967620100 16000000 rfl rfl rfl) (ep1308 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz485) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz486 qz413)) Bool.false 882276653630883 562949953421312 200000000039467 78934000000000000000 (Enclosure.clog_im_eq 1000 281010 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz486 qz413)) (@HSub.hSub Real Real Real qz391 qz99 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz413 qz486))) Bool.false 882276653630883 562949953421312 200000000039467 78934000000000000000 (BSN.arctan_recip 281010 1000 rfl rfl) ep1310)))) rfl rfl

noncomputable abbrev qz488 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz707))

noncomputable def ep1312 := @Enclosure.Complex.IsNear.of_eq qz205 qz488 Bool.false 9575224760030949 2251799813685248 25000000118401 19733500000000000000 Bool.false 874264392140195 562949953421312 200000000039467 78934000000000000000

noncomputable def ep1313 := nat_lit 6544774150244042865349287756017617201500000000

noncomputable def ep1314 := nat_lit 19007801952260973011584948063411840800000000

noncomputable def ep1315 := nat_lit 98341340186244700761491160259440300000000

noncomputable def ep1316 := BSN.log_dyadic_bound 13455620100 144527620100 3 2 ep1313 1048576 394670 ep1314 ep1315 195813 157983240200 131072000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 13455620100) (BSN.artanhQ 144527620100) 0 2 ep1314 ep1313 ep1315 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1317 := @Enclosure.Real.IsNear.mulLit_ff qz98 (Real.log (Enclosure.sfrac Bool.false 78991620100 16000000)) 1 2 0 1 9575224760030949 1125899906842624 25000000118401 9866750000000000000 9575224760030949 2251799813685248 25000000118401 19733500000000000000 qz402 (BSN.isNear_log_sfrac 78991620100 16000000 9575224760030949 1125899906842624 25000000118401 9866750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 78991620100) qz662)) Bool.false 321291228095174796115968 37778931862957161709568 1000000004736040 394670000000000000000 9575224760030949 1125899906842624 25000000118401 9866750000000000000 (BSN.log_rat_reduce_isNear 78991620100 16000000 12 157983240200 131072000000 195813 1048576 24973259072661432 36028797018963968 394670 1000000000000000 rfl rfl rfl rfl (ep1316 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1318 := BSN.arctan_dyadic_bound_f 5000 281010 1 0 1048576 394670 0 1 1 0 1 1 18655 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 281010) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 281010) 0 0 rfl) rfl rfl rfl

noncomputable def ep1319 := @Enclosure.Real.IsNear.subLit_ff_p qz99 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz417 qz486)) 884279719003555 562949953421312 1 2000000000000000 18655 1048576 1 394670 916732659252797112320 874264392140195 562949953421312 200000000039467 78934000000000000000 qz100 (ep1318 rfl) rfl rfl

noncomputable abbrev qz208 := (@HAdd.hAdd Complex Complex Complex qz274 qz473 qz407)

noncomputable abbrev qz489 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz707)

noncomputable def ep1320 := @ep1298 9575224760030949 2251799813685248 25000000118401 19733500000000000000 Bool.false 874264392140195 562949953421312 200000000039467 78934000000000000000 Bool.false ep1299 9575053498210021 1125899906842624 25000000118401 9866750000000000000 Bool.false ep1300 878270522885539 281474976710656 200000000039467 39467000000000000000 (ep1301 (BSN.log_sum_c_succ qz145 0 1 rfl) (ep1311 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1312 (@congrArg Complex Complex qz208 qz489 Complex.log (BSN.w_shift_mk qz145 Bool.false 140505 1000 1 qz146 rfl)) (@Enclosure.Complex.IsNear.of_parts qz488 Bool.false 9575224760030949 2251799813685248 25000000118401 19733500000000000000 Bool.false 874264392140195 562949953421312 200000000039467 78934000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz488) (@HMul.hMul Real Real Real qz0 qz98 (Real.log (Enclosure.sfrac Bool.false 78991620100 16000000))) Bool.false 9575224760030949 2251799813685248 25000000118401 19733500000000000000 (Enclosure.clog_re_eq 5000 281010 4000 78991620100 16000000 rfl rfl rfl) (ep1317 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz488) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz486 qz417)) Bool.false 874264392140195 562949953421312 200000000039467 78934000000000000000 (Enclosure.clog_im_eq 5000 281010 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz486 qz417)) (@HSub.hSub Real Real Real qz391 qz99 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz417 qz486))) Bool.false 874264392140195 562949953421312 200000000039467 78934000000000000000 (BSN.arctan_recip 281010 5000 rfl rfl) ep1319)))) rfl rfl

noncomputable def ep1321 := @ep1223 ep1217 Bool.false 9575053498210021 1125899906842624 25000000118401 9866750000000000000 Bool.false 878270522885539 281474976710656 200000000039467 39467000000000000000 Bool.true ep1224 6220399652835733107 56294995342131200 382102617652034855245637 ep1221 Bool.false ep1225 205431968100361867401 900719925474099200 815305339868102603110201 ep1217 (@ep1226 56294995342131200 376859737627204365850437 ep1221 Bool.false 208242433773595592201 900719925474099200 773362299859825773311801 ep1217 (BSN.logGammaStirling_unfold 1 qz185) (ep1295 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep1296 200000000039467 39467000000000000000 (BSN.log_sum_c_eq qz145 2) (ep1297 (BSN.log_sum_c_succ qz145 1 2 rfl) (ep1320 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz209 := (@HDiv.hDiv Real Real Real qz272 qz439 (2 : Real))

noncomputable def ep1322 := @Enclosure.Real.IsNear.mulLit_ff qz209 (Real.log Real.pi) 140505 2000 0 1 75021 65536 1 262144 2108165121 26214400 28101 104857600 (@Enclosure.Real.IsNear.of_eq qz209 (Enclosure.sfrac Bool.false 140505 2000) Bool.false 140505 2000 0 1 (BSN.t_half_eq qz145 Bool.false 140505 1000 qz146) (Enclosure.Real.IsNear.const Bool.false 140505 2000)) EMRow48.d5 rfl

noncomputable def ep1323 := @ep1219 28101 104857600 ep1220 132995966106258804873 900719925474099200 ep1216 ep1217 (@ep1222 815305339868102603110201 ep1217 (ep1321 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep1322 rfl rfl

noncomputable def ep1324 := BSN.cos_dyadic_bound_f 704631 2147483648 1 0 1048576 395056 0 1 1 0 1 1 1048575 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 704631) qz20 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 704631) qz21 0 0 rfl) rfl rfl

noncomputable def ep1325 := @ep1215 524288 Bool.true 1048575 1048576 1 197335 (@ep1218 154827681 1048576 193 524288 ep1323 rfl) (Enclosure.sfrac_false_div 154827681 1048576) (BSN.cos_reduce2 qz474 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 49584050128459661312) qz25) 226375608064910080 72057594037927936 Bool.false 1048575 1048576 23 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q2 154827681 1048576 226375608064910080 72057594037927936 23 49584050128459661312 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1048575 1048576 49584050128459661312 151115727451828646838272 704631 2147483648 395056 394670 (ep1324 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1326 := nat_lit 5001167031422271891701760

noncomputable def ep1327 := nat_lit 101724568257663335227902964169

noncomputable def ep1328 := nat_lit 14803579442185710356234502144000

noncomputable abbrev qz490 := (@HPow.hPow Complex Complex Complex qz538 (@Nat.cast Complex Complex.instNatCast 36) qz674)

noncomputable abbrev qz210 := qz490

noncomputable abbrev qz491 := (@Nat.cast Complex Complex.instNatCast 36)

noncomputable abbrev qz211 := (@HAdd.hAdd Complex Complex Complex qz274 (@HDiv.hDiv Complex Complex Complex qz396 qz491 (@HSub.hSub Complex Complex Complex qz388 qz437 (1 : Complex))) qz395)

noncomputable abbrev qz212 := qz491

noncomputable def ep1329 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz142 1 36) (@HAdd.hAdd Complex Complex Complex qz4 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 36, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz143) (@HMul.hMul Complex Complex Complex qz78 qz210 (@HAdd.hAdd Complex Complex Complex qz4 qz211 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz212 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1))))))) Bool.false 551341890180636259841777 750175054713340783755264 ep1212

noncomputable def ep1330 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 36, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz143) (@HMul.hMul Complex Complex Complex qz78 qz210 (@HAdd.hAdd Complex Complex Complex qz4 qz211 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz212 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))))) Bool.false 737927888093 1099511627776 1478731652607979 216972127067176960

noncomputable def ep1331 := nat_lit 63320142020564108363434759

noncomputable def ep1332 := nat_lit 1013656088703180650893914569

noncomputable def ep1333 := nat_lit 606206819133608004734000729478397952

noncomputable def ep1334 := nat_lit 9182639430507914971567805199024128

noncomputable def ep1335 := @ep1330 Bool.false 5706760909 137438953472 2882994251797 423773685678080 Bool.false 47868275313650624107025 750175054713340783755264 ep1331 ep1213 Bool.true 274471705377859404507769 ep1326 ep1332 ep1328 Bool.false ep1333 551341890180636259841777 750175054713340783755264 ep1212 ep1213 Bool.true ep1334 66812495282705021757049 ep1326

noncomputable def ep1336 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 36, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz143) (BSN.headSumC qz142 36) Bool.false 737927888093 1099511627776 1478731652607979 216972127067176960 Bool.false 5706760909 137438953472 2882994251797

noncomputable def ep1337 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 36) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz142 35) (@HPow.hPow Complex Complex Complex qz6 qz129 qz143)) Bool.false 737927888093 1099511627776 1478731652607979 216972127067176960 Bool.false 5706760909 137438953472 2882994251797 423773685678080

noncomputable def ep1338 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 35) (@HPow.hPow Complex Complex Complex qz6 qz129 qz143) Bool.false 923690280891 1099511627776 1452176892976097 216972127067176960 Bool.false 19966196655 549755813888 724869374695921 108486063533588480 Bool.true

noncomputable abbrev qz709 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 34) qz143)

noncomputable def ep1339 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 35) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz142 34) qz709) Bool.false 923690280891 1099511627776 1452176892976097 216972127067176960 Bool.false 19966196655 549755813888 724869374695921 108486063533588480

noncomputable def ep1340 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz142 34) qz709 Bool.false 806559381057 1099511627776 1425315702909707 216972127067176960 Bool.true 107840468979 1099511627776 1422843934428127 216972127067176960 Bool.false

noncomputable abbrev qz710 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 33) qz143)

noncomputable def ep1341 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz142 34) (@HAdd.hAdd Complex Complex Complex qz4 qz172 qz710) Bool.false 806559381057 1099511627776 1425315702909707 216972127067176960 Bool.true 107840468979 1099511627776 1422843934428127 216972127067176960

noncomputable def ep1342 := @Enclosure.Complex.IsNear.addLitP qz172 qz710 Bool.false 367559533959 549755813888 349534967361747 54243031766794240 Bool.false 17431680189 274877906944 348888342007097 54243031766794240 Bool.false

noncomputable abbrev qz213 := (@HMul.hMul Real Real Real qz269 qz439 qz666)

noncomputable def ep1343 := @Enclosure.Complex.IsNear.of_eq qz710 (Complex.mk (@HMul.hMul Real Real Real qz0 qz422 (Real.cos qz213)) (@HMul.hMul Real Real Real qz0 qz422 (@Neg.neg Real Real.instNeg (Real.sin qz213)))) Bool.false 71440313139 1099511627776 27175833462719 216972127067176960 Bool.true 177567189735 1099511627776 27290566399739 216972127067176960 (BSN.cpow_neg_s_mk qz145 140505 1000 33 qz146 rfl)

noncomputable def ep1344 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz666 140505 1000 0 1 15746868335186131 4503599627370496 40000000039467 7893400000000000000 442502747087065467231 900719925474099200 1124040001109062167 1578680000000000000000 qz147 (BSN.isNear_log_sfrac 33 1 15746868335186131 4503599627370496 40000000039467 7893400000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz667) Bool.false 66047152845744529997824 18889465931478580854784 1000000000986675 197335000000000000000 15746868335186131 4503599627370496 40000000039467 7893400000000000000 (BSN.log_rat_reduce_isNear 33 1 5 66 64 16133 524288 24973259072661432 36028797018963968 197335 1000000000000000 rfl rfl rfl rfl (ep708 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1345 := nat_lit 1516856912291624201584145122605511406166873643938293137321260970000598318562241

noncomputable def ep1346 := nat_lit 1798049007900862512773313412195601810516593417819831269573835427189736192961

noncomputable def ep1347 := nat_lit 4546974638859070879726888740992143014879587744979239749424635239147415483300801

noncomputable def ep1348 := BSN.cos_dyadic_bound_f 2551820903 2147483648 3 2 1048576 395056 ep1345 ep72 ep1346 ep1347 ep75 ep1346 391383 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2551820903) qz20 0 2 ep1345 ep72 ep1346 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2551820903) qz21 0 2 ep1347 ep75 ep1346 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz492 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 515140997) qz24)

noncomputable def ep1349 := @Enclosure.Real.IsNear.cos_image qz213 qz492 Bool.false 515140997 1048576 747 1048576 Bool.false 391383 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz213 Bool.false 442502747087065467231 900719925474099200 1124040001109062167 1578680000000000000000 515140997 1048576 747 1048576 (ep1344 rfl) rfl) (Enclosure.sfrac_false_div 515140997 1048576) (BSN.cos_reduce0 qz492 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 179568432330306092007424) qz25) 226375608064910080 72057594037927936 Bool.false 391383 1048576 78 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q0 515140997 1048576 226375608064910080 72057594037927936 78 179568432330306092007424 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 391383 1048576 179568432330306092007424 151115727451828646838272 2551820903 2147483648 395056 394670 (ep1348 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1350 := nat_lit 2728904002918602872841242569960164049651959284354671782162610677659325184457665

noncomputable def ep1351 := nat_lit 7144218404488310889563526128180684393776199831585765416941813184130401624505281

noncomputable def ep1352 := BSN.sin_dyadic_bound_f 2551820903 2147483648 3 2 1048576 395056 ep1350 ep79 ep1346 ep1351 ep81 ep1346 972795 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2551820903) qz15 0 2 ep1350 ep79 ep1346 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2551820903) qz16 0 2 ep1351 ep81 ep1346 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1353 := @Enclosure.Real.IsNear.sin_image qz213 qz492 Bool.false 515140997 1048576 747 1048576 Bool.false 972795 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz213 Bool.false 442502747087065467231 900719925474099200 1124040001109062167 1578680000000000000000 515140997 1048576 747 1048576 (ep1344 rfl) rfl) (Enclosure.sfrac_false_div 515140997 1048576) (BSN.sin_reduce0 qz492 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 179568432330306092007424) qz25) 226375608064910080 72057594037927936 Bool.false 972795 1048576 78 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q0 515140997 1048576 226375608064910080 72057594037927936 78 179568432330306092007424 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 972795 1048576 179568432330306092007424 151115727451828646838272 2551820903 2147483648 395056 394670 (ep1352 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1354 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz422 (Real.cos qz213)) (@HMul.hMul Real Real Real qz0 qz422 (@Neg.neg Real Real.instNeg (Real.sin qz213))) Bool.false 71440313139 1099511627776 27175833462719 216972127067176960 Bool.true 177567189735 1099511627776 27290566399739 216972127067176960 (@Enclosure.Real.IsNear.mulLit_ff qz422 (Real.cos qz213) 182533 1048576 1 1048576 391383 1048576 148457821 206920744960 71440313139 1099511627776 27175833462719 216972127067176960 qz426 (@Enclosure.Real.IsNear.recentre' (Real.cos qz213) Bool.false 391383 1048576 148457821 206920744960 391383 1048576 148457821 206920744960 (ep1349 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz422 (@Neg.neg Real Real.instNeg (Real.sin qz213)) 182533 1048576 1 1048576 972795 1048576 148457821 206920744960 177567189735 1099511627776 27290566399739 216972127067176960 qz426 (@Enclosure.Real.IsNear.neg (Real.sin qz213) Bool.false 972795 1048576 148457821 206920744960 (@Enclosure.Real.IsNear.recentre' (Real.sin qz213) Bool.false 972795 1048576 148457821 206920744960 972795 1048576 148457821 206920744960 (ep1353 rfl rfl) rfl)) rfl)

noncomputable def ep1355 := @ep1342 71440313139 1099511627776 27175833462719 216972127067176960 Bool.true 177567189735 1099511627776 27290566399739 216972127067176960 Bool.false 443410708981992564719616 806559381057 1099511627776 1425315702909707 216972127067176960 Bool.true 29642962396806880690176 107840468979 1099511627776 1422843934428127 216972127067176960 EMRow48.d16 (ep1343 ep1354) rfl rfl

noncomputable abbrev qz214 := (@HMul.hMul Real Real Real qz269 qz439 qz668)

noncomputable def ep1356 := @Enclosure.Complex.IsNear.of_eq qz709 (Complex.mk (@HMul.hMul Real Real Real qz0 qz427 (Real.cos qz214)) (@HMul.hMul Real Real Real qz0 qz427 (@Neg.neg Real Real.instNeg (Real.sin qz214)))) Bool.false 58565449917 549755813888 2686119006639 21697212706717696 Bool.false 147772862289 1099511627776 5378962992743 43394425413435392 (BSN.cpow_neg_s_mk qz145 140505 1000 34 qz146 rfl)

noncomputable def ep1357 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz668 140505 1000 0 1 15881309401485523 4503599627370496 40000000039467 7893400000000000000 446280675491144681823 900719925474099200 1124040001109062167 1578680000000000000000 qz147 (BSN.isNear_log_sfrac 34 1 15881309401485523 4503599627370496 40000000039467 7893400000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz669) Bool.false 66611039547888335060992 18889465931478580854784 1000000000986675 197335000000000000000 15881309401485523 4503599627370496 40000000039467 7893400000000000000 (BSN.log_rat_reduce_isNear 34 1 5 68 64 31784 524288 24973259072661432 36028797018963968 197335 1000000000000000 rfl rfl rfl rfl (ep719 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1358 := nat_lit 4291758084703692397681416601600000000

noncomputable def ep1359 := BSN.sin_dyadic_bound_f 1439324800 2147483648 2 1 1048576 395056 ep1358 ep58 ep1358 ep1358 ep59 ep1358 651346 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1439324800) qz15 0 1 ep1358 ep58 ep1358 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1439324800) qz16 0 1 ep1358 ep59 ep1358 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz493 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 129884771) qz31)

noncomputable def ep1360 := @Enclosure.Real.IsNear.cos_image qz214 qz493 Bool.false 129884771 262144 187 262144 Bool.false 651346 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz214 Bool.false 446280675491144681823 900719925474099200 1124040001109062167 1578680000000000000000 129884771 262144 187 262144 (ep1357 rfl) rfl) (Enclosure.sfrac_false_div 129884771 262144) (BSN.cos_reduce3 qz493 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 25320869675617340096512) qz321) 226375608064910080 72057594037927936 Bool.false 651346 1048576 78 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q3 129884771 262144 226375608064910080 72057594037927936 78 25320869675617340096512 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 651346 1048576 25320869675617340096512 37778931862957161709568 1439324800 2147483648 395056 394670 (ep1359 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1361 := nat_lit 153361427115537444686921125135542850329541238568410671442054619332608000000000

noncomputable def ep1362 := nat_lit 18419187457619506129292308103531835641735324655336093122560000000000000000

noncomputable def ep1363 := nat_lit 460047442971697095048504790790421487317340245055921342139918737997824000000000

noncomputable def ep1364 := BSN.cos_dyadic_bound_f 1439324800 2147483648 3 2 1048576 395056 ep1361 ep72 ep1362 ep1363 ep75 ep1362 821741 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1439324800) qz20 0 2 ep1361 ep72 ep1362 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1439324800) qz21 0 2 ep1363 ep75 ep1362 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1365 := @Enclosure.Real.IsNear.sin_image qz214 qz493 Bool.false 129884771 262144 187 262144 Bool.true 821741 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz214 Bool.false 446280675491144681823 900719925474099200 1124040001109062167 1578680000000000000000 129884771 262144 187 262144 (ep1357 rfl) rfl) (Enclosure.sfrac_false_div 129884771 262144) (BSN.sin_reduce3 qz493 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 25320869675617340096512) qz321) 226375608064910080 72057594037927936 Bool.false 821741 1048576 78 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q3 129884771 262144 226375608064910080 72057594037927936 78 25320869675617340096512 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 821741 1048576 25320869675617340096512 37778931862957161709568 1439324800 2147483648 395056 394670 (ep1364 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1366 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz427 (Real.cos qz214)) (@HMul.hMul Real Real Real qz0 qz427 (@Neg.neg Real Real.instNeg (Real.sin qz214))) Bool.false 58565449917 549755813888 2686119006639 21697212706717696 Bool.false 147772862289 1099511627776 5378962992743 43394425413435392 (@Enclosure.Real.IsNear.mulLit_ff qz427 (Real.cos qz214) 179829 1048576 1 1048576 325673 524288 37163789 51730186240 58565449917 549755813888 2686119006639 21697212706717696 qz431 (@Enclosure.Real.IsNear.recentre' (Real.cos qz214) Bool.false 651346 1048576 37163789 51730186240 325673 524288 37163789 51730186240 (ep1360 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz427 (@Neg.neg Real Real.instNeg (Real.sin qz214)) 179829 1048576 1 1048576 821741 1048576 37163789 51730186240 147772862289 1099511627776 5378962992743 43394425413435392 qz431 (@Enclosure.Real.IsNear.neg (Real.sin qz214) Bool.true 821741 1048576 37163789 51730186240 (@Enclosure.Real.IsNear.recentre' (Real.sin qz214) Bool.true 821741 1048576 37163789 51730186240 821741 1048576 37163789 51730186240 (ep1365 rfl rfl) rfl)) rfl)

noncomputable def ep1367 := @ep1340 58565449917 549755813888 2686119006639 21697212706717696 Bool.false 147772862289 1099511627776 5378962992743 43394425413435392 Bool.false 507804102151667038814208 923690280891 1099511627776 1452176892976097 216972127067176960 Bool.false 43906130769269552578560 19966196655 549755813888 724869374695921 108486063533588480 (ep1341 (BSN.head_sum_c_succ qz142 33 34 rfl rfl) (ep1355 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1356 ep1366) rfl rfl

noncomputable abbrev qz215 := (@HMul.hMul Real Real Real qz269 qz439 qz670)

noncomputable def ep1368 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz129 qz143) (Complex.mk (@HMul.hMul Real Real Real qz0 qz432 (Real.cos qz215)) (@HMul.hMul Real Real Real qz0 qz432 (@Neg.neg Real Real.instNeg (Real.sin qz215)))) Bool.true 92881196399 549755813888 13277379815941 108486063533588480 Bool.false 2860846981 549755813888 13177153764111 108486063533588480 (BSN.cpow_neg_s_mk qz145 140505 1000 35 qz146 rfl)

noncomputable def ep1369 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz136 140505 1000 0 1 16011859227414739 4503599627370496 40000000039467 7893400000000000000 449949256149581580639 900719925474099200 1124040001109062167 1578680000000000000000 qz147 (BSN.isNear_log_sfrac 35 1 16011859227414739 4503599627370496 40000000039467 7893400000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz434) Bool.false 67158605204982549446656 18889465931478580854784 1000000000986675 197335000000000000000 16011859227414739 4503599627370496 40000000039467 7893400000000000000 (BSN.log_rat_reduce_isNear 35 1 5 70 64 46982 524288 24973259072661432 36028797018963968 197335 1000000000000000 rfl rfl rfl rfl (ep742 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1370 := BSN.cos_dyadic_bound_f 66124442 2147483648 1 0 1048576 395056 0 1 1 0 1 1 1048078 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 66124442) qz20 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 66124442) qz21 0 0 rfl) rfl rfl

noncomputable abbrev qz494 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 261904937) qz17)

noncomputable def ep1371 := @Enclosure.Real.IsNear.cos_image qz215 qz494 Bool.false 261904937 524288 187 262144 Bool.true 1048078 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz215 Bool.false 449949256149581580639 900719925474099200 1124040001109062167 1578680000000000000000 261904937 524288 187 262144 (ep1369 rfl) rfl) (Enclosure.sfrac_false_div 261904937 524288) (BSN.cos_reduce2 qz494 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2326546989070201913344) qz19) 226375608064910080 72057594037927936 Bool.false 1048078 1048576 79 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q2 261904937 524288 226375608064910080 72057594037927936 79 2326546989070201913344 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1048078 1048576 2326546989070201913344 75557863725914323419136 66124442 2147483648 395056 394670 (ep1370 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1372 := BSN.sin_dyadic_bound_f 66124442 2147483648 1 0 1048576 395056 0 1 1 0 1 1 32282 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 66124442) qz15 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 66124442) qz16 0 0 rfl) rfl rfl

noncomputable def ep1373 := @Enclosure.Real.IsNear.sin_image qz215 qz494 Bool.false 261904937 524288 187 262144 Bool.true 32282 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz215 Bool.false 449949256149581580639 900719925474099200 1124040001109062167 1578680000000000000000 261904937 524288 187 262144 (ep1369 rfl) rfl) (Enclosure.sfrac_false_div 261904937 524288) (BSN.sin_reduce2 qz494 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2326546989070201913344) qz19) 226375608064910080 72057594037927936 Bool.false 32282 1048576 79 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q2 261904937 524288 226375608064910080 72057594037927936 79 2326546989070201913344 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 32282 1048576 2326546989070201913344 75557863725914323419136 66124442 2147483648 395056 394670 (ep1372 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1374 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz432 (Real.cos qz215)) (@HMul.hMul Real Real Real qz0 qz432 (@Neg.neg Real Real.instNeg (Real.sin qz215))) Bool.true 92881196399 549755813888 13277379815941 108486063533588480 Bool.false 2860846981 549755813888 13177153764111 108486063533588480 (@Enclosure.Real.IsNear.mulLit_ft qz432 (Real.cos qz215) 177241 1048576 1 1048576 524039 524288 37163789 51730186240 92881196399 549755813888 13277379815941 108486063533588480 qz436 (@Enclosure.Real.IsNear.recentre' (Real.cos qz215) Bool.true 1048078 1048576 37163789 51730186240 524039 524288 37163789 51730186240 (ep1371 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz432 (@Neg.neg Real Real.instNeg (Real.sin qz215)) 177241 1048576 1 1048576 16141 524288 37163789 51730186240 2860846981 549755813888 13177153764111 108486063533588480 qz436 (@Enclosure.Real.IsNear.neg (Real.sin qz215) Bool.true 16141 524288 37163789 51730186240 (@Enclosure.Real.IsNear.recentre' (Real.sin qz215) Bool.true 32282 1048576 37163789 51730186240 16141 524288 37163789 51730186240 (ep1373 rfl rfl) rfl)) rfl)

noncomputable def ep1375 := @ep1338 92881196399 549755813888 13277379815941 108486063533588480 Bool.false 2860846981 549755813888 13177153764111 108486063533588480 Bool.false 405680146709220199235584 737927888093 1099511627776 1478731652607979 216972127067176960 Bool.false 12549299952766070816768 5706760909 137438953472 2882994251797 423773685678080 (ep1339 (BSN.head_sum_c_succ qz142 34 35 rfl rfl) (ep1367 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1368 ep1374) rfl rfl

noncomputable def ep1376 := @Enclosure.Complex.IsNear.mul qz210 (@HAdd.hAdd Complex Complex Complex qz4 qz211 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz212 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1))))) Bool.false 47868275313650624107025 750175054713340783755264 ep1331 ep1213 Bool.true

noncomputable def ep1377 := nat_lit 8902002831701886292433077

noncomputable abbrev qz216 := (Complex.re qz490)

noncomputable abbrev qz217 := (Complex.im qz490)

noncomputable def ep1378 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 qz216 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz211 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz212 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz217 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz211 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz212 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1))))))) 41398965018215779395845 750175054713340783755264 ep1377

noncomputable def ep1379 := nat_lit 148035794421857103562345021440

noncomputable def ep1380 := nat_lit 274567464986009910902784000

noncomputable def ep1381 := nat_lit 997488501456975469607596473049525396281753600

noncomputable def ep1382 := @Enclosure.Real.IsNear.mulLit_ff qz216 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz211 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz212 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))))) 121295133965 1099511627776 26082043972669 216972127067176960 341307715033

noncomputable abbrev qz711 := (Real.log (Enclosure.sfrac Bool.false 36 1))

noncomputable abbrev qz218 := (@HMul.hMul Real Real Real qz269 qz439 qz711)

noncomputable abbrev qz219 := (Real.sin (@HMul.hMul Real Real Real qz269 qz439 qz711))

noncomputable abbrev qz495 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 36)))

noncomputable abbrev qz712 := (@Neg.neg Real Real.instNeg qz219)

noncomputable def ep1383 := @Enclosure.Complex.IsNear.of_eq qz210 (Complex.mk (@HMul.hMul Real Real Real qz0 qz495 (Real.cos qz218)) (@HMul.hMul Real Real Real qz0 qz495 qz712)) Bool.false 121295133965 1099511627776 26082043972669 216972127067176960 Bool.true 8585232375 68719476736 6525046984811 54243031766794240 (BSN.cpow_neg_s_mk qz145 140505 1000 36 qz146 rfl)

noncomputable abbrev qz496 := (Real.sqrt (@Nat.cast Real Real.instNatCast 36))

noncomputable abbrev qz497 := (@Nat.cast Real Real.instNatCast 36)

noncomputable abbrev qz713 := (@HDiv.hDiv Real Real Real qz1 qz497 qz14)

noncomputable def ep1384 := @Enclosure.Real.IsNear.inv_image qz496 6291457 1048576 1 1048576 87381 87382 524288 (@Enclosure.Real.IsNear.of_eq qz496 (Real.sqrt qz713) Bool.false 6291457 1048576 1 1048576 (BSN.sqrt_natCast_div_one 36) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz713) Bool.false 6291457 1048576 1 1048576 6291457 1048576 1 1048576 (BSN.sqrt_enclosure 36 1 3145728 3145729 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep1385 := BSN.log_dyadic_bound 4 68 3 2 320720640 524288 197335 370688 768 61752 72 64 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 4) (BSN.artanhQ 68) 0 2 370688 320720640 768 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1386 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz711 140505 1000 0 1 16138732561338579 4503599627370496 40000000039467 7893400000000000000 453514523706175408479 900719925474099200 1124040001109062167 1578680000000000000000 qz147 (BSN.isNear_log_sfrac 36 1 16138732561338579 4503599627370496 40000000039467 7893400000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz713) Bool.false 67690750536952647254016 18889465931478580854784 1000000000986675 197335000000000000000 16138732561338579 4503599627370496 40000000039467 7893400000000000000 (BSN.log_rat_reduce_isNear 36 1 5 72 64 61752 524288 24973259072661432 36028797018963968 197335 1000000000000000 rfl rfl rfl rfl (ep1385 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1387 := nat_lit 392030744849122685698155282517485018678313624855000627729619331762594486313216

noncomputable def ep1388 := nat_lit 120313997575723416574509515435446412248490471582639087736906815069166919936

noncomputable def ep1389 := nat_lit 1175851606552216610261316828521584163210443893621836605013384181657645125099776

noncomputable def ep1390 := BSN.cos_dyadic_bound_f 1819866454 2147483648 3 2 1048576 395056 ep1387 ep72 ep1388 ep1389 ep75 ep1388 694055 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1819866454) qz20 0 2 ep1387 ep72 ep1388 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1819866454) qz21 0 2 ep1389 ep75 ep1388 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz498 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 65995049) qz553)

noncomputable def ep1391 := @Enclosure.Real.IsNear.cos_image qz218 qz498 Bool.false 65995049 131072 747 1048576 Bool.false 694055 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 453514523706175408479 900719925474099200 1124040001109062167 1578680000000000000000 65995049 131072 747 1048576 (ep1386 rfl) rfl) (Enclosure.sfrac_false_div 65995049 131072) (BSN.cos_reduce0 qz498 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16007714619477907734528) qz305) 226375608064910080 72057594037927936 Bool.false 694055 1048576 80 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q0 65995049 131072 226375608064910080 72057594037927936 80 16007714619477907734528 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 694055 1048576 16007714619477907734528 18889465931478580854784 1819866454 2147483648 395056 394670 (ep1390 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1392 := nat_lit 10968773749864814153655564288687901456

noncomputable def ep1393 := BSN.sin_dyadic_bound_f 1819866454 2147483648 2 1 1048576 395056 ep1392 ep58 ep1392 ep1392 ep59 ep1392 786000 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1819866454) qz15 0 1 ep1392 ep58 ep1392 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1819866454) qz16 0 1 ep1392 ep59 ep1392 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1394 := @Enclosure.Real.IsNear.sin_image qz218 qz498 Bool.false 65995049 131072 747 1048576 Bool.false 786000 1048576 1 197335 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 453514523706175408479 900719925474099200 1124040001109062167 1578680000000000000000 65995049 131072 747 1048576 (ep1386 rfl) rfl) (Enclosure.sfrac_false_div 65995049 131072) (BSN.sin_reduce0 qz498 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16007714619477907734528) qz305) 226375608064910080 72057594037927936 Bool.false 786000 1048576 80 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q0 65995049 131072 226375608064910080 72057594037927936 80 16007714619477907734528 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 786000 1048576 16007714619477907734528 18889465931478580854784 1819866454 2147483648 395056 394670 (ep1393 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1395 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz495 (Real.cos qz218)) (@HMul.hMul Real Real Real qz0 qz495 qz712) Bool.false 121295133965 1099511627776 26082043972669 216972127067176960 Bool.true 8585232375 68719476736 6525046984811 54243031766794240 (@Enclosure.Real.IsNear.mulLit_ff qz495 (Real.cos qz218) 174763 1048576 1 1048576 694055 1048576 148457821 206920744960 121295133965 1099511627776 26082043972669 216972127067176960 (@Enclosure.Real.IsNear.recentre' qz495 Bool.false 174763 1048576 1 1048576 174763 1048576 1 1048576 (ep1384 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' (Real.cos qz218) Bool.false 694055 1048576 148457821 206920744960 694055 1048576 148457821 206920744960 (ep1391 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz495 qz712 174763 1048576 1 1048576 49125 65536 148457821 206920744960 8585232375 68719476736 6525046984811 54243031766794240 (@Enclosure.Real.IsNear.recentre' qz495 Bool.false 174763 1048576 1 1048576 174763 1048576 1 1048576 (ep1384 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg qz219 Bool.false 49125 65536 148457821 206920744960 (@Enclosure.Real.IsNear.recentre' qz219 Bool.false 786000 1048576 148457821 206920744960 49125 65536 148457821 206920744960 (ep1394 rfl rfl) rfl)) rfl)

noncomputable def ep1396 := @ep1382 682280237664 0 1 41398965018215779395845 750175054713340783755264 ep1377 ep1379 (@Enclosure.Complex.IsNear.re_isNear qz210 Bool.false 121295133965 1099511627776 26082043972669 216972127067176960 Bool.true 8585232375 68719476736 6525046984811 54243031766794240 (ep1383 ep1395))

noncomputable def ep1397 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz211 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz212 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1))))) Bool.false 341307715033 682280237664 0 1 Bool.false

noncomputable def ep1398 := @Enclosure.Complex.IsNear.addLitP qz211 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz212 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) Bool.false 788236201 1579352402 0 1 Bool.true 202327200

noncomputable def ep1399 := @ep1398 789676201 0 1 Bool.false 1 864 0 1 Bool.false 9367 28800 0 1 Bool.false 682615430066 341307715033 682280237664 0 1 Bool.false 1569873614767 1569873614767 22742674588800 0 1

noncomputable abbrev qz220 := (@HDiv.hDiv Complex Complex Complex qz396 qz491 (@HSub.hSub Complex Complex Complex qz388 qz437 (1 : Complex)))

noncomputable def ep1400 := @Enclosure.Complex.IsNear.addLitP qz220 qz103 Bool.true 72000000 78967620100 0 1 Bool.true 20232720000 78967620100 0 1

noncomputable def ep1401 := @Enclosure.Complex.IsNear.of_eq qz220 (Complex.mk (Enclosure.sfrac Bool.true 72000000 78967620100) (Enclosure.sfrac Bool.true 20232720000 78967620100)) Bool.true 72000000 78967620100 0 1 Bool.true 20232720000 78967620100 0 1

noncomputable def ep1402 := @ep1400 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 78823620100 788236201 1579352402 0 1 Bool.true 20232720000 202327200 789676201 0 1 (ep1401 (BSN.N_div_s_sub_one_mk qz145 140505 1000 36 qz146 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 72000000 78967620100) (Enclosure.sfrac Bool.true 20232720000 78967620100) Bool.true 72000000 78967620100 0 1 Bool.true 20232720000 78967620100 0 1 (Enclosure.Real.IsNear.const Bool.true 72000000 78967620100) (Enclosure.Real.IsNear.const Bool.true 20232720000 78967620100))) qz104 rfl

noncomputable abbrev qz221 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz421 qz491 1))

noncomputable def ep1403 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz212 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz212 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1))) qz221)) Bool.false 1 864 0 1

noncomputable def ep1404 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz212 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1))) qz221) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1405 := @ep1404 0 1 0 1 Bool.false 1 864 0 1 Bool.false 9367 28800 0 1 Bool.false 1 1 864 0 1 Bool.false 9367 9367 28800 0

noncomputable def ep1406 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz212 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1407 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1))) qz221 Bool.false 1 864 0 1 Bool.false 9367 28800 0 1

noncomputable def ep1408 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz221)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz221)) 1 864 0 1 0 1 0

noncomputable def ep1409 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz221) 1 24 0 1 1 36 0 1 1

noncomputable def ep1410 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz138)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz138)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep1411 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz138)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep1412 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)) qz142 Bool.false 1 2 0 1 Bool.false 140505 1000 0 1 (BSN.ascPochhammer_one_eval qz142)

noncomputable def ep1413 := ep1412 (@Enclosure.Complex.IsNear.of_eq qz142 (Complex.mk qz98 qz145) Bool.false 1 2 0 1 Bool.false 140505 1000 0 1 (BSN.s_crit_mk qz145 Bool.false 140505 1000 qz146) (@Enclosure.Complex.IsNear.mk qz98 qz145 Bool.false 1 2 0 1 Bool.false 140505 1000 0 1 qz402 qz147))

noncomputable def ep1414 := @ep1411 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz138) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep769) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 140505 1000 0 1 ep1413)

noncomputable def ep1415 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz138)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 140505 1000 0 1 0 1 0

noncomputable def ep1416 := @ep1415 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz138) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep769) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 140505 1000 0 1 ep1413)

noncomputable def ep1417 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz138)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz138)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)))) 9367 800 0 1 0 1 0 1 9367

noncomputable def ep1418 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz138)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 140505 1000 0 1 9367 800 0

noncomputable def ep1419 := @ep1418 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz138) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep769) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 140505 1000 0 1 ep1413)

noncomputable def ep1420 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz138)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep1421 := @ep1420 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz138) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep769) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 140505 1000 0 1 ep1413)

noncomputable def ep1422 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 9367 800 0 1 (@ep1410 1 24 0 1 (ep1414 rfl) (ep1416 rfl) rfl rfl) (@ep1417 9367 800 0 1 (ep1419 rfl) (ep1421 rfl) rfl rfl)

noncomputable def ep1423 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 9367 800 0 1 ep1422

noncomputable abbrev qz222 := (@Enclosure.Complex.IsNear.of_eq (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz421 qz491 1)) (Complex.mk (Enclosure.sfrac Bool.false 1 36) qz547) Bool.false 1 36 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 36 1 36 EMRow48.d17 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 36) qz547 Bool.false 1 36 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 36) qz549))

noncomputable def ep1424 := @ep1409 864 0 1 ep1423 (@Enclosure.Complex.IsNear.re_isNear qz221 Bool.false 1 36 0 1 Bool.false 0 1 0 1 qz222)

noncomputable def ep1425 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz221) 9367 800 0 1 0 1 0 1 0

noncomputable def ep1426 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 9367 800 0 1 ep1422

noncomputable def ep1427 := @ep1425 1 0 1 ep1426 (@Enclosure.Complex.IsNear.im_isNear qz221 Bool.false 1 36 0 1 Bool.false 0 1 0 1 qz222)

noncomputable def ep1428 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz221)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz221)) 0 1 0 1 9367 28800 0

noncomputable def ep1429 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz221) 1 24 0 1 0 1 0 1 0

noncomputable def ep1430 := @ep1429 1 0 1 ep1423 (@Enclosure.Complex.IsNear.im_isNear qz221 Bool.false 1 36 0 1 Bool.false 0 1 0 1 qz222)

noncomputable def ep1431 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz138) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz221) 9367 800 0 1 1 36 0 1 9367

noncomputable def ep1432 := @ep1431 28800 0 1 ep1426 (@Enclosure.Complex.IsNear.re_isNear qz221 Bool.false 1 36 0 1 Bool.false 0 1 0 1 qz222)

noncomputable def ep1433 := @ep1405 1 (@ep1406 0 1 0 1 (BSN.bern_sum_base qz142 36) qz119) (ep1407 (@ep1408 1 1 1 864 0 1 (ep1424 rfl) (ep1427 rfl) rfl rfl) (@ep1428 1 9367 9367 28800 0 1 (ep1430 rfl) (ep1432 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep1434 := ep1399 (ep1402 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep1403 Bool.false 9367 28800 0 1 (BSN.bern_sum_succ qz142 36 0 1 1 rfl rfl) (ep1433 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep1435 := @Enclosure.Real.IsNear.mulLit_tf qz217 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz211 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz212 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))))) 8585232375 68719476736 6525046984811 54243031766794240 1569873614767

noncomputable def ep1436 := @ep1435 22742674588800 0 1 179703063762079019755 20838195964259466215424 2279879611967451305209 ep1380 (@Enclosure.Complex.IsNear.im_isNear qz210 Bool.false 121295133965 1099511627776 26082043972669 216972127067176960 Bool.true 8585232375 68719476736 6525046984811 54243031766794240 (ep1383 ep1395))

noncomputable def ep1437 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz211 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz212 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1))))) Bool.false 341307715033 682280237664 0 1 Bool.false

noncomputable def ep1438 := nat_lit 40945512651885727982803123

noncomputable def ep1439 := @Enclosure.Real.IsNear.addLit_ft_n (@HMul.hMul Real Real Real qz0 qz216 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz211 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz212 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz217 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz211 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz212 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1))))))) 38083606082256413452231 ep1326 ep1438

noncomputable def ep1440 := nat_lit 4934526480728570118744834048000

noncomputable def ep1441 := nat_lit 8237023949580297327083520

noncomputable def ep1442 := nat_lit 4289621387481242304456449782510734861026721792

noncomputable def ep1443 := @Enclosure.Real.IsNear.mulLit_ff qz216 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz211 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz212 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))))) 121295133965 1099511627776 26082043972669 216972127067176960 1569873614767

noncomputable def ep1444 := @ep1443 22742674588800 0 1 38083606082256413452231 ep1326 ep1438 ep1440 (@Enclosure.Complex.IsNear.re_isNear qz210 Bool.false 121295133965 1099511627776 26082043972669 216972127067176960 Bool.true 8585232375 68719476736 6525046984811 54243031766794240 (ep1383 ep1395))

noncomputable def ep1445 := @Enclosure.Real.IsNear.mulLit_tf qz217 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz211 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz212 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))))) 8585232375 68719476736 6525046984811 54243031766794240 341307715033

noncomputable def ep1446 := @ep1445 682280237664 0 1 976735348312861931125 15628646973194599661568 495670793872425699391 ep1441 (@Enclosure.Complex.IsNear.im_isNear qz210 Bool.false 121295133965 1099511627776 26082043972669 216972127067176960 Bool.true 8585232375 68719476736 6525046984811 54243031766794240 (ep1383 ep1395))

noncomputable abbrev qz714 := (ep1434 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep1447 := @ep1376 274471705377859404507769 ep1326 ep1332 ep1328 (@ep1378 ep1379 179703063762079019755 20838195964259466215424 2279879611967451305209 ep1380 ep1381 47868275313650624107025 750175054713340783755264 ep1331 ep1213 (ep1396 (@ep1397 1569873614767 22742674588800 0 1 qz714) rfl) (ep1436 (@ep1437 1569873614767 22742674588800 0 1 qz714) rfl) rfl rfl) (@ep1439 ep1440 976735348312861931125 15628646973194599661568 495670793872425699391 ep1441 ep1442 274471705377859404507769 ep1326 ep1332 ep1328 (ep1444 (@ep1437 1569873614767 22742674588800 0 1 qz714) rfl) (ep1446 (@ep1397 1569873614767 22742674588800 0 1 qz714) rfl) rfl rfl)

noncomputable def ep1448 := @ep1335 ep1327 ep1328 (@ep1336 423773685678080 (BSN.head_sum_c_eq qz142 36) (ep1337 (BSN.head_sum_c_succ qz142 35 36 rfl rfl) (ep1375 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep1447 rfl rfl rfl

noncomputable def ep1449 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz142 1 36) Bool.false 551341890180636259841777 750175054713340783755264 ep1212 ep1213 Bool.true 66812495282705021757049 ep1326 ep1327 ep1328 (@ep1329 ep1213 Bool.true 66812495282705021757049 ep1326 ep1327 ep1328 (BSN.zetaApproximant_eq_folded' qz142 1 36 rfl) (ep1448 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep1450 := @Enclosure.Real.IsNear.mulLit_tt (Real.sin (@HSub.hSub Real Real Real qz391 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz181 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz182 (@Nat.cast Complex Complex.instNatCast j))))) qz183)) (Complex.im (zetaApproximant qz142 1 36)) 43 131072 38609943

noncomputable def ep1451 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz391 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz181 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz182 (@Nat.cast Complex Complex.instNatCast j))))) qz183)) Bool.true 344 1048576 38609943

noncomputable def ep1452 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz391 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz181 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz182 (@Nat.cast Complex Complex.instNatCast j))))) qz183) qz474 Bool.false 154827681 1048576 193

noncomputable def ep1453 := BSN.sin_dyadic_bound_f 704631 2147483648 1 0 1048576 395056 0 1 1 0 1 1 344 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 704631) qz15 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 704631) qz16 0 0 rfl) rfl rfl

noncomputable def ep1454 := @ep1452 524288 Bool.true 344 1048576 1 197335 (@ep1218 154827681 1048576 193 524288 ep1323 rfl) (Enclosure.sfrac_false_div 154827681 1048576) (BSN.sin_reduce2 qz474 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 49584050128459661312) qz25) 226375608064910080 72057594037927936 Bool.false 344 1048576 23 1000000000000000 394670 197335 (BSN.sin_reduce_arg_pos_rat_q2 154827681 1048576 226375608064910080 72057594037927936 23 49584050128459661312 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 344 1048576 49584050128459661312 151115727451828646838272 704631 2147483648 395056 394670 (ep1453 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1455 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz142 1 36) Bool.false 551341890180636259841777 750175054713340783755264 ep1212 ep1213 Bool.true 66812495282705021757049 ep1326 ep1327 ep1328 (@ep1329 ep1213 Bool.true 66812495282705021757049 ep1326 ep1327 ep1328 (BSN.zetaApproximant_eq_folded' qz142 1 36 rfl) (ep1448 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow48.d18 : Enclosure.Real.IsNear (hardyZApproximantEM 1 36 qz145) Bool.true ep1196 ep1197 ep1198 ep1199 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 36 qz145) ep1200 Bool.true ep1196 ep1197 ep1198 ep1199 (@Eq.refl Real ep1200) (@ep1201 Bool.true ep1196 ep1197 ep1198 ep1199 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz391 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz181 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz182 (@Nat.cast Complex Complex.instNatCast j))))) qz183) (zetaApproximant qz142 1 36)) (@ep1203 ep1204 ep1205 ep1206 ep1207 ep1208 ep1209 ep1199 ep1210 ep1196 ep1197 ep1198 ep1199 (@ep1211 103460372480 551341890180636259841777 750175054713340783755264 ep1212 ep1213 ep1202 ep1204 ep1205 ep1206 (@ep1214 103460372480 1048575 1048576 38609943 103460372480 (ep1325 rfl rfl) rfl) ep1449 rfl) (@ep1450 103460372480 66812495282705021757049 ep1326 ep1327 ep1328 ep1207 ep1208 ep1209 ep1199 (@ep1451 103460372480 43 131072 38609943 103460372480 (ep1454 rfl rfl) rfl) ep1455 rfl) rfl rfl))

theorem EMRow48.d19 : @Eq Nat (Nat.mul (BSN.factNat (Nat.succ (Nat.mul 2 1))) (Nat.pow 4 (Nat.mul 2 1))) 96 := @Eq.refl Nat 96

theorem EMRow48.d20 : @Eq Nat (Nat.mul (Nat.mul 2 1) (Nat.pow (Nat.succ (Nat.mul 4 2)) (Nat.mul 2 1))) 162 := @Eq.refl Nat 162

theorem EMRow48.d21 : @Eq Nat (BSN.factNat (Nat.mul 2 2)) 24 := @Eq.refl Nat 24

theorem EMRow48.d22 : @Eq Nat (Nat.pow 35 (Nat.succ (Nat.mul 2 3))) 64339296875 := @Eq.refl Nat 64339296875

noncomputable abbrev qz715 := (@HAdd.hAdd Complex Complex Complex qz720 qz719 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz499 := qz715

noncomputable abbrev qz223 := (@HDiv.hDiv Real Real Real qz272 (@Norm.norm Complex Complex.instNorm qz499) (@HAdd.hAdd Real Real Real qz411 (Complex.re qz273) qz290))

noncomputable abbrev qz224 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)

noncomputable abbrev qz225 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)))

noncomputable abbrev qz500 := (@HPow.hPow Complex Complex Complex qz538 (@Nat.cast Complex Complex.instNatCast 35) (@HSub.hSub Complex Complex Complex qz653 qz539 qz545))

noncomputable abbrev qz226 := qz500

noncomputable def ep1456 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 35))) (@HMul.hMul Real Real Real qz0 qz223 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226))) 1001163773 77309411328 996913 9663676416 2322683257900564019 4035225266123964416 293856131901

noncomputable def ep1457 := nat_lit 183605196722031406768508108800

noncomputable def ep1458 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 35)) 26561 1769472 1 1769472 113079 131072 1793 262144 1001163773 77309411328

noncomputable abbrev qz227 := (@HMul.hMul Real Real Real qz269 (2 : Real) Real.pi)

noncomputable abbrev qz716 := (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid)))

noncomputable abbrev qz501 := (@Inv.inv Real Real.instInv (@HPow.hPow Real Nat Real qz716 qz227 2))

noncomputable def ep1459 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 96 162) qz501 96 162 0 1 26561 1048576 1 1048576 26561 1769472 1 1769472

noncomputable def ep1460 := nat_lit 781950621441006189802102638025

noncomputable def ep1461 := nat_lit 19807040628566084398385987584

noncomputable def ep1462 := nat_lit 26986075409044041160201671

noncomputable def ep1463 := nat_lit 1073741824000000000000000000000000000000

noncomputable abbrev qz502 := (@HPow.hPow Real Nat Real qz716 qz227 1)

noncomputable def ep1464 := @Enclosure.Real.IsNear.mulLit_ff qz502 qz227 884279719003555 140737488355328 1 500000000000000 884279719003555 140737488355328 1 500000000000000 ep1460 ep1461 ep1462 ep1463

noncomputable def ep1465 := ep1464 (@Enclosure.Real.IsNear.of_eq qz502 qz227 Bool.false 884279719003555 140737488355328 1 500000000000000 (BSN.pow_one_r qz227) (@Enclosure.Real.IsNear.of_eq qz227 qz270 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz271)) (@Enclosure.Real.IsNear.of_eq qz227 qz270 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz271) rfl

noncomputable abbrev qz503 := (@HPow.hPow Real Nat Real qz716 qz227 2)

noncomputable def ep1466 := @Enclosure.Real.IsNear.inv_image qz503 ep1460 ep1461 ep1462 ep1463 13280 13281 524288 (@Enclosure.Real.IsNear.of_eq qz503 (@HMul.hMul Real Real Real qz0 qz502 qz227) Bool.false ep1460 ep1461 ep1462 ep1463 (BSN.pow_succ_r qz227 1 2 rfl) ep1465) rfl rfl rfl

noncomputable def ep1467 := ep1459 (Enclosure.Real.IsNear.const Bool.false 96 162) (@Enclosure.Real.IsNear.recentre' qz501 Bool.false 26561 1048576 1 1048576 26561 1048576 1 1048576 (ep1466 rfl rfl rfl) rfl)

noncomputable def ep1468 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 35)) (Real.sqrt (@HAdd.hAdd Real Real Real qz411 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 35)) (Complex.re (zetaApproximant qz5 1 35))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 35)) (Complex.im (zetaApproximant qz5 1 35))))) Bool.false 113079 131072 1793 262144

noncomputable def ep1469 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz411 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 35)) (Complex.re (zetaApproximant qz5 1 35))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 35)) (Complex.im (zetaApproximant qz5 1 35))))) Bool.false 904632 1048576 7172 1048576

noncomputable def ep1470 := nat_lit 190246368900825590208792896910826633611184021

noncomputable def ep1471 := nat_lit 255590953508411206890179181709728153600000000

noncomputable def ep1472 := nat_lit 563012129610232110412914682402459536162722812051665295925307803

noncomputable def ep1473 := nat_lit 47715662024567141215855304058441907736455480156838952960000000000

noncomputable def ep1474 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz411 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 35)) (Complex.re (zetaApproximant qz5 1 35))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 35)) (Complex.im (zetaApproximant qz5 1 35)))) ep1470 ep1471 ep1472 ep1473 448730 455902

noncomputable def ep1475 := nat_lit 36469824969323409928406362782940679577896535416154481

noncomputable def ep1476 := nat_lit 49013160181104392163470975360602451705723879424000000

noncomputable def ep1477 := nat_lit 183567124222921693160077650855883801777123911839437830021088013

noncomputable def ep1478 := nat_lit 15905220674855713738618434686147302578818493385612984320000000000

noncomputable def ep1479 := nat_lit 19675081482918878006042872497679199871063337596001

noncomputable def ep1480 := nat_lit 76583062782975612755423399000941330790193561600000000

noncomputable def ep1481 := nat_lit 106127215012646818385187326162139058890957556321998326396929

noncomputable def ep1482 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 35)) (Complex.re (zetaApproximant qz5 1 35))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 35)) (Complex.im (zetaApproximant qz5 1 35))) ep1475 ep1476 ep1477 ep1478 ep1479 ep1480 ep1481

noncomputable def ep1483 := nat_lit 411341914004889148412545724641740583934961035834818560000000000

noncomputable def ep1484 := nat_lit 2793935233230124936945058742940484913102243709956002477884598549172429733420628161998095732938113024000000

noncomputable def ep1485 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz5 1 35)) (Complex.re (zetaApproximant qz5 1 35)) ep550 ep551 ep552 ep553 ep550 ep551 ep552 ep553 ep1475

noncomputable def ep1486 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (zetaApproximant qz5 1 35)) (Complex.im (zetaApproximant qz5 1 35)) ep688 ep689 ep690 ep691 ep688 ep689 ep690 ep691 ep1479

noncomputable def ep1487 := @ep1456 4035225266123964416 ep1457 21374458065492963275 36317027395115679744 3749139845649701 36317027395115679744 (@ep1458 996913 9663676416 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) qz501) Bool.false 26561 1769472 1 1769472 (BSN.theta_err_eq 1 2 96 162 EMRow48.d19 EMRow48.d20 rfl) (ep1467 rfl)) (ep1468 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz5 1 35)) (@ep1469 113079 131072 1793 262144 (@ep1474 524288 (@ep1482 ep1483 ep1484 ep1470 ep1471 ep1472 ep1473 (@ep1485 ep1476 ep1477 ep1478 ep810 ep810 rfl) (@ep1486 ep1480 ep1481 ep1483 ep818 ep818 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz228 := (@Norm.norm Complex Complex.instNorm qz499)

noncomputable abbrev qz717 := (Enclosure.sfrac Bool.false 2 7)

noncomputable def ep1488 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz223 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz228 qz717) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226))) Bool.false 2322683257900564019 4035225266123964416 293856131901 4035225266123964416 (BSN.zrb_shape_eq qz228 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226)) qz12 3)

noncomputable def ep1489 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz228 qz717) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226)) 145251079 3670016 1 3670016 15990815861 1099511627776 1913 1099511627776

noncomputable def ep1490 := @Enclosure.Real.IsNear.mulLit_ff qz228 qz717 145251079 1048576 1 1048576 2 7 0 1 145251079 3670016

noncomputable abbrev qz504 := (Complex.re qz715)

noncomputable abbrev qz505 := (Complex.im qz715)

noncomputable abbrev qz229 := (@HAdd.hAdd Real Real Real qz411 (@HMul.hMul Real Real Real qz269 qz504 qz504) (@HMul.hMul Real Real Real qz269 qz505 qz505))

noncomputable abbrev qz230 := qz499

noncomputable def ep1491 := @Enclosure.Real.IsNear.of_eq qz228 (Real.sqrt qz229) Bool.false 145251079 1048576 1 1048576 (BSN.norm_eq_sqrt_mul_add qz230)

noncomputable def ep1492 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz229) Bool.false 145251079 1048576 1 1048576 145251079

noncomputable def ep1493 := @Enclosure.Real.IsNear.sqrt_image qz229 4797101621 250000 0 1 72625539 72625540 524288

noncomputable abbrev qz231 := (@HMul.hMul Real Real Real qz269 qz504 qz504)

noncomputable abbrev qz232 := (@HMul.hMul Real Real Real qz269 qz505 qz505)

noncomputable def ep1494 := @Enclosure.Real.IsNear.addLit_ff qz231 qz232 49 4 0 1 4794039121 250000 0 1

noncomputable abbrev qz233 := qz504

noncomputable def ep1495 := @Enclosure.Real.IsNear.mulLit_ff qz233 qz233 7 2 0 1 7 2 0 1 49 4

noncomputable abbrev qz506 := (Enclosure.sfrac Bool.false 7 2)

noncomputable def ep1496 := @Enclosure.Complex.IsNear.of_eq qz230 (Complex.mk qz506 qz12) Bool.false 7 2 0 1 Bool.false 138478 1000 0 1 (BSN.s_add_nat_mk qz12 Bool.false 138478 1000 3 qz13)

noncomputable abbrev qz507 := (ep1496 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz12 Bool.false 7 2 0 1 Bool.false 138478 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz18))

noncomputable def ep1497 := @ep1495 0 1 (@Enclosure.Complex.IsNear.re_isNear qz230 Bool.false 7 2 0 1 Bool.false 138478 1000 0 1 qz507)

noncomputable def ep1498 := ep1497 (@Enclosure.Complex.IsNear.re_isNear qz230 Bool.false 7 2 0 1 Bool.false 138478 1000 0 1 qz507)

noncomputable abbrev qz234 := qz505

noncomputable def ep1499 := @Enclosure.Real.IsNear.mulLit_ff qz234 qz234 138478 1000 0 1 138478 1000 0 1 4794039121 250000

noncomputable def ep1500 := @ep1499 0 1 (@Enclosure.Complex.IsNear.im_isNear qz230 Bool.false 7 2 0 1 Bool.false 138478 1000 0 1 qz507)

noncomputable def ep1501 := ep1500 (@Enclosure.Complex.IsNear.im_isNear qz230 Bool.false 7 2 0 1 Bool.false 138478 1000 0 1 qz507)

noncomputable def ep1502 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226)) (Real.sqrt (@HAdd.hAdd Real Real Real qz411 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226)) (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226)) (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226))))) Bool.false 15990815861 1099511627776

noncomputable def ep1503 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz411 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226)) (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226)) (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226))))) Bool.false 31981631722 2199023255552

noncomputable def ep1504 := nat_lit 20031612181733698283232960562668989800766289855217739265549741455729

noncomputable def ep1505 := nat_lit 94705306099042509099598777160015139673704428784844800000000000000000000

noncomputable def ep1506 := nat_lit 420169828984809836330566293740026575109688291509066454059095450531560607480248512879

noncomputable def ep1507 := nat_lit 8304756571102260082003463812429606504136351747476999817530441728000000000000000000000000000000

noncomputable def ep1508 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz411 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226)) (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226)) (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226)))) ep1504 ep1505 ep1506 ep1507

noncomputable def ep1509 := nat_lit 2556873513921667420487482755781630283193709167187159842878296351561

noncomputable def ep1510 := nat_lit 21045623577565002022133061591114475483045428618854400000000000000000000

noncomputable def ep1511 := nat_lit 6088404131374136476773650991515696864903950627867920890957114874221869165630000159

noncomputable def ep1512 := nat_lit 205055717804994076098850958331595222324354364135234563395813376000000000000000000000000000000

noncomputable def ep1513 := nat_lit 17051362738172389782078576323303307052789197205751039945194815747409

noncomputable def ep1514 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226)) (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226)) (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226))) ep1509 ep1510 ep1511 ep1512 ep1513

noncomputable def ep1515 := nat_lit 189410612198085018199197554320030279347408857569689600000000000000000000

noncomputable def ep1516 := nat_lit 347178923328314618042466857167281704162156582160831315950664596251149812544467012879

noncomputable def ep1517 := nat_lit 16609513142204520164006927624859213008272703494953999635060883456000000000000000000000000000000

noncomputable def ep1518 := nat_lit 843155539257066061428553655572543649450594806234436384059244300579441931857875344238505017509449993170367551504593715200000000000000000000

noncomputable def ep1519 := nat_lit 1599022674611485120227122152591331

noncomputable def ep1520 := nat_lit 145071098353755500964741120000000000

noncomputable def ep1521 := nat_lit 57860880678428683098273143209918641959

noncomputable def ep1522 := nat_lit 42959300043703536637930081615872000000000000000

noncomputable def ep1523 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226)) (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226)) ep1519 ep1520 ep1521 ep1522 ep1519 ep1520 ep1521

noncomputable def ep1524 := nat_lit 4129329574903460013490114355222903

noncomputable def ep1525 := nat_lit 435213295061266502894223360000000000

noncomputable def ep1526 := nat_lit 141960489117927308460625963557946519627

noncomputable def ep1527 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226) Bool.false ep1519 ep1520 ep1521 ep1522 Bool.true ep1524 ep1525 ep1526

noncomputable def ep1528 := nat_lit 128877900131110609913790244847616000000000000000

noncomputable def ep1529 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226 Bool.false ep1519 ep1520 ep1521 ep1522 Bool.true ep1524 ep1525 ep1526 ep1528

noncomputable def ep1530 := nat_lit 172026335365549025738041210481

noncomputable def ep1531 := nat_lit 580284393415022003858964480000000

noncomputable def ep1532 := nat_lit 5914310008980510790348095692013829

noncomputable def ep1533 := nat_lit 171837200174814146551720326463488000000000000

noncomputable def ep1534 := nat_lit 1642029258452872376661632455211581

noncomputable def ep1535 := nat_lit 56382303176183555400686119286915184709

noncomputable abbrev qz235 := (Complex.re qz500)

noncomputable abbrev qz236 := (Complex.im qz500)

noncomputable def ep1536 := @Enclosure.Real.IsNear.subLit_tt_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz235) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz236) ep1530 ep1531 ep1532 ep1533 ep1534 ep1520 ep1535

noncomputable def ep1537 := nat_lit 927887902793791748452707082060533455414836293753086284922880000000

noncomputable def ep1538 := nat_lit 4835703278458516698824704

noncomputable def ep1539 := nat_lit 1431976668123451221264336053862400000

noncomputable def ep1540 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz235 14381804863 120000000 0 1 11961387114083319887 ep1538 411235590061177065655483 ep1539 ep1530

noncomputable def ep1541 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) 14381804863 120000000 0 1 0 1 0 1 14381804863

noncomputable def ep1542 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 43145414589 500000 0 1 14381804863 120000000 0

noncomputable def ep1543 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (Complex.mk (Enclosure.sfrac Bool.true 1 720) qz10) Bool.true 1 720 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 2 1 30 24 Bool.true BSN.bern_real_2 EMRow48.d21 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 1 720) qz10 Bool.true 1 720 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.true 1 720) qz22)

noncomputable abbrev qz508 := (@HAdd.hAdd Complex Complex Complex qz537 qz536 qz546)

noncomputable abbrev qz237 := qz508

noncomputable def ep1544 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz78 (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) qz237) Bool.true 43145414589 500000 0 1 Bool.true 331834943636419 125000000 0 1

noncomputable abbrev qz238 := (Complex.re qz508)

noncomputable abbrev qz239 := (Complex.im qz508)

noncomputable def ep1545 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz238) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz239) 4793851621 100000 0 1 4794039121 125000 0 1

noncomputable def ep1546 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz238 4793851621 250000 0 1 5 2 0 1 4793851621 100000

noncomputable abbrev qz509 := (@HAdd.hAdd Complex Complex Complex qz537 qz536 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz240 := qz509

noncomputable def ep1547 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz78 (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz240) Bool.true 4793851621 250000 0 1 Bool.false 69239 250 0 1

noncomputable abbrev qz241 := (Complex.re qz509)

noncomputable abbrev qz242 := (Complex.im qz509)

noncomputable def ep1548 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz241) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz242) 3 4 0 1 4794039121 250000 0 1

noncomputable def ep1549 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz241 1 2 0 1 3 2 0 1 3 4

noncomputable def ep1550 := @ep1549 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 138478 1000 0 1 ep771)

noncomputable abbrev qz510 := (Enclosure.sfrac Bool.false 3 2)

noncomputable def ep1551 := @Enclosure.Complex.IsNear.of_eq qz240 (Complex.mk qz510 qz12) Bool.false 3 2 0 1 Bool.false 138478 1000 0 1 (BSN.s_add_nat_mk qz12 Bool.false 138478 1000 1 qz13)

noncomputable abbrev qz511 := (ep1551 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz12 Bool.false 3 2 0 1 Bool.false 138478 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz18))

noncomputable def ep1552 := ep1550 (@Enclosure.Complex.IsNear.re_isNear qz240 Bool.false 3 2 0 1 Bool.false 138478 1000 0 1 qz511)

noncomputable def ep1553 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz242 138478 1000 0 1 138478 1000 0 1 4794039121 250000

noncomputable def ep1554 := @ep1553 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 138478 1000 0 1 ep771)

noncomputable def ep1555 := ep1554 (@Enclosure.Complex.IsNear.im_isNear qz240 Bool.false 3 2 0 1 Bool.false 138478 1000 0 1 qz511)

noncomputable def ep1556 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz240 Bool.true 4793851621 250000 0 1 Bool.false 69239 250 0 1 (@ep1548 19175406484 4793851621 250000 0 1 (ep1552 rfl) (ep1555 rfl) rfl rfl)

noncomputable def ep1557 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz242) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz241) 69239 1000 0 1 207717 1000 0 1

noncomputable def ep1558 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz242 1 2 0 1 138478 1000 0 1 69239 1000

noncomputable def ep1559 := @ep1558 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 138478 1000 0 1 ep771)

noncomputable def ep1560 := ep1559 (@Enclosure.Complex.IsNear.im_isNear qz240 Bool.false 3 2 0 1 Bool.false 138478 1000 0 1 qz511)

noncomputable def ep1561 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz241 138478 1000 0 1 3 2 0 1 207717 1000

noncomputable def ep1562 := @ep1561 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 138478 1000 0 1 ep771)

noncomputable def ep1563 := ep1562 (@Enclosure.Complex.IsNear.re_isNear qz240 Bool.false 3 2 0 1 Bool.false 138478 1000 0 1 qz511)

noncomputable abbrev qz243 := (ep1547 (BSN.ascPochhammer_succ_eval_c 1 2 qz273 rfl) (ep1556 (@ep1557 276956000 69239 250 0 1 (ep1560 rfl) (ep1563 rfl) rfl rfl)))

noncomputable def ep1564 := @ep1546 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 4793851621 250000 0 1 Bool.false 69239 250 0 1 qz243)

noncomputable abbrev qz512 := (Enclosure.sfrac Bool.false 5 2)

noncomputable def ep1565 := @Enclosure.Complex.IsNear.of_eq qz237 (Complex.mk qz512 qz12) Bool.false 5 2 0 1 Bool.false 138478 1000 0 1 (BSN.s_add_nat_mk qz12 Bool.false 138478 1000 2 qz13)

noncomputable abbrev qz513 := (ep1565 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz12 Bool.false 5 2 0 1 Bool.false 138478 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz18))

noncomputable def ep1566 := ep1564 (@Enclosure.Complex.IsNear.re_isNear qz237 Bool.false 5 2 0 1 Bool.false 138478 1000 0 1 qz513)

noncomputable def ep1567 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz239 69239 250 0 1 138478 1000 0 1 4794039121 125000

noncomputable def ep1568 := @ep1567 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 4793851621 250000 0 1 Bool.false 69239 250 0 1 qz243)

noncomputable def ep1569 := ep1568 (@Enclosure.Complex.IsNear.im_isNear qz237 Bool.false 5 2 0 1 Bool.false 138478 1000 0 1 qz513)

noncomputable def ep1570 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) qz237 Bool.true 43145414589 500000 0 1 Bool.true 331834943636419 125000000 0 1 (@ep1545 1078635364725000 43145414589 500000 0 1 (ep1566 rfl) (ep1569 rfl) rfl rfl)

noncomputable def ep1571 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz239) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz238) 331921492386419 125000000 0 1 69239 100 0 1

noncomputable def ep1572 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz239 4793851621 250000 0 1 138478 1000 0 1 331921492386419 125000000

noncomputable def ep1573 := @ep1572 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 4793851621 250000 0 1 Bool.false 69239 250 0 1 qz243)

noncomputable def ep1574 := ep1573 (@Enclosure.Complex.IsNear.im_isNear qz237 Bool.false 5 2 0 1 Bool.false 138478 1000 0 1 qz513)

noncomputable def ep1575 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz238 69239 250 0 1 5 2 0 1 69239 100

noncomputable def ep1576 := @ep1575 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 4793851621 250000 0 1 Bool.false 69239 250 0 1 qz243)

noncomputable def ep1577 := ep1576 (@Enclosure.Complex.IsNear.re_isNear qz237 Bool.false 5 2 0 1 Bool.false 138478 1000 0 1 qz513)

noncomputable abbrev qz244 := (ep1544 (BSN.ascPochhammer_succ_eval_c 2 3 qz273 rfl) (ep1570 (@ep1571 33183494363641900 331834943636419 125000000 0 1 (ep1574 rfl) (ep1577 rfl) rfl rfl)))

noncomputable def ep1578 := @ep1542 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1543) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 43145414589 500000 0 1 Bool.true 331834943636419 125000000 0 1 qz244)

noncomputable def ep1579 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 331834943636419 125000000 0 1 0 1 0

noncomputable def ep1580 := @ep1579 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1543) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 43145414589 500000 0 1 Bool.true 331834943636419 125000000 0 1 qz244)

noncomputable def ep1581 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) 331834943636419 90000000000 0 1 0 1 0 1 331834943636419

noncomputable def ep1582 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 331834943636419 125000000 0 1 331834943636419 90000000000 0

noncomputable def ep1583 := @ep1582 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1543) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 43145414589 500000 0 1 Bool.true 331834943636419 125000000 0 1 qz244)

noncomputable def ep1584 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 43145414589 500000 0 1 0 1 0

noncomputable def ep1585 := @ep1584 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1543) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 43145414589 500000 0 1 Bool.true 331834943636419 125000000 0 1 qz244)

noncomputable def ep1586 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 14381804863 120000000 0 1 Bool.false 331834943636419 90000000000 0 1 (@ep1541 14381804863 120000000 0 1 (ep1578 rfl) (ep1580 rfl) rfl rfl) (@ep1581 331834943636419 90000000000 0 1 (ep1583 rfl) (ep1585 rfl) rfl rfl)

noncomputable def ep1587 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 14381804863 120000000 0 1 Bool.false 331834943636419 90000000000 0 1 ep1586

noncomputable def ep1588 := @Enclosure.Complex.IsNear.re_isNear qz226 Bool.true 11961387114083319887 ep1538 411235590061177065655483 ep1539 Bool.true 14844994084637375997 ep1538 509732060388069191561733 ep1539

noncomputable abbrev qz514 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 64339296875)))

noncomputable def ep1589 := @Enclosure.Complex.IsNear.of_eq qz226 (Complex.mk (@HMul.hMul Real Real Real qz0 qz514 (Real.cos qz134)) (@HMul.hMul Real Real Real qz0 qz514 qz671)) Bool.true 11961387114083319887 ep1538 411235590061177065655483 ep1539 Bool.true 14844994084637375997 ep1538 509732060388069191561733

noncomputable abbrev qz515 := (Real.sqrt (@Nat.cast Real Real.instNatCast 64339296875))

noncomputable abbrev qz516 := (@Nat.cast Real Real.instNatCast 64339296875)

noncomputable def ep1590 := @Enclosure.Real.IsNear.inv_image qz515 557786472435602635 2199023255552 1 2199023255552 4334726 4334727 1099511627776 (@Enclosure.Real.IsNear.of_eq qz515 (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz516 qz14)) Bool.false 557786472435602635 2199023255552 1 2199023255552 (BSN.sqrt_natCast_div_one 64339296875) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz516 qz14)) Bool.false 557786472435602635 2199023255552 1 2199023255552 557786472435602635 2199023255552 1 2199023255552 (BSN.sqrt_enclosure 64339296875 1 278893236217801317 278893236217801318 1099511627776 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep1591 := nat_lit 9476026700000000000000000

noncomputable def ep1592 := nat_lit 140841847005213844967262257152

noncomputable def ep1593 := nat_lit 39614081257132168796771975168

noncomputable def ep1594 := nat_lit 296125834375000000000000000

noncomputable def ep1595 := BSN.log_dyadic_bound 3 67 5 4 383733955291025745 1099511627776 296125834375 256758449434344 688905 98529610469 70 64 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 3) (BSN.artanhQ 67) 0 4 256758449434344 383733955291025745 688905 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1596 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz136 138478 1000 0 1 16011864204894419 4503599627370496 64094760267 18952053400000000000000 1108645465682684677141 2251799813685248000 4437857106126813 ep1591 qz18 (BSN.isNear_log_sfrac 35 1 16011864204894419 4503599627370496 64094760267 18952053400000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz434) Bool.false ep1592 ep1593 1001480629171875 ep1594 16011864204894419 4503599627370496 64094760267 18952053400000000000000 (BSN.log_rat_reduce_isNear 35 1 5 70 64 98529610469 1099511627776 24973259072661432 36028797018963968 296125834375 1000000000000000 rfl rfl rfl rfl (ep1595 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1597 := nat_lit 107471191623630248321499529216

noncomputable def ep1598 := nat_lit 158456325028528675187087900672

noncomputable def ep1599 := nat_lit 764498598601605084404053996011323386058548590052229350790531067981504756809501009972513758868533174645862103302394516923876356649119192535119062193694791851239431111180007471770663645958379667456

noncomputable def ep1600 := nat_lit 433508493418857668581224415970842172945704524136195884060107236574755230272398559971038183579402879451701676292035087663075723672867783462894129725544215056950382789287271065333206471540875250892800

noncomputable def ep1601 := nat_lit 659640197372256341157164257844167503953370023838368371919173698743042232652429757043226922519718095803519575534335929030058780207253440629221487441237552463134387145724474483531008966656

noncomputable def ep1602 := nat_lit 3822327649320409121566701721905592379460863183514177305864788365798023610073120487448823993099042242755044658447231647508002678557191876535777087519370781443761849805719750505052683876627294191616

noncomputable def ep1603 := nat_lit 15172797269660018400342854558979476053099658344766855942103753280116433059533949598986336425279100780809558670221228068207650328550372421201294540394047526993263397625054487286662226503930633781248000

noncomputable def ep1604 := BSN.sin_dyadic_bound_f 3054514980466088 4503599627370496 4 3 2199023255552 592830039521 ep1599 ep1600 ep1601 ep1602 ep1603 ep1601 1379716472779 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 3054514980466088) (BSN.sinEvenQ 4503599627370496) 0 3 ep1599 ep1600 ep1601 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 3054514980466088) (BSN.sinOddQ 4503599627370496) 0 3 ep1602 ep1603 ep1601 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz517 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 541330793790373) (@Nat.cast Real Real.instNatCast 1099511627776))

noncomputable def ep1605 := @Enclosure.Real.IsNear.cos_image qz134 qz517 Bool.false 541330793790373 1099511627776 1031 2199023255552 Bool.true 1379716472779 2199023255552 1 296125834375 (@Enclosure.Real.IsNear.recentre' qz134 Bool.false 1108645465682684677141 2251799813685248000 4437857106126813 ep1591 541330793790373 1099511627776 1031 2199023255552 (ep1596 rfl) rfl) (Enclosure.sfrac_false_div 541330793790373 1099511627776) (BSN.cos_reduce1 qz517 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1597) (@Nat.cast Real Real.instNatCast ep1598)) 226375608064910080 72057594037927936 Bool.false 1379716472779 2199023255552 78 1000000000000000 592251668750 296125834375 (BSN.sin_reduce_arg_pos_rat_q1 541330793790373 1099511627776 226375608064910080 72057594037927936 78 ep1597 ep1598 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1379716472779 2199023255552 ep1597 ep1598 3054514980466088 4503599627370496 592830039521 592251668750 (ep1604 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1606 := nat_lit 294054382234962535104938442153072001401801019061694949408913556836910614008642866009423907100723674191305865414917530229085770188972138961580481233244156635331813978211391533388665795862316711936

noncomputable def ep1607 := nat_lit 33346807186065974506248031997757090226592655702784298773854402813442710020953735382387552583030990727053975099387314435621209513297521804838009978888016542842337137637482389641015882426221173145600

noncomputable def ep1608 := nat_lit 1783780136011372877527745760125801051136346309470792060606950747220197092336659365423174841590725324890739220895008074490319574181399701799991092939342622987491534468893811644304756237955172925440

noncomputable def ep1609 := nat_lit 3034559453932003680068570911795895210619931668953371188420750656023286611906789919797267285055820156161911734044245613641530065710074484240258908078809505398652679525010897457332445300786126756249600

noncomputable def ep1610 := BSN.cos_dyadic_bound_f 3054514980466088 4503599627370496 4 3 2199023255552 592830039521 ep1606 ep1607 ep1601 ep1608 ep1609 ep1601 1712333417649 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 3054514980466088) (BSN.cosEvenQ 4503599627370496) 0 3 ep1606 ep1607 ep1601 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 3054514980466088) (BSN.cosOddQ 4503599627370496) 0 3 ep1608 ep1609 ep1601 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1611 := @Enclosure.Real.IsNear.sin_image qz134 qz517 Bool.false 541330793790373 1099511627776 1031 2199023255552 Bool.false 1712333417649 2199023255552 1 296125834375 (@Enclosure.Real.IsNear.recentre' qz134 Bool.false 1108645465682684677141 2251799813685248000 4437857106126813 ep1591 541330793790373 1099511627776 1031 2199023255552 (ep1596 rfl) rfl) (Enclosure.sfrac_false_div 541330793790373 1099511627776) (BSN.sin_reduce1 qz517 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1597) (@Nat.cast Real Real.instNatCast ep1598)) 226375608064910080 72057594037927936 Bool.false 1712333417649 2199023255552 78 1000000000000000 592251668750 296125834375 (BSN.sin_reduce_arg_pos_rat_q1 541330793790373 1099511627776 226375608064910080 72057594037927936 78 ep1597 ep1598 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1712333417649 2199023255552 ep1597 ep1598 3054514980466088 4503599627370496 592830039521 592251668750 (ep1610 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1612 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz514 (Real.cos qz134)) (@HMul.hMul Real Real Real qz0 qz514 qz671) Bool.true 11961387114083319887 ep1538 411235590061177065655483 ep1539 Bool.true 14844994084637375997 ep1538 509732060388069191561733 ep1539 (@Enclosure.Real.IsNear.mulLit_ft qz514 (Real.cos qz134) 8669453 2199023255552 1 2199023255552 1379716472779 2199023255552 307504758496177 651187596360364851200000 11961387114083319887 ep1538 411235590061177065655483 ep1539 (@Enclosure.Real.IsNear.recentre' qz514 Bool.false 8669453 2199023255552 1 2199023255552 8669453 2199023255552 1 2199023255552 (ep1590 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' (Real.cos qz134) Bool.true 1379716472779 2199023255552 307504758496177 651187596360364851200000 1379716472779 2199023255552 307504758496177 651187596360364851200000 (ep1605 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz514 qz671 8669453 2199023255552 1 2199023255552 1712333417649 2199023255552 307504758496177 651187596360364851200000 14844994084637375997 ep1538 509732060388069191561733 ep1539 (@Enclosure.Real.IsNear.recentre' qz514 Bool.false 8669453 2199023255552 1 2199023255552 8669453 2199023255552 1 2199023255552 (ep1590 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg qz135 Bool.false 1712333417649 2199023255552 307504758496177 651187596360364851200000 (@Enclosure.Real.IsNear.recentre' qz135 Bool.false 1712333417649 2199023255552 307504758496177 651187596360364851200000 1712333417649 2199023255552 307504758496177 651187596360364851200000 (ep1611 rfl rfl) rfl)) rfl)

noncomputable def ep1613 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz236 331834943636419 90000000000 0 1 14844994084637375997 ep1538 509732060388069191561733 ep1539 ep1534

noncomputable def ep1614 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 14381804863 120000000 0 1 Bool.false 331834943636419 90000000000 0 1 ep1586

noncomputable def ep1615 := @Enclosure.Complex.IsNear.im_isNear qz226 Bool.true 11961387114083319887 ep1538 411235590061177065655483 ep1539 Bool.true 14844994084637375997 ep1538 509732060388069191561733 ep1539

noncomputable def ep1616 := nat_lit 71165936039214682568404691137

noncomputable def ep1617 := nat_lit 193428131138340667952988160000000

noncomputable def ep1618 := nat_lit 2443622341638714388794336741369193

noncomputable def ep1619 := nat_lit 57279066724938048850573442154496000000000000

noncomputable def ep1620 := nat_lit 3969206218815226977711203800164653

noncomputable def ep1621 := nat_lit 136462338849240201085838705889865835377

noncomputable def ep1622 := @Enclosure.Real.IsNear.addLit_tt (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz236) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz235) ep1616 ep1617 ep1618 ep1619 ep1620 ep1525 ep1621

noncomputable def ep1623 := nat_lit 798728502527854987432800919201918169381623592269761719828480000000

noncomputable def ep1624 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz236 14381804863 120000000 0 1 14844994084637375997 ep1538 509732060388069191561733 ep1539 ep1616

noncomputable def ep1625 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz235 331834943636419 90000000000 0 1 11961387114083319887 ep1538 411235590061177065655483 ep1539 ep1620

noncomputable abbrev qz518 := (@ep1589 ep1539 (BSN.cpow_neg_s_sub_mk qz12 138478 1000 35 3 64339296875 qz13 rfl EMRow48.d22) ep1612)

noncomputable def ep1626 := ep1529 (@ep1536 ep1522 ep1537 ep1519 ep1520 ep1521 ep1522 (@ep1540 ep1531 ep1532 ep1533 ep1587 (ep1588 qz518) rfl) (@ep1613 ep1520 ep1535 ep1522 ep1614 (ep1615 qz518) rfl) rfl rfl) (@ep1622 ep1528 ep1623 ep1524 ep1525 ep1526 ep1528 (@ep1624 ep1617 ep1618 ep1619 ep1587 (ep1615 qz518) rfl) (@ep1625 ep1525 ep1621 ep1528 ep1614 (ep1588 qz518) rfl) rfl rfl)

noncomputable def ep1627 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226)) (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226)) ep1524 ep1525 ep1526 ep1528 ep1524 ep1525 ep1526

noncomputable def ep1628 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226) Bool.false ep1519 ep1520 ep1521 ep1522 Bool.true ep1524 ep1525 ep1526

noncomputable def ep1629 := @ep1489 2322683257900564019 4035225266123964416 293856131901 4035225266123964416 (@ep1490 1 3670016 (ep1491 (@ep1492 1048576 1 1048576 (ep1493 (@ep1494 19188406484 4797101621 250000 0 1 (ep1498 rfl) (ep1501 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep1502 1913 1099511627776 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226)) (@ep1503 3826 2199023255552 15990815861 1099511627776 1913 1099511627776 (@ep1508 15990813948 15990817774 1099511627776 (@ep1514 ep1515 ep1516 ep1517 ep1518 ep1504 ep1505 ep1506 ep1507 (@ep1523 ep1522 ep1509 ep1510 ep1511 ep1512 (@ep1527 ep1528 ep1626) (@ep1527 ep1528 ep1626) rfl) (@ep1627 ep1528 ep1513 ep1515 ep1516 ep1517 (@ep1628 ep1528 ep1626) (@ep1628 ep1528 ep1626) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow48.d23 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz411 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 35))) (@HMul.hMul Real Real Real qz0 qz223 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226)))) Bool.false 21374458065492963275 36317027395115679744 3749139845649701 36317027395115679744 := ep1487 (ep1488 ep1629) rfl rfl

theorem EMRow48.d24 : @Eq Nat (Nat.pow 36 (Nat.succ (Nat.mul 2 3))) 78364164096 := @Eq.refl Nat 78364164096

noncomputable abbrev qz718 := (@HAdd.hAdd Complex Complex Complex qz720 qz726 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz519 := qz718

noncomputable abbrev qz245 := (@HDiv.hDiv Real Real Real qz272 (@Norm.norm Complex Complex.instNorm qz519) (@HAdd.hAdd Real Real Real qz411 (Complex.re qz437) qz290))

noncomputable abbrev qz520 := (@HPow.hPow Complex Complex Complex qz538 (@Nat.cast Complex Complex.instNatCast 36) (@HSub.hSub Complex Complex Complex qz653 qz674 qz545))

noncomputable abbrev qz246 := qz520

noncomputable def ep1630 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz142 1 36))) (@HMul.hMul Real Real Real qz0 qz245 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz246))) 20471704823 1855425871872 197781097 1855425871872 4461044904337317375 8070450532247928832 88349566599

noncomputable def ep1631 := nat_lit 8442354012175012766596764532736

noncomputable def ep1632 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz142 1 36)) 26561 1769472 1 1769472 770743 1048576 7417 1048576 20471704823 1855425871872

noncomputable def ep1633 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz142 1 36)) (Real.sqrt (@HAdd.hAdd Real Real Real qz411 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz142 1 36)) (Complex.re (zetaApproximant qz142 1 36))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz142 1 36)) (Complex.im (zetaApproximant qz142 1 36))))) Bool.false 770743 1048576 7417 1048576

noncomputable def ep1634 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz411 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz142 1 36)) (Complex.re (zetaApproximant qz142 1 36))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz142 1 36)) (Complex.im (zetaApproximant qz142 1 36))))) Bool.false 770743 1048576 7417 1048576

noncomputable def ep1635 := nat_lit 154026836542482838308400973727844260021409

noncomputable def ep1636 := nat_lit 285059933173376128354092343596960605798400

noncomputable def ep1637 := nat_lit 253153424070657347306114754443385277285586567376773927184683

noncomputable def ep1638 := nat_lit 24349551589011487487497070364051043665038333087060066304000000

noncomputable def ep1639 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz411 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz142 1 36)) (Complex.re (zetaApproximant qz142 1 36))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz142 1 36)) (Complex.im (zetaApproximant qz142 1 36)))) ep1635 ep1636 ep1637 ep1638 381663 389080

noncomputable def ep1640 := nat_lit 303977879867956773840022322646685978093074517729

noncomputable def ep1641 := nat_lit 562762612714163838456870061737086315833847709696

noncomputable def ep1642 := nat_lit 17404667760804236591347706540804526465995901710557154956387

noncomputable def ep1643 := nat_lit 1712077846102370213964637759972339007698007795183910912000000

noncomputable def ep1644 := nat_lit 4463909525901480785157584381163548459181188401

noncomputable def ep1645 := nat_lit 25011671676185059486972002743870502925948787097600

noncomputable def ep1646 := nat_lit 50583343252973842062526352767488107922803687439649510244611

noncomputable def ep1647 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz142 1 36)) (Complex.re (zetaApproximant qz142 1 36))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz142 1 36)) (Complex.im (zetaApproximant qz142 1 36))) ep1640 ep1641 ep1642 ep1643 ep1644 ep1645 ep1646

noncomputable def ep1648 := nat_lit 219145964301103387387473633276459392985344997783540596736000000

noncomputable def ep1649 := nat_lit 7605507049467875012488890325860546679880633499488125399805535047045253598889706587668278983786496

noncomputable def ep1650 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz142 1 36)) (Complex.re (zetaApproximant qz142 1 36)) 551341890180636259841777 750175054713340783755264 ep1212 ep1213 551341890180636259841777 750175054713340783755264 ep1212 ep1213 ep1640

noncomputable def ep1651 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (zetaApproximant qz142 1 36)) (Complex.im (zetaApproximant qz142 1 36)) 66812495282705021757049 ep1326 ep1327 ep1328 66812495282705021757049 ep1326 ep1327 ep1328 ep1644

noncomputable def ep1652 := @ep1630 1152921504606846976 ep1631 122852419913033558501 217902164370694078464 3320601623384125 31128880624384868352 (@ep1632 197781097 1855425871872 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) qz501) Bool.false 26561 1769472 1 1769472 (BSN.theta_err_eq 1 2 96 162 EMRow48.d19 EMRow48.d20 rfl) (ep1467 rfl)) (ep1633 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz142 1 36)) (@ep1634 770743 1048576 7417 1048576 (@ep1639 524288 (@ep1647 ep1648 ep1649 ep1635 ep1636 ep1637 ep1638 (@ep1650 ep1641 ep1642 ep1643 ep1449 ep1449 rfl) (@ep1651 ep1645 ep1646 ep1648 ep1455 ep1455 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz247 := (@Norm.norm Complex Complex.instNorm qz519)

noncomputable def ep1653 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz245 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz246))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz247 qz717) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz246))) Bool.false 4461044904337317375 8070450532247928832 88349566599 1152921504606846976 (BSN.zrb_shape_eq qz247 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz246)) qz145 3)

noncomputable def ep1654 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz247 qz717) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz246)) 147375875 3670016 1 3670016 30269845077 2199023255552 3991 2199023255552

noncomputable def ep1655 := @Enclosure.Real.IsNear.mulLit_ff qz247 qz717 147375875 1048576 1 1048576 2 7 0 1 147375875 3670016

noncomputable abbrev qz521 := (Complex.re qz718)

noncomputable abbrev qz522 := (Complex.im qz718)

noncomputable abbrev qz248 := (@HAdd.hAdd Real Real Real qz411 (@HMul.hMul Real Real Real qz269 qz521 qz521) (@HMul.hMul Real Real Real qz269 qz522 qz522))

noncomputable abbrev qz249 := qz519

noncomputable def ep1656 := @Enclosure.Real.IsNear.of_eq qz247 (Real.sqrt qz248) Bool.false 147375875 1048576 1 1048576 (BSN.norm_eq_sqrt_mul_add qz249)

noncomputable def ep1657 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz248) Bool.false 147375875 1048576 1 1048576 147375875

noncomputable def ep1658 := @Enclosure.Real.IsNear.sqrt_image qz248 790156201 40000 0 1 73687937 73687938 524288

noncomputable abbrev qz250 := (@HMul.hMul Real Real Real qz269 qz521 qz521)

noncomputable abbrev qz251 := (@HMul.hMul Real Real Real qz269 qz522 qz522)

noncomputable def ep1659 := @Enclosure.Real.IsNear.addLit_ff qz250 qz251 49 4 0 1 789666201 40000 0 1

noncomputable abbrev qz252 := qz521

noncomputable def ep1660 := @Enclosure.Real.IsNear.mulLit_ff qz252 qz252 7 2 0 1 7 2 0 1 49 4

noncomputable def ep1661 := @Enclosure.Complex.IsNear.of_eq qz249 (Complex.mk qz506 qz145) Bool.false 7 2 0 1 Bool.false 140505 1000 0 1 (BSN.s_add_nat_mk qz145 Bool.false 140505 1000 3 qz146)

noncomputable abbrev qz523 := (ep1661 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz145 Bool.false 7 2 0 1 Bool.false 140505 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz147))

noncomputable def ep1662 := @ep1660 0 1 (@Enclosure.Complex.IsNear.re_isNear qz249 Bool.false 7 2 0 1 Bool.false 140505 1000 0 1 qz523)

noncomputable def ep1663 := ep1662 (@Enclosure.Complex.IsNear.re_isNear qz249 Bool.false 7 2 0 1 Bool.false 140505 1000 0 1 qz523)

noncomputable abbrev qz253 := qz522

noncomputable def ep1664 := @Enclosure.Real.IsNear.mulLit_ff qz253 qz253 140505 1000 0 1 140505 1000 0 1 789666201 40000

noncomputable def ep1665 := @ep1664 0 1 (@Enclosure.Complex.IsNear.im_isNear qz249 Bool.false 7 2 0 1 Bool.false 140505 1000 0 1 qz523)

noncomputable def ep1666 := ep1665 (@Enclosure.Complex.IsNear.im_isNear qz249 Bool.false 7 2 0 1 Bool.false 140505 1000 0 1 qz523)

noncomputable def ep1667 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz246)) (Real.sqrt (@HAdd.hAdd Real Real Real qz411 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz246)) (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz246))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz246)) (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz246))))) Bool.false 30269845077 2199023255552

noncomputable def ep1668 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz411 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz246)) (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz246))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz246)) (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz246))))) Bool.false 30269845077 2199023255552

noncomputable def ep1669 := nat_lit 8166810954254299960527315344544242637870364468452736067866458229

noncomputable def ep1670 := nat_lit 43101437086853124141328510138602445789277037811413811200000000000000

noncomputable def ep1671 := nat_lit 44557458223804343626914064106591431016840227473297521429940743654916756139

noncomputable def ep1672 := nat_lit 891979857421957827593675092173706541262412793966543287035951285534720000000000000000

noncomputable def ep1673 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz411 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz246)) (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz246))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz246)) (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz246)))) ep1669 ep1670 ep1671 ep1672

noncomputable def ep1674 := nat_lit 9695240896997172234913109363680113127409025982832216545191665809

noncomputable def ep1675 := nat_lit 86202874173706248282657020277204891578554075622827622400000000000000

noncomputable def ep1676 := nat_lit 51313576925103701112224882108403487688343757207729787550542612718719992879

noncomputable def ep1677 := nat_lit 1783959714843915655187350184347413082524825587933086574071902571069440000000000000000

noncomputable def ep1678 := nat_lit 6638381011511427686141521325408372148331702954073255590541250649

noncomputable def ep1679 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz246)) (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz246))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz246)) (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz246))) ep1674 ep1675 ep1676 ep1677 ep1678

noncomputable def ep1680 := nat_lit 37801339522504986141603246104779374345336697738865255309338874591113519399

noncomputable def ep1681 := nat_lit 1408005154180058549505523343421037359393507736775197633738551476173978949263710824040700868394942830258448788953969459200000000000000

noncomputable def ep1682 := nat_lit 98464414368832622610619537439447

noncomputable def ep1683 := nat_lit 9284550294640352061743431680000000

noncomputable def ep1684 := nat_lit 1811303870621052871150810286185247

noncomputable def ep1685 := nat_lit 1335649547914390474221918126027571200000000

noncomputable def ep1686 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz246)) (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz246)) ep1682 ep1683 ep1684 ep1685 ep1682 ep1683 ep1684

noncomputable def ep1687 := nat_lit 81476260416832016543178290890843

noncomputable def ep1688 := nat_lit 1612554599056369777539097421633387

noncomputable def ep1689 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz246) Bool.false ep1682 ep1683 ep1684 ep1685 Bool.false ep1687 ep1683 ep1688

noncomputable def ep1690 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz246 Bool.false ep1682 ep1683 ep1684 ep1685 Bool.false ep1687 ep1683 ep1688 ep1685

noncomputable def ep1691 := nat_lit 9028156706013277335952054529

noncomputable def ep1692 := nat_lit 30948500982134506872478105600000

noncomputable def ep1693 := nat_lit 8172457227623844617083309303

noncomputable def ep1694 := nat_lit 218958942281047618724904610824192000000

noncomputable def ep1695 := nat_lit 95755967357028639409833921080747

noncomputable def ep1696 := nat_lit 1761451881532547418986602099436947

noncomputable abbrev qz254 := (Complex.re qz520)

noncomputable abbrev qz255 := (Complex.im qz520)

noncomputable def ep1697 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3)))) qz254) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3)))) qz255) ep1691 ep1692 ep1693 ep1694 ep1695 ep1683 ep1696

noncomputable def ep1698 := nat_lit 3047326024799115471485534076342481495332844725698993271603200000

noncomputable def ep1699 := nat_lit 695650806205411705323915690639360

noncomputable def ep1700 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3)))) qz254 2368948603 19200000 0 1 11433118508244744729 ep1538 210439302167103420961 ep1699 ep1691

noncomputable def ep1701 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3)))) 2368948603 19200000 0 1 0 1 0 1 2368948603

noncomputable def ep1702 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 7106845809 80000 0 1 2368948603 19200000 0

noncomputable abbrev qz524 := (@HAdd.hAdd Complex Complex Complex qz537 qz673 qz546)

noncomputable abbrev qz256 := qz524

noncomputable def ep1703 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz78 (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 2)) qz256) Bool.true 7106845809 80000 0 1 Bool.true 22183946684301 8000000 0 1

noncomputable abbrev qz257 := (Complex.re qz524)

noncomputable abbrev qz258 := (Complex.im qz524)

noncomputable def ep1704 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 2))) qz257) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 2))) qz258) 789636201 16000 0 1 789666201 20000 0 1

noncomputable def ep1705 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 2))) qz257 789636201 40000 0 1 5 2 0 1 789636201 16000

noncomputable abbrev qz525 := (@HAdd.hAdd Complex Complex Complex qz537 qz673 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz259 := qz525

noncomputable def ep1706 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz78 (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)) qz259) Bool.true 789636201 40000 0 1 Bool.false 28101 100 0 1

noncomputable abbrev qz260 := (Complex.re qz525)

noncomputable abbrev qz261 := (Complex.im qz525)

noncomputable def ep1707 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1))) qz260) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1))) qz261) 3 4 0 1 789666201 40000 0 1

noncomputable def ep1708 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1))) qz260 1 2 0 1 3 2 0 1 3 4

noncomputable def ep1709 := @ep1708 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 140505 1000 0 1 ep1413)

noncomputable def ep1710 := @Enclosure.Complex.IsNear.of_eq qz259 (Complex.mk qz510 qz145) Bool.false 3 2 0 1 Bool.false 140505 1000 0 1 (BSN.s_add_nat_mk qz145 Bool.false 140505 1000 1 qz146)

noncomputable abbrev qz526 := (ep1710 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz145 Bool.false 3 2 0 1 Bool.false 140505 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz147))

noncomputable def ep1711 := ep1709 (@Enclosure.Complex.IsNear.re_isNear qz259 Bool.false 3 2 0 1 Bool.false 140505 1000 0 1 qz526)

noncomputable def ep1712 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1))) qz261 140505 1000 0 1 140505 1000 0 1 789666201 40000

noncomputable def ep1713 := @ep1712 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 140505 1000 0 1 ep1413)

noncomputable def ep1714 := ep1713 (@Enclosure.Complex.IsNear.im_isNear qz259 Bool.false 3 2 0 1 Bool.false 140505 1000 0 1 qz526)

noncomputable def ep1715 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)) qz259 Bool.true 789636201 40000 0 1 Bool.false 28101 100 0 1 (@ep1707 3158544804 789636201 40000 0 1 (ep1711 rfl) (ep1714 rfl) rfl rfl)

noncomputable def ep1716 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1))) qz261) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1))) qz260) 28101 400 0 1 84303 400 0 1

noncomputable def ep1717 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1))) qz261 1 2 0 1 140505 1000 0 1 28101 400

noncomputable def ep1718 := @ep1717 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 140505 1000 0 1 ep1413)

noncomputable def ep1719 := ep1718 (@Enclosure.Complex.IsNear.im_isNear qz259 Bool.false 3 2 0 1 Bool.false 140505 1000 0 1 qz526)

noncomputable def ep1720 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1))) qz260 140505 1000 0 1 3 2 0 1 84303 400

noncomputable def ep1721 := @ep1720 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 140505 1000 0 1 ep1413)

noncomputable def ep1722 := ep1721 (@Enclosure.Complex.IsNear.re_isNear qz259 Bool.false 3 2 0 1 Bool.false 140505 1000 0 1 qz526)

noncomputable abbrev qz262 := (ep1706 (BSN.ascPochhammer_succ_eval_c 1 2 qz437 rfl) (ep1715 (@ep1716 44961600 28101 100 0 1 (ep1719 rfl) (ep1722 rfl) rfl rfl)))

noncomputable def ep1723 := @ep1705 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 789636201 40000 0 1 Bool.false 28101 100 0 1 qz262)

noncomputable def ep1724 := @Enclosure.Complex.IsNear.of_eq qz256 (Complex.mk qz512 qz145) Bool.false 5 2 0 1 Bool.false 140505 1000 0 1 (BSN.s_add_nat_mk qz145 Bool.false 140505 1000 2 qz146)

noncomputable abbrev qz527 := (ep1724 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz145 Bool.false 5 2 0 1 Bool.false 140505 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz147))

noncomputable def ep1725 := ep1723 (@Enclosure.Complex.IsNear.re_isNear qz256 Bool.false 5 2 0 1 Bool.false 140505 1000 0 1 qz527)

noncomputable def ep1726 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 2))) qz258 28101 100 0 1 140505 1000 0 1 789666201 20000

noncomputable def ep1727 := @ep1726 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 789636201 40000 0 1 Bool.false 28101 100 0 1 qz262)

noncomputable def ep1728 := ep1727 (@Enclosure.Complex.IsNear.im_isNear qz256 Bool.false 5 2 0 1 Bool.false 140505 1000 0 1 qz527)

noncomputable def ep1729 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 2)) qz256 Bool.true 7106845809 80000 0 1 Bool.true 22183946684301 8000000 0 1 (@ep1704 28427383236000 7106845809 80000 0 1 (ep1725 rfl) (ep1728 rfl) rfl rfl)

noncomputable def ep1730 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 2))) qz258) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 2))) qz257) 22189566884301 8000000 0 1 28101 40 0 1

noncomputable def ep1731 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 2))) qz258 789636201 40000 0 1 140505 1000 0 1 22189566884301 8000000

noncomputable def ep1732 := @ep1731 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 789636201 40000 0 1 Bool.false 28101 100 0 1 qz262)

noncomputable def ep1733 := ep1732 (@Enclosure.Complex.IsNear.im_isNear qz256 Bool.false 5 2 0 1 Bool.false 140505 1000 0 1 qz527)

noncomputable def ep1734 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 2))) qz257 28101 100 0 1 5 2 0 1 28101 40

noncomputable def ep1735 := @ep1734 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 789636201 40000 0 1 Bool.false 28101 100 0 1 qz262)

noncomputable def ep1736 := ep1735 (@Enclosure.Complex.IsNear.re_isNear qz256 Bool.false 5 2 0 1 Bool.false 140505 1000 0 1 qz527)

noncomputable abbrev qz263 := (ep1703 (BSN.ascPochhammer_succ_eval_c 2 3 qz437 rfl) (ep1729 (@ep1730 887357867372040 22183946684301 8000000 0 1 (ep1733 rfl) (ep1736 rfl) rfl rfl)))

noncomputable def ep1737 := @ep1702 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1543) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 7106845809 80000 0 1 Bool.true 22183946684301 8000000 0 1 qz263)

noncomputable def ep1738 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 22183946684301 8000000 0 1 0 1 0

noncomputable def ep1739 := @ep1738 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1543) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 7106845809 80000 0 1 Bool.true 22183946684301 8000000 0 1 qz263)

noncomputable def ep1740 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3)))) 7394648894767 1920000000 0 1 0 1 0 1 7394648894767

noncomputable def ep1741 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 22183946684301 8000000 0 1 7394648894767 1920000000 0

noncomputable def ep1742 := @ep1741 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1543) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 7106845809 80000 0 1 Bool.true 22183946684301 8000000 0 1 qz263)

noncomputable def ep1743 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 7106845809 80000 0 1 0 1 0

noncomputable def ep1744 := @ep1743 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1543) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 7106845809 80000 0 1 Bool.true 22183946684301 8000000 0 1 qz263)

noncomputable def ep1745 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 2368948603 19200000 0 1 Bool.false 7394648894767 1920000000 0 1 (@ep1701 2368948603 19200000 0 1 (ep1737 rfl) (ep1739 rfl) rfl rfl) (@ep1740 7394648894767 1920000000 0 1 (ep1742 rfl) (ep1744 rfl) rfl rfl)

noncomputable def ep1746 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 2368948603 19200000 0 1 Bool.false 7394648894767 1920000000 0 1 ep1745

noncomputable def ep1747 := @Enclosure.Complex.IsNear.re_isNear qz246 Bool.false 11433118508244744729 ep1538 210439302167103420961 ep1699 Bool.true 12949359559828815941 ep1538 238206290332334904541 ep1699

noncomputable abbrev qz528 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 78364164096)))

noncomputable def ep1748 := @Enclosure.Complex.IsNear.of_eq qz246 (Complex.mk (@HMul.hMul Real Real Real qz0 qz528 (Real.cos qz218)) (@HMul.hMul Real Real Real qz0 qz528 qz712)) Bool.false 11433118508244744729 ep1538 210439302167103420961 ep1699 Bool.true 12949359559828815941 ep1538 238206290332334904541

noncomputable abbrev qz529 := (Real.sqrt (@Nat.cast Real Real.instNatCast 78364164096))

noncomputable abbrev qz530 := (@Nat.cast Real Real.instNatCast 78364164096)

noncomputable def ep1749 := @Enclosure.Real.IsNear.inv_image qz529 615585774066204673 2199023255552 1 2199023255552 3927725 3927726 1099511627776 (@Enclosure.Real.IsNear.of_eq qz529 (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz530 qz14)) Bool.false 615585774066204673 2199023255552 1 2199023255552 (BSN.sqrt_natCast_div_one 78364164096) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz530 qz14)) Bool.false 615585774066204673 2199023255552 1 2199023255552 615585774066204673 2199023255552 1 2199023255552 (BSN.sqrt_enclosure 78364164096 1 307792887033102336 307792887033102337 1099511627776 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep1750 := nat_lit 3452573160000000000000000

noncomputable def ep1751 := nat_lit 141957810414438141666634235904

noncomputable def ep1752 := nat_lit 331447023360000000000000000

noncomputable def ep1753 := BSN.log_dyadic_bound 4 68 5 4 432019261472440320 1099511627776 331447023360 499329192689664 6881280 129503817258 72 64 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 4) (BSN.artanhQ 68) 0 4 499329192689664 432019261472440320 6881280 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1754 := @Enclosure.Real.IsNear.mulLit_ff qz145 qz711 140505 1000 0 1 16138734555902163 4503599627370496 156508942987 51788597400000000000000 453514579755406682463 900719925474099200 1466019268959229 ep1750 qz147 (BSN.isNear_log_sfrac 36 1 16138734555902163 4503599627370496 156508942987 51788597400000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz713) Bool.false ep1751 ep1593 1001657235116800 ep1752 16138734555902163 4503599627370496 156508942987 51788597400000000000000 (BSN.log_rat_reduce_isNear 36 1 5 72 64 129503817258 1099511627776 24973259072661432 36028797018963968 331447023360 1000000000000000 rfl rfl rfl rfl (ep1753 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1755 := nat_lit 268584698417110577889469792256

noncomputable def ep1756 := nat_lit 316912650057057350374175801344

noncomputable def ep1757 := nat_lit 717039587891594629224071083345321745057757200357293845827293534639705037969327212609740237233282523657384339621091801466042895254656067427053426962742398427158746563601173780026970031615845072896

noncomputable def ep1758 := nat_lit 9559112984057704585878493939646108882384214877033650832914426730025147707463710836373126009772951672982181559767365955986962808842243755275413289191145561300829720690823962977098757308416

noncomputable def ep1759 := nat_lit 4349149839081806624155039572068570683566194719165567387759621440580507111494296547591449227410229294047459114263306712958062312160970108579159249759714659458330871855809744471896200041927446364160

noncomputable def ep1760 := BSN.cos_dyadic_bound_f 3816818127931904 4503599627370496 4 3 2199023255552 663541404188 ep1757 ep1607 ep1758 ep1759 ep1609 ep1758 1455437569179 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 3816818127931904) (BSN.cosEvenQ 4503599627370496) 0 3 ep1757 ep1607 ep1758 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 3816818127931904) (BSN.cosOddQ 4503599627370496) 0 3 ep1759 ep1609 ep1758 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz531 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 1107213329480973) (@Nat.cast Real Real.instNatCast 2199023255552))

noncomputable def ep1761 := @Enclosure.Real.IsNear.cos_image qz218 qz531 Bool.false 1107213329480973 2199023255552 935 2199023255552 Bool.false 1455437569179 2199023255552 1 331447023360 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 453514579755406682463 900719925474099200 1466019268959229 ep1750 1107213329480973 2199023255552 935 2199023255552 (ep1754 rfl) rfl) (Enclosure.sfrac_false_div 1107213329480973 2199023255552) (BSN.cos_reduce0 qz531 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1755) (@Nat.cast Real Real.instNatCast ep1756)) 226375608064910080 72057594037927936 Bool.false 1455437569179 2199023255552 80 1000000000000000 662894046720 331447023360 (BSN.sin_reduce_arg_pos_rat_q0 1107213329480973 2199023255552 226375608064910080 72057594037927936 80 ep1755 ep1756 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1455437569179 2199023255552 ep1755 ep1756 3816818127931904 4503599627370496 663541404188 662894046720 (ep1760 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1762 := nat_lit 1864048547787080973705889355927861869265752425612698319719370871838071848758431518626766333605386403027414491101939527294037309878203813826292754876137003938695648687130701115106255871440811196416

noncomputable def ep1763 := nat_lit 9319259925148900002222660686762939452366845821361661205230031310588258188994541913805680125927498151416616682352801571235243702833862164507999095240931072582661611176111541146332260947481671499776

noncomputable def ep1764 := BSN.sin_dyadic_bound_f 3816818127931904 4503599627370496 4 3 2199023255552 663541404188 ep1762 ep1600 ep1758 ep1763 ep1603 ep1758 1648455264991 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 3816818127931904) (BSN.sinEvenQ 4503599627370496) 0 3 ep1762 ep1600 ep1758 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 3816818127931904) (BSN.sinOddQ 4503599627370496) 0 3 ep1763 ep1603 ep1758 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1765 := @Enclosure.Real.IsNear.sin_image qz218 qz531 Bool.false 1107213329480973 2199023255552 935 2199023255552 Bool.false 1648455264991 2199023255552 1 331447023360 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 453514579755406682463 900719925474099200 1466019268959229 ep1750 1107213329480973 2199023255552 935 2199023255552 (ep1754 rfl) rfl) (Enclosure.sfrac_false_div 1107213329480973 2199023255552) (BSN.sin_reduce0 qz531 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1755) (@Nat.cast Real Real.instNatCast ep1756)) 226375608064910080 72057594037927936 Bool.false 1648455264991 2199023255552 80 1000000000000000 662894046720 331447023360 (BSN.sin_reduce_arg_pos_rat_q0 1107213329480973 2199023255552 226375608064910080 72057594037927936 80 ep1755 ep1756 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1648455264991 2199023255552 ep1755 ep1756 3816818127931904 4503599627370496 663541404188 662894046720 (ep1764 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1766 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz528 (Real.cos qz218)) (@HMul.hMul Real Real Real qz0 qz528 qz712) Bool.false 11433118508244744729 ep1538 210439302167103420961 ep1699 Bool.true 12949359559828815941 ep1538 238206290332334904541 ep1699 (@Enclosure.Real.IsNear.mulLit_ff qz528 (Real.cos qz218) 7855451 2199023255552 1 2199023255552 1455437569179 2199023255552 1219148398817 2847108251375496069120 11433118508244744729 ep1538 210439302167103420961 ep1699 (@Enclosure.Real.IsNear.recentre' qz528 Bool.false 7855451 2199023255552 1 2199023255552 7855451 2199023255552 1 2199023255552 (ep1749 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' (Real.cos qz218) Bool.false 1455437569179 2199023255552 312101990097152 728859712352126993694720 1455437569179 2199023255552 1219148398817 2847108251375496069120 (ep1761 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz528 qz712 7855451 2199023255552 1 2199023255552 1648455264991 2199023255552 1219148398817 2847108251375496069120 12949359559828815941 ep1538 238206290332334904541 ep1699 (@Enclosure.Real.IsNear.recentre' qz528 Bool.false 7855451 2199023255552 1 2199023255552 7855451 2199023255552 1 2199023255552 (ep1749 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg qz219 Bool.false 1648455264991 2199023255552 1219148398817 2847108251375496069120 (@Enclosure.Real.IsNear.recentre' qz219 Bool.false 1648455264991 2199023255552 312101990097152 728859712352126993694720 1648455264991 2199023255552 1219148398817 2847108251375496069120 (ep1765 rfl rfl) rfl)) rfl)

noncomputable def ep1767 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3)))) qz255 7394648894767 1920000000 0 1 12949359559828815941 ep1538 238206290332334904541 ep1699 ep1695

noncomputable def ep1768 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 2368948603 19200000 0 1 Bool.false 7394648894767 1920000000 0 1 ep1745

noncomputable def ep1769 := @Enclosure.Complex.IsNear.im_isNear qz246 Bool.false 11433118508244744729 ep1538 210439302167103420961 ep1699 Bool.true 12949359559828815941 ep1538 238206290332334904541 ep1699

noncomputable def ep1770 := nat_lit 30676367239001168442576080423

noncomputable def ep1771 := nat_lit 92845502946403520617434316800000

noncomputable def ep1772 := nat_lit 9250794405058970128533447643

noncomputable def ep1773 := nat_lit 28181299046910711129145299644381

noncomputable def ep1774 := nat_lit 3094850098213450687247810560000000

noncomputable def ep1775 := nat_lit 1556124753185510059755043391011087

noncomputable def ep1776 := @Enclosure.Real.IsNear.addLit_tf_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3)))) qz255) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3)))) qz254) ep1770 ep1771 ep1772 ep1694 ep1773 ep1774 ep1775

noncomputable def ep1777 := nat_lit 2521568125530972510285473328103357126522445568046437027020800000

noncomputable def ep1778 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3)))) qz255 2368948603 19200000 0 1 12949359559828815941 ep1538 238206290332334904541 ep1699 ep1770

noncomputable def ep1779 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3)))) qz254 7394648894767 1920000000 0 1 11433118508244744729 ep1538 210439302167103420961 ep1699 ep1773

noncomputable abbrev qz532 := (@ep1748 ep1699 (BSN.cpow_neg_s_sub_mk qz145 140505 1000 36 3 78364164096 qz146 rfl EMRow48.d24) ep1766)

noncomputable def ep1780 := ep1690 (@ep1697 ep1685 ep1698 ep1682 ep1683 ep1684 ep1685 (@ep1700 ep1692 ep1693 ep1694 ep1746 (ep1747 qz532) rfl) (@ep1767 ep1683 ep1696 ep1685 ep1768 (ep1769 qz532) rfl) rfl rfl) (@ep1776 ep1685 ep1777 ep1687 ep1683 ep1688 ep1685 (@ep1778 ep1771 ep1772 ep1694 ep1746 (ep1769 qz532) rfl) (@ep1779 ep1774 ep1775 ep1685 ep1768 (ep1747 qz532) rfl) rfl rfl)

noncomputable def ep1781 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz246)) (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz246)) ep1687 ep1683 ep1688 ep1685 ep1687 ep1683 ep1688

noncomputable def ep1782 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz246) Bool.false ep1682 ep1683 ep1684 ep1685 Bool.false ep1687 ep1683 ep1688

noncomputable def ep1783 := @ep1654 4461044904337317375 8070450532247928832 88349566599 1152921504606846976 (@ep1655 1 3670016 (ep1656 (@ep1657 1048576 1 1048576 (ep1658 (@ep1659 3160624804 790156201 40000 0 1 (ep1663 rfl) (ep1666 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep1667 3991 2199023255552 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz246)) (@ep1668 3991 2199023255552 30269845077 2199023255552 3991 2199023255552 (@ep1673 15134920543 15134924534 1099511627776 (@ep1679 ep1675 ep1680 ep1677 ep1681 ep1669 ep1670 ep1671 ep1672 (@ep1686 ep1685 ep1674 ep1675 ep1676 ep1677 (@ep1689 ep1685 ep1780) (@ep1689 ep1685 ep1780) rfl) (@ep1781 ep1685 ep1678 ep1675 ep1680 ep1677 (@ep1782 ep1685 ep1780) (@ep1782 ep1685 ep1780) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow48.d25 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz411 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz142 1 36))) (@HMul.hMul Real Real Real qz0 qz245 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz246)))) Bool.false 122852419913033558501 217902164370694078464 3320601623384125 31128880624384868352 := ep1652 (ep1653 ep1783) rfl rfl

noncomputable def EMRow48.d26 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J))

noncomputable abbrev qz533 := (EMRow48.d3 qz548 qz680 (@Enclosure.dec_le_dec qz548 qz680 138478 1000 140505 1000 (@Eq.refl Real qz548) (@Eq.refl Real qz680) rfl rfl rfl) 35 36 1 1)

noncomputable abbrev qz264 := qz533

noncomputable def ep1784 := @Zeta.Certificates.ZIntervalEM.Certificate.mk qz264 (@Enclosure.dec_nonneg qz12 138478 1000 qz13) (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 35 rfl)

noncomputable abbrev qz265 := (Zeta.Certificates.ZIntervalEM.fstVal qz533)

noncomputable def ep1785 := @Enclosure.Real.IsNear.pos_val qz265 ep534 ep535

noncomputable def ep1786 := @Enclosure.Real.IsNear.of_eq qz265 (hardyZApproximantEM 1 35 qz12) Bool.false

noncomputable abbrev qz266 := (Zeta.Certificates.ZIntervalEM.sndVal qz533)

noncomputable def ep1787 := BSN.mul_neg_of_pos_neg_r qz265 qz266 (@ep1785 ep536 ep537 (@ep1786 ep534 ep535 ep536 ep537 (@Eq.refl Real (hardyZApproximantEM 1 35 qz12)) EMRow48.d12) rfl rfl rfl)

noncomputable def ep1788 := @Enclosure.Real.IsNear.neg_val qz266 ep1196 ep1197

noncomputable def ep1789 := @Enclosure.Real.IsNear.of_eq qz266 (hardyZApproximantEM 1 36 qz145) Bool.true

noncomputable def ep1790 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz265) (BSN.hardyZErrorBoundStrong 1 35 qz12)

noncomputable def ep1791 := @Enclosure.norm_gt_of_isNear qz265 (BSN.hardyZErrorBoundStrong 1 35 qz12) Bool.false

noncomputable def ep1792 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 35 qz12) (@HAdd.hAdd Real Real Real qz411 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 35))) (@HMul.hMul Real Real Real qz0 qz223 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226)))) Bool.false 21374458065492963275 36317027395115679744 3749139845649701 36317027395115679744 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz411 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 35))) (@HMul.hMul Real Real Real qz0 qz223 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226)))))

noncomputable def ep1793 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz266) (BSN.hardyZErrorBoundStrong 1 36 qz145)

noncomputable def ep1794 := @Enclosure.norm_gt_of_isNear qz266 (BSN.hardyZErrorBoundStrong 1 36 qz145) Bool.true

noncomputable def ep1795 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 36 qz145) (@HAdd.hAdd Real Real Real qz411 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz142 1 36))) (@HMul.hMul Real Real Real qz0 qz245 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz246)))) Bool.false 122852419913033558501 217902164370694078464 3320601623384125 31128880624384868352 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz411 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz142 1 36))) (@HMul.hMul Real Real Real qz0 qz245 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz142 (@ascPochhammer Complex Complex.instSemiring 3))) qz246)))))

noncomputable def ep1796 := @List.cons EMRow48.d0 (@PSigma.mk Zeta.Certificates.ZIntervalEM Zeta.Certificates.ZIntervalEM.Certificate qz264 (ep1784 (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 36 rfl) (ep1787 (@ep1788 ep1198 ep1199 (@ep1789 ep1196 ep1197 ep1198 ep1199 (@Eq.refl Real (hardyZApproximantEM 1 36 qz145)) EMRow48.d18) rfl rfl rfl)) (ep1790 (hardyZErrorBoundEM 1 35 qz12) (BSN.hardyZErrorBoundEM_le_strong 1 35 qz12 rfl) (@ep1791 Bool.false ep534 ep535 ep536 ep537 21374458065492963275 36317027395115679744 3749139845649701 36317027395115679744 (@ep1786 ep534 ep535 ep536 ep537 (@Eq.refl Real (hardyZApproximantEM 1 35 qz12)) EMRow48.d12) (ep1792 EMRow48.d23) rfl rfl rfl rfl rfl)) (ep1793 (hardyZErrorBoundEM 1 36 qz145) (BSN.hardyZErrorBoundEM_le_strong 1 36 qz145 rfl) (@ep1794 Bool.false ep1196 ep1197 ep1198 ep1199 122852419913033558501 217902164370694078464 3320601623384125 31128880624384868352 (@ep1789 ep1196 ep1197 ep1198 ep1199 (@Eq.refl Real (hardyZApproximantEM 1 36 qz145)) EMRow48.d18) (ep1795 EMRow48.d25) rfl rfl rfl rfl rfl)))) (@List.nil EMRow48.d0)

noncomputable abbrev qz534 := (@Enclosure.dec_le_dec qz548 qz680 138478 1000 140505 1000 (@Eq.refl Real qz548) (@Eq.refl Real qz680) rfl rfl rfl)

noncomputable abbrev qz267 := (Zeta.Certificates.CertifiedZeroIntervals.intervals (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1796 (@List.IsChain.singleton EMRow48.d1 EMRow48.d26 (EMRow48.d2 qz279 qz439 qz534))))

noncomputable abbrev qz535 := (@NonemptyInterval Real Real.instLE)

noncomputable def ep1797 := And (@Eq (Option Real) (@Option.map qz535 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz535 qz267)) (@Option.some Real qz12))

noncomputable def ep1798 := ep1797 (@Eq (Option Real) (@Option.map qz535 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz535 qz267)) (@Option.some Real qz145))

noncomputable def ep1799 := @And.intro (@Eq Nat (@List.length qz535 qz267) 1) ep1798

noncomputable def ep1800 := @And.intro (@Eq (Option Real) (@Option.map qz535 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz535 qz267)) (@Option.some Real qz12))

noncomputable def ep1801 := @ep1800 (@Eq (Option Real) (@Option.map qz535 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz535 qz267)) (@Option.some Real qz145))

noncomputable abbrev qz268 := (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1796 (@List.IsChain.singleton EMRow48.d1 EMRow48.d26 (EMRow48.d2 qz279 qz439 qz534)))

theorem EMRow48.d27 : Zeta.Certificates.BatchSpec 1 138478 1000 140505 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz535 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 1) (And (@Eq (Option Real) (@Option.map qz535 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz535 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz12)) (@Eq (Option Real) (@Option.map qz535 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz535 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz145)))) qz268 (ep1799 (@Eq.refl Nat 1) (ep1801 (@Eq.refl (Option Real) (@Option.some Real qz12)) (@Eq.refl (Option Real) (@Option.some Real qz145))))

theorem solution : Zeta.Certificates.BatchSpec 1 138478 1000 140505 1000 := EMRow48.d27
#print axioms solution
#check solution
