-- Prove2me | solution 1 for RHHeight1000.em_main_0028_0028
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T08:56:58.743038+00:00
-- url     : https://prove2.me/submissions/740db10a-2402-4d4c-ad17-1b1f86fd02cd

import Definitions.Def_RHT1000_Support_20261118_S005
/- Copyright (c) 2026 Salvatore Mercuri, Bhavik Mehta.
Apache 2.0 license; see the source project LICENSE. -/
set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Polynomial
theorem Height20.tangent_three : TangentNumbers.tangentNumber 3 = 16 := by
  unfold TangentNumbers.tangentNumber
  change (TangentNumbers.tangentPoly 5).eval 0 = 16
  norm_num [TangentNumbers.tangentPoly, derivative_add, derivative_mul, derivative_pow, eval_add, eval_mul]

noncomputable def EMRow28.d0 := @PSigma Zeta.Certificates.ZIntervalEM fun (I : Zeta.Certificates.ZIntervalEM) => Zeta.Certificates.ZIntervalEM.Certificate I

noncomputable def EMRow28.d1 := @NonemptyInterval Real Real.instLE

noncomputable def EMRow28.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h

noncomputable def EMRow28.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) (fc sc fb sb : Nat) => Zeta.Certificates.ZIntervalEM.mk (EMRow28.d2 a b h) fc sc fb sb

noncomputable def ep0 := nat_lit 26986075409044028275299783

noncomputable def ep1 := nat_lit 4294967296000000000000000

noncomputable def ep2 := nat_lit 26986075409044045455168967

noncomputable abbrev qz0 := (@instHMul Real Real.instMul)

noncomputable abbrev qz810 := (Enclosure.sfrac Bool.false 2 1)

noncomputable abbrev qz251 := qz810

noncomputable def ep3 := @BSN.isNear_log_image_fff (@HMul.hMul Real Real Real qz0 qz251 Real.pi) 884279719003555 140737488355328 1 500000000000000 ep0 ep1 ep2 ep1 4138529546116343 2251799813685248 250000000130491 65245500000000000000 4138529546116343 2251799813685248 250000000130491 65245500000000000000 481788 262144

noncomputable abbrev qz252 := (@Enclosure.Real.IsNear.mulLit_ff qz810 Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) BSN.pi_near_15 rfl)

noncomputable def ep4 := @ep3 2 262144 qz252 rfl rfl rfl rfl

noncomputable def ep5 := nat_lit 53972150818088056550599566

noncomputable def ep6 := nat_lit 34359738368000000000000000

noncomputable def ep7 := nat_lit 9806206225044028275299783

noncomputable def ep8 := nat_lit 44165944593044028275299783

noncomputable def ep9 := nat_lit 13681445815609410487519367394620474863599256634174726093703677122907123617368241606644861540940610176751640793056574796245399519365549113997355475306157239709119582688278313060810592403844863400465080549957745

noncomputable def ep10 := nat_lit 231714499556395493334623298703961145503103241611736774613091488581016477543539392410113701224645713379230392133956226737605624599560350113120270717249177907454870984269546186598262646369758174842349131395304

noncomputable def ep11 := nat_lit 8978369550011295664474073352761810093897501552430546263638635096022803738134167562509900960712119243631997923545019968443113540909076206607473711060286601587364321108377403290080403445693385008949995305

noncomputable def ep12 := BSN.log_dyadic_bound ep7 ep8 5 4 ep9 524288 260982 ep10 ep11 236759 ep5 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep7) (BSN.artanhQ ep8) 0 4 ep10 ep9 ep11 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz1 := (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))

noncomputable def ep13 := ep4 rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep1 4138529546116343 2251799813685248 250000000130491 65245500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep0) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 34716502058787923820544 18889465931478580854784 1000000000521964 260982000000000000000 4138529546116343 2251799813685248 250000000130491 65245500000000000000 (BSN.log_rat_reduce_isNear ep0 ep1 2 ep5 ep6 236759 524288 24973259072661432 36028797018963968 260982 1000000000000000 rfl rfl rfl rfl (ep12 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep14 := nat_lit 53972150818088090910337934

noncomputable def ep15 := nat_lit 9806206225044045455168967

noncomputable def ep16 := nat_lit 44165944593044045455168967

noncomputable def ep17 := nat_lit 13681445815609453062485491347592146866046743284321690683909457683007658987562290830600045658905080811372395010565947827677605470036294121079488508864180301737865471494204890974265645509835068840465080549957745

noncomputable def ep18 := nat_lit 231714499556396865510889920206523150079811393376960301632499817942333196803513131357563499488546302200815366867712007119763002650772307103678175657719139104636874731038771518520299266622696414842349131395304

noncomputable def ep19 := nat_lit 8978369550011421500876706511871067098718760264493934208903156435737864998391937547068187824077011975074541700434630537294838404525415248443919841847024664017658842168336182958576672102333385008949995305

noncomputable def ep20 := BSN.log_dyadic_bound ep15 ep16 5 4 ep17 524288 260982 ep18 ep19 236759 ep14 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep15) (BSN.artanhQ ep16) 0 4 ep18 ep17 ep19 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep21 := ep13 (BSN.isNear_log_sfrac ep2 ep1 4138529546116343 2251799813685248 250000000130491 65245500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep2) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 34716502058787923820544 18889465931478580854784 1000000000521964 260982000000000000000 4138529546116343 2251799813685248 250000000130491 65245500000000000000 (BSN.log_rat_reduce_isNear ep2 ep1 2 ep14 ep6 236759 524288 24973259072661432 36028797018963968 260982 1000000000000000 rfl rfl rfl rfl (ep20 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable abbrev qz253 := (Real.log (@HMul.hMul Real Real Real qz0 (2 : Real) Real.pi))

theorem EMRow28.d4 : Enclosure.Real.IsNear qz253 Bool.false 120447 65536 1 131072 := @Enclosure.Real.IsNear.of_eq qz253 (Real.log (@HMul.hMul Real Real Real qz0 qz251 Real.pi)) Bool.false 120447 65536 1 131072 BSN.log_two_pi_eq (@Enclosure.Real.IsNear.recentre' (Real.log (@HMul.hMul Real Real Real qz0 qz251 Real.pi)) Bool.false 481788 262144 2 262144 120447 65536 1 131072 (ep21 rfl rfl rfl rfl rfl rfl rfl rfl) rfl)

noncomputable abbrev qz541 := (@instHPow Complex Nat (@NPow.toPow Complex (@Monoid.toNPow Complex (@Semiring.toMonoid Complex Complex.instSemiring))))

noncomputable abbrev qz811 := (@instHAdd Complex Complex.instAdd)

noncomputable abbrev qz812 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (4 : Complex))

noncomputable abbrev qz813 := (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid))

noncomputable abbrev qz814 := (Enclosure.sfrac Bool.false 95415 1000)

noncomputable abbrev qz542 := (@HAdd.hAdd Complex Complex Complex qz811 (@HAdd.hAdd Complex Complex Complex qz811 qz812 (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I (@HDiv.hDiv Complex Complex Complex qz813 (↑qz814) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 4))

noncomputable abbrev qz254 := (@HPow.hPow Complex Nat Complex qz541 qz542 3)

noncomputable abbrev qz2 := qz254

noncomputable def ep22 := Enclosure.Complex.IsNear qz2 Bool.true 18523075339 640000 0 1 Bool.true 6783832634787 64000000 0 1

noncomputable abbrev qz543 := (@instHMul Complex Complex.instMul)

noncomputable abbrev qz255 := qz543

noncomputable abbrev qz3 := qz255

noncomputable abbrev qz256 := qz541

noncomputable abbrev qz257 := qz542

noncomputable abbrev qz4 := (@HPow.hPow Complex Nat Complex qz256 qz257 2)

noncomputable abbrev qz5 := qz257

noncomputable def ep23 := @Enclosure.Complex.IsNear.of_eq qz2 (@HMul.hMul Complex Complex Complex qz3 qz4 qz5) Bool.true 18523075339 640000 0 1 Bool.true 6783832634787 64000000

noncomputable def ep24 := @Enclosure.Complex.IsNear.mul qz4 qz5 Bool.true 18523075339 640000 0 1 Bool.true 6783832634787 64000000 0

noncomputable abbrev qz6 := (Complex.re qz257)

noncomputable abbrev qz7 := (Complex.im qz257)

noncomputable def ep25 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re qz4) qz6) (@HMul.hMul Real Real Real qz0 (Complex.im qz4) qz7) 6141605113 640000 0 1 6190735113 320000

noncomputable def ep26 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re qz4) qz6 361270889 160000 0 1 17000 4000 0 1

noncomputable def ep27 := @Enclosure.Complex.IsNear.re_isNear qz4 Bool.true 361270889 160000 0 1 Bool.false 324411 800 0 1

noncomputable abbrev qz258 := (@HPow.hPow Complex Nat Complex qz541 qz542 1)

noncomputable abbrev qz8 := qz258

noncomputable def ep28 := @Enclosure.Complex.IsNear.of_eq qz4 (@HMul.hMul Complex Complex Complex qz3 qz8 qz5) Bool.true 361270889 160000 0 1 Bool.false 324411 800

noncomputable def ep29 := @Enclosure.Complex.IsNear.mul qz8 qz5 Bool.true 361270889 160000 0 1 Bool.false 324411 800 0

noncomputable abbrev qz9 := (Complex.re qz258)

noncomputable abbrev qz10 := (Complex.im qz258)

noncomputable def ep30 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz9 qz6) (@HMul.hMul Real Real Real qz0 qz10 qz7) 289 16 0 1 364160889 160000

noncomputable def ep31 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz6 17000 4000 0 1 17000 4000 0 1

noncomputable def ep32 := @Enclosure.Complex.IsNear.re_isNear qz8 Bool.false 17000 4000 0 1 Bool.false 190830 4000 0 1

noncomputable def ep33 := @Enclosure.Complex.IsNear.of_eq qz8 qz5 Bool.false 17000 4000 0 1 Bool.false 190830 4000 0

noncomputable abbrev qz259 := qz814

noncomputable abbrev qz11 := qz259

noncomputable abbrev qz544 := (Enclosure.sfrac Bool.false 17000 4000)

noncomputable abbrev qz260 := (Complex.mk qz544 (Enclosure.sfrac Bool.false 190830 4000))

noncomputable def ep34 := @Enclosure.Complex.IsNear.of_eq qz5 qz260 Bool.false 17000 4000 0 1 Bool.false 190830 4000 0 1 (BSN.w_shift_mk qz11 Bool.false 95415 1000 4 (@Eq.refl Real qz11) rfl)

noncomputable abbrev qz261 := (Enclosure.sfrac Bool.false 190830 4000)

noncomputable abbrev qz815 := (Enclosure.Real.IsNear.const Bool.false 17000 4000)

noncomputable abbrev qz12 := (@ep33 1 (BSN.pow_one_c qz257) (ep34 (@Enclosure.Complex.IsNear.mk qz544 qz261 Bool.false 17000 4000 0 1 Bool.false 190830 4000 0 1 qz815 (Enclosure.Real.IsNear.const Bool.false 190830 4000))))

noncomputable abbrev qz13 := (ep34 (@Enclosure.Complex.IsNear.mk qz544 qz261 Bool.false 17000 4000 0 1 Bool.false 190830 4000 0 1 qz815 (Enclosure.Real.IsNear.const Bool.false 190830 4000)))

noncomputable abbrev qz545 := (@Enclosure.Complex.IsNear.re_isNear qz5 Bool.false 17000 4000 0 1 Bool.false 190830 4000 0 1 qz13)

noncomputable def ep35 := @ep31 289 16 0 1 (ep32 qz12) qz545

noncomputable def ep36 := @Enclosure.Real.IsNear.mulLit_ff qz10 qz7 190830 4000 0 1 190830 4000 0 1

noncomputable def ep37 := @Enclosure.Complex.IsNear.im_isNear qz8 Bool.false 17000 4000 0 1 Bool.false 190830 4000 0 1

noncomputable abbrev qz546 := (@Enclosure.Complex.IsNear.im_isNear qz5 Bool.false 17000 4000 0 1 Bool.false 190830 4000 0 1 qz13)

noncomputable def ep38 := @ep36 364160889 160000 0 1 (ep37 qz12) qz546

noncomputable def ep39 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz9 qz7) (@HMul.hMul Real Real Real qz0 qz10 qz6) 324411 1600 0 1 324411 1600

noncomputable def ep40 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz7 17000 4000 0 1 190830 4000 0 1

noncomputable def ep41 := @ep40 324411 1600 0 1 (ep32 qz12) qz546

noncomputable def ep42 := @Enclosure.Real.IsNear.mulLit_ff qz10 qz6 190830 4000 0 1 17000 4000 0 1

noncomputable def ep43 := @ep42 324411 1600 0 1 (ep37 qz12) qz545

noncomputable abbrev qz547 := (@ep28 0 1 (BSN.pow_succ_c qz5 1 2 rfl) (@ep29 1 (@ep30 0 1 5780334224 361270889 160000 0 1 (ep35 rfl) (ep38 rfl) rfl rfl) (@ep39 0 1 1038115200 324411 800 0 1 (ep41 rfl) (ep43 rfl) rfl rfl)))

noncomputable def ep44 := @ep26 6141605113 640000 0 1 (ep27 qz547) qz545

noncomputable def ep45 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz4) qz7 324411 800 0 1 190830 4000 0 1

noncomputable def ep46 := @Enclosure.Complex.IsNear.im_isNear qz4 Bool.true 361270889 160000 0 1 Bool.false 324411 800 0 1

noncomputable def ep47 := @ep45 6190735113 320000 0 1 (ep46 qz547) qz546

noncomputable def ep48 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re qz4) qz7) (@HMul.hMul Real Real Real qz0 (Complex.im qz4) qz6) 6894132374787 64000000 0 1 5514987 3200

noncomputable def ep49 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re qz4) qz7 361270889 160000 0 1 190830 4000 0 1

noncomputable def ep50 := @ep49 6894132374787 64000000 0 1 (ep27 qz547) qz546

noncomputable def ep51 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz4) qz6 324411 800 0 1 17000 4000 0 1

noncomputable def ep52 := @ep51 5514987 3200 0 1 (ep46 qz547) qz545

theorem EMRow28.d5 : ep22 := @ep23 0 1 (BSN.pow_succ_c qz5 2 3 rfl) (@ep24 1 (@ep25 0 1 5927384108480000 18523075339 640000 0 1 (ep44 rfl) (ep47 rfl) rfl rfl) (@ep48 0 1 21708264431318400 6783832634787 64000000 0 1 (ep50 rfl) (ep52 rfl) rfl rfl))

noncomputable def ep53 := nat_lit 8589934592000000000000000

noncomputable def ep54 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 ep0 ep53 ep2 ep53 600168 524288 1 260982 600168 524288 1 260982 300084 262144 2 262144 BSN.pi_near_15 rfl rfl rfl

noncomputable def ep55 := nat_lit 17179869184000000000000000

noncomputable def ep56 := nat_lit 18396140817044028275299783

noncomputable def ep57 := nat_lit 35576010001044028275299783

noncomputable def ep58 := nat_lit 145019262663961446558303139663424756232419223153299357158415217874016130572233056993847515999529612750616182853355499335896178729185698845314776375864537073527142908641610750276034469165612529925303649396973267518946591078603565291376312767403717761600170009932259137778521478520425507632472584532570900560707662248426541531715360699177249902784721815296292248142738824858695953661559845440650653128788875447728828657762006237171740033404723254477174341920697506370253193455781322964835857351124092897592956162654178130575

noncomputable def ep59 := nat_lit 15500762873619990602332184736899274490522931101512051618692838888825382235673431503644115344741331161500627469184702974962114537943617674254904297224139410345221262767191485292268260077615645253784097850065864022184521411511133693085443040736512010941548648374196772723338837137976260321103066698629790037694560548409922339907589559883712609967105556007429010014773911317423638534096849366294542840133852248768895750397896505791271178551667935288585787166713880920071720072716082683081155281219708172458141800988558163320

noncomputable def ep60 := nat_lit 12900190794487083783367107939442176642390171280542213571554777169279725287102813254708993369099729304728646904879886535518616983985412662170766446331701281703998252143668221340329975389245922410714088123244705567402747658401492589451585970559635763980329972215329212888079422466283203384882259392047898400615815810081169907384366653346471604103896809335921621947903075223769953790093549808584241881353287841076643853121427928248525828402335494512605306631304432120211393210317325496757155861061354331245840675149075

noncomputable def ep61 := BSN.log_dyadic_bound ep56 ep57 11 10 ep58 524288 260982 ep59 ep60 600168 ep5 ep55 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep56) (BSN.artanhQ ep57) 0 10 ep59 ep58 ep60 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep62 := nat_lit 18396140817044045455168967

noncomputable def ep63 := nat_lit 35576010001044045455168967

noncomputable def ep64 := nat_lit 145019262663962847171784895425483977818796535899227200426399035286881207006285364467913811844950531107314785650583974625982406238691319033447632878979985852280879486690814033867010958364699188952871572448188560932645032521756218245629809291975913196623825614492380080480004685076434733043183791438169545293975334857826316990371107134320667652578346815517853870648072772035977941843998949310557583393428557296298890786965786350523173236912472938174255438182435383147950274229549088258679583524155427309880956162654178130575

noncomputable def ep65 := nat_lit 15500762873620157189619721156942591192100275120160672416764593300158228469749443299607348495591439275767946573253526107895503597951484257520435868240203420954375895980141891044871083424251900562230440202302413072793440172565998181227591194192658878334739610458454844032013325963992941389843551995646587189684848765634635122388286241104146031552341815777883628509454807838726994150833304950745987647656768534710890974432620160470644835720379148964170536679305861738540146791997074363921127776563807649880221800988558163320

noncomputable def ep66 := nat_lit 12900190794487324729109480814509220959173684627296055849229843377126536688487849343376525559792931631054411655715865486295286288812423905434305314401904993536755333953308594664509631000767632482919425633906965368325056855874260596615770736441041599390097968820060635361729170158825410327022636428624381203910573184452046894301676992229743752846881064485858738985580654099214803581683226335297196686880535448467637789069028262446657986458573827723305156755787640135484017403116612632808333639900906331245840675149075

noncomputable def ep67 := BSN.log_dyadic_bound ep62 ep63 11 10 ep64 524288 260982 ep65 ep66 600168 ep14 ep55 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep62) (BSN.artanhQ ep63) 0 10 ep65 ep64 ep66 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep68 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 300084 262144 2 262144 75021 65536 1 131072 (ep54 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep53 600168 524288 1 260982 Bool.false (BSN.logfrac_isNear ep5 ep55 1 ep0 ep53 600168 524288 260982 rfl rfl rfl (ep61 rfl))) (BSN.isNear_log_sfrac ep2 ep53 600168 524288 1 260982 Bool.false (BSN.logfrac_isNear ep14 ep55 1 ep2 ep53 600168 524288 260982 rfl rfl rfl (ep67 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl

theorem EMRow28.d6 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 75021 65536 1 131072 := ep68

noncomputable abbrev qz548 := qz811

noncomputable abbrev qz549 := (@HDiv.hDiv Complex Complex Complex qz813 (1 : Complex) (2 : Complex))

noncomputable abbrev qz262 := (@HAdd.hAdd Complex Complex Complex qz548 qz549 (@HMul.hMul Complex Complex Complex qz543 Complex.I ↑qz814))

noncomputable abbrev qz14 := qz262

noncomputable abbrev qz263 := qz548

noncomputable abbrev qz15 := qz263

noncomputable abbrev qz816 := (@instHPow Complex Complex Complex.instPow)

noncomputable abbrev qz16 := qz816

noncomputable abbrev qz17 := (@Neg.neg Complex Complex.instNeg qz262)

noncomputable abbrev qz817 := (@HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast 8) qz17)

noncomputable def ep69 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 9) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz14 8) qz817) Bool.true 121926352165 274877906944 29995690989017 11956364318343168 Bool.false 28445369709 137438953472 14973110512237 5978182159171584

noncomputable def ep70 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz14 8) qz817 Bool.true 36158892065 274877906944 26847063503501 11956364318343168 Bool.false 11190047857 274877906944 26806995545999 11956364318343168 Bool.true

noncomputable abbrev qz818 := (@HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast 7) qz17)

noncomputable def ep71 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 8) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz14 7) qz818) Bool.true 36158892065 274877906944 26847063503501 11956364318343168 Bool.false 11190047857 274877906944 26806995545999 11956364318343168

noncomputable def ep72 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz14 7) qz818 Bool.false 31316347733 137438953472 8802084097483 4483636619378688 Bool.true 20969825413 274877906944 70340346114635 35869092955029504 Bool.true

noncomputable abbrev qz819 := (@HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast 6) qz17)

noncomputable def ep73 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 7) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz14 6) qz819) Bool.false 31316347733 137438953472 8802084097483 4483636619378688 Bool.true 20969825413 274877906944 70340346114635 35869092955029504

noncomputable def ep74 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz14 6) qz819 Bool.false 34200396823 274877906944 59561887385617 35869092955029504 Bool.false 87586474607 274877906944 59436712327975 35869092955029504 Bool.false

noncomputable abbrev qz820 := (@Nat.cast Complex Complex.instNatCast 5)

noncomputable abbrev qz18 := qz820

noncomputable def ep75 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 6) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz14 5) (@HPow.hPow Complex Complex Complex qz16 qz18 qz17)) Bool.false 34200396823 274877906944 59561887385617 35869092955029504 Bool.false 87586474607 274877906944 59436712327975 35869092955029504

noncomputable def ep76 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz14 5) (@HPow.hPow Complex Complex Complex qz16 qz18 qz17) Bool.false 148645184661 274877906944 15875438116165 11956364318343168 Bool.false 132463372269 274877906944 15846618830839 11956364318343168 Bool.true

noncomputable abbrev qz550 := (@Nat.cast Complex Complex.instNatCast 4)

noncomputable abbrev qz264 := qz550

noncomputable abbrev qz19 := qz264

noncomputable def ep77 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 5) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz14 4) (@HPow.hPow Complex Complex Complex qz16 qz19 qz17)) Bool.false 148645184661 274877906944 15875438116165 11956364318343168 Bool.false 132463372269 274877906944 15846618830839 11956364318343168

noncomputable def ep78 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz14 4) (@HPow.hPow Complex Complex Complex qz16 qz19 qz17) Bool.false 4612638249 68719476736 17144206114541 17934546477514752 Bool.false 44123293173 68719476736 17122422990929 17934546477514752 Bool.false

noncomputable abbrev qz551 := (@Nat.cast Complex Complex.instNatCast 3)

noncomputable def ep79 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 4) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz14 3) (@HPow.hPow Complex Complex Complex qz16 qz551 qz17)) Bool.false 4612638249 68719476736 17144206114541 17934546477514752 Bool.false 44123293173 68719476736 17122422990929 17934546477514752

noncomputable def ep80 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz14 3) (@HPow.hPow Complex Complex Complex qz16 qz551 qz17) Bool.false 10386009815 34359738368 9453062204183 17934546477514752 Bool.false 3944036169 34359738368 9396660862199 17934546477514752 Bool.true

noncomputable abbrev qz552 := (@Nat.cast Complex Complex.instNatCast 2)

noncomputable def ep81 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 3) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz14 2) (@HPow.hPow Complex Complex Complex qz16 qz552 qz17)) Bool.false 10386009815 34359738368 9453062204183 17934546477514752 Bool.false 3944036169 34359738368 9396660862199 17934546477514752

noncomputable def ep82 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz14 2) (@HPow.hPow Complex Complex Complex qz16 qz552 qz17) Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.true

noncomputable abbrev qz553 := (Enclosure.sfrac Bool.false 0 1)

noncomputable abbrev qz265 := qz553

noncomputable def ep83 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz265) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz14)

noncomputable abbrev qz266 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2)))

noncomputable abbrev qz267 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log qz810))

noncomputable def ep84 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz552 qz17) (Complex.mk (@HMul.hMul Real Real Real qz0 qz266 (Real.cos qz267)) (@HMul.hMul Real Real Real qz0 qz266 (@Neg.neg Real Real.instNeg (Real.sin qz267)))) Bool.true 23973728553 34359738368 9453062204183 17934546477514752 Bool.false 3944036169 34359738368 9396660862199 17934546477514752 (BSN.cpow_neg_s_mk qz11 95415 1000 2 (@Eq.refl Real qz11) rfl)

noncomputable abbrev qz268 := (@Nat.cast Real Real.instNatCast 1)

noncomputable def ep85 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 2)) 741455 524288 1 524288 185363 185365 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 2)) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2) qz268)) Bool.false 741455 524288 1 524288 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2) qz268)) Bool.false 741455 524288 1 524288 741455 524288 1 524288 (BSN.sqrt_enclosure 2 1 370727 370728 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep86 := BSN.log_dyadic_bound 1 3 6 5 613814355 262144 130491 24381081 945 181704 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 1) (BSN.artanhQ 3) 0 5 24381081 613814355 945 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep87 := nat_lit 939598279022791561238646693236881

noncomputable def ep88 := nat_lit 31901471898837980949691369446728269824

noncomputable def ep89 := nat_lit 478522078482569714245370541700924047360

noncomputable abbrev qz269 := (BSN.cosEvenQ 1073741824)

noncomputable abbrev qz270 := (BSN.cosOddQ 1073741824)

noncomputable def ep90 := BSN.cos_dyadic_bound_f 175079603 1073741824 2 1 524288 261237 ep87 ep88 ep87 ep87 ep89 ep87 517333 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 175079603) qz269 0 1 ep87 ep88 ep87 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 175079603) qz270 0 1 ep87 ep89 ep87 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz271 := (@Nat.cast Real Real.instNatCast 262144)

noncomputable abbrev qz272 := (Real.log qz810)

noncomputable abbrev qz273 := (Enclosure.Real.IsNear.const Bool.false 95415 1000)

noncomputable abbrev qz274 := (@Nat.cast Real Real.instNatCast 37778931862957161709568)

noncomputable abbrev qz554 := (BSN.isNear_log_sfrac 2 1 181704 262144 1 130491 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 181704 262144 130491 rfl rfl rfl (ep86 rfl)))

noncomputable abbrev qz821 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 17337287) qz271)

noncomputable abbrev qz822 := (@Nat.cast Real Real.instNatCast 6160065906243927015424)

noncomputable def ep91 := @Enclosure.Real.IsNear.cos_image qz267 qz821 Bool.false 17337287 262144 3 4096 Bool.true 517333 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz267 Bool.false 433432179 6553600 6361 8699400 17337287 262144 3 4096 (@Enclosure.Real.IsNear.mulLit_ff qz11 qz272 95415 1000 0 1 181704 262144 1 130491 433432179 6553600 6361 8699400 qz273 qz554 rfl) rfl) (Enclosure.sfrac_false_div 17337287 262144) (BSN.cos_reduce2 qz821 (@HDiv.hDiv Real Real Real qz1 qz822 qz274) 226375608064910080 72057594037927936 Bool.false 517333 524288 10 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q2 17337287 262144 226375608064910080 72057594037927936 10 6160065906243927015424 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 517333 524288 6160065906243927015424 37778931862957161709568 175079603 1073741824 261237 260982 (ep90 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep92 := nat_lit 159507359494189904748456847233641349120

noncomputable def ep93 := nat_lit 1116551516459329333239197930635489443840

noncomputable abbrev qz275 := (BSN.sinEvenQ 1073741824)

noncomputable abbrev qz276 := (BSN.sinOddQ 1073741824)

noncomputable def ep94 := BSN.sin_dyadic_bound_f 175079603 1073741824 2 1 524288 261237 ep87 ep92 ep87 ep87 ep93 ep87 85109 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 175079603) qz275 0 1 ep87 ep92 ep87 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 175079603) qz276 0 1 ep87 ep93 ep87 rfl rfl rfl rfl) rfl rfl

noncomputable def ep95 := @Enclosure.Real.IsNear.sin_image qz267 qz821 Bool.false 17337287 262144 3 4096 Bool.true 85109 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz267 Bool.false 433432179 6553600 6361 8699400 17337287 262144 3 4096 (@Enclosure.Real.IsNear.mulLit_ff qz11 qz272 95415 1000 0 1 181704 262144 1 130491 433432179 6553600 6361 8699400 qz273 qz554 rfl) rfl) (Enclosure.sfrac_false_div 17337287 262144) (BSN.sin_reduce2 qz821 (@HDiv.hDiv Real Real Real qz1 qz822 qz274) 226375608064910080 72057594037927936 Bool.false 85109 524288 10 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q2 17337287 262144 226375608064910080 72057594037927936 10 6160065906243927015424 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 85109 524288 6160065906243927015424 37778931862957161709568 175079603 1073741824 261237 260982 (ep94 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz555 := (@Enclosure.Real.IsNear.recentre' qz266 Bool.false 370728 524288 2 524288 46341 65536 1 262144 (ep85 rfl rfl) rfl)

noncomputable def ep96 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz266 (Real.cos qz267)) (@HMul.hMul Real Real Real qz0 qz266 (@Neg.neg Real Real.instNeg (Real.sin qz267))) Bool.true 23973728553 34359738368 9453062204183 17934546477514752 Bool.false 3944036169 34359738368 9396660862199 17934546477514752 (@Enclosure.Real.IsNear.mulLit_ft qz266 (Real.cos qz267) 46341 65536 1 262144 517333 524288 395569 534491136 23973728553 34359738368 9453062204183 17934546477514752 qz555 (@Enclosure.Real.IsNear.recentre' (Real.cos qz267) Bool.true 517333 524288 395569 534491136 517333 524288 395569 534491136 (ep91 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz266 (@Neg.neg Real Real.instNeg (Real.sin qz267)) 46341 65536 1 262144 85109 524288 395569 534491136 3944036169 34359738368 9396660862199 17934546477514752 qz555 (@Enclosure.Real.IsNear.neg (Real.sin qz267) Bool.true 85109 524288 395569 534491136 (@Enclosure.Real.IsNear.recentre' (Real.sin qz267) Bool.true 85109 524288 395569 534491136 85109 524288 395569 534491136 (ep95 rfl rfl) rfl)) rfl)

noncomputable abbrev qz823 := (Enclosure.Real.IsNear.const Bool.false 0 1)

noncomputable abbrev qz277 := qz823

noncomputable def ep97 := @ep82 23973728553 34359738368 9453062204183 17934546477514752 Bool.false 3944036169 34359738368 9396660862199 17934546477514752 Bool.false 10386009815 10386009815 34359738368 9453062204183 17934546477514752 Bool.false 3944036169 3944036169 34359738368 9396660862199 17934546477514752 (ep83 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz265 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz277)) (ep84 ep96) rfl rfl

noncomputable abbrev qz278 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 3)))

noncomputable abbrev qz279 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 3 1)))

noncomputable def ep98 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz551 qz17) (Complex.mk (@HMul.hMul Real Real Real qz0 qz278 (Real.cos qz279)) (@HMul.hMul Real Real Real qz0 qz278 (@Neg.neg Real Real.instNeg (Real.sin qz279)))) Bool.true 16159381381 68719476736 1281857318393 2989091079585792 Bool.false 36235220835 68719476736 1287627021455 2989091079585792 (BSN.cpow_neg_s_mk qz11 95415 1000 3 (@Eq.refl Real qz11) rfl)

noncomputable def ep99 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 3)) 908093 524288 1 524288 151348 151350 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 3)) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3) qz268)) Bool.false 908093 524288 1 524288 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3) qz268)) Bool.false 908093 524288 1 524288 908093 524288 1 524288 (BSN.sqrt_enclosure 3 1 454046 454047 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep100 := BSN.log_dyadic_bound 1 2 10 9 171633298636800 262144 130491 16925142283965 34459425 287994 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP 1) (BSN.artanhQ 2) 0 9 16925142283965 171633298636800 34459425 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep101 := nat_lit 5220700417892955486284780150433083555797645759468172494689254653528456034241

noncomputable def ep102 := nat_lit 71239273651864456168798555229954474558164150722024956391463162036118429368320

noncomputable def ep103 := nat_lit 5454213181156467732164255102720123855020227699023129471704749657027508161

noncomputable def ep104 := nat_lit 15651192827316553523390011941093810419682896823006471225124354461271313086401

noncomputable def ep105 := nat_lit 3205767314333900527595934985347951355117386782491123037615842291625329321574400

noncomputable def ep106 := BSN.cos_dyadic_bound_f 1236207897 1073741824 3 2 524288 261237 ep101 ep102 ep103 ep104 ep105 ep103 213538 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1236207897) qz269 0 2 ep101 ep102 ep103 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1236207897) qz270 0 2 ep104 ep105 ep103 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz280 := (@Nat.cast Real Real.instNatCast 524288)

noncomputable abbrev qz281 := (Real.log (Enclosure.sfrac Bool.false 3 1))

noncomputable abbrev qz282 := (@Nat.cast Real Real.instNatCast 75557863725914323419136)

noncomputable abbrev qz556 := (BSN.isNear_log_sfrac 3 1 287994 262144 1 130491 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 287994 262144 130491 rfl rfl rfl (ep100 rfl)))

noncomputable abbrev qz824 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 54957895) qz280)

noncomputable def ep107 := @Enclosure.Real.IsNear.cos_image qz279 qz824 Bool.false 54957895 524288 3 4096 Bool.true 213538 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz279 Bool.false 2747894751 26214400 6361 8699400 54957895 524288 3 4096 (@Enclosure.Real.IsNear.mulLit_ff qz11 qz281 95415 1000 0 1 287994 262144 1 130491 2747894751 26214400 6361 8699400 qz273 qz556 rfl) rfl) (Enclosure.sfrac_false_div 54957895 524288) (BSN.cos_reduce2 qz824 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 86990397303191030988800) qz282) 226375608064910080 72057594037927936 Bool.false 213538 524288 16 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q2 54957895 524288 226375608064910080 72057594037927936 16 86990397303191030988800 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 213538 524288 86990397303191030988800 75557863725914323419136 1236207897 1073741824 261237 260982 (ep106 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep108 := nat_lit 9392897381662394701126872866697374301351746184883491986863294576625598855105

noncomputable def ep109 := nat_lit 641153462866780105519186997069590271023477356498224607523168458325065864314880

noncomputable def ep110 := nat_lit 24591614892536780412337353475945862017298826306039298708354440010765190559681

noncomputable def ep111 := nat_lit 11754480152557635267851761612942488302097084869134117804591421735959540845772800

noncomputable def ep112 := BSN.sin_dyadic_bound_f 1236207897 1073741824 3 2 524288 261237 ep108 ep109 ep103 ep110 ep111 ep103 478830 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1236207897) qz275 0 2 ep108 ep109 ep103 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1236207897) qz276 0 2 ep110 ep111 ep103 rfl rfl rfl rfl) rfl rfl

noncomputable def ep113 := @Enclosure.Real.IsNear.sin_image qz279 qz824 Bool.false 54957895 524288 3 4096 Bool.true 478830 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz279 Bool.false 2747894751 26214400 6361 8699400 54957895 524288 3 4096 (@Enclosure.Real.IsNear.mulLit_ff qz11 qz281 95415 1000 0 1 287994 262144 1 130491 2747894751 26214400 6361 8699400 qz273 qz556 rfl) rfl) (Enclosure.sfrac_false_div 54957895 524288) (BSN.sin_reduce2 qz824 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 86990397303191030988800) qz282) 226375608064910080 72057594037927936 Bool.false 478830 524288 16 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q2 54957895 524288 226375608064910080 72057594037927936 16 86990397303191030988800 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 478830 524288 86990397303191030988800 75557863725914323419136 1236207897 1073741824 261237 260982 (ep112 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz557 := (@Enclosure.Real.IsNear.recentre' qz278 Bool.false 302698 524288 2 524288 151349 262144 1 262144 (ep99 rfl rfl) rfl)

noncomputable def ep114 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz278 (Real.cos qz279)) (@HMul.hMul Real Real Real qz0 qz278 (@Neg.neg Real Real.instNeg (Real.sin qz279))) Bool.true 16159381381 68719476736 1281857318393 2989091079585792 Bool.false 36235220835 68719476736 1287627021455 2989091079585792 (@Enclosure.Real.IsNear.mulLit_ft qz278 (Real.cos qz279) 151349 262144 1 262144 106769 262144 395569 534491136 16159381381 68719476736 1281857318393 2989091079585792 qz557 (@Enclosure.Real.IsNear.recentre' (Real.cos qz279) Bool.true 213538 524288 395569 534491136 106769 262144 395569 534491136 (ep107 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz278 (@Neg.neg Real Real.instNeg (Real.sin qz279)) 151349 262144 1 262144 239415 262144 395569 534491136 36235220835 68719476736 1287627021455 2989091079585792 qz557 (@Enclosure.Real.IsNear.neg (Real.sin qz279) Bool.true 239415 262144 395569 534491136 (@Enclosure.Real.IsNear.recentre' (Real.sin qz279) Bool.true 478830 524288 395569 534491136 239415 262144 395569 534491136 (ep113 rfl rfl) rfl)) rfl)

noncomputable def ep115 := @ep80 16159381381 68719476736 1281857318393 2989091079585792 Bool.false 36235220835 68719476736 1287627021455 2989091079585792 Bool.false 158489043421869637632 4612638249 68719476736 17144206114541 17934546477514752 Bool.false 1516064809358840561664 44123293173 68719476736 17122422990929 17934546477514752 (ep81 (BSN.head_sum_c_succ qz14 2 3 rfl rfl) (ep97 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep98 ep114) rfl rfl

noncomputable abbrev qz283 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 4)))

noncomputable abbrev qz284 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 4 1)))

noncomputable def ep116 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz19 qz17) (Complex.mk (@HMul.hMul Real Real Real qz0 qz283 (Real.cos qz284)) (@HMul.hMul Real Real Real qz0 qz283 (@Neg.neg Real Real.instNeg (Real.sin qz284)))) Bool.false 130194631665 274877906944 13337902119413 35869092955029504 Bool.true 44029800423 274877906944 13295010510659 35869092955029504 (BSN.cpow_neg_s_mk qz11 95415 1000 4 (@Eq.refl Real qz11) rfl)

noncomputable def ep117 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 4)) 1048577 524288 1 524288 131071 131072 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 4)) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4) qz268)) Bool.false 1048577 524288 1 524288 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4) qz268)) Bool.false 1048577 524288 1 524288 1048577 524288 1 524288 (BSN.sqrt_enclosure 4 1 524288 524289 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep118 := nat_lit 318077276165597140789031982421875

noncomputable def ep119 := nat_lit 49379992292270016474244603430625

noncomputable def ep120 := nat_lit 20095619060363156210525625

noncomputable def ep121 := BSN.log_dyadic_bound 3 5 14 13 ep118 262144 130491 ep119 ep120 363408 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base13 (BSN.artanhP 3) (BSN.artanhQ 5) 0 13 ep119 ep118 ep120 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep122 := nat_lit 15033572464364664979818347091790096

noncomputable def ep123 := BSN.cos_dyadic_bound_f 350159206 1073741824 2 1 524288 261237 ep122 ep88 ep122 ep122 ep89 ep122 496655 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 350159206) qz269 0 1 ep122 ep88 ep122 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 350159206) qz270 0 1 ep122 ep89 ep122 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz285 := (@Nat.cast Real Real.instNatCast 131072)

noncomputable abbrev qz286 := (Real.log (Enclosure.sfrac Bool.false 4 1))

noncomputable abbrev qz558 := (BSN.isNear_log_sfrac 4 1 363408 262144 1 130491 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 363408 262144 130491 rfl rfl rfl (ep121 rfl)))

noncomputable abbrev qz559 := (@Nat.cast Real Real.instNatCast 18889465931478580854784)

noncomputable abbrev qz825 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 17337287) qz285)

noncomputable def ep124 := @Enclosure.Real.IsNear.cos_image qz284 qz825 Bool.false 17337287 131072 3 4096 Bool.false 496655 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz284 Bool.false 433432179 3276800 6361 8699400 17337287 131072 3 4096 (@Enclosure.Real.IsNear.mulLit_ff qz11 qz286 95415 1000 0 1 363408 262144 1 130491 433432179 3276800 6361 8699400 qz273 qz558 rfl) rfl) (Enclosure.sfrac_false_div 17337287 131072) (BSN.cos_reduce0 qz825 (@HDiv.hDiv Real Real Real qz1 qz822 qz559) 226375608064910080 72057594037927936 Bool.false 496655 524288 21 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q0 17337287 131072 226375608064910080 72057594037927936 21 6160065906243927015424 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 496655 524288 6160065906243927015424 18889465931478580854784 350159206 1073741824 261237 260982 (ep123 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep125 := BSN.sin_dyadic_bound_f 350159206 1073741824 2 1 524288 261237 ep122 ep92 ep122 ep122 ep93 ep122 167961 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 350159206) qz275 0 1 ep122 ep92 ep122 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 350159206) qz276 0 1 ep122 ep93 ep122 rfl rfl rfl rfl) rfl rfl

noncomputable def ep126 := @Enclosure.Real.IsNear.sin_image qz284 qz825 Bool.false 17337287 131072 3 4096 Bool.false 167961 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz284 Bool.false 433432179 3276800 6361 8699400 17337287 131072 3 4096 (@Enclosure.Real.IsNear.mulLit_ff qz11 qz286 95415 1000 0 1 363408 262144 1 130491 433432179 3276800 6361 8699400 qz273 qz558 rfl) rfl) (Enclosure.sfrac_false_div 17337287 131072) (BSN.sin_reduce0 qz825 (@HDiv.hDiv Real Real Real qz1 qz822 qz559) 226375608064910080 72057594037927936 Bool.false 167961 524288 21 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q0 17337287 131072 226375608064910080 72057594037927936 21 6160065906243927015424 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 167961 524288 6160065906243927015424 18889465931478580854784 350159206 1073741824 261237 260982 (ep125 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz560 := (@Enclosure.Real.IsNear.recentre' qz283 Bool.false 262143 524288 1 524288 262143 524288 1 524288 (ep117 rfl rfl) rfl)

noncomputable def ep127 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz283 (Real.cos qz284)) (@HMul.hMul Real Real Real qz0 qz283 (@Neg.neg Real Real.instNeg (Real.sin qz284))) Bool.false 130194631665 274877906944 13337902119413 35869092955029504 Bool.true 44029800423 274877906944 13295010510659 35869092955029504 (@Enclosure.Real.IsNear.mulLit_ff qz283 (Real.cos qz284) 262143 524288 1 524288 496655 524288 395569 534491136 130194631665 274877906944 13337902119413 35869092955029504 qz560 (@Enclosure.Real.IsNear.recentre' (Real.cos qz284) Bool.false 496655 524288 395569 534491136 496655 524288 395569 534491136 (ep124 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz283 (@Neg.neg Real Real.instNeg (Real.sin qz284)) 262143 524288 1 524288 167961 524288 395569 534491136 44029800423 274877906944 13295010510659 35869092955029504 qz560 (@Enclosure.Real.IsNear.neg (Real.sin qz284) Bool.false 167961 524288 395569 534491136 (@Enclosure.Real.IsNear.recentre' (Real.sin qz284) Bool.false 167961 524288 395569 534491136 167961 524288 395569 534491136 (ep126 rfl rfl) rfl)) rfl)

noncomputable def ep128 := @ep78 130194631665 274877906944 13337902119413 35869092955029504 Bool.true 44029800423 274877906944 13295010510659 35869092955029504 Bool.false 10214819309230013546496 148645184661 274877906944 15875438116165 11956364318343168 Bool.false 9102813629011653033984 132463372269 274877906944 15846618830839 11956364318343168 (ep79 (BSN.head_sum_c_succ qz14 3 4 rfl rfl) (ep115 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep116 ep127) rfl rfl

noncomputable abbrev qz561 := (@Nat.cast Real Real.instNatCast 5)

noncomputable abbrev qz287 := (@Inv.inv Real Real.instInv (Real.sqrt qz561))

noncomputable abbrev qz288 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 5 1)))

noncomputable def ep129 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz18 qz17) (Complex.mk (@HMul.hMul Real Real Real qz0 qz287 (Real.cos qz288)) (@HMul.hMul Real Real Real qz0 qz287 (@Neg.neg Real Real.instNeg (Real.sin qz288)))) Bool.true 57222393919 137438953472 5967786518561 17934546477514752 Bool.true 22438448831 137438953472 5948427917729 17934546477514752 (BSN.cpow_neg_s_mk qz11 95415 1000 5 (@Eq.refl Real qz11) rfl)

noncomputable def ep130 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz561) 1172343 524288 1 524288 117234 117235 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz561) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz561 qz268)) Bool.false 1172343 524288 1 524288 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz561 qz268)) Bool.false 1172343 524288 1 524288 1172343 524288 1 524288 (BSN.sqrt_enclosure 5 1 586171 586172 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep131 := nat_lit 11734546589655452485523914939250625

noncomputable def ep132 := nat_lit 2429970938528035899633153341031900

noncomputable def ep133 := nat_lit 824199001261152424427520000

noncomputable def ep134 := BSN.log_dyadic_bound 2 3 17 16 ep131 262144 130491 ep132 ep133 421904 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base16 (BSN.artanhP 2) (BSN.artanhQ 3) 0 16 ep132 ep131 ep133 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep135 := nat_lit 10979688508742516793957659855052724398003746264719808239467276476580982947840

noncomputable def ep136 := nat_lit 7451227934959324776258576034504038777082338679688432416348747887129133056

noncomputable def ep137 := nat_lit 28744263153859514601203738116320319265323106906880002212787826132561508171776

noncomputable def ep138 := BSN.sin_dyadic_bound_f 1285370952 1073741824 3 2 524288 261237 ep135 ep109 ep136 ep137 ep111 ep136 488102 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1285370952) qz275 0 2 ep135 ep109 ep136 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1285370952) qz276 0 2 ep137 ep111 ep136 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz289 := (Real.log (Enclosure.sfrac Bool.false 5 1))

noncomputable abbrev qz562 := (BSN.isNear_log_sfrac 5 1 421904 262144 1 130491 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 421904 262144 130491 rfl rfl rfl (ep134 rfl)))

noncomputable abbrev qz826 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 20127985) qz285)

noncomputable def ep139 := @Enclosure.Real.IsNear.cos_image qz288 qz826 Bool.false 20127985 131072 3 4096 Bool.true 488102 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz288 Bool.false 503199627 3276800 6361 8699400 20127985 131072 3 4096 (@Enclosure.Real.IsNear.mulLit_ff qz11 qz289 95415 1000 0 1 421904 262144 1 130491 503199627 3276800 6361 8699400 qz273 qz562 rfl) rfl) (Enclosure.sfrac_false_div 20127985 131072) (BSN.cos_reduce1 qz826 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 22612484935468135219200) qz559) 226375608064910080 72057594037927936 Bool.false 488102 524288 24 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q1 20127985 131072 226375608064910080 72057594037927936 24 22612484935468135219200 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 488102 524288 22612484935468135219200 18889465931478580854784 1285370952 1073741824 261237 260982 (ep138 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep140 := nat_lit 6103138606161380140988148175489070905014117853146421658555753041605936807936

noncomputable def ep141 := nat_lit 18294513362614221773411927374398204637488188882079888110834561629043552157696

noncomputable def ep142 := BSN.cos_dyadic_bound_f 1285370952 1073741824 3 2 524288 261237 ep140 ep102 ep136 ep141 ep105 ep136 191398 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1285370952) qz269 0 2 ep140 ep102 ep136 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1285370952) qz270 0 2 ep141 ep105 ep136 rfl rfl rfl rfl) rfl rfl

noncomputable def ep143 := @Enclosure.Real.IsNear.sin_image qz288 qz826 Bool.false 20127985 131072 3 4096 Bool.false 191398 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz288 Bool.false 503199627 3276800 6361 8699400 20127985 131072 3 4096 (@Enclosure.Real.IsNear.mulLit_ff qz11 qz289 95415 1000 0 1 421904 262144 1 130491 503199627 3276800 6361 8699400 qz273 qz562 rfl) rfl) (Enclosure.sfrac_false_div 20127985 131072) (BSN.sin_reduce1 qz826 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 22612484935468135219200) qz559) 226375608064910080 72057594037927936 Bool.false 191398 524288 24 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q1 20127985 131072 226375608064910080 72057594037927936 24 22612484935468135219200 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 191398 524288 22612484935468135219200 18889465931478580854784 1285370952 1073741824 261237 260982 (ep142 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz563 := (@Enclosure.Real.IsNear.recentre' qz287 Bool.false 234469 524288 1 524288 234469 524288 1 524288 (ep130 rfl rfl) rfl)

noncomputable def ep144 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz287 (Real.cos qz288)) (@HMul.hMul Real Real Real qz0 qz287 (@Neg.neg Real Real.instNeg (Real.sin qz288))) Bool.true 57222393919 137438953472 5967786518561 17934546477514752 Bool.true 22438448831 137438953472 5948427917729 17934546477514752 (@Enclosure.Real.IsNear.mulLit_ft qz287 (Real.cos qz288) 234469 524288 1 524288 244051 262144 395569 534491136 57222393919 137438953472 5967786518561 17934546477514752 qz563 (@Enclosure.Real.IsNear.recentre' (Real.cos qz288) Bool.true 488102 524288 395569 534491136 244051 262144 395569 534491136 (ep139 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz287 (@Neg.neg Real Real.instNeg (Real.sin qz288)) 234469 524288 1 524288 95699 262144 395569 534491136 22438448831 137438953472 5948427917729 17934546477514752 qz563 (@Enclosure.Real.IsNear.neg (Real.sin qz288) Bool.false 95699 262144 395569 534491136 (@Enclosure.Real.IsNear.recentre' (Real.sin qz288) Bool.false 191398 524288 395569 534491136 95699 262144 395569 534491136 (ep143 rfl rfl) rfl)) rfl)

noncomputable def ep145 := @ep76 57222393919 137438953472 5967786518561 17934546477514752 Bool.true 22438448831 137438953472 5948427917729 17934546477514752 Bool.false 4700466747680233619456 34200396823 274877906944 59561887385617 35869092955029504 Bool.false 12037793408287982485504 87586474607 274877906944 59436712327975 35869092955029504 (ep77 (BSN.head_sum_c_succ qz14 4 5 rfl rfl) (ep128 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep129 ep144) rfl rfl

noncomputable abbrev qz827 := (@Nat.cast Real Real.instNatCast 6)

noncomputable abbrev qz290 := (@Inv.inv Real Real.instInv (Real.sqrt qz827))

noncomputable abbrev qz291 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 6 1)))

noncomputable def ep146 := @Enclosure.Complex.IsNear.of_eq qz819 (Complex.mk (@HMul.hMul Real Real Real qz0 qz290 (Real.cos qz291)) (@HMul.hMul Real Real Real qz0 qz290 (@Neg.neg Real Real.instNeg (Real.sin qz291)))) Bool.false 28432298643 274877906944 10854785394247 35869092955029504 Bool.true 27139075005 68719476736 2725908446665 8967273238757376 (BSN.cpow_neg_s_mk qz11 95415 1000 6 (@Eq.refl Real qz11) rfl)

noncomputable abbrev qz828 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6) qz268)

noncomputable def ep147 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz827) 1284239 524288 1 524288 107019 107020 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz827) (Real.sqrt qz828) Bool.false 1284239 524288 1 524288 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz828) Bool.false 1284239 524288 1 524288 1284239 524288 1 524288 (BSN.sqrt_enclosure 6 1 642119 642120 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep148 := BSN.log_dyadic_bound 2 10 4 3 105000000 262144 130491 1434560 960 106290 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 2) (BSN.artanhQ 10) 0 3 1434560 105000000 960 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz292 := (Real.log (Enclosure.sfrac Bool.false 6 1))

noncomputable def ep149 := @Enclosure.Real.IsNear.mulLit_ff qz11 qz292 95415 1000 0 1 4034681531866359 2251799813685248 500000000130491 65245500000000000000 76993827672605728797 450359962737049600 3180500000830053251 4349700000000000000000 qz273 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 500000000130491 65245500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz828) Bool.false 16922680887833197019136 9444732965739290427392 1000000000260982 130491000000000000000 4034681531866359 2251799813685248 500000000130491 65245500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 106290 262144 24973259072661432 36028797018963968 130491 1000000000000000 rfl rfl rfl rfl (ep148 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep150 := nat_lit 8881834017769696943425834478379068290296169719945948867069881953276500443136

noncomputable def ep151 := nat_lit 15763217475471950530519782397704582895027268150511204556617829981324640256

noncomputable def ep152 := nat_lit 26613975618358146929216463870341795705098454623536824192096410199866852048896

noncomputable def ep153 := BSN.cos_dyadic_bound_f 1411580364 1073741824 3 2 524288 261237 ep150 ep102 ep151 ep152 ep105 ep151 132837 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1411580364) qz269 0 2 ep150 ep102 ep151 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1411580364) qz270 0 2 ep152 ep105 ep151 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz829 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 22408153) qz285)

noncomputable def ep154 := @Enclosure.Real.IsNear.cos_image qz291 qz829 Bool.false 22408153 131072 3 4096 Bool.false 132837 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz291 Bool.false 76993827672605728797 450359962737049600 3180500000830053251 4349700000000000000000 22408153 131072 3 4096 (ep149 rfl) rfl) (Enclosure.sfrac_false_div 22408153 131072) (BSN.cos_reduce0 qz829 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 24832784396893433102336) qz559) 226375608064910080 72057594037927936 Bool.false 132837 524288 27 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q0 22408153 131072 226375608064910080 72057594037927936 27 24832784396893433102336 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 132837 524288 24832784396893433102336 18889465931478580854784 1411580364 1073741824 261237 260982 (ep153 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep155 := nat_lit 15974690658005076937742086235164159256217083681382298997080493251912641085440

noncomputable def ep156 := nat_lit 41812954133148246917037003349166990632071841683757574470690577268372867710976

noncomputable def ep157 := BSN.sin_dyadic_bound_f 1411580364 1073741824 3 2 524288 261237 ep155 ep109 ep151 ep156 ep111 ep151 507180 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1411580364) qz275 0 2 ep155 ep109 ep151 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1411580364) qz276 0 2 ep156 ep111 ep151 rfl rfl rfl rfl) rfl rfl

noncomputable def ep158 := @Enclosure.Real.IsNear.sin_image qz291 qz829 Bool.false 22408153 131072 3 4096 Bool.false 507180 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz291 Bool.false 76993827672605728797 450359962737049600 3180500000830053251 4349700000000000000000 22408153 131072 3 4096 (ep149 rfl) rfl) (Enclosure.sfrac_false_div 22408153 131072) (BSN.sin_reduce0 qz829 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 24832784396893433102336) qz559) 226375608064910080 72057594037927936 Bool.false 507180 524288 27 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q0 22408153 131072 226375608064910080 72057594037927936 27 24832784396893433102336 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 507180 524288 24832784396893433102336 18889465931478580854784 1411580364 1073741824 261237 260982 (ep157 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz564 := (@Enclosure.Real.IsNear.recentre' qz290 Bool.false 214039 524288 1 524288 214039 524288 1 524288 (ep147 rfl rfl) rfl)

noncomputable def ep159 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz290 (Real.cos qz291)) (@HMul.hMul Real Real Real qz0 qz290 (@Neg.neg Real Real.instNeg (Real.sin qz291))) Bool.false 28432298643 274877906944 10854785394247 35869092955029504 Bool.true 27139075005 68719476736 2725908446665 8967273238757376 (@Enclosure.Real.IsNear.mulLit_ff qz290 (Real.cos qz291) 214039 524288 1 524288 132837 524288 395569 534491136 28432298643 274877906944 10854785394247 35869092955029504 qz564 (@Enclosure.Real.IsNear.recentre' (Real.cos qz291) Bool.false 132837 524288 395569 534491136 132837 524288 395569 534491136 (ep154 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz290 (@Neg.neg Real Real.instNeg (Real.sin qz291)) 214039 524288 1 524288 126795 131072 395569 534491136 27139075005 68719476736 2725908446665 8967273238757376 qz564 (@Enclosure.Real.IsNear.neg (Real.sin qz291) Bool.false 126795 131072 395569 534491136 (@Enclosure.Real.IsNear.recentre' (Real.sin qz291) Bool.false 507180 524288 395569 534491136 126795 131072 395569 534491136 (ep158 rfl rfl) rfl)) rfl)

noncomputable def ep160 := @ep74 28432298643 274877906944 10854785394247 35869092955029504 Bool.true 27139075005 68719476736 2725908446665 8967273238757376 Bool.false 17216344235955038715904 31316347733 137438953472 8802084097483 4483636619378688 Bool.true 1441035429626635091968 20969825413 274877906944 70340346114635 35869092955029504 (ep75 (BSN.head_sum_c_succ qz14 5 6 rfl rfl) (ep145 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep146 ep159) rfl rfl

noncomputable abbrev qz830 := (@Nat.cast Real Real.instNatCast 7)

noncomputable abbrev qz293 := (@Inv.inv Real Real.instInv (Real.sqrt qz830))

noncomputable abbrev qz294 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 7 1)))

noncomputable def ep161 := @Enclosure.Complex.IsNear.of_eq qz818 (Complex.mk (@HMul.hMul Real Real Real qz0 qz293 (Real.cos qz294)) (@HMul.hMul Real Real Real qz0 qz293 (@Neg.neg Real Real.instNeg (Real.sin qz294)))) Bool.true 98791587531 274877906944 10124517730639 35869092955029504 Bool.false 16079936635 137438953472 5040320261681 17934546477514752 (BSN.cpow_neg_s_mk qz11 95415 1000 7 (@Eq.refl Real qz11) rfl)

noncomputable abbrev qz831 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 7) qz268)

noncomputable def ep162 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz830) 1387135 524288 1 524288 99081 99082 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz830) (Real.sqrt qz831) Bool.false 1387135 524288 1 524288 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz831) Bool.false 1387135 524288 1 524288 1387135 524288 1 524288 (BSN.sqrt_enclosure 7 1 693567 693568 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep163 := BSN.log_dyadic_bound 3 11 5 4 202569142545 262144 130491 5259111624 688905 146699 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 3) (BSN.artanhQ 11) 0 4 5259111624 202569142545 688905 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz295 := (Real.log (Enclosure.sfrac Bool.false 7 1))

noncomputable def ep164 := @Enclosure.Real.IsNear.mulLit_ff qz11 qz295 95415 1000 0 1 4381792198794487 2251799813685248 500000000130491 65245500000000000000 83617740529595195421 450359962737049600 3180500000830053251 4349700000000000000000 qz273 (BSN.isNear_log_sfrac 7 1 4381792198794487 2251799813685248 500000000130491 65245500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz831) Bool.false 18378568546572512002048 9444732965739290427392 1000000000260982 130491000000000000000 4381792198794487 2251799813685248 500000000130491 65245500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 146699 262144 24973259072661432 36028797018963968 130491 1000000000000000 rfl rfl rfl rfl (ep163 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep165 := nat_lit 13039522349213437370664654910387216

noncomputable def ep166 := BSN.cos_dyadic_bound_f 337921186 1073741824 2 1 524288 261237 ep165 ep88 ep165 ep165 ep89 ep165 498537 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 337921186) qz269 0 1 ep165 ep88 ep165 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 337921186) qz270 0 1 ep165 ep89 ep165 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz832 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 97343861) qz280)

noncomputable def ep167 := @Enclosure.Real.IsNear.cos_image qz294 qz832 Bool.false 97343861 524288 385 524288 Bool.true 498537 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz294 Bool.false 83617740529595195421 450359962737049600 3180500000830053251 4349700000000000000000 97343861 524288 385 524288 (ep164 rfl) rfl) (Enclosure.sfrac_false_div 97343861 524288) (BSN.cos_reduce2 qz832 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 23779089510973489283072) qz282) 226375608064910080 72057594037927936 Bool.false 498537 524288 29 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q2 97343861 524288 226375608064910080 72057594037927936 29 23779089510973489283072 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 498537 524288 23779089510973489283072 75557863725914323419136 337921186 1073741824 261237 260982 (ep166 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep168 := BSN.sin_dyadic_bound_f 337921186 1073741824 2 1 524288 261237 ep165 ep92 ep165 ep165 ep93 ep165 162290 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 337921186) qz275 0 1 ep165 ep92 ep165 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 337921186) qz276 0 1 ep165 ep93 ep165 rfl rfl rfl rfl) rfl rfl

noncomputable def ep169 := @Enclosure.Real.IsNear.sin_image qz294 qz832 Bool.false 97343861 524288 385 524288 Bool.true 162290 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz294 Bool.false 83617740529595195421 450359962737049600 3180500000830053251 4349700000000000000000 97343861 524288 385 524288 (ep164 rfl) rfl) (Enclosure.sfrac_false_div 97343861 524288) (BSN.sin_reduce2 qz832 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 23779089510973489283072) qz282) 226375608064910080 72057594037927936 Bool.false 162290 524288 29 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q2 97343861 524288 226375608064910080 72057594037927936 29 23779089510973489283072 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 162290 524288 23779089510973489283072 75557863725914323419136 337921186 1073741824 261237 260982 (ep168 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz565 := (@Enclosure.Real.IsNear.recentre' qz293 Bool.false 198163 524288 1 524288 198163 524288 1 524288 (ep162 rfl rfl) rfl)

noncomputable def ep170 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz293 (Real.cos qz294)) (@HMul.hMul Real Real Real qz0 qz293 (@Neg.neg Real Real.instNeg (Real.sin qz294))) Bool.true 98791587531 274877906944 10124517730639 35869092955029504 Bool.false 16079936635 137438953472 5040320261681 17934546477514752 (@Enclosure.Real.IsNear.mulLit_ft qz293 (Real.cos qz294) 198163 524288 1 524288 498537 524288 50763323 68414865408 98791587531 274877906944 10124517730639 35869092955029504 qz565 (@Enclosure.Real.IsNear.recentre' (Real.cos qz294) Bool.true 498537 524288 50763323 68414865408 498537 524288 50763323 68414865408 (ep167 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz293 (@Neg.neg Real Real.instNeg (Real.sin qz294)) 198163 524288 1 524288 81145 262144 50763323 68414865408 16079936635 137438953472 5040320261681 17934546477514752 qz565 (@Enclosure.Real.IsNear.neg (Real.sin qz294) Bool.true 81145 262144 50763323 68414865408 (@Enclosure.Real.IsNear.recentre' (Real.sin qz294) Bool.true 162290 524288 50763323 68414865408 81145 262144 50763323 68414865408 (ep169 rfl rfl) rfl)) rfl)

noncomputable def ep171 := @ep72 98791587531 274877906944 10124517730639 35869092955029504 Bool.false 16079936635 137438953472 5040320261681 17934546477514752 Bool.true 4969640284120604999680 36158892065 274877906944 26847063503501 11956364318343168 Bool.false 1537948466767676309504 11190047857 274877906944 26806995545999 11956364318343168 (ep73 (BSN.head_sum_c_succ qz14 6 7 rfl rfl) (ep160 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep161 ep170) rfl rfl

noncomputable abbrev qz833 := (@Nat.cast Real Real.instNatCast 8)

noncomputable abbrev qz296 := (@Inv.inv Real Real.instInv (Real.sqrt qz833))

noncomputable abbrev qz297 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 8 1)))

noncomputable def ep172 := @Enclosure.Complex.IsNear.of_eq qz817 (Complex.mk (@HMul.hMul Real Real Real qz0 qz296 (Real.cos qz297)) (@HMul.hMul Real Real Real qz0 qz296 (@Neg.neg Real Real.instNeg (Real.sin qz297)))) Bool.true 21441865025 68719476736 262385623793 996363693195264 Bool.false 45700691561 274877906944 1046408492825 3985454772781056 (BSN.cpow_neg_s_mk qz11 95415 1000 8 (@Eq.refl Real qz11) rfl)

noncomputable abbrev qz834 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8) qz268)

noncomputable def ep173 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz833) 1482911 524288 1 524288 92681 92682 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz833) (Real.sqrt qz834) Bool.false 1482911 524288 1 524288 (BSN.sqrt_natCast_div_one 8) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz834) Bool.false 1482911 524288 1 524288 1482911 524288 1 524288 (BSN.sqrt_enclosure 8 1 741455 741456 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep174 := BSN.log_dyadic_bound 0 16 1 0 1 262144 130491 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz298 := (Real.log (Enclosure.sfrac Bool.false 8 1))

noncomputable def ep175 := @Enclosure.Real.IsNear.mulLit_ff qz11 qz298 95415 1000 0 1 9364972152248037 4503599627370496 1000000000391473 130491000000000000000 178711763581349290071 900719925474099200 6361000002490159753 8699400000000000000000 qz273 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 1000000000391473 130491000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz834) Bool.false 19639770079031275290624 9444732965739290427392 1000000000391473 130491000000000000000 9364972152248037 4503599627370496 1000000000391473 130491000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 262144 24973259072661432 36028797018963968 130491 1000000000000000 rfl rfl rfl rfl (ep174 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep176 := nat_lit 76362992373586844046052601270246881

noncomputable def ep177 := BSN.cos_dyadic_bound_f 525679129 1073741824 2 1 524288 261237 ep176 ep88 ep176 ep176 ep89 ep176 462700 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 525679129) qz269 0 1 ep176 ep88 ep176 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 525679129) qz270 0 1 ep176 ep89 ep176 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz835 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 104023937) qz280)

noncomputable def ep178 := @Enclosure.Real.IsNear.cos_image qz297 qz835 Bool.false 104023937 524288 3 4096 Bool.true 462700 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz297 Bool.false 178711763581349290071 900719925474099200 6361000002490159753 8699400000000000000000 104023937 524288 3 4096 (ep175 rfl) rfl) (Enclosure.sfrac_false_div 104023937 524288) (BSN.cos_reduce2 qz835 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 36991380202899871105024) qz282) 226375608064910080 72057594037927936 Bool.false 462700 524288 31 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q2 104023937 524288 226375608064910080 72057594037927936 31 36991380202899871105024 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 462700 524288 36991380202899871105024 75557863725914323419136 525679129 1073741824 261237 260982 (ep177 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep179 := BSN.sin_dyadic_bound_f 525679129 1073741824 2 1 524288 261237 ep176 ep92 ep176 ep176 ep93 ep176 246547 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 525679129) qz275 0 1 ep176 ep92 ep176 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 525679129) qz276 0 1 ep176 ep93 ep176 rfl rfl rfl rfl) rfl rfl

noncomputable def ep180 := @Enclosure.Real.IsNear.sin_image qz297 qz835 Bool.false 104023937 524288 3 4096 Bool.true 246547 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz297 Bool.false 178711763581349290071 900719925474099200 6361000002490159753 8699400000000000000000 104023937 524288 3 4096 (ep175 rfl) rfl) (Enclosure.sfrac_false_div 104023937 524288) (BSN.sin_reduce2 qz835 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 36991380202899871105024) qz282) 226375608064910080 72057594037927936 Bool.false 246547 524288 31 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q2 104023937 524288 226375608064910080 72057594037927936 31 36991380202899871105024 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 246547 524288 36991380202899871105024 75557863725914323419136 525679129 1073741824 261237 260982 (ep179 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz566 := (@Enclosure.Real.IsNear.recentre' qz296 Bool.false 185363 524288 1 524288 185363 524288 1 524288 (ep173 rfl rfl) rfl)

noncomputable def ep181 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz296 (Real.cos qz297)) (@HMul.hMul Real Real Real qz0 qz296 (@Neg.neg Real Real.instNeg (Real.sin qz297))) Bool.true 21441865025 68719476736 262385623793 996363693195264 Bool.false 45700691561 274877906944 1046408492825 3985454772781056 (@Enclosure.Real.IsNear.mulLit_ft qz296 (Real.cos qz297) 185363 524288 1 524288 115675 131072 395569 534491136 21441865025 68719476736 262385623793 996363693195264 qz566 (@Enclosure.Real.IsNear.recentre' (Real.cos qz297) Bool.true 462700 524288 395569 534491136 115675 131072 395569 534491136 (ep178 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz296 (@Neg.neg Real Real.instNeg (Real.sin qz297)) 185363 524288 1 524288 246547 524288 395569 534491136 45700691561 274877906944 1046408492825 3985454772781056 qz566 (@Enclosure.Real.IsNear.neg (Real.sin qz297) Bool.true 246547 524288 395569 534491136 (@Enclosure.Real.IsNear.recentre' (Real.sin qz297) Bool.true 246547 524288 395569 534491136 246547 524288 395569 534491136 (ep180 rfl rfl) rfl)) rfl)

noncomputable def ep182 := @ep70 21441865025 68719476736 262385623793 996363693195264 Bool.false 45700691561 274877906944 1046408492825 3985454772781056 Bool.true 8378715121108060733440 121926352165 274877906944 29995690989017 11956364318343168 Bool.false 15638007375716356718592 28445369709 137438953472 14973110512237 5978182159171584 (ep71 (BSN.head_sum_c_succ qz14 7 8 rfl rfl) (ep171 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep172 ep181) rfl rfl

theorem EMRow28.d7 : Enclosure.Complex.IsNear (BSN.headSumC qz14 9) Bool.true 121926352165 274877906944 29995690989017 11956364318343168 Bool.false 28445369709 137438953472 14973110512237 5978182159171584 := ep69 (BSN.head_sum_c_succ qz14 8 9 rfl rfl) (ep182 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz836 := (@HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast 16) qz17)

noncomputable def ep183 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 17) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz14 16) qz836) Bool.false 8303683425 34359738368 25215172822777 5978182159171584 Bool.true 7356088589 34359738368 1573400418433 373636384948224

noncomputable def ep184 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz14 16) qz836 Bool.false 1479865023 34359738368 72300070700611 17934546477514752 Bool.true 8554836523 137438953472 72184169638339 17934546477514752 Bool.false

noncomputable abbrev qz837 := (@HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast 15) qz17)

noncomputable def ep185 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 16) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz14 15) qz837) Bool.false 1479865023 34359738368 72300070700611 17934546477514752 Bool.true 8554836523 137438953472 72184169638339 17934546477514752

noncomputable def ep186 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz14 15) qz837 Bool.true 9683515241 68719476736 68839729484179 17934546477514752 Bool.false 16342868539 137438953472 68724203192059 17934546477514752 Bool.false

noncomputable abbrev qz838 := (@HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast 14) qz17)

noncomputable def ep187 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 15) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz14 14) qz838) Bool.true 9683515241 68719476736 68839729484179 17934546477514752 Bool.false 16342868539 137438953472 68724203192059 17934546477514752

noncomputable def ep188 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz14 14) qz838 Bool.true 51983416015 137438953472 5438497321657 1494545539792896 Bool.false 66473253929 274877906944 43440722424431 11956364318343168 Bool.false

noncomputable abbrev qz839 := (@HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast 13) qz17)

noncomputable def ep189 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 14) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz14 13) qz839) Bool.true 51983416015 137438953472 5438497321657 1494545539792896 Bool.false 66473253929 274877906944 43440722424431 11956364318343168

noncomputable def ep190 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz14 13) qz839 Bool.true 176571562207 274877906944 123096159283247 35869092955029504 Bool.false 21610653987 137438953472 61469339871577 17934546477514752 Bool.false

noncomputable abbrev qz840 := (@HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast 12) qz17)

noncomputable def ep191 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 13) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz14 12) qz840) Bool.true 176571562207 274877906944 123096159283247 35869092955029504 Bool.false 21610653987 137438953472 61469339871577 17934546477514752

noncomputable def ep192 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz14 12) qz840 Bool.true 42301313757 68719476736 57713264516293 17934546477514752 Bool.true 35786351053 274877906944 115207281316661 35869092955029504 Bool.true

noncomputable abbrev qz841 := (@HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast 11) qz17)

noncomputable def ep193 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 12) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz14 11) qz841) Bool.true 42301313757 68719476736 57713264516293 17934546477514752 Bool.true 35786351053 274877906944 115207281316661 35869092955029504

noncomputable def ep194 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz14 11) qz841 Bool.true 24544299687 68719476736 17890538452771 5978182159171584 Bool.false 6920903903 274877906944 35715787082099 11956364318343168 Bool.true

noncomputable abbrev qz842 := (@HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast 10) qz17)

noncomputable def ep195 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 11) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz14 10) qz842) Bool.true 24544299687 68719476736 17890538452771 5978182159171584 Bool.false 6920903903 274877906944 35715787082099 11956364318343168

noncomputable def ep196 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz14 10) qz842 Bool.true 45795239607 68719476736 49440803222345 17934546477514752 Bool.true 11250228097 274877906944 98738338418425 35869092955029504 Bool.false

noncomputable abbrev qz843 := (@HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast 9) qz17)

noncomputable def ep197 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 10) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz14 9) qz843) Bool.true 45795239607 68719476736 49440803222345 17934546477514752 Bool.true 11250228097 274877906944 98738338418425 35869092955029504

noncomputable def ep198 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz14 9) qz843 Bool.true 121926352165 274877906944 29995690989017 11956364318343168 Bool.false 28445369709 137438953472 14973110512237 5978182159171584 Bool.true

noncomputable abbrev qz844 := (@Nat.cast Real Real.instNatCast 9)

noncomputable abbrev qz299 := (@Inv.inv Real Real.instInv (Real.sqrt qz844))

noncomputable abbrev qz300 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 9 1)))

noncomputable def ep199 := @Enclosure.Complex.IsNear.of_eq qz843 (Complex.mk (@HMul.hMul Real Real Real qz0 qz299 (Real.cos qz300)) (@HMul.hMul Real Real Real qz0 qz299 (@Neg.neg Real Real.instNeg (Real.sin qz300)))) Bool.true 61254606263 274877906944 8894533477639 35869092955029504 Bool.true 68140967515 274877906944 8899675345003 35869092955029504 (BSN.cpow_neg_s_mk qz11 95415 1000 9 (@Eq.refl Real qz11) rfl)

noncomputable abbrev qz845 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9) qz268)

noncomputable def ep200 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz844) 1572865 524288 1 524288 87381 87382 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz844) (Real.sqrt qz845) Bool.false 1572865 524288 1 524288 (BSN.sqrt_natCast_div_one 9) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz845) Bool.false 1572865 524288 1 524288 1572865 524288 1 524288 (BSN.sqrt_enclosure 9 1 786432 786433 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep201 := BSN.log_dyadic_bound 1 17 2 1 867 262144 130491 1 1 30876 18 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1) (BSN.artanhQ 17) 0 1 1 867 1 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz301 := (Real.log (Enclosure.sfrac Bool.false 9 1))

noncomputable def ep202 := @Enclosure.Real.IsNear.mulLit_ff qz11 qz301 95415 1000 0 1 9895417793173221 4503599627370496 1000000000391473 130491000000000000000 188834257747124576343 900719925474099200 6361000002490159753 8699400000000000000000 qz273 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 1000000000391473 130491000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz845) Bool.false 20752195215788806766592 9444732965739290427392 1000000000391473 130491000000000000000 9895417793173221 4503599627370496 1000000000391473 130491000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 30876 262144 24973259072661432 36028797018963968 130491 1000000000000000 rfl rfl rfl rfl (ep201 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep203 := nat_lit 382107858362926091327419670046243856

noncomputable def ep204 := BSN.sin_dyadic_bound_f 786224354 1073741824 2 1 524288 261237 ep203 ep92 ep203 ep203 ep93 ep203 350501 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 786224354) qz275 0 1 ep203 ep92 ep203 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 786224354) qz276 0 1 ep203 ep93 ep203 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz846 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 27479001) qz285)

noncomputable def ep205 := @Enclosure.Real.IsNear.cos_image qz300 qz846 Bool.false 27479001 131072 3 4096 Bool.true 350501 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz300 Bool.false 188834257747124576343 900719925474099200 6361000002490159753 8699400000000000000000 27479001 131072 3 4096 (ep202 rfl) rfl) (Enclosure.sfrac_false_div 27479001 131072) (BSN.cos_reduce1 qz846 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13831405113873679777792) qz559) 226375608064910080 72057594037927936 Bool.false 350501 524288 33 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q1 27479001 131072 226375608064910080 72057594037927936 33 13831405113873679777792 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 350501 524288 13831405113873679777792 18889465931478580854784 786224354 1073741824 261237 260982 (ep204 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep206 := nat_lit 853432223827726208536641795593432571289295825681833997168908023795131842816

noncomputable def ep207 := nat_lit 146006415422701986870580761343072564563630680114884988144233534217748736

noncomputable def ep208 := nat_lit 2560004658652333221636184225257611568738760215685272221530435604316960030976

noncomputable def ep209 := BSN.cos_dyadic_bound_f 786224354 1073741824 3 2 524288 261237 ep206 ep102 ep207 ep208 ep105 ep207 389905 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 786224354) qz269 0 2 ep206 ep102 ep207 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 786224354) qz270 0 2 ep208 ep105 ep207 rfl rfl rfl rfl) rfl rfl

noncomputable def ep210 := @Enclosure.Real.IsNear.sin_image qz300 qz846 Bool.false 27479001 131072 3 4096 Bool.false 389905 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz300 Bool.false 188834257747124576343 900719925474099200 6361000002490159753 8699400000000000000000 27479001 131072 3 4096 (ep202 rfl) rfl) (Enclosure.sfrac_false_div 27479001 131072) (BSN.sin_reduce1 qz846 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13831405113873679777792) qz559) 226375608064910080 72057594037927936 Bool.false 389905 524288 33 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q1 27479001 131072 226375608064910080 72057594037927936 33 13831405113873679777792 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 389905 524288 13831405113873679777792 18889465931478580854784 786224354 1073741824 261237 260982 (ep209 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz567 := (@Enclosure.Real.IsNear.recentre' qz299 Bool.false 174763 524288 1 524288 174763 524288 1 524288 (ep200 rfl rfl) rfl)

noncomputable def ep211 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz299 (Real.cos qz300)) (@HMul.hMul Real Real Real qz0 qz299 (@Neg.neg Real Real.instNeg (Real.sin qz300))) Bool.true 61254606263 274877906944 8894533477639 35869092955029504 Bool.true 68140967515 274877906944 8899675345003 35869092955029504 (@Enclosure.Real.IsNear.mulLit_ft qz299 (Real.cos qz300) 174763 524288 1 524288 350501 524288 395569 534491136 61254606263 274877906944 8894533477639 35869092955029504 qz567 (@Enclosure.Real.IsNear.recentre' (Real.cos qz300) Bool.true 350501 524288 395569 534491136 350501 524288 395569 534491136 (ep205 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz299 (@Neg.neg Real Real.instNeg (Real.sin qz300)) 174763 524288 1 524288 389905 524288 395569 534491136 68140967515 274877906944 8899675345003 35869092955029504 qz567 (@Enclosure.Real.IsNear.neg (Real.sin qz300) Bool.false 389905 524288 395569 534491136 (@Enclosure.Real.IsNear.recentre' (Real.sin qz300) Bool.false 389905 524288 395569 534491136 389905 524288 395569 534491136 (ep210 rfl rfl) rfl)) rfl)

noncomputable def ep212 := @ep198 61254606263 274877906944 8894533477639 35869092955029504 Bool.true 68140967515 274877906944 8899675345003 35869092955029504 Bool.true 50352398444684516524032 45795239607 68719476736 49440803222345 17934546477514752 Bool.true 1546219575972970102784 11250228097 274877906944 98738338418425 35869092955029504 EMRow28.d7 (ep199 ep211) rfl rfl

noncomputable abbrev qz847 := (@Nat.cast Real Real.instNatCast 10)

noncomputable abbrev qz302 := (@Inv.inv Real Real.instInv (Real.sqrt qz847))

noncomputable abbrev qz303 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 10 1)))

noncomputable def ep213 := @Enclosure.Complex.IsNear.of_eq qz842 (Complex.mk (@HMul.hMul Real Real Real qz0 qz302 (Real.cos qz303)) (@HMul.hMul Real Real Real qz0 qz302 (@Neg.neg Real Real.instNeg (Real.sin qz303)))) Bool.false 1328183745 4294967296 132212879249 560454577422336 Bool.false 567847875 8589934592 262781963371 1120909154844672 (BSN.cpow_neg_s_mk qz11 95415 1000 10 (@Eq.refl Real qz11) rfl)

noncomputable abbrev qz848 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 10) qz268)

noncomputable def ep214 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz847) 1657945 524288 1 524288 82897 82898 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz847) (Real.sqrt qz848) Bool.false 1657945 524288 1 524288 (BSN.sqrt_natCast_div_one 10) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz848) Bool.false 1657945 524288 1 524288 1657945 524288 1 524288 (BSN.sqrt_enclosure 10 1 828972 828973 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep215 := BSN.log_dyadic_bound 2 18 3 2 1574640 262144 130491 6528 48 58495 20 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 2) (BSN.artanhQ 18) 0 2 6528 1574640 48 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz304 := (Real.log (Enclosure.sfrac Bool.false 10 1))

noncomputable def ep216 := @Enclosure.Real.IsNear.mulLit_ff qz11 qz304 95415 1000 0 1 10369908600166117 4503599627370496 1000000000391473 130491000000000000000 197888965816970010711 900719925474099200 6361000002490159753 8699400000000000000000 qz273 (BSN.isNear_log_sfrac 10 1 10369908600166117 4503599627370496 1000000000391473 130491000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz848) Bool.false 21747274560655572598784 9444732965739290427392 1000000000391473 130491000000000000000 10369908600166117 4503599627370496 1000000000391473 130491000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 58495 262144 24973259072661432 36028797018963968 130491 1000000000000000 rfl rfl rfl rfl (ep215 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep217 := nat_lit 18309584202557646481123073900395872068495571949431159359030660295547608198625

noncomputable def ep218 := nat_lit 20701975651848294103597545231528765430852829473678201398017818482132741601

noncomputable def ep219 := nat_lit 47920155427071795926773654665900046940124164810314700280912081448891711319521

noncomputable def ep220 := BSN.sin_dyadic_bound_f 1460499707 1073741824 3 2 524288 261237 ep217 ep109 ep218 ep219 ep111 ep218 512704 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1460499707) qz275 0 2 ep217 ep109 ep218 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1460499707) qz276 0 2 ep219 ep111 ep218 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz849 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 57593269) qz271)

noncomputable def ep221 := @Enclosure.Real.IsNear.cos_image qz303 qz849 Bool.false 57593269 262144 3 4096 Bool.false 512704 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz303 Bool.false 197888965816970010711 900719925474099200 6361000002490159753 8699400000000000000000 57593269 262144 3 4096 (ep216 rfl) rfl) (Enclosure.sfrac_false_div 57593269 262144) (BSN.cos_reduce3 qz849 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 51386765159437107724288) qz274) 226375608064910080 72057594037927936 Bool.false 512704 524288 34 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q3 57593269 262144 226375608064910080 72057594037927936 34 51386765159437107724288 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 512704 524288 51386765159437107724288 37778931862957161709568 1460499707 1073741824 261237 260982 (ep220 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep222 := nat_lit 10181192101710625064669973298100608378244585673894501066749485861296285773281

noncomputable def ep223 := nat_lit 30502172353828178605802724803838767603872051362736146797452421946924591836641

noncomputable def ep224 := BSN.cos_dyadic_bound_f 1460499707 1073741824 3 2 524288 261237 ep222 ep102 ep218 ep223 ep105 ep218 109600 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1460499707) qz269 0 2 ep222 ep102 ep218 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1460499707) qz270 0 2 ep223 ep105 ep218 rfl rfl rfl rfl) rfl rfl

noncomputable def ep225 := @Enclosure.Real.IsNear.sin_image qz303 qz849 Bool.false 57593269 262144 3 4096 Bool.true 109600 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz303 Bool.false 197888965816970010711 900719925474099200 6361000002490159753 8699400000000000000000 57593269 262144 3 4096 (ep216 rfl) rfl) (Enclosure.sfrac_false_div 57593269 262144) (BSN.sin_reduce3 qz849 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 51386765159437107724288) qz274) 226375608064910080 72057594037927936 Bool.false 109600 524288 34 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q3 57593269 262144 226375608064910080 72057594037927936 34 51386765159437107724288 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 109600 524288 51386765159437107724288 37778931862957161709568 1460499707 1073741824 261237 260982 (ep224 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz568 := (@Enclosure.Real.IsNear.recentre' qz302 Bool.false 165795 524288 1 524288 165795 524288 1 524288 (ep214 rfl rfl) rfl)

noncomputable def ep226 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz302 (Real.cos qz303)) (@HMul.hMul Real Real Real qz0 qz302 (@Neg.neg Real Real.instNeg (Real.sin qz303))) Bool.false 1328183745 4294967296 132212879249 560454577422336 Bool.false 567847875 8589934592 262781963371 1120909154844672 (@Enclosure.Real.IsNear.mulLit_ff qz302 (Real.cos qz303) 165795 524288 1 524288 8011 8192 395569 534491136 1328183745 4294967296 132212879249 560454577422336 qz568 (@Enclosure.Real.IsNear.recentre' (Real.cos qz303) Bool.false 512704 524288 395569 534491136 8011 8192 395569 534491136 (ep221 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz302 (@Neg.neg Real Real.instNeg (Real.sin qz303)) 165795 524288 1 524288 3425 16384 395569 534491136 567847875 8589934592 262781963371 1120909154844672 qz568 (@Enclosure.Real.IsNear.neg (Real.sin qz303) Bool.true 3425 16384 395569 534491136 (@Enclosure.Real.IsNear.recentre' (Real.sin qz303) Bool.true 109600 524288 395569 534491136 3425 16384 395569 534491136 (ep225 rfl rfl) rfl)) rfl)

noncomputable def ep227 := @ep196 1328183745 4294967296 132212879249 560454577422336 Bool.false 567847875 8589934592 262781963371 1120909154844672 Bool.true 105416964458888036352 24544299687 68719476736 17890538452771 5978182159171584 Bool.false 59450111844287512576 6920903903 274877906944 35715787082099 11956364318343168 (ep197 (BSN.head_sum_c_succ qz14 9 10 rfl rfl) (ep212 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep213 ep226) rfl rfl

noncomputable abbrev qz850 := (@Nat.cast Real Real.instNatCast 11)

noncomputable abbrev qz305 := (@Inv.inv Real Real.instInv (Real.sqrt qz850))

noncomputable abbrev qz306 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 11 1)))

noncomputable def ep228 := @Enclosure.Complex.IsNear.of_eq qz841 (Complex.mk (@HMul.hMul Real Real Real qz0 qz305 (Real.cos qz306)) (@HMul.hMul Real Real Real qz0 qz305 (@Neg.neg Real Real.instNeg (Real.sin qz306)))) Bool.true 8878507035 34359738368 1010412289495 4483636619378688 Bool.true 10676813739 68719476736 2014980017591 8967273238757376 (BSN.cpow_neg_s_mk qz11 95415 1000 11 (@Eq.refl Real qz11) rfl)

noncomputable abbrev qz851 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11) qz268)

noncomputable def ep229 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz850) 1738867 524288 1 524288 79039 79040 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz850) (Real.sqrt qz851) Bool.false 1738867 524288 1 524288 (BSN.sqrt_natCast_div_one 11) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz851) Bool.false 1738867 524288 1 524288 1738867 524288 1 524288 (BSN.sqrt_enclosure 11 1 869433 869434 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep230 := BSN.log_dyadic_bound 3 19 4 3 4939817505 262144 130491 41676111 10935 83480 22 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 3) (BSN.artanhQ 19) 0 3 41676111 4939817505 10935 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz307 := (Real.log (Enclosure.sfrac Bool.false 11 1))

noncomputable def ep231 := @Enclosure.Real.IsNear.mulLit_ff qz11 qz307 95415 1000 0 1 10799147631728357 4503599627370496 1000000000391473 130491000000000000000 206080134256272236631 900719925474099200 6361000002490159753 8699400000000000000000 qz273 (BSN.isNear_log_sfrac 11 1 10799147631728357 4503599627370496 1000000000391473 130491000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz851) Bool.false 22647454054174387339264 9444732965739290427392 1000000000391473 130491000000000000000 10799147631728357 4503599627370496 1000000000391473 130491000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 83480 262144 24973259072661432 36028797018963968 130491 1000000000000000 rfl rfl rfl rfl (ep230 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep232 := nat_lit 6002719967583444516449172224647828113475637586924591377061160911399947030625

noncomputable def ep233 := nat_lit 2228492173585913784965769732563148078527878889370618235292966596250390625

noncomputable def ep234 := nat_lit 15717801403961310825524554104034447581261434257076853558017328060129741590625

noncomputable def ep235 := BSN.sin_dyadic_bound_f 1105354005 1073741824 3 2 524288 261237 ep232 ep109 ep233 ep234 ep111 ep233 449320 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1105354005) qz275 0 2 ep232 ep109 ep233 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1105354005) qz276 0 2 ep234 ep111 ep233 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz852 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 119954425) qz280)

noncomputable def ep236 := @Enclosure.Real.IsNear.cos_image qz306 qz852 Bool.false 119954425 524288 385 524288 Bool.true 449320 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz306 Bool.false 206080134256272236631 900719925474099200 6361000002490159753 8699400000000000000000 119954425 524288 385 524288 (ep231 rfl) rfl) (Enclosure.sfrac_false_div 119954425 524288) (BSN.cos_reduce1 qz852 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 77782373241488985292800) qz282) 226375608064910080 72057594037927936 Bool.false 449320 524288 36 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q1 119954425 524288 226375608064910080 72057594037927936 36 77782373241488985292800 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 449320 524288 77782373241488985292800 75557863725914323419136 1105354005 1073741824 261237 260982 (ep235 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep237 := nat_lit 3335834867401285137487302689129932573299144383353382150916330713709415190625

noncomputable def ep238 := nat_lit 10003047617856683584891976527924671423740377392281405216278406207935744790625

noncomputable def ep239 := BSN.cos_dyadic_bound_f 1105354005 1073741824 3 2 524288 261237 ep237 ep102 ep233 ep238 ep105 ep233 270164 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1105354005) qz269 0 2 ep237 ep102 ep233 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1105354005) qz270 0 2 ep238 ep105 ep233 rfl rfl rfl rfl) rfl rfl

noncomputable def ep240 := @Enclosure.Real.IsNear.sin_image qz306 qz852 Bool.false 119954425 524288 385 524288 Bool.false 270164 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz306 Bool.false 206080134256272236631 900719925474099200 6361000002490159753 8699400000000000000000 119954425 524288 385 524288 (ep231 rfl) rfl) (Enclosure.sfrac_false_div 119954425 524288) (BSN.sin_reduce1 qz852 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 77782373241488985292800) qz282) 226375608064910080 72057594037927936 Bool.false 270164 524288 36 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q1 119954425 524288 226375608064910080 72057594037927936 36 77782373241488985292800 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 270164 524288 77782373241488985292800 75557863725914323419136 1105354005 1073741824 261237 260982 (ep239 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz569 := (@Enclosure.Real.IsNear.recentre' qz305 Bool.false 158079 524288 1 524288 158079 524288 1 524288 (ep229 rfl rfl) rfl)

noncomputable def ep241 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz305 (Real.cos qz306)) (@HMul.hMul Real Real Real qz0 qz305 (@Neg.neg Real Real.instNeg (Real.sin qz306))) Bool.true 8878507035 34359738368 1010412289495 4483636619378688 Bool.true 10676813739 68719476736 2014980017591 8967273238757376 (@Enclosure.Real.IsNear.mulLit_ft qz305 (Real.cos qz306) 158079 524288 1 524288 56165 65536 50763323 68414865408 8878507035 34359738368 1010412289495 4483636619378688 qz569 (@Enclosure.Real.IsNear.recentre' (Real.cos qz306) Bool.true 449320 524288 50763323 68414865408 56165 65536 50763323 68414865408 (ep236 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz305 (@Neg.neg Real Real.instNeg (Real.sin qz306)) 158079 524288 1 524288 67541 131072 50763323 68414865408 10676813739 68719476736 2014980017591 8967273238757376 qz569 (@Enclosure.Real.IsNear.neg (Real.sin qz306) Bool.false 67541 131072 50763323 68414865408 (@Enclosure.Real.IsNear.recentre' (Real.sin qz306) Bool.false 270164 524288 50763323 68414865408 67541 131072 50763323 68414865408 (ep240 rfl rfl) rfl)) rfl)

noncomputable def ep242 := @ep194 8878507035 34359738368 1010412289495 4483636619378688 Bool.true 10676813739 68719476736 2014980017591 8967273238757376 Bool.true 1453462073313199128576 42301313757 68719476736 57713264516293 17934546477514752 Bool.true 2459219318652962603008 35786351053 274877906944 115207281316661 35869092955029504 (ep195 (BSN.head_sum_c_succ qz14 10 11 rfl rfl) (ep227 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep228 ep241) rfl rfl

noncomputable abbrev qz853 := (@Nat.cast Real Real.instNatCast 12)

noncomputable abbrev qz308 := (@Inv.inv Real Real.instInv (Real.sqrt qz853))

noncomputable abbrev qz309 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 12 1)))

noncomputable def ep243 := @Enclosure.Complex.IsNear.of_eq qz840 (Complex.mk (@HMul.hMul Real Real Real qz0 qz308 (Real.cos qz309)) (@HMul.hMul Real Real Real qz0 qz308 (@Neg.neg Real Real.instNeg (Real.sin qz309)))) Bool.true 7366307179 274877906944 2556543416887 11956364318343168 Bool.false 79007659027 274877906944 2577132808831 11956364318343168 (BSN.cpow_neg_s_mk qz11 95415 1000 12 (@Eq.refl Real qz11) rfl)

noncomputable abbrev qz854 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 12) qz268)

noncomputable def ep244 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz853) 1816187 524288 1 524288 75674 75675 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz853) (Real.sqrt qz854) Bool.false 1816187 524288 1 524288 (BSN.sqrt_natCast_div_one 12) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz854) Bool.false 1816187 524288 1 524288 1816187 524288 1 524288 (BSN.sqrt_enclosure 12 1 908093 908094 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep245 := BSN.log_dyadic_bound 4 20 4 3 6720000000 262144 130491 91811840 61440 106290 24 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 4) (BSN.artanhQ 20) 0 3 91811840 6720000000 61440 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz310 := (Real.log (Enclosure.sfrac Bool.false 12 1))

noncomputable def ep246 := @Enclosure.Real.IsNear.mulLit_ff qz11 qz310 95415 1000 0 1 11191020447815397 4503599627370496 1000000000391473 130491000000000000000 213558243205661220951 900719925474099200 6361000002490159753 8699400000000000000000 qz273 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 1000000000391473 130491000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz854) Bool.false 23469270914176955449344 9444732965739290427392 1000000000391473 130491000000000000000 11191020447815397 4503599627370496 1000000000391473 130491000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 106290 262144 24973259072661432 36028797018963968 130491 1000000000000000 rfl rfl rfl rfl (ep245 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep247 := nat_lit 14198319204148617991959038398655814208494496228008060530412010221874924486656

noncomputable def ep248 := nat_lit 40197013666566827330495764662340109951999581147123416863192278290426494976

noncomputable def ep249 := nat_lit 42514563585112720321216123666642762405579489521729934757509646109043920470016

noncomputable def ep250 := BSN.cos_dyadic_bound_f 1586807424 1073741824 3 2 524288 261237 ep247 ep102 ep248 ep249 ep105 ep248 48671 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1586807424) qz269 0 2 ep247 ep102 ep248 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1586807424) qz270 0 2 ep249 ep105 ep248 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz855 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 62153629) qz271)

noncomputable def ep251 := @Enclosure.Real.IsNear.cos_image qz309 qz855 Bool.false 62153629 262144 3 4096 Bool.true 48671 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz309 Bool.false 213558243205661220951 900719925474099200 6361000002490159753 8699400000000000000000 62153629 262144 3 4096 (ep246 rfl) rfl) (Enclosure.sfrac_false_div 62153629 262144) (BSN.cos_reduce2 qz855 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 55830822846801524031488) qz274) 226375608064910080 72057594037927936 Bool.false 48671 524288 37 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q2 62153629 262144 226375608064910080 72057594037927936 37 55830822846801524031488 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 48671 524288 55830822846801524031488 37778931862957161709568 1586807424 1073741824 261237 260982 (ep250 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep252 := nat_lit 25524816956534258923661872505850593487328493545496810221251064576742522880000

noncomputable def ep253 := nat_lit 66785630197367665174865053896345860860223769487777255523593334012331631312896

noncomputable def ep254 := BSN.sin_dyadic_bound_f 1586807424 1073741824 3 2 524288 261237 ep252 ep109 ep248 ep253 ep111 ep248 522023 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1586807424) qz275 0 2 ep252 ep109 ep248 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1586807424) qz276 0 2 ep253 ep111 ep248 rfl rfl rfl rfl) rfl rfl

noncomputable def ep255 := @Enclosure.Real.IsNear.sin_image qz309 qz855 Bool.false 62153629 262144 3 4096 Bool.true 522023 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz309 Bool.false 213558243205661220951 900719925474099200 6361000002490159753 8699400000000000000000 62153629 262144 3 4096 (ep246 rfl) rfl) (Enclosure.sfrac_false_div 62153629 262144) (BSN.sin_reduce2 qz855 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 55830822846801524031488) qz274) 226375608064910080 72057594037927936 Bool.false 522023 524288 37 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q2 62153629 262144 226375608064910080 72057594037927936 37 55830822846801524031488 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 522023 524288 55830822846801524031488 37778931862957161709568 1586807424 1073741824 261237 260982 (ep254 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz570 := (@Enclosure.Real.IsNear.recentre' qz308 Bool.false 151349 524288 1 524288 151349 524288 1 524288 (ep244 rfl rfl) rfl)

noncomputable def ep256 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz308 (Real.cos qz309)) (@HMul.hMul Real Real Real qz0 qz308 (@Neg.neg Real Real.instNeg (Real.sin qz309))) Bool.true 7366307179 274877906944 2556543416887 11956364318343168 Bool.false 79007659027 274877906944 2577132808831 11956364318343168 (@Enclosure.Real.IsNear.mulLit_ft qz308 (Real.cos qz309) 151349 524288 1 524288 48671 524288 395569 534491136 7366307179 274877906944 2556543416887 11956364318343168 qz570 (@Enclosure.Real.IsNear.recentre' (Real.cos qz309) Bool.true 48671 524288 395569 534491136 48671 524288 395569 534491136 (ep251 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz308 (@Neg.neg Real Real.instNeg (Real.sin qz309)) 151349 524288 1 524288 522023 524288 395569 534491136 79007659027 274877906944 2577132808831 11956364318343168 qz570 (@Enclosure.Real.IsNear.neg (Real.sin qz309) Bool.true 522023 524288 395569 534491136 (@Enclosure.Real.IsNear.recentre' (Real.sin qz309) Bool.true 522023 524288 395569 534491136 522023 524288 395569 534491136 (ep255 rfl rfl) rfl)) rfl)

noncomputable def ep257 := @ep192 7366307179 274877906944 2556543416887 11956364318343168 Bool.false 79007659027 274877906944 2577132808831 11956364318343168 Bool.true 12133905361323113316352 176571562207 274877906944 123096159283247 35869092955029504 Bool.false 11880582671275137171456 21610653987 137438953472 61469339871577 17934546477514752 (ep193 (BSN.head_sum_c_succ qz14 11 12 rfl rfl) (ep242 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep243 ep256) rfl rfl

noncomputable abbrev qz856 := (@Nat.cast Real Real.instNatCast 13)

noncomputable abbrev qz311 := (@Inv.inv Real Real.instInv (Real.sqrt qz856))

noncomputable abbrev qz312 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 13 1)))

noncomputable def ep258 := @Enclosure.Complex.IsNear.of_eq qz839 (Complex.mk (@HMul.hMul Real Real Real qz0 qz311 (Real.cos qz312)) (@HMul.hMul Real Real Real qz0 qz311 (@Neg.neg Real Real.instNeg (Real.sin qz312)))) Bool.false 72604730177 274877906944 7427776436521 35869092955029504 Bool.false 23251945955 274877906944 7383487530139 35869092955029504 (BSN.cpow_neg_s_mk qz11 95415 1000 13 (@Eq.refl Real qz11) rfl)

noncomputable abbrev qz857 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13) qz268)

noncomputable def ep259 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz856) 1890347 524288 1 524288 72705 72706 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz856) (Real.sqrt qz857) Bool.false 1890347 524288 1 524288 (BSN.sqrt_natCast_div_one 13) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz857) Bool.false 1890347 524288 1 524288 1890347 524288 1 524288 (BSN.sqrt_enclosure 13 1 945173 945174 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep260 := BSN.log_dyadic_bound 5 21 5 4 35742602096145 262144 130491 699352521000 41015625 127272 26 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 5) (BSN.artanhQ 21) 0 4 699352521000 35742602096145 41015625 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz313 := (Real.log (Enclosure.sfrac Bool.false 13 1))

noncomputable def ep261 := @Enclosure.Real.IsNear.mulLit_ff qz11 qz313 95415 1000 0 1 11551488463034085 4503599627370496 1000000000391473 130491000000000000000 44087410868015888811 180143985094819840 6361000002490159753 8699400000000000000000 qz273 (BSN.isNear_log_sfrac 13 1 11551488463034085 4503599627370496 1000000000391473 130491000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz857) Bool.false 24225227133228857425920 9444732965739290427392 1000000000391473 130491000000000000000 11551488463034085 4503599627370496 1000000000391473 130491000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 127272 262144 24973259072661432 36028797018963968 130491 1000000000000000 rfl rfl rfl rfl (ep260 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep262 := nat_lit 13514943850539657412557410109366410708660579528016341233523486180689416249600

noncomputable def ep263 := nat_lit 11286007056331571738842165490225225517720176503778992330071868554581074176

noncomputable def ep264 := nat_lit 35378008930465042107216043923261187205177589906655727719265204590812482724096

noncomputable def ep265 := BSN.sin_dyadic_bound_f 1353840618 1073741824 3 2 524288 261237 ep262 ep109 ep263 ep264 ep111 ep263 499307 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1353840618) qz275 0 2 ep262 ep109 ep263 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1353840618) qz276 0 2 ep264 ep111 ep263 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz858 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 128311253) qz280)

noncomputable def ep266 := @Enclosure.Real.IsNear.cos_image qz312 qz858 Bool.false 128311253 524288 3 4096 Bool.false 499307 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz312 Bool.false 44087410868015888811 180143985094819840 6361000002490159753 8699400000000000000000 128311253 524288 3 4096 (ep261 rfl) rfl) (Enclosure.sfrac_false_div 128311253 524288) (BSN.cos_reduce3 qz858 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 95268064167711700156416) qz282) 226375608064910080 72057594037927936 Bool.false 499307 524288 38 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q3 128311253 524288 226375608064910080 72057594037927936 38 95268064167711700156416 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 499307 524288 95268064167711700156416 75557863725914323419136 1353840618 1073741824 261237 260982 (ep265 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep267 := nat_lit 7513318142324845927749157689865883827263753149566313570770857597518378393856

noncomputable def ep268 := nat_lit 22517382412861874639769788738617201030755819095691382727652429055445973033216

noncomputable def ep269 := BSN.cos_dyadic_bound_f 1353840618 1073741824 3 2 524288 261237 ep267 ep102 ep263 ep268 ep105 ep263 159905 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1353840618) qz269 0 2 ep267 ep102 ep263 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1353840618) qz270 0 2 ep268 ep105 ep263 rfl rfl rfl rfl) rfl rfl

noncomputable def ep270 := @Enclosure.Real.IsNear.sin_image qz312 qz858 Bool.false 128311253 524288 3 4096 Bool.true 159905 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz312 Bool.false 44087410868015888811 180143985094819840 6361000002490159753 8699400000000000000000 128311253 524288 3 4096 (ep261 rfl) rfl) (Enclosure.sfrac_false_div 128311253 524288) (BSN.sin_reduce3 qz858 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 95268064167711700156416) qz282) 226375608064910080 72057594037927936 Bool.false 159905 524288 38 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q3 128311253 524288 226375608064910080 72057594037927936 38 95268064167711700156416 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 159905 524288 95268064167711700156416 75557863725914323419136 1353840618 1073741824 261237 260982 (ep269 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz571 := (@Enclosure.Real.IsNear.recentre' qz311 Bool.false 145411 524288 1 524288 145411 524288 1 524288 (ep259 rfl rfl) rfl)

noncomputable def ep271 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz311 (Real.cos qz312)) (@HMul.hMul Real Real Real qz0 qz311 (@Neg.neg Real Real.instNeg (Real.sin qz312))) Bool.false 72604730177 274877906944 7427776436521 35869092955029504 Bool.false 23251945955 274877906944 7383487530139 35869092955029504 (@Enclosure.Real.IsNear.mulLit_ff qz311 (Real.cos qz312) 145411 524288 1 524288 499307 524288 395569 534491136 72604730177 274877906944 7427776436521 35869092955029504 qz571 (@Enclosure.Real.IsNear.recentre' (Real.cos qz312) Bool.false 499307 524288 395569 534491136 499307 524288 395569 534491136 (ep266 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz311 (@Neg.neg Real Real.instNeg (Real.sin qz312)) 145411 524288 1 524288 159905 524288 395569 534491136 23251945955 274877906944 7383487530139 35869092955029504 qz571 (@Enclosure.Real.IsNear.neg (Real.sin qz312) Bool.true 159905 524288 395569 534491136 (@Enclosure.Real.IsNear.recentre' (Real.sin qz312) Bool.true 159905 524288 395569 534491136 159905 524288 395569 534491136 (ep270 rfl rfl) rfl)) rfl)

noncomputable def ep272 := @ep190 72604730177 274877906944 7427776436521 35869092955029504 Bool.false 23251945955 274877906944 7383487530139 35869092955029504 Bool.true 28578185180004818616320 51983416015 137438953472 5438497321657 1494545539792896 Bool.false 9136014453880272191488 66473253929 274877906944 43440722424431 11956364318343168 (ep191 (BSN.head_sum_c_succ qz14 12 13 rfl rfl) (ep257 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep258 ep271) rfl rfl

noncomputable abbrev qz859 := (@Nat.cast Real Real.instNatCast 14)

noncomputable abbrev qz314 := (@Inv.inv Real Real.instInv (Real.sqrt qz859))

noncomputable abbrev qz315 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 14 1)))

noncomputable def ep273 := @Enclosure.Complex.IsNear.of_eq qz838 (Complex.mk (@HMul.hMul Real Real Real qz0 qz314 (Real.cos qz315)) (@HMul.hMul Real Real Real qz0 qz314 (@Neg.neg Real Real.instNeg (Real.sin qz315)))) Bool.false 32616385533 137438953472 3577761624295 17934546477514752 Bool.true 33787516851 274877906944 7126239110825 35869092955029504 (BSN.cpow_neg_s_mk qz11 95415 1000 14 (@Eq.refl Real qz11) rfl)

noncomputable abbrev qz860 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14) qz268)

noncomputable def ep274 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz859) 1961707 524288 1 524288 70060 70061 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz859) (Real.sqrt qz860) Bool.false 1961707 524288 1 524288 (BSN.sqrt_natCast_div_one 14) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz860) Bool.false 1961707 524288 1 524288 1961707 524288 1 524288 (BSN.sqrt_enclosure 14 1 980853 980854 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep275 := BSN.log_dyadic_bound 6 22 5 4 51857700491520 262144 130491 1346332575744 176359680 146699 28 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 6) (BSN.artanhQ 22) 0 4 1346332575744 51857700491520 176359680 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz316 := (Real.log (Enclosure.sfrac Bool.false 14 1))

noncomputable def ep276 := @Enclosure.Real.IsNear.mulLit_ff qz11 qz316 95415 1000 0 1 11885241781671653 4503599627370496 1000000000391473 130491000000000000000 226806068919640154199 900719925474099200 6361000002490159753 8699400000000000000000 qz273 (BSN.isNear_log_sfrac 14 1 11885241781671653 4503599627370496 1000000000391473 130491000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz860) Bool.false 24925158572916270432256 9444732965739290427392 1000000000391473 130491000000000000000 11885241781671653 4503599627370496 1000000000391473 130491000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 146699 262144 24973259072661432 36028797018963968 130491 1000000000000000 rfl rfl rfl rfl (ep275 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep277 := nat_lit 69338012947220322518533763729000625

noncomputable def ep278 := BSN.cos_dyadic_bound_f 513148245 1073741824 2 1 524288 261237 ep277 ep88 ep277 ep277 ep89 ep277 465546 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 513148245) qz269 0 1 ep277 ep88 ep277 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 513148245) qz270 0 1 ep277 ep89 ep277 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz861 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 132018507) qz280)

noncomputable def ep279 := @Enclosure.Real.IsNear.cos_image qz315 qz861 Bool.false 132018507 524288 3 4096 Bool.false 465546 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz315 Bool.false 226806068919640154199 900719925474099200 6361000002490159753 8699400000000000000000 132018507 524288 3 4096 (ep276 rfl) rfl) (Enclosure.sfrac_false_div 132018507 524288) (BSN.cos_reduce0 qz861 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 36109597617002804936704) qz282) 226375608064910080 72057594037927936 Bool.false 465546 524288 40 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q0 132018507 524288 226375608064910080 72057594037927936 40 36109597617002804936704 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 465546 524288 36109597617002804936704 75557863725914323419136 513148245 1073741824 261237 260982 (ep278 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep280 := BSN.sin_dyadic_bound_f 513148245 1073741824 2 1 524288 261237 ep277 ep92 ep277 ep277 ep93 ep277 241131 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 513148245) qz275 0 1 ep277 ep92 ep277 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 513148245) qz276 0 1 ep277 ep93 ep277 rfl rfl rfl rfl) rfl rfl

noncomputable def ep281 := @Enclosure.Real.IsNear.sin_image qz315 qz861 Bool.false 132018507 524288 3 4096 Bool.false 241131 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz315 Bool.false 226806068919640154199 900719925474099200 6361000002490159753 8699400000000000000000 132018507 524288 3 4096 (ep276 rfl) rfl) (Enclosure.sfrac_false_div 132018507 524288) (BSN.sin_reduce0 qz861 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 36109597617002804936704) qz282) 226375608064910080 72057594037927936 Bool.false 241131 524288 40 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q0 132018507 524288 226375608064910080 72057594037927936 40 36109597617002804936704 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 241131 524288 36109597617002804936704 75557863725914323419136 513148245 1073741824 261237 260982 (ep280 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz572 := (@Enclosure.Real.IsNear.recentre' qz314 Bool.false 140121 524288 1 524288 140121 524288 1 524288 (ep274 rfl rfl) rfl)

noncomputable def ep282 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz314 (Real.cos qz315)) (@HMul.hMul Real Real Real qz0 qz314 (@Neg.neg Real Real.instNeg (Real.sin qz315))) Bool.false 32616385533 137438953472 3577761624295 17934546477514752 Bool.true 33787516851 274877906944 7126239110825 35869092955029504 (@Enclosure.Real.IsNear.mulLit_ff qz314 (Real.cos qz315) 140121 524288 1 524288 232773 262144 395569 534491136 32616385533 137438953472 3577761624295 17934546477514752 qz572 (@Enclosure.Real.IsNear.recentre' (Real.cos qz315) Bool.false 465546 524288 395569 534491136 232773 262144 395569 534491136 (ep279 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz314 (@Neg.neg Real Real.instNeg (Real.sin qz315)) 140121 524288 1 524288 241131 524288 395569 534491136 33787516851 274877906944 7126239110825 35869092955029504 qz572 (@Enclosure.Real.IsNear.neg (Real.sin qz315) Bool.false 241131 524288 395569 534491136 (@Enclosure.Real.IsNear.recentre' (Real.sin qz315) Bool.false 241131 524288 395569 534491136 241131 524288 395569 534491136 (ep281 rfl rfl) rfl)) rfl)

noncomputable def ep283 := @ep188 32616385533 137438953472 3577761624295 17934546477514752 Bool.true 33787516851 274877906944 7126239110825 35869092955029504 Bool.true 2661784401306403733504 9683515241 68719476736 68839729484179 17934546477514752 Bool.false 8984586994922534469632 16342868539 137438953472 68724203192059 17934546477514752 (ep189 (BSN.head_sum_c_succ qz14 13 14 rfl rfl) (ep272 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep273 ep282) rfl rfl

noncomputable abbrev qz862 := (@Nat.cast Real Real.instNatCast 15)

noncomputable abbrev qz317 := (@Inv.inv Real Real.instInv (Real.sqrt qz862))

noncomputable abbrev qz318 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 15 1)))

noncomputable def ep284 := @Enclosure.Complex.IsNear.of_eq qz837 (Complex.mk (@HMul.hMul Real Real Real qz0 qz317 (Real.cos qz318)) (@HMul.hMul Real Real Real qz0 qz317 (@Neg.neg Real Real.instNeg (Real.sin qz318)))) Bool.false 12643245287 68719476736 72090442009 373636384948224 Bool.true 12448852531 68719476736 144165268595 747272769896448 (BSN.cpow_neg_s_mk qz11 95415 1000 15 (@Eq.refl Real qz11) rfl)

noncomputable abbrev qz863 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 15) qz268)

noncomputable def ep285 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz862) 2030559 524288 1 524288 67685 67686 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz862) (Real.sqrt qz863) Bool.false 2030559 524288 1 524288 (BSN.sqrt_natCast_div_one 15) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz863) Bool.false 2030559 524288 1 524288 2030559 524288 1 524288 (BSN.sqrt_enclosure 15 1 1015279 1015280 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep286 := BSN.log_dyadic_bound 7 23 6 5 430628584065881355 262144 130491 14087658153505881 266939110305 164785 30 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 7) (BSN.artanhQ 23) 0 5 14087658153505881 430628584065881355 266939110305 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz319 := (Real.log (Enclosure.sfrac Bool.false 15 1))

noncomputable def ep287 := @Enclosure.Real.IsNear.mulLit_ff qz11 qz319 95415 1000 0 1 12195956895733477 4503599627370496 1000000000391473 130491000000000000000 232735445441281941591 900719925474099200 6361000002490159753 8699400000000000000000 qz273 (BSN.isNear_log_sfrac 15 1 12195956895733477 4503599627370496 1000000000391473 130491000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz863) Bool.false 25576775395801252757504 9444732965739290427392 1000000000391473 130491000000000000000 12195956895733477 4503599627370496 1000000000391473 130491000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 164785 262144 24973259072661432 36028797018963968 130491 1000000000000000 rfl rfl rfl rfl (ep286 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep288 := nat_lit 1085778836119913643487456303974358941404818687365939884728466365472031235201

noncomputable def ep289 := nat_lit 236306769450809928445163559299392524615529361386304614391109479568366721

noncomputable def ep290 := nat_lit 3256863894820839310605478584804478039165225003375047044956616877456956972161

noncomputable def ep291 := BSN.cos_dyadic_bound_f 834996241 1073741824 3 2 524288 261237 ep288 ep102 ep289 ep290 ep105 ep289 373588 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 834996241) qz269 0 2 ep288 ep102 ep289 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 834996241) qz270 0 2 ep290 ep105 ep289 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz864 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 67734929) qz271)

noncomputable def ep292 := @Enclosure.Real.IsNear.cos_image qz318 qz864 Bool.false 67734929 262144 385 524288 Bool.false 373588 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz318 Bool.false 232735445441281941591 900719925474099200 6361000002490159753 8699400000000000000000 67734929 262144 385 524288 (ep287 rfl) rfl) (Enclosure.sfrac_false_div 67734929 262144) (BSN.cos_reduce0 qz864 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 29378818446626870263808) qz274) 226375608064910080 72057594037927936 Bool.false 373588 524288 41 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q0 67734929 262144 226375608064910080 72057594037927936 41 29378818446626870263808 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 373588 524288 29378818446626870263808 37778931862957161709568 834996241 1073741824 261237 260982 (ep291 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep293 := nat_lit 486113946982402396947534899329066561

noncomputable def ep294 := BSN.sin_dyadic_bound_f 834996241 1073741824 2 1 524288 261237 ep293 ep92 ep293 ep293 ep93 ep293 367844 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 834996241) qz275 0 1 ep293 ep92 ep293 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 834996241) qz276 0 1 ep293 ep93 ep293 rfl rfl rfl rfl) rfl rfl

noncomputable def ep295 := @Enclosure.Real.IsNear.sin_image qz318 qz864 Bool.false 67734929 262144 385 524288 Bool.false 367844 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz318 Bool.false 232735445441281941591 900719925474099200 6361000002490159753 8699400000000000000000 67734929 262144 385 524288 (ep287 rfl) rfl) (Enclosure.sfrac_false_div 67734929 262144) (BSN.sin_reduce0 qz864 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 29378818446626870263808) qz274) 226375608064910080 72057594037927936 Bool.false 367844 524288 41 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q0 67734929 262144 226375608064910080 72057594037927936 41 29378818446626870263808 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 367844 524288 29378818446626870263808 37778931862957161709568 834996241 1073741824 261237 260982 (ep294 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz573 := (@Enclosure.Real.IsNear.recentre' qz317 Bool.false 135371 524288 1 524288 135371 524288 1 524288 (ep285 rfl rfl) rfl)

noncomputable def ep296 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz317 (Real.cos qz318)) (@HMul.hMul Real Real Real qz0 qz317 (@Neg.neg Real Real.instNeg (Real.sin qz318))) Bool.false 12643245287 68719476736 72090442009 373636384948224 Bool.true 12448852531 68719476736 144165268595 747272769896448 (@Enclosure.Real.IsNear.mulLit_ff qz317 (Real.cos qz318) 135371 524288 1 524288 93397 131072 50763323 68414865408 12643245287 68719476736 72090442009 373636384948224 qz573 (@Enclosure.Real.IsNear.recentre' (Real.cos qz318) Bool.false 373588 524288 50763323 68414865408 93397 131072 50763323 68414865408 (ep292 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz317 (@Neg.neg Real Real.instNeg (Real.sin qz318)) 135371 524288 1 524288 91961 131072 50763323 68414865408 12448852531 68719476736 144165268595 747272769896448 qz573 (@Enclosure.Real.IsNear.neg (Real.sin qz318) Bool.false 91961 131072 50763323 68414865408 (@Enclosure.Real.IsNear.recentre' (Real.sin qz318) Bool.false 367844 524288 50763323 68414865408 91961 131072 50763323 68414865408 (ep295 rfl rfl) rfl)) rfl)

noncomputable def ep297 := @ep186 12643245287 68719476736 72090442009 373636384948224 Bool.true 12448852531 68719476736 144165268595 747272769896448 Bool.false 203391100040937209856 1479865023 34359738368 72300070700611 17934546477514752 Bool.true 587883889422581628928 8554836523 137438953472 72184169638339 17934546477514752 (ep187 (BSN.head_sum_c_succ qz14 14 15 rfl rfl) (ep283 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep284 ep296) rfl rfl

noncomputable abbrev qz865 := (@Nat.cast Real Real.instNatCast 16)

noncomputable abbrev qz320 := (@Inv.inv Real Real.instInv (Real.sqrt qz865))

noncomputable abbrev qz321 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 16 1)))

noncomputable def ep298 := @Enclosure.Complex.IsNear.of_eq qz836 (Complex.mk (@HMul.hMul Real Real Real qz0 qz320 (Real.cos qz321)) (@HMul.hMul Real Real Real qz0 qz320 (@Neg.neg Real Real.instNeg (Real.sin qz321)))) Bool.false 3411909201 17179869184 418180970965 2241818309689344 Bool.true 20869517833 137438953472 3339050446445 17934546477514752 (BSN.cpow_neg_s_mk qz11 95415 1000 16 (@Eq.refl Real qz11) rfl)

noncomputable abbrev qz866 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16) qz268)

noncomputable def ep299 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz865) 2097153 524288 1 524288 65535 65536 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz865) (Real.sqrt qz866) Bool.false 2097153 524288 1 524288 (BSN.sqrt_natCast_div_one 16) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz866) Bool.false 2097153 524288 1 524288 2097153 524288 1 524288 (BSN.sqrt_enclosure 16 1 1048576 1048577 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep300 := BSN.log_dyadic_bound 0 32 1 0 1 262144 130491 0 1 0 32 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 32) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz322 := (Real.log (Enclosure.sfrac Bool.false 16 1))

noncomputable def ep301 := @Enclosure.Real.IsNear.mulLit_ff qz11 qz322 95415 1000 0 1 3121657384082679 1125899906842624 250000000130491 32622750000000000000 59570587860449763357 225179981368524800 1590250000830053251 2174850000000000000000 qz273 (BSN.isNear_log_sfrac 16 1 3121657384082679 1125899906842624 250000000130491 32622750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz866) Bool.false 26186360105375033720832 9444732965739290427392 1000000000521964 130491000000000000000 3121657384082679 1125899906842624 250000000130491 32622750000000000000 (BSN.log_rat_reduce_isNear 16 1 4 32 32 0 262144 24973259072661432 36028797018963968 130491 1000000000000000 rfl rfl rfl rfl (ep300 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep302 := nat_lit 241345707657075469778575413610845841

noncomputable def ep303 := BSN.cos_dyadic_bound_f 700906189 1073741824 2 1 524288 261237 ep302 ep88 ep302 ep302 ep89 ep302 416496 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 700906189) qz269 0 1 ep302 ep88 ep302 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 700906189) qz270 0 1 ep302 ep89 ep302 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz867 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 138698583) qz280)

noncomputable def ep304 := @Enclosure.Real.IsNear.cos_image qz321 qz867 Bool.false 138698583 524288 3 4096 Bool.false 416496 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz321 Bool.false 59570587860449763357 225179981368524800 1590250000830053251 2174850000000000000000 138698583 524288 3 4096 (ep301 rfl) rfl) (Enclosure.sfrac_false_div 138698583 524288) (BSN.cos_reduce0 qz867 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 49321888308929186758656) qz282) 226375608064910080 72057594037927936 Bool.false 416496 524288 42 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q0 138698583 524288 226375608064910080 72057594037927936 42 49321888308929186758656 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 416496 524288 49321888308929186758656 75557863725914323419136 700906189 1073741824 261237 260982 (ep303 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep305 := BSN.sin_dyadic_bound_f 700906189 1073741824 2 1 524288 261237 ep302 ep92 ep302 ep302 ep93 ep302 318446 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 700906189) qz275 0 1 ep302 ep92 ep302 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 700906189) qz276 0 1 ep302 ep93 ep302 rfl rfl rfl rfl) rfl rfl

noncomputable def ep306 := @Enclosure.Real.IsNear.sin_image qz321 qz867 Bool.false 138698583 524288 3 4096 Bool.false 318446 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz321 Bool.false 59570587860449763357 225179981368524800 1590250000830053251 2174850000000000000000 138698583 524288 3 4096 (ep301 rfl) rfl) (Enclosure.sfrac_false_div 138698583 524288) (BSN.sin_reduce0 qz867 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 49321888308929186758656) qz282) 226375608064910080 72057594037927936 Bool.false 318446 524288 42 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q0 138698583 524288 226375608064910080 72057594037927936 42 49321888308929186758656 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 318446 524288 49321888308929186758656 75557863725914323419136 700906189 1073741824 261237 260982 (ep305 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz574 := (@Enclosure.Real.IsNear.recentre' qz320 Bool.false 131071 524288 1 524288 131071 524288 1 524288 (ep299 rfl rfl) rfl)

noncomputable def ep307 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz320 (Real.cos qz321)) (@HMul.hMul Real Real Real qz0 qz320 (@Neg.neg Real Real.instNeg (Real.sin qz321))) Bool.false 3411909201 17179869184 418180970965 2241818309689344 Bool.true 20869517833 137438953472 3339050446445 17934546477514752 (@Enclosure.Real.IsNear.mulLit_ff qz320 (Real.cos qz321) 131071 524288 1 524288 26031 32768 395569 534491136 3411909201 17179869184 418180970965 2241818309689344 qz574 (@Enclosure.Real.IsNear.recentre' (Real.cos qz321) Bool.false 416496 524288 395569 534491136 26031 32768 395569 534491136 (ep304 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz320 (@Neg.neg Real Real.instNeg (Real.sin qz321)) 131071 524288 1 524288 159223 262144 395569 534491136 20869517833 137438953472 3339050446445 17934546477514752 qz574 (@Enclosure.Real.IsNear.neg (Real.sin qz321) Bool.false 159223 262144 395569 534491136 (@Enclosure.Real.IsNear.recentre' (Real.sin qz321) Bool.false 318446 524288 395569 534491136 159223 262144 395569 534491136 (ep306 rfl rfl) rfl)) rfl)

noncomputable def ep308 := @ep184 3411909201 17179869184 418180970965 2241818309689344 Bool.true 20869517833 137438953472 3339050446445 17934546477514752 Bool.false 142656194986849075200 8303683425 34359738368 25215172822777 5978182159171584 Bool.true 4044052469277924524032 7356088589 34359738368 1573400418433 373636384948224 (ep185 (BSN.head_sum_c_succ qz14 15 16 rfl rfl) (ep297 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep298 ep307) rfl rfl

theorem EMRow28.d8 : Enclosure.Complex.IsNear (BSN.headSumC qz14 17) Bool.false 8303683425 34359738368 25215172822777 5978182159171584 Bool.true 7356088589 34359738368 1573400418433 373636384948224 := ep183 (BSN.head_sum_c_succ qz14 16 17 rfl rfl) (ep308 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

theorem EMRow28.d9 : @Eq Nat (BSN.factNat (Nat.mul 2 1)) 2 := @Eq.refl Nat 2

theorem EMRow28.d10 : @Eq Nat (Nat.pow 24 1) 24 := @Eq.refl Nat 24

theorem EMRow28.d11 : @Eq Nat (BSN.factNat (Nat.mul 2 2)) 24 := @Eq.refl Nat 24

noncomputable abbrev qz20 := (@HAdd.hAdd Complex Complex Complex qz263 qz262 qz552)

noncomputable def ep309 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz3 (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 2)) qz20) Bool.true 3277298001 80000 0 1 Bool.true 6944893154787 8000000 0 1

noncomputable def ep310 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.re qz20)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.im qz20)) 364130889 16000 0 1 364160889 20000 0 1

noncomputable def ep311 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.re qz20) 364130889 40000 0 1 5 2 0 1 364130889 16000

noncomputable abbrev qz575 := (@Nat.cast Complex Complex.instNatCast 1)

noncomputable abbrev qz21 := (@HAdd.hAdd Complex Complex Complex qz263 qz262 qz575)

noncomputable def ep312 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz3 (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1)) qz21) Bool.true 364130889 40000 0 1 Bool.false 19083 100 0 1

noncomputable def ep313 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.re qz21)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.im qz21)) 3 4 0 1 364160889 40000 0 1

noncomputable def ep314 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.re qz21) 1 2 0 1 3 2 0 1 3 4

noncomputable def ep315 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1)) qz14 Bool.false 1 2 0 1 Bool.false 95415 1000 0 1 (BSN.ascPochhammer_one_eval qz14)

noncomputable abbrev qz323 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz324 := (Enclosure.Real.IsNear.const Bool.false 1 2)

noncomputable def ep316 := ep315 (@Enclosure.Complex.IsNear.of_eq qz14 (Complex.mk qz323 qz11) Bool.false 1 2 0 1 Bool.false 95415 1000 0 1 (BSN.s_crit_mk qz11 Bool.false 95415 1000 (@Eq.refl Real qz11)) (@Enclosure.Complex.IsNear.mk qz323 qz11 Bool.false 1 2 0 1 Bool.false 95415 1000 0 1 qz324 qz273))

noncomputable def ep317 := @ep314 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 95415 1000 0 1 ep316)

noncomputable def ep318 := @Enclosure.Complex.IsNear.of_eq qz21 (Complex.mk (Enclosure.sfrac Bool.false 3 2) qz11) Bool.false 3 2 0 1 Bool.false 95415 1000 0 1 (BSN.s_add_nat_mk qz11 Bool.false 95415 1000 1 (@Eq.refl Real qz11))

noncomputable abbrev qz576 := (ep318 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz11 Bool.false 3 2 0 1 Bool.false 95415 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz273))

noncomputable def ep319 := ep317 (@Enclosure.Complex.IsNear.re_isNear qz21 Bool.false 3 2 0 1 Bool.false 95415 1000 0 1 qz576)

noncomputable def ep320 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.im qz21) 95415 1000 0 1 95415 1000 0 1 364160889 40000

noncomputable def ep321 := @ep320 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 95415 1000 0 1 ep316)

noncomputable def ep322 := ep321 (@Enclosure.Complex.IsNear.im_isNear qz21 Bool.false 3 2 0 1 Bool.false 95415 1000 0 1 qz576)

noncomputable def ep323 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1)) qz21 Bool.true 364130889 40000 0 1 Bool.false 19083 100 0 1 (@ep313 1456523556 364130889 40000 0 1 (ep319 rfl) (ep322 rfl) rfl rfl)

noncomputable def ep324 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.im qz21)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.re qz21)) 19083 400 0 1 57249 400 0 1

noncomputable def ep325 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.im qz21) 1 2 0 1 95415 1000 0 1 19083 400

noncomputable def ep326 := @ep325 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 95415 1000 0 1 ep316)

noncomputable def ep327 := ep326 (@Enclosure.Complex.IsNear.im_isNear qz21 Bool.false 3 2 0 1 Bool.false 95415 1000 0 1 qz576)

noncomputable def ep328 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.re qz21) 95415 1000 0 1 3 2 0 1 57249 400

noncomputable def ep329 := @ep328 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 95415 1000 0 1 ep316)

noncomputable def ep330 := ep329 (@Enclosure.Complex.IsNear.re_isNear qz21 Bool.false 3 2 0 1 Bool.false 95415 1000 0 1 qz576)

noncomputable abbrev qz577 := (ep312 (BSN.ascPochhammer_succ_eval_c 1 2 qz14 rfl) (ep323 (@ep324 30532800 19083 100 0 1 (ep327 rfl) (ep330 rfl) rfl rfl)))

noncomputable def ep331 := @ep311 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 364130889 40000 0 1 Bool.false 19083 100 0 1 qz577)

noncomputable def ep332 := @Enclosure.Complex.IsNear.of_eq qz20 (Complex.mk (Enclosure.sfrac Bool.false 5 2) qz11) Bool.false 5 2 0 1 Bool.false 95415 1000 0 1 (BSN.s_add_nat_mk qz11 Bool.false 95415 1000 2 (@Eq.refl Real qz11))

noncomputable abbrev qz578 := (ep332 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz11 Bool.false 5 2 0 1 Bool.false 95415 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz273))

noncomputable def ep333 := ep331 (@Enclosure.Complex.IsNear.re_isNear qz20 Bool.false 5 2 0 1 Bool.false 95415 1000 0 1 qz578)

noncomputable def ep334 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.im qz20) 19083 100 0 1 95415 1000 0 1 364160889 20000

noncomputable def ep335 := @ep334 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 364130889 40000 0 1 Bool.false 19083 100 0 1 qz577)

noncomputable def ep336 := ep335 (@Enclosure.Complex.IsNear.im_isNear qz20 Bool.false 5 2 0 1 Bool.false 95415 1000 0 1 qz578)

noncomputable def ep337 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 2)) qz20 Bool.true 3277298001 80000 0 1 Bool.true 6944893154787 8000000 0 1 (@ep310 13109192004000 3277298001 80000 0 1 (ep333 rfl) (ep336 rfl) rfl rfl)

noncomputable def ep338 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.im qz20)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.re qz20)) 6948709754787 8000000 0 1 19083 40 0 1

noncomputable def ep339 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.im qz20) 364130889 40000 0 1 95415 1000 0 1 6948709754787 8000000

noncomputable def ep340 := @ep339 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 364130889 40000 0 1 Bool.false 19083 100 0 1 qz577)

noncomputable def ep341 := ep340 (@Enclosure.Complex.IsNear.im_isNear qz20 Bool.false 5 2 0 1 Bool.false 95415 1000 0 1 qz578)

noncomputable def ep342 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.re qz20) 19083 100 0 1 5 2 0 1 19083 40

noncomputable def ep343 := @ep342 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 364130889 40000 0 1 Bool.false 19083 100 0 1 qz577)

noncomputable def ep344 := ep343 (@Enclosure.Complex.IsNear.re_isNear qz20 Bool.false 5 2 0 1 Bool.false 95415 1000 0 1 qz578)

noncomputable abbrev qz579 := (ep337 (@ep338 277795726191480 6944893154787 8000000 0 1 (ep341 rfl) (ep344 rfl) rfl rfl))

theorem EMRow28.d12 : Enclosure.Complex.IsNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 3277298001 80000 0 1 Bool.true 6944893154787 8000000 0 1 := ep309 (BSN.ascPochhammer_succ_eval_c 2 3 qz14 rfl) qz579

theorem EMRow28.d13 : @Eq Nat (Nat.pow 24 3) 13824 := @Eq.refl Nat 13824

noncomputable def ep345 := nat_lit 74446297036252599495477174088283804597

noncomputable def ep346 := nat_lit 154777356022539777172764056616960000000

noncomputable def ep347 := nat_lit 136138598849929480118537956354576332141618205363

noncomputable def ep348 := nat_lit 23719801571374742388770473830832905482403840000000

noncomputable abbrev qz580 := (@instHSub Complex Complex.instSub)

noncomputable abbrev qz22 := qz580

noncomputable abbrev qz23 := (Complex.Stirling.logGammaStirling 2 qz257)

noncomputable abbrev qz581 := (@HAdd.hAdd Complex Complex Complex qz811 qz812 (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I (@HDiv.hDiv Complex Complex Complex qz813 (↑qz814) (2 : Complex))))

noncomputable abbrev qz325 := qz581

noncomputable abbrev qz24 := qz325

noncomputable abbrev qz326 := (@instHSub Real Real.instSub)

noncomputable abbrev qz327 := (@HMul.hMul Real Real Real qz0 (@HDiv.hDiv Real Real Real qz1 qz11 (2 : Real)) (Real.log Real.pi))

noncomputable def ep349 := Complex.re (@HMul.hMul Complex Complex Complex qz3 (Complex.exp (@HMul.hMul Complex Complex Complex qz3 Complex.I ↑(@HSub.hSub Real Real Real qz326 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz23 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz24 (@Nat.cast Complex Complex.instNatCast j))))) qz327))) (zetaApproximant qz14 2 24))

noncomputable def ep350 := @Enclosure.Real.IsNear.of_eq ep349 (@HSub.hSub Real Real Real qz326 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz326 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz23 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz24 (@Nat.cast Complex Complex.instNatCast j))))) qz327)) (Complex.re (zetaApproximant qz14 2 24))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz326 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz23 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz24 (@Nat.cast Complex Complex.instNatCast j))))) qz327)) (Complex.im (zetaApproximant qz14 2 24))))

noncomputable def ep351 := nat_lit 14889271964799951077476493941708625983

noncomputable def ep352 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz326 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz23 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz24 (@Nat.cast Complex Complex.instNatCast j))))) qz327)) (Complex.re (zetaApproximant qz14 2 24))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz326 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz23 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz24 (@Nat.cast Complex Complex.instNatCast j))))) qz327)) (Complex.im (zetaApproximant qz14 2 24))) ep351

noncomputable def ep353 := nat_lit 30955471204507955434552811323392000000

noncomputable def ep354 := nat_lit 5440791449739315420027195365923895132002562453

noncomputable def ep355 := nat_lit 948792062854989695550818953233316219296153600000

noncomputable def ep356 := nat_lit 3488208175327328071978903295851

noncomputable def ep357 := nat_lit 8598742001252209842931336478720000000

noncomputable def ep358 := nat_lit 59406303223297308929036103239476920777072019

noncomputable def ep359 := nat_lit 11859900785687371194385236915416452741201920000000

noncomputable def ep360 := nat_lit 128028900232664627161904774979209015717255498177417381731074905735168000000

noncomputable def ep361 := @Enclosure.Real.IsNear.mulLit_ff (Real.cos (@HSub.hSub Real Real Real qz326 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz23 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz24 (@Nat.cast Complex Complex.instNatCast j))))) qz327)) (Complex.re (zetaApproximant qz14 2 24)) 524287 524288 132539

noncomputable def ep362 := nat_lit 28399086692593848555231188150209

noncomputable def ep363 := nat_lit 59042875679984961384873984000000

noncomputable def ep364 := nat_lit 22406065808264811276210449293230853

noncomputable def ep365 := nat_lit 4078886765483074021450724671488000000

noncomputable def ep366 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz326 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz23 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz24 (@Nat.cast Complex Complex.instNatCast j))))) qz327)) Bool.false 524287 524288 132539

noncomputable abbrev qz868 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 42824649) qz280)

noncomputable def ep367 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz326 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz23 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz24 (@Nat.cast Complex Complex.instNatCast j))))) qz327) qz868 Bool.false 42824649 524288 1

noncomputable def ep368 := nat_lit 376689603252002468980186327

noncomputable def ep369 := nat_lit 4611686018427387904000000

noncomputable def ep370 := nat_lit 14253475026192545392431569492095873

noncomputable def ep371 := nat_lit 29383960948760169676800000000000000000

noncomputable def ep372 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz326 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz23 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz24 (@Nat.cast Complex Complex.instNatCast j))))) qz327) Bool.false ep368 ep369 ep370 ep371

noncomputable def ep373 := nat_lit 628543867420315338991066327

noncomputable def ep374 := nat_lit 3558320325242107504431569492095873

noncomputable def ep375 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz23 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz24 (@Nat.cast Complex Complex.instNatCast j))))) qz327 ep373 ep369 ep374 ep371 1431625743 26214400

noncomputable def ep376 := nat_lit 9874691935489293522834196450508800

noncomputable def ep377 := nat_lit 10374382190366030985966557

noncomputable def ep378 := nat_lit 1479942239556019848503097776616017

noncomputable def ep379 := nat_lit 7345990237190042419200000000000000000

noncomputable def ep380 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz22 qz23 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz24 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true ep377 138350580552821637120000 ep378 ep379 Bool.false ep373 ep369

noncomputable def ep381 := nat_lit 8234910117648809282286557

noncomputable def ep382 := nat_lit 474549081350758954428305614464539

noncomputable def ep383 := nat_lit 2448663412396680806400000000000000000

noncomputable def ep384 := nat_lit 656843974299960166639066327

noncomputable def ep385 := nat_lit 1035986787482096660844683050914091

noncomputable def ep386 := @Enclosure.Complex.IsNear.subLitP qz23 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz24 (@Nat.cast Complex Complex.instNatCast j))) Bool.true ep381 138350580552821637120000 ep382 ep383 Bool.false ep384 ep369 ep385

noncomputable def ep387 := nat_lit 9794653649586723225600000000000000000

noncomputable def ep388 := nat_lit 23361031883365783622935640677925452251136

noncomputable def ep389 := nat_lit 88459685221879456300196938076384191840256

noncomputable abbrev qz328 := (@HSub.hSub Complex Complex Complex qz580 qz542 qz549)

noncomputable abbrev qz329 := (Complex.log qz542)

noncomputable abbrev qz25 := (@HSub.hSub Complex Complex Complex qz580 (@HMul.hMul Complex Complex Complex qz255 qz328 qz329) qz257)

noncomputable abbrev qz330 := qz549

noncomputable abbrev qz26 := qz330

noncomputable abbrev qz582 := qz813

noncomputable abbrev qz331 := qz582

noncomputable abbrev qz27 := qz331

noncomputable abbrev qz869 := (@instHMul Nat instMulNat)

noncomputable abbrev qz28 := qz869

noncomputable abbrev qz583 := (@instHPow Complex Int (@ZPow.toPow Complex (@DivInvMonoid.toZPow Complex Complex.instDivInvMonoid)))

noncomputable abbrev qz29 := qz583

noncomputable abbrev qz30 := (@instHSub Int Int.instSub)

noncomputable abbrev qz870 := (@OfNat.ofNat Int 1 (@instOfNat 1))

noncomputable abbrev qz332 := qz870

noncomputable abbrev qz31 := qz332

noncomputable abbrev qz32 := (@instHMul Int Int.instMul)

noncomputable abbrev qz584 := (@OfNat.ofNat Int 2 (@instOfNat 2))

noncomputable abbrev qz33 := qz584

noncomputable abbrev qz871 := (@HMul.hMul Complex Complex Complex qz3 qz26 ↑qz253)

noncomputable def ep390 := @Enclosure.Complex.IsNear.of_eq qz23 (@HAdd.hAdd Complex Complex Complex qz15 (@HAdd.hAdd Complex Complex Complex qz15 qz25 qz871) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz22 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz29 qz5 (@HSub.hSub Int Int Int qz30 qz31 (@HMul.hMul Int Int Int qz32 qz33 (@Nat.cast Int instNatCastInt k)))))) Bool.true ep381

noncomputable def ep391 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz15 qz25 qz871) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz22 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz29 qz5 (@HSub.hSub Int Int Int qz30 qz31 (@HMul.hMul Int Int Int qz32 qz33 (@Nat.cast Int instNatCastInt k))))) Bool.true 53612835140918771209 900719925474099200

noncomputable def ep392 := nat_lit 2075258708292324556800000

noncomputable def ep393 := nat_lit 23058430092136939520000000

noncomputable def ep394 := nat_lit 7417347627454540971929657811232855844454400

noncomputable def ep395 := nat_lit 2366529822318285006154235996643654037510553600

noncomputable def ep396 := @ep391 6743742311118066251 34797600000000000000000 Bool.false 513165598809171677823 3602879701896396800 3680500009195831261 34797600000000000000000 Bool.false 21359996313975415843 138350580552821637120000 342273729475339 ep392 Bool.true 7992175779580974373673 ep369 42688702149581643 ep393 Bool.true ep394 ep381 138350580552821637120000 ep382 ep383 Bool.false ep395

noncomputable def ep397 := @Enclosure.Complex.IsNear.addLitP qz25 qz871 Bool.true 54440540622360870409 900719925474099200 6611000001547753751 34797600000000000000000

noncomputable def ep398 := nat_lit 7027141527590505179906048

noncomputable def ep399 := @ep397 Bool.false 513165598809171677823 3602879701896396800 3680500009195831261 34797600000000000000000 Bool.false 120447 131072 1 262144 Bool.false 0 1 0 1 Bool.true ep398 53612835140918771209 900719925474099200 6743742311118066251 34797600000000000000000 Bool.false 513165598809171677823 513165598809171677823 3602879701896396800

noncomputable abbrev qz34 := (@HMul.hMul Complex Complex Complex qz255 qz328 qz329)

noncomputable def ep400 := @Enclosure.Complex.IsNear.subLitP qz34 qz5 Bool.true 50612480939095948809 900719925474099200 6611000001547753751 34797600000000000000000 Bool.false 685049982187394028159

noncomputable def ep401 := nat_lit 2052662395236686711292000

noncomputable def ep402 := @ep400 3602879701896396800 3680500009195831261 34797600000000000000000 Bool.false 17000 4000 0 1 Bool.false 190830 4000 0 1 Bool.true 217762162489443481636000 54440540622360870409 900719925474099200 6611000001547753751 34797600000000000000000 Bool.false ep401 513165598809171677823 3602879701896396800 3680500009195831261 34797600000000000000000

noncomputable abbrev qz35 := qz328

noncomputable abbrev qz36 := qz329

noncomputable def ep403 := @Enclosure.Complex.IsNear.mul qz35 qz36 Bool.true 50612480939095948809 900719925474099200 6611000001547753751 34797600000000000000000 Bool.false 685049982187394028159 3602879701896396800 3680500009195831261

noncomputable def ep404 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re qz35) (Complex.re qz36)) (@HMul.hMul Real Real Real qz0 (Complex.im qz35) (Complex.im qz36)) 522738309959756595 36028797018963968 500000001435401 69595200000000000000 15920234672022465921 225179981368524800

noncomputable def ep405 := nat_lit 455876700595217693022869573785878528

noncomputable def ep406 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz35) (Complex.re qz36) 15000 4000 0 1 34849220663983773 9007199254740992 500000001435401 260982000000000000000

noncomputable def ep407 := @Enclosure.Complex.IsNear.re_isNear qz35 Bool.false 15000 4000 0 1 Bool.false 190830 4000 0 1

noncomputable def ep408 := @Enclosure.Complex.IsNear.of_eq qz35 (Complex.mk (Enclosure.sfrac Bool.false 15000 4000) qz261) Bool.false 15000 4000 0 1 Bool.false 190830 4000 0

noncomputable def ep409 := @Enclosure.Complex.IsNear.of_eq qz36 (Complex.log qz260) Bool.false 34849220663983773 9007199254740992 500000001435401 260982000000000000000 Bool.false 834262677357987 562949953421312 1000000000130491 260982000000000000000

noncomputable def ep410 := nat_lit 349427993474415459646076329243144561500000000

noncomputable def ep411 := nat_lit 374791488353424522467541601762432800000000

noncomputable def ep412 := nat_lit 720812218947507634011815220912300000000

noncomputable def ep413 := BSN.log_dyadic_bound 3937088900 69473088900 3 2 ep410 524288 260982 ep411 ep412 59487 73410177800 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 3937088900) (BSN.artanhQ 69473088900) 0 2 ep411 ep410 ep412 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz585 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable def ep414 := @Enclosure.Real.IsNear.mulLit_ff qz323 (Real.log (Enclosure.sfrac Bool.false 36705088900 16000000)) 1 2 0 1 34849220663983773 4503599627370496 500000001435401 130491000000000000000 34849220663983773 9007199254740992 500000001435401 260982000000000000000 qz324 (BSN.isNear_log_sfrac 36705088900 16000000 34849220663983773 4503599627370496 500000001435401 130491000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 36705088900) qz585)) Bool.false 146168225627829795028992 18889465931478580854784 1000000002870802 260982000000000000000 34849220663983773 4503599627370496 500000001435401 130491000000000000000 (BSN.log_rat_reduce_isNear 36705088900 16000000 11 73410177800 65536000000 59487 524288 24973259072661432 36028797018963968 260982 1000000000000000 rfl rfl rfl rfl (ep413 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep415 := BSN.arctan_dyadic_bound_f 17000 190830 1 0 524288 260982 0 1 1 0 1 1 46582 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 17000) (BSN.arctanEvenQ 190830) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 17000) (BSN.arctanOddQ 190830) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz333 := (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz334 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 2) Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable abbrev qz586 := (@Nat.cast Real Real.instNatCast 17000)

noncomputable abbrev qz587 := (@Nat.cast Real Real.instNatCast 190830)

noncomputable def ep416 := @Enclosure.Real.IsNear.subLit_ff_p qz333 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz586 qz587)) 884279719003555 562949953421312 1 2000000000000000 46582 524288 1 260982 437393910586664288256 834262677357987 562949953421312 1000000000130491 260982000000000000000 qz334 (ep415 rfl) rfl rfl

noncomputable abbrev qz588 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 190830) (@Nat.cast Real Real.instNatCast 17000)))

noncomputable def ep417 := @Enclosure.Complex.IsNear.re_isNear qz36 Bool.false 34849220663983773 9007199254740992 500000001435401 260982000000000000000 Bool.false 834262677357987 562949953421312 1000000000130491 260982000000000000000 (ep409 (@congrArg Complex Complex qz5 qz260 Complex.log (BSN.w_shift_mk qz11 Bool.false 95415 1000 4 (@Eq.refl Real qz11) rfl)) (@Enclosure.Complex.IsNear.of_parts (Complex.log qz260) Bool.false 34849220663983773 9007199254740992 500000001435401 260982000000000000000 Bool.false 834262677357987 562949953421312 1000000000130491 260982000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re (Complex.log qz260)) (@HMul.hMul Real Real Real qz0 qz323 (Real.log (Enclosure.sfrac Bool.false 36705088900 16000000))) Bool.false 34849220663983773 9007199254740992 500000001435401 260982000000000000000 (Enclosure.clog_re_eq 17000 190830 4000 36705088900 16000000 rfl rfl rfl) (ep414 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im (Complex.log qz260)) qz588 Bool.false 834262677357987 562949953421312 1000000000130491 260982000000000000000 (Enclosure.clog_im_eq 17000 190830 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz588 (@HSub.hSub Real Real Real qz326 qz333 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz586 qz587))) Bool.false 834262677357987 562949953421312 1000000000130491 260982000000000000000 (BSN.arctan_recip 190830 17000 rfl rfl) ep416))))

noncomputable def ep418 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz35) (Complex.im qz36) 190830 4000 0 1 834262677357987 562949953421312 1000000000130491 260982000000000000000

noncomputable def ep419 := @Enclosure.Complex.IsNear.im_isNear qz35 Bool.false 15000 4000 0 1 Bool.false 190830 4000 0 1

noncomputable def ep420 := @Enclosure.Complex.IsNear.im_isNear qz36 Bool.false 34849220663983773 9007199254740992 500000001435401 260982000000000000000 Bool.false 834262677357987 562949953421312 1000000000130491 260982000000000000000 (ep409 (@congrArg Complex Complex qz5 qz260 Complex.log (BSN.w_shift_mk qz11 Bool.false 95415 1000 4 (@Eq.refl Real qz11) rfl)) (@Enclosure.Complex.IsNear.of_parts (Complex.log qz260) Bool.false 34849220663983773 9007199254740992 500000001435401 260982000000000000000 Bool.false 834262677357987 562949953421312 1000000000130491 260982000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re (Complex.log qz260)) (@HMul.hMul Real Real Real qz0 qz323 (Real.log (Enclosure.sfrac Bool.false 36705088900 16000000))) Bool.false 34849220663983773 9007199254740992 500000001435401 260982000000000000000 (Enclosure.clog_re_eq 17000 190830 4000 36705088900 16000000 rfl rfl rfl) (ep414 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im (Complex.log qz260)) qz588 Bool.false 834262677357987 562949953421312 1000000000130491 260982000000000000000 (Enclosure.clog_im_eq 17000 190830 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz588 (@HSub.hSub Real Real Real qz326 qz333 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz586 qz587))) Bool.false 834262677357987 562949953421312 1000000000130491 260982000000000000000 (BSN.arctan_recip 190830 17000 rfl rfl) ep416))))

noncomputable abbrev qz335 := (@ep408 1 (BSN.w_sub_half_mk qz11 Bool.false 95415 1000 4 (@Eq.refl Real qz11) rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 15000 4000) (Enclosure.sfrac Bool.false 190830 4000) Bool.false 15000 4000 0 1 Bool.false 190830 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 15000 4000) (Enclosure.Real.IsNear.const Bool.false 190830 4000)))

noncomputable def ep421 := @ep404 6361000000830053251 34797600000000000000000 ep405 50612480939095948809 900719925474099200 6611000001547753751 34797600000000000000000 (@ep406 522738309959756595 36028797018963968 500000001435401 69595200000000000000 (ep407 qz335) ep417 rfl) (@ep418 15920234672022465921 225179981368524800 6361000000830053251 34797600000000000000000 (ep419 qz335) ep420 rfl) rfl

noncomputable def ep422 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re qz35) (Complex.im qz36)) (@HMul.hMul Real Real Real qz0 (Complex.im qz35) (Complex.re qz36)) 12513940160369805 2251799813685248 1000000000130491 69595200000000000000 665027677930802340159 3602879701896396800

noncomputable def ep423 := nat_lit 1542595422254656333759700317274898432

noncomputable def ep424 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz35) (Complex.im qz36) 15000 4000 0 1 834262677357987 562949953421312 1000000000130491 260982000000000000000

noncomputable def ep425 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz35) (Complex.re qz36) 190830 4000 0 1 34849220663983773 9007199254740992 500000001435401 260982000000000000000

noncomputable def ep426 := @ep422 3180500009130585761 34797600000000000000000 ep423 685049982187394028159 3602879701896396800 3680500009195831261 34797600000000000000000 (@ep424 12513940160369805 2251799813685248 1000000000130491 69595200000000000000 (ep407 qz335) ep420 rfl) (@ep425 665027677930802340159 3602879701896396800 3180500009130585761 34797600000000000000000 (ep419 qz335) ep417 rfl) rfl

noncomputable def ep427 := ep402 (@ep403 34797600000000000000000 (ep421 rfl) (ep426 rfl)) qz13 rfl rfl rfl rfl rfl rfl

noncomputable def ep428 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re qz26) (Complex.re ↑qz253)) (@HMul.hMul Real Real Real qz0 (Complex.im qz26) (Complex.im ↑qz253)) 120447 131072 1 262144 0 1 0 1 120447 120447

noncomputable def ep429 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz26) (Complex.re ↑qz253) 1 2 0 1 120447 65536 1 131072 120447 131072 1 262144

noncomputable abbrev qz336 := (@Enclosure.Complex.IsNear.of_eq qz26 (Complex.mk (Enclosure.sfrac Bool.false 1 2) qz553) Bool.false 1 2 0 1 Bool.false 0 1 0 1 BSN.half_c_mk (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 2) qz553 Bool.false 1 2 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 2) qz823))

noncomputable def ep430 := ep429 (@Enclosure.Complex.IsNear.re_isNear qz26 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz336) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz253) qz253 Bool.false 120447 65536 1 131072 (Complex.ofReal_re qz253) EMRow28.d4)

noncomputable def ep431 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz26) (Complex.im ↑qz253) 0 1 0 1 0 1 0 1 0 1 0 1

noncomputable def ep432 := ep431 (@Enclosure.Complex.IsNear.im_isNear qz26 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz336) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz253) qz265 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz253) (0 : Real) qz265 (Complex.ofReal_im qz253) Enclosure.sfrac_zero_eq) qz277)

noncomputable def ep433 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re qz26) (Complex.im ↑qz253)) (@HMul.hMul Real Real Real qz0 (Complex.im qz26) (Complex.re ↑qz253)) 0 1 0 1 0 1 0 1 0 0

noncomputable def ep434 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz26) (Complex.im ↑qz253) 1 2 0 1 0 1 0 1 0 1 0 1

noncomputable def ep435 := ep434 (@Enclosure.Complex.IsNear.re_isNear qz26 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz336) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz253) qz265 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz253) (0 : Real) qz265 (Complex.ofReal_im qz253) Enclosure.sfrac_zero_eq) qz277)

noncomputable def ep436 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz26) (Complex.re ↑qz253) 0 1 0 1 120447 65536 1 131072 0 1 0 1

noncomputable def ep437 := ep436 (@Enclosure.Complex.IsNear.im_isNear qz26 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz336) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz253) qz253 Bool.false 120447 65536 1 131072 (Complex.ofReal_re qz253) EMRow28.d4)

noncomputable def ep438 := @ep399 3680500009195831261 34797600000000000000000 (ep427 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz26 (↑qz253) Bool.false 120447 131072 1 262144 Bool.false 0 1 0 1 (@ep428 131072 1 262144 (ep430 rfl) (ep432 rfl) rfl rfl) (@ep433 1 0 1 (ep435 rfl) (ep437 rfl) rfl rfl))

noncomputable abbrev qz37 := (@HMul.hMul Nat Nat Nat qz869 2 2)

noncomputable abbrev qz38 := (@HMul.hMul Complex Complex Complex qz255 (@HMul.hMul Complex Complex Complex qz255 (2 : Complex) qz552) (@HSub.hSub Complex Complex Complex qz580 (@HMul.hMul Complex Complex Complex qz255 (2 : Complex) qz552) (1 : Complex)))

noncomputable abbrev qz39 := (@HPow.hPow Complex Int Complex qz583 qz257 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) qz332 (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) qz584 (@Nat.cast Int instNatCastInt 2))))

noncomputable def ep439 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz22 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz29 qz5 (@HSub.hSub Int Int Int qz30 qz31 (@HMul.hMul Int Int Int qz32 qz33 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz15 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz22 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz29 qz5 (@HSub.hSub Int Int Int qz30 qz31 (@HMul.hMul Int Int Int qz32 qz33 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz37)) qz38) qz39)) Bool.false 21359996313975415843 138350580552821637120000 342273729475339 ep392

noncomputable def ep440 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz22 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz29 qz5 (@HSub.hSub Int Int Int qz30 qz31 (@HMul.hMul Int Int Int qz32 qz33 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz37)) qz38) qz39) Bool.false 15913751 103079215104 17 103079215104 Bool.true

noncomputable def ep441 := nat_lit 733923884889639670349482164224

noncomputable def ep442 := nat_lit 27460906877746871614991694718566400

noncomputable def ep443 := @ep440 5954551183 3435973836800 6361 3435973836800 Bool.false 307094066045281 46116860184273879040000 18523075339 ep392 Bool.true 112469161252133673 ep369 753759181643 ep393 Bool.false ep441 21359996313975415843 138350580552821637120000 342273729475339 ep392 Bool.true ep442 7992175779580974373673 ep369 42688702149581643

noncomputable abbrev qz40 := (@HMul.hMul Nat Nat Nat qz869 2 1)

noncomputable abbrev qz41 := (@HMul.hMul Complex Complex Complex qz255 (@HMul.hMul Complex Complex Complex qz255 (2 : Complex) qz575) (@HSub.hSub Complex Complex Complex qz580 (@HMul.hMul Complex Complex Complex qz255 (2 : Complex) qz575) (1 : Complex)))

noncomputable abbrev qz42 := (@HPow.hPow Complex Int Complex qz583 qz257 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) qz332 (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) qz584 (@Nat.cast Int instNatCastInt 1))))

noncomputable def ep444 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz22 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz29 qz5 (@HSub.hSub Int Int Int qz30 qz31 (@HMul.hMul Int Int Int qz32 qz33 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz15 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz22 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz29 qz5 (@HSub.hSub Int Int Int qz30 qz31 (@HMul.hMul Int Int Int qz32 qz33 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz40)) qz41) qz42)) Bool.false 15913751 103079215104 17 103079215104

noncomputable def ep445 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz22 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz29 qz5 (@HSub.hSub Int Int Int qz30 qz31 (@HMul.hMul Int Int Int qz32 qz33 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz40)) qz41) qz42) Bool.false 0 1 0 1 Bool.false

noncomputable def ep446 := @ep445 0 1 0 1 Bool.false 15913751 103079215104 17 103079215104 Bool.true 5954551183 3435973836800 6361 3435973836800 Bool.false 15913751 15913751 103079215104 17 103079215104 Bool.true 5954551183 5954551183 3435973836800 6361

noncomputable def ep447 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz22 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz29 qz5 (@HSub.hSub Int Int Int qz30 qz31 (@HMul.hMul Int Int Int qz32 qz33 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz265 qz265) Bool.false 0 1 0 1 Bool.false

noncomputable def ep448 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz40)) qz41) qz42 Bool.false 15913751 103079215104 17 103079215104 Bool.true 5954551183 3435973836800 6361 3435973836800

noncomputable def ep449 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz40)) qz41)) (Complex.re qz42)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz40)) qz41)) (Complex.im qz42)) 15913751 103079215104 17 103079215104 0 1 0

noncomputable def ep450 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz40)) qz41)) (Complex.re qz42) 1 12 0 1 15913751 8589934592 17 8589934592 15913751

noncomputable def ep451 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz40)) qz41) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz265) Bool.false 1 12 0 1 Bool.false 0 1 0 1

noncomputable abbrev qz589 := (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 12) qz265 Bool.false 1 12 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 12) qz277)

noncomputable def ep452 := @Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz40)) qz41) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep451 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz589)

noncomputable def ep453 := @Enclosure.Complex.IsNear.re_isNear qz42 Bool.false 15913751 8589934592 17 8589934592 Bool.true 17863653549 858993459200 19083 858993459200

noncomputable def ep454 := @Enclosure.Complex.IsNear.of_eq qz42 (@Inv.inv Complex Complex.instInv qz8) Bool.false 15913751 8589934592 17 8589934592 Bool.true 17863653549 858993459200 19083

noncomputable def ep455 := @Enclosure.Complex.IsNear.of_parts (@Inv.inv Complex Complex.instInv qz8) Bool.false 15913751 8589934592 17 8589934592 Bool.true 17863653549 858993459200 19083

noncomputable abbrev qz337 := (@MonoidWithZeroHom Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz338 := (@MonoidWithZeroHom.funLike Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable def ep456 := @Enclosure.Real.IsNear.mulLit_ff qz9 (@Inv.inv Real Real.instInv (@DFunLike.coe qz337 Complex (fun (x : Complex) => Real) qz338 Complex.normSq qz8)) 17000 4000 0 1 936103 2147483648 1 2147483648

noncomputable def ep457 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz337 Complex (fun (x : Complex) => Real) qz338 Complex.normSq qz8)) Bool.false 936103 2147483648 1 2147483648 936103 2147483648 1

noncomputable abbrev qz590 := (@instHAdd Real Real.instAdd)

noncomputable def ep458 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz337 Complex (fun (x : Complex) => Real) qz338 Complex.normSq qz8) (@HAdd.hAdd Real Real Real qz590 (@HMul.hMul Real Real Real qz0 qz9 qz9) (@HMul.hMul Real Real Real qz0 qz10 qz10)) Bool.false 367050889 160000 0 1

noncomputable def ep459 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz9 qz9) (@HMul.hMul Real Real Real qz0 qz10 qz10) 289 16 0 1 364160889 160000

noncomputable def ep460 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz9 17000 4000 0 1 17000 4000 0 1

noncomputable def ep461 := @Enclosure.Real.IsNear.mulLit_ff qz10 qz10 190830 4000 0 1 190830 4000 0 1

noncomputable def ep462 := @ep459 0 1 5872814224 367050889 160000 0 1 (@ep460 289 16 0 1 (ep32 qz12) (ep32 qz12) rfl) (@ep461 364160889 160000 0 1 (ep37 qz12) (ep37 qz12) rfl)

noncomputable def ep463 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz337 Complex (fun (x : Complex) => Real) qz338 Complex.normSq qz8) 367050889 160000 0 1 468051 468052 1073741824 (ep458 (Enclosure.Complex.normSq_eq_mul_add_mul qz8) (ep462 rfl rfl)) rfl

noncomputable def ep464 := @Enclosure.Real.IsNear.of_eq (Complex.re (@Inv.inv Complex Complex.instInv qz8)) (@HMul.hMul Real Real Real qz0 qz9 (@Inv.inv Real Real.instInv (@DFunLike.coe qz337 Complex (fun (x : Complex) => Real) qz338 Complex.normSq qz8))) Bool.false 15913751 8589934592 17 8589934592 (Enclosure.Complex.inv_re_eq_mul qz8) (@ep456 15913751 8589934592 17 8589934592 (ep32 qz12) (@ep457 2147483648 (ep463 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep465 := @Enclosure.Real.IsNear.of_eq (Complex.im (@Inv.inv Complex Complex.instInv qz8)) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz10) (@Inv.inv Real Real.instInv (@DFunLike.coe qz337 Complex (fun (x : Complex) => Real) qz338 Complex.normSq qz8))) Bool.true 17863653549 858993459200 19083 858993459200 (Enclosure.Complex.inv_im_eq_mul qz8)

noncomputable def ep466 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz10) (@Inv.inv Real Real.instInv (@DFunLike.coe qz337 Complex (fun (x : Complex) => Real) qz338 Complex.normSq qz8)) 190830 4000 0 1 936103 2147483648 1

noncomputable def ep467 := @ep466 2147483648 17863653549 858993459200 19083 858993459200 (@Enclosure.Real.IsNear.neg qz10 Bool.false 190830 4000 0 1 (ep37 qz12)) (@ep457 2147483648 (ep463 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep468 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz40)) qz41)) (Complex.im qz42) 0 1 0 1 17863653549 858993459200 19083 858993459200 0

noncomputable def ep469 := @Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz40)) qz41) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep451 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz589)

noncomputable def ep470 := @Enclosure.Complex.IsNear.im_isNear qz42 Bool.false 15913751 8589934592 17 8589934592 Bool.true 17863653549 858993459200 19083 858993459200

noncomputable abbrev qz591 := (@ep454 858993459200 (BSN.zpow_one_sub_two_mul qz5 1 1 rfl rfl) (@ep455 858993459200 ep464 (ep465 ep467)))

noncomputable def ep471 := @ep449 1 15913751 15913751 103079215104 17 103079215104 (@ep450 103079215104 17 103079215104 ep452 (ep453 qz591) rfl) (@ep468 1 0 1 ep469 (ep470 qz591) rfl) rfl

noncomputable def ep472 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz40)) qz41)) (Complex.im qz42)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz40)) qz41)) (Complex.re qz42)) 5954551183 3435973836800 6361 3435973836800 0 1 0

noncomputable def ep473 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz40)) qz41)) (Complex.im qz42) 1 12 0 1 17863653549 858993459200 19083 858993459200 5954551183

noncomputable def ep474 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz40)) qz41)) (Complex.re qz42) 0 1 0 1 15913751 8589934592 17 8589934592 0

noncomputable def ep475 := @ep472 1 5954551183 5954551183 3435973836800 6361 3435973836800 (@ep473 3435973836800 6361 3435973836800 ep452 (ep470 qz591) rfl) (@ep474 1 0 1 ep469 (ep453 qz591) rfl) rfl

noncomputable abbrev qz339 := (@Enclosure.Complex.IsNear.mk qz553 qz553 Bool.false 0 1 0 1 Bool.false 0 1 0 1 qz823 qz823)

noncomputable def ep476 := @ep446 3435973836800 (@ep447 0 1 0 1 (BSN.stirling_sum_base qz5) qz339) (ep448 (ep471 rfl) (ep475 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep477 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz37)) qz38) qz39 Bool.false 307094066045281 46116860184273879040000 18523075339 ep392 Bool.true 112469161252133673 ep369 753759181643 ep393

noncomputable def ep478 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz37)) qz38)) (Complex.re qz39)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz37)) qz38)) (Complex.im qz39)) 307094066045281 46116860184273879040000 18523075339 ep392 0 1 0

noncomputable def ep479 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz37)) qz38)) (Complex.re qz39) 1 360 0 1 2763846594407529 1152921504606846976000 18523075339 5764607523034234880000 307094066045281

noncomputable def ep480 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz37)) qz38) (Complex.mk (Enclosure.sfrac Bool.true 1 360) qz265) Bool.true 1 360 0 1 Bool.false 0 1 0 1

noncomputable def ep481 := @Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz37)) qz38) Bool.true 1 360 0 1 Bool.false 0 1 0 1 (ep480 (BSN.stirling_coeff_mk 2 1 30 Bool.true BSN.bern_real_2 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 1 360) qz265 Bool.true 1 360 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.true 1 360) qz277))

noncomputable def ep482 := @Enclosure.Complex.IsNear.re_isNear qz39 Bool.true 2763846594407529 1152921504606846976000 18523075339 5764607523034234880000 Bool.false 1012222451269203057 115292150460684697600000 6783832634787 576460752303423488000000

noncomputable def ep483 := @Enclosure.Complex.IsNear.of_eq qz39 (@Inv.inv Complex Complex.instInv qz2) Bool.true 2763846594407529 1152921504606846976000 18523075339 5764607523034234880000 Bool.false 1012222451269203057 115292150460684697600000 6783832634787

noncomputable def ep484 := @Enclosure.Complex.IsNear.of_parts (@Inv.inv Complex Complex.instInv qz2) Bool.true 2763846594407529 1152921504606846976000 18523075339 5764607523034234880000 Bool.false 1012222451269203057 115292150460684697600000 6783832634787

noncomputable abbrev qz43 := (Complex.re qz254)

noncomputable def ep485 := @Enclosure.Real.IsNear.mulLit_tf qz43 (@Inv.inv Real Real.instInv (@DFunLike.coe qz337 Complex (fun (x : Complex) => Real) qz338 Complex.normSq qz2)) 18523075339 640000 0 1 746055 9007199254740992 1 9007199254740992

noncomputable def ep486 := @Enclosure.Complex.IsNear.re_isNear qz2 Bool.true 18523075339 640000 0 1 Bool.true 6783832634787 64000000 0 1

noncomputable def ep487 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz337 Complex (fun (x : Complex) => Real) qz338 Complex.normSq qz2)) Bool.false 746055 9007199254740992 1 9007199254740992 746055 9007199254740992 1

noncomputable def ep488 := nat_lit 49451428416943830171745369

noncomputable abbrev qz44 := (Complex.im qz254)

noncomputable def ep489 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz337 Complex (fun (x : Complex) => Real) qz338 Complex.normSq qz2) (@HAdd.hAdd Real Real Real qz590 (@HMul.hMul Real Real Real qz0 qz43 qz43) (@HMul.hMul Real Real Real qz0 qz44 qz44)) Bool.false ep488 4096000000000000 0 1

noncomputable def ep490 := nat_lit 46020385216801130522535369

noncomputable def ep491 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz43 qz43) (@HMul.hMul Real Real Real qz0 qz44 qz44) 343104320014269964921 409600000000 0 1 ep490 4096000000000000

noncomputable def ep492 := nat_lit 20255305079580192838346903142400000000

noncomputable def ep493 := @Enclosure.Real.IsNear.mulLit_tt qz43 qz43 18523075339 640000 0 1 18523075339 640000 0 1

noncomputable def ep494 := @Enclosure.Real.IsNear.mulLit_tt qz44 qz44 6783832634787 64000000 0 1 6783832634787 64000000 0 1

noncomputable def ep495 := @Enclosure.Complex.IsNear.im_isNear qz2 Bool.true 18523075339 640000 0 1 Bool.true 6783832634787 64000000 0 1

noncomputable def ep496 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz337 Complex (fun (x : Complex) => Real) qz338 Complex.normSq qz2) ep488 4096000000000000 0 1 373027 373028 4503599627370496 (ep489 (Enclosure.Complex.normSq_eq_mul_add_mul qz2) (@ep491 0 1 ep492 ep488 4096000000000000 0 1 (@ep493 343104320014269964921 409600000000 0 1 (ep486 EMRow28.d5) (ep486 EMRow28.d5) rfl) (@ep494 ep490 4096000000000000 0 1 (ep495 EMRow28.d5) (ep495 EMRow28.d5) rfl) rfl rfl)) rfl

noncomputable def ep497 := @Enclosure.Real.IsNear.of_eq (Complex.re (@Inv.inv Complex Complex.instInv qz2)) (@HMul.hMul Real Real Real qz0 qz43 (@Inv.inv Real Real.instInv (@DFunLike.coe qz337 Complex (fun (x : Complex) => Real) qz338 Complex.normSq qz2))) Bool.true 2763846594407529 1152921504606846976000 18523075339 5764607523034234880000 (Enclosure.Complex.inv_re_eq_mul qz2) (@ep485 2763846594407529 1152921504606846976000 18523075339 5764607523034234880000 (ep486 EMRow28.d5) (@ep487 9007199254740992 (ep496 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep498 := @Enclosure.Real.IsNear.of_eq (Complex.im (@Inv.inv Complex Complex.instInv qz2)) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz44) (@Inv.inv Real Real.instInv (@DFunLike.coe qz337 Complex (fun (x : Complex) => Real) qz338 Complex.normSq qz2))) Bool.false 1012222451269203057 115292150460684697600000 6783832634787 576460752303423488000000 (Enclosure.Complex.inv_im_eq_mul qz2)

noncomputable def ep499 := @Enclosure.Real.IsNear.mulLit_ff (@Neg.neg Real Real.instNeg qz44) (@Inv.inv Real Real.instInv (@DFunLike.coe qz337 Complex (fun (x : Complex) => Real) qz338 Complex.normSq qz2)) 6783832634787 64000000 0 1 746055 9007199254740992 1

noncomputable def ep500 := @ep499 9007199254740992 1012222451269203057 115292150460684697600000 6783832634787 576460752303423488000000 (@Enclosure.Real.IsNear.neg qz44 Bool.true 6783832634787 64000000 0 1 (ep495 EMRow28.d5)) (@ep487 9007199254740992 (ep496 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep501 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz37)) qz38)) (Complex.im qz39) 0 1 0 1 1012222451269203057 115292150460684697600000 6783832634787 576460752303423488000000 0

noncomputable def ep502 := @Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz37)) qz38) Bool.true 1 360 0 1 Bool.false 0 1 0 1 (ep480 (BSN.stirling_coeff_mk 2 1 30 Bool.true BSN.bern_real_2 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 1 360) qz265 Bool.true 1 360 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.true 1 360) qz277))

noncomputable def ep503 := @Enclosure.Complex.IsNear.im_isNear qz39 Bool.true 2763846594407529 1152921504606846976000 18523075339 5764607523034234880000 Bool.false 1012222451269203057 115292150460684697600000 6783832634787 576460752303423488000000

noncomputable abbrev qz592 := (@ep483 576460752303423488000000 (BSN.zpow_one_sub_two_mul qz5 2 3 rfl rfl) (@ep484 576460752303423488000000 ep497 (ep498 ep500)))

noncomputable def ep504 := @ep478 1 307094066045281 307094066045281 46116860184273879040000 18523075339 ep392 (@ep479 46116860184273879040000 18523075339 ep392 ep481 (ep482 qz592) rfl) (@ep501 1 0 1 ep502 (ep503 qz592) rfl) rfl

noncomputable def ep505 := @Enclosure.Real.IsNear.addLit_tt (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz37)) qz38)) (Complex.im qz39)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz37)) qz38)) (Complex.re qz39)) 112469161252133673 ep369 753759181643 ep393 0 1 0

noncomputable def ep506 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz37)) qz38)) (Complex.im qz39) 1 360 0 1 1012222451269203057 115292150460684697600000 6783832634787 576460752303423488000000 112469161252133673

noncomputable def ep507 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz37)) qz38)) (Complex.re qz39) 0 1 0 1 2763846594407529 1152921504606846976000 18523075339 5764607523034234880000 0

noncomputable def ep508 := @ep505 1 112469161252133673 112469161252133673 ep369 753759181643 ep393 (@ep506 ep369 753759181643 ep393 ep481 (ep503 qz592) rfl) (@ep507 1 0 1 ep502 (ep482 qz592) rfl) rfl

noncomputable def ep509 := @ep443 ep393 (@ep444 Bool.true 5954551183 3435973836800 6361 3435973836800 (BSN.stirling_sum_succ qz5 0 1 rfl) (ep476 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep477 (ep504 rfl) (ep508 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep510 := @ep396 ep384 ep369 ep385 ep387 (ep438 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep439 Bool.true 7992175779580974373673 ep369 42688702149581643 ep393 (BSN.stirling_sum_succ qz5 1 2 rfl) (ep509 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep511 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz24 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz11 4) Bool.false 34822136600215197 2251799813685248 500000001435401 65245500000000000000 Bool.false 863650722645411 140737488355328

noncomputable abbrev qz872 := (@HAdd.hAdd Complex Complex Complex qz15 qz24 qz551)

noncomputable def ep512 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz11 4) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.logSumC qz11 3) (Complex.log qz872)) Bool.false 34822136600215197 2251799813685248 500000001435401 65245500000000000000 Bool.false 863650722645411 140737488355328 1000000000130491 65245500000000000000

noncomputable def ep513 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz11 3) (Complex.log qz872) Bool.false 104454074654571479 9007199254740992 500000001435401 86994000000000000000 Bool.false 2608613878763753 562949953421312 1000000000130491 86994000000000000000 Bool.false

noncomputable def ep514 := nat_lit 1254599691335789373206118789021696

noncomputable def ep515 := nat_lit 1944768536342066285499465596928

noncomputable abbrev qz873 := (@HAdd.hAdd Complex Complex Complex qz15 qz24 qz552)

noncomputable def ep516 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz11 3) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.logSumC qz11 2) (Complex.log qz873)) Bool.false 104454074654571479 9007199254740992 500000001435401 86994000000000000000 Bool.false 2608613878763753 562949953421312 1000000000130491 86994000000000000000

noncomputable def ep517 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz11 2) (Complex.log qz873) Bool.false 34815225997835933 4503599627370496 500000001435401 130491000000000000000 Bool.false 875432086373795 281474976710656 1000000000130491 130491000000000000000 Bool.false

noncomputable def ep518 := nat_lit 470419331691658083512458447683584

noncomputable def ep519 := nat_lit 734259530772121389971661651968

noncomputable abbrev qz874 := (@HAdd.hAdd Complex Complex Complex qz15 qz24 qz575)

noncomputable def ep520 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz11 2) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.logSumC qz11 1) (Complex.log qz874)) Bool.false 34815225997835933 4503599627370496 500000001435401 130491000000000000000 Bool.false 875432086373795 281474976710656 1000000000130491 130491000000000000000

noncomputable def ep521 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz11 1) (Complex.log qz874) Bool.false 34813744234118813 9007199254740992 500000001435401 260982000000000000000 Bool.false 881330150213027 562949953421312 1000000000130491 260982000000000000000 Bool.false

noncomputable def ep522 := nat_lit 627175355322694050549164851331072

noncomputable def ep523 := nat_lit 985648904495299757711902638080

noncomputable abbrev qz875 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz24 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep524 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz11 1) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.logSumC qz11 0) qz875) Bool.false 34813744234118813 9007199254740992 500000001435401 260982000000000000000 Bool.false 881330150213027 562949953421312 1000000000130491 260982000000000000000

noncomputable def ep525 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz11 0) qz875 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz593 := (Enclosure.sfrac Bool.false 1000 4000)

noncomputable def ep526 := @Enclosure.Complex.IsNear.of_eq qz875 (Complex.log (Complex.mk qz593 qz261)) Bool.false 34813744234118813 9007199254740992 500000001435401 260982000000000000000 Bool.false 881330150213027 562949953421312 1000000000130491 260982000000000000000

noncomputable def ep527 := BSN.log_dyadic_bound 3649088900 69185088900 2 1 14359729578302709630000 524288 260982 13315849800103210000 13315849800103210000 55357 72834177800 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 3649088900) (BSN.artanhQ 69185088900) 0 1 13315849800103210000 14359729578302709630000 13315849800103210000 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep528 := @Enclosure.Real.IsNear.mulLit_ff qz323 (Real.log (Enclosure.sfrac Bool.false 36417088900 16000000)) 1 2 0 1 34813744234118813 4503599627370496 500000001435401 130491000000000000000 34813744234118813 9007199254740992 500000001435401 260982000000000000000 qz324 (BSN.isNear_log_sfrac 36417088900 16000000 34813744234118813 4503599627370496 500000001435401 130491000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 36417088900) qz585)) Bool.false 146019426696141473841152 18889465931478580854784 1000000002870802 260982000000000000000 34813744234118813 4503599627370496 500000001435401 130491000000000000000 (BSN.log_rat_reduce_isNear 36417088900 16000000 11 72834177800 65536000000 55357 524288 24973259072661432 36028797018963968 260982 1000000000000000 rfl rfl rfl rfl (ep527 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep529 := BSN.arctan_dyadic_bound_f 1000 190830 1 0 524288 260982 0 1 1 0 1 1 2747 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 190830) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 190830) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz876 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable def ep530 := @Enclosure.Real.IsNear.subLit_ff_p qz333 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz876 qz587)) 884279719003555 562949953421312 1 2000000000000000 2747 524288 1 260982 462070821794887499776 881330150213027 562949953421312 1000000000130491 260982000000000000000 qz334 (ep529 rfl) rfl rfl

noncomputable abbrev qz877 := (@HAdd.hAdd Complex Complex Complex qz15 qz24 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable def ep531 := @ep525 34813744234118813 9007199254740992 500000001435401 260982000000000000000 Bool.false 881330150213027 562949953421312 1000000000130491 260982000000000000000 Bool.false 34813744234118813 34813744234118813 9007199254740992 500000001435401 260982000000000000000 Bool.false 881330150213027 881330150213027 562949953421312 1000000000130491 260982000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz11 0) (Complex.mk qz265 qz265) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz11) qz339) (ep526 (@congrArg Complex Complex qz877 (Complex.mk qz593 qz261) Complex.log (BSN.w_shift_mk qz11 Bool.false 95415 1000 0 (@Eq.refl Real qz11) rfl)) (@Enclosure.Complex.IsNear.of_parts (Complex.log (Complex.mk qz593 qz261)) Bool.false 34813744234118813 9007199254740992 500000001435401 260982000000000000000 Bool.false 881330150213027 562949953421312 1000000000130491 260982000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re (Complex.log (Complex.mk qz593 qz261))) (@HMul.hMul Real Real Real qz0 qz323 (Real.log (Enclosure.sfrac Bool.false 36417088900 16000000))) Bool.false 34813744234118813 9007199254740992 500000001435401 260982000000000000000 (Enclosure.clog_re_eq 1000 190830 4000 36417088900 16000000 rfl rfl rfl) (ep528 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im (Complex.log (Complex.mk qz593 qz261))) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz587 qz876)) Bool.false 881330150213027 562949953421312 1000000000130491 260982000000000000000 (Enclosure.clog_im_eq 1000 190830 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz587 qz876)) (@HSub.hSub Real Real Real qz326 qz333 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz876 qz587))) Bool.false 881330150213027 562949953421312 1000000000130491 260982000000000000000 (BSN.arctan_recip 190830 1000 rfl rfl) ep530)))) rfl rfl

noncomputable abbrev qz594 := (Enclosure.sfrac Bool.false 5000 4000)

noncomputable def ep532 := @Enclosure.Complex.IsNear.of_eq (Complex.log qz874) (Complex.log (Complex.mk qz594 qz261)) Bool.false 34816707761553053 9007199254740992 500000001435401 260982000000000000000 Bool.false 869534022534563 562949953421312 1000000000130491 260982000000000000000

noncomputable def ep533 := BSN.log_dyadic_bound 3673088900 69209088900 2 1 14369693959104309630000 524288 260982 13491582067303210000 13491582067303210000 55702 72882177800 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 3673088900) (BSN.artanhQ 69209088900) 0 1 13491582067303210000 14369693959104309630000 13491582067303210000 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep534 := @Enclosure.Real.IsNear.mulLit_ff qz323 (Real.log (Enclosure.sfrac Bool.false 36441088900 16000000)) 1 2 0 1 34816707761553053 4503599627370496 500000001435401 130491000000000000000 34816707761553053 9007199254740992 500000001435401 260982000000000000000 qz324 (BSN.isNear_log_sfrac 36441088900 16000000 34816707761553053 4503599627370496 500000001435401 130491000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 36441088900) qz585)) Bool.false 146031856631113016410112 18889465931478580854784 1000000002870802 260982000000000000000 34816707761553053 4503599627370496 500000001435401 130491000000000000000 (BSN.log_rat_reduce_isNear 36441088900 16000000 11 72882177800 65536000000 55702 524288 24973259072661432 36028797018963968 260982 1000000000000000 rfl rfl rfl rfl (ep533 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep535 := BSN.arctan_dyadic_bound_f 5000 190830 1 0 524288 260982 0 1 1 0 1 1 13733 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 190830) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 190830) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz878 := (@Nat.cast Real Real.instNatCast 5000)

noncomputable def ep536 := @Enclosure.Real.IsNear.subLit_ff_p qz333 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz878 qz587)) 884279719003555 562949953421312 1 2000000000000000 13733 524288 1 260982 455886253606600966144 869534022534563 562949953421312 1000000000130491 260982000000000000000 qz334 (ep535 rfl) rfl rfl

noncomputable def ep537 := @ep521 34816707761553053 9007199254740992 500000001435401 260982000000000000000 Bool.false 869534022534563 562949953421312 1000000000130491 260982000000000000000 Bool.false ep522 34815225997835933 4503599627370496 500000001435401 130491000000000000000 Bool.false ep523 875432086373795 281474976710656 1000000000130491 130491000000000000000 (ep524 (BSN.log_sum_c_succ qz11 0 1 rfl) (ep531 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep532 (@congrArg Complex Complex qz874 (Complex.mk qz594 qz261) Complex.log (BSN.w_shift_mk qz11 Bool.false 95415 1000 1 (@Eq.refl Real qz11) rfl)) (@Enclosure.Complex.IsNear.of_parts (Complex.log (Complex.mk qz594 qz261)) Bool.false 34816707761553053 9007199254740992 500000001435401 260982000000000000000 Bool.false 869534022534563 562949953421312 1000000000130491 260982000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re (Complex.log (Complex.mk qz594 qz261))) (@HMul.hMul Real Real Real qz0 qz323 (Real.log (Enclosure.sfrac Bool.false 36441088900 16000000))) Bool.false 34816707761553053 9007199254740992 500000001435401 260982000000000000000 (Enclosure.clog_re_eq 5000 190830 4000 36441088900 16000000 rfl rfl rfl) (ep534 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im (Complex.log (Complex.mk qz594 qz261))) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz587 qz878)) Bool.false 869534022534563 562949953421312 1000000000130491 260982000000000000000 (Enclosure.clog_im_eq 5000 190830 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz587 qz878)) (@HSub.hSub Real Real Real qz326 qz333 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz878 qz587))) Bool.false 869534022534563 562949953421312 1000000000130491 260982000000000000000 (BSN.arctan_recip 190830 5000 rfl rfl) ep536)))) rfl rfl

noncomputable abbrev qz595 := (Enclosure.sfrac Bool.false 9000 4000)

noncomputable def ep538 := @Enclosure.Complex.IsNear.of_eq (Complex.log qz873) (Complex.log (Complex.mk qz595 qz261)) Bool.false 34823622658899613 9007199254740992 500000001435401 260982000000000000000 Bool.false 857749706016163 562949953421312 1000000000130491 260982000000000000000

noncomputable def ep539 := BSN.log_dyadic_bound 3729088900 69265088900 2 1 14392957620974709630000 524288 260982 13906104024103210000 13906104024103210000 56507 72994177800 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 3729088900) (BSN.artanhQ 69265088900) 0 1 13906104024103210000 14392957620974709630000 13906104024103210000 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep540 := @Enclosure.Real.IsNear.mulLit_ff qz323 (Real.log (Enclosure.sfrac Bool.false 36497088900 16000000)) 1 2 0 1 34823622658899613 4503599627370496 500000001435401 130491000000000000000 34823622658899613 9007199254740992 500000001435401 260982000000000000000 qz324 (BSN.isNear_log_sfrac 36497088900 16000000 34823622658899613 4503599627370496 500000001435401 130491000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 36497088900) qz585)) Bool.false 146060859812713282404352 18889465931478580854784 1000000002870802 260982000000000000000 34823622658899613 4503599627370496 500000001435401 130491000000000000000 (BSN.log_rat_reduce_isNear 36497088900 16000000 11 72994177800 65536000000 56507 524288 24973259072661432 36028797018963968 260982 1000000000000000 rfl rfl rfl rfl (ep539 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep541 := BSN.arctan_dyadic_bound_f 9000 190830 1 0 524288 260982 0 1 1 0 1 1 24708 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 190830) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 190830) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz879 := (@Nat.cast Real Real.instNatCast 9000)

noncomputable def ep542 := @Enclosure.Real.IsNear.subLit_ff_p qz333 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz879 qz587)) 884279719003555 562949953421312 1 2000000000000000 24708 524288 1 260982 449707877867802066944 857749706016163 562949953421312 1000000000130491 260982000000000000000 qz334 (ep541 rfl) rfl rfl

noncomputable def ep543 := @ep517 34823622658899613 9007199254740992 500000001435401 260982000000000000000 Bool.false 857749706016163 562949953421312 1000000000130491 260982000000000000000 Bool.false ep518 104454074654571479 9007199254740992 500000001435401 86994000000000000000 Bool.false ep519 2608613878763753 562949953421312 1000000000130491 86994000000000000000 (ep520 (BSN.log_sum_c_succ qz11 1 2 rfl) (ep537 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep538 (@congrArg Complex Complex qz873 (Complex.mk qz595 qz261) Complex.log (BSN.w_shift_mk qz11 Bool.false 95415 1000 2 (@Eq.refl Real qz11) rfl)) (@Enclosure.Complex.IsNear.of_parts (Complex.log (Complex.mk qz595 qz261)) Bool.false 34823622658899613 9007199254740992 500000001435401 260982000000000000000 Bool.false 857749706016163 562949953421312 1000000000130491 260982000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re (Complex.log (Complex.mk qz595 qz261))) (@HMul.hMul Real Real Real qz0 qz323 (Real.log (Enclosure.sfrac Bool.false 36497088900 16000000))) Bool.false 34823622658899613 9007199254740992 500000001435401 260982000000000000000 (Enclosure.clog_re_eq 9000 190830 4000 36497088900 16000000 rfl rfl rfl) (ep540 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im (Complex.log (Complex.mk qz595 qz261))) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz587 qz879)) Bool.false 857749706016163 562949953421312 1000000000130491 260982000000000000000 (Enclosure.clog_im_eq 9000 190830 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz587 qz879)) (@HSub.hSub Real Real Real qz326 qz333 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz879 qz587))) Bool.false 857749706016163 562949953421312 1000000000130491 260982000000000000000 (BSN.arctan_recip 190830 9000 rfl rfl) ep542)))) rfl rfl

noncomputable abbrev qz596 := (Enclosure.sfrac Bool.false 13000 4000)

noncomputable def ep544 := @Enclosure.Complex.IsNear.of_eq (Complex.log qz872) (Complex.log (Complex.mk qz596 qz261)) Bool.false 34834471746289309 9007199254740992 500000001435401 260982000000000000000 Bool.false 845989011817891 562949953421312 1000000000130491 260982000000000000000

noncomputable def ep545 := nat_lit 347019990971142435529317874586344561500000000

noncomputable def ep546 := nat_lit 351038542685386520059200984802432800000000

noncomputable def ep547 := nat_lit 636869357839730811140083860912300000000

noncomputable def ep548 := BSN.log_dyadic_bound 3817088900 69353088900 3 2 ep545 524288 260982 ep546 ep547 57770 73170177800 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 3817088900) (BSN.artanhQ 69353088900) 0 2 ep546 ep545 ep547 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep549 := @Enclosure.Real.IsNear.mulLit_ff qz323 (Real.log (Enclosure.sfrac Bool.false 36585088900 16000000)) 1 2 0 1 34834471746289309 4503599627370496 500000001435401 130491000000000000000 34834471746289309 9007199254740992 500000001435401 260982000000000000000 qz324 (BSN.isNear_log_sfrac 36585088900 16000000 34834471746289309 4503599627370496 500000001435401 130491000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 36585088900) qz585)) Bool.false 146106364183348233895936 18889465931478580854784 1000000002870802 260982000000000000000 34834471746289309 4503599627370496 500000001435401 130491000000000000000 (BSN.log_rat_reduce_isNear 36585088900 16000000 11 73170177800 65536000000 57770 524288 24973259072661432 36028797018963968 260982 1000000000000000 rfl rfl rfl rfl (ep548 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep550 := BSN.arctan_dyadic_bound_f 13000 190830 1 0 524288 260982 0 1 1 0 1 1 35661 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 13000) (BSN.arctanEvenQ 190830) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 13000) (BSN.arctanOddQ 190830) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz880 := (@Nat.cast Real Real.instNatCast 13000)

noncomputable def ep551 := @Enclosure.Real.IsNear.subLit_ff_p qz333 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz880 qz587)) 884279719003555 562949953421312 1 2000000000000000 35661 524288 1 260982 443541887027978436608 845989011817891 562949953421312 1000000000130491 260982000000000000000 qz334 (ep550 rfl) rfl rfl

noncomputable def ep552 := @ep513 34834471746289309 9007199254740992 500000001435401 260982000000000000000 Bool.false 845989011817891 562949953421312 1000000000130491 260982000000000000000 Bool.false ep514 34822136600215197 2251799813685248 500000001435401 65245500000000000000 Bool.false ep515 863650722645411 140737488355328 1000000000130491 65245500000000000000 (ep516 (BSN.log_sum_c_succ qz11 2 3 rfl) (ep543 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep544 (@congrArg Complex Complex qz872 (Complex.mk qz596 qz261) Complex.log (BSN.w_shift_mk qz11 Bool.false 95415 1000 3 (@Eq.refl Real qz11) rfl)) (@Enclosure.Complex.IsNear.of_parts (Complex.log (Complex.mk qz596 qz261)) Bool.false 34834471746289309 9007199254740992 500000001435401 260982000000000000000 Bool.false 845989011817891 562949953421312 1000000000130491 260982000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re (Complex.log (Complex.mk qz596 qz261))) (@HMul.hMul Real Real Real qz0 qz323 (Real.log (Enclosure.sfrac Bool.false 36585088900 16000000))) Bool.false 34834471746289309 9007199254740992 500000001435401 260982000000000000000 (Enclosure.clog_re_eq 13000 190830 4000 36585088900 16000000 rfl rfl rfl) (ep549 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im (Complex.log (Complex.mk qz596 qz261))) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz587 qz880)) Bool.false 845989011817891 562949953421312 1000000000130491 260982000000000000000 (Enclosure.clog_im_eq 13000 190830 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz587 qz880)) (@HSub.hSub Real Real Real qz326 qz333 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz880 qz587))) Bool.false 845989011817891 562949953421312 1000000000130491 260982000000000000000 (BSN.arctan_recip 190830 13000 rfl rfl) ep551)))) rfl rfl

noncomputable def ep553 := @ep386 ep387 Bool.false 34822136600215197 2251799813685248 500000001435401 65245500000000000000 Bool.false 863650722645411 140737488355328 1000000000130491 65245500000000000000 Bool.true ep388 ep377 138350580552821637120000 ep378 ep379 Bool.false ep389 ep373 ep369 ep374 ep371 (@ep390 138350580552821637120000 ep382 ep383 Bool.false ep384 ep369 ep385 ep387 (BSN.logGammaStirling_unfold 2 qz5) (ep510 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep511 1000000000130491 65245500000000000000 (BSN.log_sum_c_eq qz11 4) (ep512 (BSN.log_sum_c_succ qz11 3 4 rfl) (ep552 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable def ep554 := @Enclosure.Real.IsNear.mulLit_ff (@HDiv.hDiv Real Real Real qz1 qz11 (2 : Real)) (Real.log Real.pi) 95415 2000 0 1 75021 65536 1 131072 1431625743 26214400 19083 52428800 (@Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real qz1 qz11 (2 : Real)) (Enclosure.sfrac Bool.false 95415 2000) Bool.false 95415 2000 0 1 (BSN.t_half_eq qz11 Bool.false 95415 1000 (@Eq.refl Real qz11)) (Enclosure.Real.IsNear.const Bool.false 95415 2000)) EMRow28.d6 rfl

noncomputable def ep555 := @ep375 19083 52428800 ep376 ep368 ep369 ep370 ep371 (@ep380 ep374 ep371 (ep553 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep554 rfl rfl

noncomputable def ep556 := BSN.cos_dyadic_bound_f 136072 1073741824 1 0 524288 261237 0 1 1 0 1 1 524287 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 136072) qz269 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 136072) qz270 0 0 rfl) rfl rfl

noncomputable def ep557 := @ep367 2048 Bool.false 524287 524288 1 130491 (@ep372 42824649 524288 1 2048 ep555 rfl) (Enclosure.sfrac_false_div 42824649 524288) (BSN.cos_reduce0 qz868 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9575258463139790848) qz282) 226375608064910080 72057594037927936 Bool.false 524287 524288 13 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q0 42824649 524288 226375608064910080 72057594037927936 13 9575258463139790848 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 524287 524288 9575258463139790848 75557863725914323419136 136072 1073741824 261237 260982 (ep556 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep558 := nat_lit 317109834120666188361718481441

noncomputable def ep559 := nat_lit 98404792799974935641456640000000

noncomputable def ep560 := nat_lit 1901726993414613818680319455508060137

noncomputable def ep561 := nat_lit 346705375066061291823311597076480000000

noncomputable abbrev qz881 := (@Nat.cast Complex Complex.instNatCast 24)

noncomputable abbrev qz45 := (@HPow.hPow Complex Complex Complex qz816 qz881 (@Neg.neg Complex Complex.instNeg qz262))

noncomputable abbrev qz46 := (@HAdd.hAdd Complex Complex Complex qz263 (@HDiv.hDiv Complex Complex Complex qz331 qz881 (@HSub.hSub Complex Complex Complex qz580 qz262 (1 : Complex))) qz330)

noncomputable abbrev qz47 := (@instHSub Nat instSubNat)

noncomputable abbrev qz48 := qz256

noncomputable abbrev qz49 := qz881

noncomputable def ep562 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz14 2 24) (@HAdd.hAdd Complex Complex Complex qz15 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 24, @HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast n) qz17) (@HMul.hMul Complex Complex Complex qz3 qz45 (@HAdd.hAdd Complex Complex Complex qz15 qz46 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz49 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1))))))) Bool.false ep362 ep363 ep364

noncomputable def ep563 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 24, @HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast n) qz17) (@HMul.hMul Complex Complex Complex qz3 qz45 (@HAdd.hAdd Complex Complex Complex qz15 qz46 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz49 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))))) Bool.false 31213327361 68719476736 2014306409105 373636384948224

noncomputable def ep564 := nat_lit 1581004040216126072117204150209

noncomputable def ep565 := nat_lit 416430738691342305388571533230853

noncomputable def ep566 := nat_lit 10344756806864478033006601518559

noncomputable def ep567 := nat_lit 35603611121780126102561534228060137

noncomputable def ep568 := nat_lit 1951570377295350159287916845189926249037824

noncomputable def ep569 := nat_lit 43583243737223878295889814276732094513152

noncomputable def ep570 := @ep563 Bool.false 14891101861 137438953472 16088624972587 2989091079585792 Bool.false ep564 ep363 ep565 ep365 Bool.true ep566 ep559 ep567 ep561 Bool.false ep568 ep362 ep363 ep364 ep365 Bool.false ep569 ep558 ep559

noncomputable def ep571 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 24, @HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast n) qz17) (BSN.headSumC qz14 24) Bool.false 31213327361 68719476736 2014306409105 373636384948224 Bool.false 14891101861 137438953472 16088624972587

noncomputable abbrev qz882 := (@HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast 23) qz17)

noncomputable def ep572 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 24) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz14 23) qz882) Bool.false 31213327361 68719476736 2014306409105 373636384948224 Bool.false 14891101861 137438953472 16088624972587 2989091079585792

noncomputable def ep573 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz14 23) qz882 Bool.false 167879322019 274877906944 187786774818851 35869092955029504 Bool.true 8083857653 274877906944 187483018391015 35869092955029504 Bool.true

noncomputable abbrev qz883 := (@HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast 22) qz17)

noncomputable def ep574 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 23) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz14 22) qz883) Bool.false 167879322019 274877906944 187786774818851 35869092955029504 Bool.true 8083857653 274877906944 187483018391015 35869092955029504

noncomputable def ep575 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz14 22) qz883 Bool.false 113415674943 274877906944 182063455901087 35869092955029504 Bool.true 29721365799 274877906944 181798020765221 35869092955029504 Bool.false

noncomputable abbrev qz884 := (@HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast 21) qz17)

noncomputable def ep576 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 22) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz14 21) qz884) Bool.false 113415674943 274877906944 182063455901087 35869092955029504 Bool.true 29721365799 274877906944 181798020765221 35869092955029504

noncomputable def ep577 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz14 21) qz884 Bool.false 53579380571 137438953472 88124243847179 17934546477514752 Bool.false 7483643961 68719476736 87961073725067 17934546477514752 Bool.false

noncomputable abbrev qz885 := (@HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast 20) qz17)

noncomputable def ep578 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 21) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz14 20) qz885) Bool.false 53579380571 137438953472 88124243847179 17934546477514752 Bool.false 7483643961 68719476736 87961073725067 17934546477514752

noncomputable def ep579 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz14 20) qz885 Bool.false 42138624043 68719476736 14185738406951 2989091079585792 Bool.false 16423698327 137438953472 1770496003495 373636384948224 Bool.true

noncomputable abbrev qz886 := (@HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast 19) qz17)

noncomputable def ep580 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 20) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz14 19) qz886) Bool.false 42138624043 68719476736 14185738406951 2989091079585792 Bool.false 16423698327 137438953472 1770496003495 373636384948224

noncomputable def ep581 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz14 19) qz886 Bool.false 182874793633 274877906944 164107512265003 35869092955029504 Bool.true 7141464489 68719476736 81897588222695 17934546477514752 Bool.true

noncomputable abbrev qz887 := (@HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast 18) qz17)

noncomputable def ep582 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 19) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz14 18) qz887) Bool.false 182874793633 274877906944 164107512265003 35869092955029504 Bool.true 7141464489 68719476736 81897588222695 17934546477514752

noncomputable def ep583 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz14 18) qz887 Bool.false 132308892233 274877906944 157797113544499 35869092955029504 Bool.true 69071147881 274877906944 157495401388669 35869092955029504 Bool.false

noncomputable abbrev qz888 := (@HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast 17) qz17)

noncomputable def ep584 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 18) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz14 17) qz888) Bool.false 132308892233 274877906944 157797113544499 35869092955029504 Bool.true 69071147881 274877906944 157495401388669 35869092955029504

noncomputable def ep585 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz14 17) qz888 Bool.false 8303683425 34359738368 25215172822777 5978182159171584 Bool.true 7356088589 34359738368 1573400418433 373636384948224 Bool.false

noncomputable abbrev qz889 := (@Nat.cast Real Real.instNatCast 17)

noncomputable abbrev qz340 := (@Inv.inv Real Real.instInv (Real.sqrt qz889))

noncomputable abbrev qz341 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 17 1)))

noncomputable def ep586 := @Enclosure.Complex.IsNear.of_eq qz888 (Complex.mk (@HMul.hMul Real Real Real qz0 qz340 (Real.cos qz341)) (@HMul.hMul Real Real Real qz0 qz340 (@Neg.neg Real Real.instNeg (Real.sin qz341)))) Bool.false 65879424833 274877906944 6506076607837 35869092955029504 Bool.true 10222439169 274877906944 6448961219101 35869092955029504 (BSN.cpow_neg_s_mk qz11 95415 1000 17 (@Eq.refl Real qz11) rfl)

noncomputable abbrev qz890 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 17) qz268)

noncomputable def ep587 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz889) 2161695 524288 1 524288 63579 63580 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz889) (Real.sqrt qz890) Bool.false 2161695 524288 1 524288 (BSN.sqrt_natCast_div_one 17) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz890) Bool.false 2161695 524288 1 524288 2161695 524288 1 524288 (BSN.sqrt_enclosure 17 1 1080847 1080848 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep588 := BSN.log_dyadic_bound 1 33 2 1 3267 262144 130491 1 1 15892 34 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1) (BSN.artanhQ 33) 0 1 1 3267 1 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz342 := (Real.log (Enclosure.sfrac Bool.false 17 1))

noncomputable def ep589 := @Enclosure.Real.IsNear.mulLit_ff qz11 qz342 95415 1000 0 1 3189913004350711 1125899906842624 250000000130491 32622750000000000000 60873109862024618013 225179981368524800 1590250000830053251 2174850000000000000000 qz273 (BSN.isNear_log_sfrac 17 1 3189913004350711 1125899906842624 250000000130491 32622750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz890) Bool.false 26758929747600409100288 9444732965739290427392 1000000000521964 130491000000000000000 3189913004350711 1125899906842624 250000000130491 32622750000000000000 (BSN.log_rat_reduce_isNear 17 1 4 34 32 15892 262144 24973259072661432 36028797018963968 130491 1000000000000000 rfl rfl rfl rfl (ep588 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep590 := nat_lit 746524525289681917299700928352256

noncomputable def ep591 := BSN.cos_dyadic_bound_f 165295496 1073741824 2 1 524288 261237 ep590 ep88 ep590 ep590 ep89 ep590 518087 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 165295496) qz269 0 1 ep590 ep88 ep590 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 165295496) qz270 0 1 ep590 ep89 ep590 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz891 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 141731253) qz280)

noncomputable def ep592 := @Enclosure.Real.IsNear.cos_image qz341 qz891 Bool.false 141731253 524288 3 4096 Bool.false 518087 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz341 Bool.false 60873109862024618013 225179981368524800 1590250000830053251 2174850000000000000000 141731253 524288 3 4096 (ep589 rfl) rfl) (Enclosure.sfrac_false_div 141731253 524288) (BSN.cos_reduce0 qz891 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11631636526392710004736) qz282) 226375608064910080 72057594037927936 Bool.false 518087 524288 43 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q0 141731253 524288 226375608064910080 72057594037927936 43 11631636526392710004736 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 518087 524288 11631636526392710004736 75557863725914323419136 165295496 1073741824 261237 260982 (ep591 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep593 := BSN.sin_dyadic_bound_f 165295496 1073741824 1 0 524288 261237 0 1 1 0 1 1 80391 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 165295496) qz275 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 165295496) qz276 0 0 rfl) rfl rfl

noncomputable def ep594 := @Enclosure.Real.IsNear.sin_image qz341 qz891 Bool.false 141731253 524288 3 4096 Bool.false 80391 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz341 Bool.false 60873109862024618013 225179981368524800 1590250000830053251 2174850000000000000000 141731253 524288 3 4096 (ep589 rfl) rfl) (Enclosure.sfrac_false_div 141731253 524288) (BSN.sin_reduce0 qz891 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11631636526392710004736) qz282) 226375608064910080 72057594037927936 Bool.false 80391 524288 43 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q0 141731253 524288 226375608064910080 72057594037927936 43 11631636526392710004736 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 80391 524288 11631636526392710004736 75557863725914323419136 165295496 1073741824 261237 260982 (ep593 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz597 := (@Enclosure.Real.IsNear.recentre' qz340 Bool.false 127159 524288 1 524288 127159 524288 1 524288 (ep587 rfl rfl) rfl)

noncomputable def ep595 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz340 (Real.cos qz341)) (@HMul.hMul Real Real Real qz0 qz340 (@Neg.neg Real Real.instNeg (Real.sin qz341))) Bool.false 65879424833 274877906944 6506076607837 35869092955029504 Bool.true 10222439169 274877906944 6448961219101 35869092955029504 (@Enclosure.Real.IsNear.mulLit_ff qz340 (Real.cos qz341) 127159 524288 1 524288 518087 524288 395569 534491136 65879424833 274877906944 6506076607837 35869092955029504 qz597 (@Enclosure.Real.IsNear.recentre' (Real.cos qz341) Bool.false 518087 524288 395569 534491136 518087 524288 395569 534491136 (ep592 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz340 (@Neg.neg Real Real.instNeg (Real.sin qz341)) 127159 524288 1 524288 80391 524288 395569 534491136 10222439169 274877906944 6448961219101 35869092955029504 qz597 (@Enclosure.Real.IsNear.neg (Real.sin qz341) Bool.false 80391 524288 395569 534491136 (@Enclosure.Real.IsNear.recentre' (Real.sin qz341) Bool.false 80391 524288 395569 534491136 80391 524288 395569 534491136 (ep594 rfl rfl) rfl)) rfl)

noncomputable def ep596 := @ep585 65879424833 274877906944 6506076607837 35869092955029504 Bool.true 10222439169 274877906944 6448961219101 35869092955029504 Bool.false 4546098920885787295744 132308892233 274877906944 157797113544499 35869092955029504 Bool.true 2373266569968597598208 69071147881 274877906944 157495401388669 35869092955029504 EMRow28.d8 (ep586 ep595) rfl rfl

noncomputable abbrev qz892 := (@Nat.cast Real Real.instNatCast 18)

noncomputable abbrev qz343 := (@Inv.inv Real Real.instInv (Real.sqrt qz892))

noncomputable abbrev qz344 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 18 1)))

noncomputable def ep597 := @Enclosure.Complex.IsNear.of_eq qz887 (Complex.mk (@HMul.hMul Real Real Real qz0 qz343 (Real.cos qz344)) (@HMul.hMul Real Real Real qz0 qz343 (@Neg.neg Real Real.instNeg (Real.sin qz344)))) Bool.false 6320737675 34359738368 262933280021 1494545539792896 Bool.false 40505289925 274877906944 2099925018907 11956364318343168 (BSN.cpow_neg_s_mk qz11 95415 1000 18 (@Eq.refl Real qz11) rfl)

noncomputable abbrev qz893 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 18) qz268)

noncomputable def ep598 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz892) 2224365 524288 1 524288 61787 61788 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz892) (Real.sqrt qz893) Bool.false 2224365 524288 1 524288 (BSN.sqrt_natCast_div_one 18) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz893) Bool.false 2224365 524288 1 524288 2224365 524288 1 524288 (BSN.sqrt_enclosure 18 1 1112182 1112183 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep599 := BSN.log_dyadic_bound 2 34 2 1 3468 262144 130491 4 4 30876 36 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 2) (BSN.artanhQ 34) 0 1 4 3468 4 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz345 := (Real.log (Enclosure.sfrac Bool.false 18 1))

noncomputable def ep600 := @Enclosure.Real.IsNear.mulLit_ff qz11 qz345 95415 1000 0 1 3254268794313975 1125899906842624 250000000130491 32622750000000000000 2484048456075743397 9007199254740992 1590250000830053251 2174850000000000000000 qz273 (BSN.isNear_log_sfrac 18 1 3254268794313975 1125899906842624 250000000130491 32622750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz893) Bool.false 27298785242132565196800 9444732965739290427392 1000000000521964 130491000000000000000 3254268794313975 1125899906842624 250000000130491 32622750000000000000 (BSN.log_rat_reduce_isNear 18 1 4 36 32 30876 262144 24973259072661432 36028797018963968 130491 1000000000000000 rfl rfl rfl rfl (ep599 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep601 := nat_lit 3435444591010701464031471532714759947317866438952728896014435157063379289185

noncomputable def ep602 := nat_lit 730161174771589468668127115322041068230982716812779588635502832906241121

noncomputable def ep603 := nat_lit 8996410810745064118085534189399564176483942891906116894037158406769859462241

noncomputable def ep604 := BSN.sin_dyadic_bound_f 961451413 1073741824 3 2 524288 261237 ep601 ep109 ep602 ep603 ep111 ep602 409192 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 961451413) qz275 0 2 ep601 ep109 ep602 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 961451413) qz276 0 2 ep603 ep111 ep602 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz894 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 72295325) qz271)

noncomputable def ep605 := @Enclosure.Real.IsNear.cos_image qz344 qz894 Bool.false 72295325 262144 3 4096 Bool.false 409192 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz344 Bool.false 2484048456075743397 9007199254740992 1590250000830053251 2174850000000000000000 72295325 262144 3 4096 (ep600 rfl) rfl) (Enclosure.sfrac_false_div 72295325 262144) (BSN.cos_reduce3 qz894 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 33828064280762017382400) qz274) 226375608064910080 72057594037927936 Bool.false 409192 524288 43 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q3 72295325 262144 226375608064910080 72057594037927936 43 33828064280762017382400 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 409192 524288 33828064280762017382400 37778931862957161709568 961451413 1073741824 261237 260982 (ep604 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep606 := nat_lit 1908904844416954853114670019115009766762472902847877288714079755183169045601

noncomputable def ep607 := nat_lit 5725254210901321380406673803114385218150956743110006306964968259883694654561

noncomputable def ep608 := BSN.cos_dyadic_bound_f 961451413 1073741824 3 2 524288 261237 ep606 ep102 ep602 ep607 ep105 ep602 327779 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 961451413) qz269 0 2 ep606 ep102 ep602 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 961451413) qz270 0 2 ep607 ep105 ep602 rfl rfl rfl rfl) rfl rfl

noncomputable def ep609 := @Enclosure.Real.IsNear.sin_image qz344 qz894 Bool.false 72295325 262144 3 4096 Bool.true 327779 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz344 Bool.false 2484048456075743397 9007199254740992 1590250000830053251 2174850000000000000000 72295325 262144 3 4096 (ep600 rfl) rfl) (Enclosure.sfrac_false_div 72295325 262144) (BSN.sin_reduce3 qz894 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 33828064280762017382400) qz274) 226375608064910080 72057594037927936 Bool.false 327779 524288 43 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q3 72295325 262144 226375608064910080 72057594037927936 43 33828064280762017382400 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 327779 524288 33828064280762017382400 37778931862957161709568 961451413 1073741824 261237 260982 (ep608 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz598 := (@Enclosure.Real.IsNear.recentre' qz343 Bool.false 123575 524288 1 524288 123575 524288 1 524288 (ep598 rfl rfl) rfl)

noncomputable def ep610 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz343 (Real.cos qz344)) (@HMul.hMul Real Real Real qz0 qz343 (@Neg.neg Real Real.instNeg (Real.sin qz344))) Bool.false 6320737675 34359738368 262933280021 1494545539792896 Bool.false 40505289925 274877906944 2099925018907 11956364318343168 (@Enclosure.Real.IsNear.mulLit_ff qz343 (Real.cos qz344) 123575 524288 1 524288 51149 65536 395569 534491136 6320737675 34359738368 262933280021 1494545539792896 qz598 (@Enclosure.Real.IsNear.recentre' (Real.cos qz344) Bool.false 409192 524288 395569 534491136 51149 65536 395569 534491136 (ep605 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz343 (@Neg.neg Real Real.instNeg (Real.sin qz344)) 123575 524288 1 524288 327779 524288 395569 534491136 40505289925 274877906944 2099925018907 11956364318343168 qz598 (@Enclosure.Real.IsNear.neg (Real.sin qz344) Bool.true 327779 524288 395569 534491136 (@Enclosure.Real.IsNear.recentre' (Real.sin qz344) Bool.true 327779 524288 395569 534491136 327779 524288 395569 534491136 (ep609 rfl rfl) rfl)) rfl)

noncomputable def ep611 := @ep583 6320737675 34359738368 262933280021 1494545539792896 Bool.false 40505289925 274877906944 2099925018907 11956364318343168 Bool.false 6283530063331872210944 182874793633 274877906944 164107512265003 35869092955029504 Bool.true 7852123245004890046464 7141464489 68719476736 81897588222695 17934546477514752 (ep584 (BSN.head_sum_c_succ qz14 17 18 rfl rfl) (ep596 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep597 ep610) rfl rfl

noncomputable abbrev qz895 := (@Nat.cast Real Real.instNatCast 19)

noncomputable abbrev qz346 := (@Inv.inv Real Real.instInv (Real.sqrt qz895))

noncomputable abbrev qz347 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 19 1)))

noncomputable def ep612 := @Enclosure.Complex.IsNear.of_eq qz886 (Complex.mk (@HMul.hMul Real Real Real qz0 qz346 (Real.cos qz347)) (@HMul.hMul Real Real Real qz0 qz346 (@Neg.neg Real Real.instNeg (Real.sin qz347)))) Bool.true 14320297461 274877906944 6121348618409 35869092955029504 Bool.false 30706627305 137438953472 3086219945065 17934546477514752 (BSN.cpow_neg_s_mk qz11 95415 1000 19 (@Eq.refl Real qz11) rfl)

noncomputable abbrev qz896 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 19) qz268)

noncomputable def ep613 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz895) 2285319 524288 1 524288 60139 60140 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz895) (Real.sqrt qz896) Bool.false 2285319 524288 1 524288 (BSN.sqrt_natCast_div_one 19) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz896) Bool.false 2285319 524288 1 524288 2285319 524288 1 524288 (BSN.sqrt_enclosure 19 1 1142659 1142660 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep614 := BSN.log_dyadic_bound 3 35 3 2 22509375 262144 130491 55368 243 45049 38 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 3) (BSN.artanhQ 35) 0 2 55368 22509375 243 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz348 := (Real.log (Enclosure.sfrac Bool.false 19 1))

noncomputable def ep615 := @Enclosure.Real.IsNear.mulLit_ff qz11 qz348 95415 1000 0 1 3315141365800183 1125899906842624 250000000130491 32622750000000000000 63262842683564892189 225179981368524800 1590250000830053251 2174850000000000000000 qz273 (BSN.isNear_log_sfrac 19 1 3315141365800183 1125899906842624 250000000130491 32622750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz896) Bool.false 27809421382282341515264 9444732965739290427392 1000000000521964 130491000000000000000 3315141365800183 1125899906842624 250000000130491 32622750000000000000 (BSN.log_rat_reduce_isNear 19 1 4 38 32 45049 262144 24973259072661432 36028797018963968 130491 1000000000000000 rfl rfl rfl rfl (ep614 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep616 := nat_lit 9637855799201603657359550176083358945174261773557115230924019088878390640896

noncomputable def ep617 := nat_lit 18555363021822010947137258472879776999950675384449865634477227368927887616

noncomputable def ep618 := nat_lit 28876456671561166950184376011304317281522883969902445961503102811897316147456

noncomputable def ep619 := BSN.cos_dyadic_bound_f 1440650658 1073741824 3 2 524288 261237 ep616 ep102 ep617 ep618 ep105 ep617 119059 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1440650658) qz269 0 2 ep616 ep102 ep617 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1440650658) qz270 0 2 ep618 ep105 ep617 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz897 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 147295283) qz280)

noncomputable def ep620 := @Enclosure.Real.IsNear.cos_image qz347 qz897 Bool.false 147295283 524288 385 524288 Bool.true 119059 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz347 Bool.false 63262842683564892189 225179981368524800 1590250000830053251 2174850000000000000000 147295283 524288 385 524288 (ep615 rfl) rfl) (Enclosure.sfrac_false_div 147295283 524288) (BSN.cos_reduce2 qz897 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 101376777629283601350656) qz282) 226375608064910080 72057594037927936 Bool.false 119059 524288 44 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q2 147295283 524288 226375608064910080 72057594037927936 44 101376777629283601350656 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 119059 524288 101376777629283601350656 75557863725914323419136 1440650658 1073741824 261237 260982 (ep619 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep621 := nat_lit 17333296148145428974489480510171742279713710652095247523155652578085960843520

noncomputable def ep622 := nat_lit 45366685990726506915462798155779424426964560138198443730570888860199252295936

noncomputable def ep623 := BSN.sin_dyadic_bound_f 1440650658 1073741824 3 2 524288 261237 ep621 ep109 ep617 ep622 ep111 ep617 510590 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1440650658) qz275 0 2 ep621 ep109 ep617 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1440650658) qz276 0 2 ep622 ep111 ep617 rfl rfl rfl rfl) rfl rfl

noncomputable def ep624 := @Enclosure.Real.IsNear.sin_image qz347 qz897 Bool.false 147295283 524288 385 524288 Bool.true 510590 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz347 Bool.false 63262842683564892189 225179981368524800 1590250000830053251 2174850000000000000000 147295283 524288 385 524288 (ep615 rfl) rfl) (Enclosure.sfrac_false_div 147295283 524288) (BSN.sin_reduce2 qz897 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 101376777629283601350656) qz282) 226375608064910080 72057594037927936 Bool.false 510590 524288 44 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q2 147295283 524288 226375608064910080 72057594037927936 44 101376777629283601350656 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 510590 524288 101376777629283601350656 75557863725914323419136 1440650658 1073741824 261237 260982 (ep623 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz599 := (@Enclosure.Real.IsNear.recentre' qz346 Bool.false 120279 524288 1 524288 120279 524288 1 524288 (ep613 rfl rfl) rfl)

noncomputable def ep625 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz346 (Real.cos qz347)) (@HMul.hMul Real Real Real qz0 qz346 (@Neg.neg Real Real.instNeg (Real.sin qz347))) Bool.true 14320297461 274877906944 6121348618409 35869092955029504 Bool.false 30706627305 137438953472 3086219945065 17934546477514752 (@Enclosure.Real.IsNear.mulLit_ft qz346 (Real.cos qz347) 120279 524288 1 524288 119059 524288 50763323 68414865408 14320297461 274877906944 6121348618409 35869092955029504 qz599 (@Enclosure.Real.IsNear.recentre' (Real.cos qz347) Bool.true 119059 524288 50763323 68414865408 119059 524288 50763323 68414865408 (ep620 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz346 (@Neg.neg Real Real.instNeg (Real.sin qz347)) 120279 524288 1 524288 255295 262144 50763323 68414865408 30706627305 137438953472 3086219945065 17934546477514752 qz599 (@Enclosure.Real.IsNear.neg (Real.sin qz347) Bool.true 255295 262144 50763323 68414865408 (@Enclosure.Real.IsNear.recentre' (Real.sin qz347) Bool.true 510590 524288 50763323 68414865408 255295 262144 50763323 68414865408 (ep624 rfl rfl) rfl)) rfl)

noncomputable def ep626 := @ep581 14320297461 274877906944 6121348618409 35869092955029504 Bool.false 30706627305 137438953472 3086219945065 17934546477514752 Bool.false 46331907113759820218368 42138624043 68719476736 14185738406951 2989091079585792 Bool.false 1128627955101358620672 16423698327 137438953472 1770496003495 373636384948224 (ep582 (BSN.head_sum_c_succ qz14 18 19 rfl rfl) (ep611 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep612 ep625) rfl rfl

noncomputable abbrev qz898 := (@Nat.cast Real Real.instNatCast 20)

noncomputable abbrev qz349 := (@Inv.inv Real Real.instInv (Real.sqrt qz898))

noncomputable abbrev qz350 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 20 1)))

noncomputable def ep627 := @Enclosure.Complex.IsNear.of_eq qz885 (Complex.mk (@HMul.hMul Real Real Real qz0 qz349 (Real.cos qz350)) (@HMul.hMul Real Real Real qz0 qz349 (@Neg.neg Real Real.instNeg (Real.sin qz350)))) Bool.true 30697867515 137438953472 3009813405473 17934546477514752 Bool.true 1456410405 137438953472 2977265557307 17934546477514752 (BSN.cpow_neg_s_mk qz11 95415 1000 20 (@Eq.refl Real qz11) rfl)

noncomputable abbrev qz899 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 20) qz268)

noncomputable def ep628 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz898) 2344687 524288 1 524288 58617 58618 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz898) (Real.sqrt qz899) Bool.false 2344687 524288 1 524288 (BSN.sqrt_natCast_div_one 20) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz899) Bool.false 2344687 524288 1 524288 2344687 524288 1 524288 (BSN.sqrt_enclosure 20 1 1172343 1172344 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep629 := BSN.log_dyadic_bound 4 36 3 2 25194240 262144 130491 104448 768 58495 40 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 4) (BSN.artanhQ 36) 0 2 104448 25194240 768 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz351 := (Real.log (Enclosure.sfrac Bool.false 20 1))

noncomputable def ep630 := @Enclosure.Real.IsNear.mulLit_ff qz11 qz351 95415 1000 0 1 3372891496062199 1125899906842624 250000000130491 32622750000000000000 64364888419354943517 225179981368524800 1590250000830053251 2174850000000000000000 qz273 (BSN.isNear_log_sfrac 20 1 3372891496062199 1125899906842624 250000000130491 32622750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz899) Bool.false 28293864586999331028992 9444732965739290427392 1000000000521964 130491000000000000000 3372891496062199 1125899906842624 250000000130491 32622750000000000000 (BSN.log_rat_reduce_isNear 20 1 4 40 32 58495 262144 24973259072661432 36028797018963968 130491 1000000000000000 rfl rfl rfl rfl (ep629 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep631 := nat_lit 28826699203132631970836450546820034719657256455662699506924972750793307311745

noncomputable def ep632 := nat_lit 51248567931101114659815974164536194583965257330527787668580123671749709441

noncomputable def ep633 := nat_lit 75415524041077967642741477950167032331680680300581453719054370337561543429761

noncomputable def ep634 := BSN.sin_dyadic_bound_f 1635724719 1073741824 3 2 524288 261237 ep631 ep109 ep632 ep633 ep111 ep632 523698 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1635724719) qz275 0 2 ep631 ep109 ep632 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1635724719) qz276 0 2 ep633 ep111 ep632 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz900 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 149861183) qz280)

noncomputable def ep635 := @Enclosure.Real.IsNear.cos_image qz350 qz900 Bool.false 149861183 524288 385 524288 Bool.true 523698 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz350 Bool.false 64364888419354943517 225179981368524800 1590250000830053251 2174850000000000000000 149861183 524288 385 524288 (ep630 rfl) rfl) (Enclosure.sfrac_false_div 149861183 524288) (BSN.cos_reduce1 qz900 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 115103894309715455246336) qz282) 226375608064910080 72057594037927936 Bool.false 523698 524288 45 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q1 149861183 524288 226375608064910080 72057594037927936 45 115103894309715455246336 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 523698 524288 115103894309715455246336 75557863725914323419136 1635724719 1073741824 261237 260982 (ep634 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep636 := nat_lit 16037610031931951590313501847862035375180238145292845409477687138739281710721

noncomputable def ep637 := nat_lit 48010332959933652541620873595257033736372783921217480653095901168874345713281

noncomputable def ep638 := BSN.cos_dyadic_bound_f 1635724719 1073741824 3 2 524288 261237 ep636 ep102 ep632 ep637 ep105 ep632 24846 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1635724719) qz269 0 2 ep636 ep102 ep632 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1635724719) qz270 0 2 ep637 ep105 ep632 rfl rfl rfl rfl) rfl rfl

noncomputable def ep639 := @Enclosure.Real.IsNear.sin_image qz350 qz900 Bool.false 149861183 524288 385 524288 Bool.false 24846 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz350 Bool.false 64364888419354943517 225179981368524800 1590250000830053251 2174850000000000000000 149861183 524288 385 524288 (ep630 rfl) rfl) (Enclosure.sfrac_false_div 149861183 524288) (BSN.sin_reduce1 qz900 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 115103894309715455246336) qz282) 226375608064910080 72057594037927936 Bool.false 24846 524288 45 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q1 149861183 524288 226375608064910080 72057594037927936 45 115103894309715455246336 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 24846 524288 115103894309715455246336 75557863725914323419136 1635724719 1073741824 261237 260982 (ep638 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz600 := (@Enclosure.Real.IsNear.recentre' qz349 Bool.false 117235 524288 1 524288 117235 524288 1 524288 (ep628 rfl rfl) rfl)

noncomputable def ep640 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz349 (Real.cos qz350)) (@HMul.hMul Real Real Real qz0 qz349 (@Neg.neg Real Real.instNeg (Real.sin qz350))) Bool.true 30697867515 137438953472 3009813405473 17934546477514752 Bool.true 1456410405 137438953472 2977265557307 17934546477514752 (@Enclosure.Real.IsNear.mulLit_ft qz349 (Real.cos qz350) 117235 524288 1 524288 261849 262144 50763323 68414865408 30697867515 137438953472 3009813405473 17934546477514752 qz600 (@Enclosure.Real.IsNear.recentre' (Real.cos qz350) Bool.true 523698 524288 50763323 68414865408 261849 262144 50763323 68414865408 (ep635 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz349 (@Neg.neg Real Real.instNeg (Real.sin qz350)) 117235 524288 1 524288 12423 262144 50763323 68414865408 1456410405 137438953472 2977265557307 17934546477514752 qz600 (@Enclosure.Real.IsNear.neg (Real.sin qz350) Bool.false 12423 262144 50763323 68414865408 (@Enclosure.Real.IsNear.recentre' (Real.sin qz350) Bool.false 24846 524288 50763323 68414865408 12423 262144 50763323 68414865408 (ep639 rfl rfl) rfl)) rfl)

noncomputable def ep641 := @ep579 30697867515 137438953472 3009813405473 17934546477514752 Bool.true 1456410405 137438953472 2977265557307 17934546477514752 Bool.false 3681946996678124896256 53579380571 137438953472 88124243847179 17934546477514752 Bool.false 2057088388313785565184 7483643961 68719476736 87961073725067 17934546477514752 (ep580 (BSN.head_sum_c_succ qz14 19 20 rfl rfl) (ep626 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep627 ep640) rfl rfl

noncomputable abbrev qz901 := (@Nat.cast Real Real.instNatCast 21)

noncomputable abbrev qz352 := (@Inv.inv Real Real.instInv (Real.sqrt qz901))

noncomputable abbrev qz353 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 21 1)))

noncomputable def ep642 := @Enclosure.Complex.IsNear.of_eq qz884 (Complex.mk (@HMul.hMul Real Real Real qz0 qz352 (Real.cos qz353)) (@HMul.hMul Real Real Real qz0 qz352 (@Neg.neg Real Real.instNeg (Real.sin qz353)))) Bool.false 6256913801 274877906944 5814968206729 35869092955029504 Bool.true 59655941643 274877906944 5875873315087 35869092955029504 (BSN.cpow_neg_s_mk qz11 95415 1000 21 (@Eq.refl Real qz11) rfl)

noncomputable abbrev qz902 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 21) qz268)

noncomputable def ep643 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz901) 2402589 524288 1 524288 57204 57205 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz901) (Real.sqrt qz902) Bool.false 2402589 524288 1 524288 (BSN.sqrt_natCast_div_one 21) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz902) Bool.false 2402589 524288 1 524288 2402589 524288 1 524288 (BSN.sqrt_enclosure 21 1 1201294 1201295 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep644 := BSN.log_dyadic_bound 5 37 3 2 28112415 262144 130491 173000 1875 71285 42 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 5) (BSN.artanhQ 37) 0 2 173000 28112415 1875 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz354 := (Real.log (Enclosure.sfrac Bool.false 21 1))

noncomputable def ep645 := @Enclosure.Real.IsNear.mulLit_ff qz11 qz354 95415 1000 0 1 3427824127778039 1125899906842624 250000000130491 32622750000000000000 65413167830388318237 225179981368524800 1590250000830053251 2174850000000000000000 qz273 (BSN.isNear_log_sfrac 21 1 3427824127778039 1125899906842624 250000000130491 32622750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz902) Bool.false 28754672900871880179712 9444732965739290427392 1000000000521964 130491000000000000000 3427824127778039 1125899906842624 250000000130491 32622750000000000000 (BSN.log_rat_reduce_isNear 21 1 4 42 32 71285 262144 24973259072661432 36028797018963968 130491 1000000000000000 rfl rfl rfl rfl (ep644 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep646 := nat_lit 13758992666768844600742482465502444032634061447182087095289251641897577193441

noncomputable def ep647 := nat_lit 37754531078377796365173775106401825994767575817047033078393151623504699361

noncomputable def ep648 := nat_lit 41201468938149778209497099846294528445912649189912167219710968622445722181601

noncomputable def ep649 := BSN.cos_dyadic_bound_f 1574421947 1073741824 3 2 524288 261237 ep646 ep102 ep647 ep648 ep105 ep647 54689 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1574421947) qz269 0 2 ep646 ep102 ep647 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1574421947) qz270 0 2 ep648 ep105 ep647 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz903 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 152301899) qz280)

noncomputable def ep650 := @Enclosure.Real.IsNear.cos_image qz353 qz903 Bool.false 152301899 524288 385 524288 Bool.false 54689 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz353 Bool.false 65413167830388318237 225179981368524800 1590250000830053251 2174850000000000000000 152301899 524288 385 524288 (ep645 rfl) rfl) (Enclosure.sfrac_false_div 152301899 524288) (BSN.cos_reduce0 qz903 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 110790095286059367661568) qz282) 226375608064910080 72057594037927936 Bool.false 54689 524288 46 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q0 152301899 524288 226375608064910080 72057594037927936 46 110790095286059367661568 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 54689 524288 110790095286059367661568 75557863725914323419136 1574421947 1073741824 261237 260982 (ep649 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep651 := nat_lit 24735983175321218044244329417819277797945496544274119145057938434116835188705

noncomputable def ep652 := nat_lit 64723591456476292731286771886973457943008581540823664469215297462915560742881

noncomputable def ep653 := BSN.sin_dyadic_bound_f 1574421947 1073741824 3 2 524288 261237 ep651 ep109 ep647 ep652 ep111 ep647 521427 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1574421947) qz275 0 2 ep651 ep109 ep647 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1574421947) qz276 0 2 ep652 ep111 ep647 rfl rfl rfl rfl) rfl rfl

noncomputable def ep654 := @Enclosure.Real.IsNear.sin_image qz353 qz903 Bool.false 152301899 524288 385 524288 Bool.false 521427 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz353 Bool.false 65413167830388318237 225179981368524800 1590250000830053251 2174850000000000000000 152301899 524288 385 524288 (ep645 rfl) rfl) (Enclosure.sfrac_false_div 152301899 524288) (BSN.sin_reduce0 qz903 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 110790095286059367661568) qz282) 226375608064910080 72057594037927936 Bool.false 521427 524288 46 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q0 152301899 524288 226375608064910080 72057594037927936 46 110790095286059367661568 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 521427 524288 110790095286059367661568 75557863725914323419136 1574421947 1073741824 261237 260982 (ep653 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz601 := (@Enclosure.Real.IsNear.recentre' qz352 Bool.false 114409 524288 1 524288 114409 524288 1 524288 (ep643 rfl rfl) rfl)

noncomputable def ep655 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz352 (Real.cos qz353)) (@HMul.hMul Real Real Real qz0 qz352 (@Neg.neg Real Real.instNeg (Real.sin qz353))) Bool.false 6256913801 274877906944 5814968206729 35869092955029504 Bool.true 59655941643 274877906944 5875873315087 35869092955029504 (@Enclosure.Real.IsNear.mulLit_ff qz352 (Real.cos qz353) 114409 524288 1 524288 54689 524288 50763323 68414865408 6256913801 274877906944 5814968206729 35869092955029504 qz601 (@Enclosure.Real.IsNear.recentre' (Real.cos qz353) Bool.false 54689 524288 50763323 68414865408 54689 524288 50763323 68414865408 (ep650 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz352 (@Neg.neg Real Real.instNeg (Real.sin qz353)) 114409 524288 1 524288 521427 524288 50763323 68414865408 59655941643 274877906944 5875873315087 35869092955029504 qz601 (@Enclosure.Real.IsNear.neg (Real.sin qz353) Bool.false 521427 524288 50763323 68414865408 (@Enclosure.Real.IsNear.recentre' (Real.sin qz353) Bool.false 521427 524288 50763323 68414865408 521427 524288 50763323 68414865408 (ep654 rfl rfl) rfl)) rfl)

noncomputable def ep656 := @ep577 6256913801 274877906944 5814968206729 35869092955029504 Bool.true 59655941643 274877906944 5875873315087 35869092955029504 Bool.false 15587731671486453252096 113415674943 274877906944 182063455901087 35869092955029504 Bool.true 2042436705586526552064 29721365799 274877906944 181798020765221 35869092955029504 (ep578 (BSN.head_sum_c_succ qz14 20 21 rfl rfl) (ep641 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep642 ep655) rfl rfl

noncomputable abbrev qz904 := (@Nat.cast Real Real.instNatCast 22)

noncomputable abbrev qz355 := (@Inv.inv Real Real.instInv (Real.sqrt qz904))

noncomputable abbrev qz356 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 22 1)))

noncomputable def ep657 := @Enclosure.Complex.IsNear.of_eq qz883 (Complex.mk (@HMul.hMul Real Real Real qz0 qz355 (Real.cos qz356)) (@HMul.hMul Real Real Real qz0 qz355 (@Neg.neg Real Real.instNeg (Real.sin qz356)))) Bool.false 13615911769 68719476736 5888188187 36902359007232 Bool.false 10818754073 137438953472 11697525979 73804718014464 (BSN.cpow_neg_s_mk qz11 95415 1000 22 (@Eq.refl Real qz11) rfl)

noncomputable abbrev qz905 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 22) qz268)

noncomputable def ep658 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz904) 2459129 524288 1 524288 55889 55890 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz904) (Real.sqrt qz905) Bool.false 2459129 524288 1 524288 (BSN.sqrt_natCast_div_one 22) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz905) Bool.false 2459129 524288 1 524288 2459129 524288 1 524288 (BSN.sqrt_enclosure 22 1 1229564 1229565 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep659 := BSN.log_dyadic_bound 6 38 4 3 316148320320 262144 130491 2667271104 699840 83480 44 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 6) (BSN.artanhQ 38) 0 3 2667271104 316148320320 699840 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz357 := (Real.log (Enclosure.sfrac Bool.false 22 1))

noncomputable def ep660 := @Enclosure.Real.IsNear.mulLit_ff qz11 qz357 95415 1000 0 1 3480201253952759 1125899906842624 250000000130491 32622750000000000000 66412680529180499997 225179981368524800 1590250000830053251 2174850000000000000000 qz273 (BSN.isNear_log_sfrac 22 1 3480201253952759 1125899906842624 250000000130491 32622750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz905) Bool.false 29194044080518145769472 9444732965739290427392 1000000000521964 130491000000000000000 3480201253952759 1125899906842624 250000000130491 32622750000000000000 (BSN.log_rat_reduce_isNear 22 1 4 44 32 83480 262144 24973259072661432 36028797018963968 130491 1000000000000000 rfl rfl rfl rfl (ep659 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep661 := nat_lit 10816830610314545074639008793768175345437558537091701886957224365273005424640

noncomputable def ep662 := nat_lit 7231969815912350363079412389600791571880060094130887570310297212636102656

noncomputable def ep663 := nat_lit 28318085552074236152038132554095391289791514166516340647869370951656460517376

noncomputable def ep664 := BSN.sin_dyadic_bound_f 1280581064 1073741824 3 2 524288 261237 ep661 ep109 ep662 ep663 ep111 ep662 487244 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1280581064) qz275 0 2 ep661 ep109 ep662 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1280581064) qz276 0 2 ep663 ep111 ep662 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz906 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 154629071) qz280)

noncomputable def ep665 := @Enclosure.Real.IsNear.cos_image qz356 qz906 Bool.false 154629071 524288 3 4096 Bool.false 487244 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz356 Bool.false 66412680529180499997 225179981368524800 1590250000830053251 2174850000000000000000 154629071 524288 3 4096 (ep660 rfl) rfl) (Enclosure.sfrac_false_div 154629071 524288) (BSN.cos_reduce3 qz906 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 90112881347518300946432) qz282) 226375608064910080 72057594037927936 Bool.false 487244 524288 46 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q3 154629071 524288 226375608064910080 72057594037927936 46 90112881347518300946432 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 487244 524288 90112881347518300946432 75557863725914323419136 1280581064 1073741824 261237 260982 (ep664 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep666 := nat_lit 6012564547870708308294151290933253321497256991759448109451929223912841281536

noncomputable def ep667 := nat_lit 18023229703980300224156295048020558381348010855090082553215167077313251639296

noncomputable def ep668 := BSN.cos_dyadic_bound_f 1280581064 1073741824 3 2 524288 261237 ep666 ep102 ep662 ep667 ep105 ep662 193574 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1280581064) qz269 0 2 ep666 ep102 ep662 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1280581064) qz270 0 2 ep667 ep105 ep662 rfl rfl rfl rfl) rfl rfl

noncomputable def ep669 := @Enclosure.Real.IsNear.sin_image qz356 qz906 Bool.false 154629071 524288 3 4096 Bool.true 193574 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz356 Bool.false 66412680529180499997 225179981368524800 1590250000830053251 2174850000000000000000 154629071 524288 3 4096 (ep660 rfl) rfl) (Enclosure.sfrac_false_div 154629071 524288) (BSN.sin_reduce3 qz906 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 90112881347518300946432) qz282) 226375608064910080 72057594037927936 Bool.false 193574 524288 46 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q3 154629071 524288 226375608064910080 72057594037927936 46 90112881347518300946432 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 193574 524288 90112881347518300946432 75557863725914323419136 1280581064 1073741824 261237 260982 (ep668 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz602 := (@Enclosure.Real.IsNear.recentre' qz355 Bool.false 111779 524288 1 524288 111779 524288 1 524288 (ep658 rfl rfl) rfl)

noncomputable def ep670 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz355 (Real.cos qz356)) (@HMul.hMul Real Real Real qz0 qz355 (@Neg.neg Real Real.instNeg (Real.sin qz356))) Bool.false 13615911769 68719476736 5888188187 36902359007232 Bool.false 10818754073 137438953472 11697525979 73804718014464 (@Enclosure.Real.IsNear.mulLit_ff qz355 (Real.cos qz356) 111779 524288 1 524288 121811 131072 395569 534491136 13615911769 68719476736 5888188187 36902359007232 qz602 (@Enclosure.Real.IsNear.recentre' (Real.cos qz356) Bool.false 487244 524288 395569 534491136 121811 131072 395569 534491136 (ep665 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz355 (@Neg.neg Real Real.instNeg (Real.sin qz356)) 111779 524288 1 524288 96787 262144 395569 534491136 10818754073 137438953472 11697525979 73804718014464 qz602 (@Enclosure.Real.IsNear.neg (Real.sin qz356) Bool.true 96787 262144 395569 534491136 (@Enclosure.Real.IsNear.recentre' (Real.sin qz356) Bool.true 193574 524288 395569 534491136 96787 262144 395569 534491136 (ep669 rfl rfl) rfl)) rfl)

noncomputable def ep671 := @ep575 13615911769 68719476736 5888188187 36902359007232 Bool.false 10818754073 137438953472 11697525979 73804718014464 Bool.false 11536579163940123049984 167879322019 274877906944 187786774818851 35869092955029504 Bool.true 1111036935844938121216 8083857653 274877906944 187483018391015 35869092955029504 (ep576 (BSN.head_sum_c_succ qz14 21 22 rfl rfl) (ep656 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep657 ep670) rfl rfl

noncomputable abbrev qz907 := (@Nat.cast Real Real.instNatCast 23)

noncomputable abbrev qz358 := (@Inv.inv Real Real.instInv (Real.sqrt qz907))

noncomputable abbrev qz359 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 23 1)))

noncomputable def ep672 := @Enclosure.Complex.IsNear.of_eq qz882 (Complex.mk (@HMul.hMul Real Real Real qz0 qz358 (Real.cos qz359)) (@HMul.hMul Real Real Real qz0 qz358 (@Neg.neg Real Real.instNeg (Real.sin qz359)))) Bool.true 43026012575 274877906944 5586640455229 35869092955029504 Bool.false 37866061375 274877906944 5580481280029 35869092955029504 (BSN.cpow_neg_s_mk qz11 95415 1000 23 (@Eq.refl Real qz11) rfl)

noncomputable abbrev qz908 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 23) qz268)

noncomputable def ep673 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz907) 2514397 524288 1 524288 54660 54661 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz907) (Real.sqrt qz908) Bool.false 2514397 524288 1 524288 (BSN.sqrt_natCast_div_one 23) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz908) Bool.false 2514397 524288 1 524288 2514397 524288 1 524288 (BSN.sqrt_enclosure 23 1 1257198 1257199 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep674 := BSN.log_dyadic_bound 7 39 4 3 369468094905 262144 130491 4046006391 1764735 95133 46 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 7) (BSN.artanhQ 39) 0 3 4046006391 369468094905 1764735 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz360 := (Real.log (Enclosure.sfrac Bool.false 23 1))

noncomputable def ep675 := @Enclosure.Real.IsNear.mulLit_ff qz11 qz360 95415 1000 0 1 3530250507853047 1125899906842624 250000000130491 32622750000000000000 67367770441359695901 225179981368524800 1590250000830053251 2174850000000000000000 qz273 (BSN.isNear_log_sfrac 23 1 3530250507853047 1125899906842624 250000000130491 32622750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz908) Bool.false 29613887652180132888576 9444732965739290427392 1000000000521964 130491000000000000000 3530250507853047 1125899906842624 250000000130491 32622750000000000000 (BSN.log_rat_reduce_isNear 23 1 4 46 32 95133 262144 24973259072661432 36028797018963968 130491 1000000000000000 rfl rfl rfl rfl (ep674 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep676 := nat_lit 805371704328433773996679189463375454932266957490765404314716992439209557601

noncomputable def ep677 := nat_lit 130027426281923272245985261379422247096869046936358264813479560388673121

noncomputable def ep678 := nat_lit 2415855058132737475445545597867367520302607134378423496414524018196851326561

noncomputable def ep679 := BSN.cos_dyadic_bound_f 774915541 1073741824 3 2 524288 261237 ep676 ep102 ep677 ep678 ep105 ep677 393575 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 774915541) qz269 0 2 ep676 ep102 ep677 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 774915541) qz270 0 2 ep678 ep105 ep677 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz909 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 156852813) qz280)

noncomputable def ep680 := @Enclosure.Real.IsNear.cos_image qz359 qz909 Bool.false 156852813 524288 3 4096 Bool.true 393575 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz359 Bool.false 67367770441359695901 225179981368524800 1590250000830053251 2174850000000000000000 156852813 524288 3 4096 (ep675 rfl) rfl) (Enclosure.sfrac_false_div 156852813 524288) (BSN.cos_reduce2 qz909 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 54529833506291461390336) qz282) 226375608064910080 72057594037927936 Bool.false 393575 524288 47 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q2 156852813 524288 226375608064910080 72057594037927936 47 54529833506291461390336 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 393575 524288 54529833506291461390336 75557863725914323419136 774915541 1073741824 261237 260982 (ep679 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep681 := nat_lit 360593158950531495307067276369027761

noncomputable def ep682 := BSN.sin_dyadic_bound_f 774915541 1073741824 2 1 524288 261237 ep681 ep92 ep681 ep681 ep93 ep681 346375 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 774915541) qz275 0 1 ep681 ep92 ep681 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 774915541) qz276 0 1 ep681 ep93 ep681 rfl rfl rfl rfl) rfl rfl

noncomputable def ep683 := @Enclosure.Real.IsNear.sin_image qz359 qz909 Bool.false 156852813 524288 3 4096 Bool.true 346375 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz359 Bool.false 67367770441359695901 225179981368524800 1590250000830053251 2174850000000000000000 156852813 524288 3 4096 (ep675 rfl) rfl) (Enclosure.sfrac_false_div 156852813 524288) (BSN.sin_reduce2 qz909 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 54529833506291461390336) qz282) 226375608064910080 72057594037927936 Bool.false 346375 524288 47 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q2 156852813 524288 226375608064910080 72057594037927936 47 54529833506291461390336 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 346375 524288 54529833506291461390336 75557863725914323419136 774915541 1073741824 261237 260982 (ep682 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz603 := (@Enclosure.Real.IsNear.recentre' qz358 Bool.false 109321 524288 1 524288 109321 524288 1 524288 (ep673 rfl rfl) rfl)

noncomputable def ep684 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz358 (Real.cos qz359)) (@HMul.hMul Real Real Real qz0 qz358 (@Neg.neg Real Real.instNeg (Real.sin qz359))) Bool.true 43026012575 274877906944 5586640455229 35869092955029504 Bool.false 37866061375 274877906944 5580481280029 35869092955029504 (@Enclosure.Real.IsNear.mulLit_ft qz358 (Real.cos qz359) 109321 524288 1 524288 393575 524288 395569 534491136 43026012575 274877906944 5586640455229 35869092955029504 qz603 (@Enclosure.Real.IsNear.recentre' (Real.cos qz359) Bool.true 393575 524288 395569 534491136 393575 524288 395569 534491136 (ep680 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz358 (@Neg.neg Real Real.instNeg (Real.sin qz359)) 109321 524288 1 524288 346375 524288 395569 534491136 37866061375 274877906944 5580481280029 35869092955029504 qz603 (@Enclosure.Real.IsNear.neg (Real.sin qz359) Bool.true 346375 524288 395569 534491136 (@Enclosure.Real.IsNear.recentre' (Real.sin qz359) Bool.true 346375 524288 395569 534491136 346375 524288 395569 534491136 (ep683 rfl rfl) rfl)) rfl)

noncomputable def ep685 := @ep573 43026012575 274877906944 5586640455229 35869092955029504 Bool.false 37866061375 274877906944 5580481280029 35869092955029504 Bool.false 34319416374998268379136 31213327361 68719476736 2014306409105 373636384948224 Bool.false 8186469823283166445568 14891101861 137438953472 16088624972587 2989091079585792 (ep574 (BSN.head_sum_c_succ qz14 22 23 rfl rfl) (ep671 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep672 ep684) rfl rfl

noncomputable def ep686 := @Enclosure.Complex.IsNear.mul qz45 (@HAdd.hAdd Complex Complex Complex qz15 qz46 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz49 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1))))) Bool.false ep564 ep363 ep565 ep365 Bool.true

noncomputable def ep687 := nat_lit 21332575139313470813719260971

noncomputable def ep688 := nat_lit 2952143783999248069243699200000

noncomputable def ep689 := nat_lit 265172876475577274854380593391551

noncomputable def ep690 := @Enclosure.Real.IsNear.subLit_tt_p (@HMul.hMul Real Real Real qz0 (Complex.re qz45) (Complex.re (@HAdd.hAdd Complex Complex Complex qz15 qz46 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz49 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 (Complex.im qz45) (Complex.im (@HAdd.hAdd Complex Complex Complex qz15 qz46 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz49 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1))))))) ep687 ep688 ep689

noncomputable def ep691 := nat_lit 3467053750660612918233115970764800000

noncomputable def ep692 := nat_lit 2007655543002395488391589369629

noncomputable def ep693 := nat_lit 1775865028241273694518104197093481

noncomputable def ep694 := nat_lit 69341075013212258364662319415296000000

noncomputable def ep695 := nat_lit 4667351249801733794797465619402406240296234154063613132800000

noncomputable def ep696 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re qz45) (Complex.re (@HAdd.hAdd Complex Complex Complex qz15 qz46 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz49 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))))) 3936907953 274877906944 5437491199877 35869092955029504 48767504484710830963

noncomputable abbrev qz910 := (@Nat.cast Real Real.instNatCast 24)

noncomputable abbrev qz361 := (@Inv.inv Real Real.instInv (Real.sqrt qz910))

noncomputable abbrev qz362 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 24 1)))

noncomputable abbrev qz911 := (@Neg.neg Real Real.instNeg (Real.sin qz362))

noncomputable def ep697 := @Enclosure.Complex.IsNear.of_eq qz45 (Complex.mk (@HMul.hMul Real Real Real qz0 qz361 (Real.cos qz362)) (@HMul.hMul Real Real Real qz0 qz361 qz911)) Bool.true 3936907953 274877906944 5437491199877 35869092955029504 Bool.true 55970401905 274877906944 5500936968005 35869092955029504 (BSN.cpow_neg_s_mk qz11 95415 1000 24 (@Eq.refl Real qz11) rfl)

noncomputable abbrev qz912 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 24) qz268)

noncomputable def ep698 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz910) 2568477 524288 1 524288 53509 53510 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz910) (Real.sqrt qz912) Bool.false 2568477 524288 1 524288 (BSN.sqrt_natCast_div_one 24) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz912) Bool.false 2568477 524288 1 524288 2568477 524288 1 524288 (BSN.sqrt_enclosure 24 1 1284238 1284239 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep699 := BSN.log_dyadic_bound 8 40 4 3 430080000000 262144 130491 5875957760 3932160 106290 48 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 8) (BSN.artanhQ 40) 0 3 5875957760 430080000000 3932160 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz363 := (Real.log (Enclosure.sfrac Bool.false 24 1))

noncomputable abbrev qz913 := (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 24) qz268))

noncomputable def ep700 := @Enclosure.Real.IsNear.mulLit_ff qz11 qz363 95415 1000 0 1 3578169457974519 1125899906842624 250000000130491 32622750000000000000 68282207766527746077 225179981368524800 1590250000830053251 2174850000000000000000 qz273 (BSN.isNear_log_sfrac 24 1 3578169457974519 1125899906842624 250000000130491 32622750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz913 Bool.false 30015860940520713879552 9444732965739290427392 1000000000521964 130491000000000000000 3578169457974519 1125899906842624 250000000130491 32622750000000000000 (BSN.log_rat_reduce_isNear 24 1 4 48 32 106290 262144 24973259072661432 36028797018963968 130491 1000000000000000 rfl rfl rfl rfl (ep699 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep701 := BSN.sin_dyadic_bound_f 75402722 1073741824 1 0 524288 261237 0 1 1 0 1 1 36787 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 75402722) qz275 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 75402722) qz276 0 0 rfl) rfl rfl

noncomputable abbrev qz914 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 158981903) qz280)

noncomputable def ep702 := @Enclosure.Real.IsNear.cos_image qz362 qz914 Bool.false 158981903 524288 385 524288 Bool.true 36787 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz362 Bool.false 68282207766527746077 225179981368524800 1590250000830053251 2174850000000000000000 158981903 524288 385 524288 (ep700 rfl) rfl) (Enclosure.sfrac_false_div 158981903 524288) (BSN.cos_reduce1 qz914 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 5305994883308711837696) qz282) 226375608064910080 72057594037927936 Bool.false 36787 524288 48 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q1 158981903 524288 226375608064910080 72057594037927936 48 5305994883308711837696 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 36787 524288 5305994883308711837696 75557863725914323419136 75402722 1073741824 261237 260982 (ep701 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep703 := nat_lit 32325711740008704897765566192656

noncomputable def ep704 := BSN.cos_dyadic_bound_f 75402722 1073741824 2 1 524288 261237 ep703 ep88 ep703 ep703 ep89 ep703 522995 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 75402722) qz269 0 1 ep703 ep88 ep703 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 75402722) qz270 0 1 ep703 ep89 ep703 rfl rfl rfl rfl) rfl rfl

noncomputable def ep705 := @Enclosure.Real.IsNear.sin_image qz362 qz914 Bool.false 158981903 524288 385 524288 Bool.false 522995 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz362 Bool.false 68282207766527746077 225179981368524800 1590250000830053251 2174850000000000000000 158981903 524288 385 524288 (ep700 rfl) rfl) (Enclosure.sfrac_false_div 158981903 524288) (BSN.sin_reduce1 qz914 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 5305994883308711837696) qz282) 226375608064910080 72057594037927936 Bool.false 522995 524288 48 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q1 158981903 524288 226375608064910080 72057594037927936 48 5305994883308711837696 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 522995 524288 5305994883308711837696 75557863725914323419136 75402722 1073741824 261237 260982 (ep704 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz604 := (@Enclosure.Real.IsNear.recentre' qz361 Bool.false 107019 524288 1 524288 107019 524288 1 524288 (ep698 rfl rfl) rfl)

noncomputable def ep706 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz361 (Real.cos qz362)) (@HMul.hMul Real Real Real qz0 qz361 qz911) Bool.true 3936907953 274877906944 5437491199877 35869092955029504 Bool.true 55970401905 274877906944 5500936968005 35869092955029504 (@Enclosure.Real.IsNear.mulLit_ft qz361 (Real.cos qz362) 107019 524288 1 524288 36787 524288 50763323 68414865408 3936907953 274877906944 5437491199877 35869092955029504 qz604 (@Enclosure.Real.IsNear.recentre' (Real.cos qz362) Bool.true 36787 524288 50763323 68414865408 36787 524288 50763323 68414865408 (ep702 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz361 qz911 107019 524288 1 524288 522995 524288 50763323 68414865408 55970401905 274877906944 5500936968005 35869092955029504 qz604 (@Enclosure.Real.IsNear.neg (Real.sin qz362) Bool.false 522995 524288 50763323 68414865408 (@Enclosure.Real.IsNear.recentre' (Real.sin qz362) Bool.false 522995 524288 50763323 68414865408 522995 524288 50763323 68414865408 (ep705 rfl rfl) rfl)) rfl)

noncomputable def ep707 := @ep696 96658528695091200000 0 1 ep687 ep688 ep689 ep691 (@Enclosure.Complex.IsNear.re_isNear qz45 Bool.true 3936907953 274877906944 5437491199877 35869092955029504 Bool.true 55970401905 274877906944 5500936968005 35869092955029504 (ep697 ep706))

noncomputable def ep708 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz15 qz46 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz49 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1))))) Bool.false 48767504484710830963 96658528695091200000 0 1 Bool.false

noncomputable def ep709 := @Enclosure.Complex.IsNear.addLitP qz46 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz49 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) Bool.false 363210889 728341778 0 1 Bool.true 91598400

noncomputable def ep710 := @ep709 364170889 0 1 Bool.false 1553232667 265420800000 0 1 Bool.false 11108410784929 26542080000000 0 1 Bool.false 97535008969421661926 48767504484710830963 96658528695091200000 0 1 Bool.false 1614147770252781731881 1614147770252781731881 9665852869509120000000 0 1

noncomputable abbrev qz50 := (@HDiv.hDiv Complex Complex Complex qz331 qz881 (@HSub.hSub Complex Complex Complex qz580 qz262 (1 : Complex)))

noncomputable def ep711 := @Enclosure.Complex.IsNear.addLitP qz50 qz26 Bool.true 48000000 36417088900 0 1 Bool.true 9159840000 36417088900 0 1

noncomputable def ep712 := @Enclosure.Complex.IsNear.of_eq qz50 (Complex.mk (Enclosure.sfrac Bool.true 48000000 36417088900) (Enclosure.sfrac Bool.true 9159840000 36417088900)) Bool.true 48000000 36417088900 0 1 Bool.true 9159840000 36417088900 0 1

noncomputable def ep713 := @ep711 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 36321088900 363210889 728341778 0 1 Bool.true 9159840000 91598400 364170889 0 1 (ep712 (BSN.N_div_s_sub_one_mk qz11 95415 1000 24 (@Eq.refl Real qz11) rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 48000000 36417088900) (Enclosure.sfrac Bool.true 9159840000 36417088900) Bool.true 48000000 36417088900 0 1 Bool.true 9159840000 36417088900 0 1 (Enclosure.Real.IsNear.const Bool.true 48000000 36417088900) (Enclosure.Real.IsNear.const Bool.true 9159840000 36417088900))) qz336 rfl

noncomputable abbrev qz51 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz869 2 2)))

noncomputable abbrev qz364 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz49 3))

noncomputable def ep714 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz49 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz15 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz49 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3))) qz364)) Bool.false 1553232667 265420800000 0 1

noncomputable def ep715 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz49 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3))) qz364) Bool.false 1 576 0 1 Bool.false

noncomputable def ep716 := @ep715 6361 19200 0 1 Bool.false 1092432667 265420800000 0 1 Bool.false 2314964384929 26542080000000 0 1 Bool.false 894662016192 1553232667 265420800000 0 1 Bool.false 213281487070636800 11108410784929 26542080000000 0

noncomputable abbrev qz52 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz869 2 1)))

noncomputable abbrev qz365 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz49 1))

noncomputable def ep717 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz49 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz15 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz49 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1))) qz365)) Bool.false 1 576 0 1

noncomputable def ep718 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz49 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1))) qz365) Bool.false 0 1 0 1 Bool.false

noncomputable def ep719 := @ep718 0 1 0 1 Bool.false 1 576 0 1 Bool.false 6361 19200 0 1 Bool.false 1 1 576 0 1 Bool.false 6361 6361 19200 0

noncomputable def ep720 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz49 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (Complex.mk qz265 qz265) Bool.false 0 1 0 1 Bool.false

noncomputable def ep721 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1))) qz365 Bool.false 1 576 0 1 Bool.false 6361 19200 0 1

noncomputable def ep722 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz365)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz365)) 1 576 0 1 0 1 0

noncomputable def ep723 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz365) 1 24 0 1 1 24 0 1 1

noncomputable def ep724 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep725 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep726 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz265) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 1 1 6 2 Bool.false BSN.bern_real_1 EMRow28.d9 rfl) qz589

noncomputable def ep727 := @ep725 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep726) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 95415 1000 0 1 ep316)

noncomputable def ep728 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 95415 1000 0 1 0 1 0

noncomputable def ep729 := @ep728 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep726) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 95415 1000 0 1 ep316)

noncomputable def ep730 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1)))) 6361 800 0 1 0 1 0 1 6361

noncomputable def ep731 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 95415 1000 0 1 6361 800 0

noncomputable def ep732 := @ep731 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep726) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 95415 1000 0 1 ep316)

noncomputable def ep733 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep734 := @ep733 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep726) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 95415 1000 0 1 ep316)

noncomputable def ep735 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 6361 800 0 1 (@ep724 1 24 0 1 (ep727 rfl) (ep729 rfl) rfl rfl) (@ep730 6361 800 0 1 (ep732 rfl) (ep734 rfl) rfl rfl)

noncomputable def ep736 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 6361 800 0 1 ep735

noncomputable abbrev qz366 := (@Enclosure.Complex.IsNear.of_eq (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz49 1)) (Complex.mk (Enclosure.sfrac Bool.false 1 24) qz553) Bool.false 1 24 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 24 1 24 EMRow28.d10 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 24) qz553 Bool.false 1 24 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 24) qz823))

noncomputable def ep737 := @ep723 576 0 1 ep736 (@Enclosure.Complex.IsNear.re_isNear qz365 Bool.false 1 24 0 1 Bool.false 0 1 0 1 qz366)

noncomputable def ep738 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz365) 6361 800 0 1 0 1 0 1 0

noncomputable def ep739 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 6361 800 0 1 ep735

noncomputable def ep740 := @ep738 1 0 1 ep739 (@Enclosure.Complex.IsNear.im_isNear qz365 Bool.false 1 24 0 1 Bool.false 0 1 0 1 qz366)

noncomputable def ep741 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz365)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz365)) 0 1 0 1 6361 19200 0

noncomputable def ep742 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz365) 1 24 0 1 0 1 0 1 0

noncomputable def ep743 := @ep742 1 0 1 ep736 (@Enclosure.Complex.IsNear.im_isNear qz365 Bool.false 1 24 0 1 Bool.false 0 1 0 1 qz366)

noncomputable def ep744 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz365) 6361 800 0 1 1 24 0 1 6361

noncomputable def ep745 := @ep744 19200 0 1 ep739 (@Enclosure.Complex.IsNear.re_isNear qz365 Bool.false 1 24 0 1 Bool.false 0 1 0 1 qz366)

noncomputable def ep746 := @ep719 1 (@ep720 0 1 0 1 (BSN.bern_sum_base qz14 24) qz339) (ep721 (@ep722 1 1 1 576 0 1 (ep737 rfl) (ep740 rfl) rfl rfl) (@ep741 1 6361 6361 19200 0 1 (ep743 rfl) (ep745 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep747 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3))) qz364 Bool.false 1092432667 265420800000 0 1 Bool.false 2314964384929 26542080000000 0 1

noncomputable def ep748 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.re qz364)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.im qz364)) 1092432667 265420800000 0 1 0 1 0

noncomputable def ep749 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.re qz364) 1092432667 19200000 0 1 1 13824 0 1 1092432667

noncomputable def ep750 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3)))) 1092432667 19200000 0 1 0 1 0 1 1092432667

noncomputable def ep751 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 3277298001 80000 0 1 1092432667 19200000 0

noncomputable def ep752 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (Complex.mk (Enclosure.sfrac Bool.true 1 720) qz265) Bool.true 1 720 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 2 1 30 24 Bool.true BSN.bern_real_2 EMRow28.d11 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 1 720) qz265 Bool.true 1 720 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.true 1 720) qz277)

noncomputable def ep753 := @ep751 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep752) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 3277298001 80000 0 1 Bool.true 6944893154787 8000000 0 1 EMRow28.d12)

noncomputable def ep754 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 6944893154787 8000000 0 1 0 1 0

noncomputable def ep755 := @ep754 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep752) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 3277298001 80000 0 1 Bool.true 6944893154787 8000000 0 1 EMRow28.d12)

noncomputable def ep756 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3)))) 2314964384929 1920000000 0 1 0 1 0 1 2314964384929

noncomputable def ep757 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 6944893154787 8000000 0 1 2314964384929 1920000000 0

noncomputable def ep758 := @ep757 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep752) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 3277298001 80000 0 1 Bool.true 6944893154787 8000000 0 1 EMRow28.d12)

noncomputable def ep759 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 3277298001 80000 0 1 0 1 0

noncomputable def ep760 := @ep759 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep752) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 3277298001 80000 0 1 Bool.true 6944893154787 8000000 0 1 EMRow28.d12)

noncomputable def ep761 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 1092432667 19200000 0 1 Bool.false 2314964384929 1920000000 0 1 (@ep750 1092432667 19200000 0 1 (ep753 rfl) (ep755 rfl) rfl rfl) (@ep756 2314964384929 1920000000 0 1 (ep758 rfl) (ep760 rfl) rfl rfl)

noncomputable def ep762 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 1092432667 19200000 0 1 Bool.false 2314964384929 1920000000 0 1 ep761

noncomputable abbrev qz367 := (@Enclosure.Complex.IsNear.of_eq (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz49 3)) (Complex.mk (Enclosure.sfrac Bool.false 1 13824) qz553) Bool.false 1 13824 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 24 3 13824 EMRow28.d13 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 13824) qz553 Bool.false 1 13824 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 13824) qz823))

noncomputable def ep763 := @ep749 265420800000 0 1 ep762 (@Enclosure.Complex.IsNear.re_isNear qz364 Bool.false 1 13824 0 1 Bool.false 0 1 0 1 qz367)

noncomputable def ep764 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.im qz364) 2314964384929 1920000000 0 1 0 1 0 1 0

noncomputable def ep765 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 1092432667 19200000 0 1 Bool.false 2314964384929 1920000000 0 1 ep761

noncomputable def ep766 := @ep764 1 0 1 ep765 (@Enclosure.Complex.IsNear.im_isNear qz364 Bool.false 1 13824 0 1 Bool.false 0 1 0 1 qz367)

noncomputable def ep767 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.im qz364)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.re qz364)) 0 1 0 1 2314964384929 26542080000000 0

noncomputable def ep768 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.im qz364) 1092432667 19200000 0 1 0 1 0 1 0

noncomputable def ep769 := @ep768 1 0 1 ep762 (@Enclosure.Complex.IsNear.im_isNear qz364 Bool.false 1 13824 0 1 Bool.false 0 1 0 1 qz367)

noncomputable def ep770 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.re qz364) 2314964384929 1920000000 0 1 1 13824 0 1 2314964384929

noncomputable def ep771 := @ep770 26542080000000 0 1 ep765 (@Enclosure.Complex.IsNear.re_isNear qz364 Bool.false 1 13824 0 1 Bool.false 0 1 0 1 qz367)

noncomputable def ep772 := @ep716 1 (@ep717 Bool.false 6361 19200 0 1 (BSN.bern_sum_succ qz14 24 0 1 1 rfl rfl) (ep746 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep747 (@ep748 1 1092432667 1092432667 265420800000 0 1 (ep763 rfl) (ep766 rfl) rfl rfl) (@ep767 1 2314964384929 2314964384929 26542080000000 0 1 (ep769 rfl) (ep771 rfl) rfl rfl)) rfl rfl rfl rfl

noncomputable def ep773 := ep710 (ep713 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep714 Bool.false 11108410784929 26542080000000 0 1 (BSN.bern_sum_succ qz14 24 1 2 3 rfl rfl) (ep772 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep774 := @Enclosure.Real.IsNear.mulLit_tf (Complex.im qz45) (Complex.im (@HAdd.hAdd Complex Complex Complex qz15 qz46 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz49 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))))) 55970401905 274877906944 5500936968005 35869092955029504 1614147770252781731881

noncomputable def ep775 := @ep774 9665852869509120000000 0 1 ep692 ep363 ep693 ep694 (@Enclosure.Complex.IsNear.im_isNear qz45 Bool.true 3936907953 274877906944 5437491199877 35869092955029504 Bool.true 55970401905 274877906944 5500936968005 35869092955029504 (ep697 ep706))

noncomputable def ep776 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz15 qz46 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz49 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1))))) Bool.false 48767504484710830963 96658528695091200000 0 1 Bool.false

noncomputable def ep777 := nat_lit 706083466002821468957269172177

noncomputable def ep778 := nat_lit 295214378399924806924369920000000

noncomputable def ep779 := nat_lit 8776914296050582266882604794178637

noncomputable def ep780 := @Enclosure.Real.IsNear.addLit_tt (@HMul.hMul Real Real Real qz0 (Complex.re qz45) (Complex.im (@HAdd.hAdd Complex Complex Complex qz15 qz46 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz49 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 (Complex.im qz45) (Complex.re (@HAdd.hAdd Complex Complex Complex qz15 qz46 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz49 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1))))))) ep777 ep778 ep779

noncomputable def ep781 := nat_lit 60656373909181225260125070767

noncomputable def ep782 := nat_lit 590428756799849613848739840000

noncomputable def ep783 := nat_lit 53653393651459087671357858867763

noncomputable def ep784 := nat_lit 693410750132122583646623194152960000

noncomputable def ep785 := nat_lit 18323525702621327288841271228904702163258498478417568071680000

noncomputable def ep786 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re qz45) (Complex.im (@HAdd.hAdd Complex Complex Complex qz15 qz46 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz49 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))))) 3936907953 274877906944 5437491199877 35869092955029504 1614147770252781731881

noncomputable def ep787 := @ep786 9665852869509120000000 0 1 ep777 ep778 ep779 ep561 (@Enclosure.Complex.IsNear.re_isNear qz45 Bool.true 3936907953 274877906944 5437491199877 35869092955029504 Bool.true 55970401905 274877906944 5500936968005 35869092955029504 (ep697 ep706))

noncomputable def ep788 := @Enclosure.Real.IsNear.mulLit_tf (Complex.im qz45) (Complex.re (@HAdd.hAdd Complex Complex Complex qz15 qz46 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz49 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))))) 55970401905 274877906944 5500936968005 35869092955029504 48767504484710830963

noncomputable def ep789 := @ep788 96658528695091200000 0 1 ep781 ep782 ep783 ep784 (@Enclosure.Complex.IsNear.im_isNear qz45 Bool.true 3936907953 274877906944 5437491199877 35869092955029504 Bool.true 55970401905 274877906944 5500936968005 35869092955029504 (ep697 ep706))

noncomputable abbrev qz915 := (ep773 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep790 := @ep686 ep566 ep559 ep567 ep561 (@ep690 ep691 ep692 ep363 ep693 ep694 ep695 ep564 ep363 ep565 ep365 (ep707 (@ep708 1614147770252781731881 9665852869509120000000 0 1 qz915) rfl) (ep775 (@ep776 1614147770252781731881 9665852869509120000000 0 1 qz915) rfl) rfl rfl) (@ep780 ep561 ep781 ep782 ep783 ep784 ep785 ep566 ep559 ep567 ep561 (ep787 (@ep776 1614147770252781731881 9665852869509120000000 0 1 qz915) rfl) (ep789 (@ep708 1614147770252781731881 9665852869509120000000 0 1 qz915) rfl) rfl rfl)

noncomputable def ep791 := @ep570 ep560 ep561 (@ep571 2989091079585792 (BSN.head_sum_c_eq qz14 24) (ep572 (BSN.head_sum_c_succ qz14 23 24 rfl rfl) (ep685 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep790 rfl rfl rfl

noncomputable def ep792 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz14 2 24) Bool.false ep362 ep363 ep364 ep365 Bool.false ep558 ep559 ep560 ep561 (@ep562 ep365 Bool.false ep558 ep559 ep560 ep561 (BSN.zetaApproximant_eq_folded' qz14 2 24 rfl) (ep791 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep793 := @Enclosure.Real.IsNear.mulLit_ff (Real.sin (@HSub.hSub Real Real Real qz326 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz23 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz24 (@Nat.cast Complex Complex.instNatCast j))))) qz327)) (Complex.im (zetaApproximant qz14 2 24)) 33 262144 132539

noncomputable def ep794 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz326 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz23 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz24 (@Nat.cast Complex Complex.instNatCast j))))) qz327)) Bool.false 66 524288 132539

noncomputable def ep795 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz326 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz23 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz24 (@Nat.cast Complex Complex.instNatCast j))))) qz327) qz868 Bool.false 42824649 524288 1

noncomputable def ep796 := BSN.sin_dyadic_bound_f 136072 1073741824 1 0 524288 261237 0 1 1 0 1 1 66 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 136072) qz275 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 136072) qz276 0 0 rfl) rfl rfl

noncomputable def ep797 := @ep795 2048 Bool.false 66 524288 1 130491 (@ep372 42824649 524288 1 2048 ep555 rfl) (Enclosure.sfrac_false_div 42824649 524288) (BSN.sin_reduce0 qz868 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9575258463139790848) qz282) 226375608064910080 72057594037927936 Bool.false 66 524288 13 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q0 42824649 524288 226375608064910080 72057594037927936 13 9575258463139790848 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 66 524288 9575258463139790848 75557863725914323419136 136072 1073741824 261237 260982 (ep796 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep798 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz14 2 24) Bool.false ep362 ep363 ep364 ep365 Bool.false ep558 ep559 ep560 ep561 (@ep562 ep365 Bool.false ep558 ep559 ep560 ep561 (BSN.zetaApproximant_eq_folded' qz14 2 24 rfl) (ep791 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow28.d14 : Enclosure.Real.IsNear (hardyZApproximantEM 2 24 qz11) Bool.false ep345 ep346 ep347 ep348 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 2 24 qz11) ep349 Bool.false ep345 ep346 ep347 ep348 (@Eq.refl Real ep349) (@ep350 Bool.false ep345 ep346 ep347 ep348 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz326 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz23 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz24 (@Nat.cast Complex Complex.instNatCast j))))) qz327) (zetaApproximant qz14 2 24)) (@ep352 ep353 ep354 ep355 ep356 ep357 ep358 ep359 ep360 ep345 ep346 ep347 ep348 (@ep361 267245568 ep362 ep363 ep364 ep365 ep351 ep353 ep354 ep355 (@ep366 267245568 524287 524288 132539 267245568 (ep557 rfl rfl) rfl) ep792 rfl) (@ep793 267245568 ep558 ep559 ep560 ep561 ep356 ep357 ep358 ep359 (@ep794 267245568 33 262144 132539 267245568 (ep797 rfl rfl) rfl) ep798 rfl) rfl rfl))

noncomputable abbrev qz605 := (@HAdd.hAdd Complex Complex Complex qz811 (@HAdd.hAdd Complex Complex Complex qz811 qz812 (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I (@HDiv.hDiv Complex Complex Complex qz813 (↑(Enclosure.sfrac Bool.false 97714 1000)) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 4))

noncomputable abbrev qz368 := (@HPow.hPow Complex Nat Complex qz541 qz605 3)

noncomputable abbrev qz53 := qz368

noncomputable def ep799 := Enclosure.Complex.IsNear qz53 Bool.true 121430266399 4000000 0 1 Bool.true 113974535391293 1000000000 0 1

noncomputable abbrev qz369 := qz605

noncomputable abbrev qz54 := (@HPow.hPow Complex Nat Complex qz256 qz369 2)

noncomputable abbrev qz55 := qz369

noncomputable def ep800 := @Enclosure.Complex.IsNear.of_eq qz53 (@HMul.hMul Complex Complex Complex qz3 qz54 qz55) Bool.true 121430266399 4000000 0 1 Bool.true 113974535391293 1000000000

noncomputable def ep801 := @Enclosure.Complex.IsNear.mul qz54 qz55 Bool.true 121430266399 4000000 0 1 Bool.true 113974535391293 1000000000 0

noncomputable abbrev qz56 := (Complex.re qz369)

noncomputable abbrev qz57 := (Complex.im qz369)

noncomputable def ep802 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re qz54) qz56) (@HMul.hMul Real Real Real qz0 (Complex.im qz54) qz57) 40272047133 4000000 0 1 40579109633 2000000

noncomputable def ep803 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re qz54) qz56 2368943949 1000000 0 1 17000 4000 0 1

noncomputable def ep804 := @Enclosure.Complex.IsNear.re_isNear qz54 Bool.true 2368943949 1000000 0 1 Bool.false 830569 2000 0 1

noncomputable abbrev qz370 := (@HPow.hPow Complex Nat Complex qz541 qz605 1)

noncomputable abbrev qz58 := qz370

noncomputable def ep805 := @Enclosure.Complex.IsNear.of_eq qz54 (@HMul.hMul Complex Complex Complex qz3 qz58 qz55) Bool.true 2368943949 1000000 0 1 Bool.false 830569 2000

noncomputable def ep806 := @Enclosure.Complex.IsNear.mul qz58 qz55 Bool.true 2368943949 1000000 0 1 Bool.false 830569 2000 0

noncomputable abbrev qz59 := (Complex.re qz370)

noncomputable abbrev qz60 := (Complex.im qz370)

noncomputable def ep807 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz59 qz56) (@HMul.hMul Real Real Real qz0 qz60 qz57) 289 16 0 1 2387006449 1000000

noncomputable def ep808 := @Enclosure.Real.IsNear.mulLit_ff qz59 qz56 17000 4000 0 1 17000 4000 0 1

noncomputable def ep809 := @Enclosure.Complex.IsNear.re_isNear qz58 Bool.false 17000 4000 0 1 Bool.false 195428 4000 0 1

noncomputable def ep810 := @Enclosure.Complex.IsNear.of_eq qz58 qz55 Bool.false 17000 4000 0 1 Bool.false 195428 4000 0

noncomputable abbrev qz371 := (Enclosure.sfrac Bool.false 97714 1000)

noncomputable abbrev qz61 := qz371

noncomputable abbrev qz372 := (Enclosure.sfrac Bool.false 195428 4000)

noncomputable abbrev qz606 := (Complex.mk (Enclosure.sfrac Bool.false 17000 4000) qz372)

noncomputable def ep811 := @Enclosure.Complex.IsNear.of_eq qz55 qz606 Bool.false 17000 4000 0 1 Bool.false 195428 4000 0 1 (BSN.w_shift_mk qz61 Bool.false 97714 1000 4 (@Eq.refl Real qz61) rfl)

noncomputable abbrev qz62 := (@ep810 1 (BSN.pow_one_c qz369) (ep811 (@Enclosure.Complex.IsNear.mk qz544 qz372 Bool.false 17000 4000 0 1 Bool.false 195428 4000 0 1 qz815 (Enclosure.Real.IsNear.const Bool.false 195428 4000))))

noncomputable abbrev qz63 := (ep811 (@Enclosure.Complex.IsNear.mk qz544 qz372 Bool.false 17000 4000 0 1 Bool.false 195428 4000 0 1 qz815 (Enclosure.Real.IsNear.const Bool.false 195428 4000)))

noncomputable abbrev qz607 := (@Enclosure.Complex.IsNear.re_isNear qz55 Bool.false 17000 4000 0 1 Bool.false 195428 4000 0 1 qz63)

noncomputable def ep812 := @ep808 289 16 0 1 (ep809 qz62) qz607

noncomputable def ep813 := @Enclosure.Real.IsNear.mulLit_ff qz60 qz57 195428 4000 0 1 195428 4000 0 1

noncomputable def ep814 := @Enclosure.Complex.IsNear.im_isNear qz58 Bool.false 17000 4000 0 1 Bool.false 195428 4000 0 1

noncomputable abbrev qz608 := (@Enclosure.Complex.IsNear.im_isNear qz55 Bool.false 17000 4000 0 1 Bool.false 195428 4000 0 1 qz63)

noncomputable def ep815 := @ep813 2387006449 1000000 0 1 (ep814 qz62) qz608

noncomputable def ep816 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz59 qz57) (@HMul.hMul Real Real Real qz0 qz60 qz56) 830569 4000 0 1 830569 4000

noncomputable def ep817 := @Enclosure.Real.IsNear.mulLit_ff qz59 qz57 17000 4000 0 1 195428 4000 0 1

noncomputable def ep818 := @ep817 830569 4000 0 1 (ep809 qz62) qz608

noncomputable def ep819 := @Enclosure.Real.IsNear.mulLit_ff qz60 qz56 195428 4000 0 1 17000 4000 0 1

noncomputable def ep820 := @ep819 830569 4000 0 1 (ep814 qz62) qz607

noncomputable abbrev qz609 := (@ep805 0 1 (BSN.pow_succ_c qz55 1 2 rfl) (@ep806 1 (@ep807 0 1 37903103184 2368943949 1000000 0 1 (ep812 rfl) (ep815 rfl) rfl rfl) (@ep816 0 1 6644552000 830569 2000 0 1 (ep818 rfl) (ep820 rfl) rfl rfl)))

noncomputable def ep821 := @ep803 40272047133 4000000 0 1 (ep804 qz609) qz607

noncomputable def ep822 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz54) qz57 830569 2000 0 1 195428 4000 0 1

noncomputable def ep823 := @Enclosure.Complex.IsNear.im_isNear qz54 Bool.true 2368943949 1000000 0 1 Bool.false 830569 2000 0 1

noncomputable def ep824 := @ep822 40579109633 2000000 0 1 (ep823 qz609) qz608

noncomputable def ep825 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re qz54) qz57) (@HMul.hMul Real Real Real qz0 (Complex.im qz54) qz56) 115739494516293 1000000000 0 1 14119673 8000

noncomputable def ep826 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re qz54) qz57 2368943949 1000000 0 1 195428 4000 0 1

noncomputable def ep827 := @ep826 115739494516293 1000000000 0 1 (ep804 qz609) qz608

noncomputable def ep828 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz54) qz56 830569 2000 0 1 17000 4000 0 1

noncomputable def ep829 := @ep828 14119673 8000 0 1 (ep823 qz609) qz607

theorem EMRow28.d15 : ep799 := @ep800 0 1 (BSN.pow_succ_c qz55 2 3 rfl) (@ep801 1 (@ep802 0 1 242860532798000000 121430266399 4000000 0 1 (ep821 rfl) (ep824 rfl) rfl rfl) (@ep825 0 1 911796283130344000 113974535391293 1000000000 0 1 (ep827 rfl) (ep829 rfl) rfl rfl))

noncomputable abbrev qz373 := (@HAdd.hAdd Complex Complex Complex qz548 qz549 (@HMul.hMul Complex Complex Complex qz543 Complex.I ↑(Enclosure.sfrac Bool.false 97714 1000)))

noncomputable abbrev qz64 := qz373

noncomputable abbrev qz65 := (@Neg.neg Complex Complex.instNeg qz373)

noncomputable abbrev qz916 := (@HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast 8) qz65)

noncomputable def ep830 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 9) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 8) qz916) Bool.false 227423633195 137438953472 15344026482061 5978182159171584 Bool.false 4447422973 34359738368 7676911372955 2989091079585792

noncomputable def ep831 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 8) qz916 Bool.false 506290503691 274877906944 27466852169507 11956364318343168 Bool.false 59015349907 137438953472 13739584194277 5978182159171584 Bool.true

noncomputable abbrev qz917 := (@HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast 7) qz65)

noncomputable def ep832 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 8) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 7) qz917) Bool.false 506290503691 274877906944 27466852169507 11956364318343168 Bool.false 59015349907 137438953472 13739584194277 5978182159171584

noncomputable def ep833 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 7) qz917 Bool.false 257087605649 137438953472 36064516157479 17934546477514752 Bool.false 221625362139 274877906944 72102955645973 35869092955029504 Bool.true

noncomputable abbrev qz918 := (@HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast 6) qz65)

noncomputable def ep834 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 7) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 6) qz918) Bool.false 257087605649 137438953472 36064516157479 17934546477514752 Bool.false 221625362139 274877906944 72102955645973 35869092955029504

noncomputable def ep835 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 6) qz918 Bool.false 110013483419 68719476736 7624377442325 4483636619378688 Bool.false 68685204031 137438953472 15240691193305 8967273238757376 Bool.false

noncomputable def ep836 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 6) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 5) (@HPow.hPow Complex Complex Complex qz16 qz18 qz65)) Bool.false 110013483419 68719476736 7624377442325 4483636619378688 Bool.false 68685204031 137438953472 15240691193305 8967273238757376

noncomputable def ep837 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 5) (@HPow.hPow Complex Complex Complex qz16 qz18 qz65) Bool.false 319217755367 274877906944 16249975733203 11956364318343168 Bool.false 159958448115 274877906944 16257450431671 11956364318343168 Bool.false

noncomputable def ep838 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 5) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 4) (@HPow.hPow Complex Complex Complex qz16 qz19 qz65)) Bool.false 319217755367 274877906944 16249975733203 11956364318343168 Bool.false 159958448115 274877906944 16257450431671 11956364318343168

noncomputable def ep839 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 4) (@HPow.hPow Complex Complex Complex qz16 qz19 qz65) Bool.false 27954712331 17179869184 8767753628947 8967273238757376 Bool.false 13756687347 34359738368 17566170946511 17934546477514752 Bool.true

noncomputable def ep840 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 4) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 3) (@HPow.hPow Complex Complex Complex qz16 qz551 qz65)) Bool.false 27954712331 17179869184 8767753628947 8967273238757376 Bool.false 13756687347 34359738368 17566170946511 17934546477514752

noncomputable def ep841 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 3) (@HPow.hPow Complex Complex Complex qz16 qz551 qz65) Bool.false 38848003241 34359738368 4807944763219 8967273238757376 Bool.false 373091391 536870912 9670488396239 17934546477514752 Bool.false

noncomputable def ep842 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 3) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 2) (@HPow.hPow Complex Complex Complex qz16 qz552 qz65)) Bool.false 38848003241 34359738368 4807944763219 8967273238757376 Bool.false 373091391 536870912 9670488396239 17934546477514752

noncomputable def ep843 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 2) (@HPow.hPow Complex Complex Complex qz16 qz552 qz65) Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable def ep844 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz265) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz64)

noncomputable abbrev qz374 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log qz810))

noncomputable def ep845 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz552 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz266 (Real.cos qz374)) (@HMul.hMul Real Real Real qz0 qz266 (@Neg.neg Real Real.instNeg (Real.sin qz374)))) Bool.false 4488264873 34359738368 4807944763219 8967273238757376 Bool.false 373091391 536870912 9670488396239 17934546477514752 (BSN.cpow_neg_s_mk qz61 97714 1000 2 (@Eq.refl Real qz61) rfl)

noncomputable def ep846 := nat_lit 1584145337803162067359343143210000

noncomputable def ep847 := BSN.sin_dyadic_bound_f 199502690 1073741824 2 1 524288 261237 ep846 ep92 ep846 ep846 ep93 ep846 96853 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 199502690) qz275 0 1 ep846 ep92 ep846 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 199502690) qz276 0 1 ep846 ep93 ep846 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz375 := (Enclosure.Real.IsNear.const Bool.false 97714 1000)

noncomputable abbrev qz919 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 35510049) qz280)

noncomputable abbrev qz920 := (@Nat.cast Real Real.instNatCast 14038753769027962667008)

noncomputable def ep848 := @Enclosure.Real.IsNear.cos_image qz374 qz919 Bool.false 35510049 524288 393 524288 Bool.false 96853 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz374 Bool.false 1109689041 16384000 48857 65245500 35510049 524288 393 524288 (@Enclosure.Real.IsNear.mulLit_ff qz61 qz272 97714 1000 0 1 181704 262144 1 130491 1109689041 16384000 48857 65245500 qz375 qz554 rfl) rfl) (Enclosure.sfrac_false_div 35510049 524288) (BSN.cos_reduce3 qz919 (@HDiv.hDiv Real Real Real qz1 qz920 qz282) 226375608064910080 72057594037927936 Bool.false 96853 524288 10 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q3 35510049 524288 226375608064910080 72057594037927936 10 14038753769027962667008 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 96853 524288 14038753769027962667008 75557863725914323419136 199502690 1073741824 261237 260982 (ep847 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep849 := BSN.cos_dyadic_bound_f 199502690 1073741824 2 1 524288 261237 ep846 ep88 ep846 ep846 ep89 ep846 515264 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 199502690) qz269 0 1 ep846 ep88 ep846 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 199502690) qz270 0 1 ep846 ep89 ep846 rfl rfl rfl rfl) rfl rfl

noncomputable def ep850 := @Enclosure.Real.IsNear.sin_image qz374 qz919 Bool.false 35510049 524288 393 524288 Bool.true 515264 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz374 Bool.false 1109689041 16384000 48857 65245500 35510049 524288 393 524288 (@Enclosure.Real.IsNear.mulLit_ff qz61 qz272 97714 1000 0 1 181704 262144 1 130491 1109689041 16384000 48857 65245500 qz375 qz554 rfl) rfl) (Enclosure.sfrac_false_div 35510049 524288) (BSN.sin_reduce3 qz919 (@HDiv.hDiv Real Real Real qz1 qz920 qz282) 226375608064910080 72057594037927936 Bool.false 515264 524288 10 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q3 35510049 524288 226375608064910080 72057594037927936 10 14038753769027962667008 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 515264 524288 14038753769027962667008 75557863725914323419136 199502690 1073741824 261237 260982 (ep849 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep851 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz266 (Real.cos qz374)) (@HMul.hMul Real Real Real qz0 qz266 (@Neg.neg Real Real.instNeg (Real.sin qz374))) Bool.false 4488264873 34359738368 4807944763219 8967273238757376 Bool.false 373091391 536870912 9670488396239 17934546477514752 (@Enclosure.Real.IsNear.mulLit_ff qz266 (Real.cos qz374) 46341 65536 1 262144 96853 524288 51807251 68414865408 4488264873 34359738368 4807944763219 8967273238757376 qz555 (@Enclosure.Real.IsNear.recentre' (Real.cos qz374) Bool.false 96853 524288 51807251 68414865408 96853 524288 51807251 68414865408 (ep848 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz266 (@Neg.neg Real Real.instNeg (Real.sin qz374)) 46341 65536 1 262144 8051 8192 51807251 68414865408 373091391 536870912 9670488396239 17934546477514752 qz555 (@Enclosure.Real.IsNear.neg (Real.sin qz374) Bool.true 8051 8192 51807251 68414865408 (@Enclosure.Real.IsNear.recentre' (Real.sin qz374) Bool.true 515264 524288 51807251 68414865408 8051 8192 51807251 68414865408 (ep850 rfl rfl) rfl)) rfl)

noncomputable def ep852 := @ep843 4488264873 34359738368 4807944763219 8967273238757376 Bool.false 373091391 536870912 9670488396239 17934546477514752 Bool.false 38848003241 38848003241 34359738368 4807944763219 8967273238757376 Bool.false 373091391 373091391 536870912 9670488396239 17934546477514752 (ep844 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz265 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz277)) (ep845 ep851) rfl rfl

noncomputable abbrev qz376 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 3 1)))

noncomputable def ep853 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz551 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz278 (Real.cos qz376)) (@HMul.hMul Real Real Real qz0 qz278 (@Neg.neg Real Real.instNeg (Real.sin qz376)))) Bool.false 17061421421 34359738368 20624004509 46704548118528 Bool.true 10121161677 34359738368 5140418327 11676137029632 (BSN.cpow_neg_s_mk qz61 97714 1000 3 (@Eq.refl Real qz61) rfl)

noncomputable def ep854 := nat_lit 109238294833900481893028505350270881

noncomputable def ep855 := BSN.cos_dyadic_bound_f 574901879 1073741824 2 1 524288 261237 ep854 ep88 ep854 ep854 ep89 ep854 450916 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 574901879) qz269 0 1 ep854 ep88 ep854 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 574901879) qz270 0 1 ep854 ep89 ep854 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz921 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 56282091) qz280)

noncomputable def ep856 := @Enclosure.Real.IsNear.cos_image qz376 qz921 Bool.false 56282091 524288 197 262144 Bool.false 450916 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz376 Bool.false 7035261429 65536000 48857 65245500 56282091 524288 197 262144 (@Enclosure.Real.IsNear.mulLit_ff qz61 qz281 97714 1000 0 1 287994 262144 1 130491 7035261429 65536000 48857 65245500 qz375 qz556 rfl) rfl) (Enclosure.sfrac_false_div 56282091 524288) (BSN.cos_reduce0 qz921 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 40455123290215921221632) qz282) 226375608064910080 72057594037927936 Bool.false 450916 524288 17 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q0 56282091 524288 226375608064910080 72057594037927936 17 40455123290215921221632 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 450916 524288 40455123290215921221632 75557863725914323419136 574901879 1073741824 261237 260982 (ep855 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep857 := BSN.sin_dyadic_bound_f 574901879 1073741824 2 1 524288 261237 ep854 ep92 ep854 ep854 ep93 ep854 267492 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 574901879) qz275 0 1 ep854 ep92 ep854 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 574901879) qz276 0 1 ep854 ep93 ep854 rfl rfl rfl rfl) rfl rfl

noncomputable def ep858 := @Enclosure.Real.IsNear.sin_image qz376 qz921 Bool.false 56282091 524288 197 262144 Bool.false 267492 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz376 Bool.false 7035261429 65536000 48857 65245500 56282091 524288 197 262144 (@Enclosure.Real.IsNear.mulLit_ff qz61 qz281 97714 1000 0 1 287994 262144 1 130491 7035261429 65536000 48857 65245500 qz375 qz556 rfl) rfl) (Enclosure.sfrac_false_div 56282091 524288) (BSN.sin_reduce0 qz921 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 40455123290215921221632) qz282) 226375608064910080 72057594037927936 Bool.false 267492 524288 17 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q0 56282091 524288 226375608064910080 72057594037927936 17 40455123290215921221632 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 267492 524288 40455123290215921221632 75557863725914323419136 574901879 1073741824 261237 260982 (ep857 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep859 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz278 (Real.cos qz376)) (@HMul.hMul Real Real Real qz0 qz278 (@Neg.neg Real Real.instNeg (Real.sin qz376))) Bool.false 17061421421 34359738368 20624004509 46704548118528 Bool.true 10121161677 34359738368 5140418327 11676137029632 (@Enclosure.Real.IsNear.mulLit_ff qz278 (Real.cos qz376) 151349 262144 1 262144 112729 131072 25968871 34207432704 17061421421 34359738368 20624004509 46704548118528 qz557 (@Enclosure.Real.IsNear.recentre' (Real.cos qz376) Bool.false 450916 524288 25968871 34207432704 112729 131072 25968871 34207432704 (ep856 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz278 (@Neg.neg Real Real.instNeg (Real.sin qz376)) 151349 262144 1 262144 66873 131072 25968871 34207432704 10121161677 34359738368 5140418327 11676137029632 qz557 (@Enclosure.Real.IsNear.neg (Real.sin qz376) Bool.false 66873 131072 25968871 34207432704 (@Enclosure.Real.IsNear.recentre' (Real.sin qz376) Bool.false 267492 524288 25968871 34207432704 66873 131072 25968871 34207432704 (ep858 rfl rfl) rfl)) rfl)

noncomputable def ep860 := @ep841 17061421421 34359738368 20624004509 46704548118528 Bool.true 10121161677 34359738368 5140418327 11676137029632 Bool.false 1921033203691726831616 27954712331 17179869184 8767753628947 8967273238757376 Bool.false 7385565282082750464 13756687347 34359738368 17566170946511 17934546477514752 (ep842 (BSN.head_sum_c_succ qz64 2 3 rfl rfl) (ep852 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep853 ep859) rfl rfl

noncomputable abbrev qz377 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 4 1)))

noncomputable def ep861 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz19 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz283 (Real.cos qz377)) (@HMul.hMul Real Real Real qz0 qz283 (@Neg.neg Real Real.instNeg (Real.sin qz377)))) Bool.true 128057641929 274877906944 13678912683821 35869092955029504 Bool.false 49904949339 274877906944 13640009401991 35869092955029504 (BSN.cpow_neg_s_mk qz61 97714 1000 4 (@Eq.refl Real qz61) rfl)

noncomputable def ep862 := nat_lit 25346325404850593077749490291360000

noncomputable def ep863 := BSN.cos_dyadic_bound_f 399005380 1073741824 2 1 524288 261237 ep862 ep88 ep862 ep862 ep89 ep862 488503 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 399005380) qz269 0 1 ep862 ep88 ep862 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 399005380) qz270 0 1 ep862 ep89 ep862 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz922 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 35510049) qz271)

noncomputable def ep864 := @Enclosure.Real.IsNear.cos_image qz377 qz922 Bool.false 35510049 262144 197 262144 Bool.true 488503 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz377 Bool.false 1109689041 8192000 48857 65245500 35510049 262144 197 262144 (@Enclosure.Real.IsNear.mulLit_ff qz61 qz286 97714 1000 0 1 363408 262144 1 130491 1109689041 8192000 48857 65245500 qz375 qz558 rfl) rfl) (Enclosure.sfrac_false_div 35510049 262144) (BSN.cos_reduce2 qz922 (@HDiv.hDiv Real Real Real qz1 qz920 qz274) 226375608064910080 72057594037927936 Bool.false 488503 524288 21 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q2 35510049 262144 226375608064910080 72057594037927936 21 14038753769027962667008 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 488503 524288 14038753769027962667008 37778931862957161709568 399005380 1073741824 261237 260982 (ep863 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep865 := BSN.sin_dyadic_bound_f 399005380 1073741824 2 1 524288 261237 ep862 ep92 ep862 ep862 ep93 ep862 190373 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 399005380) qz275 0 1 ep862 ep92 ep862 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 399005380) qz276 0 1 ep862 ep93 ep862 rfl rfl rfl rfl) rfl rfl

noncomputable def ep866 := @Enclosure.Real.IsNear.sin_image qz377 qz922 Bool.false 35510049 262144 197 262144 Bool.true 190373 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz377 Bool.false 1109689041 8192000 48857 65245500 35510049 262144 197 262144 (@Enclosure.Real.IsNear.mulLit_ff qz61 qz286 97714 1000 0 1 363408 262144 1 130491 1109689041 8192000 48857 65245500 qz375 qz558 rfl) rfl) (Enclosure.sfrac_false_div 35510049 262144) (BSN.sin_reduce2 qz922 (@HDiv.hDiv Real Real Real qz1 qz920 qz274) 226375608064910080 72057594037927936 Bool.false 190373 524288 21 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q2 35510049 262144 226375608064910080 72057594037927936 21 14038753769027962667008 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 190373 524288 14038753769027962667008 37778931862957161709568 399005380 1073741824 261237 260982 (ep865 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep867 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz283 (Real.cos qz377)) (@HMul.hMul Real Real Real qz0 qz283 (@Neg.neg Real Real.instNeg (Real.sin qz377))) Bool.true 128057641929 274877906944 13678912683821 35869092955029504 Bool.false 49904949339 274877906944 13640009401991 35869092955029504 (@Enclosure.Real.IsNear.mulLit_ft qz283 (Real.cos qz377) 262143 524288 1 524288 488503 524288 25968871 34207432704 128057641929 274877906944 13678912683821 35869092955029504 qz560 (@Enclosure.Real.IsNear.recentre' (Real.cos qz377) Bool.true 488503 524288 25968871 34207432704 488503 524288 25968871 34207432704 (ep864 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz283 (@Neg.neg Real Real.instNeg (Real.sin qz377)) 262143 524288 1 524288 190373 524288 25968871 34207432704 49904949339 274877906944 13640009401991 35869092955029504 qz560 (@Enclosure.Real.IsNear.neg (Real.sin qz377) Bool.true 190373 524288 25968871 34207432704 (@Enclosure.Real.IsNear.recentre' (Real.sin qz377) Bool.true 190373 524288 25968871 34207432704 190373 524288 25968871 34207432704 (ep866 rfl rfl) rfl)) rfl)

noncomputable def ep868 := @ep839 128057641929 274877906944 13678912683821 35869092955029504 Bool.false 49904949339 274877906944 13640009401991 35869092955029504 Bool.false 5484119278415173910528 319217755367 274877906944 16249975733203 11956364318343168 Bool.false 5496130426982702776320 159958448115 274877906944 16257450431671 11956364318343168 (ep840 (BSN.head_sum_c_succ qz64 3 4 rfl rfl) (ep860 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep861 ep867) rfl rfl

noncomputable abbrev qz378 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 5 1)))

noncomputable def ep869 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz18 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz287 (Real.cos qz378)) (@HMul.hMul Real Real Real qz0 qz287 (@Neg.neg Real Real.instNeg (Real.sin qz378)))) Bool.false 120836178309 274877906944 12245092338991 35869092955029504 Bool.true 22588040053 274877906944 12190413478207 35869092955029504 (BSN.cpow_neg_s_mk qz61 97714 1000 5 (@Eq.refl Real qz61) rfl)

noncomputable def ep870 := nat_lit 1550213636884290321875673434600625

noncomputable def ep871 := BSN.cos_dyadic_bound_f 198425685 1073741824 2 1 524288 261237 ep870 ep88 ep870 ep870 ep89 ep870 515361 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 198425685) qz269 0 1 ep870 ep88 ep870 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 198425685) qz270 0 1 ep870 ep89 ep870 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz923 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 41225927) qz271)

noncomputable def ep872 := @Enclosure.Real.IsNear.cos_image qz378 qz923 Bool.false 41225927 262144 197 262144 Bool.false 515361 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz378 Bool.false 1288310233 8192000 48857 65245500 41225927 262144 197 262144 (@Enclosure.Real.IsNear.mulLit_ff qz61 qz289 97714 1000 0 1 421904 262144 1 130491 1288310233 8192000 48857 65245500 qz375 qz562 rfl) rfl) (Enclosure.sfrac_false_div 41225927 262144) (BSN.cos_reduce0 qz923 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6981483149725840441344) qz274) 226375608064910080 72057594037927936 Bool.false 515361 524288 25 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q0 41225927 262144 226375608064910080 72057594037927936 25 6981483149725840441344 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 515361 524288 6981483149725840441344 37778931862957161709568 198425685 1073741824 261237 260982 (ep871 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep873 := BSN.sin_dyadic_bound_f 198425685 1073741824 2 1 524288 261237 ep870 ep92 ep870 ep870 ep93 ep870 96337 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 198425685) qz275 0 1 ep870 ep92 ep870 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 198425685) qz276 0 1 ep870 ep93 ep870 rfl rfl rfl rfl) rfl rfl

noncomputable def ep874 := @Enclosure.Real.IsNear.sin_image qz378 qz923 Bool.false 41225927 262144 197 262144 Bool.false 96337 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz378 Bool.false 1288310233 8192000 48857 65245500 41225927 262144 197 262144 (@Enclosure.Real.IsNear.mulLit_ff qz61 qz289 97714 1000 0 1 421904 262144 1 130491 1288310233 8192000 48857 65245500 qz375 qz562 rfl) rfl) (Enclosure.sfrac_false_div 41225927 262144) (BSN.sin_reduce0 qz923 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6981483149725840441344) qz274) 226375608064910080 72057594037927936 Bool.false 96337 524288 25 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q0 41225927 262144 226375608064910080 72057594037927936 25 6981483149725840441344 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 96337 524288 6981483149725840441344 37778931862957161709568 198425685 1073741824 261237 260982 (ep873 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep875 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz287 (Real.cos qz378)) (@HMul.hMul Real Real Real qz0 qz287 (@Neg.neg Real Real.instNeg (Real.sin qz378))) Bool.false 120836178309 274877906944 12245092338991 35869092955029504 Bool.true 22588040053 274877906944 12190413478207 35869092955029504 (@Enclosure.Real.IsNear.mulLit_ff qz287 (Real.cos qz378) 234469 524288 1 524288 515361 524288 25968871 34207432704 120836178309 274877906944 12245092338991 35869092955029504 qz563 (@Enclosure.Real.IsNear.recentre' (Real.cos qz378) Bool.false 515361 524288 25968871 34207432704 515361 524288 25968871 34207432704 (ep872 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz287 (@Neg.neg Real Real.instNeg (Real.sin qz378)) 234469 524288 1 524288 96337 524288 25968871 34207432704 22588040053 274877906944 12190413478207 35869092955029504 qz563 (@Enclosure.Real.IsNear.neg (Real.sin qz378) Bool.false 96337 524288 25968871 34207432704 (@Enclosure.Real.IsNear.recentre' (Real.sin qz378) Bool.false 96337 524288 25968871 34207432704 96337 524288 25968871 34207432704 (ep874 rfl rfl) rfl)) rfl)

noncomputable def ep876 := @ep837 120836178309 274877906944 12245092338991 35869092955029504 Bool.true 22588040053 274877906944 12190413478207 35869092955029504 Bool.false 120961104231332675846144 110013483419 68719476736 7624377442325 4483636619378688 Bool.false 37760090244125743382528 68685204031 137438953472 15240691193305 8967273238757376 (ep838 (BSN.head_sum_c_succ qz64 4 5 rfl rfl) (ep868 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep869 ep875) rfl rfl

noncomputable abbrev qz379 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 6 1)))

noncomputable def ep877 := @Enclosure.Complex.IsNear.of_eq qz918 (Complex.mk (@HMul.hMul Real Real Real qz0 qz290 (Real.cos qz379)) (@HMul.hMul Real Real Real qz0 qz290 (@Neg.neg Real Real.instNeg (Real.sin qz379)))) Bool.false 37060638811 137438953472 5567006388179 17934546477514752 Bool.false 84254954077 274877906944 11140190872753 35869092955029504 (BSN.cpow_neg_s_mk qz61 97714 1000 6 (@Eq.refl Real qz61) rfl)

noncomputable def ep878 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz292 97714 1000 0 1 4034681531866359 2251799813685248 500000000130491 65245500000000000000 197122435602394701663 1125899906842624000 24428500006375398787 32622750000000000000000 qz375 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 500000000130491 65245500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz828) Bool.false 16922680887833197019136 9444732965739290427392 1000000000260982 130491000000000000000 4034681531866359 2251799813685248 500000000130491 65245500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 106290 262144 24973259072661432 36028797018963968 130491 1000000000000000 rfl rfl rfl rfl (ep148 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep879 := nat_lit 360202594983234061106762847900390625

noncomputable def ep880 := BSN.sin_dyadic_bound_f 774705625 1073741824 2 1 524288 261237 ep879 ep92 ep879 ep879 ep93 ep879 346298 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 774705625) qz275 0 1 ep879 ep92 ep879 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 774705625) qz276 0 1 ep879 ep93 ep879 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz924 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 91792287) qz280)

noncomputable def ep881 := @Enclosure.Real.IsNear.cos_image qz379 qz924 Bool.false 91792287 524288 393 524288 Bool.false 346298 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz379 Bool.false 197122435602394701663 1125899906842624000 24428500006375398787 32622750000000000000000 91792287 524288 393 524288 (ep878 rfl) rfl) (Enclosure.sfrac_false_div 91792287 524288) (BSN.cos_reduce3 qz924 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 54515061991891034701824) qz282) 226375608064910080 72057594037927936 Bool.false 346298 524288 27 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q3 91792287 524288 226375608064910080 72057594037927936 27 54515061991891034701824 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 346298 524288 54515061991891034701824 75557863725914323419136 774705625 1073741824 261237 260982 (ep880 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep882 := nat_lit 804499253231663862348147287148897811629609505714427369725684922027587890625

noncomputable def ep883 := nat_lit 129745909432655755606370196433593771498013601101958192884922027587890625

noncomputable def ep884 := nat_lit 2413238267876126275533229121053826247345832489941078192791284922027587890625

noncomputable def ep885 := BSN.cos_dyadic_bound_f 774705625 1073741824 3 2 524288 261237 ep882 ep102 ep883 ep884 ep105 ep883 393643 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 774705625) qz269 0 2 ep882 ep102 ep883 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 774705625) qz270 0 2 ep884 ep105 ep883 rfl rfl rfl rfl) rfl rfl

noncomputable def ep886 := @Enclosure.Real.IsNear.sin_image qz379 qz924 Bool.false 91792287 524288 393 524288 Bool.true 393643 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz379 Bool.false 197122435602394701663 1125899906842624000 24428500006375398787 32622750000000000000000 91792287 524288 393 524288 (ep878 rfl) rfl) (Enclosure.sfrac_false_div 91792287 524288) (BSN.sin_reduce3 qz924 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 54515061991891034701824) qz282) 226375608064910080 72057594037927936 Bool.false 393643 524288 27 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q3 91792287 524288 226375608064910080 72057594037927936 27 54515061991891034701824 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 393643 524288 54515061991891034701824 75557863725914323419136 774705625 1073741824 261237 260982 (ep885 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep887 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz290 (Real.cos qz379)) (@HMul.hMul Real Real Real qz0 qz290 (@Neg.neg Real Real.instNeg (Real.sin qz379))) Bool.false 37060638811 137438953472 5567006388179 17934546477514752 Bool.false 84254954077 274877906944 11140190872753 35869092955029504 (@Enclosure.Real.IsNear.mulLit_ff qz290 (Real.cos qz379) 214039 524288 1 524288 173149 262144 51807251 68414865408 37060638811 137438953472 5567006388179 17934546477514752 qz564 (@Enclosure.Real.IsNear.recentre' (Real.cos qz379) Bool.false 346298 524288 51807251 68414865408 173149 262144 51807251 68414865408 (ep881 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz290 (@Neg.neg Real Real.instNeg (Real.sin qz379)) 214039 524288 1 524288 393643 524288 51807251 68414865408 84254954077 274877906944 11140190872753 35869092955029504 qz564 (@Enclosure.Real.IsNear.neg (Real.sin qz379) Bool.true 393643 524288 51807251 68414865408 (@Enclosure.Real.IsNear.recentre' (Real.sin qz379) Bool.true 393643 524288 51807251 68414865408 393643 524288 51807251 68414865408 (ep886 rfl rfl) rfl)) rfl)

noncomputable def ep888 := @ep835 37060638811 137438953472 5567006388179 17934546477514752 Bool.false 84254954077 274877906944 11140190872753 35869092955029504 Bool.false 17666925735510397681664 257087605649 137438953472 36064516157479 17934546477514752 Bool.false 30459957835237171396608 221625362139 274877906944 72102955645973 35869092955029504 (ep836 (BSN.head_sum_c_succ qz64 5 6 rfl rfl) (ep876 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep877 ep887) rfl rfl

noncomputable abbrev qz380 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 7 1)))

noncomputable def ep889 := @Enclosure.Complex.IsNear.of_eq qz917 (Complex.mk (@HMul.hMul Real Real Real qz0 qz293 (Real.cos qz380)) (@HMul.hMul Real Real Real qz0 qz293 (@Neg.neg Real Real.instNeg (Real.sin qz380)))) Bool.true 7884707607 274877906944 10271524193563 35869092955029504 Bool.true 103594662325 274877906944 10334549519689 35869092955029504 (BSN.cpow_neg_s_mk qz61 97714 1000 7 (@Eq.refl Real qz61) rfl)

noncomputable def ep890 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz295 97714 1000 0 1 4381792198794487 2251799813685248 500000000130491 65245500000000000000 214081221456502251359 1125899906842624000 24428500006375398787 32622750000000000000000 qz375 (BSN.isNear_log_sfrac 7 1 4381792198794487 2251799813685248 500000000130491 65245500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz831) Bool.false 18378568546572512002048 9444732965739290427392 1000000000260982 130491000000000000000 4381792198794487 2251799813685248 500000000130491 65245500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 146699 262144 24973259072661432 36028797018963968 130491 1000000000000000 rfl rfl rfl rfl (ep163 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep891 := BSN.sin_dyadic_bound_f 81566895 1073741824 1 0 524288 261237 0 1 1 0 1 1 39789 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 81566895) qz275 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 81566895) qz276 0 0 rfl) rfl rfl

noncomputable abbrev qz925 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 99689337) qz280)

noncomputable def ep892 := @Enclosure.Real.IsNear.cos_image qz380 qz925 Bool.false 99689337 524288 393 524288 Bool.true 39789 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz380 Bool.false 214081221456502251359 1125899906842624000 24428500006375398787 32622750000000000000000 99689337 524288 393 524288 (ep890 rfl) rfl) (Enclosure.sfrac_false_div 99689337 524288) (BSN.cos_reduce1 qz925 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 5739759974972888449024) qz282) 226375608064910080 72057594037927936 Bool.false 39789 524288 30 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q1 99689337 524288 226375608064910080 72057594037927936 30 5739759974972888449024 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 39789 524288 5739759974972888449024 75557863725914323419136 81566895 1073741824 261237 260982 (ep891 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep893 := nat_lit 44264516162453149571441478050625

noncomputable def ep894 := BSN.cos_dyadic_bound_f 81566895 1073741824 2 1 524288 261237 ep893 ep88 ep893 ep893 ep89 ep893 522775 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 81566895) qz269 0 1 ep893 ep88 ep893 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 81566895) qz270 0 1 ep893 ep89 ep893 rfl rfl rfl rfl) rfl rfl

noncomputable def ep895 := @Enclosure.Real.IsNear.sin_image qz380 qz925 Bool.false 99689337 524288 393 524288 Bool.false 522775 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz380 Bool.false 214081221456502251359 1125899906842624000 24428500006375398787 32622750000000000000000 99689337 524288 393 524288 (ep890 rfl) rfl) (Enclosure.sfrac_false_div 99689337 524288) (BSN.sin_reduce1 qz925 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 5739759974972888449024) qz282) 226375608064910080 72057594037927936 Bool.false 522775 524288 30 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q1 99689337 524288 226375608064910080 72057594037927936 30 5739759974972888449024 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 522775 524288 5739759974972888449024 75557863725914323419136 81566895 1073741824 261237 260982 (ep894 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep896 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz293 (Real.cos qz380)) (@HMul.hMul Real Real Real qz0 qz293 (@Neg.neg Real Real.instNeg (Real.sin qz380))) Bool.true 7884707607 274877906944 10271524193563 35869092955029504 Bool.true 103594662325 274877906944 10334549519689 35869092955029504 (@Enclosure.Real.IsNear.mulLit_ft qz293 (Real.cos qz380) 198163 524288 1 524288 39789 524288 51807251 68414865408 7884707607 274877906944 10271524193563 35869092955029504 qz565 (@Enclosure.Real.IsNear.recentre' (Real.cos qz380) Bool.true 39789 524288 51807251 68414865408 39789 524288 51807251 68414865408 (ep892 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz293 (@Neg.neg Real Real.instNeg (Real.sin qz380)) 198163 524288 1 524288 522775 524288 51807251 68414865408 103594662325 274877906944 10334549519689 35869092955029504 qz565 (@Enclosure.Real.IsNear.neg (Real.sin qz380) Bool.false 522775 524288 51807251 68414865408 (@Enclosure.Real.IsNear.recentre' (Real.sin qz380) Bool.false 522775 524288 51807251 68414865408 522775 524288 51807251 68414865408 (ep895 rfl rfl) rfl)) rfl)

noncomputable def ep897 := @ep833 7884707607 274877906944 10271524193563 35869092955029504 Bool.true 103594662325 274877906944 10334549519689 35869092955029504 Bool.false 69584036980102793265152 506290503691 274877906944 27466852169507 11956364318343168 Bool.false 32444031720007890108416 59015349907 137438953472 13739584194277 5978182159171584 (ep834 (BSN.head_sum_c_succ qz64 6 7 rfl rfl) (ep888 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep889 ep896) rfl rfl

noncomputable abbrev qz381 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 8 1)))

noncomputable def ep898 := @Enclosure.Complex.IsNear.of_eq qz916 (Complex.mk (@HMul.hMul Real Real Real qz0 qz296 (Real.cos qz381)) (@HMul.hMul Real Real Real qz0 qz296 (@Neg.neg Real Real.instNeg (Real.sin qz381)))) Bool.true 51443237301 274877906944 1073733598205 3985454772781056 Bool.true 41225658015 137438953472 538079517211 1992727386390528 (BSN.cpow_neg_s_mk qz61 97714 1000 8 (@Eq.refl Real qz61) rfl)

noncomputable def ep899 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz298 97714 1000 0 1 9364972152248037 4503599627370496 1000000000391473 130491000000000000000 457544444442382343709 2251799813685248000 48857000019126196361 65245500000000000000000 qz375 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 1000000000391473 130491000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz834) Bool.false 19639770079031275290624 9444732965739290427392 1000000000391473 130491000000000000000 9364972152248037 4503599627370496 1000000000391473 130491000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 262144 24973259072661432 36028797018963968 130491 1000000000000000 rfl rfl rfl rfl (ep174 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep900 := nat_lit 128702596026009576207303391233610000

noncomputable def ep901 := BSN.sin_dyadic_bound_f 598958630 1073741824 2 1 524288 261237 ep900 ep92 ep900 ep900 ep93 ep900 277527 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 598958630) qz275 0 1 ep900 ep92 ep900 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 598958630) qz276 0 1 ep900 ep93 ep900 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz926 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 106530367) qz280)

noncomputable def ep902 := @Enclosure.Real.IsNear.cos_image qz381 qz926 Bool.false 106530367 524288 197 262144 Bool.true 277527 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz381 Bool.false 457544444442382343709 2251799813685248000 48857000019126196361 65245500000000000000000 106530367 524288 197 262144 (ep899 rfl) rfl) (Enclosure.sfrac_false_div 106530367 524288) (BSN.cos_reduce1 qz926 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 42147966648460576292864) qz282) 226375608064910080 72057594037927936 Bool.false 277527 524288 32 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q1 106530367 524288 226375608064910080 72057594037927936 32 42147966648460576292864 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 277527 524288 42147966648460576292864 75557863725914323419136 598958630 1073741824 261237 260982 (ep901 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep903 := BSN.cos_dyadic_bound_f 598958630 1073741824 2 1 524288 261237 ep900 ep88 ep900 ep900 ep89 ep900 444810 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 598958630) qz269 0 1 ep900 ep88 ep900 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 598958630) qz270 0 1 ep900 ep89 ep900 rfl rfl rfl rfl) rfl rfl

noncomputable def ep904 := @Enclosure.Real.IsNear.sin_image qz381 qz926 Bool.false 106530367 524288 197 262144 Bool.false 444810 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz381 Bool.false 457544444442382343709 2251799813685248000 48857000019126196361 65245500000000000000000 106530367 524288 197 262144 (ep899 rfl) rfl) (Enclosure.sfrac_false_div 106530367 524288) (BSN.sin_reduce1 qz926 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 42147966648460576292864) qz282) 226375608064910080 72057594037927936 Bool.false 444810 524288 32 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q1 106530367 524288 226375608064910080 72057594037927936 32 42147966648460576292864 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 444810 524288 42147966648460576292864 75557863725914323419136 598958630 1073741824 261237 260982 (ep903 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep905 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz296 (Real.cos qz381)) (@HMul.hMul Real Real Real qz0 qz296 (@Neg.neg Real Real.instNeg (Real.sin qz381))) Bool.true 51443237301 274877906944 1073733598205 3985454772781056 Bool.true 41225658015 137438953472 538079517211 1992727386390528 (@Enclosure.Real.IsNear.mulLit_ft qz296 (Real.cos qz381) 185363 524288 1 524288 277527 524288 25968871 34207432704 51443237301 274877906944 1073733598205 3985454772781056 qz566 (@Enclosure.Real.IsNear.recentre' (Real.cos qz381) Bool.true 277527 524288 25968871 34207432704 277527 524288 25968871 34207432704 (ep902 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz296 (@Neg.neg Real Real.instNeg (Real.sin qz381)) 185363 524288 1 524288 222405 262144 25968871 34207432704 41225658015 137438953472 538079517211 1992727386390528 qz566 (@Enclosure.Real.IsNear.neg (Real.sin qz381) Bool.false 222405 262144 25968871 34207432704 (@Enclosure.Real.IsNear.recentre' (Real.sin qz381) Bool.false 444810 524288 25968871 34207432704 222405 262144 25968871 34207432704 (ep904 rfl rfl) rfl)) rfl)

noncomputable def ep906 := @ep831 51443237301 274877906944 1073733598205 3985454772781056 Bool.true 41225658015 137438953472 538079517211 1992727386390528 Bool.false 125027464564483198812160 227423633195 137438953472 15344026482061 5978182159171584 Bool.false 2444996636225803649024 4447422973 34359738368 7676911372955 2989091079585792 (ep832 (BSN.head_sum_c_succ qz64 7 8 rfl rfl) (ep897 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep898 ep905) rfl rfl

theorem EMRow28.d16 : Enclosure.Complex.IsNear (BSN.headSumC qz64 9) Bool.false 227423633195 137438953472 15344026482061 5978182159171584 Bool.false 4447422973 34359738368 7676911372955 2989091079585792 := ep830 (BSN.head_sum_c_succ qz64 8 9 rfl rfl) (ep906 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz927 := (@HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast 16) qz65)

noncomputable def ep907 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 17) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 16) qz927) Bool.false 693501566641 274877906944 51602524071587 11956364318343168 Bool.true 44883595319 274877906944 51641902949615 11956364318343168

noncomputable def ep908 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 16) qz927 Bool.false 642929656285 274877906944 147949640369861 35869092955029504 Bool.false 821666453 137438953472 18508975510837 4483636619378688 Bool.false

noncomputable abbrev qz928 := (@HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast 15) qz65)

noncomputable def ep909 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 16) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 15) qz928) Bool.false 642929656285 274877906944 147949640369861 35869092955029504 Bool.false 821666453 137438953472 18508975510837 4483636619378688

noncomputable def ep910 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 15) qz928 Bool.false 18424495967 8589934592 8804206352561 2241818309689344 Bool.false 48456113787 274877906944 140995762853471 35869092955029504 Bool.false

noncomputable abbrev qz929 := (@HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast 14) qz65)

noncomputable def ep911 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 15) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 14) qz929) Bool.false 18424495967 8589934592 8804206352561 2241818309689344 Bool.false 48456113787 274877906944 140995762853471 35869092955029504

noncomputable def ep912 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 14) qz929 Bool.false 64828184447 34359738368 11126966639177 2989091079585792 Bool.false 8434674927 34359738368 11141702378849 2989091079585792 Bool.false

noncomputable abbrev qz930 := (@HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast 13) qz65)

noncomputable def ep913 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 14) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 13) qz930) Bool.false 64828184447 34359738368 11126966639177 2989091079585792 Bool.false 8434674927 34359738368 11141702378849 2989091079585792

noncomputable def ep914 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 13) qz930 Bool.false 57516919367 34359738368 31479685007645 8967273238757376 Bool.false 18579606213 274877906944 126104177006441 35869092955029504 Bool.false

noncomputable abbrev qz931 := (@HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast 12) qz65)

noncomputable def ep915 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 13) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 12) qz931) Bool.false 57516919367 34359738368 31479685007645 8967273238757376 Bool.false 18579606213 274877906944 126104177006441 35869092955029504

noncomputable def ep916 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 12) qz931 Bool.false 508996412049 274877906944 118015835455913 35869092955029504 Bool.true 43942968385 274877906944 118189493661659 35869092955029504 Bool.true

noncomputable abbrev qz932 := (@HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast 11) qz65)

noncomputable def ep917 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 12) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 11) qz932) Bool.false 508996412049 274877906944 118015835455913 35869092955029504 Bool.true 43942968385 274877906944 118189493661659 35869092955029504

noncomputable def ep918 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 11) qz932 Bool.false 530223576327 274877906944 36595998202697 11956364318343168 Bool.false 2260706921 17179869184 18318840449665 5978182159171584 Bool.true

noncomputable abbrev qz933 := (@HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast 10) qz65)

noncomputable def ep919 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 11) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 10) qz933) Bool.false 530223576327 274877906944 36595998202697 11956364318343168 Bool.false 2260706921 17179869184 18318840449665 5978182159171584

noncomputable def ep920 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 10) qz933 Bool.false 249368972631 137438953472 50586889233479 17934546477514752 Bool.true 44850218839 274877906944 101259838716859 35869092955029504 Bool.false

noncomputable abbrev qz934 := (@HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast 9) qz65)

noncomputable def ep921 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 10) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 9) qz934) Bool.false 249368972631 137438953472 50586889233479 17934546477514752 Bool.true 44850218839 274877906944 101259838716859 35869092955029504

noncomputable def ep922 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 9) qz934 Bool.false 227423633195 137438953472 15344026482061 5978182159171584 Bool.false 4447422973 34359738368 7676911372955 2989091079585792 Bool.false

noncomputable abbrev qz382 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 9 1)))

noncomputable def ep923 := @Enclosure.Complex.IsNear.of_eq qz934 (Complex.mk (@HMul.hMul Real Real Real qz0 qz299 (Real.cos qz382)) (@HMul.hMul Real Real Real qz0 qz299 (@Neg.neg Real Real.instNeg (Real.sin qz382)))) Bool.false 5486334859 34359738368 142337805853 560454577422336 Bool.true 80429602623 274877906944 9136902241399 35869092955029504 (BSN.cpow_neg_s_mk qz61 97714 1000 9 (@Eq.refl Real qz61) rfl)

noncomputable def ep924 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz301 97714 1000 0 1 9895417793173221 4503599627370496 1000000000391473 130491000000000000000 483460427121064058397 2251799813685248000 48857000019126196361 65245500000000000000000 qz375 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 1000000000391473 130491000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz845) Bool.false 20752195215788806766592 9444732965739290427392 1000000000391473 130491000000000000000 9895417793173221 4503599627370496 1000000000391473 130491000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 30876 262144 24973259072661432 36028797018963968 130491 1000000000000000 rfl rfl rfl rfl (ep201 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep925 := nat_lit 3912231691261106664140123058536015654797859397577715217122624999524871713921

noncomputable def ep926 := nat_lit 3064439002086154689529595528800415323233087203718382683350960773968704641

noncomputable def ep927 := nat_lit 11730566195779147683041309984550446133747112018325708886001173077026677732481

noncomputable def ep928 := BSN.cos_dyadic_bound_f 1150254319 1073741824 3 2 524288 261237 ep925 ep102 ep926 ep927 ep105 ep926 251144 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1150254319) qz269 0 2 ep925 ep102 ep926 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1150254319) qz270 0 2 ep927 ep105 ep926 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz935 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 56282201) qz271)

noncomputable def ep929 := @Enclosure.Real.IsNear.cos_image qz382 qz935 Bool.false 56282201 262144 197 262144 Bool.false 251144 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz382 Bool.false 483460427121064058397 2251799813685248000 48857000019126196361 65245500000000000000000 56282201 262144 197 262144 (ep924 rfl) rfl) (Enclosure.sfrac_false_div 56282201 262144) (BSN.cos_reduce0 qz935 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 40470975960904265367552) qz274) 226375608064910080 72057594037927936 Bool.false 251144 524288 34 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q0 56282201 262144 226375608064910080 72057594037927936 34 40470975960904265367552 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 251144 524288 40470975960904265367552 37778931862957161709568 1150254319 1073741824 261237 260982 (ep928 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep930 := nat_lit 7039565493068323071700597828941787846377560445876912684674044230525594121345

noncomputable def ep931 := nat_lit 18431995771080325699242327349705672258560757121823989173611357143456797176961

noncomputable def ep932 := BSN.sin_dyadic_bound_f 1150254319 1073741824 3 2 524288 261237 ep930 ep109 ep926 ep931 ep111 ep926 460221 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1150254319) qz275 0 2 ep930 ep109 ep926 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1150254319) qz276 0 2 ep931 ep111 ep926 rfl rfl rfl rfl) rfl rfl

noncomputable def ep933 := @Enclosure.Real.IsNear.sin_image qz382 qz935 Bool.false 56282201 262144 197 262144 Bool.false 460221 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz382 Bool.false 483460427121064058397 2251799813685248000 48857000019126196361 65245500000000000000000 56282201 262144 197 262144 (ep924 rfl) rfl) (Enclosure.sfrac_false_div 56282201 262144) (BSN.sin_reduce0 qz935 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 40470975960904265367552) qz274) 226375608064910080 72057594037927936 Bool.false 460221 524288 34 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q0 56282201 262144 226375608064910080 72057594037927936 34 40470975960904265367552 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 460221 524288 40470975960904265367552 37778931862957161709568 1150254319 1073741824 261237 260982 (ep932 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep934 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz299 (Real.cos qz382)) (@HMul.hMul Real Real Real qz0 qz299 (@Neg.neg Real Real.instNeg (Real.sin qz382))) Bool.false 5486334859 34359738368 142337805853 560454577422336 Bool.true 80429602623 274877906944 9136902241399 35869092955029504 (@Enclosure.Real.IsNear.mulLit_ff qz299 (Real.cos qz382) 174763 524288 1 524288 31393 65536 25968871 34207432704 5486334859 34359738368 142337805853 560454577422336 qz567 (@Enclosure.Real.IsNear.recentre' (Real.cos qz382) Bool.false 251144 524288 25968871 34207432704 31393 65536 25968871 34207432704 (ep929 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz299 (@Neg.neg Real Real.instNeg (Real.sin qz382)) 174763 524288 1 524288 460221 524288 25968871 34207432704 80429602623 274877906944 9136902241399 35869092955029504 qz567 (@Enclosure.Real.IsNear.neg (Real.sin qz382) Bool.false 460221 524288 25968871 34207432704 (@Enclosure.Real.IsNear.recentre' (Real.sin qz382) Bool.false 460221 524288 25968871 34207432704 460221 524288 25968871 34207432704 (ep933 rfl rfl) rfl)) rfl)

noncomputable def ep935 := @ep922 5486334859 34359738368 142337805853 560454577422336 Bool.true 80429602623 274877906944 9136902241399 35869092955029504 Bool.false 8568252656698112606208 249368972631 137438953472 50586889233479 17934546477514752 Bool.true 1541041785055584714752 44850218839 274877906944 101259838716859 35869092955029504 EMRow28.d16 (ep923 ep934) rfl rfl

noncomputable abbrev qz383 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 10 1)))

noncomputable def ep936 := @Enclosure.Complex.IsNear.of_eq qz933 (Complex.mk (@HMul.hMul Real Real Real qz0 qz302 (Real.cos qz383)) (@HMul.hMul Real Real Real qz0 qz302 (@Neg.neg Real Real.instNeg (Real.sin qz383)))) Bool.false 31485631065 274877906944 8614216141133 35869092955029504 Bool.false 81021529575 274877906944 8653203981131 35869092955029504 (BSN.cpow_neg_s_mk qz61 97714 1000 10 (@Eq.refl Real qz61) rfl)

noncomputable def ep937 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz304 97714 1000 0 1 10369908600166117 4503599627370496 1000000000391473 130491000000000000000 506642624478315978269 2251799813685248000 48857000019126196361 65245500000000000000000 qz375 (BSN.isNear_log_sfrac 10 1 10369908600166117 4503599627370496 1000000000391473 130491000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz848) Bool.false 21747274560655572598784 9444732965739290427392 1000000000391473 130491000000000000000 10369908600166117 4503599627370496 1000000000391473 130491000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 58495 262144 24973259072661432 36028797018963968 130491 1000000000000000 rfl rfl rfl rfl (ep215 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep938 := nat_lit 25086676852978513213528798875390625

noncomputable def ep939 := BSN.sin_dyadic_bound_f 397979575 1073741824 2 1 524288 261237 ep938 ep92 ep938 ep938 ep93 ep938 189907 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 397979575) qz275 0 1 ep938 ep92 ep938 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 397979575) qz276 0 1 ep938 ep93 ep938 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz610 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14745241) (@Nat.cast Real Real.instNatCast 65536))

noncomputable abbrev qz936 := (@Nat.cast Real Real.instNatCast 9444732965739290427392)

noncomputable def ep940 := @Enclosure.Real.IsNear.cos_image qz383 qz610 Bool.false 14745241 65536 393 524288 Bool.false 189907 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz383 Bool.false 506642624478315978269 2251799813685248000 48857000019126196361 65245500000000000000000 14745241 65536 393 524288 (ep937 rfl) rfl) (Enclosure.sfrac_false_div 14745241 65536) (BSN.cos_reduce3 qz610 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3500665368522692493312) qz936) 226375608064910080 72057594037927936 Bool.false 189907 524288 35 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q3 14745241 65536 226375608064910080 72057594037927936 35 3500665368522692493312 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 189907 524288 3500665368522692493312 9444732965739290427392 397979575 1073741824 261237 260982 (ep939 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep941 := BSN.cos_dyadic_bound_f 397979575 1073741824 2 1 524288 261237 ep938 ep88 ep938 ep938 ep89 ep938 488685 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 397979575) qz269 0 1 ep938 ep88 ep938 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 397979575) qz270 0 1 ep938 ep89 ep938 rfl rfl rfl rfl) rfl rfl

noncomputable def ep942 := @Enclosure.Real.IsNear.sin_image qz383 qz610 Bool.false 14745241 65536 393 524288 Bool.true 488685 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz383 Bool.false 506642624478315978269 2251799813685248000 48857000019126196361 65245500000000000000000 14745241 65536 393 524288 (ep937 rfl) rfl) (Enclosure.sfrac_false_div 14745241 65536) (BSN.sin_reduce3 qz610 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3500665368522692493312) qz936) 226375608064910080 72057594037927936 Bool.false 488685 524288 35 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q3 14745241 65536 226375608064910080 72057594037927936 35 3500665368522692493312 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 488685 524288 3500665368522692493312 9444732965739290427392 397979575 1073741824 261237 260982 (ep941 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep943 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz302 (Real.cos qz383)) (@HMul.hMul Real Real Real qz0 qz302 (@Neg.neg Real Real.instNeg (Real.sin qz383))) Bool.false 31485631065 274877906944 8614216141133 35869092955029504 Bool.false 81021529575 274877906944 8653203981131 35869092955029504 (@Enclosure.Real.IsNear.mulLit_ff qz302 (Real.cos qz383) 165795 524288 1 524288 189907 524288 51807251 68414865408 31485631065 274877906944 8614216141133 35869092955029504 qz568 (@Enclosure.Real.IsNear.recentre' (Real.cos qz383) Bool.false 189907 524288 51807251 68414865408 189907 524288 51807251 68414865408 (ep940 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz302 (@Neg.neg Real Real.instNeg (Real.sin qz383)) 165795 524288 1 524288 488685 524288 51807251 68414865408 81021529575 274877906944 8653203981131 35869092955029504 qz568 (@Enclosure.Real.IsNear.neg (Real.sin qz383) Bool.true 488685 524288 51807251 68414865408 (@Enclosure.Real.IsNear.recentre' (Real.sin qz383) Bool.true 488685 524288 51807251 68414865408 488685 524288 51807251 68414865408 (ep942 rfl rfl) rfl)) rfl)

noncomputable def ep944 := @ep920 31485631065 274877906944 8614216141133 35869092955029504 Bool.false 81021529575 274877906944 8653203981131 35869092955029504 Bool.false 72873373436563993657344 530223576327 274877906944 36595998202697 11956364318343168 Bool.false 9942694186532716150784 2260706921 17179869184 18318840449665 5978182159171584 (ep921 (BSN.head_sum_c_succ qz64 9 10 rfl rfl) (ep935 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep936 ep943) rfl rfl

noncomputable abbrev qz384 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 11 1)))

noncomputable def ep945 := @Enclosure.Complex.IsNear.of_eq qz932 (Complex.mk (@HMul.hMul Real Real Real qz0 qz305 (Real.cos qz384)) (@HMul.hMul Real Real Real qz0 qz305 (@Neg.neg Real Real.instNeg (Real.sin qz384)))) Bool.true 10613582139 137438953472 4113920423911 17934546477514752 Bool.true 80114279121 274877906944 8276450963669 35869092955029504 (BSN.cpow_neg_s_mk qz61 97714 1000 11 (@Eq.refl Real qz61) rfl)

noncomputable def ep946 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz307 97714 1000 0 1 10799147631728357 4503599627370496 1000000000391473 130491000000000000000 527613955843352337949 2251799813685248000 48857000019126196361 65245500000000000000000 qz375 (BSN.isNear_log_sfrac 11 1 10799147631728357 4503599627370496 1000000000391473 130491000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz851) Bool.false 22647454054174387339264 9444732965739290427392 1000000000391473 130491000000000000000 10799147631728357 4503599627370496 1000000000391473 130491000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 83480 262144 24973259072661432 36028797018963968 130491 1000000000000000 rfl rfl rfl rfl (ep230 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep947 := nat_lit 5982289499930630998642549987538241

noncomputable def ep948 := BSN.sin_dyadic_bound_f 278110161 1073741824 2 1 524288 261237 ep947 ep92 ep947 ep947 ep93 ep947 134282 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 278110161) qz275 0 1 ep947 ep92 ep947 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 278110161) qz276 0 1 ep947 ep93 ep947 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz611 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 15355587) (@Nat.cast Real Real.instNatCast 65536))

noncomputable def ep949 := @Enclosure.Real.IsNear.cos_image qz384 qz611 Bool.false 15355587 65536 197 262144 Bool.true 134282 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz384 Bool.false 527613955843352337949 2251799813685248000 48857000019126196361 65245500000000000000000 15355587 65536 197 262144 (ep946 rfl) rfl) (Enclosure.sfrac_false_div 15355587 65536) (BSN.cos_reduce1 qz611 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2446282849017338527744) qz936) 226375608064910080 72057594037927936 Bool.false 134282 524288 37 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q1 15355587 65536 226375608064910080 72057594037927936 37 2446282849017338527744 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 134282 524288 2446282849017338527744 9444732965739290427392 278110161 1073741824 261237 260982 (ep948 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep950 := BSN.cos_dyadic_bound_f 278110161 1073741824 2 1 524288 261237 ep947 ep88 ep947 ep947 ep89 ep947 506799 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 278110161) qz269 0 1 ep947 ep88 ep947 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 278110161) qz270 0 1 ep947 ep89 ep947 rfl rfl rfl rfl) rfl rfl

noncomputable def ep951 := @Enclosure.Real.IsNear.sin_image qz384 qz611 Bool.false 15355587 65536 197 262144 Bool.false 506799 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz384 Bool.false 527613955843352337949 2251799813685248000 48857000019126196361 65245500000000000000000 15355587 65536 197 262144 (ep946 rfl) rfl) (Enclosure.sfrac_false_div 15355587 65536) (BSN.sin_reduce1 qz611 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2446282849017338527744) qz936) 226375608064910080 72057594037927936 Bool.false 506799 524288 37 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q1 15355587 65536 226375608064910080 72057594037927936 37 2446282849017338527744 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 506799 524288 2446282849017338527744 9444732965739290427392 278110161 1073741824 261237 260982 (ep950 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep952 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz305 (Real.cos qz384)) (@HMul.hMul Real Real Real qz0 qz305 (@Neg.neg Real Real.instNeg (Real.sin qz384))) Bool.true 10613582139 137438953472 4113920423911 17934546477514752 Bool.true 80114279121 274877906944 8276450963669 35869092955029504 (@Enclosure.Real.IsNear.mulLit_ft qz305 (Real.cos qz384) 158079 524288 1 524288 67141 262144 25968871 34207432704 10613582139 137438953472 4113920423911 17934546477514752 qz569 (@Enclosure.Real.IsNear.recentre' (Real.cos qz384) Bool.true 134282 524288 25968871 34207432704 67141 262144 25968871 34207432704 (ep949 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz305 (@Neg.neg Real Real.instNeg (Real.sin qz384)) 158079 524288 1 524288 506799 524288 25968871 34207432704 80114279121 274877906944 8276450963669 35869092955029504 qz569 (@Enclosure.Real.IsNear.neg (Real.sin qz384) Bool.false 506799 524288 25968871 34207432704 (@Enclosure.Real.IsNear.recentre' (Real.sin qz384) Bool.false 506799 524288 25968871 34207432704 506799 524288 25968871 34207432704 (ep951 rfl rfl) rfl)) rfl)

noncomputable def ep953 := @ep918 10613582139 137438953472 4113920423911 17934546477514752 Bool.true 80114279121 274877906944 8276450963669 35869092955029504 Bool.false 69955934193017451184128 508996412049 274877906944 118015835455913 35869092955029504 Bool.true 754934448410947747840 43942968385 274877906944 118189493661659 35869092955029504 (ep919 (BSN.head_sum_c_succ qz64 10 11 rfl rfl) (ep944 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep945 ep952) rfl rfl

noncomputable abbrev qz385 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 12 1)))

noncomputable def ep954 := @Enclosure.Complex.IsNear.of_eq qz931 (Complex.mk (@HMul.hMul Real Real Real qz0 qz308 (Real.cos qz385)) (@HMul.hMul Real Real Real qz0 qz308 (@Neg.neg Real Real.instNeg (Real.sin qz385)))) Bool.true 48861057113 274877906944 2634301524889 11956364318343168 Bool.false 31261287299 137438953472 1319113890797 5978182159171584 (BSN.cpow_neg_s_mk qz61 97714 1000 12 (@Eq.refl Real qz61) rfl)

noncomputable def ep955 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz310 97714 1000 0 1 11191020447815397 4503599627370496 1000000000391473 130491000000000000000 546759686018916851229 2251799813685248000 48857000019126196361 65245500000000000000000 qz375 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 1000000000391473 130491000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz854) Bool.false 23469270914176955449344 9444732965739290427392 1000000000391473 130491000000000000000 11191020447815397 4503599627370496 1000000000391473 130491000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 106290 262144 24973259072661432 36028797018963968 130491 1000000000000000 rfl rfl rfl rfl (ep245 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep956 := nat_lit 2013529104158800412791786615294395327571305513836042960376033685960905085921

noncomputable def ep957 := nat_lit 812358627096720502213379739626018199160834403476708141944028309706396641

noncomputable def ep958 := nat_lit 6038962595222207797370933086403933946315594872701175464844213001263302464481

noncomputable def ep959 := BSN.cos_dyadic_bound_f 974357819 1073741824 3 2 524288 261237 ep956 ep102 ep957 ep958 ep105 ep957 322837 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 974357819) qz269 0 2 ep956 ep102 ep957 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 974357819) qz270 0 2 ep958 ep105 ep957 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz937 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 127302409) qz280)

noncomputable def ep960 := @Enclosure.Real.IsNear.cos_image qz385 qz937 Bool.false 127302409 524288 197 262144 Bool.true 322837 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz385 Bool.false 546759686018916851229 2251799813685248000 48857000019126196361 65245500000000000000000 127302409 524288 197 262144 (ep955 rfl) rfl) (Enclosure.sfrac_false_div 127302409 524288) (BSN.cos_reduce2 qz937 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 68564336169648534847488) qz282) 226375608064910080 72057594037927936 Bool.false 322837 524288 38 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q2 127302409 524288 226375608064910080 72057594037927936 38 68564336169648534847488 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 322837 524288 68564336169648534847488 75557863725914323419136 974357819 1073741824 261237 260982 (ep959 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep961 := nat_lit 3623702500584163366623445203738210775069021257382095962163305412081864037345

noncomputable def ep962 := nat_lit 9489334158990842698438772918783538476667842894585574754388366700093928788961

noncomputable def ep963 := BSN.sin_dyadic_bound_f 974357819 1073741824 3 2 524288 261237 ep961 ep109 ep957 ep962 ep111 ep957 413102 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 974357819) qz275 0 2 ep961 ep109 ep957 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 974357819) qz276 0 2 ep962 ep111 ep957 rfl rfl rfl rfl) rfl rfl

noncomputable def ep964 := @Enclosure.Real.IsNear.sin_image qz385 qz937 Bool.false 127302409 524288 197 262144 Bool.true 413102 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz385 Bool.false 546759686018916851229 2251799813685248000 48857000019126196361 65245500000000000000000 127302409 524288 197 262144 (ep955 rfl) rfl) (Enclosure.sfrac_false_div 127302409 524288) (BSN.sin_reduce2 qz937 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 68564336169648534847488) qz282) 226375608064910080 72057594037927936 Bool.false 413102 524288 38 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q2 127302409 524288 226375608064910080 72057594037927936 38 68564336169648534847488 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 413102 524288 68564336169648534847488 75557863725914323419136 974357819 1073741824 261237 260982 (ep963 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep965 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz308 (Real.cos qz385)) (@HMul.hMul Real Real Real qz0 qz308 (@Neg.neg Real Real.instNeg (Real.sin qz385))) Bool.true 48861057113 274877906944 2634301524889 11956364318343168 Bool.false 31261287299 137438953472 1319113890797 5978182159171584 (@Enclosure.Real.IsNear.mulLit_ft qz308 (Real.cos qz385) 151349 524288 1 524288 322837 524288 25968871 34207432704 48861057113 274877906944 2634301524889 11956364318343168 qz570 (@Enclosure.Real.IsNear.recentre' (Real.cos qz385) Bool.true 322837 524288 25968871 34207432704 322837 524288 25968871 34207432704 (ep960 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz308 (@Neg.neg Real Real.instNeg (Real.sin qz385)) 151349 524288 1 524288 206551 262144 25968871 34207432704 31261287299 137438953472 1319113890797 5978182159171584 qz570 (@Enclosure.Real.IsNear.neg (Real.sin qz385) Bool.true 206551 262144 25968871 34207432704 (@Enclosure.Real.IsNear.recentre' (Real.sin qz385) Bool.true 413102 524288 25968871 34207432704 206551 262144 25968871 34207432704 (ep964 rfl rfl) rfl)) rfl)

noncomputable def ep966 := @ep916 48861057113 274877906944 2634301524889 11956364318343168 Bool.false 31261287299 137438953472 1319113890797 5978182159171584 Bool.false 126481043275742219075584 57516919367 34359738368 31479685007645 8967273238757376 Bool.false 2553561633836589121536 18579606213 274877906944 126104177006441 35869092955029504 (ep917 (BSN.head_sum_c_succ qz64 11 12 rfl rfl) (ep953 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep954 ep965) rfl rfl

noncomputable abbrev qz386 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 13 1)))

noncomputable def ep967 := @Enclosure.Complex.IsNear.of_eq qz930 (Complex.mk (@HMul.hMul Real Real Real qz0 qz311 (Real.cos qz386)) (@HMul.hMul Real Real Real qz0 qz311 (@Neg.neg Real Real.instNeg (Real.sin qz386)))) Bool.false 913908135 4294967296 950607454943 4483636619378688 Bool.false 48897793203 274877906944 7596251539747 35869092955029504 (BSN.cpow_neg_s_mk qz61 97714 1000 13 (@Eq.refl Real qz61) rfl)

noncomputable def ep968 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz313 97714 1000 0 1 11551488463034085 4503599627370496 1000000000391473 130491000000000000000 112874214367691258169 450359962737049600 48857000019126196361 65245500000000000000000 qz375 (BSN.isNear_log_sfrac 13 1 11551488463034085 4503599627370496 1000000000391473 130491000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz857) Bool.false 24225227133228857425920 9444732965739290427392 1000000000391473 130491000000000000000 11551488463034085 4503599627370496 1000000000391473 130491000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 127272 262144 24973259072661432 36028797018963968 130491 1000000000000000 rfl rfl rfl rfl (ep260 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep969 := nat_lit 777338581225292402569270046348755216

noncomputable def ep970 := BSN.sin_dyadic_bound_f 938971814 1073741824 2 1 524288 261237 ep969 ep92 ep969 ep969 ep93 ep969 402240 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 938971814) qz275 0 1 ep969 ep92 ep969 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 938971814) qz276 0 1 ep969 ep93 ep969 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz938 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 131402879) qz280)

noncomputable def ep971 := @Enclosure.Real.IsNear.cos_image qz386 qz938 Bool.false 131402879 524288 197 262144 Bool.false 402240 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz386 Bool.false 112874214367691258169 450359962737049600 48857000019126196361 65245500000000000000000 131402879 524288 197 262144 (ep968 rfl) rfl) (Enclosure.sfrac_false_div 131402879 524288) (BSN.cos_reduce3 qz938 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 66074267413375382192128) qz282) 226375608064910080 72057594037927936 Bool.false 402240 524288 39 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q3 131402879 524288 226375608064910080 72057594037927936 39 66074267413375382192128 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 402240 524288 66074267413375382192128 75557863725914323419136 938971814 1073741824 261237 260982 (ep970 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep972 := nat_lit 1736481398608748914208734165527565458901008942348915336721520459856965345536

noncomputable def ep973 := nat_lit 604255269861350514097310930724525258024770162315251575831750072687206656

noncomputable def ep974 := nat_lit 5208235685286524041598007874721247326186977286722115507012897879425521623296

noncomputable def ep975 := BSN.cos_dyadic_bound_f 938971814 1073741824 3 2 524288 261237 ep972 ep102 ep973 ep974 ep105 ep973 336273 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 938971814) qz269 0 2 ep972 ep102 ep973 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 938971814) qz270 0 2 ep974 ep105 ep973 rfl rfl rfl rfl) rfl rfl

noncomputable def ep976 := @Enclosure.Real.IsNear.sin_image qz386 qz938 Bool.false 131402879 524288 197 262144 Bool.true 336273 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz386 Bool.false 112874214367691258169 450359962737049600 48857000019126196361 65245500000000000000000 131402879 524288 197 262144 (ep968 rfl) rfl) (Enclosure.sfrac_false_div 131402879 524288) (BSN.sin_reduce3 qz938 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 66074267413375382192128) qz282) 226375608064910080 72057594037927936 Bool.false 336273 524288 39 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q3 131402879 524288 226375608064910080 72057594037927936 39 66074267413375382192128 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 336273 524288 66074267413375382192128 75557863725914323419136 938971814 1073741824 261237 260982 (ep975 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep977 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz311 (Real.cos qz386)) (@HMul.hMul Real Real Real qz0 qz311 (@Neg.neg Real Real.instNeg (Real.sin qz386))) Bool.false 913908135 4294967296 950607454943 4483636619378688 Bool.false 48897793203 274877906944 7596251539747 35869092955029504 (@Enclosure.Real.IsNear.mulLit_ff qz311 (Real.cos qz386) 145411 524288 1 524288 6285 8192 25968871 34207432704 913908135 4294967296 950607454943 4483636619378688 qz571 (@Enclosure.Real.IsNear.recentre' (Real.cos qz386) Bool.false 402240 524288 25968871 34207432704 6285 8192 25968871 34207432704 (ep971 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz311 (@Neg.neg Real Real.instNeg (Real.sin qz386)) 145411 524288 1 524288 336273 524288 25968871 34207432704 48897793203 274877906944 7596251539747 35869092955029504 qz571 (@Enclosure.Real.IsNear.neg (Real.sin qz386) Bool.true 336273 524288 25968871 34207432704 (@Enclosure.Real.IsNear.recentre' (Real.sin qz386) Bool.true 336273 524288 25968871 34207432704 336273 524288 25968871 34207432704 (ep976 rfl rfl) rfl)) rfl)

noncomputable def ep978 := @ep914 913908135 4294967296 950607454943 4483636619378688 Bool.false 48897793203 274877906944 7596251539747 35869092955029504 Bool.false 278434932058920845312 64828184447 34359738368 11126966639177 2989091079585792 Bool.false 18548046317494367944704 8434674927 34359738368 11141702378849 2989091079585792 (ep915 (BSN.head_sum_c_succ qz64 12 13 rfl rfl) (ep966 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep967 ep977) rfl rfl

noncomputable abbrev qz387 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 14 1)))

noncomputable def ep979 := @Enclosure.Complex.IsNear.of_eq qz929 (Complex.mk (@HMul.hMul Real Real Real qz0 qz314 (Real.cos qz387)) (@HMul.hMul Real Real Real qz0 qz314 (@Neg.neg Real Real.instNeg (Real.sin qz387)))) Bool.false 8869799421 34359738368 1835925492713 8967273238757376 Bool.true 19021285629 274877906944 7295334307283 35869092955029504 (BSN.cpow_neg_s_mk qz61 97714 1000 14 (@Eq.refl Real qz61) rfl)

noncomputable def ep980 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz316 97714 1000 0 1 11885241781671653 4503599627370496 1000000000391473 130491000000000000000 580677257727131950621 2251799813685248000 48857000019126196361 65245500000000000000000 qz375 (BSN.isNear_log_sfrac 14 1 11885241781671653 4503599627370496 1000000000391473 130491000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz860) Bool.false 24925158572916270432256 9444732965739290427392 1000000000391473 130491000000000000000 11885241781671653 4503599627370496 1000000000391473 130491000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 146699 262144 24973259072661432 36028797018963968 130491 1000000000000000 rfl rfl rfl rfl (ep275 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep981 := nat_lit 6254306896444412157503829257586241

noncomputable def ep982 := BSN.cos_dyadic_bound_f 281219089 1073741824 2 1 524288 261237 ep981 ep88 ep981 ep981 ep89 ep981 506408 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 281219089) qz269 0 1 ep981 ep88 ep981 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 281219089) qz270 0 1 ep981 ep89 ep981 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz939 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 135199459) qz280)

noncomputable def ep983 := @Enclosure.Real.IsNear.cos_image qz387 qz939 Bool.false 135199459 524288 197 262144 Bool.false 506408 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz387 Bool.false 580677257727131950621 2251799813685248000 48857000019126196361 65245500000000000000000 135199459 524288 197 262144 (ep980 rfl) rfl) (Enclosure.sfrac_false_div 135199459 524288) (BSN.cos_reduce0 qz939 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 19789034152730388594688) qz282) 226375608064910080 72057594037927936 Bool.false 506408 524288 41 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q0 135199459 524288 226375608064910080 72057594037927936 41 19789034152730388594688 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 506408 524288 19789034152730388594688 75557863725914323419136 281219089 1073741824 261237 260982 (ep982 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep984 := BSN.sin_dyadic_bound_f 281219089 1073741824 2 1 524288 261237 ep981 ep92 ep981 ep981 ep93 ep981 135749 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 281219089) qz275 0 1 ep981 ep92 ep981 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 281219089) qz276 0 1 ep981 ep93 ep981 rfl rfl rfl rfl) rfl rfl

noncomputable def ep985 := @Enclosure.Real.IsNear.sin_image qz387 qz939 Bool.false 135199459 524288 197 262144 Bool.false 135749 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz387 Bool.false 580677257727131950621 2251799813685248000 48857000019126196361 65245500000000000000000 135199459 524288 197 262144 (ep980 rfl) rfl) (Enclosure.sfrac_false_div 135199459 524288) (BSN.sin_reduce0 qz939 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 19789034152730388594688) qz282) 226375608064910080 72057594037927936 Bool.false 135749 524288 41 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q0 135199459 524288 226375608064910080 72057594037927936 41 19789034152730388594688 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 135749 524288 19789034152730388594688 75557863725914323419136 281219089 1073741824 261237 260982 (ep984 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep986 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz314 (Real.cos qz387)) (@HMul.hMul Real Real Real qz0 qz314 (@Neg.neg Real Real.instNeg (Real.sin qz387))) Bool.false 8869799421 34359738368 1835925492713 8967273238757376 Bool.true 19021285629 274877906944 7295334307283 35869092955029504 (@Enclosure.Real.IsNear.mulLit_ff qz314 (Real.cos qz387) 140121 524288 1 524288 63301 65536 25968871 34207432704 8869799421 34359738368 1835925492713 8967273238757376 qz572 (@Enclosure.Real.IsNear.recentre' (Real.cos qz387) Bool.false 506408 524288 25968871 34207432704 63301 65536 25968871 34207432704 (ep983 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz314 (@Neg.neg Real Real.instNeg (Real.sin qz387)) 140121 524288 1 524288 135749 524288 25968871 34207432704 19021285629 274877906944 7295334307283 35869092955029504 qz572 (@Enclosure.Real.IsNear.neg (Real.sin qz387) Bool.false 135749 524288 25968871 34207432704 (@Enclosure.Real.IsNear.recentre' (Real.sin qz387) Bool.false 135749 524288 25968871 34207432704 135749 524288 25968871 34207432704 (ep985 rfl rfl) rfl)) rfl)

noncomputable def ep987 := @ep912 8869799421 34359738368 1835925492713 8967273238757376 Bool.true 19021285629 274877906944 7295334307283 35869092955029504 Bool.false 2532243443953564647424 18424495967 8589934592 8804206352561 2241818309689344 Bool.false 1664939392051357679616 48456113787 274877906944 140995762853471 35869092955029504 (ep913 (BSN.head_sum_c_succ qz64 13 14 rfl rfl) (ep978 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep979 ep986) rfl rfl

noncomputable abbrev qz388 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 15 1)))

noncomputable def ep988 := @Enclosure.Complex.IsNear.of_eq qz928 (Complex.mk (@HMul.hMul Real Real Real qz0 qz317 (Real.cos qz388)) (@HMul.hMul Real Real Real qz0 qz317 (@Neg.neg Real Real.instNeg (Real.sin qz388)))) Bool.false 53345785341 274877906944 2360779576295 11956364318343168 Bool.true 46812780881 274877906944 2358680411075 11956364318343168 (BSN.cpow_neg_s_mk qz61 97714 1000 15 (@Eq.refl Real qz61) rfl)

noncomputable def ep989 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz319 97714 1000 0 1 12195956895733477 4503599627370496 1000000000391473 130491000000000000000 595857866054850485789 2251799813685248000 48857000019126196361 65245500000000000000000 qz375 (BSN.isNear_log_sfrac 15 1 12195956895733477 4503599627370496 1000000000391473 130491000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz863) Bool.false 25576775395801252757504 9444732965739290427392 1000000000391473 130491000000000000000 12195956895733477 4503599627370496 1000000000391473 130491000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 164785 262144 24973259072661432 36028797018963968 130491 1000000000000000 rfl rfl rfl rfl (ep286 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep990 := nat_lit 799000962697539611329052880114293994801234990769625815999651840056614190625

noncomputable def ep991 := nat_lit 127978774252542954433522451654450118195927436229482333501426241625390625

noncomputable def ep992 := nat_lit 2396746930544113748078291595439573084167313117436418483331952667686591790625

noncomputable def ep993 := BSN.cos_dyadic_bound_f 773378765 1073741824 3 2 524288 261237 ep990 ep102 ep991 ep992 ep105 ep991 394071 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 773378765) qz269 0 2 ep990 ep102 ep991 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 773378765) qz270 0 2 ep992 ep105 ep991 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz940 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 69366985) qz271)

noncomputable def ep994 := @Enclosure.Real.IsNear.cos_image qz388 qz940 Bool.false 69366985 262144 197 262144 Bool.false 394071 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz388 Bool.false 595857866054850485789 2251799813685248000 48857000019126196361 65245500000000000000000 69366985 262144 197 262144 (ep989 rfl) rfl) (Enclosure.sfrac_false_div 69366985 262144) (BSN.cos_reduce0 qz940 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 27210846234684749250560) qz274) 226375608064910080 72057594037927936 Bool.false 394071 524288 42 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q0 69366985 262144 226375608064910080 72057594037927936 42 27210846234684749250560 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 394071 524288 27210846234684749250560 37778931862957161709568 773378765 1073741824 261237 260982 (ep993 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep995 := nat_lit 357741211286235450451907424441300625

noncomputable def ep996 := BSN.sin_dyadic_bound_f 773378765 1073741824 2 1 524288 261237 ep995 ep92 ep995 ep995 ep93 ep995 345811 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 773378765) qz275 0 1 ep995 ep92 ep995 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 773378765) qz276 0 1 ep995 ep93 ep995 rfl rfl rfl rfl) rfl rfl

noncomputable def ep997 := @Enclosure.Real.IsNear.sin_image qz388 qz940 Bool.false 69366985 262144 197 262144 Bool.false 345811 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz388 Bool.false 595857866054850485789 2251799813685248000 48857000019126196361 65245500000000000000000 69366985 262144 197 262144 (ep989 rfl) rfl) (Enclosure.sfrac_false_div 69366985 262144) (BSN.sin_reduce0 qz940 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 27210846234684749250560) qz274) 226375608064910080 72057594037927936 Bool.false 345811 524288 42 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q0 69366985 262144 226375608064910080 72057594037927936 42 27210846234684749250560 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 345811 524288 27210846234684749250560 37778931862957161709568 773378765 1073741824 261237 260982 (ep996 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep998 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz317 (Real.cos qz388)) (@HMul.hMul Real Real Real qz0 qz317 (@Neg.neg Real Real.instNeg (Real.sin qz388))) Bool.false 53345785341 274877906944 2360779576295 11956364318343168 Bool.true 46812780881 274877906944 2358680411075 11956364318343168 (@Enclosure.Real.IsNear.mulLit_ff qz317 (Real.cos qz388) 135371 524288 1 524288 394071 524288 25968871 34207432704 53345785341 274877906944 2360779576295 11956364318343168 qz573 (@Enclosure.Real.IsNear.recentre' (Real.cos qz388) Bool.false 394071 524288 25968871 34207432704 394071 524288 25968871 34207432704 (ep994 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz317 (@Neg.neg Real Real.instNeg (Real.sin qz388)) 135371 524288 1 524288 345811 524288 25968871 34207432704 46812780881 274877906944 2358680411075 11956364318343168 qz573 (@Enclosure.Real.IsNear.neg (Real.sin qz388) Bool.false 345811 524288 25968871 34207432704 (@Enclosure.Real.IsNear.recentre' (Real.sin qz388) Bool.false 345811 524288 25968871 34207432704 345811 524288 25968871 34207432704 (ep997 rfl rfl) rfl)) rfl)

noncomputable def ep999 := @ep910 53345785341 274877906944 2360779576295 11956364318343168 Bool.true 46812780881 274877906944 2358680411075 11956364318343168 Bool.false 5522723694745191710720 642929656285 274877906944 147949640369861 35869092955029504 Bool.false 451715909613481099264 821666453 137438953472 18508975510837 4483636619378688 (ep911 (BSN.head_sum_c_succ qz64 14 15 rfl rfl) (ep987 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep988 ep998) rfl rfl

noncomputable abbrev qz389 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 16 1)))

noncomputable def ep1000 := @Enclosure.Complex.IsNear.of_eq qz927 (Complex.mk (@HMul.hMul Real Real Real qz0 qz320 (Real.cos qz389)) (@HMul.hMul Real Real Real qz0 qz320 (@Neg.neg Real Real.instNeg (Real.sin qz389)))) Bool.false 12642977589 68719476736 1714482961225 8967273238757376 Bool.true 46526928225 274877906944 6853904762149 35869092955029504 (BSN.cpow_neg_s_mk qz61 97714 1000 16 (@Eq.refl Real qz61) rfl)

noncomputable def ep1001 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz322 97714 1000 0 1 3121657384082679 1125899906842624 250000000130491 32622750000000000000 152514814814127447903 562949953421312000 12214250006375398787 16311375000000000000000 qz375 (BSN.isNear_log_sfrac 16 1 3121657384082679 1125899906842624 250000000130491 32622750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz866) Bool.false 26186360105375033720832 9444732965739290427392 1000000000521964 130491000000000000000 3121657384082679 1125899906842624 250000000130491 32622750000000000000 (BSN.log_rat_reduce_isNear 16 1 4 32 32 0 262144 24973259072661432 36028797018963968 130491 1000000000000000 rfl rfl rfl rfl (ep300 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1002 := nat_lit 908507736515055622132186544858401524119545110357336693790298934478117011456

noncomputable def ep1003 := nat_lit 165455625198349609489014710777079557790931644449374442601065887643467776

noncomputable def ep1004 := nat_lit 2725192298294770167177581605153650413243053467783111332485694671659064098816

noncomputable def ep1005 := BSN.cos_dyadic_bound_f 798610824 1073741824 3 2 524288 261237 ep1002 ep102 ep1003 ep1004 ep105 ep1003 385836 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 798610824) qz269 0 2 ep1002 ep102 ep1003 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 798610824) qz270 0 2 ep1004 ep105 ep1003 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz941 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 142040489) qz280)

noncomputable def ep1006 := @Enclosure.Real.IsNear.cos_image qz389 qz941 Bool.false 142040489 524288 197 262144 Bool.false 385836 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz389 Bool.false 152514814814127447903 562949953421312000 12214250006375398787 16311375000000000000000 142040489 524288 197 262144 (ep1001 rfl) rfl) (Enclosure.sfrac_false_div 142040489 524288) (BSN.cos_reduce0 qz941 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 56197240826218076438528) qz282) 226375608064910080 72057594037927936 Bool.false 385836 524288 43 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q0 142040489 524288 226375608064910080 72057594037927936 43 56197240826218076438528 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 385836 524288 56197240826218076438528 75557863725914323419136 798610824 1073741824 261237 260982 (ep1005 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1007 := nat_lit 406762369447260459692342867602968576

noncomputable def ep1008 := BSN.sin_dyadic_bound_f 798610824 1073741824 2 1 524288 261237 ep1007 ep92 ep1007 ep1007 ep93 ep1007 354975 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 798610824) qz275 0 1 ep1007 ep92 ep1007 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 798610824) qz276 0 1 ep1007 ep93 ep1007 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1009 := @Enclosure.Real.IsNear.sin_image qz389 qz941 Bool.false 142040489 524288 197 262144 Bool.false 354975 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz389 Bool.false 152514814814127447903 562949953421312000 12214250006375398787 16311375000000000000000 142040489 524288 197 262144 (ep1001 rfl) rfl) (Enclosure.sfrac_false_div 142040489 524288) (BSN.sin_reduce0 qz941 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 56197240826218076438528) qz282) 226375608064910080 72057594037927936 Bool.false 354975 524288 43 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q0 142040489 524288 226375608064910080 72057594037927936 43 56197240826218076438528 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 354975 524288 56197240826218076438528 75557863725914323419136 798610824 1073741824 261237 260982 (ep1008 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1010 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz320 (Real.cos qz389)) (@HMul.hMul Real Real Real qz0 qz320 (@Neg.neg Real Real.instNeg (Real.sin qz389))) Bool.false 12642977589 68719476736 1714482961225 8967273238757376 Bool.true 46526928225 274877906944 6853904762149 35869092955029504 (@Enclosure.Real.IsNear.mulLit_ff qz320 (Real.cos qz389) 131071 524288 1 524288 96459 131072 25968871 34207432704 12642977589 68719476736 1714482961225 8967273238757376 qz574 (@Enclosure.Real.IsNear.recentre' (Real.cos qz389) Bool.false 385836 524288 25968871 34207432704 96459 131072 25968871 34207432704 (ep1006 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz320 (@Neg.neg Real Real.instNeg (Real.sin qz389)) 131071 524288 1 524288 354975 524288 25968871 34207432704 46526928225 274877906944 6853904762149 35869092955029504 qz574 (@Enclosure.Real.IsNear.neg (Real.sin qz389) Bool.false 354975 524288 25968871 34207432704 (@Enclosure.Real.IsNear.recentre' (Real.sin qz389) Bool.false 354975 524288 25968871 34207432704 354975 524288 25968871 34207432704 (ep1009 rfl rfl) rfl)) rfl)

noncomputable def ep1011 := @ep908 12642977589 68719476736 1714482961225 8967273238757376 Bool.true 46526928225 274877906944 6853904762149 35869092955029504 Bool.false 47657064775165753163776 693501566641 274877906944 51602524071587 11956364318343168 Bool.true 6168754368704117997568 44883595319 274877906944 51641902949615 11956364318343168 (ep909 (BSN.head_sum_c_succ qz64 15 16 rfl rfl) (ep999 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1000 ep1010) rfl rfl

theorem EMRow28.d17 : Enclosure.Complex.IsNear (BSN.headSumC qz64 17) Bool.false 693501566641 274877906944 51602524071587 11956364318343168 Bool.true 44883595319 274877906944 51641902949615 11956364318343168 := ep907 (BSN.head_sum_c_succ qz64 16 17 rfl rfl) (ep1011 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep1012 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 25) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 24) (@HPow.hPow Complex Complex Complex qz16 qz49 qz65)) Bool.false 753758885689 274877906944 203507419277183 35869092955029504 Bool.false 18905083 8589934592 50897184501527 8967273238757376

noncomputable def ep1013 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 24) (@HPow.hPow Complex Complex Complex qz16 qz49 qz65) Bool.false 200898472081 68719476736 2061481689413 373636384948224 Bool.false 26385946775 274877906944 66004296863899 11956364318343168 Bool.true

noncomputable abbrev qz942 := (@HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast 23) qz65)

noncomputable def ep1014 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 24) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 23) qz942) Bool.false 200898472081 68719476736 2061481689413 373636384948224 Bool.false 26385946775 274877906944 66004296863899 11956364318343168

noncomputable def ep1015 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 23) qz942 Bool.false 799230121967 274877906944 192219095543477 35869092955029504 Bool.true 30763355111 274877906944 192266736502667 35869092955029504 Bool.false

noncomputable abbrev qz943 := (@HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast 22) qz65)

noncomputable def ep1016 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 23) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 22) qz943) Bool.false 799230121967 274877906944 192219095543477 35869092955029504 Bool.true 30763355111 274877906944 192266736502667 35869092955029504

noncomputable def ep1017 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 22) qz943 Bool.false 746332051565 274877906944 186351741442859 35869092955029504 Bool.true 346199637 17179869184 46607922243089 8967273238757376 Bool.false

noncomputable abbrev qz944 := (@HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast 21) qz65)

noncomputable def ep1018 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 22) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 21) qz944) Bool.false 746332051565 274877906944 186351741442859 35869092955029504 Bool.true 346199637 17179869184 46607922243089 8967273238757376

noncomputable def ep1019 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 21) qz944 Bool.false 390388069757 137438953472 22546282328711 4483636619378688 Bool.false 43568695287 274877906944 180433481127715 35869092955029504 Bool.true

noncomputable abbrev qz945 := (@HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast 20) qz65)

noncomputable def ep1020 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 21) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 20) qz945) Bool.false 390388069757 137438953472 22546282328711 4483636619378688 Bool.false 43568695287 274877906944 180433481127715 35869092955029504

noncomputable def ep1021 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 20) qz945 Bool.false 832963651469 274877906944 58074399016151 11956364318343168 Bool.false 2774324173 68719476736 907856067713 186818192474112 Bool.true

noncomputable abbrev qz946 := (@HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast 19) qz65)

noncomputable def ep1022 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 20) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 19) qz946) Bool.false 832963651469 274877906944 58074399016151 11956364318343168 Bool.false 2774324173 68719476736 907856067713 186818192474112

noncomputable def ep1023 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 19) qz946 Bool.false 816935512487 274877906944 167958736471015 35869092955029504 Bool.true 24946287919 137438953472 83997562660883 17934546477514752 Bool.false

noncomputable abbrev qz947 := (@HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast 18) qz65)

noncomputable def ep1024 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 19) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 18) qz947) Bool.false 816935512487 274877906944 167958736471015 35869092955029504 Bool.true 24946287919 137438953472 83997562660883 17934546477514752

noncomputable def ep1025 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 18) qz947 Bool.false 755306435637 274877906944 161475399855085 35869092955029504 Bool.true 69878731313 274877906944 161555762215471 35869092955029504 Bool.false

noncomputable abbrev qz948 := (@HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast 17) qz65)

noncomputable def ep1026 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 18) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 17) qz948) Bool.false 755306435637 274877906944 161475399855085 35869092955029504 Bool.true 69878731313 274877906944 161555762215471 35869092955029504

noncomputable def ep1027 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 17) qz948 Bool.false 693501566641 274877906944 51602524071587 11956364318343168 Bool.true 44883595319 274877906944 51641902949615 11956364318343168 Bool.false

noncomputable abbrev qz390 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 17 1)))

noncomputable def ep1028 := @Enclosure.Complex.IsNear.of_eq qz948 (Complex.mk (@HMul.hMul Real Real Real qz0 qz340 (Real.cos qz390)) (@HMul.hMul Real Real Real qz0 qz340 (@Neg.neg Real Real.instNeg (Real.sin qz390)))) Bool.false 15451217249 68719476736 1666956910081 8967273238757376 Bool.true 12497567997 137438953472 3315026683313 17934546477514752 (BSN.cpow_neg_s_mk qz61 97714 1000 17 (@Eq.refl Real qz61) rfl)

noncomputable def ep1029 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz342 97714 1000 0 1 3189913004350711 1125899906842624 250000000130491 32622750000000000000 155849579653562687327 562949953421312000 12214250006375398787 16311375000000000000000 qz375 (BSN.isNear_log_sfrac 17 1 3189913004350711 1125899906842624 250000000130491 32622750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz890) Bool.false 26758929747600409100288 9444732965739290427392 1000000000521964 130491000000000000000 3189913004350711 1125899906842624 250000000130491 32622750000000000000 (BSN.log_rat_reduce_isNear 17 1 4 34 32 15892 262144 24973259072661432 36028797018963968 130491 1000000000000000 rfl rfl rfl rfl (ep588 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1030 := nat_lit 28995732395134688548238145676001536

noncomputable def ep1031 := BSN.cos_dyadic_bound_f 412651588 1073741824 2 1 524288 261237 ep1030 ep88 ep1030 ep1030 ep89 ep1030 486044 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 412651588) qz269 0 1 ep1030 ep88 ep1030 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 412651588) qz270 0 1 ep1030 ep89 ep1030 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz949 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 145146231) qz280)

noncomputable def ep1032 := @Enclosure.Real.IsNear.cos_image qz390 qz949 Bool.false 145146231 524288 197 262144 Bool.false 486044 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz390 Bool.false 155849579653562687327 562949953421312000 12214250006375398787 16311375000000000000000 145146231 524288 197 262144 (ep1029 rfl) rfl) (Enclosure.sfrac_false_div 145146231 524288) (BSN.cos_reduce0 qz949 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 29037774066760539963392) qz282) 226375608064910080 72057594037927936 Bool.false 486044 524288 44 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q0 145146231 524288 226375608064910080 72057594037927936 44 29037774066760539963392 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 486044 524288 29037774066760539963392 75557863725914323419136 412651588 1073741824 261237 260982 (ep1031 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1033 := BSN.sin_dyadic_bound_f 412651588 1073741824 2 1 524288 261237 ep1030 ep92 ep1030 ep1030 ep93 ep1030 196566 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 412651588) qz275 0 1 ep1030 ep92 ep1030 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 412651588) qz276 0 1 ep1030 ep93 ep1030 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1034 := @Enclosure.Real.IsNear.sin_image qz390 qz949 Bool.false 145146231 524288 197 262144 Bool.false 196566 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz390 Bool.false 155849579653562687327 562949953421312000 12214250006375398787 16311375000000000000000 145146231 524288 197 262144 (ep1029 rfl) rfl) (Enclosure.sfrac_false_div 145146231 524288) (BSN.sin_reduce0 qz949 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 29037774066760539963392) qz282) 226375608064910080 72057594037927936 Bool.false 196566 524288 44 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q0 145146231 524288 226375608064910080 72057594037927936 44 29037774066760539963392 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 196566 524288 29037774066760539963392 75557863725914323419136 412651588 1073741824 261237 260982 (ep1033 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1035 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz340 (Real.cos qz390)) (@HMul.hMul Real Real Real qz0 qz340 (@Neg.neg Real Real.instNeg (Real.sin qz390))) Bool.false 15451217249 68719476736 1666956910081 8967273238757376 Bool.true 12497567997 137438953472 3315026683313 17934546477514752 (@Enclosure.Real.IsNear.mulLit_ff qz340 (Real.cos qz390) 127159 524288 1 524288 121511 131072 25968871 34207432704 15451217249 68719476736 1666956910081 8967273238757376 qz597 (@Enclosure.Real.IsNear.recentre' (Real.cos qz390) Bool.false 486044 524288 25968871 34207432704 121511 131072 25968871 34207432704 (ep1032 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz340 (@Neg.neg Real Real.instNeg (Real.sin qz390)) 127159 524288 1 524288 98283 262144 25968871 34207432704 12497567997 137438953472 3315026683313 17934546477514752 qz597 (@Enclosure.Real.IsNear.neg (Real.sin qz390) Bool.false 98283 262144 25968871 34207432704 (@Enclosure.Real.IsNear.recentre' (Real.sin qz390) Bool.false 196566 524288 25968871 34207432704 98283 262144 25968871 34207432704 (ep1034 rfl rfl) rfl)) rfl)

noncomputable def ep1036 := @ep1027 15451217249 68719476736 1666956910081 8967273238757376 Bool.true 12497567997 137438953472 3315026683313 17934546477514752 Bool.false 51904263032307902840832 755306435637 274877906944 161475399855085 35869092955029504 Bool.true 9604059701609796468736 69878731313 274877906944 161555762215471 35869092955029504 EMRow28.d17 (ep1028 ep1035) rfl rfl

noncomputable abbrev qz391 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 18 1)))

noncomputable def ep1037 := @Enclosure.Complex.IsNear.of_eq qz947 (Complex.mk (@HMul.hMul Real Real Real qz0 qz343 (Real.cos qz391)) (@HMul.hMul Real Real Real qz0 qz343 (@Neg.neg Real Real.instNeg (Real.sin qz391)))) Bool.false 30814538425 137438953472 1080556102655 5978182159171584 Bool.false 19986155475 274877906944 2146454368765 11956364318343168 (BSN.cpow_neg_s_mk qz61 97714 1000 18 (@Eq.refl Real qz61) rfl)

noncomputable def ep1038 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz345 97714 1000 0 1 3254268794313975 1125899906842624 250000000130491 32622750000000000000 6359752419351915063 22517998136852480 12214250006375398787 16311375000000000000000 qz375 (BSN.isNear_log_sfrac 18 1 3254268794313975 1125899906842624 250000000130491 32622750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz893) Bool.false 27298785242132565196800 9444732965739290427392 1000000000521964 130491000000000000000 3254268794313975 1125899906842624 250000000130491 32622750000000000000 (BSN.log_rat_reduce_isNear 18 1 4 36 32 30876 262144 24973259072661432 36028797018963968 130491 1000000000000000 rfl rfl rfl rfl (ep599 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1039 := nat_lit 13358406673895556176419544891457234503253116938858670793527655430323659193985

noncomputable def ep1040 := nat_lit 11026293330953051043976339032447552293991040322084308237330518457972014721

noncomputable def ep1041 := nat_lit 34968451099571580284170465404906889566710749346013144150664371954296676531841

noncomputable def ep1042 := BSN.sin_dyadic_bound_f 1349906513 1073741824 3 2 524288 261237 ep1039 ep109 ep1040 ep1041 ep111 ep1040 498718 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1349906513) qz275 0 2 ep1039 ep109 ep1040 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1349906513) qz276 0 2 ep1041 ep111 ep1040 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz950 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 37018631) qz285)

noncomputable def ep1043 := @Enclosure.Real.IsNear.cos_image qz391 qz950 Bool.false 37018631 131072 197 262144 Bool.false 498718 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz391 Bool.false 6359752419351915063 22517998136852480 12214250006375398787 16311375000000000000000 37018631 131072 197 262144 (ep1038 rfl) rfl) (Enclosure.sfrac_false_div 37018631 131072) (BSN.cos_reduce3 qz950 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 23747806524891507720192) qz559) 226375608064910080 72057594037927936 Bool.false 498718 524288 44 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q3 37018631 131072 226375608064910080 72057594037927936 44 23747806524891507720192 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 498718 524288 23747806524891507720192 18889465931478580854784 1349906513 1073741824 261237 260982 (ep1042 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1044 := nat_lit 7426237615866843676252625534823995858382394317286854577843066580605576003201

noncomputable def ep1045 := nat_lit 22256660260938624926669923926407092470559200871216395117054538704900783980161

noncomputable def ep1046 := BSN.cos_dyadic_bound_f 1349906513 1073741824 3 2 524288 261237 ep1044 ep102 ep1040 ep1045 ep105 ep1040 161733 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1349906513) qz269 0 2 ep1044 ep102 ep1040 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1349906513) qz270 0 2 ep1045 ep105 ep1040 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1047 := @Enclosure.Real.IsNear.sin_image qz391 qz950 Bool.false 37018631 131072 197 262144 Bool.true 161733 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz391 Bool.false 6359752419351915063 22517998136852480 12214250006375398787 16311375000000000000000 37018631 131072 197 262144 (ep1038 rfl) rfl) (Enclosure.sfrac_false_div 37018631 131072) (BSN.sin_reduce3 qz950 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 23747806524891507720192) qz559) 226375608064910080 72057594037927936 Bool.false 161733 524288 44 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q3 37018631 131072 226375608064910080 72057594037927936 44 23747806524891507720192 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 161733 524288 23747806524891507720192 18889465931478580854784 1349906513 1073741824 261237 260982 (ep1046 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1048 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz343 (Real.cos qz391)) (@HMul.hMul Real Real Real qz0 qz343 (@Neg.neg Real Real.instNeg (Real.sin qz391))) Bool.false 30814538425 137438953472 1080556102655 5978182159171584 Bool.false 19986155475 274877906944 2146454368765 11956364318343168 (@Enclosure.Real.IsNear.mulLit_ff qz343 (Real.cos qz391) 123575 524288 1 524288 249359 262144 25968871 34207432704 30814538425 137438953472 1080556102655 5978182159171584 qz598 (@Enclosure.Real.IsNear.recentre' (Real.cos qz391) Bool.false 498718 524288 25968871 34207432704 249359 262144 25968871 34207432704 (ep1043 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz343 (@Neg.neg Real Real.instNeg (Real.sin qz391)) 123575 524288 1 524288 161733 524288 25968871 34207432704 19986155475 274877906944 2146454368765 11956364318343168 qz598 (@Enclosure.Real.IsNear.neg (Real.sin qz391) Bool.true 161733 524288 25968871 34207432704 (@Enclosure.Real.IsNear.recentre' (Real.sin qz391) Bool.true 161733 524288 25968871 34207432704 161733 524288 25968871 34207432704 (ep1047 rfl rfl) rfl)) rfl)

noncomputable def ep1049 := @ep1025 30814538425 137438953472 1080556102655 5978182159171584 Bool.false 19986155475 274877906944 2146454368765 11956364318343168 Bool.false 112278761890325268004864 816935512487 274877906944 167958736471015 35869092955029504 Bool.true 13714366818394226819072 24946287919 137438953472 83997562660883 17934546477514752 (ep1026 (BSN.head_sum_c_succ qz64 17 18 rfl rfl) (ep1036 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1037 ep1048) rfl rfl

noncomputable abbrev qz392 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 19 1)))

noncomputable def ep1050 := @Enclosure.Complex.IsNear.of_eq qz946 (Complex.mk (@HMul.hMul Real Real Real qz0 qz346 (Real.cos qz392)) (@HMul.hMul Real Real Real qz0 qz346 (@Neg.neg Real Real.instNeg (Real.sin qz392)))) Bool.false 8014069491 137438953472 3132230288719 17934546477514752 Bool.false 30494936265 137438953472 3156619839565 17934546477514752 (BSN.cpow_neg_s_mk qz61 97714 1000 19 (@Eq.refl Real qz61) rfl)

noncomputable def ep1051 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz348 97714 1000 0 1 3315141365800183 1125899906842624 250000000130491 32622750000000000000 161967861708899540831 562949953421312000 12214250006375398787 16311375000000000000000 qz375 (BSN.isNear_log_sfrac 19 1 3315141365800183 1125899906842624 250000000130491 32622750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz896) Bool.false 27809421382282341515264 9444732965739290427392 1000000000521964 130491000000000000000 3315141365800183 1125899906842624 250000000130491 32622750000000000000 (BSN.log_rat_reduce_isNear 19 1 4 38 32 45049 262144 24973259072661432 36028797018963968 130491 1000000000000000 rfl rfl rfl rfl (ep614 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1052 := nat_lit 5797747883666719937653710950198161

noncomputable def ep1053 := BSN.sin_dyadic_bound_f 275940109 1073741824 2 1 524288 261237 ep1052 ep92 ep1052 ep1052 ep93 ep1052 133258 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 275940109) qz275 0 1 ep1052 ep92 ep1052 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 275940109) qz276 0 1 ep1052 ep93 ep1052 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz951 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 150844325) qz280)

noncomputable def ep1054 := @Enclosure.Real.IsNear.cos_image qz392 qz951 Bool.false 150844325 524288 197 262144 Bool.false 133258 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz392 Bool.false 161967861708899540831 562949953421312000 12214250006375398787 16311375000000000000000 150844325 524288 197 262144 (ep1051 rfl) rfl) (Enclosure.sfrac_false_div 150844325 524288) (BSN.cos_reduce3 qz951 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 19417558942717396910080) qz282) 226375608064910080 72057594037927936 Bool.false 133258 524288 45 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q3 150844325 524288 226375608064910080 72057594037927936 45 19417558942717396910080 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 133258 524288 19417558942717396910080 75557863725914323419136 275940109 1073741824 261237 260982 (ep1053 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1055 := BSN.cos_dyadic_bound_f 275940109 1073741824 2 1 524288 261237 ep1052 ep88 ep1052 ep1052 ep89 ep1052 507070 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 275940109) qz269 0 1 ep1052 ep88 ep1052 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 275940109) qz270 0 1 ep1052 ep89 ep1052 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1056 := @Enclosure.Real.IsNear.sin_image qz392 qz951 Bool.false 150844325 524288 197 262144 Bool.true 507070 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz392 Bool.false 161967861708899540831 562949953421312000 12214250006375398787 16311375000000000000000 150844325 524288 197 262144 (ep1051 rfl) rfl) (Enclosure.sfrac_false_div 150844325 524288) (BSN.sin_reduce3 qz951 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 19417558942717396910080) qz282) 226375608064910080 72057594037927936 Bool.false 507070 524288 45 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q3 150844325 524288 226375608064910080 72057594037927936 45 19417558942717396910080 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 507070 524288 19417558942717396910080 75557863725914323419136 275940109 1073741824 261237 260982 (ep1055 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1057 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz346 (Real.cos qz392)) (@HMul.hMul Real Real Real qz0 qz346 (@Neg.neg Real Real.instNeg (Real.sin qz392))) Bool.false 8014069491 137438953472 3132230288719 17934546477514752 Bool.false 30494936265 137438953472 3156619839565 17934546477514752 (@Enclosure.Real.IsNear.mulLit_ff qz346 (Real.cos qz392) 120279 524288 1 524288 66629 262144 25968871 34207432704 8014069491 137438953472 3132230288719 17934546477514752 qz599 (@Enclosure.Real.IsNear.recentre' (Real.cos qz392) Bool.false 133258 524288 25968871 34207432704 66629 262144 25968871 34207432704 (ep1054 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz346 (@Neg.neg Real Real.instNeg (Real.sin qz392)) 120279 524288 1 524288 253535 262144 25968871 34207432704 30494936265 137438953472 3156619839565 17934546477514752 qz599 (@Enclosure.Real.IsNear.neg (Real.sin qz392) Bool.true 253535 262144 25968871 34207432704 (@Enclosure.Real.IsNear.recentre' (Real.sin qz392) Bool.true 507070 524288 25968871 34207432704 253535 262144 25968871 34207432704 (ep1056 rfl rfl) rfl)) rfl)

noncomputable def ep1058 := @ep1023 8014069491 137438953472 3132230288719 17934546477514752 Bool.false 30494936265 137438953472 3156619839565 17934546477514752 Bool.false 114481652538115115450368 832963651469 274877906944 58074399016151 11956364318343168 Bool.false 762600421858383757312 2774324173 68719476736 907856067713 186818192474112 (ep1024 (BSN.head_sum_c_succ qz64 18 19 rfl rfl) (ep1049 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1050 ep1057) rfl rfl

noncomputable abbrev qz393 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 20 1)))

noncomputable def ep1059 := @Enclosure.Complex.IsNear.of_eq qz945 (Complex.mk (@HMul.hMul Real Real Real qz0 qz349 (Real.cos qz393)) (@HMul.hMul Real Real Real qz0 qz349 (@Neg.neg Real Real.instNeg (Real.sin qz393)))) Bool.true 52187511955 274877906944 6147061581235 35869092955029504 Bool.false 32471398595 274877906944 6125116126819 35869092955029504 (BSN.cpow_neg_s_mk qz61 97714 1000 20 (@Eq.refl Real qz61) rfl)

noncomputable def ep1060 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz351 97714 1000 0 1 3372891496062199 1125899906842624 250000000130491 32622750000000000000 164789359823110856543 562949953421312000 12214250006375398787 16311375000000000000000 qz375 (BSN.isNear_log_sfrac 20 1 3372891496062199 1125899906842624 250000000130491 32622750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz899) Bool.false 28293864586999331028992 9444732965739290427392 1000000000521964 130491000000000000000 3372891496062199 1125899906842624 250000000130491 32622750000000000000 (BSN.log_rat_reduce_isNear 20 1 4 40 32 58495 262144 24973259072661432 36028797018963968 130491 1000000000000000 rfl rfl rfl rfl (ep629 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1061 := nat_lit 127565930969046040484259900406948321

noncomputable def ep1062 := BSN.cos_dyadic_bound_f 597631769 1073741824 2 1 524288 261237 ep1061 ep88 ep1061 ep1061 ep89 ep1061 445153 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 597631769) qz269 0 1 ep1061 ep88 ep1061 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 597631769) qz270 0 1 ep1061 ep89 ep1061 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz952 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 76736025) qz271)

noncomputable def ep1063 := @Enclosure.Real.IsNear.cos_image qz393 qz952 Bool.false 76736025 262144 197 262144 Bool.true 445153 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz393 Bool.false 164789359823110856543 562949953421312000 12214250006375398787 16311375000000000000000 76736025 262144 197 262144 (ep1060 rfl) rfl) (Enclosure.sfrac_false_div 76736025 262144) (BSN.cos_reduce2 qz952 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 21027298562969520046080) qz274) 226375608064910080 72057594037927936 Bool.false 445153 524288 46 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q2 76736025 262144 226375608064910080 72057594037927936 46 21027298562969520046080 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 445153 524288 21027298562969520046080 37778931862957161709568 597631769 1073741824 261237 260982 (ep1062 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1064 := BSN.sin_dyadic_bound_f 597631769 1073741824 2 1 524288 261237 ep1061 ep92 ep1061 ep1061 ep93 ep1061 276977 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 597631769) qz275 0 1 ep1061 ep92 ep1061 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 597631769) qz276 0 1 ep1061 ep93 ep1061 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1065 := @Enclosure.Real.IsNear.sin_image qz393 qz952 Bool.false 76736025 262144 197 262144 Bool.true 276977 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz393 Bool.false 164789359823110856543 562949953421312000 12214250006375398787 16311375000000000000000 76736025 262144 197 262144 (ep1060 rfl) rfl) (Enclosure.sfrac_false_div 76736025 262144) (BSN.sin_reduce2 qz952 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 21027298562969520046080) qz274) 226375608064910080 72057594037927936 Bool.false 276977 524288 46 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q2 76736025 262144 226375608064910080 72057594037927936 46 21027298562969520046080 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 276977 524288 21027298562969520046080 37778931862957161709568 597631769 1073741824 261237 260982 (ep1064 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1066 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz349 (Real.cos qz393)) (@HMul.hMul Real Real Real qz0 qz349 (@Neg.neg Real Real.instNeg (Real.sin qz393))) Bool.true 52187511955 274877906944 6147061581235 35869092955029504 Bool.false 32471398595 274877906944 6125116126819 35869092955029504 (@Enclosure.Real.IsNear.mulLit_ft qz349 (Real.cos qz393) 117235 524288 1 524288 445153 524288 25968871 34207432704 52187511955 274877906944 6147061581235 35869092955029504 qz600 (@Enclosure.Real.IsNear.recentre' (Real.cos qz393) Bool.true 445153 524288 25968871 34207432704 445153 524288 25968871 34207432704 (ep1063 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz349 (@Neg.neg Real Real.instNeg (Real.sin qz393)) 117235 524288 1 524288 276977 524288 25968871 34207432704 32471398595 274877906944 6125116126819 35869092955029504 qz600 (@Enclosure.Real.IsNear.neg (Real.sin qz393) Bool.true 276977 524288 25968871 34207432704 (@Enclosure.Real.IsNear.recentre' (Real.sin qz393) Bool.true 276977 524288 25968871 34207432704 276977 524288 25968871 34207432704 (ep1065 rfl rfl) rfl)) rfl)

noncomputable def ep1067 := @ep1021 52187511955 274877906944 6147061581235 35869092955029504 Bool.false 32471398595 274877906944 6125116126819 35869092955029504 Bool.false 214618111021424853385216 390388069757 137438953472 22546282328711 4483636619378688 Bool.false 2994017942192869343232 43568695287 274877906944 180433481127715 35869092955029504 (ep1022 (BSN.head_sum_c_succ qz64 19 20 rfl rfl) (ep1058 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1059 ep1066) rfl rfl

noncomputable abbrev qz394 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 21 1)))

noncomputable def ep1068 := @Enclosure.Complex.IsNear.of_eq qz944 (Complex.mk (@HMul.hMul Real Real Real qz0 qz352 (Real.cos qz394)) (@HMul.hMul Real Real Real qz0 qz352 (@Neg.neg Real Real.instNeg (Real.sin qz394)))) Bool.true 34444087949 274877906944 5981482813171 35869092955029504 Bool.true 49107889479 274877906944 5998207844641 35869092955029504 (BSN.cpow_neg_s_mk qz61 97714 1000 21 (@Eq.refl Real qz61) rfl)

noncomputable def ep1069 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz354 97714 1000 0 1 3427824127778039 1125899906842624 250000000130491 32622750000000000000 167473203410851651423 562949953421312000 12214250006375398787 16311375000000000000000 qz375 (BSN.isNear_log_sfrac 21 1 3427824127778039 1125899906842624 250000000130491 32622750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz902) Bool.false 28754672900871880179712 9444732965739290427392 1000000000521964 130491000000000000000 3427824127778039 1125899906842624 250000000130491 32622750000000000000 (BSN.log_rat_reduce_isNear 21 1 4 42 32 71285 262144 24973259072661432 36028797018963968 130491 1000000000000000 rfl rfl rfl rfl (ep644 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1070 := nat_lit 186057576866502035526106901513826576

noncomputable def ep1071 := BSN.sin_dyadic_bound_f 656767782 1073741824 2 1 524288 261237 ep1070 ep92 ep1070 ep1070 ep93 ep1070 301061 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 656767782) qz275 0 1 ep1070 ep92 ep1070 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 656767782) qz276 0 1 ep1070 ep93 ep1070 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz953 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 77985787) qz271)

noncomputable def ep1072 := @Enclosure.Real.IsNear.cos_image qz394 qz953 Bool.false 77985787 262144 197 262144 Bool.true 301061 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz394 Bool.false 167473203410851651423 562949953421312000 12214250006375398787 16311375000000000000000 77985787 262144 197 262144 (ep1069 rfl) rfl) (Enclosure.sfrac_false_div 77985787 262144) (BSN.cos_reduce1 qz953 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 23107962041323942313984) qz274) 226375608064910080 72057594037927936 Bool.false 301061 524288 47 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q1 77985787 262144 226375608064910080 72057594037927936 47 23107962041323942313984 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 301061 524288 23107962041323942313984 37778931862957161709568 656767782 1073741824 261237 260982 (ep1071 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1073 := BSN.cos_dyadic_bound_f 656767782 1073741824 2 1 524288 261237 ep1070 ep88 ep1070 ep1070 ep89 ep1070 429231 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 656767782) qz269 0 1 ep1070 ep88 ep1070 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 656767782) qz270 0 1 ep1070 ep89 ep1070 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1074 := @Enclosure.Real.IsNear.sin_image qz394 qz953 Bool.false 77985787 262144 197 262144 Bool.false 429231 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz394 Bool.false 167473203410851651423 562949953421312000 12214250006375398787 16311375000000000000000 77985787 262144 197 262144 (ep1069 rfl) rfl) (Enclosure.sfrac_false_div 77985787 262144) (BSN.sin_reduce1 qz953 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 23107962041323942313984) qz274) 226375608064910080 72057594037927936 Bool.false 429231 524288 47 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q1 77985787 262144 226375608064910080 72057594037927936 47 23107962041323942313984 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 429231 524288 23107962041323942313984 37778931862957161709568 656767782 1073741824 261237 260982 (ep1073 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1075 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz352 (Real.cos qz394)) (@HMul.hMul Real Real Real qz0 qz352 (@Neg.neg Real Real.instNeg (Real.sin qz394))) Bool.true 34444087949 274877906944 5981482813171 35869092955029504 Bool.true 49107889479 274877906944 5998207844641 35869092955029504 (@Enclosure.Real.IsNear.mulLit_ft qz352 (Real.cos qz394) 114409 524288 1 524288 301061 524288 25968871 34207432704 34444087949 274877906944 5981482813171 35869092955029504 qz601 (@Enclosure.Real.IsNear.recentre' (Real.cos qz394) Bool.true 301061 524288 25968871 34207432704 301061 524288 25968871 34207432704 (ep1072 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz352 (@Neg.neg Real Real.instNeg (Real.sin qz394)) 114409 524288 1 524288 429231 524288 25968871 34207432704 49107889479 274877906944 5998207844641 35869092955029504 qz601 (@Enclosure.Real.IsNear.neg (Real.sin qz394) Bool.false 429231 524288 25968871 34207432704 (@Enclosure.Real.IsNear.recentre' (Real.sin qz394) Bool.false 429231 524288 25968871 34207432704 429231 524288 25968871 34207432704 (ep1074 rfl rfl) rfl)) rfl)

noncomputable def ep1076 := @ep1019 34444087949 274877906944 5981482813171 35869092955029504 Bool.true 49107889479 274877906944 5998207844641 35869092955029504 Bool.false 102575096109704339783680 746332051565 274877906944 186351741442859 35869092955029504 Bool.true 1522602105653321269248 346199637 17179869184 46607922243089 8967273238757376 (ep1020 (BSN.head_sum_c_succ qz64 20 21 rfl rfl) (ep1067 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1068 ep1075) rfl rfl

noncomputable abbrev qz395 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 22 1)))

noncomputable def ep1077 := @Enclosure.Complex.IsNear.of_eq qz943 (Complex.mk (@HMul.hMul Real Real Real qz0 qz355 (Real.cos qz395)) (@HMul.hMul Real Real Real qz0 qz355 (@Neg.neg Real Real.instNeg (Real.sin qz395)))) Bool.false 26449035201 137438953472 12072745063 73804718014464 Bool.true 25224160919 274877906944 24012541277 147609436028928 (BSN.cpow_neg_s_mk qz61 97714 1000 22 (@Eq.refl Real qz61) rfl)

noncomputable def ep1078 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz357 97714 1000 0 1 3480201253952759 1125899906842624 250000000130491 32622750000000000000 170032192664369946463 562949953421312000 12214250006375398787 16311375000000000000000 qz375 (BSN.isNear_log_sfrac 22 1 3480201253952759 1125899906842624 250000000130491 32622750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz905) Bool.false 29194044080518145769472 9444732965739290427392 1000000000521964 130491000000000000000 3480201253952759 1125899906842624 250000000130491 32622750000000000000 (BSN.log_rat_reduce_isNear 22 1 4 44 32 83480 262144 24973259072661432 36028797018963968 130491 1000000000000000 rfl rfl rfl rfl (ep659 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1079 := nat_lit 52102091087183170913719076003995281

noncomputable def ep1080 := BSN.cos_dyadic_bound_f 477764403 1073741824 2 1 524288 261237 ep1079 ep88 ep1079 ep1079 ep89 ep1079 473238 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 477764403) qz269 0 1 ep1079 ep88 ep1079 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 477764403) qz270 0 1 ep1079 ep89 ep1079 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz954 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 158354819) qz280)

noncomputable def ep1081 := @Enclosure.Real.IsNear.cos_image qz395 qz954 Bool.false 158354819 524288 197 262144 Bool.false 473238 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz395 Bool.false 170032192664369946463 562949953421312000 12214250006375398787 16311375000000000000000 158354819 524288 197 262144 (ep1078 rfl) rfl) (Enclosure.sfrac_false_div 158354819 524288) (BSN.cos_reduce0 qz954 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 33619681085084284223488) qz282) 226375608064910080 72057594037927936 Bool.false 473238 524288 48 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q0 158354819 524288 226375608064910080 72057594037927936 48 33619681085084284223488 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 473238 524288 33619681085084284223488 75557863725914323419136 477764403 1073741824 261237 260982 (ep1080 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1082 := BSN.sin_dyadic_bound_f 477764403 1073741824 2 1 524288 261237 ep1079 ep92 ep1079 ep1079 ep93 ep1079 225661 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 477764403) qz275 0 1 ep1079 ep92 ep1079 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 477764403) qz276 0 1 ep1079 ep93 ep1079 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1083 := @Enclosure.Real.IsNear.sin_image qz395 qz954 Bool.false 158354819 524288 197 262144 Bool.false 225661 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz395 Bool.false 170032192664369946463 562949953421312000 12214250006375398787 16311375000000000000000 158354819 524288 197 262144 (ep1078 rfl) rfl) (Enclosure.sfrac_false_div 158354819 524288) (BSN.sin_reduce0 qz954 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 33619681085084284223488) qz282) 226375608064910080 72057594037927936 Bool.false 225661 524288 48 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q0 158354819 524288 226375608064910080 72057594037927936 48 33619681085084284223488 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 225661 524288 33619681085084284223488 75557863725914323419136 477764403 1073741824 261237 260982 (ep1082 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1084 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz355 (Real.cos qz395)) (@HMul.hMul Real Real Real qz0 qz355 (@Neg.neg Real Real.instNeg (Real.sin qz395))) Bool.false 26449035201 137438953472 12072745063 73804718014464 Bool.true 25224160919 274877906944 24012541277 147609436028928 (@Enclosure.Real.IsNear.mulLit_ff qz355 (Real.cos qz395) 111779 524288 1 524288 236619 262144 25968871 34207432704 26449035201 137438953472 12072745063 73804718014464 qz602 (@Enclosure.Real.IsNear.recentre' (Real.cos qz395) Bool.false 473238 524288 25968871 34207432704 236619 262144 25968871 34207432704 (ep1081 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz355 (@Neg.neg Real Real.instNeg (Real.sin qz395)) 111779 524288 1 524288 225661 524288 25968871 34207432704 25224160919 274877906944 24012541277 147609436028928 qz602 (@Enclosure.Real.IsNear.neg (Real.sin qz395) Bool.false 225661 524288 25968871 34207432704 (@Enclosure.Real.IsNear.recentre' (Real.sin qz395) Bool.false 225661 524288 25968871 34207432704 225661 524288 25968871 34207432704 (ep1083 rfl rfl) rfl)) rfl)

noncomputable def ep1085 := @ep1017 26449035201 137438953472 12072745063 73804718014464 Bool.true 25224160919 274877906944 24012541277 147609436028928 Bool.false 109845351546443398119424 799230121967 274877906944 192219095543477 35869092955029504 Bool.true 528510416467917799424 30763355111 274877906944 192266736502667 35869092955029504 (ep1018 (BSN.head_sum_c_succ qz64 21 22 rfl rfl) (ep1076 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1077 ep1084) rfl rfl

noncomputable abbrev qz396 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 23 1)))

noncomputable def ep1086 := @Enclosure.Complex.IsNear.of_eq qz942 (Complex.mk (@HMul.hMul Real Real Real qz0 qz358 (Real.cos qz396)) (@HMul.hMul Real Real Real qz0 qz358 (@Neg.neg Real Real.instNeg (Real.sin qz396)))) Bool.false 4363766357 274877906944 5683146640171 35869092955029504 Bool.false 28574650943 137438953472 2873077044515 17934546477514752 (BSN.cpow_neg_s_mk qz61 97714 1000 23 (@Eq.refl Real qz61) rfl)

noncomputable def ep1087 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz360 97714 1000 0 1 3530250507853047 1125899906842624 250000000130491 32622750000000000000 172477449062176317279 562949953421312000 12214250006375398787 16311375000000000000000 qz375 (BSN.isNear_log_sfrac 23 1 3530250507853047 1125899906842624 250000000130491 32622750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz908) Bool.false 29613887652180132888576 9444732965739290427392 1000000000521964 130491000000000000000 3530250507853047 1125899906842624 250000000130491 32622750000000000000 (BSN.log_rat_reduce_isNear 23 1 4 46 32 95133 262144 24973259072661432 36028797018963968 130491 1000000000000000 rfl rfl rfl rfl (ep674 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1088 := BSN.sin_dyadic_bound_f 81830720 1073741824 1 0 524288 261237 0 1 1 0 1 1 39917 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 81830720) qz275 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 81830720) qz276 0 0 rfl) rfl rfl

noncomputable abbrev qz955 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 160632141) qz280)

noncomputable def ep1089 := @Enclosure.Real.IsNear.cos_image qz396 qz955 Bool.false 160632141 524288 197 262144 Bool.false 39917 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz396 Bool.false 172477449062176317279 562949953421312000 12214250006375398787 16311375000000000000000 160632141 524288 197 262144 (ep1087 rfl) rfl) (Enclosure.sfrac_false_div 160632141 524288) (BSN.cos_reduce3 qz955 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 5758325020961802289152) qz282) 226375608064910080 72057594037927936 Bool.false 39917 524288 48 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q3 160632141 524288 226375608064910080 72057594037927936 48 5758325020961802289152 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 39917 524288 5758325020961802289152 75557863725914323419136 81830720 1073741824 261237 260982 (ep1088 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1090 := nat_lit 44839988195888756270364098560000

noncomputable def ep1091 := BSN.cos_dyadic_bound_f 81830720 1073741824 2 1 524288 261237 ep1090 ep88 ep1090 ep1090 ep89 ep1090 522766 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 81830720) qz269 0 1 ep1090 ep88 ep1090 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 81830720) qz270 0 1 ep1090 ep89 ep1090 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1092 := @Enclosure.Real.IsNear.sin_image qz396 qz955 Bool.false 160632141 524288 197 262144 Bool.true 522766 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz396 Bool.false 172477449062176317279 562949953421312000 12214250006375398787 16311375000000000000000 160632141 524288 197 262144 (ep1087 rfl) rfl) (Enclosure.sfrac_false_div 160632141 524288) (BSN.sin_reduce3 qz955 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 5758325020961802289152) qz282) 226375608064910080 72057594037927936 Bool.false 522766 524288 48 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q3 160632141 524288 226375608064910080 72057594037927936 48 5758325020961802289152 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 522766 524288 5758325020961802289152 75557863725914323419136 81830720 1073741824 261237 260982 (ep1091 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1093 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz358 (Real.cos qz396)) (@HMul.hMul Real Real Real qz0 qz358 (@Neg.neg Real Real.instNeg (Real.sin qz396))) Bool.false 4363766357 274877906944 5683146640171 35869092955029504 Bool.false 28574650943 137438953472 2873077044515 17934546477514752 (@Enclosure.Real.IsNear.mulLit_ff qz358 (Real.cos qz396) 109321 524288 1 524288 39917 524288 25968871 34207432704 4363766357 274877906944 5683146640171 35869092955029504 qz603 (@Enclosure.Real.IsNear.recentre' (Real.cos qz396) Bool.false 39917 524288 25968871 34207432704 39917 524288 25968871 34207432704 (ep1089 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz358 (@Neg.neg Real Real.instNeg (Real.sin qz396)) 109321 524288 1 524288 261383 262144 25968871 34207432704 28574650943 137438953472 2873077044515 17934546477514752 qz603 (@Enclosure.Real.IsNear.neg (Real.sin qz396) Bool.true 261383 262144 25968871 34207432704 (@Enclosure.Real.IsNear.recentre' (Real.sin qz396) Bool.true 522766 524288 25968871 34207432704 261383 262144 25968871 34207432704 (ep1092 rfl rfl) rfl)) rfl)

noncomputable def ep1094 := @ep1015 4363766357 274877906944 5683146640171 35869092955029504 Bool.false 28574650943 137438953472 2873077044515 17934546477514752 Bool.false 220890206055491600121856 200898472081 68719476736 2061481689413 373636384948224 Bool.false 3626456911123893452800 26385946775 274877906944 66004296863899 11956364318343168 (ep1016 (BSN.head_sum_c_succ qz64 22 23 rfl rfl) (ep1085 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1086 ep1093) rfl rfl

noncomputable abbrev qz397 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 24 1)))

noncomputable def ep1095 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz49 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz361 (Real.cos qz397)) (@HMul.hMul Real Real Real qz0 qz361 (@Neg.neg Real Real.instNeg (Real.sin qz397)))) Bool.true 49835002635 274877906944 5605177093535 35869092955029504 Bool.true 25780984119 274877906944 5575847414411 35869092955029504 (BSN.cpow_neg_s_mk qz61 97714 1000 24 (@Eq.refl Real qz61) rfl)

noncomputable def ep1096 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz363 97714 1000 0 1 3578169457974519 1125899906842624 250000000130491 32622750000000000000 174818625208261074783 562949953421312000 12214250006375398787 16311375000000000000000 qz375 (BSN.isNear_log_sfrac 24 1 3578169457974519 1125899906842624 250000000130491 32622750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz913 Bool.false 30015860940520713879552 9444732965739290427392 1000000000521964 130491000000000000000 3578169457974519 1125899906842624 250000000130491 32622750000000000000 (BSN.log_rat_reduce_isNear 24 1 4 48 32 106290 262144 24973259072661432 36028797018963968 130491 1000000000000000 rfl rfl rfl rfl (ep699 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1097 := nat_lit 7639707103390526422529412730726901778243144132179935839277433050764817301760

noncomputable def ep1098 := nat_lit 3608946729287362154307220718318093668969141875644359723717253650525552896

noncomputable def ep1099 := nat_lit 20002913642746818234565297842169370600887046497434502996650115769902242038016

noncomputable def ep1100 := BSN.sin_dyadic_bound_f 1174012062 1073741824 3 2 524288 261237 ep1097 ep109 ep1098 ep1099 ep111 ep1098 465665 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1174012062) qz275 0 2 ep1097 ep109 ep1098 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1174012062) qz276 0 2 ep1099 ep111 ep1098 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz956 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 40703133) qz285)

noncomputable def ep1101 := @Enclosure.Real.IsNear.cos_image qz397 qz956 Bool.false 40703133 131072 393 524288 Bool.true 465665 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz397 Bool.false 174818625208261074783 562949953421312000 12214250006375398787 16311375000000000000000 40703133 131072 393 524288 (ep1096 rfl) rfl) (Enclosure.sfrac_false_div 40703133 131072) (BSN.cos_reduce1 qz956 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 20653438615648527712256) qz559) 226375608064910080 72057594037927936 Bool.false 465665 524288 49 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q1 40703133 131072 226375608064910080 72057594037927936 49 20653438615648527712256 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 465665 524288 20653438615648527712256 18889465931478580854784 1174012062 1073741824 261237 260982 (ep1100 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1102 := nat_lit 4245885700429975729029365837389753473987955247600250737253559363158465413376

noncomputable def ep1103 := nat_lit 12730439207831352462779483070732624234625927459049463492313243582174345134336

noncomputable def ep1104 := BSN.cos_dyadic_bound_f 1174012062 1073741824 3 2 524288 261237 ep1102 ep102 ep1098 ep1103 ep105 ep1098 240901 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1174012062) qz269 0 2 ep1102 ep102 ep1098 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1174012062) qz270 0 2 ep1103 ep105 ep1098 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1105 := @Enclosure.Real.IsNear.sin_image qz397 qz956 Bool.false 40703133 131072 393 524288 Bool.false 240901 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz397 Bool.false 174818625208261074783 562949953421312000 12214250006375398787 16311375000000000000000 40703133 131072 393 524288 (ep1096 rfl) rfl) (Enclosure.sfrac_false_div 40703133 131072) (BSN.sin_reduce1 qz956 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 20653438615648527712256) qz559) 226375608064910080 72057594037927936 Bool.false 240901 524288 49 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q1 40703133 131072 226375608064910080 72057594037927936 49 20653438615648527712256 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 240901 524288 20653438615648527712256 18889465931478580854784 1174012062 1073741824 261237 260982 (ep1104 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1106 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz361 (Real.cos qz397)) (@HMul.hMul Real Real Real qz0 qz361 (@Neg.neg Real Real.instNeg (Real.sin qz397))) Bool.true 49835002635 274877906944 5605177093535 35869092955029504 Bool.true 25780984119 274877906944 5575847414411 35869092955029504 (@Enclosure.Real.IsNear.mulLit_ft qz361 (Real.cos qz397) 107019 524288 1 524288 465665 524288 51807251 68414865408 49835002635 274877906944 5605177093535 35869092955029504 qz604 (@Enclosure.Real.IsNear.recentre' (Real.cos qz397) Bool.true 465665 524288 51807251 68414865408 465665 524288 51807251 68414865408 (ep1101 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz361 (@Neg.neg Real Real.instNeg (Real.sin qz397)) 107019 524288 1 524288 240901 524288 51807251 68414865408 25780984119 274877906944 5575847414411 35869092955029504 qz604 (@Enclosure.Real.IsNear.neg (Real.sin qz397) Bool.false 240901 524288 51807251 68414865408 (@Enclosure.Real.IsNear.recentre' (Real.sin qz397) Bool.false 240901 524288 51807251 68414865408 240901 524288 51807251 68414865408 (ep1105 rfl rfl) rfl)) rfl)

noncomputable def ep1107 := @ep1013 49835002635 274877906944 5605177093535 35869092955029504 Bool.true 25780984119 274877906944 5575847414411 35869092955029504 Bool.false 51797916209658518831104 753758885689 274877906944 203507419277183 35869092955029504 Bool.false 166290868660563083264 18905083 8589934592 50897184501527 8967273238757376 (ep1014 (BSN.head_sum_c_succ qz64 23 24 rfl rfl) (ep1094 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1095 ep1106) rfl rfl

theorem EMRow28.d18 : Enclosure.Complex.IsNear (BSN.headSumC qz64 25) Bool.false 753758885689 274877906944 203507419277183 35869092955029504 Bool.false 18905083 8589934592 50897184501527 8967273238757376 := ep1012 (BSN.head_sum_c_succ qz64 24 25 rfl rfl) (ep1107 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

theorem EMRow28.d19 : @Eq Nat (Nat.pow 25 1) 25 := @Eq.refl Nat 25

noncomputable abbrev qz66 := (@HAdd.hAdd Complex Complex Complex qz263 qz373 qz552)

noncomputable def ep1108 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz3 (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2)) qz66) Bool.true 21482120541 500000 0 1 Bool.true 116551742141293 125000000 0 1

noncomputable def ep1109 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.re qz66)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.im qz66)) 2386818949 100000 0 1 2387006449 125000 0 1

noncomputable def ep1110 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.re qz66) 2386818949 250000 0 1 5 2 0 1 2386818949 100000

noncomputable abbrev qz67 := (@HAdd.hAdd Complex Complex Complex qz263 qz373 qz575)

noncomputable def ep1111 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz3 (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)) qz67) Bool.true 2386818949 250000 0 1 Bool.false 48857 250 0 1

noncomputable def ep1112 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.re qz67)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.im qz67)) 3 4 0 1 2387006449 250000 0 1

noncomputable def ep1113 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.re qz67) 1 2 0 1 3 2 0 1 3 4

noncomputable def ep1114 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)) qz64 Bool.false 1 2 0 1 Bool.false 97714 1000 0 1 (BSN.ascPochhammer_one_eval qz64)

noncomputable def ep1115 := ep1114 (@Enclosure.Complex.IsNear.of_eq qz64 (Complex.mk qz323 qz61) Bool.false 1 2 0 1 Bool.false 97714 1000 0 1 (BSN.s_crit_mk qz61 Bool.false 97714 1000 (@Eq.refl Real qz61)) (@Enclosure.Complex.IsNear.mk qz323 qz61 Bool.false 1 2 0 1 Bool.false 97714 1000 0 1 qz324 qz375))

noncomputable def ep1116 := @ep1113 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 97714 1000 0 1 ep1115)

noncomputable def ep1117 := @Enclosure.Complex.IsNear.of_eq qz67 (Complex.mk (Enclosure.sfrac Bool.false 3 2) qz61) Bool.false 3 2 0 1 Bool.false 97714 1000 0 1 (BSN.s_add_nat_mk qz61 Bool.false 97714 1000 1 (@Eq.refl Real qz61))

noncomputable abbrev qz612 := (ep1117 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz61 Bool.false 3 2 0 1 Bool.false 97714 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz375))

noncomputable def ep1118 := ep1116 (@Enclosure.Complex.IsNear.re_isNear qz67 Bool.false 3 2 0 1 Bool.false 97714 1000 0 1 qz612)

noncomputable def ep1119 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.im qz67) 97714 1000 0 1 97714 1000 0 1 2387006449 250000

noncomputable def ep1120 := @ep1119 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 97714 1000 0 1 ep1115)

noncomputable def ep1121 := ep1120 (@Enclosure.Complex.IsNear.im_isNear qz67 Bool.false 3 2 0 1 Bool.false 97714 1000 0 1 qz612)

noncomputable def ep1122 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)) qz67 Bool.true 2386818949 250000 0 1 Bool.false 48857 250 0 1 (@ep1112 9547275796 2386818949 250000 0 1 (ep1118 rfl) (ep1121 rfl) rfl rfl)

noncomputable def ep1123 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.im qz67)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.re qz67)) 48857 1000 0 1 146571 1000 0 1

noncomputable def ep1124 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.im qz67) 1 2 0 1 97714 1000 0 1 48857 1000

noncomputable def ep1125 := @ep1124 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 97714 1000 0 1 ep1115)

noncomputable def ep1126 := ep1125 (@Enclosure.Complex.IsNear.im_isNear qz67 Bool.false 3 2 0 1 Bool.false 97714 1000 0 1 qz612)

noncomputable def ep1127 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.re qz67) 97714 1000 0 1 3 2 0 1 146571 1000

noncomputable def ep1128 := @ep1127 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 97714 1000 0 1 ep1115)

noncomputable def ep1129 := ep1128 (@Enclosure.Complex.IsNear.re_isNear qz67 Bool.false 3 2 0 1 Bool.false 97714 1000 0 1 qz612)

noncomputable abbrev qz613 := (ep1111 (BSN.ascPochhammer_succ_eval_c 1 2 qz64 rfl) (ep1122 (@ep1123 195428000 48857 250 0 1 (ep1126 rfl) (ep1129 rfl) rfl rfl)))

noncomputable def ep1130 := @ep1110 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 2386818949 250000 0 1 Bool.false 48857 250 0 1 qz613)

noncomputable def ep1131 := @Enclosure.Complex.IsNear.of_eq qz66 (Complex.mk (Enclosure.sfrac Bool.false 5 2) qz61) Bool.false 5 2 0 1 Bool.false 97714 1000 0 1 (BSN.s_add_nat_mk qz61 Bool.false 97714 1000 2 (@Eq.refl Real qz61))

noncomputable abbrev qz614 := (ep1131 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz61 Bool.false 5 2 0 1 Bool.false 97714 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz375))

noncomputable def ep1132 := ep1130 (@Enclosure.Complex.IsNear.re_isNear qz66 Bool.false 5 2 0 1 Bool.false 97714 1000 0 1 qz614)

noncomputable def ep1133 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.im qz66) 48857 250 0 1 97714 1000 0 1 2387006449 125000

noncomputable def ep1134 := @ep1133 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 2386818949 250000 0 1 Bool.false 48857 250 0 1 qz613)

noncomputable def ep1135 := ep1134 (@Enclosure.Complex.IsNear.im_isNear qz66 Bool.false 5 2 0 1 Bool.false 97714 1000 0 1 qz614)

noncomputable def ep1136 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2)) qz66 Bool.true 21482120541 500000 0 1 Bool.true 116551742141293 125000000 0 1 (@ep1109 537053013525000 21482120541 500000 0 1 (ep1132 rfl) (ep1135 rfl) rfl rfl)

noncomputable def ep1137 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.im qz66)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.re qz66)) 116612813391293 125000000 0 1 48857 100 0 1

noncomputable def ep1138 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.im qz66) 2386818949 250000 0 1 97714 1000 0 1 116612813391293 125000000

noncomputable def ep1139 := @ep1138 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 2386818949 250000 0 1 Bool.false 48857 250 0 1 qz613)

noncomputable def ep1140 := ep1139 (@Enclosure.Complex.IsNear.im_isNear qz66 Bool.false 5 2 0 1 Bool.false 97714 1000 0 1 qz614)

noncomputable def ep1141 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.re qz66) 48857 250 0 1 5 2 0 1 48857 100

noncomputable def ep1142 := @ep1141 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 2386818949 250000 0 1 Bool.false 48857 250 0 1 qz613)

noncomputable def ep1143 := ep1142 (@Enclosure.Complex.IsNear.re_isNear qz66 Bool.false 5 2 0 1 Bool.false 97714 1000 0 1 qz614)

noncomputable abbrev qz615 := (ep1136 (@ep1137 11655174214129300 116551742141293 125000000 0 1 (ep1140 rfl) (ep1143 rfl) rfl rfl))

theorem EMRow28.d20 : Enclosure.Complex.IsNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 21482120541 500000 0 1 Bool.true 116551742141293 125000000 0 1 := ep1108 (BSN.ascPochhammer_succ_eval_c 2 3 qz64 rfl) qz615

theorem EMRow28.d21 : @Eq Nat (Nat.pow 25 3) 15625 := @Eq.refl Nat 15625

noncomputable def ep1144 := nat_lit 459129705833673352039539068191121974421467

noncomputable def ep1145 := nat_lit 161256042438361222804930560000000000000000

noncomputable def ep1146 := nat_lit 59525995297007490738321620339191293687460127641367

noncomputable def ep1147 := nat_lit 8237555818061858825005676804261806080000000000000000

noncomputable abbrev qz68 := (Complex.Stirling.logGammaStirling 2 qz369)

noncomputable abbrev qz616 := (@HAdd.hAdd Complex Complex Complex qz811 qz812 (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I (@HDiv.hDiv Complex Complex Complex qz813 (↑(Enclosure.sfrac Bool.false 97714 1000)) (2 : Complex))))

noncomputable abbrev qz398 := qz616

noncomputable abbrev qz69 := qz398

noncomputable abbrev qz399 := (@HMul.hMul Real Real Real qz0 (@HDiv.hDiv Real Real Real qz1 qz61 (2 : Real)) (Real.log Real.pi))

noncomputable def ep1148 := Complex.re (@HMul.hMul Complex Complex Complex qz3 (Complex.exp (@HMul.hMul Complex Complex Complex qz3 Complex.I ↑(@HSub.hSub Real Real Real qz326 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz399))) (zetaApproximant qz64 2 25))

noncomputable def ep1149 := @Enclosure.Real.IsNear.of_eq ep1148 (@HSub.hSub Real Real Real qz326 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz326 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz399)) (Complex.re (zetaApproximant qz64 2 25))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz326 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz399)) (Complex.im (zetaApproximant qz64 2 25))))

noncomputable def ep1150 := nat_lit 275478219780076217318534586212574021980111

noncomputable def ep1151 := @Enclosure.Real.IsNear.subLit_tt_n (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz326 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz399)) (Complex.re (zetaApproximant qz64 2 25))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz326 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz399)) (Complex.im (zetaApproximant qz64 2 25))) ep1150

noncomputable def ep1152 := nat_lit 96753625463016733682958336000000000000000

noncomputable def ep1153 := nat_lit 59444122314629992693466940786261356098260892280941

noncomputable def ep1154 := nat_lit 990699680515237027863244752093318077

noncomputable def ep1155 := nat_lit 241884063657541834207395840000000000000000

noncomputable def ep1156 := nat_lit 40936491188749022427339776464968794599617680213

noncomputable def ep1157 := nat_lit 4118777909030929412502838402130903040000000000000000

noncomputable def ep1158 := nat_lit 66633695395764420911477227397181832947926301731717113546845997498368000000000000000

noncomputable def ep1159 := @Enclosure.Real.IsNear.mulLit_tf (Real.cos (@HSub.hSub Real Real Real qz326 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz399)) (Complex.re (zetaApproximant qz64 2 25)) 524287 524288 34582439

noncomputable def ep1160 := nat_lit 525434008052986660585775703407816753

noncomputable def ep1161 := nat_lit 184542895246537654272000000000000000

noncomputable def ep1162 := nat_lit 695237026002945500106798550379532718601

noncomputable def ep1163 := nat_lit 120405934718079725218037760000000000000000

noncomputable def ep1164 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz326 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz399)) Bool.true 524287 524288 34582439

noncomputable abbrev qz957 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11117827) qz285)

noncomputable def ep1165 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz326 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz399) qz957 Bool.false 11117827 131072 261

noncomputable def ep1166 := nat_lit 30560450515830533162045772873

noncomputable def ep1167 := nat_lit 360287970189639680000000000

noncomputable def ep1168 := nat_lit 9109927780631232767987552978949623

noncomputable def ep1169 := nat_lit 18364975592975106048000000000000000000

noncomputable def ep1170 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz326 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz399) Bool.false ep1166 ep1167 ep1168 ep1169

noncomputable def ep1171 := nat_lit 50710655843332861625405772873

noncomputable def ep1172 := nat_lit 2264395458350465279987552978949623

noncomputable def ep1173 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz399 ep1171 ep1167 ep1172 ep1169 3665300997 65536000

noncomputable def ep1174 := nat_lit 2002809685005469821307831771004928000

noncomputable def ep1175 := nat_lit 110677195427577092211762339

noncomputable def ep1176 := nat_lit 1441151880758558720000000

noncomputable def ep1177 := nat_lit 1890372235170422617533999865210409

noncomputable def ep1178 := nat_lit 9182487796487553024000000000000000000

noncomputable def ep1179 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz22 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz69 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true ep1175 ep1176 ep1177 ep1178 Bool.false ep1171 ep1167

noncomputable def ep1180 := nat_lit 88254030229008011251762339

noncomputable def ep1181 := nat_lit 1820003490790743886011273698682409

noncomputable def ep1182 := nat_lit 52922842767054965945405772873

noncomputable def ep1183 := nat_lit 1982920481603079328801602766853623

noncomputable def ep1184 := @Enclosure.Complex.IsNear.subLitP qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz69 (@Nat.cast Complex Complex.instNatCast j))) Bool.true ep1180 ep1176 ep1181 ep1178 Bool.false ep1182 ep1167 ep1183

noncomputable def ep1185 := nat_lit 249222888043023878097886538644568326275072

noncomputable def ep1186 := nat_lit 7136890336242104412510984510476745487417344

noncomputable abbrev qz400 := (@HSub.hSub Complex Complex Complex qz580 qz605 qz549)

noncomputable abbrev qz401 := (Complex.log qz605)

noncomputable abbrev qz70 := (@HSub.hSub Complex Complex Complex qz580 (@HMul.hMul Complex Complex Complex qz255 qz400 qz401) qz369)

noncomputable def ep1187 := @Enclosure.Complex.IsNear.of_eq qz68 (@HAdd.hAdd Complex Complex Complex qz15 (@HAdd.hAdd Complex Complex Complex qz15 qz70 qz871) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz22 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz29 qz55 (@HSub.hSub Int Int Int qz30 qz31 (@HMul.hMul Int Int Int qz32 qz33 (@Nat.cast Int instNatCastInt k)))))) Bool.true ep1180

noncomputable def ep1188 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz15 qz70 qz871) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz22 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz29 qz55 (@HSub.hSub Int Int Int qz30 qz31 (@HMul.hMul Int Int Int qz32 qz33 (@Nat.cast Int instNatCastInt k))))) Bool.true 275794507685942489457 4503599627370496000

noncomputable def ep1189 := nat_lit 12970366926827028480000000

noncomputable def ep1190 := nat_lit 3242591731706757120000000000

noncomputable def ep1191 := nat_lit 397460817653304969237175225149780492550144000

noncomputable def ep1192 := nat_lit 476686589930192188148099875474797151194710016000

noncomputable def ep1193 := @ep1188 51727567333535496287 260982000000000000000000 Bool.false 1323086317202576946229 9007199254740992000 28178500070618727907 260982000000000000000000 Bool.false 212230493585374477661 ep1176 2139216470266399 ep1189 Bool.true 609921048111903754227127 ep1167 6147747290375391293 ep1190 Bool.true ep1191 ep1180 ep1176 ep1181 ep1178 Bool.false ep1192

noncomputable def ep1194 := @Enclosure.Complex.IsNear.addLitP qz70 qz871 Bool.true 279933035093152985457 4503599627370496000 50732000011758152537 260982000000000000000000

noncomputable def ep1195 := nat_lit 36148937711411853978107904

noncomputable def ep1196 := @ep1194 Bool.false 1323086317202576946229 9007199254740992000 28178500070618727907 260982000000000000000000 Bool.false 120447 131072 1 262144 Bool.false 0 1 0 1 Bool.true ep1195 275794507685942489457 4503599627370496000 51727567333535496287 260982000000000000000000 Bool.false 1323086317202576946229 1323086317202576946229 9007199254740992000

noncomputable abbrev qz71 := (@HMul.hMul Complex Complex Complex qz255 qz400 qz401)

noncomputable def ep1197 := @Enclosure.Complex.IsNear.subLitP qz71 qz55 Bool.true 260792736676828377457 4503599627370496000 50732000011758152537 260982000000000000000000 Bool.false 1763151051191457592373

noncomputable def ep1198 := nat_lit 5292345268810307784916000

noncomputable def ep1199 := @ep1197 9007199254740992000 28178500070618727907 260982000000000000000000 Bool.false 17000 4000 0 1 Bool.false 195428 4000 0 1 Bool.true 1119732140372611941828000 279933035093152985457 4503599627370496000 50732000011758152537 260982000000000000000000 Bool.false ep1198 1323086317202576946229 9007199254740992000 28178500070618727907 260982000000000000000000

noncomputable abbrev qz72 := qz400

noncomputable abbrev qz73 := qz401

noncomputable def ep1200 := @Enclosure.Complex.IsNear.mul qz72 qz73 Bool.true 260792736676828377457 4503599627370496000 50732000011758152537 260982000000000000000000 Bool.false 1763151051191457592373 9007199254740992000 28178500070618727907

noncomputable def ep1201 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re qz72) (Complex.re qz73)) (@HMul.hMul Real Real Real qz0 (Complex.im qz72) (Complex.im qz73)) 525930286704470835 36028797018963968 500000001435401 69595200000000000000 40816752814360903979 562949953421312000

noncomputable def ep1202 := nat_lit 1174506071718696166026178615073308672

noncomputable def ep1203 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz72) (Complex.re qz73) 15000 4000 0 1 35062019113631389 9007199254740992 500000001435401 260982000000000000000

noncomputable def ep1204 := @Enclosure.Complex.IsNear.re_isNear qz72 Bool.false 15000 4000 0 1 Bool.false 195428 4000 0 1

noncomputable def ep1205 := @Enclosure.Complex.IsNear.of_eq qz72 (Complex.mk (Enclosure.sfrac Bool.false 15000 4000) qz372) Bool.false 15000 4000 0 1 Bool.false 195428 4000 0

noncomputable abbrev qz617 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 17000 4000) qz372))

noncomputable def ep1206 := @Enclosure.Complex.IsNear.of_eq qz73 qz617 Bool.false 35062019113631389 9007199254740992 500000001435401 260982000000000000000 Bool.false 835433055946147 562949953421312 1000000000130491 260982000000000000000

noncomputable def ep1207 := nat_lit 386552839639477548085376758708911232648151040

noncomputable def ep1208 := nat_lit 831658691087452241307573873443124911013888

noncomputable def ep1209 := nat_lit 3196020279176435194056906755228801630208

noncomputable def ep1210 := BSN.log_dyadic_bound 5713103184 71249103184 3 2 ep1207 524288 260982 ep1208 ep1209 84260 76962206368 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 5713103184) (BSN.artanhQ 71249103184) 0 2 ep1208 ep1207 ep1209 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1211 := @Enclosure.Real.IsNear.mulLit_ff qz323 (Real.log (Enclosure.sfrac Bool.false 38481103184 16000000)) 1 2 0 1 35062019113631389 4503599627370496 500000001435401 130491000000000000000 35062019113631389 9007199254740992 500000001435401 260982000000000000000 qz324 (BSN.isNear_log_sfrac 38481103184 16000000 35062019113631389 4503599627370496 500000001435401 130491000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 38481103184) qz585)) Bool.false 147060767016380589408256 18889465931478580854784 1000000002870802 260982000000000000000 35062019113631389 4503599627370496 500000001435401 130491000000000000000 (BSN.log_rat_reduce_isNear 38481103184 16000000 11 76962206368 65536000000 84260 524288 24973259072661432 36028797018963968 260982 1000000000000000 rfl rfl rfl rfl (ep1210 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1212 := BSN.arctan_dyadic_bound_f 17000 195428 1 0 524288 260982 0 1 1 0 1 1 45492 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 17000) (BSN.arctanEvenQ 195428) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 17000) (BSN.arctanOddQ 195428) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz618 := (@Nat.cast Real Real.instNatCast 195428)

noncomputable def ep1213 := @Enclosure.Real.IsNear.subLit_ff_p qz333 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz586 qz618)) 884279719003555 562949953421312 1 2000000000000000 45492 524288 1 260982 438007526035893518336 835433055946147 562949953421312 1000000000130491 260982000000000000000 qz334 (ep1212 rfl) rfl rfl

noncomputable abbrev qz619 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 195428) (@Nat.cast Real Real.instNatCast 17000)))

noncomputable def ep1214 := @Enclosure.Complex.IsNear.re_isNear qz73 Bool.false 35062019113631389 9007199254740992 500000001435401 260982000000000000000 Bool.false 835433055946147 562949953421312 1000000000130491 260982000000000000000 (ep1206 (@congrArg Complex Complex qz55 qz606 Complex.log (BSN.w_shift_mk qz61 Bool.false 97714 1000 4 (@Eq.refl Real qz61) rfl)) (@Enclosure.Complex.IsNear.of_parts qz617 Bool.false 35062019113631389 9007199254740992 500000001435401 260982000000000000000 Bool.false 835433055946147 562949953421312 1000000000130491 260982000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz617) (@HMul.hMul Real Real Real qz0 qz323 (Real.log (Enclosure.sfrac Bool.false 38481103184 16000000))) Bool.false 35062019113631389 9007199254740992 500000001435401 260982000000000000000 (Enclosure.clog_re_eq 17000 195428 4000 38481103184 16000000 rfl rfl rfl) (ep1211 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz617) qz619 Bool.false 835433055946147 562949953421312 1000000000130491 260982000000000000000 (Enclosure.clog_im_eq 17000 195428 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz619 (@HSub.hSub Real Real Real qz326 qz333 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz586 qz618))) Bool.false 835433055946147 562949953421312 1000000000130491 260982000000000000000 (BSN.arctan_recip 195428 17000 rfl rfl) ep1213))))

noncomputable def ep1215 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz72) (Complex.im qz73) 195428 4000 0 1 835433055946147 562949953421312 1000000000130491 260982000000000000000

noncomputable def ep1216 := @Enclosure.Complex.IsNear.im_isNear qz72 Bool.false 15000 4000 0 1 Bool.false 195428 4000 0 1

noncomputable def ep1217 := @Enclosure.Complex.IsNear.im_isNear qz73 Bool.false 35062019113631389 9007199254740992 500000001435401 260982000000000000000 Bool.false 835433055946147 562949953421312 1000000000130491 260982000000000000000 (ep1206 (@congrArg Complex Complex qz55 qz606 Complex.log (BSN.w_shift_mk qz61 Bool.false 97714 1000 4 (@Eq.refl Real qz61) rfl)) (@Enclosure.Complex.IsNear.of_parts qz617 Bool.false 35062019113631389 9007199254740992 500000001435401 260982000000000000000 Bool.false 835433055946147 562949953421312 1000000000130491 260982000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz617) (@HMul.hMul Real Real Real qz0 qz323 (Real.log (Enclosure.sfrac Bool.false 38481103184 16000000))) Bool.false 35062019113631389 9007199254740992 500000001435401 260982000000000000000 (Enclosure.clog_re_eq 17000 195428 4000 38481103184 16000000 rfl rfl rfl) (ep1211 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz617) qz619 Bool.false 835433055946147 562949953421312 1000000000130491 260982000000000000000 (Enclosure.clog_im_eq 17000 195428 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz619 (@HSub.hSub Real Real Real qz326 qz333 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz586 qz618))) Bool.false 835433055946147 562949953421312 1000000000130491 260982000000000000000 (BSN.arctan_recip 195428 17000 rfl rfl) ep1213))))

noncomputable abbrev qz402 := (@ep1205 1 (BSN.w_sub_half_mk qz61 Bool.false 97714 1000 4 (@Eq.refl Real qz61) rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 15000 4000) (Enclosure.sfrac Bool.false 195428 4000) Bool.false 15000 4000 0 1 Bool.false 195428 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 15000 4000) (Enclosure.Real.IsNear.const Bool.false 195428 4000)))

noncomputable def ep1218 := @ep1201 48857000006375398787 260982000000000000000000 ep1202 260792736676828377457 4503599627370496000 50732000011758152537 260982000000000000000000 (@ep1203 525930286704470835 36028797018963968 500000001435401 69595200000000000000 (ep1204 qz402) ep1214 rfl) (@ep1215 40816752814360903979 562949953421312000 48857000006375398787 260982000000000000000000 (ep1216 qz402) ep1217 rfl) rfl

noncomputable def ep1219 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re qz72) (Complex.im qz73)) (@HMul.hMul Real Real Real qz0 (Complex.im qz72) (Complex.re qz73)) 12531495839192205 2251799813685248 1000000000130491 69595200000000000000 1713025067834688772373 9007199254740992000

noncomputable def ep1220 := nat_lit 3970263208571873365229795558507413504

noncomputable def ep1221 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz72) (Complex.im qz73) 15000 4000 0 1 835433055946147 562949953421312 1000000000130491 260982000000000000000

noncomputable def ep1222 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz72) (Complex.re qz73) 195428 4000 0 1 35062019113631389 9007199254740992 500000001435401 260982000000000000000

noncomputable def ep1223 := @ep1219 24428500070129386657 260982000000000000000000 ep1220 1763151051191457592373 9007199254740992000 28178500070618727907 260982000000000000000000 (@ep1221 12531495839192205 2251799813685248 1000000000130491 69595200000000000000 (ep1204 qz402) ep1217 rfl) (@ep1222 1713025067834688772373 9007199254740992000 24428500070129386657 260982000000000000000000 (ep1216 qz402) ep1214 rfl) rfl

noncomputable def ep1224 := ep1199 (@ep1200 260982000000000000000000 (ep1218 rfl) (ep1223 rfl)) qz63 rfl rfl rfl rfl rfl rfl

noncomputable def ep1225 := @ep1196 28178500070618727907 260982000000000000000000 (ep1224 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz26 (↑qz253) Bool.false 120447 131072 1 262144 Bool.false 0 1 0 1 (@ep428 131072 1 262144 (ep430 rfl) (ep432 rfl) rfl rfl) (@ep433 1 0 1 (ep435 rfl) (ep437 rfl) rfl rfl))

noncomputable abbrev qz74 := (@HPow.hPow Complex Int Complex qz583 qz369 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) qz332 (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) qz584 (@Nat.cast Int instNatCastInt 2))))

noncomputable def ep1226 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz22 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz29 qz55 (@HSub.hSub Int Int Int qz30 qz31 (@HMul.hMul Int Int Int qz32 qz33 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz15 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz22 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz29 qz55 (@HSub.hSub Int Int Int qz30 qz31 (@HMul.hMul Int Int Int qz32 qz33 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz37)) qz38) qz74)) Bool.false 212230493585374477661 ep1176 2139216470266399 ep1189

noncomputable def ep1227 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz22 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz29 qz55 (@HSub.hSub Int Int Int qz30 qz31 (@HMul.hMul Int Int Int qz32 qz33 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz37)) qz38) qz74) Bool.false 5059761 34359738368 17 103079215104 Bool.true

noncomputable def ep1228 := nat_lit 7292184233304969323736620597248

noncomputable def ep1229 := nat_lit 5239181909565338345410264442077184000

noncomputable def ep1230 := @ep1227 14541455481 8589934592000 48857 25769803776000 Bool.false 8735571934477661 ep1176 121430266399 ep1189 Bool.true 8199214101514227127 ep1167 113974535391293 ep1190 Bool.false ep1228 212230493585374477661 ep1176 2139216470266399 ep1189 Bool.true ep1229 609921048111903754227127 ep1167 6147747290375391293

noncomputable abbrev qz75 := (@HPow.hPow Complex Int Complex qz583 qz369 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) qz332 (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) qz584 (@Nat.cast Int instNatCastInt 1))))

noncomputable def ep1231 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz22 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz29 qz55 (@HSub.hSub Int Int Int qz30 qz31 (@HMul.hMul Int Int Int qz32 qz33 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz15 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz22 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz29 qz55 (@HSub.hSub Int Int Int qz30 qz31 (@HMul.hMul Int Int Int qz32 qz33 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz40)) qz41) qz75)) Bool.false 5059761 34359738368 17 103079215104

noncomputable def ep1232 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz22 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz29 qz55 (@HSub.hSub Int Int Int qz30 qz31 (@HMul.hMul Int Int Int qz32 qz33 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz40)) qz41) qz75) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1233 := @ep1232 0 1 0 1 Bool.false 5059761 34359738368 17 103079215104 Bool.true 14541455481 8589934592000 48857 25769803776000 Bool.false 5059761 5059761 34359738368 17 103079215104 Bool.true 14541455481 14541455481 8589934592000 48857

noncomputable def ep1234 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz22 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz29 qz55 (@HSub.hSub Int Int Int qz30 qz31 (@HMul.hMul Int Int Int qz32 qz33 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz265 qz265) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1235 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz40)) qz41) qz75 Bool.false 5059761 34359738368 17 103079215104 Bool.true 14541455481 8589934592000 48857 25769803776000

noncomputable def ep1236 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz40)) qz41)) (Complex.re qz75)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz40)) qz41)) (Complex.im qz75)) 5059761 34359738368 17 103079215104 0 1 0

noncomputable def ep1237 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz40)) qz41)) (Complex.re qz75) 1 12 0 1 15179283 8589934592 17 8589934592 5059761

noncomputable def ep1238 := @Enclosure.Complex.IsNear.re_isNear qz75 Bool.false 15179283 8589934592 17 8589934592 Bool.true 43624366443 2147483648000 48857 2147483648000

noncomputable def ep1239 := @Enclosure.Complex.IsNear.of_eq qz75 (@Inv.inv Complex Complex.instInv qz58) Bool.false 15179283 8589934592 17 8589934592 Bool.true 43624366443 2147483648000 48857

noncomputable def ep1240 := @Enclosure.Complex.IsNear.of_parts (@Inv.inv Complex Complex.instInv qz58) Bool.false 15179283 8589934592 17 8589934592 Bool.true 43624366443 2147483648000 48857

noncomputable def ep1241 := @Enclosure.Real.IsNear.mulLit_ff qz59 (@Inv.inv Real Real.instInv (@DFunLike.coe qz337 Complex (fun (x : Complex) => Real) qz338 Complex.normSq qz58)) 17000 4000 0 1 892899 2147483648 1 2147483648

noncomputable def ep1242 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz337 Complex (fun (x : Complex) => Real) qz338 Complex.normSq qz58)) Bool.false 892899 2147483648 1 2147483648 892899 2147483648 1

noncomputable def ep1243 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz337 Complex (fun (x : Complex) => Real) qz338 Complex.normSq qz58) (@HAdd.hAdd Real Real Real qz590 (@HMul.hMul Real Real Real qz0 qz59 qz59) (@HMul.hMul Real Real Real qz0 qz60 qz60)) Bool.false 2405068949 1000000 0 1

noncomputable def ep1244 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz59 qz59) (@HMul.hMul Real Real Real qz0 qz60 qz60) 289 16 0 1 2387006449 1000000

noncomputable def ep1245 := @Enclosure.Real.IsNear.mulLit_ff qz59 qz59 17000 4000 0 1 17000 4000 0 1

noncomputable def ep1246 := @Enclosure.Real.IsNear.mulLit_ff qz60 qz60 195428 4000 0 1 195428 4000 0 1

noncomputable def ep1247 := @ep1244 0 1 38481103184 2405068949 1000000 0 1 (@ep1245 289 16 0 1 (ep809 qz62) (ep809 qz62) rfl) (@ep1246 2387006449 1000000 0 1 (ep814 qz62) (ep814 qz62) rfl)

noncomputable def ep1248 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz337 Complex (fun (x : Complex) => Real) qz338 Complex.normSq qz58) 2405068949 1000000 0 1 446449 446450 1073741824 (ep1243 (Enclosure.Complex.normSq_eq_mul_add_mul qz58) (ep1247 rfl rfl)) rfl

noncomputable def ep1249 := @Enclosure.Real.IsNear.of_eq (Complex.re (@Inv.inv Complex Complex.instInv qz58)) (@HMul.hMul Real Real Real qz0 qz59 (@Inv.inv Real Real.instInv (@DFunLike.coe qz337 Complex (fun (x : Complex) => Real) qz338 Complex.normSq qz58))) Bool.false 15179283 8589934592 17 8589934592 (Enclosure.Complex.inv_re_eq_mul qz58) (@ep1241 15179283 8589934592 17 8589934592 (ep809 qz62) (@ep1242 2147483648 (ep1248 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep1250 := @Enclosure.Real.IsNear.of_eq (Complex.im (@Inv.inv Complex Complex.instInv qz58)) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz60) (@Inv.inv Real Real.instInv (@DFunLike.coe qz337 Complex (fun (x : Complex) => Real) qz338 Complex.normSq qz58))) Bool.true 43624366443 2147483648000 48857 2147483648000 (Enclosure.Complex.inv_im_eq_mul qz58)

noncomputable def ep1251 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz60) (@Inv.inv Real Real.instInv (@DFunLike.coe qz337 Complex (fun (x : Complex) => Real) qz338 Complex.normSq qz58)) 195428 4000 0 1 892899 2147483648 1

noncomputable def ep1252 := @ep1251 2147483648 43624366443 2147483648000 48857 2147483648000 (@Enclosure.Real.IsNear.neg qz60 Bool.false 195428 4000 0 1 (ep814 qz62)) (@ep1242 2147483648 (ep1248 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep1253 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz40)) qz41)) (Complex.im qz75) 0 1 0 1 43624366443 2147483648000 48857 2147483648000 0

noncomputable def ep1254 := @Enclosure.Complex.IsNear.im_isNear qz75 Bool.false 15179283 8589934592 17 8589934592 Bool.true 43624366443 2147483648000 48857 2147483648000

noncomputable abbrev qz620 := (@ep1239 2147483648000 (BSN.zpow_one_sub_two_mul qz55 1 1 rfl rfl) (@ep1240 2147483648000 ep1249 (ep1250 ep1252)))

noncomputable def ep1255 := @ep1236 1 5059761 5059761 34359738368 17 103079215104 (@ep1237 34359738368 17 103079215104 ep452 (ep1238 qz620) rfl) (@ep1253 1 0 1 ep469 (ep1254 qz620) rfl) rfl

noncomputable def ep1256 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz40)) qz41)) (Complex.im qz75)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz40)) qz41)) (Complex.re qz75)) 14541455481 8589934592000 48857 25769803776000 0 1 0

noncomputable def ep1257 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz40)) qz41)) (Complex.im qz75) 1 12 0 1 43624366443 2147483648000 48857 2147483648000 14541455481

noncomputable def ep1258 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz40)) qz41)) (Complex.re qz75) 0 1 0 1 15179283 8589934592 17 8589934592 0

noncomputable def ep1259 := @ep1256 1 14541455481 14541455481 8589934592000 48857 25769803776000 (@ep1257 8589934592000 48857 25769803776000 ep452 (ep1254 qz620) rfl) (@ep1258 1 0 1 ep469 (ep1238 qz620) rfl) rfl

noncomputable def ep1260 := @ep1233 25769803776000 (@ep1234 0 1 0 1 (BSN.stirling_sum_base qz55) qz339) (ep1235 (ep1255 rfl) (ep1259 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep1261 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz37)) qz38) qz74 Bool.false 8735571934477661 ep1176 121430266399 ep1189 Bool.true 8199214101514227127 ep1167 113974535391293 ep1190

noncomputable def ep1262 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz37)) qz38)) (Complex.re qz74)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz37)) qz38)) (Complex.im qz74)) 8735571934477661 ep1176 121430266399 ep1189 0 1 0

noncomputable def ep1263 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz37)) qz38)) (Complex.re qz74) 1 360 0 1 78620147410298949 36028797018963968000000 121430266399 36028797018963968000000 8735571934477661

noncomputable def ep1264 := nat_lit 9007199254740992000000000

noncomputable def ep1265 := @Enclosure.Complex.IsNear.re_isNear qz74 Bool.true 78620147410298949 36028797018963968000000 121430266399 36028797018963968000000 Bool.false 73792926913628044143 ep1264 113974535391293 ep1264

noncomputable def ep1266 := @Enclosure.Complex.IsNear.of_eq qz74 (@Inv.inv Complex Complex.instInv qz53) Bool.true 78620147410298949 36028797018963968000000 121430266399 36028797018963968000000 Bool.false 73792926913628044143 ep1264 113974535391293

noncomputable def ep1267 := @Enclosure.Complex.IsNear.of_parts (@Inv.inv Complex Complex.instInv qz53) Bool.true 78620147410298949 36028797018963968000000 121430266399 36028797018963968000000 Bool.false 73792926913628044143 ep1264 113974535391293

noncomputable abbrev qz76 := (Complex.re qz368)

noncomputable def ep1268 := @Enclosure.Real.IsNear.mulLit_tf qz76 (@Inv.inv Real Real.instInv (@DFunLike.coe qz337 Complex (fun (x : Complex) => Real) qz338 Complex.normSq qz53)) 121430266399 4000000 0 1 647451 9007199254740992 1 9007199254740992

noncomputable def ep1269 := @Enclosure.Complex.IsNear.re_isNear qz53 Bool.true 121430266399 4000000 0 1 Bool.true 113974535391293 1000000000 0 1

noncomputable def ep1270 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz337 Complex (fun (x : Complex) => Real) qz338 Complex.normSq qz53)) Bool.false 647451 9007199254740992 1 9007199254740992 647451 9007199254740992 1

noncomputable def ep1271 := nat_lit 13911776567519357377320274349

noncomputable abbrev qz77 := (Complex.im qz368)

noncomputable def ep1272 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz337 Complex (fun (x : Complex) => Real) qz338 Complex.normSq qz53) (@HAdd.hAdd Real Real Real qz590 (@HMul.hMul Real Real Real qz0 qz76 qz76) (@HMul.hMul Real Real Real qz0 qz77 qz77)) Bool.false ep1271 1000000000000000000 0 1

noncomputable def ep1273 := nat_lit 12990194717661100600620211849

noncomputable def ep1274 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz76 qz76) (@HMul.hMul Real Real Real qz0 qz77 qz77) 14745309597732108427201 16000000000000 0 1 ep1273 1000000000000000000

noncomputable def ep1275 := nat_lit 222588425080309718037124389584000000000000

noncomputable def ep1276 := @Enclosure.Real.IsNear.mulLit_tt qz76 qz76 121430266399 4000000 0 1 121430266399 4000000 0 1

noncomputable def ep1277 := @Enclosure.Real.IsNear.mulLit_tt qz77 qz77 113974535391293 1000000000 0 1 113974535391293 1000000000 0 1

noncomputable def ep1278 := @Enclosure.Complex.IsNear.im_isNear qz53 Bool.true 121430266399 4000000 0 1 Bool.true 113974535391293 1000000000 0 1

noncomputable def ep1279 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz337 Complex (fun (x : Complex) => Real) qz338 Complex.normSq qz53) ep1271 1000000000000000000 0 1 323725 323726 4503599627370496 (ep1272 (Enclosure.Complex.normSq_eq_mul_add_mul qz53) (@ep1274 0 1 ep1275 ep1271 1000000000000000000 0 1 (@ep1276 14745309597732108427201 16000000000000 0 1 (ep1269 EMRow28.d15) (ep1269 EMRow28.d15) rfl) (@ep1277 ep1273 1000000000000000000 0 1 (ep1278 EMRow28.d15) (ep1278 EMRow28.d15) rfl) rfl rfl)) rfl

noncomputable def ep1280 := @Enclosure.Real.IsNear.of_eq (Complex.re (@Inv.inv Complex Complex.instInv qz53)) (@HMul.hMul Real Real Real qz0 qz76 (@Inv.inv Real Real.instInv (@DFunLike.coe qz337 Complex (fun (x : Complex) => Real) qz338 Complex.normSq qz53))) Bool.true 78620147410298949 36028797018963968000000 121430266399 36028797018963968000000 (Enclosure.Complex.inv_re_eq_mul qz53) (@ep1268 78620147410298949 36028797018963968000000 121430266399 36028797018963968000000 (ep1269 EMRow28.d15) (@ep1270 9007199254740992 (ep1279 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep1281 := @Enclosure.Real.IsNear.of_eq (Complex.im (@Inv.inv Complex Complex.instInv qz53)) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz77) (@Inv.inv Real Real.instInv (@DFunLike.coe qz337 Complex (fun (x : Complex) => Real) qz338 Complex.normSq qz53))) Bool.false 73792926913628044143 ep1264 113974535391293 ep1264 (Enclosure.Complex.inv_im_eq_mul qz53)

noncomputable def ep1282 := @Enclosure.Real.IsNear.mulLit_ff (@Neg.neg Real Real.instNeg qz77) (@Inv.inv Real Real.instInv (@DFunLike.coe qz337 Complex (fun (x : Complex) => Real) qz338 Complex.normSq qz53)) 113974535391293 1000000000 0 1 647451 9007199254740992 1

noncomputable def ep1283 := @ep1282 9007199254740992 73792926913628044143 ep1264 113974535391293 ep1264 (@Enclosure.Real.IsNear.neg qz77 Bool.true 113974535391293 1000000000 0 1 (ep1278 EMRow28.d15)) (@ep1270 9007199254740992 (ep1279 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep1284 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz37)) qz38)) (Complex.im qz74) 0 1 0 1 73792926913628044143 ep1264 113974535391293 ep1264 0

noncomputable def ep1285 := @Enclosure.Complex.IsNear.im_isNear qz74 Bool.true 78620147410298949 36028797018963968000000 121430266399 36028797018963968000000 Bool.false 73792926913628044143 ep1264 113974535391293 ep1264

noncomputable abbrev qz621 := (@ep1266 ep1264 (BSN.zpow_one_sub_two_mul qz55 2 3 rfl rfl) (@ep1267 ep1264 ep1280 (ep1281 ep1283)))

noncomputable def ep1286 := @ep1262 1 8735571934477661 8735571934477661 ep1176 121430266399 ep1189 (@ep1263 ep1176 121430266399 ep1189 ep481 (ep1265 qz621) rfl) (@ep1284 1 0 1 ep502 (ep1285 qz621) rfl) rfl

noncomputable def ep1287 := @Enclosure.Real.IsNear.addLit_tt (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz37)) qz38)) (Complex.im qz74)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz37)) qz38)) (Complex.re qz74)) 8199214101514227127 ep1167 113974535391293 ep1190 0 1 0

noncomputable def ep1288 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz37)) qz38)) (Complex.im qz74) 1 360 0 1 73792926913628044143 ep1264 113974535391293 ep1264 8199214101514227127

noncomputable def ep1289 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz37)) qz38)) (Complex.re qz74) 0 1 0 1 78620147410298949 36028797018963968000000 121430266399 36028797018963968000000 0

noncomputable def ep1290 := @ep1287 1 8199214101514227127 8199214101514227127 ep1167 113974535391293 ep1190 (@ep1288 ep1167 113974535391293 ep1190 ep481 (ep1285 qz621) rfl) (@ep1289 1 0 1 ep502 (ep1265 qz621) rfl) rfl

noncomputable def ep1291 := @ep1230 ep1190 (@ep1231 Bool.true 14541455481 8589934592000 48857 25769803776000 (BSN.stirling_sum_succ qz55 0 1 rfl) (ep1260 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1261 (ep1286 rfl) (ep1290 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep1292 := @ep1193 ep1182 ep1167 ep1183 ep1169 (ep1225 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep1226 Bool.true 609921048111903754227127 ep1167 6147747290375391293 ep1190 (BSN.stirling_sum_succ qz55 1 2 rfl) (ep1291 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep1293 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz69 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz61 4) Bool.false 35036195622764189 2251799813685248 500000001435401 65245500000000000000 Bool.false 864135517078947 140737488355328

noncomputable abbrev qz958 := (@HAdd.hAdd Complex Complex Complex qz15 qz69 qz551)

noncomputable def ep1294 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz61 4) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.logSumC qz61 3) (Complex.log qz958)) Bool.false 35036195622764189 2251799813685248 500000001435401 65245500000000000000 Bool.false 864135517078947 140737488355328 1000000000130491 65245500000000000000

noncomputable def ep1295 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz61 3) (Complex.log qz958) Bool.false 105096825100352471 9007199254740992 500000001435401 86994000000000000000 Bool.false 2609654334591209 562949953421312 1000000000130491 86994000000000000000 Bool.false

noncomputable def ep1296 := nat_lit 1262311980409284836982473151741952

noncomputable def ep1297 := nat_lit 1945860196357178295644225273856

noncomputable abbrev qz959 := (@HAdd.hAdd Complex Complex Complex qz15 qz69 qz552)

noncomputable def ep1298 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz61 3) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.logSumC qz61 2) (Complex.log qz959)) Bool.false 105096825100352471 9007199254740992 500000001435401 86994000000000000000 Bool.false 2609654334591209 562949953421312 1000000000130491 86994000000000000000

noncomputable def ep1299 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz61 2) (Complex.log qz959) Bool.false 35029604995448477 4503599627370496 500000001435401 130491000000000000000 Bool.false 875640392287651 281474976710656 1000000000130491 130491000000000000000 Bool.false

noncomputable def ep1300 := nat_lit 473314022359769579276508506095616

noncomputable def ep1301 := nat_lit 734552393051923033889234223104

noncomputable abbrev qz960 := (@HAdd.hAdd Complex Complex Complex qz15 qz69 qz575)

noncomputable def ep1302 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz61 2) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.logSumC qz61 1) (Complex.log qz960)) Bool.false 35029604995448477 4503599627370496 500000001435401 130491000000000000000 Bool.false 875640392287651 281474976710656 1000000000130491 130491000000000000000

noncomputable def ep1303 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz61 1) (Complex.log qz960) Bool.false 35028191951208093 9007199254740992 500000001435401 260982000000000000000 Bool.false 881399943431587 562949953421312 1000000000130491 260982000000000000000 Bool.false

noncomputable def ep1304 := nat_lit 631037264017749704989247031738368

noncomputable def ep1305 := nat_lit 985883436104304995771795636224

noncomputable abbrev qz961 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz69 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep1306 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz61 1) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.logSumC qz61 0) qz961) Bool.false 35028191951208093 9007199254740992 500000001435401 260982000000000000000 Bool.false 881399943431587 562949953421312 1000000000130491 260982000000000000000

noncomputable def ep1307 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz61 0) qz961 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable def ep1308 := @Enclosure.Complex.IsNear.of_eq qz961 (Complex.log (Complex.mk qz593 qz372)) Bool.false 35028191951208093 9007199254740992 500000001435401 260982000000000000000 Bool.false 881399943431587 562949953421312 1000000000130491 260982000000000000000

noncomputable def ep1309 := nat_lit 380340605266516854014639895064236283528151040

noncomputable def ep1310 := nat_lit 743613218150638736155534746811152047013888

noncomputable def ep1311 := nat_lit 2598682763013786156674078108238977630208

noncomputable def ep1312 := BSN.log_dyadic_bound 5425103184 70961103184 3 2 ep1309 524288 260982 ep1310 ep1311 80322 76386206368 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 5425103184) (BSN.artanhQ 70961103184) 0 2 ep1310 ep1309 ep1311 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1313 := @Enclosure.Real.IsNear.mulLit_ff qz323 (Real.log (Enclosure.sfrac Bool.false 38193103184 16000000)) 1 2 0 1 35028191951208093 4503599627370496 500000001435401 130491000000000000000 35028191951208093 9007199254740992 500000001435401 260982000000000000000 qz324 (BSN.isNear_log_sfrac 38193103184 16000000 35028191951208093 4503599627370496 500000001435401 130491000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 38193103184) qz585)) Bool.false 146918885613719909302272 18889465931478580854784 1000000002870802 260982000000000000000 35028191951208093 4503599627370496 500000001435401 130491000000000000000 (BSN.log_rat_reduce_isNear 38193103184 16000000 11 76386206368 65536000000 80322 524288 24973259072661432 36028797018963968 260982 1000000000000000 rfl rfl rfl rfl (ep1312 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1314 := BSN.arctan_dyadic_bound_f 1000 195428 1 0 524288 260982 0 1 1 0 1 1 2682 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 195428) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 195428) 0 0 rfl) rfl rfl rfl

noncomputable def ep1315 := @Enclosure.Real.IsNear.subLit_ff_p qz333 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz876 qz618)) 884279719003555 562949953421312 1 2000000000000000 2682 524288 1 260982 462107413541859885056 881399943431587 562949953421312 1000000000130491 260982000000000000000 qz334 (ep1314 rfl) rfl rfl

noncomputable abbrev qz962 := (@HAdd.hAdd Complex Complex Complex qz15 qz69 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable def ep1316 := @ep1307 35028191951208093 9007199254740992 500000001435401 260982000000000000000 Bool.false 881399943431587 562949953421312 1000000000130491 260982000000000000000 Bool.false 35028191951208093 35028191951208093 9007199254740992 500000001435401 260982000000000000000 Bool.false 881399943431587 881399943431587 562949953421312 1000000000130491 260982000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz61 0) (Complex.mk qz265 qz265) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz61) qz339) (ep1308 (@congrArg Complex Complex qz962 (Complex.mk qz593 qz372) Complex.log (BSN.w_shift_mk qz61 Bool.false 97714 1000 0 (@Eq.refl Real qz61) rfl)) (@Enclosure.Complex.IsNear.of_parts (Complex.log (Complex.mk qz593 qz372)) Bool.false 35028191951208093 9007199254740992 500000001435401 260982000000000000000 Bool.false 881399943431587 562949953421312 1000000000130491 260982000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re (Complex.log (Complex.mk qz593 qz372))) (@HMul.hMul Real Real Real qz0 qz323 (Real.log (Enclosure.sfrac Bool.false 38193103184 16000000))) Bool.false 35028191951208093 9007199254740992 500000001435401 260982000000000000000 (Enclosure.clog_re_eq 1000 195428 4000 38193103184 16000000 rfl rfl rfl) (ep1313 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im (Complex.log (Complex.mk qz593 qz372))) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz618 qz876)) Bool.false 881399943431587 562949953421312 1000000000130491 260982000000000000000 (Enclosure.clog_im_eq 1000 195428 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz618 qz876)) (@HSub.hSub Real Real Real qz326 qz333 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz876 qz618))) Bool.false 881399943431587 562949953421312 1000000000130491 260982000000000000000 (BSN.arctan_recip 195428 1000 rfl rfl) ep1315)))) rfl rfl

noncomputable def ep1317 := @Enclosure.Complex.IsNear.of_eq (Complex.log qz960) (Complex.log (Complex.mk qz594 qz372)) Bool.false 35031018039688861 9007199254740992 500000001435401 260982000000000000000 Bool.false 869880841143715 562949953421312 1000000000130491 260982000000000000000

noncomputable def ep1318 := nat_lit 380855411607909288384763990695852529288151040

noncomputable def ep1319 := nat_lit 750736101048832415598352404462483119013888

noncomputable def ep1320 := nat_lit 2644973844615046290231379407488129630208

noncomputable def ep1321 := BSN.log_dyadic_bound 5449103184 70985103184 3 2 ep1318 524288 260982 ep1319 ep1320 80651 76434206368 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 5449103184) (BSN.artanhQ 70985103184) 0 2 ep1319 ep1318 ep1320 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1322 := @Enclosure.Real.IsNear.mulLit_ff qz323 (Real.log (Enclosure.sfrac Bool.false 38217103184 16000000)) 1 2 0 1 35031018039688861 4503599627370496 500000001435401 130491000000000000000 35031018039688861 9007199254740992 500000001435401 260982000000000000000 qz324 (BSN.isNear_log_sfrac 38217103184 16000000 35031018039688861 4503599627370496 500000001435401 130491000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 38217103184) qz585)) Bool.false 146930739087939148447744 18889465931478580854784 1000000002870802 260982000000000000000 35031018039688861 4503599627370496 500000001435401 130491000000000000000 (BSN.log_rat_reduce_isNear 38217103184 16000000 11 76434206368 65536000000 80651 524288 24973259072661432 36028797018963968 260982 1000000000000000 rfl rfl rfl rfl (ep1321 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1323 := BSN.arctan_dyadic_bound_f 5000 195428 1 0 524288 260982 0 1 1 0 1 1 13410 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 195428) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 195428) 0 0 rfl) rfl rfl rfl

noncomputable def ep1324 := @Enclosure.Real.IsNear.subLit_ff_p qz333 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz878 qz618)) 884279719003555 562949953421312 1 2000000000000000 13410 524288 1 260982 456068086441556049920 869880841143715 562949953421312 1000000000130491 260982000000000000000 qz334 (ep1323 rfl) rfl rfl

noncomputable def ep1325 := @ep1303 35031018039688861 9007199254740992 500000001435401 260982000000000000000 Bool.false 869880841143715 562949953421312 1000000000130491 260982000000000000000 Bool.false ep1304 35029604995448477 4503599627370496 500000001435401 130491000000000000000 Bool.false ep1305 875640392287651 281474976710656 1000000000130491 130491000000000000000 (ep1306 (BSN.log_sum_c_succ qz61 0 1 rfl) (ep1316 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1317 (@congrArg Complex Complex qz960 (Complex.mk qz594 qz372) Complex.log (BSN.w_shift_mk qz61 Bool.false 97714 1000 1 (@Eq.refl Real qz61) rfl)) (@Enclosure.Complex.IsNear.of_parts (Complex.log (Complex.mk qz594 qz372)) Bool.false 35031018039688861 9007199254740992 500000001435401 260982000000000000000 Bool.false 869880841143715 562949953421312 1000000000130491 260982000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re (Complex.log (Complex.mk qz594 qz372))) (@HMul.hMul Real Real Real qz0 qz323 (Real.log (Enclosure.sfrac Bool.false 38217103184 16000000))) Bool.false 35031018039688861 9007199254740992 500000001435401 260982000000000000000 (Enclosure.clog_re_eq 5000 195428 4000 38217103184 16000000 rfl rfl rfl) (ep1322 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im (Complex.log (Complex.mk qz594 qz372))) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz618 qz878)) Bool.false 869880841143715 562949953421312 1000000000130491 260982000000000000000 (Enclosure.clog_im_eq 5000 195428 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz618 qz878)) (@HSub.hSub Real Real Real qz326 qz333 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz878 qz618))) Bool.false 869880841143715 562949953421312 1000000000130491 260982000000000000000 (BSN.arctan_recip 195428 5000 rfl rfl) ep1324)))) rfl rfl

noncomputable def ep1326 := @Enclosure.Complex.IsNear.of_eq (Complex.log qz959) (Complex.log (Complex.mk qz595 qz372)) Bool.false 35037615109455517 9007199254740992 500000001435401 260982000000000000000 Bool.false 858373550015907 562949953421312 1000000000130491 260982000000000000000

noncomputable def ep1327 := nat_lit 382058658693617442584662624042157102728151040

noncomputable def ep1328 := nat_lit 767506868480980504927670159888922287013888

noncomputable def ep1329 := nat_lit 2755390195763546071627123612402817630208

noncomputable def ep1330 := BSN.log_dyadic_bound 5505103184 71041103184 3 2 ep1327 524288 260982 ep1328 ep1329 81419 76546206368 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 5505103184) (BSN.artanhQ 71041103184) 0 2 ep1328 ep1327 ep1329 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1331 := @Enclosure.Real.IsNear.mulLit_ff qz323 (Real.log (Enclosure.sfrac Bool.false 38273103184 16000000)) 1 2 0 1 35037615109455517 4503599627370496 500000001435401 130491000000000000000 35037615109455517 9007199254740992 500000001435401 260982000000000000000 qz324 (BSN.isNear_log_sfrac 38273103184 16000000 35037615109455517 4503599627370496 500000001435401 130491000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 38273103184) qz585)) Bool.false 146958409204049712775168 18889465931478580854784 1000000002870802 260982000000000000000 35037615109455517 4503599627370496 500000001435401 130491000000000000000 (BSN.log_rat_reduce_isNear 38273103184 16000000 11 76546206368 65536000000 81419 524288 24973259072661432 36028797018963968 260982 1000000000000000 rfl rfl rfl rfl (ep1330 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1332 := BSN.arctan_dyadic_bound_f 9000 195428 1 0 524288 260982 0 1 1 0 1 1 24127 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 195428) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 195428) 0 0 rfl) rfl rfl rfl

noncomputable def ep1333 := @Enclosure.Real.IsNear.subLit_ff_p qz333 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz879 qz618)) 884279719003555 562949953421312 1 2000000000000000 24127 524288 1 260982 450034951790739849216 858373550015907 562949953421312 1000000000130491 260982000000000000000 qz334 (ep1332 rfl) rfl rfl

noncomputable def ep1334 := @ep1299 35037615109455517 9007199254740992 500000001435401 260982000000000000000 Bool.false 858373550015907 562949953421312 1000000000130491 260982000000000000000 Bool.false ep1300 105096825100352471 9007199254740992 500000001435401 86994000000000000000 Bool.false ep1301 2609654334591209 562949953421312 1000000000130491 86994000000000000000 (ep1302 (BSN.log_sum_c_succ qz61 1 2 rfl) (ep1325 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1326 (@congrArg Complex Complex qz959 (Complex.mk qz595 qz372) Complex.log (BSN.w_shift_mk qz61 Bool.false 97714 1000 2 (@Eq.refl Real qz61) rfl)) (@Enclosure.Complex.IsNear.of_parts (Complex.log (Complex.mk qz595 qz372)) Bool.false 35037615109455517 9007199254740992 500000001435401 260982000000000000000 Bool.false 858373550015907 562949953421312 1000000000130491 260982000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re (Complex.log (Complex.mk qz595 qz372))) (@HMul.hMul Real Real Real qz0 qz323 (Real.log (Enclosure.sfrac Bool.false 38273103184 16000000))) Bool.false 35037615109455517 9007199254740992 500000001435401 260982000000000000000 (Enclosure.clog_re_eq 9000 195428 4000 38273103184 16000000 rfl rfl rfl) (ep1331 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im (Complex.log (Complex.mk qz595 qz372))) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz618 qz879)) Bool.false 858373550015907 562949953421312 1000000000130491 260982000000000000000 (Enclosure.clog_im_eq 9000 195428 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz618 qz879)) (@HSub.hSub Real Real Real qz326 qz333 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz879 qz618))) Bool.false 858373550015907 562949953421312 1000000000130491 260982000000000000000 (BSN.arctan_recip 195428 9000 rfl rfl) ep1333)))) rfl rfl

noncomputable def ep1335 := @Enclosure.Complex.IsNear.of_eq (Complex.log qz958) (Complex.log (Complex.mk qz596 qz372)) Bool.false 35047957390704285 9007199254740992 500000001435401 260982000000000000000 Bool.false 846887733724579 562949953421312 1000000000130491 260982000000000000000

noncomputable def ep1336 := nat_lit 383955233090357673341689419597230003848151040

noncomputable def ep1337 := nat_lit 794288987463489045809719743266469551013888

noncomputable def ep1338 := nat_lit 2935841333193380286658209538983041630208

noncomputable def ep1339 := BSN.log_dyadic_bound 5593103184 71129103184 3 2 ep1336 524288 260982 ep1337 ep1338 82623 76722206368 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 5593103184) (BSN.artanhQ 71129103184) 0 2 ep1337 ep1336 ep1338 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1340 := @Enclosure.Real.IsNear.mulLit_ff qz323 (Real.log (Enclosure.sfrac Bool.false 38361103184 16000000)) 1 2 0 1 35047957390704285 4503599627370496 500000001435401 130491000000000000000 35047957390704285 9007199254740992 500000001435401 260982000000000000000 qz324 (BSN.isNear_log_sfrac 38361103184 16000000 35047957390704285 4503599627370496 500000001435401 130491000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 38361103184) qz585)) Bool.false 147001787875660545392640 18889465931478580854784 1000000002870802 260982000000000000000 35047957390704285 4503599627370496 500000001435401 130491000000000000000 (BSN.log_rat_reduce_isNear 38361103184 16000000 11 76722206368 65536000000 82623 524288 24973259072661432 36028797018963968 260982 1000000000000000 rfl rfl rfl rfl (ep1339 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1341 := BSN.arctan_dyadic_bound_f 13000 195428 1 0 524288 260982 0 1 1 0 1 1 34824 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 13000) (BSN.arctanEvenQ 195428) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 13000) (BSN.arctanOddQ 195428) 0 0 rfl) rfl rfl rfl

noncomputable def ep1342 := @Enclosure.Real.IsNear.subLit_ff_p qz333 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz880 qz618)) 884279719003555 562949953421312 1 2000000000000000 34824 524288 1 260982 444013076138992074752 846887733724579 562949953421312 1000000000130491 260982000000000000000 qz334 (ep1341 rfl) rfl rfl

noncomputable def ep1343 := @ep1295 35047957390704285 9007199254740992 500000001435401 260982000000000000000 Bool.false 846887733724579 562949953421312 1000000000130491 260982000000000000000 Bool.false ep1296 35036195622764189 2251799813685248 500000001435401 65245500000000000000 Bool.false ep1297 864135517078947 140737488355328 1000000000130491 65245500000000000000 (ep1298 (BSN.log_sum_c_succ qz61 2 3 rfl) (ep1334 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1335 (@congrArg Complex Complex qz958 (Complex.mk qz596 qz372) Complex.log (BSN.w_shift_mk qz61 Bool.false 97714 1000 3 (@Eq.refl Real qz61) rfl)) (@Enclosure.Complex.IsNear.of_parts (Complex.log (Complex.mk qz596 qz372)) Bool.false 35047957390704285 9007199254740992 500000001435401 260982000000000000000 Bool.false 846887733724579 562949953421312 1000000000130491 260982000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re (Complex.log (Complex.mk qz596 qz372))) (@HMul.hMul Real Real Real qz0 qz323 (Real.log (Enclosure.sfrac Bool.false 38361103184 16000000))) Bool.false 35047957390704285 9007199254740992 500000001435401 260982000000000000000 (Enclosure.clog_re_eq 13000 195428 4000 38361103184 16000000 rfl rfl rfl) (ep1340 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im (Complex.log (Complex.mk qz596 qz372))) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz618 qz880)) Bool.false 846887733724579 562949953421312 1000000000130491 260982000000000000000 (Enclosure.clog_im_eq 13000 195428 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz618 qz880)) (@HSub.hSub Real Real Real qz326 qz333 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz880 qz618))) Bool.false 846887733724579 562949953421312 1000000000130491 260982000000000000000 (BSN.arctan_recip 195428 13000 rfl rfl) ep1342)))) rfl rfl

noncomputable def ep1344 := @ep1184 ep1169 Bool.false 35036195622764189 2251799813685248 500000001435401 65245500000000000000 Bool.false 864135517078947 140737488355328 1000000000130491 65245500000000000000 Bool.true ep1185 ep1175 ep1176 ep1177 ep1178 Bool.false ep1186 ep1171 ep1167 ep1172 ep1169 (@ep1187 ep1176 ep1181 ep1178 Bool.false ep1182 ep1167 ep1183 ep1169 (BSN.logGammaStirling_unfold 2 qz55) (ep1292 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep1293 1000000000130491 65245500000000000000 (BSN.log_sum_c_eq qz61 4) (ep1294 (BSN.log_sum_c_succ qz61 3 4 rfl) (ep1343 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable def ep1345 := @Enclosure.Real.IsNear.mulLit_ff (@HDiv.hDiv Real Real Real qz1 qz61 (2 : Real)) (Real.log Real.pi) 97714 2000 0 1 75021 65536 1 131072 3665300997 65536000 48857 131072000 (@Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real qz1 qz61 (2 : Real)) (Enclosure.sfrac Bool.false 97714 2000) Bool.false 97714 2000 0 1 (BSN.t_half_eq qz61 Bool.false 97714 1000 (@Eq.refl Real qz61)) (Enclosure.Real.IsNear.const Bool.false 97714 2000)) EMRow28.d6 rfl

noncomputable def ep1346 := @ep1173 48857 131072000 ep1174 ep1166 ep1167 ep1168 ep1169 (@ep1179 ep1172 ep1169 (ep1344 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep1345 rfl rfl

noncomputable def ep1347 := nat_lit 32534436223465807079657414527461295979511174022483984168730561342682487665985

noncomputable def ep1348 := nat_lit 65249963939246609322626020164232283998516426207648152007231540682649318721

noncomputable def ep1349 := nat_lit 85103594929365952603056595920227970534150714892645671052949285784015559275841

noncomputable def ep1350 := BSN.sin_dyadic_bound_f 1685863991 1073741824 3 2 524288 261237 ep1347 ep109 ep1348 ep1349 ep111 ep1348 524287 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1685863991) qz275 0 2 ep1347 ep109 ep1348 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1685863991) qz276 0 2 ep1349 ep111 ep1348 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1351 := @ep1165 524288 Bool.true 524287 524288 1 130491 (@ep1170 11117827 131072 261 524288 ep1346 rfl) (Enclosure.sfrac_false_div 11117827 131072) (BSN.cos_reduce1 qz957 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 29658032984782079524864) qz559) 226375608064910080 72057594037927936 Bool.false 524287 524288 13 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q1 11117827 131072 226375608064910080 72057594037927936 13 29658032984782079524864 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 524287 524288 29658032984782079524864 18889465931478580854784 1685863991 1073741824 261237 260982 (ep1350 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1352 := nat_lit 2656031315054254766389396118212649

noncomputable def ep1353 := nat_lit 461357238116344135680000000000000000

noncomputable def ep1354 := nat_lit 43466494707685184259332737418509566227

noncomputable def ep1355 := nat_lit 7525370919879982826127360000000000000000

noncomputable abbrev qz963 := (@Nat.cast Complex Complex.instNatCast 25)

noncomputable abbrev qz78 := (@HPow.hPow Complex Complex Complex qz816 qz963 (@Neg.neg Complex Complex.instNeg qz373))

noncomputable abbrev qz79 := (@HAdd.hAdd Complex Complex Complex qz263 (@HDiv.hDiv Complex Complex Complex qz331 qz963 (@HSub.hSub Complex Complex Complex qz580 qz373 (1 : Complex))) qz330)

noncomputable abbrev qz80 := qz963

noncomputable def ep1356 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz64 2 25) (@HAdd.hAdd Complex Complex Complex qz15 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 25, @HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast n) qz65) (@HMul.hMul Complex Complex Complex qz3 qz78 (@HAdd.hAdd Complex Complex Complex qz15 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz80 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1))))))) Bool.false ep1160 ep1161 ep1162

noncomputable def ep1357 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 25, @HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast n) qz65) (@HMul.hMul Complex Complex Complex qz3 qz78 (@HAdd.hAdd Complex Complex Complex qz15 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz80 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))))) Bool.false 753758885689 274877906944 203507419277183 35869092955029504

noncomputable def ep1358 := nat_lit 19388074317065681281119453407816753

noncomputable def ep1359 := nat_lit 12100123967134863948048081629532718601

noncomputable def ep1360 := nat_lit 3671405388724529523889396118212649

noncomputable def ep1361 := nat_lit 753377581276109920812932731009566227

noncomputable def ep1362 := nat_lit 144430200370801813909770166331389997113338232832

noncomputable def ep1363 := nat_lit 22815135270619793374589152657825354857054208

noncomputable def ep1364 := @ep1357 Bool.false 18905083 8589934592 50897184501527 8967273238757376 Bool.false ep1358 ep1161 ep1359 ep1163 Bool.true ep1360 ep1353 ep1361 ep1355 Bool.false ep1362 ep1160 ep1161 ep1162 ep1163 Bool.true ep1363 ep1352 ep1353

noncomputable def ep1365 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 25, @HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast n) qz65) (BSN.headSumC qz64 25) Bool.false 753758885689 274877906944 203507419277183 35869092955029504 Bool.false 18905083 8589934592 50897184501527

noncomputable def ep1366 := @Enclosure.Complex.IsNear.mul qz78 (@HAdd.hAdd Complex Complex Complex qz15 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz80 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1))))) Bool.false ep1358 ep1161 ep1359 ep1163 Bool.true

noncomputable def ep1367 := nat_lit 2409788521907441519715451592521

noncomputable def ep1368 := nat_lit 25630957673130229760000000000000

noncomputable def ep1369 := nat_lit 2067091872482192305631026879844663

noncomputable def ep1370 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re qz78) (Complex.re (@HAdd.hAdd Complex Complex Complex qz15 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz80 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 (Complex.im qz78) (Complex.im (@HAdd.hAdd Complex Complex Complex qz15 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz80 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1))))))) ep1367 ep1368 ep1369

noncomputable def ep1371 := nat_lit 26756874381795494492897280000000000000

noncomputable def ep1372 := nat_lit 2037596959332102339168201941665553

noncomputable def ep1373 := nat_lit 2798210540964998572708460670231735101

noncomputable def ep1374 := nat_lit 496934912184213762742454751930123482431926926867169280000000000000

noncomputable def ep1375 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz78) (Complex.re (@HAdd.hAdd Complex Complex Complex qz15 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz80 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))))) 3203695921 17179869184 2748097494863 17934546477514752 752190152040163464601

noncomputable abbrev qz403 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 25 1)))

noncomputable abbrev qz622 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 25)))

noncomputable abbrev qz964 := (@Neg.neg Real Real.instNeg (Real.sin qz403))

noncomputable def ep1376 := @Enclosure.Complex.IsNear.of_eq qz78 (Complex.mk (@HMul.hMul Real Real Real qz0 qz622 (Real.cos qz403)) (@HMul.hMul Real Real Real qz0 qz622 qz964)) Bool.false 3203695921 17179869184 2748097494863 17934546477514752 Bool.true 19868828645 274877906944 5457130812493 35869092955029504 (BSN.cpow_neg_s_mk qz61 97714 1000 25 (@Eq.refl Real qz61) rfl)

noncomputable abbrev qz623 := (Real.sqrt (@Nat.cast Real Real.instNatCast 25))

noncomputable abbrev qz624 := (@Nat.cast Real Real.instNatCast 25)

noncomputable def ep1377 := @Enclosure.Real.IsNear.inv_image qz623 2621441 524288 1 524288 52428 52429 262144 (@Enclosure.Real.IsNear.of_eq qz623 (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz624 qz268)) Bool.false 2621441 524288 1 524288 (BSN.sqrt_natCast_div_one 25) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz624 qz268)) Bool.false 2621441 524288 1 524288 2621441 524288 1 524288 (BSN.sqrt_enclosure 25 1 1310720 1310721 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep1378 := BSN.log_dyadic_bound 9 41 5 4 7545754341519345 262144 130491 124828057765224 4519905705 116991 50 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 9) (BSN.artanhQ 41) 0 4 124828057765224 7545754341519345 4519905705 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz404 := (Real.log (Enclosure.sfrac Bool.false 25 1))

noncomputable def ep1379 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz404 97714 1000 0 1 3624129903009015 1125899906842624 250000000130491 32622750000000000000 35412822934262289171 112589990684262400 12214250006375398787 16311375000000000000000 qz375 (BSN.isNear_log_sfrac 25 1 3624129903009015 1125899906842624 250000000130491 32622750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 qz624 qz268)) Bool.false 30401405097420647301120 9444732965739290427392 1000000000521964 130491000000000000000 3624129903009015 1125899906842624 250000000130491 32622750000000000000 (BSN.log_rat_reduce_isNear 25 1 4 50 32 116991 262144 24973259072661432 36028797018963968 130491 1000000000000000 rfl rfl rfl rfl (ep1378 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1380 := nat_lit 24854145472758060264705105532701456

noncomputable def ep1381 := BSN.cos_dyadic_bound_f 397054122 1073741824 2 1 524288 261237 ep1380 ep88 ep1380 ep1380 ep89 ep1380 488848 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 397054122) qz269 0 1 ep1380 ep88 ep1380 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 397054122) qz270 0 1 ep1380 ep89 ep1380 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz965 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 164903807) qz280)

noncomputable def ep1382 := @Enclosure.Real.IsNear.cos_image qz403 qz965 Bool.false 164903807 524288 393 524288 Bool.false 488848 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz403 Bool.false 35412822934262289171 112589990684262400 12214250006375398787 16311375000000000000000 164903807 524288 393 524288 (ep1379 rfl) rfl) (Enclosure.sfrac_false_div 164903807 524288) (BSN.cos_reduce0 qz965 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 27940200002522871496704) qz282) 226375608064910080 72057594037927936 Bool.false 488848 524288 50 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q0 164903807 524288 226375608064910080 72057594037927936 50 27940200002522871496704 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 488848 524288 27940200002522871496704 75557863725914323419136 397054122 1073741824 261237 260982 (ep1381 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1383 := BSN.sin_dyadic_bound_f 397054122 1073741824 2 1 524288 261237 ep1380 ep92 ep1380 ep1380 ep93 ep1380 189485 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 397054122) qz275 0 1 ep1380 ep92 ep1380 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 397054122) qz276 0 1 ep1380 ep93 ep1380 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1384 := @Enclosure.Real.IsNear.sin_image qz403 qz965 Bool.false 164903807 524288 393 524288 Bool.false 189485 524288 1 130491 (@Enclosure.Real.IsNear.recentre' qz403 Bool.false 35412822934262289171 112589990684262400 12214250006375398787 16311375000000000000000 164903807 524288 393 524288 (ep1379 rfl) rfl) (Enclosure.sfrac_false_div 164903807 524288) (BSN.sin_reduce0 qz965 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 27940200002522871496704) qz282) 226375608064910080 72057594037927936 Bool.false 189485 524288 50 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q0 164903807 524288 226375608064910080 72057594037927936 50 27940200002522871496704 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 189485 524288 27940200002522871496704 75557863725914323419136 397054122 1073741824 261237 260982 (ep1383 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1385 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz622 (Real.cos qz403)) (@HMul.hMul Real Real Real qz0 qz622 qz964) Bool.false 3203695921 17179869184 2748097494863 17934546477514752 Bool.true 19868828645 274877906944 5457130812493 35869092955029504 (@Enclosure.Real.IsNear.mulLit_ff qz622 (Real.cos qz403) 104857 524288 1 524288 30553 32768 51807251 68414865408 3203695921 17179869184 2748097494863 17934546477514752 (@Enclosure.Real.IsNear.recentre' qz622 Bool.false 104857 524288 1 524288 104857 524288 1 524288 (ep1377 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' (Real.cos qz403) Bool.false 488848 524288 51807251 68414865408 30553 32768 51807251 68414865408 (ep1382 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz622 qz964 104857 524288 1 524288 189485 524288 51807251 68414865408 19868828645 274877906944 5457130812493 35869092955029504 (@Enclosure.Real.IsNear.recentre' qz622 Bool.false 104857 524288 1 524288 104857 524288 1 524288 (ep1377 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg (Real.sin qz403) Bool.false 189485 524288 51807251 68414865408 (@Enclosure.Real.IsNear.recentre' (Real.sin qz403) Bool.false 189485 524288 51807251 68414865408 189485 524288 51807251 68414865408 (ep1384 rfl rfl) rfl)) rfl)

noncomputable def ep1386 := @ep1375 1491918093125000000000 0 1 ep1367 ep1368 ep1369 ep1371 (@Enclosure.Complex.IsNear.re_isNear qz78 Bool.false 3203695921 17179869184 2748097494863 17934546477514752 Bool.true 19868828645 274877906944 5457130812493 35869092955029504 (ep1376 ep1385))

noncomputable def ep1387 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz15 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz80 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1))))) Bool.false 752190152040163464601 1491918093125000000000 0 1 Bool.false

noncomputable def ep1388 := nat_lit 3356815709531250000000000

noncomputable def ep1389 := @Enclosure.Complex.IsNear.addLitP qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz80 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) Bool.false 2380818949 4774137898 0 1 Bool.true 610712500

noncomputable def ep1390 := @ep1389 2387068949 0 1 Bool.false 3428568949 625000000000 0 1 Bool.false 574586117141293 1406250000000000 0 1 Bool.false 1504380304080326929202 752190152040163464601 1491918093125000000000 0 1 Bool.false 512762225629457166011057 512762225629457166011057 ep1388 0 1

noncomputable abbrev qz81 := (@HDiv.hDiv Complex Complex Complex qz331 qz963 (@HSub.hSub Complex Complex Complex qz580 qz373 (1 : Complex)))

noncomputable def ep1391 := @Enclosure.Complex.IsNear.addLitP qz81 qz26 Bool.true 50000000 38193103184 0 1 Bool.true 9771400000 38193103184 0 1

noncomputable def ep1392 := @Enclosure.Complex.IsNear.of_eq qz81 (Complex.mk (Enclosure.sfrac Bool.true 50000000 38193103184) (Enclosure.sfrac Bool.true 9771400000 38193103184)) Bool.true 50000000 38193103184 0 1 Bool.true 9771400000 38193103184 0 1

noncomputable def ep1393 := @ep1391 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 38093103184 2380818949 4774137898 0 1 Bool.true 9771400000 610712500 2387068949 0 1 (ep1392 (BSN.N_div_s_sub_one_mk qz61 97714 1000 25 (@Eq.refl Real qz61) rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 50000000 38193103184) (Enclosure.sfrac Bool.true 9771400000 38193103184) Bool.true 50000000 38193103184 0 1 Bool.true 9771400000 38193103184 0 1 (Enclosure.Real.IsNear.const Bool.true 50000000 38193103184) (Enclosure.Real.IsNear.const Bool.true 9771400000 38193103184))) qz336 rfl

noncomputable abbrev qz405 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz80 3))

noncomputable def ep1394 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz80 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz15 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz80 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) qz405)) Bool.false 3428568949 625000000000 0 1

noncomputable def ep1395 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz80 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) qz405) Bool.false 1 600 0 1 Bool.false

noncomputable def ep1396 := @ep1395 48857 150000 0 1 Bool.false 7160706847 1875000000000 0 1 Bool.false 116551742141293 1406250000000000 0 1 Bool.false 6171424108200 3428568949 625000000000 0 1 Bool.false 86187917571193950000 574586117141293 1406250000000000 0

noncomputable abbrev qz406 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz80 1))

noncomputable def ep1397 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz80 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz15 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz80 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) qz406)) Bool.false 1 600 0 1

noncomputable def ep1398 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz80 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) qz406) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1399 := @ep1398 0 1 0 1 Bool.false 1 600 0 1 Bool.false 48857 150000 0 1 Bool.false 1 1 600 0 1 Bool.false 48857 48857 150000 0

noncomputable def ep1400 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz80 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (Complex.mk qz265 qz265) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1401 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) qz406 Bool.false 1 600 0 1 Bool.false 48857 150000 0 1

noncomputable def ep1402 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz406)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz406)) 1 600 0 1 0 1 0

noncomputable def ep1403 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz406) 1 24 0 1 1 25 0 1 1

noncomputable def ep1404 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep1405 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep1406 := @ep1405 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep726) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 97714 1000 0 1 ep1115)

noncomputable def ep1407 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 97714 1000 0 1 0 1 0

noncomputable def ep1408 := @ep1407 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep726) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 97714 1000 0 1 ep1115)

noncomputable def ep1409 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)))) 48857 6000 0 1 0 1 0 1 48857

noncomputable def ep1410 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 97714 1000 0 1 48857 6000 0

noncomputable def ep1411 := @ep1410 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep726) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 97714 1000 0 1 ep1115)

noncomputable def ep1412 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep1413 := @ep1412 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep726) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 97714 1000 0 1 ep1115)

noncomputable def ep1414 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 48857 6000 0 1 (@ep1404 1 24 0 1 (ep1406 rfl) (ep1408 rfl) rfl rfl) (@ep1409 48857 6000 0 1 (ep1411 rfl) (ep1413 rfl) rfl rfl)

noncomputable def ep1415 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 48857 6000 0 1 ep1414

noncomputable abbrev qz407 := (@Enclosure.Complex.IsNear.of_eq (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz80 1)) (Complex.mk (Enclosure.sfrac Bool.false 1 25) qz553) Bool.false 1 25 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 25 1 25 EMRow28.d19 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 25) qz553 Bool.false 1 25 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 25) qz823))

noncomputable def ep1416 := @ep1403 600 0 1 ep1415 (@Enclosure.Complex.IsNear.re_isNear qz406 Bool.false 1 25 0 1 Bool.false 0 1 0 1 qz407)

noncomputable def ep1417 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz406) 48857 6000 0 1 0 1 0 1 0

noncomputable def ep1418 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 48857 6000 0 1 ep1414

noncomputable def ep1419 := @ep1417 1 0 1 ep1418 (@Enclosure.Complex.IsNear.im_isNear qz406 Bool.false 1 25 0 1 Bool.false 0 1 0 1 qz407)

noncomputable def ep1420 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz406)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz406)) 0 1 0 1 48857 150000 0

noncomputable def ep1421 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz406) 1 24 0 1 0 1 0 1 0

noncomputable def ep1422 := @ep1421 1 0 1 ep1415 (@Enclosure.Complex.IsNear.im_isNear qz406 Bool.false 1 25 0 1 Bool.false 0 1 0 1 qz407)

noncomputable def ep1423 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz406) 48857 6000 0 1 1 25 0 1 48857

noncomputable def ep1424 := @ep1423 150000 0 1 ep1418 (@Enclosure.Complex.IsNear.re_isNear qz406 Bool.false 1 25 0 1 Bool.false 0 1 0 1 qz407)

noncomputable def ep1425 := @ep1399 1 (@ep1400 0 1 0 1 (BSN.bern_sum_base qz64 25) qz339) (ep1401 (@ep1402 1 1 1 600 0 1 (ep1416 rfl) (ep1419 rfl) rfl rfl) (@ep1420 1 48857 48857 150000 0 1 (ep1422 rfl) (ep1424 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep1426 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) qz405 Bool.false 7160706847 1875000000000 0 1 Bool.false 116551742141293 1406250000000000 0 1

noncomputable def ep1427 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.re qz405)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.im qz405)) 7160706847 1875000000000 0 1 0 1 0

noncomputable def ep1428 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.re qz405) 7160706847 120000000 0 1 1 15625 0 1 7160706847

noncomputable def ep1429 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)))) 7160706847 120000000 0 1 0 1 0 1 7160706847

noncomputable def ep1430 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 21482120541 500000 0 1 7160706847 120000000 0

noncomputable def ep1431 := @ep1430 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep752) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 21482120541 500000 0 1 Bool.true 116551742141293 125000000 0 1 EMRow28.d20)

noncomputable def ep1432 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 116551742141293 125000000 0 1 0 1 0

noncomputable def ep1433 := @ep1432 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep752) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 21482120541 500000 0 1 Bool.true 116551742141293 125000000 0 1 EMRow28.d20)

noncomputable def ep1434 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)))) 116551742141293 90000000000 0 1 0 1 0 1 116551742141293

noncomputable def ep1435 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 116551742141293 125000000 0 1 116551742141293 90000000000 0

noncomputable def ep1436 := @ep1435 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep752) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 21482120541 500000 0 1 Bool.true 116551742141293 125000000 0 1 EMRow28.d20)

noncomputable def ep1437 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 21482120541 500000 0 1 0 1 0

noncomputable def ep1438 := @ep1437 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep752) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 21482120541 500000 0 1 Bool.true 116551742141293 125000000 0 1 EMRow28.d20)

noncomputable def ep1439 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 7160706847 120000000 0 1 Bool.false 116551742141293 90000000000 0 1 (@ep1429 7160706847 120000000 0 1 (ep1431 rfl) (ep1433 rfl) rfl rfl) (@ep1434 116551742141293 90000000000 0 1 (ep1436 rfl) (ep1438 rfl) rfl rfl)

noncomputable def ep1440 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 7160706847 120000000 0 1 Bool.false 116551742141293 90000000000 0 1 ep1439

noncomputable abbrev qz408 := (@Enclosure.Complex.IsNear.of_eq (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz80 3)) (Complex.mk (Enclosure.sfrac Bool.false 1 15625) qz553) Bool.false 1 15625 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 25 3 15625 EMRow28.d21 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 15625) qz553 Bool.false 1 15625 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 15625) qz823))

noncomputable def ep1441 := @ep1428 1875000000000 0 1 ep1440 (@Enclosure.Complex.IsNear.re_isNear qz405 Bool.false 1 15625 0 1 Bool.false 0 1 0 1 qz408)

noncomputable def ep1442 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.im qz405) 116551742141293 90000000000 0 1 0 1 0 1 0

noncomputable def ep1443 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 7160706847 120000000 0 1 Bool.false 116551742141293 90000000000 0 1 ep1439

noncomputable def ep1444 := @ep1442 1 0 1 ep1443 (@Enclosure.Complex.IsNear.im_isNear qz405 Bool.false 1 15625 0 1 Bool.false 0 1 0 1 qz408)

noncomputable def ep1445 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.im qz405)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.re qz405)) 0 1 0 1 116551742141293 1406250000000000 0

noncomputable def ep1446 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.im qz405) 7160706847 120000000 0 1 0 1 0 1 0

noncomputable def ep1447 := @ep1446 1 0 1 ep1440 (@Enclosure.Complex.IsNear.im_isNear qz405 Bool.false 1 15625 0 1 Bool.false 0 1 0 1 qz408)

noncomputable def ep1448 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.re qz405) 116551742141293 90000000000 0 1 1 15625 0 1 116551742141293

noncomputable def ep1449 := @ep1448 1406250000000000 0 1 ep1443 (@Enclosure.Complex.IsNear.re_isNear qz405 Bool.false 1 15625 0 1 Bool.false 0 1 0 1 qz408)

noncomputable def ep1450 := @ep1396 1 (@ep1397 Bool.false 48857 150000 0 1 (BSN.bern_sum_succ qz64 25 0 1 1 rfl rfl) (ep1425 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1426 (@ep1427 1 7160706847 7160706847 1875000000000 0 1 (ep1441 rfl) (ep1444 rfl) rfl rfl) (@ep1445 1 116551742141293 116551742141293 1406250000000000 0 1 (ep1447 rfl) (ep1449 rfl) rfl rfl)) rfl rfl rfl rfl

noncomputable def ep1451 := ep1390 (ep1393 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep1394 Bool.false 574586117141293 1406250000000000 0 1 (BSN.bern_sum_succ qz64 25 1 2 3 rfl rfl) (ep1450 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep1452 := @Enclosure.Real.IsNear.mulLit_tf (Complex.im qz78) (Complex.im (@HAdd.hAdd Complex Complex Complex qz15 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz80 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))))) 19868828645 274877906944 5457130812493 35869092955029504 512762225629457166011057

noncomputable def ep1453 := @ep1452 ep1388 0 1 ep1372 ep1161 ep1373 ep1163 (@Enclosure.Complex.IsNear.im_isNear qz78 Bool.false 3203695921 17179869184 2748097494863 17934546477514752 Bool.true 19868828645 274877906944 5457130812493 35869092955029504 (ep1376 ep1385))

noncomputable def ep1454 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz15 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz80 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1))))) Bool.false 752190152040163464601 1491918093125000000000 0 1 Bool.false

noncomputable def ep1455 := nat_lit 1642734250691973580193843151798497

noncomputable def ep1456 := nat_lit 57669654764543016960000000000000000

noncomputable def ep1457 := nat_lit 1409120587712687611213549252258700191

noncomputable def ep1458 := @Enclosure.Real.IsNear.addLit_ft_n (@HMul.hMul Real Real Real qz0 (Complex.re qz78) (Complex.im (@HAdd.hAdd Complex Complex Complex qz15 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz80 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 (Complex.im qz78) (Complex.re (@HAdd.hAdd Complex Complex Complex qz15 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz80 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1))))))) ep1455 ep1456 ep1457

noncomputable def ep1459 := nat_lit 60202967359039862609018880000000000000000

noncomputable def ep1460 := nat_lit 2989027447868501007189358459129

noncomputable def ep1461 := nat_lit 82019064554016735232000000000000

noncomputable def ep1462 := nat_lit 4104800055552170449146588974060293

noncomputable def ep1463 := nat_lit 53513748763590988985794560000000000000

noncomputable def ep1464 := nat_lit 37640654447720261570513702570179176502090216763293696000000000000

noncomputable def ep1465 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz78) (Complex.im (@HAdd.hAdd Complex Complex Complex qz15 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz80 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))))) 3203695921 17179869184 2748097494863 17934546477514752 512762225629457166011057

noncomputable def ep1466 := @ep1465 ep1388 0 1 ep1455 ep1456 ep1457 ep1459 (@Enclosure.Complex.IsNear.re_isNear qz78 Bool.false 3203695921 17179869184 2748097494863 17934546477514752 Bool.true 19868828645 274877906944 5457130812493 35869092955029504 (ep1376 ep1385))

noncomputable def ep1467 := @Enclosure.Real.IsNear.mulLit_tf (Complex.im qz78) (Complex.re (@HAdd.hAdd Complex Complex Complex qz15 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz80 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))))) 19868828645 274877906944 5457130812493 35869092955029504 752190152040163464601

noncomputable def ep1468 := @ep1467 1491918093125000000000 0 1 ep1460 ep1461 ep1462 ep1463 (@Enclosure.Complex.IsNear.im_isNear qz78 Bool.false 3203695921 17179869184 2748097494863 17934546477514752 Bool.true 19868828645 274877906944 5457130812493 35869092955029504 (ep1376 ep1385))

noncomputable abbrev qz966 := (ep1451 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep1469 := @ep1366 ep1360 ep1353 ep1361 ep1355 (@ep1370 ep1371 ep1372 ep1161 ep1373 ep1163 ep1374 ep1358 ep1161 ep1359 ep1163 (ep1386 (@ep1387 512762225629457166011057 ep1388 0 1 qz966) rfl) (ep1453 (@ep1454 512762225629457166011057 ep1388 0 1 qz966) rfl) rfl rfl) (@ep1458 ep1459 ep1460 ep1461 ep1462 ep1463 ep1464 ep1360 ep1353 ep1361 ep1355 (ep1466 (@ep1454 512762225629457166011057 ep1388 0 1 qz966) rfl) (ep1468 (@ep1387 512762225629457166011057 ep1388 0 1 qz966) rfl) rfl rfl)

noncomputable def ep1470 := @ep1364 ep1354 ep1355 (@ep1365 8967273238757376 (BSN.head_sum_c_eq qz64 25) EMRow28.d18) ep1469 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def ep1471 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz64 2 25) Bool.false ep1160 ep1161 ep1162 ep1163 Bool.true ep1352 ep1353 ep1354 ep1355 (@ep1356 ep1163 Bool.true ep1352 ep1353 ep1354 ep1355 (BSN.zetaApproximant_eq_folded' qz64 2 25 rfl) (ep1470 rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep1472 := @Enclosure.Real.IsNear.mulLit_ft (Real.sin (@HSub.hSub Real Real Real qz326 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz399)) (Complex.im (zetaApproximant qz64 2 25)) 373 524288 34582439

noncomputable def ep1473 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz326 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz399)) Bool.false 373 524288 34582439

noncomputable def ep1474 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz326 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz399) qz957 Bool.false 11117827 131072 261

noncomputable def ep1475 := nat_lit 18103686774787335759508619635329267670394437313027834827964636986238115067201

noncomputable def ep1476 := nat_lit 54180560396483514059880606865659338443186279086668208179879447877349046564161

noncomputable def ep1477 := BSN.cos_dyadic_bound_f 1685863991 1073741824 3 2 524288 261237 ep1475 ep102 ep1348 ep1476 ep105 ep1348 373 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1685863991) qz269 0 2 ep1475 ep102 ep1348 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1685863991) qz270 0 2 ep1476 ep105 ep1348 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1478 := @ep1474 524288 Bool.false 373 524288 1 130491 (@ep1170 11117827 131072 261 524288 ep1346 rfl) (Enclosure.sfrac_false_div 11117827 131072) (BSN.sin_reduce1 qz957 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 29658032984782079524864) qz559) 226375608064910080 72057594037927936 Bool.false 373 524288 13 1000000000000000 260982 130491 (BSN.sin_reduce_arg_pos_rat_q1 11117827 131072 226375608064910080 72057594037927936 13 29658032984782079524864 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 373 524288 29658032984782079524864 18889465931478580854784 1685863991 1073741824 261237 260982 (ep1477 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1479 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz64 2 25) Bool.false ep1160 ep1161 ep1162 ep1163 Bool.true ep1352 ep1353 ep1354 ep1355 (@ep1356 ep1163 Bool.true ep1352 ep1353 ep1354 ep1355 (BSN.zetaApproximant_eq_folded' qz64 2 25 rfl) (ep1470 rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow28.d22 : Enclosure.Real.IsNear (hardyZApproximantEM 2 25 qz61) Bool.true ep1144 ep1145 ep1146 ep1147 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 2 25 qz61) ep1148 Bool.true ep1144 ep1145 ep1146 ep1147 (@Eq.refl Real ep1148) (@ep1149 Bool.true ep1144 ep1145 ep1146 ep1147 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz326 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz399) (zetaApproximant qz64 2 25)) (@ep1151 ep1152 ep1153 ep1147 ep1154 ep1155 ep1156 ep1157 ep1158 ep1144 ep1145 ep1146 ep1147 (@ep1159 68414865408 ep1160 ep1161 ep1162 ep1163 ep1150 ep1152 ep1153 ep1147 (@ep1164 68414865408 524287 524288 34582439 68414865408 (ep1351 rfl rfl) rfl) ep1471 rfl) (@ep1472 68414865408 ep1352 ep1353 ep1354 ep1355 ep1154 ep1155 ep1156 ep1157 (@ep1473 68414865408 373 524288 34582439 68414865408 (ep1478 rfl rfl) rfl) ep1479 rfl) rfl rfl))

theorem EMRow28.d23 : @Eq Nat (Nat.mul (BSN.factNat (Nat.succ (Nat.mul 2 2))) (Nat.pow 4 (Nat.mul 2 2))) 30720 := @Eq.refl Nat 30720

theorem EMRow28.d24 : @Eq Nat (Nat.mul (Nat.mul 2 2) (Nat.pow (Nat.succ (Nat.mul 4 4)) (Nat.mul 2 2))) 334084 := @Eq.refl Nat 334084

theorem EMRow28.d178 : @Eq Nat (TangentNumbers.tangentNumber 3) 16 := Height20.tangent_three

noncomputable abbrev qz233 := (@HMul.hMul Nat Nat Nat qz869 2 3)

theorem EMRow28.d179 : @Eq Real (@Rat.cast Real Real.instRatCast (bernoulli qz233)) (Enclosure.sfrac Bool.false 1 42) := BSN.bern_real_tangent_pos 2 16 1 42 EMRow28.d178 rfl rfl rfl

theorem EMRow28.d180 : @Eq Nat (BSN.factNat (Nat.mul 2 3)) 720 := @Eq.refl Nat 720

theorem EMRow28.d181 : @Eq Nat (Nat.pow 24 (Nat.succ (Nat.mul 2 5))) 1521681143169024 := @Eq.refl Nat 1521681143169024

noncomputable def ep1613 := nat_lit 1181671153346359170692730265957638242378174781758650

noncomputable def ep1614 := nat_lit 5986310706507378352962293074805895248510699696029696

noncomputable def ep1615 := nat_lit 2000000000000000000000000000000000000000000000000000

noncomputable def ep1616 := nat_lit 1499028120395240233173640088155429295548437777754679499662777369540625

noncomputable def ep1617 := nat_lit 4680297997409431328241185462095581837349556053595733828842639923095703125

noncomputable def ep1618 := nat_lit 13442882392639581675476766202062253719655739830178303899086159055189875

noncomputable def ep1619 := nat_lit 19584239746202378791298717228947477708711488730841665528714656829833984375

noncomputable def ep1620 := nat_lit 2442358029135994033939875

noncomputable def ep1621 := nat_lit 37260822860694382775919147000

noncomputable def ep1622 := nat_lit 116336546489037573337554931640625

noncomputable def ep1623 := nat_lit 57493278893883548332405996866302358825

noncomputable def ep1624 := nat_lit 40230676762013536063022911548614501953125

noncomputable def ep1625 := nat_lit 236310350532676991248348623960

noncomputable def ep1626 := nat_lit 344268321641720831394195556640625

noncomputable def ep1627 := nat_lit 81801971833623620377505564448994707675

noncomputable def ep1628 := nat_lit 56886557708273976459167897701263427734375

noncomputable def ep1629 := BSN.arctan_dyadic_bound_f 1 5 18 17 ep1614 ep1615 ep1616 ep1617 200200021673987500790625 ep1618 ep1619 ep1620 ep1613 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 17 8 ep1621 ep1622 151412625 ep1623 ep1624 1322214852783825 ep1616 ep1617 200200021673987500790625 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 8 ep1621 ep1622 151412625 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 8 17 ep1623 ep1624 1322214852783825 rfl rfl rfl rfl)) (@BSN.binarySplit_rec (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 17 8 ep1625 ep1626 1267389585 ep1627 ep1628 1927077560082675 ep1618 ep1619 ep1620 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 8 ep1625 ep1626 1267389585 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 8 17 ep1627 ep1628 1927077560082675 rfl rfl rfl rfl)) rfl

theorem EMRow28.d182 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz268 qz561)) Bool.false ep1613 ep1614 1 ep1615 := ep1629 rfl rfl rfl

noncomputable def ep1630 := nat_lit 25047178968060507272880539293402373975644382030403

noncomputable def ep1631 := nat_lit 4733915408010924740926662591654183582145509

noncomputable def ep1632 := nat_lit 77229300481955664312677298336960122659119574530232845

noncomputable def ep1633 := nat_lit 24516194103503660983641551147684725335332607

noncomputable def ep1634 := nat_lit 186647183216068817672719845704257068688983305564016735

noncomputable def ep1635 := BSN.arctan_dyadic_bound_f 1 239 6 5 ep1614 ep1615 ep1631 ep1632 9945 ep1633 ep1634 65835 ep1630 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 239) 0 5 ep1631 ep1632 9945 rfl rfl rfl rfl) (@BSN.binarySplit_of_base5 (BSN.arctanOddP 1) (BSN.arctanOddQ 239) 0 5 ep1633 ep1634 65835 rfl rfl rfl rfl) rfl rfl rfl

theorem EMRow28.d183 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz268 (@Nat.cast Real Real.instNatCast 239))) Bool.false ep1630 ep1614 1 ep1615 := ep1635 rfl

noncomputable def ep1636 := nat_lit 18806549737669504701992162098148602382148218980016788

noncomputable def ep1637 := nat_lit 100000000000000000000000000000000000000000000000000

theorem EMRow28.d184 : Enclosure.Real.IsNear Real.pi Bool.false ep1636 ep1614 1 ep1637 := BSN.pi_combine ep1613 ep1630 ep1614 ep1615 ep1637 ep1636 rfl rfl rfl rfl EMRow28.d182 EMRow28.d183

noncomputable def ep1638 := nat_lit 3958592073026781228359749

noncomputable def ep1639 := nat_lit 33895191259166500131438592

noncomputable abbrev qz536 := (@HAdd.hAdd Complex Complex Complex qz548 (@HAdd.hAdd Complex Complex Complex qz548 qz549 (@HMul.hMul Complex Complex Complex qz543 Complex.I ↑qz814)) qz820)

noncomputable abbrev qz234 := (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Norm.norm Complex Complex.instNorm qz536) (@HAdd.hAdd Real Real Real qz590 (Complex.re qz262) qz561))

noncomputable abbrev qz235 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz869 2 3)))

noncomputable abbrev qz236 := (@HPow.hPow Complex Complex Complex qz816 qz881 (@HSub.hSub Complex Complex Complex qz580 (@Neg.neg Complex Complex.instNeg qz262) qz820))

noncomputable def ep1640 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 2 4) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz14 2 24))) (@HMul.hMul Real Real Real qz0 qz234 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236))) 1274704185 44839995441152 18652815 44839995441152 47384831431332610309 405828369621610135552 14315916607691

noncomputable def ep1641 := nat_lit 2125252936481858638493978709721088

noncomputable def ep1642 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 2 4) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz14 2 24)) 5055 85525504 15 85525504 252167 524288 2933 524288 1274704185 44839995441152

noncomputable abbrev qz537 := (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid)))

noncomputable abbrev qz538 := (@HMul.hMul Real Real Real qz0 (2 : Real) Real.pi)

noncomputable abbrev qz1099 := (@Inv.inv Real Real.instInv (@HPow.hPow Real Nat Real qz537 qz538 4))

noncomputable def ep1643 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 30720 334084) qz1099 30720 334084 0 1 337 524288 1 524288 5055 85525504 15 85525504

noncomputable def ep1644 := nat_lit 611446774371975769155682509262542103857872115376664175900625

noncomputable def ep1645 := nat_lit 392318858461667547739736838950479151006397215279002157056

noncomputable def ep1646 := nat_lit 19652562622312316682495810535216024035134795670488584765154486969712234385047

noncomputable def ep1647 := nat_lit 9903520314283042199192993792000000000000000000000000000000000000000000000000000000000000

noncomputable def ep1648 := nat_lit 691463075802508163054686763366652189853178875

noncomputable def ep1649 := nat_lit 2787593149816327892691964784081045188247552

noncomputable def ep1650 := nat_lit 2184744797947834540264818678394244808492865883128339

noncomputable def ep1651 := nat_lit 9223372036854775808000000000000000000000000000000000000000000000

noncomputable def ep1652 := @Enclosure.Real.IsNear.mulLit_ff (@HPow.hPow Real Nat Real qz537 qz538 3) qz538 ep1648 ep1649 ep1650 ep1651 884279719003555 140737488355328 1 500000000000000 ep1644 ep1645 ep1646 ep1647

noncomputable def ep1653 := nat_lit 781950621441006189802102638025

noncomputable def ep1654 := nat_lit 19807040628566084398385987584

noncomputable def ep1655 := nat_lit 26986075409044041160201671

noncomputable def ep1656 := nat_lit 1073741824000000000000000000000000000000

noncomputable def ep1657 := @Enclosure.Real.IsNear.mulLit_ff (@HPow.hPow Real Nat Real qz537 qz538 2) qz538 ep1653 ep1654 ep1655 ep1656 884279719003555 140737488355328 1 500000000000000 ep1648 ep1649 ep1650 ep1651

noncomputable def ep1658 := @Enclosure.Real.IsNear.mulLit_ff (@HPow.hPow Real Nat Real qz537 qz538 1) qz538 884279719003555 140737488355328 1 500000000000000 884279719003555 140737488355328 1 500000000000000 ep1653 ep1654 ep1655 ep1656

noncomputable abbrev qz539 := (@Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 (2 : Real) Real.pi) (@HMul.hMul Real Real Real qz0 qz810 Real.pi) Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq (@Enclosure.Real.IsNear.mulLit_ff qz810 Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) BSN.pi_near_15 rfl))

noncomputable def ep1659 := ep1658 (@Enclosure.Real.IsNear.of_eq (@HPow.hPow Real Nat Real qz537 qz538 1) qz538 Bool.false 884279719003555 140737488355328 1 500000000000000 (BSN.pow_one_r qz538) qz539) qz539 rfl

noncomputable def ep1660 := @Enclosure.Real.IsNear.of_eq (@HPow.hPow Real Nat Real qz537 qz538 3) (@HMul.hMul Real Real Real qz0 (@HPow.hPow Real Nat Real qz537 qz538 2) qz538) Bool.false ep1648 ep1649 ep1650 ep1651 (BSN.pow_succ_r qz538 2 3 rfl) (ep1657 (@Enclosure.Real.IsNear.of_eq (@HPow.hPow Real Nat Real qz537 qz538 2) (@HMul.hMul Real Real Real qz0 (@HPow.hPow Real Nat Real qz537 qz538 1) qz538) Bool.false ep1653 ep1654 ep1655 ep1656 (BSN.pow_succ_r qz538 1 2 rfl) ep1659) qz539 rfl)

noncomputable abbrev qz1100 := (@HPow.hPow Real Nat Real qz537 qz538 4)

noncomputable def ep1661 := @Enclosure.Real.IsNear.inv_image qz1100 ep1644 ep1645 ep1646 ep1647 168 169 262144 (@Enclosure.Real.IsNear.of_eq qz1100 (@HMul.hMul Real Real Real qz0 (@HPow.hPow Real Nat Real qz537 qz538 3) qz538) Bool.false ep1644 ep1645 ep1646 ep1647 (BSN.pow_succ_r qz538 3 4 rfl) (ep1652 ep1660 qz539 rfl))

noncomputable def ep1662 := ep1643 (Enclosure.Real.IsNear.const Bool.false 30720 334084) (@Enclosure.Real.IsNear.recentre' qz1099 Bool.false 337 524288 1 524288 337 524288 1 524288 (ep1661 rfl rfl rfl rfl rfl rfl) rfl)

noncomputable def ep1663 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz14 2 24)) (Real.sqrt (@HAdd.hAdd Real Real Real qz590 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz14 2 24)) (Complex.re (zetaApproximant qz14 2 24))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz14 2 24)) (Complex.im (zetaApproximant qz14 2 24))))) Bool.false 252167 524288 2933 524288

noncomputable def ep1664 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz590 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz14 2 24)) (Complex.re (zetaApproximant qz14 2 24))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz14 2 24)) (Complex.im (zetaApproximant qz14 2 24))))) Bool.false 252167 524288 2933 524288

noncomputable def ep1665 := nat_lit 27684266866480079534224816794259444735794170051250807593

noncomputable def ep1666 := nat_lit 119657462810068256726906813716944407809228800000000000000

noncomputable def ep1667 := nat_lit 323347681536730836164033392174221873251437148981512971552025641416762160841

noncomputable def ep1668 := nat_lit 60102308549849117456767728144932269917065087475992075441484595200000000000000

noncomputable def ep1669 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz590 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz14 2 24)) (Complex.re (zetaApproximant qz14 2 24))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz14 2 24)) (Complex.im (zetaApproximant qz14 2 24)))) ep1665 ep1666 ep1667 ep1668 124617 127550

noncomputable def ep1670 := nat_lit 806508124973461016068211580866447187360178923156787059146743681

noncomputable def ep1671 := nat_lit 3486061168562159616233430765716563148437231560032256000000000000

noncomputable def ep1672 := nat_lit 1503127888550137638673916045991190982529659052269264680213109195415381479

noncomputable def ep1673 := nat_lit 282834393175760552737730485387916564315600411651727413842280448000000000000

noncomputable def ep1674 := nat_lit 100558646896036425936154888222720906288108693631983061436481

noncomputable def ep1675 := nat_lit 9683503246005998933981752126990453190103421000089600000000000000

noncomputable def ep1676 := nat_lit 7866010439653175891652464802187578927769200748588454013479874781987193107

noncomputable def ep1677 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz14 2 24)) (Complex.re (zetaApproximant qz14 2 24))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz14 2 24)) (Complex.im (zetaApproximant qz14 2 24))) ep1670 ep1671 ep1672 ep1673 ep1674 ep1675 ep1676

noncomputable def ep1678 := nat_lit 120204617099698234913535456289864539834130174951984150882969190400000000000000

noncomputable def ep1679 := nat_lit 7810174599704829028276365053790452799758873662883597166479606170047493262441811105834539939398925318406419288948736000000000000

noncomputable def ep1680 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz14 2 24)) (Complex.re (zetaApproximant qz14 2 24)) ep362 ep363 ep364 ep365 ep362 ep363 ep364 ep365 ep1670

noncomputable def ep1681 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (zetaApproximant qz14 2 24)) (Complex.im (zetaApproximant qz14 2 24)) ep558 ep559 ep560 ep561 ep558 ep559 ep560 ep561 ep1674

noncomputable def ep1682 := @ep1640 405828369621610135552 ep1641 ep1638 ep1639 15295608221978490251 ep1639 (@ep1642 18652815 44839995441152 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 2 4) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 30720 334084) qz1099) Bool.false 5055 85525504 15 85525504 (BSN.theta_err_eq 2 4 30720 334084 EMRow28.d23 EMRow28.d24 rfl) (ep1662 rfl)) (ep1663 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz14 2 24)) (@ep1664 252167 524288 2933 524288 (@ep1669 262144 (@ep1677 ep1678 ep1679 ep1665 ep1666 ep1667 ep1668 (@ep1680 ep1671 ep1672 ep1673 ep792 ep792 rfl) (@ep1681 ep1675 ep1676 ep1678 ep798 ep798 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz237 := (@Norm.norm Complex Complex.instNorm qz536)

noncomputable abbrev qz1101 := (Enclosure.sfrac Bool.false 2 11)

noncomputable def ep1683 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz234 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz237 qz1101) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236))) Bool.false 47384831431332610309 405828369621610135552 14315916607691 405828369621610135552 (BSN.zrb_shape_eq qz237 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236)) qz11 5)

noncomputable def ep1684 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz237 qz1101) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236)) 50107979 2883584 1 2883584 945654412271 140737488355328 266829 140737488355328

noncomputable def ep1685 := @Enclosure.Real.IsNear.mulLit_ff qz237 qz1101 50107979 524288 1 524288 2 11 0 1 50107979 2883584

noncomputable abbrev qz238 := (Complex.re qz536)

noncomputable abbrev qz239 := (Complex.im qz536)

noncomputable abbrev qz240 := qz536

noncomputable abbrev qz779 := (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HMul.hMul Real Real Real qz0 qz238 qz238) (@HMul.hMul Real Real Real qz0 qz239 qz239))

noncomputable def ep1686 := @Enclosure.Real.IsNear.of_eq qz237 (Real.sqrt qz779) Bool.false 50107979 524288 1 524288 (BSN.norm_eq_sqrt_mul_add qz240)

noncomputable def ep1687 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz779) Bool.false 50107979 524288 1 524288 50107979

noncomputable def ep1688 := @Enclosure.Real.IsNear.sqrt_image qz779 365370889 40000 0 1 25053989 25053990 262144

noncomputable def ep1689 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz238 qz238) (@HMul.hMul Real Real Real qz0 qz239 qz239) 121 4 0 1 364160889 40000 0 1

noncomputable def ep1690 := @Enclosure.Real.IsNear.mulLit_ff qz238 qz238 11 2 0 1 11 2 0 1 121 4

noncomputable def ep1691 := @Enclosure.Complex.IsNear.of_eq qz240 (Complex.mk (Enclosure.sfrac Bool.false 11 2) qz11) Bool.false 11 2 0 1 Bool.false 95415 1000 0 1 (BSN.s_add_nat_mk qz11 Bool.false 95415 1000 5 (@Eq.refl Real qz11))

noncomputable abbrev qz780 := (ep1691 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 11 2) qz11 Bool.false 11 2 0 1 Bool.false 95415 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 11 2) qz273))

noncomputable def ep1692 := @ep1690 0 1 (@Enclosure.Complex.IsNear.re_isNear qz240 Bool.false 11 2 0 1 Bool.false 95415 1000 0 1 qz780)

noncomputable def ep1693 := ep1692 (@Enclosure.Complex.IsNear.re_isNear qz240 Bool.false 11 2 0 1 Bool.false 95415 1000 0 1 qz780)

noncomputable def ep1694 := @Enclosure.Real.IsNear.mulLit_ff qz239 qz239 95415 1000 0 1 95415 1000 0 1 364160889 40000

noncomputable def ep1695 := @ep1694 0 1 (@Enclosure.Complex.IsNear.im_isNear qz240 Bool.false 11 2 0 1 Bool.false 95415 1000 0 1 qz780)

noncomputable def ep1696 := ep1695 (@Enclosure.Complex.IsNear.im_isNear qz240 Bool.false 11 2 0 1 Bool.false 95415 1000 0 1 qz780)

noncomputable def ep1697 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236)) (Real.sqrt (@HAdd.hAdd Real Real Real qz590 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236)) (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236)) (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236))))) Bool.false 945654412271 140737488355328

noncomputable def ep1698 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz590 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236)) (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236)) (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236))))) Bool.false 945654412271 140737488355328

noncomputable def ep1699 := nat_lit 22752048293710717350154396163110429925820167666074654627310220864257442972915413

noncomputable def ep1700 := nat_lit 503935770679619350409959312158188592150962858850283833150511513600000000000000000000

noncomputable def ep1701 := nat_lit 2904728756944863697018903857787771987480710869545660060728923350212769746147298555444339301

noncomputable def ep1702 := nat_lit 114006961408174794205419548891130812925448238857223838856450813536692836384112640000000000000000000000

noncomputable def ep1703 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz590 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236)) (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236)) (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236)))) ep1699 ep1700 ep1701 ep1702

noncomputable def ep1704 := nat_lit 5460702899489091815102236574562405851457810829487892330806675480242572791791801

noncomputable def ep1705 := nat_lit 125983942669904837602489828039547148037740714712570958287627878400000000000000000000

noncomputable def ep1706 := nat_lit 15946799617429433149738098986002096843069929587528710547083957241711891119224858438732163

noncomputable def ep1707 := nat_lit 651468350903855966888111707949318931002561364898421936322576077352530493623500800000000000000000000

noncomputable def ep1708 := nat_lit 18555850933762246729498976833894010612018864247409904164969774352799016443841

noncomputable def ep1709 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236)) (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236)) (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236))) ep1704 ep1705 ep1706 ep1707 ep1708

noncomputable def ep1710 := nat_lit 10284403483257537763468557390983440656142099160209874145928806400000000000000000000

noncomputable def ep1711 := nat_lit 14254852986839111976842066904675629992934148966016964373653854114148600035368541083276347

noncomputable def ep1712 := nat_lit 14250870176021849275677443611391351615681029857152979857056351692086604548014080000000000000000000000

noncomputable def ep1713 := nat_lit 58497811180770555035561816997792282243588815671389098055529588703461416767114179510792074049078172085961069753178162691578951185393936813260800000000000000000000

noncomputable def ep1714 := nat_lit 2336814690874972185821174431379863084651

noncomputable def ep1715 := nat_lit 354942168063904232419076897505280000000000

noncomputable def ep1716 := nat_lit 17934163407936288233765881426338894022501

noncomputable def ep1717 := nat_lit 9647119117745951406686791297769008005120000000000

noncomputable def ep1718 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236)) (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236)) ep1714 ep1715 ep1716 ep1717 ep1714 ep1715 ep1716

noncomputable def ep1719 := nat_lit 136219862478869970152306161197782658529

noncomputable def ep1720 := nat_lit 101412048018258352119736256430080000000000

noncomputable def ep1721 := nat_lit 62860250694278343028556778312329777317333

noncomputable def ep1722 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236) Bool.false ep1714 ep1715 ep1716 ep1717 Bool.true ep1719 ep1720 ep1721

noncomputable def ep1723 := nat_lit 168824584560554149617018847710957640089600000000000

noncomputable def ep1724 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236 Bool.false ep1714 ep1715 ep1716 ep1717 Bool.true ep1719 ep1720 ep1721 ep1723

noncomputable def ep1725 := nat_lit 17503225084554229826819246932428141

noncomputable def ep1726 := nat_lit 283953734451123385935261518004224000000

noncomputable def ep1727 := nat_lit 3462058570010052482949534788492912003

noncomputable def ep1728 := nat_lit 202589501472664979540422617253149168107520000000

noncomputable def ep1729 := nat_lit 2358693722230664973104698490045398260901

noncomputable def ep1730 := nat_lit 373155372996652000426133975164623862469521

noncomputable def ep1731 := @Enclosure.Real.IsNear.subLit_tt_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.re qz236)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.im qz236)) ep1725 ep1726 ep1727 ep1728 ep1729 ep1715 ep1730

noncomputable def ep1732 := nat_lit 202589501472664979540422617253149168107520000000000

noncomputable def ep1733 := nat_lit 663547258194195834960843255386434049428089150166326887616005301887565824000000

noncomputable def ep1734 := nat_lit 9903520314283042199192993792

noncomputable def ep1735 := nat_lit 471050738171189033529628481336377344

noncomputable def ep1736 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.re qz236) 14719419524383369 430080000000 0 1 17836870253843261835 ep1734 235203471459930838187 ep1735 ep1725

noncomputable def ep1737 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5)))) 14719419524383369 430080000000 0 1 0 1 0 1 14719419524383369

noncomputable def ep1738 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) 1 30240 0 1 132474775719450321 128000000 0 1 14719419524383369 430080000000 0

noncomputable def ep1739 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (Complex.mk (Enclosure.sfrac Bool.false 1 30240) qz265) Bool.false 1 30240 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 3 1 42 720 Bool.false EMRow28.d179 EMRow28.d180 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 30240) qz265 Bool.false 1 30240 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 30240) qz277)

noncomputable abbrev qz241 := (@HAdd.hAdd Complex Complex Complex qz263 qz262 qz264)

noncomputable def ep1740 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5)) (@HMul.hMul Complex Complex Complex qz3 (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 4)) qz241) Bool.false 132474775719450321 128000000 0 1 Bool.false 2514676674129239435643 320000000000 0 1

noncomputable def ep1741 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.re qz241)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.im qz241)) 1190699866914572889 3200000000 0 1 132573095379480321 200000000 0 1

noncomputable def ep1742 := nat_lit 662373878597251605000000000

noncomputable def ep1743 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.re qz241) 132299985212730321 1600000000 0 1 9 2 0 1 1190699866914572889 3200000000

noncomputable abbrev qz242 := (@HAdd.hAdd Complex Complex Complex qz263 qz262 qz551)

noncomputable def ep1744 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 4)) (@HMul.hMul Complex Complex Complex qz3 (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3)) qz242) Bool.false 132299985212730321 1600000000 0 1 Bool.true 6947183114787 1000000 0 1

noncomputable def ep1745 := @Enclosure.Real.IsNear.subLit_tt_p (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.re qz242)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.im qz242)) 22941086007 160000 0 1 132529396072800321 1600000000 0 1

noncomputable def ep1746 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.re qz242) 3277298001 80000 0 1 7 2 0 1 22941086007 160000

noncomputable abbrev qz781 := (ep309 (BSN.ascPochhammer_succ_eval_c 2 3 qz14 rfl) (ep337 (@ep338 277795726191480 6944893154787 8000000 0 1 (ep341 rfl) (ep344 rfl) rfl rfl)))

noncomputable def ep1747 := @ep1746 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 3277298001 80000 0 1 Bool.true 6944893154787 8000000 0 1 qz781)

noncomputable def ep1748 := @Enclosure.Complex.IsNear.of_eq qz242 (Complex.mk (Enclosure.sfrac Bool.false 7 2) qz11) Bool.false 7 2 0 1 Bool.false 95415 1000 0 1 (BSN.s_add_nat_mk qz11 Bool.false 95415 1000 3 (@Eq.refl Real qz11))

noncomputable abbrev qz782 := (ep1748 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz11 Bool.false 7 2 0 1 Bool.false 95415 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz273))

noncomputable def ep1749 := ep1747 (@Enclosure.Complex.IsNear.re_isNear qz242 Bool.false 7 2 0 1 Bool.false 95415 1000 0 1 qz782)

noncomputable def ep1750 := @Enclosure.Real.IsNear.mulLit_tf (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.im qz242) 6944893154787 8000000 0 1 95415 1000 0 1 132529396072800321 1600000000

noncomputable def ep1751 := @ep1750 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 3277298001 80000 0 1 Bool.true 6944893154787 8000000 0 1 qz781)

noncomputable def ep1752 := ep1751 (@Enclosure.Complex.IsNear.im_isNear qz242 Bool.false 7 2 0 1 Bool.false 95415 1000 0 1 qz782)

noncomputable def ep1753 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3)) qz242 Bool.false 132299985212730321 1600000000 0 1 Bool.true 6947183114787 1000000 0 1 (@ep1745 21167997634036851360000 132299985212730321 1600000000 0 1 (ep1749 rfl) (ep1752 rfl) rfl rfl)

noncomputable def ep1754 := @Enclosure.Real.IsNear.addLit_tt (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.im qz242)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.re qz242)) 62540677753083 16000000 0 1 48614252083509 16000000 0 1

noncomputable def ep1755 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.im qz242) 3277298001 80000 0 1 95415 1000 0 1 62540677753083 16000000

noncomputable def ep1756 := @ep1755 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 3277298001 80000 0 1 Bool.true 6944893154787 8000000 0 1 qz781)

noncomputable def ep1757 := ep1756 (@Enclosure.Complex.IsNear.im_isNear qz242 Bool.false 7 2 0 1 Bool.false 95415 1000 0 1 qz782)

noncomputable def ep1758 := @Enclosure.Real.IsNear.mulLit_tf (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.re qz242) 6944893154787 8000000 0 1 7 2 0 1 48614252083509 16000000

noncomputable def ep1759 := @ep1758 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 3277298001 80000 0 1 Bool.true 6944893154787 8000000 0 1 qz781)

noncomputable def ep1760 := ep1759 (@Enclosure.Complex.IsNear.re_isNear qz242 Bool.false 7 2 0 1 Bool.false 95415 1000 0 1 qz782)

noncomputable abbrev qz783 := (ep1744 (BSN.ascPochhammer_succ_eval_c 3 4 qz14 rfl) (ep1753 (@ep1754 1778478877385472000000 6947183114787 1000000 0 1 (ep1757 rfl) (ep1760 rfl) rfl rfl)))

noncomputable def ep1761 := @ep1743 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 4)) Bool.false 132299985212730321 1600000000 0 1 Bool.true 6947183114787 1000000 0 1 qz783)

noncomputable def ep1762 := @Enclosure.Complex.IsNear.of_eq qz241 (Complex.mk (Enclosure.sfrac Bool.false 9 2) qz11) Bool.false 9 2 0 1 Bool.false 95415 1000 0 1 (BSN.s_add_nat_mk qz11 Bool.false 95415 1000 4 (@Eq.refl Real qz11))

noncomputable abbrev qz784 := (ep1762 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9 2) qz11 Bool.false 9 2 0 1 Bool.false 95415 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 9 2) qz273))

noncomputable def ep1763 := ep1761 (@Enclosure.Complex.IsNear.re_isNear qz241 Bool.false 9 2 0 1 Bool.false 95415 1000 0 1 qz784)

noncomputable def ep1764 := @Enclosure.Real.IsNear.mulLit_tf (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.im qz241) 6947183114787 1000000 0 1 95415 1000 0 1 132573095379480321 200000000

noncomputable def ep1765 := @ep1764 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 4)) Bool.false 132299985212730321 1600000000 0 1 Bool.true 6947183114787 1000000 0 1 qz783)

noncomputable def ep1766 := ep1765 (@Enclosure.Complex.IsNear.im_isNear qz241 Bool.false 9 2 0 1 Bool.false 95415 1000 0 1 qz784)

noncomputable def ep1767 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 4)) qz241 Bool.false 132474775719450321 128000000 0 1 Bool.false 2514676674129239435643 320000000000 0 1 (@ep1741 ep1742 132474775719450321 128000000 0 1 (ep1763 rfl) (ep1766 rfl) rfl rfl)

noncomputable def ep1768 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.im qz241)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.re qz241)) 2524680617814532715643 320000000000 0 1 62524648033083 2000000 0 1

noncomputable def ep1769 := nat_lit 5029353348258478871286000000

noncomputable def ep1770 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.im qz241) 132299985212730321 1600000000 0 1 95415 1000 0 1 2524680617814532715643 320000000000

noncomputable def ep1771 := @ep1770 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 4)) Bool.false 132299985212730321 1600000000 0 1 Bool.true 6947183114787 1000000 0 1 qz783)

noncomputable def ep1772 := ep1771 (@Enclosure.Complex.IsNear.im_isNear qz241 Bool.false 9 2 0 1 Bool.false 95415 1000 0 1 qz784)

noncomputable def ep1773 := @Enclosure.Real.IsNear.mulLit_tf (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.re qz241) 6947183114787 1000000 0 1 9 2 0 1 62524648033083 2000000

noncomputable def ep1774 := @ep1773 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 4)) Bool.false 132299985212730321 1600000000 0 1 Bool.true 6947183114787 1000000 0 1 qz783)

noncomputable def ep1775 := ep1774 (@Enclosure.Complex.IsNear.re_isNear qz241 Bool.false 9 2 0 1 Bool.false 95415 1000 0 1 qz784)

noncomputable abbrev qz785 := (ep1740 (BSN.ascPochhammer_succ_eval_c 4 5 qz14 rfl) (ep1767 (@ep1768 ep1769 2514676674129239435643 320000000000 0 1 (ep1772 rfl) (ep1775 rfl) rfl rfl)))

noncomputable def ep1776 := @ep1738 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) Bool.false 1 30240 0 1 Bool.false 0 1 0 1 ep1739) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5)) Bool.false 132474775719450321 128000000 0 1 Bool.false 2514676674129239435643 320000000000 0 1 qz785)

noncomputable def ep1777 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) 0 1 0 1 2514676674129239435643 320000000000 0 1 0 1 0

noncomputable def ep1778 := @ep1777 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) Bool.false 1 30240 0 1 Bool.false 0 1 0 1 ep1739) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5)) Bool.false 132474775719450321 128000000 0 1 Bool.false 2514676674129239435643 320000000000 0 1 qz785)

noncomputable def ep1779 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5)))) 279408519347693270627 1075200000000000 0 1 0 1 0 1 279408519347693270627

noncomputable def ep1780 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) 1 30240 0 1 2514676674129239435643 320000000000 0 1 279408519347693270627 1075200000000000 0

noncomputable def ep1781 := @ep1780 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) Bool.false 1 30240 0 1 Bool.false 0 1 0 1 ep1739) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5)) Bool.false 132474775719450321 128000000 0 1 Bool.false 2514676674129239435643 320000000000 0 1 qz785)

noncomputable def ep1782 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) 0 1 0 1 132474775719450321 128000000 0 1 0 1 0

noncomputable def ep1783 := @ep1782 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) Bool.false 1 30240 0 1 Bool.false 0 1 0 1 ep1739) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5)) Bool.false 132474775719450321 128000000 0 1 Bool.false 2514676674129239435643 320000000000 0 1 qz785)

noncomputable def ep1784 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5)) Bool.false 14719419524383369 430080000000 0 1 Bool.false 279408519347693270627 1075200000000000 0 1 (@ep1737 14719419524383369 430080000000 0 1 (ep1776 rfl) (ep1778 rfl) rfl rfl) (@ep1779 279408519347693270627 1075200000000000 0 1 (ep1781 rfl) (ep1783 rfl) rfl rfl)

noncomputable def ep1785 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) Bool.false 14719419524383369 430080000000 0 1 Bool.false 279408519347693270627 1075200000000000 0 1 ep1784

noncomputable def ep1786 := nat_lit 4951760157141521099596496896

noncomputable def ep1787 := nat_lit 942101476342378067059256962672754688

noncomputable def ep1788 := @Enclosure.Complex.IsNear.re_isNear qz236 Bool.true 17836870253843261835 ep1734 235203471459930838187 ep1735 Bool.true 126626081108976273945 ep1786 6677594761029835456615 ep1787

noncomputable abbrev qz786 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 1521681143169024)))

noncomputable def ep1789 := @Enclosure.Complex.IsNear.of_eq qz236 (Complex.mk (@HMul.hMul Real Real Real qz0 qz786 (Real.cos qz362)) (@HMul.hMul Real Real Real qz0 qz786 qz911)) Bool.true 17836870253843261835 ep1734 235203471459930838187 ep1735 Bool.true 126626081108976273945 ep1786 6677594761029835456615

noncomputable abbrev qz787 := (Real.sqrt (@Nat.cast Real Real.instNatCast 1521681143169024))

noncomputable abbrev qz788 := (@Nat.cast Real Real.instNatCast 1521681143169024)

noncomputable def ep1790 := @Enclosure.Real.IsNear.inv_image qz787 5489990913150197828255 140737488355328 1 140737488355328 1803922 1803923 70368744177664 (@Enclosure.Real.IsNear.of_eq qz787 (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz788 qz268)) Bool.false 5489990913150197828255 140737488355328 1 140737488355328 (BSN.sqrt_natCast_div_one 1521681143169024) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz788 qz268)) Bool.false 5489990913150197828255 140737488355328 1 140737488355328 5489990913150197828255 140737488355328 1 140737488355328 (BSN.sqrt_enclosure 1521681143169024 1 2744995456575098914127 2744995456575098914128 70368744177664 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep1791 := nat_lit 3509601489984907459688398848

noncomputable def ep1792 := nat_lit 50734900800000000000000000

noncomputable def ep1793 := nat_lit 8057323691196381544451112173568

noncomputable def ep1794 := nat_lit 2535301200456458802993406410752

noncomputable def ep1795 := nat_lit 24937218441216000000000000000

noncomputable def ep1796 := nat_lit 44992639437845299200000000000000000000

noncomputable def ep1797 := nat_lit 614724096498688896779568985355059200

noncomputable def ep1798 := BSN.log_dyadic_bound 8 40 10 9 ep1796 70368744177664 24937218441216 ep1797 620765814357606216499200 28532070465432 48 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP 8) (BSN.artanhQ 40) 0 9 ep1797 ep1796 620765814357606216499200 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1799 := @Enclosure.Real.IsNear.mulLit_ff qz11 qz363 95415 1000 0 1 3578170511529591 1125899906842624 33561672173 761023512000000000000000 68282227871519185053 225179981368524800 213485796692453 ep1792 qz273 (BSN.isNear_log_sfrac 24 1 3578170511529591 1125899906842624 33561672173 761023512000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz913 Bool.false ep1793 ep1794 1099748873764864 ep1795 3578170511529591 1125899906842624 33561672173 761023512000000000000000 (BSN.log_rat_reduce_isNear 24 1 4 48 32 28532070465432 70368744177664 24973259072661432 36028797018963968 24937218441216 1000000000000000 rfl rfl rfl rfl (ep1798 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1800 := nat_lit 59240397723558570122214237905631398364384594442408167035333771264

noncomputable def ep1801 := nat_lit 842498333348457493583344221469363458551160763204392890034487820288

noncomputable def ep1802 := nat_lit 168715372356585192657954456905841204448267235928416295277841123521

noncomputable def ep1803 := nat_lit 828209561614867654492170703473243054294133076660446386619502906855915520

noncomputable def ep1804 := nat_lit 5797466931304073581445194924312701380058931536623124706336520347991408640

noncomputable def ep1805 := BSN.sin_dyadic_bound_f 20266962489261233 288230376151711744 2 1 140737488355328 49923142387201 ep1802 ep1803 ep1802 ep1802 ep1804 ep1802 9887825144286 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 20266962489261233) (BSN.sinEvenQ 288230376151711744) 0 1 ep1802 ep1803 ep1802 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 20266962489261233) (BSN.sinOddQ 288230376151711744) 0 1 ep1802 ep1804 ep1802 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz789 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 21338196209849745) (@Nat.cast Real Real.instNatCast 70368744177664))

noncomputable def ep1806 := @Enclosure.Real.IsNear.cos_image qz362 qz789 Bool.false 21338196209849745 70368744177664 593 140737488355328 Bool.true 9887825144286 140737488355328 1 24937218441216 (@Enclosure.Real.IsNear.recentre' qz362 Bool.false 68282227871519185053 225179981368524800 213485796692453 ep1792 21338196209849745 70368744177664 593 140737488355328 (ep1799 rfl) rfl) (Enclosure.sfrac_false_div 21338196209849745 70368744177664) (BSN.cos_reduce1 qz789 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1800) (@Nat.cast Real Real.instNatCast ep1801)) ep1636 ep1614 Bool.false 9887825144286 140737488355328 48 ep1637 49874436882432 24937218441216 (BSN.sin_reduce_arg_pos_rat_q1 21338196209849745 70368744177664 ep1636 ep1614 48 ep1800 ep1801 rfl rfl rfl rfl) EMRow28.d184 (@BSN.sin_arg_round Bool.false 9887825144286 140737488355328 ep1800 ep1801 20266962489261233 288230376151711744 49923142387201 49874436882432 (ep1805 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1807 := nat_lit 1956243612544789033493353892920784052544938293417189914888555953631715997586940976479384535329460731260434898016620348762838653797632680321

noncomputable def ep1808 := nat_lit 1920607018260815532978912358173530051388297685428644360391864145082015815875441738941203950126953068194034147076646652757941625662062128655237120

noncomputable def ep1809 := nat_lit 28464876869421190985109909534764432681789213911802744649850049230739348993838516887677391942190330325535746943204039309411579437441

noncomputable def ep1810 := nat_lit 5868730780704613361637679708542533088105949516673141921060178561195049531282124941761119830633598309400644042978367159880437342569739166081

noncomputable def ep1811 := nat_lit 86427315821736698984051056117808852312473395844288996217633886528690711714394878252354177755712888068731536618449099374107373154792795789485670400

noncomputable def ep1812 := BSN.cos_dyadic_bound_f 20266962489261233 288230376151711744 3 2 140737488355328 49923142387201 ep1807 ep1808 ep1809 ep1810 ep1811 ep1809 140389713093524 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 20266962489261233) (BSN.cosEvenQ 288230376151711744) 0 2 ep1807 ep1808 ep1809 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 20266962489261233) (BSN.cosOddQ 288230376151711744) 0 2 ep1810 ep1811 ep1809 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1813 := @Enclosure.Real.IsNear.sin_image qz362 qz789 Bool.false 21338196209849745 70368744177664 593 140737488355328 Bool.false 140389713093524 140737488355328 1 24937218441216 (@Enclosure.Real.IsNear.recentre' qz362 Bool.false 68282227871519185053 225179981368524800 213485796692453 ep1792 21338196209849745 70368744177664 593 140737488355328 (ep1799 rfl) rfl) (Enclosure.sfrac_false_div 21338196209849745 70368744177664) (BSN.sin_reduce1 qz789 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1800) (@Nat.cast Real Real.instNatCast ep1801)) ep1636 ep1614 Bool.false 140389713093524 140737488355328 48 ep1637 49874436882432 24937218441216 (BSN.sin_reduce_arg_pos_rat_q1 21338196209849745 70368744177664 ep1636 ep1614 48 ep1800 ep1801 rfl rfl rfl rfl) EMRow28.d184 (@BSN.cos_arg_round Bool.false 140389713093524 140737488355328 ep1800 ep1801 20266962489261233 288230376151711744 49923142387201 49874436882432 (ep1812 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1814 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz786 (Real.cos qz362)) (@HMul.hMul Real Real Real qz0 qz786 qz911) Bool.true 17836870253843261835 ep1734 235203471459930838187 ep1735 Bool.true 126626081108976273945 ep1786 6677594761029835456615 ep1787 (@Enclosure.Real.IsNear.mulLit_ft qz786 (Real.cos qz362) 3607845 140737488355328 1 140737488355328 4943912572143 70368744177664 56947738739 13388067207278852308992 17836870253843261835 ep1734 235203471459930838187 ep1735 (@Enclosure.Real.IsNear.recentre' qz786 Bool.false 3607845 140737488355328 1 140737488355328 3607845 140737488355328 1 140737488355328 (ep1790 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' (Real.cos qz362) Bool.true 9887825144286 140737488355328 14928508023996416 ep1791 4943912572143 70368744177664 56947738739 13388067207278852308992 (ep1806 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz786 qz911 3607845 140737488355328 1 140737488355328 35097428273381 35184372088832 56947738739 13388067207278852308992 126626081108976273945 ep1786 6677594761029835456615 ep1787 (@Enclosure.Real.IsNear.recentre' qz786 Bool.false 3607845 140737488355328 1 140737488355328 3607845 140737488355328 1 140737488355328 (ep1790 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg (Real.sin qz362) Bool.false 35097428273381 35184372088832 56947738739 13388067207278852308992 (@Enclosure.Real.IsNear.recentre' (Real.sin qz362) Bool.false 140389713093524 140737488355328 14928508023996416 ep1791 35097428273381 35184372088832 56947738739 13388067207278852308992 (ep1813 rfl rfl) rfl)) rfl)

noncomputable def ep1815 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.im qz236) 279408519347693270627 1075200000000000 0 1 126626081108976273945 ep1786 6677594761029835456615 ep1787 ep1729

noncomputable def ep1816 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) Bool.false 14719419524383369 430080000000 0 1 Bool.false 279408519347693270627 1075200000000000 0 1 ep1784

noncomputable def ep1817 := @Enclosure.Complex.IsNear.im_isNear qz236 Bool.true 17836870253843261835 ep1734 235203471459930838187 ep1735 Bool.true 126626081108976273945 ep1786 6677594761029835456615 ep1787

noncomputable def ep1818 := nat_lit 124257494038107830163164841823068047

noncomputable def ep1819 := nat_lit 141976867225561692967630759002112000000

noncomputable def ep1820 := nat_lit 19658063740284531438509506588085407187

noncomputable def ep1821 := nat_lit 81035800589065991816169046901259667243008000000

noncomputable def ep1822 := nat_lit 332251567161550640250318919269138374703

noncomputable def ep1823 := nat_lit 709884336127808464838153795010560000000000

noncomputable def ep1824 := nat_lit 65717853706056707594985918761455537033249

noncomputable def ep1825 := @Enclosure.Real.IsNear.addLit_tt (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.im qz236)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.re qz236)) ep1818 ep1819 ep1820 ep1821 ep1822 ep1823 ep1824

noncomputable def ep1826 := nat_lit 506473753681662448851056543132872920268800000000000

noncomputable def ep1827 := nat_lit 135380485300527564014117866601558641599095070403455472689326673400692736000000

noncomputable def ep1828 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.im qz236) 14719419524383369 430080000000 0 1 126626081108976273945 ep1786 6677594761029835456615 ep1787 ep1818

noncomputable def ep1829 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.re qz236) 279408519347693270627 1075200000000000 0 1 17836870253843261835 ep1734 235203471459930838187 ep1735 ep1822

noncomputable abbrev qz790 := (@ep1789 ep1787 (BSN.cpow_neg_s_sub_mk qz11 95415 1000 24 5 1521681143169024 (@Eq.refl Real qz11) rfl EMRow28.d181) ep1814)

noncomputable def ep1830 := ep1724 (@ep1731 ep1732 ep1733 ep1714 ep1715 ep1716 ep1717 (@ep1736 ep1726 ep1727 ep1728 ep1785 (ep1788 qz790) rfl) (@ep1815 ep1715 ep1730 ep1732 ep1816 (ep1817 qz790) rfl) rfl rfl) (@ep1825 ep1826 ep1827 ep1719 ep1720 ep1721 ep1723 (@ep1828 ep1819 ep1820 ep1821 ep1785 (ep1817 qz790) rfl) (@ep1829 ep1823 ep1824 ep1826 ep1816 (ep1788 qz790) rfl) rfl rfl)

noncomputable def ep1831 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236)) (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236)) ep1719 ep1720 ep1721 ep1723 ep1719 ep1720 ep1721

noncomputable def ep1832 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236) Bool.false ep1714 ep1715 ep1716 ep1717 Bool.true ep1719 ep1720 ep1721

noncomputable def ep1833 := @ep1684 47384831431332610309 405828369621610135552 14315916607691 405828369621610135552 (@ep1685 1 2883584 (ep1686 (@ep1687 524288 1 524288 (ep1688 (@ep1689 1461483556 365370889 40000 0 1 (ep1693 rfl) (ep1696 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 11) rfl) (@ep1697 266829 140737488355328 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236)) (@ep1698 266829 140737488355328 945654412271 140737488355328 266829 140737488355328 (@ep1703 472827072721 472827339550 70368744177664 (@ep1709 ep1710 ep1711 ep1712 ep1713 ep1699 ep1700 ep1701 ep1702 (@ep1718 ep1717 ep1704 ep1705 ep1706 ep1707 (@ep1722 ep1723 ep1830) (@ep1722 ep1723 ep1830) rfl) (@ep1831 ep1723 ep1708 ep1710 ep1711 ep1712 (@ep1832 ep1723 ep1830) (@ep1832 ep1723 ep1830) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow28.d185 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz590 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 2 4) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz14 2 24))) (@HMul.hMul Real Real Real qz0 qz234 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236)))) Bool.false ep1638 ep1639 15295608221978490251 ep1639 := ep1682 (ep1683 ep1833) rfl rfl

theorem EMRow28.d186 : @Eq Nat (Nat.pow 25 (Nat.succ (Nat.mul 2 5))) 2384185791015625 := @Eq.refl Nat 2384185791015625

noncomputable abbrev qz540 := (@HAdd.hAdd Complex Complex Complex qz548 (@HAdd.hAdd Complex Complex Complex qz548 qz549 (@HMul.hMul Complex Complex Complex qz543 Complex.I ↑(Enclosure.sfrac Bool.false 97714 1000))) qz820)

noncomputable abbrev qz243 := (@Norm.norm Complex Complex.instNorm qz540)

noncomputable abbrev qz244 := (@HPow.hPow Complex Complex Complex qz816 qz963 (@HSub.hSub Complex Complex Complex qz580 (@Neg.neg Complex Complex.instNeg qz373) qz820))

noncomputable abbrev qz791 := (@HDiv.hDiv Real Real Real qz1 qz243 (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (Complex.re qz64) (@Nat.cast Real Real.instNatCast 5)))

noncomputable def ep1834 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 2 4) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz64 2 25))) (@HMul.hMul Real Real Real qz0 qz791 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244))) 7545916965 44839995441152 37809315 44839995441152 170550438564251187 1585267068834414592 97877920297

noncomputable def ep1835 := nat_lit 7659443181376270909166221000704

noncomputable def ep1836 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 2 4) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz64 2 25)) 5055 85525504 15 85525504 1492763 524288 3041 524288 7545916965 44839995441152

noncomputable def ep1837 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz64 2 25)) (Real.sqrt (@HAdd.hAdd Real Real Real qz590 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz64 2 25)) (Complex.re (zetaApproximant qz64 2 25))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz64 2 25)) (Complex.im (zetaApproximant qz64 2 25))))) Bool.false 1492763 524288 3041 524288

noncomputable def ep1838 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz590 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz64 2 25)) (Complex.re (zetaApproximant qz64 2 25))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz64 2 25)) (Complex.im (zetaApproximant qz64 2 25))))) Bool.false 1492763 524288 3041 524288

noncomputable def ep1839 := nat_lit 2891433295785809104214503187469150755939912979334321224809638921

noncomputable def ep1840 := nat_lit 356672564906864887048857609830400000000000000000000000000000000

noncomputable def ep1841 := nat_lit 478616341912094045052094047380346714614406575159308643618187239545926985429037807

noncomputable def ep1842 := nat_lit 14497589115334476518320872049348294528372464785817600000000000000000000000000000000

noncomputable def ep1843 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz590 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz64 2 25)) (Complex.re (zetaApproximant qz64 2 25))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz64 2 25)) (Complex.im (zetaApproximant qz64 2 25)))) ep1839 ep1840 ep1841 ep1842 744861 747902

noncomputable def ep1844 := nat_lit 276080896818626050887047097461209026525266877969952459533819222027463009

noncomputable def ep1845 := nat_lit 34056080185974569952508809853940199849984000000000000000000000000000000

noncomputable def ep1846 := nat_lit 477168513557418501099327284319463244550519724913202267147486077360827146756032431

noncomputable def ep1847 := nat_lit 7054502346548833942039434727500443092908370556349347314238383597201

noncomputable def ep1848 := nat_lit 212850501162341062203180061587126249062400000000000000000000000000000000

noncomputable def ep1849 := nat_lit 22622318041805374261980672826304219748232035095412132354705659142184979265709

noncomputable def ep1850 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz64 2 25)) (Complex.re (zetaApproximant qz64 2 25))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz64 2 25)) (Complex.im (zetaApproximant qz64 2 25))) ep1844 ep1845 ep1846 ep1842 ep1847 ep1848 ep1849

noncomputable def ep1851 := nat_lit 226524829927101195598763625771067102005819762278400000000000000000000000000000000

noncomputable def ep1852 := nat_lit 58764197497890713319354542399737206496184832140824370597339923121753939407613219608910270736549986670963415056384000000000000000000000000000000

noncomputable def ep1853 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz64 2 25)) (Complex.re (zetaApproximant qz64 2 25)) ep1160 ep1161 ep1162 ep1163 ep1160 ep1161 ep1162 ep1163 ep1844

noncomputable def ep1854 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (zetaApproximant qz64 2 25)) (Complex.im (zetaApproximant qz64 2 25)) ep1352 ep1353 ep1354 ep1355 ep1352 ep1353 ep1354 ep1355 ep1847

noncomputable def ep1855 := @ep1834 2305843009213693952 ep1835 14266824687600640410867 132403090856119141138432 170564633190287977 192586313972536932564992 (@ep1836 37809315 44839995441152 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 2 4) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 30720 334084) qz1099) Bool.false 5055 85525504 15 85525504 (BSN.theta_err_eq 2 4 30720 334084 EMRow28.d23 EMRow28.d24 rfl) (ep1662 rfl)) (ep1837 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz64 2 25)) (@ep1838 1492763 524288 3041 524288 (@ep1843 262144 (@ep1850 ep1851 ep1852 ep1839 ep1840 ep1841 ep1842 (@ep1853 ep1845 ep1846 ep1842 ep1471 ep1471 rfl) (@ep1854 ep1848 ep1849 ep1851 ep1479 ep1479 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable def ep1856 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz791 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz243 qz1101) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244))) Bool.false 170550438564251187 1585267068834414592 97877920297 2305843009213693952 (BSN.zrb_shape_eq qz243 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244)) qz61 5)

noncomputable def ep1857 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz243 qz1101) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244)) 51311367 2883584 1 2883584 3323833461 549755813888 159571 70368744177664

noncomputable def ep1858 := @Enclosure.Real.IsNear.mulLit_ff qz243 qz1101 51311367 524288 1 524288 2 11 0 1 51311367 2883584

noncomputable abbrev qz245 := (Complex.re qz540)

noncomputable abbrev qz246 := (Complex.im qz540)

noncomputable abbrev qz247 := qz540

noncomputable abbrev qz792 := (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HMul.hMul Real Real Real qz0 qz245 qz245) (@HMul.hMul Real Real Real qz0 qz246 qz246))

noncomputable def ep1859 := @Enclosure.Real.IsNear.of_eq qz243 (Real.sqrt qz792) Bool.false 51311367 524288 1 524288 (BSN.norm_eq_sqrt_mul_add qz247)

noncomputable def ep1860 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz792) Bool.false 51311367 524288 1 524288 51311367

noncomputable def ep1861 := @Enclosure.Real.IsNear.sqrt_image qz792 2394568949 250000 0 1 25655683 25655684 262144

noncomputable def ep1862 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz245 qz245) (@HMul.hMul Real Real Real qz0 qz246 qz246) 121 4 0 1 2387006449 250000 0 1

noncomputable def ep1863 := @Enclosure.Real.IsNear.mulLit_ff qz245 qz245 11 2 0 1 11 2 0 1 121 4

noncomputable def ep1864 := @Enclosure.Complex.IsNear.of_eq qz247 (Complex.mk (Enclosure.sfrac Bool.false 11 2) qz61) Bool.false 11 2 0 1 Bool.false 97714 1000 0 1 (BSN.s_add_nat_mk qz61 Bool.false 97714 1000 5 (@Eq.refl Real qz61))

noncomputable abbrev qz793 := (ep1864 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 11 2) qz61 Bool.false 11 2 0 1 Bool.false 97714 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 11 2) qz375))

noncomputable def ep1865 := @ep1863 0 1 (@Enclosure.Complex.IsNear.re_isNear qz247 Bool.false 11 2 0 1 Bool.false 97714 1000 0 1 qz793)

noncomputable def ep1866 := ep1865 (@Enclosure.Complex.IsNear.re_isNear qz247 Bool.false 11 2 0 1 Bool.false 97714 1000 0 1 qz793)

noncomputable def ep1867 := @Enclosure.Real.IsNear.mulLit_ff qz246 qz246 97714 1000 0 1 97714 1000 0 1 2387006449 250000

noncomputable def ep1868 := @ep1867 0 1 (@Enclosure.Complex.IsNear.im_isNear qz247 Bool.false 11 2 0 1 Bool.false 97714 1000 0 1 qz793)

noncomputable def ep1869 := ep1868 (@Enclosure.Complex.IsNear.im_isNear qz247 Bool.false 11 2 0 1 Bool.false 97714 1000 0 1 qz793)

noncomputable def ep1870 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244)) (Real.sqrt (@HAdd.hAdd Real Real Real qz590 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244))))) Bool.false 3323833461 549755813888

noncomputable def ep1871 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz590 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244))))) Bool.false 850901366016 140737488355328

noncomputable def ep1872 := nat_lit 512273207660829204863219852478085477504428225950828564886518178112342579308610532087269

noncomputable def ep1873 := nat_lit 14014021943109226472811139624150065753099514926981236052197376000000000000000000000000000000

noncomputable def ep1874 := nat_lit 165121251954054226970520734033518849112124008779276371643514113262608631653112629901641803397588054024163

noncomputable def ep1875 := nat_lit 6021871408391691042092555049473837481670907169548648683929600000000000000000000000000000000000000000000000000000000

noncomputable def ep1876 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz590 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244)))) ep1872 ep1873 ep1874 ep1875

noncomputable def ep1877 := nat_lit 2920354533970675859103347000697250026386917837817210543308554310727944462610064699983449

noncomputable def ep1878 := nat_lit 350350548577730661820278490603751643827487873174530901304934400000000000000000000000000000000

noncomputable def ep1879 := nat_lit 34830919264827871770409958061446780637474670722283661225819172790368330250660586128575803424352010410519

noncomputable def ep1880 := nat_lit 69192321446418453168144434025187473133617394606488505213000756852276112231636842489

noncomputable def ep1881 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244))) ep1877 ep1878 ep1879 ep1875 ep1880

noncomputable def ep1882 := nat_lit 2451992865385422173373355243440494693789982595493763481600000000000000000000000000000000

noncomputable def ep1883 := nat_lit 32572583172306588800027693993018017118662334514248177604423735118060075350613010943266499993309010903411

noncomputable def ep1884 := nat_lit 1505467852097922760523138762368459370417726792387162170982400000000000000000000000000000000000000000000000000000000

noncomputable def ep1885 := nat_lit 31402256257811450084145382661927862553209812806284856377508892220566919055858552584515546406973631456541812003684096230934804706622336411893760000000000000000000000000000000000

noncomputable def ep1886 := nat_lit 54040304717596438245042985127595316612598107

noncomputable def ep1887 := nat_lit 18717653393994949756474758266880000000000000000

noncomputable def ep1888 := nat_lit 2458118065849354950613074054869432109613843341613

noncomputable def ep1889 := nat_lit 2453950164202951176569078415360000000000000000000000000000

noncomputable def ep1890 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244)) ep1886 ep1887 ep1888 ep1889 ep1886 ep1887 ep1888

noncomputable def ep1891 := nat_lit 263044333613971721244386510956297276763317

noncomputable def ep1892 := nat_lit 49517601571415210995964968960000000000000000

noncomputable def ep1893 := nat_lit 2498716761238087242286549793625146560434485147369

noncomputable def ep1894 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244) Bool.false ep1886 ep1887 ep1888 ep1889 Bool.false ep1891 ep1892 ep1893

noncomputable def ep1895 := nat_lit 1226975082101475588284539207680000000000000000000000000000

noncomputable def ep1896 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244 Bool.false ep1886 ep1887 ep1888 ep1889 Bool.false ep1891 ep1892 ep1893 ep1895

noncomputable def ep1897 := nat_lit 67274163249073217807152095226243315249

noncomputable def ep1898 := nat_lit 93588266969974748782373791334400000000000

noncomputable def ep1899 := nat_lit 9180132539632210543268448726760613110548461

noncomputable def ep1900 := nat_lit 36809252463044267648536176230400000000000000000000000

noncomputable def ep1901 := nat_lit 40585472067781794683612566082346653562798107

noncomputable def ep1902 := nat_lit 5538327689621622743185532419256173706731837824839

noncomputable def ep1903 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.re qz244)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.im qz244)) ep1897 ep1898 ep1899 ep1900 ep1901 ep1887 ep1902

noncomputable def ep1904 := nat_lit 7361850492608853529707235246080000000000000000000000000000

noncomputable def ep1905 := nat_lit 5057538465049201335703190512760753875236981847673265261313569208266443980800000000000

noncomputable def ep1906 := nat_lit 618970019642690137449562112

noncomputable def ep1907 := nat_lit 1612776106242205459327861

noncomputable def ep1908 := nat_lit 243447436924895950056456192000000000000

noncomputable def ep1909 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.re qz244) 5692130794907464601 151200000000000 0 1 11818801372108469849 ep1906 ep1907 ep1908 ep1897

noncomputable def ep1910 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)))) 5692130794907464601 151200000000000 0 1 0 1 0 1 5692130794907464601

noncomputable def ep1911 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) 1 30240 0 1 5692130794907464601 5000000000 0 1 5692130794907464601 151200000000000 0

noncomputable abbrev qz248 := (@HAdd.hAdd Complex Complex Complex qz263 qz373 qz264)

noncomputable def ep1912 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)) (@HMul.hMul Complex Complex Complex qz3 (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4)) qz248) Bool.false 5692130794907464601 5000000000 0 1 Bool.false 276701285685498482011057 31250000000000 0 1

noncomputable def ep1913 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.re qz248)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.im qz248)) 51164730342544181409 125000000000 0 1 5696158720633902101 7812500000 0 1

noncomputable def ep1914 := nat_lit 1111744295880364179882812500000

noncomputable def ep1915 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.re qz248) 5684970038060464601 62500000000 0 1 9 2 0 1 51164730342544181409 125000000000

noncomputable abbrev qz249 := (@HAdd.hAdd Complex Complex Complex qz263 qz373 qz551)

noncomputable def ep1916 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4)) (@HMul.hMul Complex Complex Complex qz3 (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) qz249) Bool.false 5684970038060464601 62500000000 0 1 Bool.true 116588384891293 15625000 0 1

noncomputable def ep1917 := @Enclosure.Real.IsNear.subLit_tt_p (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.re qz249)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.im qz249)) 150374843787 1000000 0 1 5694368465797152101 62500000000 0 1

noncomputable def ep1918 := nat_lit 5684970038060464601000000

noncomputable def ep1919 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.re qz249) 21482120541 500000 0 1 7 2 0 1 150374843787 1000000

noncomputable abbrev qz794 := (ep1108 (BSN.ascPochhammer_succ_eval_c 2 3 qz64 rfl) (ep1136 (@ep1137 11655174214129300 116551742141293 125000000 0 1 (ep1140 rfl) (ep1143 rfl) rfl rfl)))

noncomputable def ep1920 := @ep1919 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 21482120541 500000 0 1 Bool.true 116551742141293 125000000 0 1 qz794)

noncomputable def ep1921 := @Enclosure.Complex.IsNear.of_eq qz249 (Complex.mk (Enclosure.sfrac Bool.false 7 2) qz61) Bool.false 7 2 0 1 Bool.false 97714 1000 0 1 (BSN.s_add_nat_mk qz61 Bool.false 97714 1000 3 (@Eq.refl Real qz61))

noncomputable abbrev qz795 := (ep1921 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz61 Bool.false 7 2 0 1 Bool.false 97714 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz375))

noncomputable def ep1922 := ep1920 (@Enclosure.Complex.IsNear.re_isNear qz249 Bool.false 7 2 0 1 Bool.false 97714 1000 0 1 qz795)

noncomputable def ep1923 := @Enclosure.Real.IsNear.mulLit_tf (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.im qz249) 116551742141293 125000000 0 1 97714 1000 0 1 5694368465797152101 62500000000

noncomputable def ep1924 := @ep1923 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 21482120541 500000 0 1 Bool.true 116551742141293 125000000 0 1 qz794)

noncomputable def ep1925 := ep1924 (@Enclosure.Complex.IsNear.im_isNear qz249 Bool.false 7 2 0 1 Bool.false 97714 1000 0 1 qz795)

noncomputable def ep1926 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) qz249 Bool.false 5684970038060464601 62500000000 0 1 Bool.true 116588384891293 15625000 0 1 (@ep1917 ep1918 5684970038060464601 62500000000 0 1 (ep1922 rfl) (ep1925 rfl) rfl rfl)

noncomputable def ep1927 := @Enclosure.Real.IsNear.addLit_tt (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.im qz249)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.re qz249)) 1049551963271637 250000000 0 1 815862194989051 250000000 0 1

noncomputable def ep1928 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.im qz249) 21482120541 500000 0 1 97714 1000 0 1 1049551963271637 250000000

noncomputable def ep1929 := @ep1928 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 21482120541 500000 0 1 Bool.true 116551742141293 125000000 0 1 qz794)

noncomputable def ep1930 := ep1929 (@Enclosure.Complex.IsNear.im_isNear qz249 Bool.false 7 2 0 1 Bool.false 97714 1000 0 1 qz795)

noncomputable def ep1931 := @Enclosure.Real.IsNear.mulLit_tf (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.re qz249) 116551742141293 125000000 0 1 7 2 0 1 815862194989051 250000000

noncomputable def ep1932 := @ep1931 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 21482120541 500000 0 1 Bool.true 116551742141293 125000000 0 1 qz794)

noncomputable def ep1933 := ep1932 (@Enclosure.Complex.IsNear.re_isNear qz249 Bool.false 7 2 0 1 Bool.false 97714 1000 0 1 qz795)

noncomputable abbrev qz796 := (ep1916 (BSN.ascPochhammer_succ_eval_c 3 4 qz64 rfl) (ep1926 (@ep1927 466353539565172000000000 116588384891293 15625000 0 1 (ep1930 rfl) (ep1933 rfl) rfl rfl)))

noncomputable def ep1934 := @ep1915 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4)) Bool.false 5684970038060464601 62500000000 0 1 Bool.true 116588384891293 15625000 0 1 qz796)

noncomputable def ep1935 := @Enclosure.Complex.IsNear.of_eq qz248 (Complex.mk (Enclosure.sfrac Bool.false 9 2) qz61) Bool.false 9 2 0 1 Bool.false 97714 1000 0 1 (BSN.s_add_nat_mk qz61 Bool.false 97714 1000 4 (@Eq.refl Real qz61))

noncomputable abbrev qz797 := (ep1935 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9 2) qz61 Bool.false 9 2 0 1 Bool.false 97714 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 9 2) qz375))

noncomputable def ep1936 := ep1934 (@Enclosure.Complex.IsNear.re_isNear qz248 Bool.false 9 2 0 1 Bool.false 97714 1000 0 1 qz797)

noncomputable def ep1937 := @Enclosure.Real.IsNear.mulLit_tf (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.im qz248) 116588384891293 15625000 0 1 97714 1000 0 1 5696158720633902101 7812500000

noncomputable def ep1938 := @ep1937 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4)) Bool.false 5684970038060464601 62500000000 0 1 Bool.true 116588384891293 15625000 0 1 qz796)

noncomputable def ep1939 := ep1938 (@Enclosure.Complex.IsNear.im_isNear qz248 Bool.false 9 2 0 1 Bool.false 97714 1000 0 1 qz797)

noncomputable def ep1940 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4)) qz248 Bool.false 5692130794907464601 5000000000 0 1 Bool.false 276701285685498482011057 31250000000000 0 1 (@ep1913 ep1914 5692130794907464601 5000000000 0 1 (ep1936 rfl) (ep1939 rfl) rfl rfl)

noncomputable def ep1941 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.im qz248)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.re qz248)) 277750581149520119011057 31250000000000 0 1 1049295464021637 31250000 0 1

noncomputable def ep1942 := nat_lit 8646915177671827562845531250000

noncomputable def ep1943 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.im qz248) 5684970038060464601 62500000000 0 1 97714 1000 0 1 277750581149520119011057 31250000000000

noncomputable def ep1944 := @ep1943 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4)) Bool.false 5684970038060464601 62500000000 0 1 Bool.true 116588384891293 15625000 0 1 qz796)

noncomputable def ep1945 := ep1944 (@Enclosure.Complex.IsNear.im_isNear qz248 Bool.false 9 2 0 1 Bool.false 97714 1000 0 1 qz797)

noncomputable def ep1946 := @Enclosure.Real.IsNear.mulLit_tf (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.re qz248) 116588384891293 15625000 0 1 9 2 0 1 1049295464021637 31250000

noncomputable def ep1947 := @ep1946 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4)) Bool.false 5684970038060464601 62500000000 0 1 Bool.true 116588384891293 15625000 0 1 qz796)

noncomputable def ep1948 := ep1947 (@Enclosure.Complex.IsNear.re_isNear qz248 Bool.false 9 2 0 1 Bool.false 97714 1000 0 1 qz797)

noncomputable abbrev qz798 := (ep1912 (BSN.ascPochhammer_succ_eval_c 4 5 qz64 rfl) (ep1940 (@ep1941 ep1942 276701285685498482011057 31250000000000 0 1 (ep1945 rfl) (ep1948 rfl) rfl rfl)))

noncomputable def ep1949 := @ep1911 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) Bool.false 1 30240 0 1 Bool.false 0 1 0 1 ep1739) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)) Bool.false 5692130794907464601 5000000000 0 1 Bool.false 276701285685498482011057 31250000000000 0 1 qz798)

noncomputable def ep1950 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) 0 1 0 1 276701285685498482011057 31250000000000 0 1 0 1 0

noncomputable def ep1951 := @ep1950 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) Bool.false 1 30240 0 1 Bool.false 0 1 0 1 ep1739) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)) Bool.false 5692130794907464601 5000000000 0 1 Bool.false 276701285685498482011057 31250000000000 0 1 qz798)

noncomputable def ep1952 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)))) 276701285685498482011057 945000000000000000 0 1 0 1 0 1 276701285685498482011057

noncomputable def ep1953 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) 1 30240 0 1 276701285685498482011057 31250000000000 0 1 276701285685498482011057 945000000000000000 0

noncomputable def ep1954 := @ep1953 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) Bool.false 1 30240 0 1 Bool.false 0 1 0 1 ep1739) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)) Bool.false 5692130794907464601 5000000000 0 1 Bool.false 276701285685498482011057 31250000000000 0 1 qz798)

noncomputable def ep1955 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) 0 1 0 1 5692130794907464601 5000000000 0 1 0 1 0

noncomputable def ep1956 := @ep1955 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) Bool.false 1 30240 0 1 Bool.false 0 1 0 1 ep1739) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)) Bool.false 5692130794907464601 5000000000 0 1 Bool.false 276701285685498482011057 31250000000000 0 1 qz798)

noncomputable def ep1957 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)) Bool.false 5692130794907464601 151200000000000 0 1 Bool.false 276701285685498482011057 945000000000000000 0 1 (@ep1910 5692130794907464601 151200000000000 0 1 (ep1949 rfl) (ep1951 rfl) rfl rfl) (@ep1952 276701285685498482011057 945000000000000000 0 1 (ep1954 rfl) (ep1956 rfl) rfl rfl)

noncomputable def ep1958 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) Bool.false 5692130794907464601 151200000000000 0 1 Bool.false 276701285685498482011057 945000000000000000 0 1 ep1957

noncomputable def ep1959 := nat_lit 20015547365098052969975927

noncomputable def ep1960 := nat_lit 7790317981596670401806598144000000000000

noncomputable def ep1961 := @Enclosure.Complex.IsNear.re_isNear qz244 Bool.false 11818801372108469849 ep1906 ep1907 ep1908 Bool.true 146676123919104800651 ep1654 ep1959 ep1960

noncomputable abbrev qz799 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2384185791015625)))

noncomputable def ep1962 := @Enclosure.Complex.IsNear.of_eq qz244 (Complex.mk (@HMul.hMul Real Real Real qz0 qz799 (Real.cos qz403)) (@HMul.hMul Real Real Real qz0 qz799 qz964)) Bool.false 11818801372108469849 ep1906 ep1907 ep1908 Bool.true 146676123919104800651 ep1654 ep1959

noncomputable def ep1963 := nat_lit 4483636619378688000000000000

noncomputable abbrev qz800 := (Real.sqrt (@Nat.cast Real Real.instNatCast 2384185791015625))

noncomputable abbrev qz801 := (@Nat.cast Real Real.instNatCast 2384185791015625)

noncomputable def ep1964 := @Enclosure.Real.IsNear.inv_image qz800 6871947673600000000001 140737488355328 1 140737488355328 1441151 1441152 70368744177664 (@Enclosure.Real.IsNear.of_eq qz800 (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz801 qz268)) Bool.false 6871947673600000000001 140737488355328 1 140737488355328 (BSN.sqrt_natCast_div_one 2384185791015625) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz801 qz268)) Bool.false 6871947673600000000001 140737488355328 1 140737488355328 6871947673600000000001 140737488355328 1 140737488355328 (BSN.sqrt_enclosure 2384185791015625 1 3435973836800000000000 3435973836800000000001 70368744177664 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep1965 := nat_lit 8160819742908617307239682670592

noncomputable def ep1966 := nat_lit 31858154296875000000000000000

noncomputable def ep1967 := nat_lit 2477182803477023050167337757039390524570575

noncomputable def ep1968 := nat_lit 40979650847029476010101634771649910523320

noncomputable def ep1969 := nat_lit 7959977060167793366219589075

noncomputable def ep1970 := BSN.log_dyadic_bound 9 41 11 10 ep1967 70368744177664 31858154296875 ep1968 ep1969 31404662954650 50 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP 9) (BSN.artanhQ 41) 0 10 ep1968 ep1967 ep1969 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1971 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz404 97714 1000 0 1 3624131991357079 1125899906842624 1154491 32622750000000000000 177064216701732808703 562949953421312000 56404966787 16311375000000000000000 qz375 (BSN.isNear_log_sfrac 25 1 3624131991357079 1125899906842624 1154491 32622750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 qz624 qz268)) Bool.false ep1965 ep1794 1127432617187500 ep1966 3624131991357079 1125899906842624 1154491 32622750000000000000 (BSN.log_rat_reduce_isNear 25 1 4 50 32 31404662954650 70368744177664 24973259072661432 36028797018963968 31858154296875 1000000000000000 rfl rfl rfl rfl (ep1970 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1972 := nat_lit 311696574315539865212020685673585566011487228507158206505331720192

noncomputable def ep1973 := nat_lit 122930447571395263187776240566788730727844474775025919782007257381375708434322031222913238048683577989660286419485138449269706460352289391944628473649029929424333037313779714745955078681735822625896294570560032935936

noncomputable def ep1974 := nat_lit 157475844566194586710377858717712139937779852880999049736115734363710475742484286820110103296463932017452925328428721010605290554933102646532775267477867748133619504176774923002822752918037699780581068853165128522137600

noncomputable def ep1975 := nat_lit 2161885694472464739849814584559681289867135566109066167285396337586250516742479509353305330630907238492497663141758672123428614221171211909284385068295127732079346074517530970655745736013802447240946323456

noncomputable def ep1976 := nat_lit 745772504168768552942234825685819523246402458536028946835375449720622011387784855152618452001655374222360456883577001184696452647602705453479029810845293008781725872548659236835883681545902412844512923932605532672000

noncomputable def ep1977 := nat_lit 14330301855523707390644385143311804734337966612170913525986531827097653292566070100630019399978217813588216204887013611965081440498912340834482549340485965080159374880086517993256870515541430680032877265638026695514521600

noncomputable def ep1978 := BSN.cos_dyadic_bound_f 106635725323162166 288230376151711744 4 3 140737488355328 63778531551362 ep1973 ep1974 ep1975 ep1976 ep1977 ep1975 131215088735456 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 106635725323162166) (BSN.cosEvenQ 288230376151711744) 0 3 ep1973 ep1974 ep1975 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 106635725323162166) (BSN.cosOddQ 288230376151711744) 0 3 ep1976 ep1977 ep1975 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz802 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 22133027087716601) (@Nat.cast Real Real.instNatCast 70368744177664))

noncomputable def ep1979 := @Enclosure.Real.IsNear.cos_image qz403 qz802 Bool.false 22133027087716601 70368744177664 487 140737488355328 Bool.false 131215088735456 140737488355328 1 31858154296875 (@Enclosure.Real.IsNear.recentre' qz403 Bool.false 177064216701732808703 562949953421312000 56404966787 16311375000000000000000 22133027087716601 70368744177664 487 140737488355328 (ep1971 rfl) rfl) (Enclosure.sfrac_false_div 22133027087716601 70368744177664) (BSN.cos_reduce0 qz802 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1972) (@Nat.cast Real Real.instNatCast ep1801)) ep1636 ep1614 Bool.false 131215088735456 140737488355328 50 ep1637 63716308593750 31858154296875 (BSN.sin_reduce_arg_pos_rat_q0 22133027087716601 70368744177664 ep1636 ep1614 50 ep1972 ep1801 rfl rfl rfl rfl) EMRow28.d184 (@BSN.cos_arg_round Bool.false 131215088735456 140737488355328 ep1972 ep1801 106635725323162166 288230376151711744 63778531551362 63716308593750 (ep1978 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1980 := nat_lit 2698698581302181336294915001857385226933775316483373579525186889760783648062394443392028724340033233895200784736360173076246795257034482704640

noncomputable def ep1981 := nat_lit 17285463164347339796810211223561770462494679168857799243526777305738142342878975650470835551142577613746307323689819874821474630958559157897134080

noncomputable def ep1982 := nat_lit 16719443518100583791617473036789993234325605068948602183067200999907503840955726144691996629162502353574177432157821475422655448687370496

noncomputable def ep1983 := nat_lit 7067993024311445622684352862289187458170841682667295362924335935809957323252433423422507633848401730436001030403196007298257588992935294198016

noncomputable def ep1984 := nat_lit 316900158013034562941520539098632458479069118095726319464657583938532609619447886925298651770947256252015634267646697705060368234240251228114124800

noncomputable def ep1985 := BSN.sin_dyadic_bound_f 106635725323162166 288230376151711744 3 2 140737488355328 63778531551362 ep1980 ep1981 ep1982 ep1983 ep1984 ep1982 50888516550517 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 106635725323162166) (BSN.sinEvenQ 288230376151711744) 0 2 ep1980 ep1981 ep1982 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 106635725323162166) (BSN.sinOddQ 288230376151711744) 0 2 ep1983 ep1984 ep1982 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1986 := @Enclosure.Real.IsNear.sin_image qz403 qz802 Bool.false 22133027087716601 70368744177664 487 140737488355328 Bool.false 50888516550517 140737488355328 1 31858154296875 (@Enclosure.Real.IsNear.recentre' qz403 Bool.false 177064216701732808703 562949953421312000 56404966787 16311375000000000000000 22133027087716601 70368744177664 487 140737488355328 (ep1971 rfl) rfl) (Enclosure.sfrac_false_div 22133027087716601 70368744177664) (BSN.sin_reduce0 qz802 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1972) (@Nat.cast Real Real.instNatCast ep1801)) ep1636 ep1614 Bool.false 50888516550517 140737488355328 50 ep1637 63716308593750 31858154296875 (BSN.sin_reduce_arg_pos_rat_q0 22133027087716601 70368744177664 ep1636 ep1614 50 ep1972 ep1801 rfl rfl rfl rfl) EMRow28.d184 (@BSN.sin_arg_round Bool.false 50888516550517 140737488355328 ep1972 ep1801 106635725323162166 288230376151711744 63778531551362 63716308593750 (ep1985 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1987 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz799 (Real.cos qz403)) (@HMul.hMul Real Real Real qz0 qz799 qz964) Bool.false 11818801372108469849 ep1906 ep1907 ep1908 Bool.true 146676123919104800651 ep1654 ep1959 ep1960 (@Enclosure.Real.IsNear.mulLit_ff qz799 (Real.cos qz403) 2882303 140737488355328 1 140737488355328 4100471522983 4398046511104 15655658630933453 ep1963 11818801372108469849 ep1906 ep1907 ep1908 (@Enclosure.Real.IsNear.recentre' qz799 Bool.false 2882303 140737488355328 1 140737488355328 2882303 140737488355328 1 140737488355328 (ep1964 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' (Real.cos qz403) Bool.false 131215088735456 140737488355328 15655658630933453 ep1963 4100471522983 4398046511104 15655658630933453 ep1963 (ep1979 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz799 qz964 2882303 140737488355328 1 140737488355328 50888516550517 140737488355328 15655658630933453 ep1963 146676123919104800651 ep1654 ep1959 ep1960 (@Enclosure.Real.IsNear.recentre' qz799 Bool.false 2882303 140737488355328 1 140737488355328 2882303 140737488355328 1 140737488355328 (ep1964 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg (Real.sin qz403) Bool.false 50888516550517 140737488355328 15655658630933453 ep1963 (@Enclosure.Real.IsNear.recentre' (Real.sin qz403) Bool.false 50888516550517 140737488355328 15655658630933453 ep1963 50888516550517 140737488355328 15655658630933453 ep1963 (ep1986 rfl rfl) rfl)) rfl)

noncomputable def ep1988 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.im qz244) 276701285685498482011057 945000000000000000 0 1 146676123919104800651 ep1654 ep1959 ep1960 ep1901

noncomputable def ep1989 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) Bool.false 5692130794907464601 151200000000000 0 1 Bool.false 276701285685498482011057 945000000000000000 0 1 ep1957

noncomputable def ep1990 := @Enclosure.Complex.IsNear.im_isNear qz244 Bool.false 11818801372108469849 ep1906 ep1907 ep1908 Bool.true 146676123919104800651 ep1654 ep1959 ep1960

noncomputable def ep1991 := nat_lit 834899681837599790967265341093944255251

noncomputable def ep1992 := nat_lit 2994824543039191961035961322700800000000000

noncomputable def ep1993 := nat_lit 113931113533803588843308437479672107574660127

noncomputable def ep1994 := nat_lit 1177896078817416564753157639372800000000000000000000000

noncomputable def ep1995 := nat_lit 3270277534923947166372609672603672569120393

noncomputable def ep1996 := nat_lit 584926668562342179889836195840000000000000000

noncomputable def ep1997 := nat_lit 446257222120070344482769407109466521570790159077

noncomputable def ep1998 := @Enclosure.Real.IsNear.addLit_tf_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.im qz244)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.re qz244)) ep1991 ep1992 ep1993 ep1994 ep1995 ep1996 ep1997

noncomputable def ep1999 := nat_lit 230057827894026672803351101440000000000000000000000000000

noncomputable def ep2000 := nat_lit 9305552334658918532091649151122949021275791569644580440879460661523277414400000000000

noncomputable def ep2001 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.im qz244) 5692130794907464601 151200000000000 0 1 146676123919104800651 ep1654 ep1959 ep1960 ep1991

noncomputable def ep2002 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.re qz244) 276701285685498482011057 945000000000000000 0 1 11818801372108469849 ep1906 ep1907 ep1908 ep1995

noncomputable abbrev qz803 := (@ep1962 ep1960 (BSN.cpow_neg_s_sub_mk qz61 97714 1000 25 5 2384185791015625 (@Eq.refl Real qz61) rfl EMRow28.d186) ep1987)

noncomputable def ep2003 := ep1896 (@ep1903 ep1904 ep1905 ep1886 ep1887 ep1888 ep1889 (@ep1909 ep1898 ep1899 ep1900 ep1958 (ep1961 qz803) rfl) (@ep1988 ep1887 ep1902 ep1904 ep1989 (ep1990 qz803) rfl) rfl rfl) (@ep1998 ep1999 ep2000 ep1891 ep1892 ep1893 ep1895 (@ep2001 ep1992 ep1993 ep1994 ep1958 (ep1990 qz803) rfl) (@ep2002 ep1996 ep1997 ep1999 ep1989 (ep1961 qz803) rfl) rfl rfl)

noncomputable def ep2004 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244)) ep1891 ep1892 ep1893 ep1895 ep1891 ep1892 ep1893

noncomputable def ep2005 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244) Bool.false ep1886 ep1887 ep1888 ep1889 Bool.false ep1891 ep1892 ep1893

noncomputable def ep2006 := @ep1857 170550438564251187 1585267068834414592 97877920297 2305843009213693952 (@ep1858 1 2883584 (ep1859 (@ep1860 524288 1 524288 (ep1861 (@ep1862 9578275796 2394568949 250000 0 1 (ep1866 rfl) (ep1869 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 11) rfl) (@ep1870 159571 70368744177664 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244)) (@ep1871 319142 140737488355328 3323833461 549755813888 159571 70368744177664 (@ep1876 425450523437 425450842579 70368744177664 (@ep1881 ep1882 ep1883 ep1884 ep1885 ep1872 ep1873 ep1874 ep1875 (@ep1890 ep1889 ep1877 ep1878 ep1879 ep1875 (@ep1894 ep1895 ep2003) (@ep1894 ep1895 ep2003) rfl) (@ep2004 ep1895 ep1880 ep1882 ep1883 ep1884 (@ep2005 ep1895 ep2003) (@ep2005 ep1895 ep2003) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow28.d187 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz590 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 2 4) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz64 2 25))) (@HMul.hMul Real Real Real qz0 qz791 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244)))) Bool.false 14266824687600640410867 132403090856119141138432 170564633190287977 192586313972536932564992 := ep1855 (ep1856 ep2006) rfl rfl

noncomputable def EMRow28.d188 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J))

noncomputable abbrev qz250 := (@Enclosure.dec_le_dec qz259 qz371 95415 1000 97714 1000 (@Eq.refl Real qz259) (@Eq.refl Real qz371) rfl rfl rfl)

noncomputable abbrev qz804 := (EMRow28.d3 qz11 qz61 qz250 24 25 2 2)

noncomputable def ep2007 := @Zeta.Certificates.ZIntervalEM.Certificate.mk qz804 (@Enclosure.dec_nonneg qz11 95415 1000 (@Eq.refl Real qz11)) (@Enclosure.pos_of_ble 2 rfl) (@Enclosure.pos_of_ble 24 rfl)

noncomputable abbrev qz805 := (Zeta.Certificates.ZIntervalEM.fstVal (EMRow28.d3 qz11 qz61 qz250 24 25 2 2))

noncomputable def ep2008 := @Enclosure.Real.IsNear.pos_val qz805 ep345 ep346

noncomputable def ep2009 := @Enclosure.Real.IsNear.of_eq qz805 (hardyZApproximantEM 2 24 qz11) Bool.false

noncomputable abbrev qz806 := (Zeta.Certificates.ZIntervalEM.sndVal (EMRow28.d3 qz11 qz61 qz250 24 25 2 2))

noncomputable def ep2010 := BSN.mul_neg_of_pos_neg_r qz805 qz806 (@ep2008 ep347 ep348 (@ep2009 ep345 ep346 ep347 ep348 (@Eq.refl Real (hardyZApproximantEM 2 24 qz11)) EMRow28.d14) rfl rfl rfl)

noncomputable def ep2011 := @Enclosure.Real.IsNear.neg_val qz806 ep1144 ep1145

noncomputable def ep2012 := @Enclosure.Real.IsNear.of_eq qz806 (hardyZApproximantEM 2 25 qz61) Bool.true

noncomputable def ep2013 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz805) (BSN.hardyZErrorBoundStrong 2 24 qz11)

noncomputable def ep2014 := @Enclosure.norm_gt_of_isNear qz805 (BSN.hardyZErrorBoundStrong 2 24 qz11) Bool.false

noncomputable def ep2015 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 2 24 qz11) (@HAdd.hAdd Real Real Real qz590 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 2 4) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz14 2 24))) (@HMul.hMul Real Real Real qz0 qz234 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236)))) Bool.false ep1638 ep1639 15295608221978490251 ep1639 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz590 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 2 4) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz14 2 24))) (@HMul.hMul Real Real Real qz0 qz234 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236)))))

noncomputable def ep2016 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz806) (BSN.hardyZErrorBoundStrong 2 25 qz61)

noncomputable def ep2017 := @Enclosure.norm_gt_of_isNear qz806 (BSN.hardyZErrorBoundStrong 2 25 qz61) Bool.true

noncomputable def ep2018 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 2 25 qz61) (@HAdd.hAdd Real Real Real qz590 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 2 4) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz64 2 25))) (@HMul.hMul Real Real Real qz0 qz791 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244)))) Bool.false 14266824687600640410867 132403090856119141138432 170564633190287977 192586313972536932564992 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz590 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 2 4) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz64 2 25))) (@HMul.hMul Real Real Real qz0 qz791 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244)))))

noncomputable def ep2019 := @List.cons EMRow28.d0 (@PSigma.mk Zeta.Certificates.ZIntervalEM Zeta.Certificates.ZIntervalEM.Certificate qz804 (ep2007 (@Enclosure.pos_of_ble 2 rfl) (@Enclosure.pos_of_ble 25 rfl) (ep2010 (@ep2011 ep1146 ep1147 (@ep2012 ep1144 ep1145 ep1146 ep1147 (@Eq.refl Real (hardyZApproximantEM 2 25 qz61)) EMRow28.d22) rfl rfl rfl)) (ep2013 (hardyZErrorBoundEM 2 24 qz11) (BSN.hardyZErrorBoundEM_le_strong 2 24 qz11 rfl) (@ep2014 Bool.false ep345 ep346 ep347 ep348 ep1638 ep1639 15295608221978490251 ep1639 (@ep2009 ep345 ep346 ep347 ep348 (@Eq.refl Real (hardyZApproximantEM 2 24 qz11)) EMRow28.d14) (ep2015 EMRow28.d185) rfl rfl rfl rfl rfl)) (ep2016 (hardyZErrorBoundEM 2 25 qz61) (BSN.hardyZErrorBoundEM_le_strong 2 25 qz61 rfl) (@ep2017 Bool.false ep1144 ep1145 ep1146 ep1147 14266824687600640410867 132403090856119141138432 170564633190287977 192586313972536932564992 (@ep2012 ep1144 ep1145 ep1146 ep1147 (@Eq.refl Real (hardyZApproximantEM 2 25 qz61)) EMRow28.d22) (ep2018 EMRow28.d187) rfl rfl rfl rfl rfl)))) (@List.nil EMRow28.d0)

noncomputable abbrev qz807 := (@NonemptyInterval Real Real.instLE)

noncomputable abbrev qz808 := (Zeta.Certificates.CertifiedZeroIntervals.intervals (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep2019 (@List.IsChain.singleton EMRow28.d1 EMRow28.d188 (EMRow28.d2 qz11 qz61 qz250))))

noncomputable def ep2020 := And (@Eq (Option Real) (@Option.map qz807 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz807 qz808)) (@Option.some Real qz11))

noncomputable def ep2021 := ep2020 (@Eq (Option Real) (@Option.map qz807 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz807 qz808)) (@Option.some Real qz61))

noncomputable def ep2022 := @And.intro (@Eq Nat (@List.length qz807 qz808) 1) ep2021

noncomputable def ep2023 := @And.intro (@Eq (Option Real) (@Option.map qz807 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz807 qz808)) (@Option.some Real qz11))

noncomputable def ep2024 := @ep2023 (@Eq (Option Real) (@Option.map qz807 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz807 qz808)) (@Option.some Real qz61))

noncomputable abbrev qz809 := (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep2019 (@List.IsChain.singleton EMRow28.d1 EMRow28.d188 (EMRow28.d2 qz11 qz61 qz250)))

theorem EMRow28.d189 : Zeta.Certificates.BatchSpec 1 95415 1000 97714 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz807 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 1) (And (@Eq (Option Real) (@Option.map qz807 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz807 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz11)) (@Eq (Option Real) (@Option.map qz807 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz807 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz61)))) qz809 (ep2022 (@Eq.refl Nat 1) (ep2024 (@Eq.refl (Option Real) (@Option.some Real qz11)) (@Eq.refl (Option Real) (@Option.some Real qz61))))

theorem solution : Zeta.Certificates.BatchSpec 1 95415 1000 97714 1000 := EMRow28.d189
#print axioms solution
#check solution
