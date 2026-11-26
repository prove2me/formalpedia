-- Prove2me | solution 1 for RHHeight1000.em_main_0034_0034
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T09:36:15.596066+00:00
-- url     : https://prove2.me/submissions/c22ddc8b-5c80-4dec-bcff-6c7b082c14aa

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

noncomputable def EMRow34.d0 := @PSigma Zeta.Certificates.ZIntervalEM fun (I : Zeta.Certificates.ZIntervalEM) => Zeta.Certificates.ZIntervalEM.Certificate I

noncomputable def EMRow34.d1 := @NonemptyInterval Real Real.instLE

noncomputable def EMRow34.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h

noncomputable def EMRow34.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) (fc sc fb sb : Nat) => Zeta.Certificates.ZIntervalEM.mk (EMRow34.d2 a b h) fc sc fb sb

noncomputable def ep0 := nat_lit 26986075409044028275299783

noncomputable def ep1 := nat_lit 4294967296000000000000000

noncomputable def ep2 := nat_lit 26986075409044045455168967

noncomputable abbrev qz0 := (@instHMul Real Real.instMul)

noncomputable abbrev qz249 := (Enclosure.sfrac Bool.false 2 1)

noncomputable def ep3 := @BSN.isNear_log_image_fff (@HMul.hMul Real Real Real qz0 qz249 Real.pi) 884279719003555 140737488355328 1 500000000000000 ep0 ep1 ep2 ep1 4138529546116343 2251799813685248 125000000068337 34168500000000000000 4138529546116343 2251799813685248 125000000068337 34168500000000000000 963576 524288

noncomputable abbrev qz250 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 2 1) Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) BSN.pi_near_15 rfl)

noncomputable def ep4 := @ep3 3 524288 qz250 rfl rfl rfl rfl

noncomputable def ep5 := nat_lit 53972150818088056550599566

noncomputable def ep6 := nat_lit 34359738368000000000000000

noncomputable def ep7 := nat_lit 9806206225044028275299783

noncomputable def ep8 := nat_lit 44165944593044028275299783

noncomputable def ep9 := nat_lit 13681445815609410487519367394620474863599256634174726093703677122907123617368241606644861540940610176751640793056574796245399519365549113997355475306157239709119582688278313060810592403844863400465080549957745

noncomputable def ep10 := nat_lit 231714499556395493334623298703961145503103241611736774613091488581016477543539392410113701224645713379230392133956226737605624599560350113120270717249177907454870984269546186598262646369758174842349131395304

noncomputable def ep11 := nat_lit 8978369550011295664474073352761810093897501552430546263638635096022803738134167562509900960712119243631997923545019968443113540909076206607473711060286601587364321108377403290080403445693385008949995305

noncomputable def ep12 := BSN.log_dyadic_bound ep7 ep8 5 4 ep9 1048576 273348 ep10 ep11 473518 ep5 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep7) (BSN.artanhQ ep8) 0 4 ep10 ep9 ep11 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz1 := (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))

noncomputable def ep13 := ep4 rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep1 4138529546116343 2251799813685248 125000000068337 34168500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep0) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 69433004117575847641088 37778931862957161709568 1000000000546696 273348000000000000000 4138529546116343 2251799813685248 125000000068337 34168500000000000000 (BSN.log_rat_reduce_isNear ep0 ep1 2 ep5 ep6 473518 1048576 24973259072661432 36028797018963968 273348 1000000000000000 rfl rfl rfl rfl (ep12 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep14 := nat_lit 53972150818088090910337934

noncomputable def ep15 := nat_lit 9806206225044045455168967

noncomputable def ep16 := nat_lit 44165944593044045455168967

noncomputable def ep17 := nat_lit 13681445815609453062485491347592146866046743284321690683909457683007658987562290830600045658905080811372395010565947827677605470036294121079488508864180301737865471494204890974265645509835068840465080549957745

noncomputable def ep18 := nat_lit 231714499556396865510889920206523150079811393376960301632499817942333196803513131357563499488546302200815366867712007119763002650772307103678175657719139104636874731038771518520299266622696414842349131395304

noncomputable def ep19 := nat_lit 8978369550011421500876706511871067098718760264493934208903156435737864998391937547068187824077011975074541700434630537294838404525415248443919841847024664017658842168336182958576672102333385008949995305

noncomputable def ep20 := BSN.log_dyadic_bound ep15 ep16 5 4 ep17 1048576 273348 ep18 ep19 473518 ep14 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep15) (BSN.artanhQ ep16) 0 4 ep18 ep17 ep19 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep21 := ep13 (BSN.isNear_log_sfrac ep2 ep1 4138529546116343 2251799813685248 125000000068337 34168500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep2) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 69433004117575847641088 37778931862957161709568 1000000000546696 273348000000000000000 4138529546116343 2251799813685248 125000000068337 34168500000000000000 (BSN.log_rat_reduce_isNear ep2 ep1 2 ep14 ep6 473518 1048576 24973259072661432 36028797018963968 273348 1000000000000000 rfl rfl rfl rfl (ep20 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable abbrev qz251 := (Real.log (@HMul.hMul Real Real Real qz0 (2 : Real) Real.pi))

theorem EMRow34.d4 : Enclosure.Real.IsNear qz251 Bool.false 120447 65536 3 524288 := @Enclosure.Real.IsNear.of_eq qz251 (Real.log (@HMul.hMul Real Real Real qz0 qz249 Real.pi)) Bool.false 120447 65536 3 524288 BSN.log_two_pi_eq (@Enclosure.Real.IsNear.recentre' (Real.log (@HMul.hMul Real Real Real qz0 qz249 Real.pi)) Bool.false 963576 524288 3 524288 120447 65536 3 524288 (ep21 rfl rfl rfl rfl rfl rfl rfl rfl) rfl)

noncomputable abbrev qz541 := (@instHPow Complex Nat (@NPow.toPow Complex (@Monoid.toNPow Complex (@Semiring.toMonoid Complex Complex.instSemiring))))

noncomputable abbrev qz811 := (@instHAdd Complex Complex.instAdd)

noncomputable abbrev qz812 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (4 : Complex))

noncomputable abbrev qz813 := (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid))

noncomputable abbrev qz542 := (@HAdd.hAdd Complex Complex Complex qz811 (@HAdd.hAdd Complex Complex Complex qz811 qz812 (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I (@HDiv.hDiv Complex Complex Complex qz813 (↑(Enclosure.sfrac Bool.false 108936 1000)) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 4))

noncomputable abbrev qz252 := (@HPow.hPow Complex Nat Complex qz541 qz542 3)

noncomputable abbrev qz2 := qz252

noncomputable def ep22 := Enclosure.Complex.IsNear qz2 Bool.true 37749462931 1000000 0 1 Bool.true 9915135227577 62500000 0 1

noncomputable abbrev qz543 := (@instHMul Complex Complex.instMul)

noncomputable abbrev qz253 := qz543

noncomputable abbrev qz3 := qz253

noncomputable abbrev qz254 := qz541

noncomputable abbrev qz255 := qz542

noncomputable abbrev qz4 := (@HPow.hPow Complex Nat Complex qz254 qz255 2)

noncomputable abbrev qz5 := qz255

noncomputable def ep23 := @Enclosure.Complex.IsNear.of_eq qz2 (@HMul.hMul Complex Complex Complex qz3 qz4 qz5) Bool.true 37749462931 1000000 0 1 Bool.true 9915135227577 62500000

noncomputable def ep24 := @Enclosure.Complex.IsNear.mul qz4 qz5 Bool.true 37749462931 1000000 0 1 Bool.true 9915135227577 62500000 0

noncomputable def ep25 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re qz4) (Complex.re qz5)) (@HMul.hMul Real Real Real qz0 (Complex.im qz4) (Complex.im qz5)) 12531977227 1000000 0 1 3152185713 125000

noncomputable def ep26 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re qz4) (Complex.re qz5) 737175131 250000 0 1 17000 4000 0 1

noncomputable def ep27 := @Enclosure.Complex.IsNear.re_isNear qz4 Bool.true 737175131 250000 0 1 Bool.false 231489 500 0 1

noncomputable abbrev qz256 := (@HPow.hPow Complex Nat Complex qz541 qz542 1)

noncomputable abbrev qz6 := qz256

noncomputable def ep28 := @Enclosure.Complex.IsNear.of_eq qz4 (@HMul.hMul Complex Complex Complex qz3 qz6 qz5) Bool.true 737175131 250000 0 1 Bool.false 231489 500

noncomputable def ep29 := @Enclosure.Complex.IsNear.mul qz6 qz5 Bool.true 737175131 250000 0 1 Bool.false 231489 500 0

noncomputable abbrev qz7 := (Complex.re qz256)

noncomputable abbrev qz8 := (Complex.im qz256)

noncomputable def ep30 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz7 (Complex.re qz5)) (@HMul.hMul Real Real Real qz0 qz8 (Complex.im qz5)) 289 16 0 1 185422689 62500

noncomputable def ep31 := @Enclosure.Real.IsNear.mulLit_ff qz7 (Complex.re qz5) 17000 4000 0 1 17000 4000 0 1

noncomputable def ep32 := @Enclosure.Complex.IsNear.re_isNear qz6 Bool.false 17000 4000 0 1 Bool.false 217872 4000 0 1

noncomputable def ep33 := @Enclosure.Complex.IsNear.of_eq qz6 qz5 Bool.false 17000 4000 0 1 Bool.false 217872 4000 0

noncomputable abbrev qz257 := (Enclosure.sfrac Bool.false 108936 1000)

noncomputable abbrev qz9 := qz257

noncomputable abbrev qz258 := (Enclosure.sfrac Bool.false 217872 4000)

noncomputable abbrev qz544 := (Complex.mk (Enclosure.sfrac Bool.false 17000 4000) qz258)

noncomputable def ep34 := @Enclosure.Complex.IsNear.of_eq qz5 qz544 Bool.false 17000 4000 0 1 Bool.false 217872 4000 0 1 (BSN.w_shift_mk qz9 Bool.false 108936 1000 4 (@Eq.refl Real qz9) rfl)

noncomputable abbrev qz545 := (Enclosure.sfrac Bool.false 17000 4000)

noncomputable abbrev qz10 := (@ep33 1 (BSN.pow_one_c qz255) (ep34 (@Enclosure.Complex.IsNear.mk qz545 qz258 Bool.false 17000 4000 0 1 Bool.false 217872 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 17000 4000) (Enclosure.Real.IsNear.const Bool.false 217872 4000))))

noncomputable abbrev qz11 := (ep34 (@Enclosure.Complex.IsNear.mk qz545 qz258 Bool.false 17000 4000 0 1 Bool.false 217872 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 17000 4000) (Enclosure.Real.IsNear.const Bool.false 217872 4000)))

noncomputable abbrev qz814 := (@Enclosure.Complex.IsNear.re_isNear qz5 Bool.false 17000 4000 0 1 Bool.false 217872 4000 0 1 qz11)

noncomputable def ep35 := @ep31 289 16 0 1 (ep32 qz10) qz814

noncomputable def ep36 := @Enclosure.Real.IsNear.mulLit_ff qz8 (Complex.im qz5) 217872 4000 0 1 217872 4000 0 1

noncomputable def ep37 := @Enclosure.Complex.IsNear.im_isNear qz6 Bool.false 17000 4000 0 1 Bool.false 217872 4000 0 1

noncomputable abbrev qz815 := (@Enclosure.Complex.IsNear.im_isNear qz5 Bool.false 17000 4000 0 1 Bool.false 217872 4000 0 1 qz11)

noncomputable def ep38 := @ep36 185422689 62500 0 1 (ep37 qz10) qz815

noncomputable def ep39 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz7 (Complex.im qz5)) (@HMul.hMul Real Real Real qz0 qz8 (Complex.re qz5)) 231489 1000 0 1 231489 1000

noncomputable def ep40 := @Enclosure.Real.IsNear.mulLit_ff qz7 (Complex.im qz5) 17000 4000 0 1 217872 4000 0 1

noncomputable def ep41 := @ep40 231489 1000 0 1 (ep32 qz10) qz815

noncomputable def ep42 := @Enclosure.Real.IsNear.mulLit_ff qz8 (Complex.re qz5) 217872 4000 0 1 17000 4000 0 1

noncomputable def ep43 := @ep42 231489 1000 0 1 (ep37 qz10) qz814

noncomputable abbrev qz546 := (@ep28 0 1 (BSN.pow_succ_c qz5 1 2 rfl) (@ep29 1 (@ep30 0 1 2948700524 737175131 250000 0 1 (ep35 rfl) (ep38 rfl) rfl rfl) (@ep39 0 1 462978000 231489 500 0 1 (ep41 rfl) (ep43 rfl) rfl rfl)))

noncomputable def ep44 := @ep26 12531977227 1000000 0 1 (ep27 qz546) qz814

noncomputable def ep45 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz4) (Complex.im qz5) 231489 500 0 1 217872 4000 0 1

noncomputable def ep46 := @Enclosure.Complex.IsNear.im_isNear qz4 Bool.true 737175131 250000 0 1 Bool.false 231489 500 0 1

noncomputable def ep47 := @ep45 3152185713 125000 0 1 (ep46 qz546) qz815

noncomputable def ep48 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re qz4) (Complex.im qz5)) (@HMul.hMul Real Real Real qz0 (Complex.im qz4) (Complex.re qz5)) 10038113758827 62500000 0 1 3935313 2000

noncomputable def ep49 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re qz4) (Complex.im qz5) 737175131 250000 0 1 217872 4000 0 1

noncomputable def ep50 := @ep49 10038113758827 62500000 0 1 (ep27 qz546) qz815

noncomputable def ep51 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz4) (Complex.re qz5) 231489 500 0 1 17000 4000 0 1

noncomputable def ep52 := @ep51 3935313 2000 0 1 (ep46 qz546) qz814

theorem EMRow34.d5 : ep22 := @ep23 0 1 (BSN.pow_succ_c qz5 2 3 rfl) (@ep24 1 (@ep25 0 1 4718682866375000 37749462931 1000000 0 1 (ep44 rfl) (ep47 rfl) rfl rfl) (@ep48 0 1 19830270455154000 9915135227577 62500000 0 1 (ep50 rfl) (ep52 rfl) rfl rfl))

noncomputable def ep53 := nat_lit 8589934592000000000000000

noncomputable def ep54 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 ep0 ep53 ep2 ep53 1200336 1048576 1 273348 1200336 1048576 1 273348 600168 524288 2 524288 BSN.pi_near_15 rfl rfl rfl

noncomputable def ep55 := nat_lit 17179869184000000000000000

noncomputable def ep56 := nat_lit 18396140817044028275299783

noncomputable def ep57 := nat_lit 35576010001044028275299783

noncomputable def ep58 := nat_lit 145019262663961446558303139663424756232419223153299357158415217874016130572233056993847515999529612750616182853355499335896178729185698845314776375864537073527142908641610750276034469165612529925303649396973267518946591078603565291376312767403717761600170009932259137778521478520425507632472584532570900560707662248426541531715360699177249902784721815296292248142738824858695953661559845440650653128788875447728828657762006237171740033404723254477174341920697506370253193455781322964835857351124092897592956162654178130575

noncomputable def ep59 := nat_lit 15500762873619990602332184736899274490522931101512051618692838888825382235673431503644115344741331161500627469184702974962114537943617674254904297224139410345221262767191485292268260077615645253784097850065864022184521411511133693085443040736512010941548648374196772723338837137976260321103066698629790037694560548409922339907589559883712609967105556007429010014773911317423638534096849366294542840133852248768895750397896505791271178551667935288585787166713880920071720072716082683081155281219708172458141800988558163320

noncomputable def ep60 := nat_lit 12900190794487083783367107939442176642390171280542213571554777169279725287102813254708993369099729304728646904879886535518616983985412662170766446331701281703998252143668221340329975389245922410714088123244705567402747658401492589451585970559635763980329972215329212888079422466283203384882259392047898400615815810081169907384366653346471604103896809335921621947903075223769953790093549808584241881353287841076643853121427928248525828402335494512605306631304432120211393210317325496757155861061354331245840675149075

noncomputable def ep61 := BSN.log_dyadic_bound ep56 ep57 11 10 ep58 1048576 273348 ep59 ep60 1200336 ep5 ep55 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep56) (BSN.artanhQ ep57) 0 10 ep59 ep58 ep60 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep62 := nat_lit 18396140817044045455168967

noncomputable def ep63 := nat_lit 35576010001044045455168967

noncomputable def ep64 := nat_lit 145019262663962847171784895425483977818796535899227200426399035286881207006285364467913811844950531107314785650583974625982406238691319033447632878979985852280879486690814033867010958364699188952871572448188560932645032521756218245629809291975913196623825614492380080480004685076434733043183791438169545293975334857826316990371107134320667652578346815517853870648072772035977941843998949310557583393428557296298890786965786350523173236912472938174255438182435383147950274229549088258679583524155427309880956162654178130575

noncomputable def ep65 := nat_lit 15500762873620157189619721156942591192100275120160672416764593300158228469749443299607348495591439275767946573253526107895503597951484257520435868240203420954375895980141891044871083424251900562230440202302413072793440172565998181227591194192658878334739610458454844032013325963992941389843551995646587189684848765634635122388286241104146031552341815777883628509454807838726994150833304950745987647656768534710890974432620160470644835720379148964170536679305861738540146791997074363921127776563807649880221800988558163320

noncomputable def ep66 := nat_lit 12900190794487324729109480814509220959173684627296055849229843377126536688487849343376525559792931631054411655715865486295286288812423905434305314401904993536755333953308594664509631000767632482919425633906965368325056855874260596615770736441041599390097968820060635361729170158825410327022636428624381203910573184452046894301676992229743752846881064485858738985580654099214803581683226335297196686880535448467637789069028262446657986458573827723305156755787640135484017403116612632808333639900906331245840675149075

noncomputable def ep67 := BSN.log_dyadic_bound ep62 ep63 11 10 ep64 1048576 273348 ep65 ep66 1200336 ep14 ep55 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep62) (BSN.artanhQ ep63) 0 10 ep65 ep64 ep66 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep68 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 600168 524288 2 524288 75021 65536 1 262144 (ep54 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep53 1200336 1048576 1 273348 Bool.false (BSN.logfrac_isNear ep5 ep55 1 ep0 ep53 1200336 1048576 273348 rfl rfl rfl (ep61 rfl))) (BSN.isNear_log_sfrac ep2 ep53 1200336 1048576 1 273348 Bool.false (BSN.logfrac_isNear ep14 ep55 1 ep2 ep53 1200336 1048576 273348 rfl rfl rfl (ep67 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl

theorem EMRow34.d6 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 75021 65536 1 262144 := ep68

noncomputable abbrev qz547 := qz811

noncomputable abbrev qz548 := (@HDiv.hDiv Complex Complex Complex qz813 (1 : Complex) (2 : Complex))

noncomputable abbrev qz259 := (@HAdd.hAdd Complex Complex Complex qz547 qz548 (@HMul.hMul Complex Complex Complex qz543 Complex.I ↑(Enclosure.sfrac Bool.false 108936 1000)))

noncomputable abbrev qz12 := qz259

noncomputable abbrev qz260 := qz547

noncomputable abbrev qz13 := qz260

noncomputable abbrev qz14 := (@instHPow Complex Complex Complex.instPow)

noncomputable abbrev qz15 := (@Neg.neg Complex Complex.instNeg qz259)

noncomputable abbrev qz816 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 8) qz15)

noncomputable def ep69 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 9) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 8) qz816) Bool.false 4167506520365 1099511627776 68156169946871 25045775369109504 Bool.true 440662229 137438953472 17022438093437 6261443842277376

noncomputable def ep70 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 8) qz816 Bool.false 3799919578055 1099511627776 61000485896369 25045775369109504 Bool.false 960515577 8589934592 15237220866485 6261443842277376 Bool.false

noncomputable def ep71 := nat_lit 2291110938986807421829120

noncomputable abbrev qz817 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 7) qz15)

noncomputable def ep72 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 8) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 7) qz817) Bool.false 3799919578055 1099511627776 61000485896369 25045775369109504 Bool.false 960515577 8589934592 15237220866485 6261443842277376

noncomputable def ep73 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 7) qz817 Bool.false 3832306464405 1099511627776 160119002465759 75137326107328512 Bool.true 145683306297 549755813888 39974585248589 18784331526832128 Bool.true

noncomputable def ep74 := nat_lit 2089027880342572069027840

noncomputable abbrev qz818 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 6) qz15)

noncomputable def ep75 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 7) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 6) qz818) Bool.false 3832306464405 1099511627776 160119002465759 75137326107328512 Bool.true 145683306297 549755813888 39974585248589 18784331526832128

noncomputable def ep76 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 6) qz818 Bool.false 106885167975 34359738368 11278620724507 6261443842277376 Bool.true 56578662447 549755813888 5631671071529 3130721921138688 Bool.false

noncomputable abbrev qz16 := (@Nat.cast Complex Complex.instNatCast 5)

noncomputable def ep77 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 6) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 5) (@HPow.hPow Complex Complex Complex qz14 qz16 qz15)) Bool.false 106885167975 34359738368 11278620724507 6261443842277376 Bool.true 56578662447 549755813888 5631671071529 3130721921138688

noncomputable def ep78 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 5) (@HPow.hPow Complex Complex Complex qz14 qz16 qz15) Bool.false 3015515041013 1099511627776 108216250063631 75137326107328512 Bool.true 98071611725 274877906944 1688300348291 1174020720427008 Bool.false

noncomputable def ep79 := nat_lit 3760687520809709941555200

noncomputable abbrev qz549 := (@Nat.cast Complex Complex.instNatCast 4)

noncomputable abbrev qz261 := qz549

noncomputable abbrev qz17 := qz261

noncomputable def ep80 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 5) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 4) (@HPow.hPow Complex Complex Complex qz14 qz17 qz15)) Bool.false 3015515041013 1099511627776 108216250063631 75137326107328512 Bool.true 98071611725 274877906944 1688300348291 1174020720427008

noncomputable def ep81 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 4) (@HPow.hPow Complex Complex Complex qz14 qz17 qz15) Bool.false 2479108622721 1099511627776 77883194278723 75137326107328512 Bool.true 16992418405 68719476736 19443097227097 18784331526832128 Bool.false

noncomputable abbrev qz550 := (@Nat.cast Complex Complex.instNatCast 3)

noncomputable def ep82 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 4) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 3) (@HPow.hPow Complex Complex Complex qz14 qz550 qz15)) Bool.false 2479108622721 1099511627776 77883194278723 75137326107328512 Bool.true 16992418405 68719476736 19443097227097 18784331526832128

noncomputable def ep83 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 3) (@HPow.hPow Complex Complex Complex qz14 qz550 qz15) Bool.false 1872258253141 1099511627776 4763312106467 8348591789703168 Bool.true 2674428185 34359738368 297267192095 521786986856448 Bool.false

noncomputable abbrev qz551 := (@Nat.cast Complex Complex.instNatCast 2)

noncomputable def ep84 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 3) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 2) (@HPow.hPow Complex Complex Complex qz14 qz551 qz15)) Bool.false 1872258253141 1099511627776 4763312106467 8348591789703168 Bool.true 2674428185 34359738368 297267192095 521786986856448

noncomputable def ep85 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 2) (@HPow.hPow Complex Complex Complex qz14 qz551 qz15) Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz262 := (Enclosure.sfrac Bool.false 0 1)

noncomputable def ep86 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz262) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz12)

noncomputable abbrev qz263 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2)))

noncomputable abbrev qz264 := (@HMul.hMul Real Real Real qz0 qz9 (Real.log (Enclosure.sfrac Bool.false 2 1)))

noncomputable def ep87 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz14 qz551 qz15) (Complex.mk (@HMul.hMul Real Real Real qz0 qz263 (Real.cos qz264)) (@HMul.hMul Real Real Real qz0 qz263 (@Neg.neg Real Real.instNeg (Real.sin qz264)))) Bool.false 772746625365 1099511627776 4763312106467 8348591789703168 Bool.true 2674428185 34359738368 297267192095 521786986856448 (BSN.cpow_neg_s_mk qz9 108936 1000 2 (@Eq.refl Real qz9) rfl)

noncomputable abbrev qz265 := (@Nat.cast Real Real.instNatCast 1)

noncomputable def ep88 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 2)) 1482911 1048576 1 1048576 370727 370728 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 2)) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2) qz265)) Bool.false 1482911 1048576 1 1048576 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2) qz265)) Bool.false 1482911 1048576 1 1048576 1482911 1048576 1 1048576 (BSN.sqrt_enclosure 2 1 741455 741456 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep89 := BSN.log_dyadic_bound 1 3 6 5 613814355 524288 136674 24381081 945 363408 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 1) (BSN.artanhQ 3) 0 5 24381081 613814355 945 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep90 := nat_lit 3148042166480788516562434671905761

noncomputable def ep91 := nat_lit 510423550381407695195061911147652317184

noncomputable def ep92 := nat_lit 7656353255721115427925928667214784757760

noncomputable abbrev qz266 := (BSN.cosEvenQ 2147483648)

noncomputable abbrev qz267 := (BSN.cosOddQ 2147483648)

noncomputable def ep93 := BSN.cos_dyadic_bound_f 236870041 2147483648 2 1 1048576 273615 ep90 ep91 ep90 ep90 ep92 ep90 1042203 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 236870041) qz266 0 1 ep90 ep91 ep90 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 236870041) qz267 0 1 ep90 ep92 ep90 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz268 := (@Nat.cast Real Real.instNatCast 1048576)

noncomputable abbrev qz269 := (Real.log (Enclosure.sfrac Bool.false 2 1))

noncomputable abbrev qz270 := (Enclosure.Real.IsNear.const Bool.false 108936 1000)

noncomputable abbrev qz271 := (@Nat.cast Real Real.instNatCast 151115727451828646838272)

noncomputable abbrev qz552 := (BSN.isNear_log_sfrac 2 1 363408 524288 1 136674 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 363408 524288 136674 rfl rfl rfl (ep89 rfl)))

noncomputable abbrev qz819 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 79176427) qz268)

noncomputable def ep94 := @Enclosure.Real.IsNear.cos_image qz264 qz819 Bool.false 79176427 1048576 837 1048576 Bool.false 1042203 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz264 Bool.false 309282921 4096000 1513 1898250 79176427 1048576 837 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz9 qz269 108936 1000 0 1 363408 524288 1 136674 309282921 4096000 1513 1898250 qz270 qz552 rfl) rfl) (Enclosure.sfrac_false_div 79176427 1048576) (BSN.cos_reduce0 qz819 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16668247370257613717504) qz271) 226375608064910080 72057594037927936 Bool.false 1042203 1048576 12 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q0 79176427 1048576 226375608064910080 72057594037927936 12 16668247370257613717504 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1042203 1048576 16668247370257613717504 151115727451828646838272 236870041 2147483648 273615 273348 (ep93 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz272 := (BSN.sinEvenQ 2147483648)

noncomputable abbrev qz273 := (BSN.sinOddQ 2147483648)

noncomputable def ep95 := BSN.sin_dyadic_bound_f 236870041 2147483648 1 0 1048576 273615 0 1 1 0 1 1 115424 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 236870041) qz272 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 236870041) qz273 0 0 rfl) rfl rfl

noncomputable def ep96 := @Enclosure.Real.IsNear.sin_image qz264 qz819 Bool.false 79176427 1048576 837 1048576 Bool.false 115424 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz264 Bool.false 309282921 4096000 1513 1898250 79176427 1048576 837 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz9 qz269 108936 1000 0 1 363408 524288 1 136674 309282921 4096000 1513 1898250 qz270 qz552 rfl) rfl) (Enclosure.sfrac_false_div 79176427 1048576) (BSN.sin_reduce0 qz819 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16668247370257613717504) qz271) 226375608064910080 72057594037927936 Bool.false 115424 1048576 12 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q0 79176427 1048576 226375608064910080 72057594037927936 12 16668247370257613717504 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 115424 1048576 16668247370257613717504 151115727451828646838272 236870041 2147483648 273615 273348 (ep95 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz553 := (@Enclosure.Real.IsNear.recentre' qz263 Bool.false 741455 1048576 1 1048576 741455 1048576 1 1048576 (ep88 rfl rfl) rfl)

noncomputable def ep97 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz263 (Real.cos qz264)) (@HMul.hMul Real Real Real qz0 qz263 (@Neg.neg Real Real.instNeg (Real.sin qz264))) Bool.false 772746625365 1099511627776 4763312106467 8348591789703168 Bool.true 2674428185 34359738368 297267192095 521786986856448 (@Enclosure.Real.IsNear.mulLit_ff qz263 (Real.cos qz264) 741455 1048576 1 1048576 1042203 1048576 57722357 71656538112 772746625365 1099511627776 4763312106467 8348591789703168 qz553 (@Enclosure.Real.IsNear.recentre' (Real.cos qz264) Bool.false 1042203 1048576 115444714 143313076224 1042203 1048576 57722357 71656538112 (ep94 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz263 (@Neg.neg Real Real.instNeg (Real.sin qz264)) 741455 1048576 1 1048576 3607 32768 57722357 71656538112 2674428185 34359738368 297267192095 521786986856448 qz553 (@Enclosure.Real.IsNear.neg (Real.sin qz264) Bool.false 3607 32768 57722357 71656538112 (@Enclosure.Real.IsNear.recentre' (Real.sin qz264) Bool.false 115424 1048576 115444714 143313076224 3607 32768 57722357 71656538112 (ep96 rfl rfl) rfl)) rfl)

noncomputable abbrev qz274 := (Enclosure.Real.IsNear.const Bool.false 0 1)

noncomputable def ep98 := @ep85 772746625365 1099511627776 4763312106467 8348591789703168 Bool.true 2674428185 34359738368 297267192095 521786986856448 Bool.false 1872258253141 1872258253141 1099511627776 4763312106467 8348591789703168 Bool.true 2674428185 2674428185 34359738368 297267192095 521786986856448 (ep86 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz262 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz274)) (ep87 ep97) rfl rfl

noncomputable abbrev qz275 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 3)))

noncomputable abbrev qz276 := (@HMul.hMul Real Real Real qz0 qz9 (Real.log (Enclosure.sfrac Bool.false 3 1)))

noncomputable def ep99 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz14 qz550 qz15) (Complex.mk (@HMul.hMul Real Real Real qz0 qz275 (Real.cos qz276)) (@HMul.hMul Real Real Real qz0 qz275 (@Neg.neg Real Real.instNeg (Real.sin qz276)))) Bool.false 151712592395 274877906944 4376673165065 9392165763416064 Bool.true 11643562035 68719476736 8741478311677 18784331526832128 (BSN.cpow_neg_s_mk qz9 108936 1000 3 (@Eq.refl Real qz9) rfl)

noncomputable def ep100 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 3)) 1816187 1048576 1 1048576 302697 302698 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 3)) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3) qz265)) Bool.false 1816187 1048576 1 1048576 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3) qz265)) Bool.false 1816187 1048576 1 1048576 1816187 1048576 1 1048576 (BSN.sqrt_enclosure 3 1 908093 908094 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep101 := BSN.log_dyadic_bound 1 2 10 9 171633298636800 524288 136674 16925142283965 34459425 575989 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP 1) (BSN.artanhQ 2) 0 9 16925142283965 171633298636800 34459425 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep102 := nat_lit 167398774219988792747397998913152016

noncomputable def ep103 := BSN.cos_dyadic_bound_f 639643614 2147483648 2 1 1048576 273615 ep102 ep91 ep102 ep102 ep92 ep102 1002404 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 639643614) qz266 0 1 ep102 ep91 ep102 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 639643614) qz267 0 1 ep102 ep92 ep102 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz277 := (Real.log (Enclosure.sfrac Bool.false 3 1))

noncomputable abbrev qz554 := (BSN.isNear_log_sfrac 3 1 575989 524288 1 136674 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 575989 524288 136674 rfl rfl rfl (ep101 rfl)))

noncomputable abbrev qz820 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 125491875) qz268)

noncomputable def ep104 := @Enclosure.Real.IsNear.cos_image qz276 qz820 Bool.false 125491875 1048576 837 1048576 Bool.false 1002404 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz276 Bool.false 7843242213 65536000 1513 1898250 125491875 1048576 837 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz9 qz277 108936 1000 0 1 575989 524288 1 136674 7843242213 65536000 1513 1898250 qz270 qz554 rfl) rfl) (Enclosure.sfrac_false_div 125491875 1048576) (BSN.cos_reduce0 qz820 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 45010917844188051537920) qz271) 226375608064910080 72057594037927936 Bool.false 1002404 1048576 19 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q0 125491875 1048576 226375608064910080 72057594037927936 19 45010917844188051537920 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1002404 1048576 45010917844188051537920 151115727451828646838272 639643614 2147483648 273615 273348 (ep103 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep105 := nat_lit 2552117751907038475975309555738261585920

noncomputable def ep106 := nat_lit 17864824263349269331827166890167831101440

noncomputable def ep107 := BSN.sin_dyadic_bound_f 639643614 2147483648 2 1 1048576 273615 ep102 ep105 ep102 ep102 ep106 ep102 307728 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 639643614) qz272 0 1 ep102 ep105 ep102 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 639643614) qz273 0 1 ep102 ep106 ep102 rfl rfl rfl rfl) rfl rfl

noncomputable def ep108 := @Enclosure.Real.IsNear.sin_image qz276 qz820 Bool.false 125491875 1048576 837 1048576 Bool.false 307728 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz276 Bool.false 7843242213 65536000 1513 1898250 125491875 1048576 837 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz9 qz277 108936 1000 0 1 575989 524288 1 136674 7843242213 65536000 1513 1898250 qz270 qz554 rfl) rfl) (Enclosure.sfrac_false_div 125491875 1048576) (BSN.sin_reduce0 qz820 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 45010917844188051537920) qz271) 226375608064910080 72057594037927936 Bool.false 307728 1048576 19 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q0 125491875 1048576 226375608064910080 72057594037927936 19 45010917844188051537920 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 307728 1048576 45010917844188051537920 151115727451828646838272 639643614 2147483648 273615 273348 (ep107 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz555 := (@Enclosure.Real.IsNear.recentre' qz275 Bool.false 605395 1048576 1 1048576 605395 1048576 1 1048576 (ep100 rfl rfl) rfl)

noncomputable def ep109 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz275 (Real.cos qz276)) (@HMul.hMul Real Real Real qz0 qz275 (@Neg.neg Real Real.instNeg (Real.sin qz276))) Bool.false 151712592395 274877906944 4376673165065 9392165763416064 Bool.true 11643562035 68719476736 8741478311677 18784331526832128 (@Enclosure.Real.IsNear.mulLit_ff qz275 (Real.cos qz276) 605395 1048576 1 1048576 250601 262144 57722357 71656538112 151712592395 274877906944 4376673165065 9392165763416064 qz555 (@Enclosure.Real.IsNear.recentre' (Real.cos qz276) Bool.false 1002404 1048576 115444714 143313076224 250601 262144 57722357 71656538112 (ep104 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz275 (@Neg.neg Real Real.instNeg (Real.sin qz276)) 605395 1048576 1 1048576 19233 65536 57722357 71656538112 11643562035 68719476736 8741478311677 18784331526832128 qz555 (@Enclosure.Real.IsNear.neg (Real.sin qz276) Bool.false 19233 65536 57722357 71656538112 (@Enclosure.Real.IsNear.recentre' (Real.sin qz276) Bool.false 307728 1048576 115444714 143313076224 19233 65536 57722357 71656538112 (ep108 rfl rfl) rfl)) rfl)

noncomputable def ep110 := @ep83 151712592395 274877906944 4376673165065 9392165763416064 Bool.true 11643562035 68719476736 8741478311677 18784331526832128 Bool.false 681452189300371042074624 2479108622721 1099511627776 77883194278723 75137326107328512 Bool.true 583855050635387863040 16992418405 68719476736 19443097227097 18784331526832128 (ep84 (BSN.head_sum_c_succ qz12 2 3 rfl rfl) (ep98 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep99 ep109) rfl rfl

noncomputable abbrev qz278 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 4)))

noncomputable abbrev qz279 := (@HMul.hMul Real Real Real qz0 qz9 (Real.log (Enclosure.sfrac Bool.false 4 1)))

noncomputable def ep111 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz14 qz17 qz15) (Complex.mk (@HMul.hMul Real Real Real qz0 qz278 (Real.cos qz279)) (@HMul.hMul Real Real Real qz0 qz278 (@Neg.neg Real Real.instNeg (Real.sin qz279)))) Bool.false 134101604573 274877906944 7583263946227 18784331526832128 Bool.true 30101938105 274877906944 7569708345559 18784331526832128 (BSN.cpow_neg_s_mk qz9 108936 1000 4 (@Eq.refl Real qz9) rfl)

noncomputable def ep112 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 4)) 2097153 1048576 1 1048576 262143 262144 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 4)) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4) qz265)) Bool.false 2097153 1048576 1 1048576 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4) qz265)) Bool.false 2097153 1048576 1 1048576 2097153 1048576 1 1048576 (BSN.sqrt_enclosure 4 1 1048576 1048577 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep113 := nat_lit 318077276165597140789031982421875

noncomputable def ep114 := nat_lit 49379992292270016474244603430625

noncomputable def ep115 := nat_lit 20095619060363156210525625

noncomputable def ep116 := BSN.log_dyadic_bound 3 5 14 13 ep113 524288 136674 ep114 ep115 726817 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base13 (BSN.artanhP 3) (BSN.artanhQ 5) 0 13 ep114 ep113 ep115 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep117 := nat_lit 50559691708812276839022130879700625

noncomputable def ep118 := BSN.cos_dyadic_bound_f 474188595 2147483648 2 1 1048576 273615 ep117 ep91 ep117 ep117 ep92 ep117 1023116 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 474188595) qz266 0 1 ep117 ep91 ep117 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 474188595) qz267 0 1 ep117 ep92 ep117 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz280 := (Real.log (Enclosure.sfrac Bool.false 4 1))

noncomputable abbrev qz556 := (BSN.isNear_log_sfrac 4 1 726817 524288 1 136674 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 726817 524288 136674 rfl rfl rfl (ep116 rfl)))

noncomputable abbrev qz821 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 158353073) qz268)

noncomputable def ep119 := @Enclosure.Real.IsNear.cos_image qz279 qz821 Bool.false 158353073 1048576 837 1048576 Bool.false 1023116 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz279 Bool.false 9897067089 65536000 1513 1898250 158353073 1048576 837 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz9 qz280 108936 1000 0 1 726817 524288 1 136674 9897067089 65536000 1513 1898250 qz270 qz556 rfl) rfl) (Enclosure.sfrac_false_div 158353073 1048576) (BSN.cos_reduce0 qz821 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 33368055966703839870976) qz271) 226375608064910080 72057594037927936 Bool.false 1023116 1048576 24 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q0 158353073 1048576 226375608064910080 72057594037927936 24 33368055966703839870976 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1023116 1048576 33368055966703839870976 151115727451828646838272 474188595 2147483648 273615 273348 (ep118 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep120 := BSN.sin_dyadic_bound_f 474188595 2147483648 2 1 1048576 273615 ep117 ep105 ep117 ep117 ep106 ep117 229660 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 474188595) qz272 0 1 ep117 ep105 ep117 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 474188595) qz273 0 1 ep117 ep106 ep117 rfl rfl rfl rfl) rfl rfl

noncomputable def ep121 := @Enclosure.Real.IsNear.sin_image qz279 qz821 Bool.false 158353073 1048576 837 1048576 Bool.false 229660 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz279 Bool.false 9897067089 65536000 1513 1898250 158353073 1048576 837 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz9 qz280 108936 1000 0 1 726817 524288 1 136674 9897067089 65536000 1513 1898250 qz270 qz556 rfl) rfl) (Enclosure.sfrac_false_div 158353073 1048576) (BSN.sin_reduce0 qz821 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 33368055966703839870976) qz271) 226375608064910080 72057594037927936 Bool.false 229660 1048576 24 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q0 158353073 1048576 226375608064910080 72057594037927936 24 33368055966703839870976 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 229660 1048576 33368055966703839870976 151115727451828646838272 474188595 2147483648 273615 273348 (ep120 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz557 := (@Enclosure.Real.IsNear.recentre' qz278 Bool.false 524287 1048576 1 1048576 524287 1048576 1 1048576 (ep112 rfl rfl) rfl)

noncomputable def ep122 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz278 (Real.cos qz279)) (@HMul.hMul Real Real Real qz0 qz278 (@Neg.neg Real Real.instNeg (Real.sin qz279))) Bool.false 134101604573 274877906944 7583263946227 18784331526832128 Bool.true 30101938105 274877906944 7569708345559 18784331526832128 (@Enclosure.Real.IsNear.mulLit_ff qz278 (Real.cos qz279) 524287 1048576 1 1048576 255779 262144 57722357 71656538112 134101604573 274877906944 7583263946227 18784331526832128 qz557 (@Enclosure.Real.IsNear.recentre' (Real.cos qz279) Bool.false 1023116 1048576 115444714 143313076224 255779 262144 57722357 71656538112 (ep119 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz278 (@Neg.neg Real Real.instNeg (Real.sin qz279)) 524287 1048576 1 1048576 57415 262144 57722357 71656538112 30101938105 274877906944 7569708345559 18784331526832128 qz557 (@Enclosure.Real.IsNear.neg (Real.sin qz279) Bool.false 57415 262144 57722357 71656538112 (@Enclosure.Real.IsNear.recentre' (Real.sin qz279) Bool.false 229660 1048576 115444714 143313076224 57415 262144 57722357 71656538112 (ep121 rfl rfl) rfl)) rfl)

noncomputable def ep123 := @ep81 134101604573 274877906944 7583263946227 18784331526832128 Bool.true 30101938105 274877906944 7569708345559 18784331526832128 Bool.false 828898462831803757494272 3015515041013 1099511627776 108216250063631 75137326107328512 Bool.true 6739429840398162329600 98071611725 274877906944 1688300348291 1174020720427008 (ep82 (BSN.head_sum_c_succ qz12 3 4 rfl rfl) (ep110 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep111 ep122) rfl rfl

noncomputable abbrev qz281 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 5)))

noncomputable abbrev qz282 := (@HMul.hMul Real Real Real qz0 qz9 (Real.log (Enclosure.sfrac Bool.false 5 1)))

noncomputable def ep124 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz14 qz16 qz15) (Complex.mk (@HMul.hMul Real Real Real qz0 qz281 (Real.cos qz282)) (@HMul.hMul Real Real Real qz0 qz281 (@Neg.neg Real Real.instNeg (Real.sin qz282)))) Bool.false 404810334187 1099511627776 27127198630453 75137326107328512 Bool.false 139564561003 549755813888 3388610428259 9392165763416064 (BSN.cpow_neg_s_mk qz9 108936 1000 5 (@Eq.refl Real qz9) rfl)

noncomputable abbrev qz283 := (@Nat.cast Real Real.instNatCast 5)

noncomputable def ep125 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz283) 2344687 1048576 1 1048576 234468 234469 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz283) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz283 qz265)) Bool.false 2344687 1048576 1 1048576 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz283 qz265)) Bool.false 2344687 1048576 1 1048576 2344687 1048576 1 1048576 (BSN.sqrt_enclosure 5 1 1172343 1172344 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep126 := nat_lit 11734546589655452485523914939250625

noncomputable def ep127 := nat_lit 2429970938528035899633153341031900

noncomputable def ep128 := nat_lit 824199001261152424427520000

noncomputable def ep129 := BSN.log_dyadic_bound 2 3 17 16 ep126 524288 136674 ep127 ep128 843808 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base16 (BSN.artanhP 2) (BSN.artanhQ 3) 0 16 ep127 ep126 ep128 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep130 := nat_lit 1196982326169923094106407407473719205883269567514456348791564277174795143445025

noncomputable def ep131 := nat_lit 164135286493895707012911871249815109382010203263545499525931125331216861264609280

noncomputable def ep132 := nat_lit 346195744122181571761333233201442870637823482162783753127358194498367093281

noncomputable def ep133 := nat_lit 3134393204002172190591072480053605107903720962614360215996652622190513733728801

noncomputable def ep134 := nat_lit 3009146919054754628570050972913277005336853726498334157975403964405642456517836800

noncomputable def ep135 := BSN.sin_dyadic_bound_f 2076898227 2147483648 3 2 1048576 273615 ep130 ep131 ep132 ep133 ep134 ep132 863251 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2076898227) qz272 0 2 ep130 ep131 ep132 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2076898227) qz273 0 2 ep133 ep134 ep132 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz284 := (Real.log (Enclosure.sfrac Bool.false 5 1))

noncomputable abbrev qz558 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 22980267) (@Nat.cast Real Real.instNatCast 131072))

noncomputable abbrev qz559 := (BSN.isNear_log_sfrac 5 1 843808 524288 1 136674 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 843808 524288 136674 rfl rfl rfl (ep129 rfl)))

noncomputable abbrev qz560 := (@Nat.cast Real Real.instNatCast 18889465931478580854784)

noncomputable def ep136 := @Enclosure.Real.IsNear.cos_image qz282 qz558 Bool.false 22980267 131072 837 1048576 Bool.false 863251 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz282 Bool.false 359066673 2048000 1513 1898250 22980267 131072 837 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz9 qz284 108936 1000 0 1 843808 524288 1 136674 359066673 2048000 1513 1898250 qz270 qz559 rfl) rfl) (Enclosure.sfrac_false_div 22980267 131072) (BSN.cos_reduce3 qz558 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 18268590006871957438464) qz560) 226375608064910080 72057594037927936 Bool.false 863251 1048576 27 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q3 22980267 131072 226375608064910080 72057594037927936 27 18268590006871957438464 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 863251 1048576 18268590006871957438464 18889465931478580854784 2076898227 2147483648 273615 273348 (ep135 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep137 := nat_lit 665144045980678244091009152255711311210988792388992542107814535405774353955361

noncomputable def ep138 := nat_lit 18237254054877300779212430138868345486890022584838388836214569481246317918289920

noncomputable def ep139 := nat_lit 1994739746453790369129504790300731047891690730202652058817188889828326327679521

noncomputable def ep140 := nat_lit 820676432469478535064559356249075546910051016317727497629655626656084306323046400

noncomputable def ep141 := BSN.cos_dyadic_bound_f 2076898227 2147483648 3 2 1048576 273615 ep137 ep138 ep132 ep139 ep140 ep132 595238 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2076898227) qz266 0 2 ep137 ep138 ep132 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2076898227) qz267 0 2 ep139 ep140 ep132 rfl rfl rfl rfl) rfl rfl

noncomputable def ep142 := @Enclosure.Real.IsNear.sin_image qz282 qz558 Bool.false 22980267 131072 837 1048576 Bool.true 595238 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz282 Bool.false 359066673 2048000 1513 1898250 22980267 131072 837 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz9 qz284 108936 1000 0 1 843808 524288 1 136674 359066673 2048000 1513 1898250 qz270 qz559 rfl) rfl) (Enclosure.sfrac_false_div 22980267 131072) (BSN.sin_reduce3 qz558 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 18268590006871957438464) qz560) 226375608064910080 72057594037927936 Bool.false 595238 1048576 27 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q3 22980267 131072 226375608064910080 72057594037927936 27 18268590006871957438464 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 595238 1048576 18268590006871957438464 18889465931478580854784 2076898227 2147483648 273615 273348 (ep141 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz561 := (@Enclosure.Real.IsNear.recentre' qz281 Bool.false 468937 1048576 1 1048576 468937 1048576 1 1048576 (ep125 rfl rfl) rfl)

noncomputable def ep143 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz281 (Real.cos qz282)) (@HMul.hMul Real Real Real qz0 qz281 (@Neg.neg Real Real.instNeg (Real.sin qz282))) Bool.false 404810334187 1099511627776 27127198630453 75137326107328512 Bool.false 139564561003 549755813888 3388610428259 9392165763416064 (@Enclosure.Real.IsNear.mulLit_ff qz281 (Real.cos qz282) 468937 1048576 1 1048576 863251 1048576 57722357 71656538112 404810334187 1099511627776 27127198630453 75137326107328512 qz561 (@Enclosure.Real.IsNear.recentre' (Real.cos qz282) Bool.false 863251 1048576 115444714 143313076224 863251 1048576 57722357 71656538112 (ep136 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz281 (@Neg.neg Real Real.instNeg (Real.sin qz282)) 468937 1048576 1 1048576 297619 524288 57722357 71656538112 139564561003 549755813888 3388610428259 9392165763416064 qz561 (@Enclosure.Real.IsNear.neg (Real.sin qz282) Bool.true 297619 524288 57722357 71656538112 (@Enclosure.Real.IsNear.recentre' (Real.sin qz282) Bool.true 595238 1048576 115444714 143313076224 297619 524288 57722357 71656538112 (ep142 rfl rfl) rfl)) rfl)

noncomputable def ep144 := @ep78 404810334187 1099511627776 27127198630453 75137326107328512 Bool.false 139564561003 549755813888 3388610428259 9392165763416064 Bool.false ep79 106885167975 34359738368 11278620724507 6261443842277376 Bool.true 15552224311122453331968 56578662447 549755813888 5631671071529 3130721921138688 (ep80 (BSN.head_sum_c_succ qz12 4 5 rfl rfl) (ep123 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep124 ep143) rfl rfl

noncomputable abbrev qz822 := (@Nat.cast Real Real.instNatCast 6)

noncomputable abbrev qz285 := (@Inv.inv Real Real.instInv (Real.sqrt qz822))

noncomputable abbrev qz286 := (@HMul.hMul Real Real Real qz0 qz9 (Real.log (Enclosure.sfrac Bool.false 6 1)))

noncomputable def ep145 := @Enclosure.Complex.IsNear.of_eq qz818 (Complex.mk (@HMul.hMul Real Real Real qz0 qz285 (Real.cos qz286)) (@HMul.hMul Real Real Real qz0 qz285 (@Neg.neg Real Real.instNeg (Real.sin qz286)))) Bool.false 411981089205 1099511627776 24775553771675 75137326107328512 Bool.true 44552321925 274877906944 6184558819415 18784331526832128 (BSN.cpow_neg_s_mk qz9 108936 1000 6 (@Eq.refl Real qz9) rfl)

noncomputable abbrev qz823 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6) qz265)

noncomputable def ep146 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz822) 2568477 1048576 1 1048576 214039 214040 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz822) (Real.sqrt qz823) Bool.false 2568477 1048576 1 1048576 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz823) Bool.false 2568477 1048576 1 1048576 2568477 1048576 1 1048576 (BSN.sqrt_enclosure 6 1 1284238 1284239 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep147 := BSN.log_dyadic_bound 2 10 4 3 105000000 524288 136674 1434560 960 212580 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 2) (BSN.artanhQ 10) 0 3 1434560 105000000 960 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz287 := (Real.log (Enclosure.sfrac Bool.false 6 1))

noncomputable def ep148 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz287 108936 1000 0 1 4034681531866359 2251799813685248 250000000068337 34168500000000000000 54940258419424210503 281474976710656000 378250000103393881 474562500000000000000 qz270 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 250000000068337 34168500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz823) Bool.false 33845361775666394038272 18889465931478580854784 1000000000273348 136674000000000000000 4034681531866359 2251799813685248 250000000068337 34168500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 212580 524288 24973259072661432 36028797018963968 136674 1000000000000000 rfl rfl rfl rfl (ep147 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep149 := nat_lit 590849831673033457611520765180691361

noncomputable def ep150 := BSN.cos_dyadic_bound_f 876736887 2147483648 2 1 1048576 273615 ep149 ep91 ep149 ep149 ep92 ep149 962395 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 876736887) qz266 0 1 ep149 ep91 ep149 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 876736887) qz267 0 1 ep149 ep92 ep149 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz824 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 204668411) qz268)

noncomputable def ep151 := @Enclosure.Real.IsNear.cos_image qz286 qz824 Bool.false 204668411 1048576 837 1048576 Bool.false 962395 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz286 Bool.false 54940258419424210503 281474976710656000 378250000103393881 474562500000000000000 204668411 1048576 837 1048576 (ep148 rfl) rfl) (Enclosure.sfrac_false_div 204668411 1048576) (BSN.cos_reduce0 qz824 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 61694873769945933545472) qz271) 226375608064910080 72057594037927936 Bool.false 962395 1048576 31 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q0 204668411 1048576 226375608064910080 72057594037927936 31 61694873769945933545472 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 962395 1048576 61694873769945933545472 151115727451828646838272 876736887 2147483648 273615 273348 (ep150 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep152 := BSN.sin_dyadic_bound_f 876736887 2147483648 2 1 1048576 273615 ep149 ep105 ep149 ep149 ep106 ep149 416300 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 876736887) qz272 0 1 ep149 ep105 ep149 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 876736887) qz273 0 1 ep149 ep106 ep149 rfl rfl rfl rfl) rfl rfl

noncomputable def ep153 := @Enclosure.Real.IsNear.sin_image qz286 qz824 Bool.false 204668411 1048576 837 1048576 Bool.false 416300 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz286 Bool.false 54940258419424210503 281474976710656000 378250000103393881 474562500000000000000 204668411 1048576 837 1048576 (ep148 rfl) rfl) (Enclosure.sfrac_false_div 204668411 1048576) (BSN.sin_reduce0 qz824 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 61694873769945933545472) qz271) 226375608064910080 72057594037927936 Bool.false 416300 1048576 31 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q0 204668411 1048576 226375608064910080 72057594037927936 31 61694873769945933545472 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 416300 1048576 61694873769945933545472 151115727451828646838272 876736887 2147483648 273615 273348 (ep152 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz562 := (@Enclosure.Real.IsNear.recentre' qz285 Bool.false 428079 1048576 1 1048576 428079 1048576 1 1048576 (ep146 rfl rfl) rfl)

noncomputable def ep154 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz285 (Real.cos qz286)) (@HMul.hMul Real Real Real qz0 qz285 (@Neg.neg Real Real.instNeg (Real.sin qz286))) Bool.false 411981089205 1099511627776 24775553771675 75137326107328512 Bool.true 44552321925 274877906944 6184558819415 18784331526832128 (@Enclosure.Real.IsNear.mulLit_ff qz285 (Real.cos qz286) 428079 1048576 1 1048576 962395 1048576 57722357 71656538112 411981089205 1099511627776 24775553771675 75137326107328512 qz562 (@Enclosure.Real.IsNear.recentre' (Real.cos qz286) Bool.false 962395 1048576 115444714 143313076224 962395 1048576 57722357 71656538112 (ep151 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz285 (@Neg.neg Real Real.instNeg (Real.sin qz286)) 428079 1048576 1 1048576 104075 262144 57722357 71656538112 44552321925 274877906944 6184558819415 18784331526832128 qz562 (@Enclosure.Real.IsNear.neg (Real.sin qz286) Bool.false 104075 262144 57722357 71656538112 (@Enclosure.Real.IsNear.recentre' (Real.sin qz286) Bool.false 416300 1048576 115444714 143313076224 104075 262144 57722357 71656538112 (ep153 rfl rfl) rfl)) rfl)

noncomputable def ep155 := @ep76 411981089205 1099511627776 24775553771675 75137326107328512 Bool.true 44552321925 274877906944 6184558819415 18784331526832128 Bool.false 131677047462950904791040 3832306464405 1099511627776 160119002465759 75137326107328512 Bool.true 40045122311601015226368 145683306297 549755813888 39974585248589 18784331526832128 (ep77 (BSN.head_sum_c_succ qz12 5 6 rfl rfl) (ep144 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep145 ep154) rfl rfl

noncomputable abbrev qz825 := (@Nat.cast Real Real.instNatCast 7)

noncomputable abbrev qz288 := (@Inv.inv Real Real.instInv (Real.sqrt qz825))

noncomputable abbrev qz289 := (@HMul.hMul Real Real Real qz0 qz9 (Real.log (Enclosure.sfrac Bool.false 7 1)))

noncomputable def ep156 := @Enclosure.Complex.IsNear.of_eq qz817 (Complex.mk (@HMul.hMul Real Real Real qz0 qz288 (Real.cos qz289)) (@HMul.hMul Real Real Real qz0 qz288 (@Neg.neg Real Real.instNeg (Real.sin qz289)))) Bool.true 16193443175 549755813888 5720613805837 18784331526832128 Bool.false 207156303225 549755813888 2868538675433 9392165763416064 (BSN.cpow_neg_s_mk qz9 108936 1000 7 (@Eq.refl Real qz9) rfl)

noncomputable abbrev qz826 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 7) qz265)

noncomputable def ep157 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz825) 2774271 1048576 1 1048576 198162 198163 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz825) (Real.sqrt qz826) Bool.false 2774271 1048576 1 1048576 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz826) Bool.false 2774271 1048576 1 1048576 2774271 1048576 1 1048576 (BSN.sqrt_enclosure 7 1 1387135 1387136 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep158 := BSN.log_dyadic_bound 3 11 5 4 202569142545 524288 136674 5259111624 688905 293399 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 3) (BSN.artanhQ 11) 0 4 5259111624 202569142545 688905 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz290 := (Real.log (Enclosure.sfrac Bool.false 7 1))

noncomputable def ep159 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz290 108936 1000 0 1 4381796493761783 2251799813685248 250000000068337 34168500000000000000 59666922855554199111 281474976710656000 378250000103393881 474562500000000000000 qz270 (BSN.isNear_log_sfrac 7 1 4381796493761783 2251799813685248 250000000068337 34168500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz826) Bool.false 36757173121942042968064 18889465931478580854784 1000000000273348 136674000000000000000 4381796493761783 2251799813685248 250000000068337 34168500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 293399 524288 24973259072661432 36028797018963968 136674 1000000000000000 rfl rfl rfl rfl (ep158 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep160 := nat_lit 3784585842226532083196581668206323802382398941335485709385459565784318994841856

noncomputable def ep161 := nat_lit 11153614257489325940215166793116130232056285811890814679782926059872703774976

noncomputable def ep162 := nat_lit 11331450298164617597709314671032739146683084252382675498796812845233211576975616

noncomputable def ep163 := BSN.cos_dyadic_bound_f 3205730082 2147483648 3 2 1048576 273615 ep160 ep138 ep161 ep162 ep140 ep161 81718 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3205730082) qz266 0 2 ep160 ep138 ep161 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3205730082) qz267 0 2 ep162 ep140 ep161 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz563 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 217067) (@Nat.cast Real Real.instNatCast 1024))

noncomputable def ep164 := @Enclosure.Real.IsNear.cos_image qz289 qz563 Bool.false 217067 1024 837 1048576 Bool.true 81718 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz289 Bool.false 59666922855554199111 281474976710656000 378250000103393881 474562500000000000000 217067 1024 837 1048576 (ep159 rfl) rfl) (Enclosure.sfrac_false_div 217067 1024) (BSN.cos_reduce2 qz563 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 220296093827105030144) (@Nat.cast Real Real.instNatCast 147573952589676412928)) 226375608064910080 72057594037927936 Bool.false 81718 1048576 33 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q2 217067 1024 226375608064910080 72057594037927936 33 220296093827105030144 147573952589676412928 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 81718 1048576 220296093827105030144 147573952589676412928 3205730082 2147483648 273615 273348 (ep163 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep165 := nat_lit 6803331624601766289001674869336889940102673065754361625150000877563876027695360

noncomputable def ep166 := nat_lit 17800191260397262324434514387741095156083671661851695318292258513332262361661696

noncomputable def ep167 := BSN.sin_dyadic_bound_f 3205730082 2147483648 3 2 1048576 273615 ep165 ep131 ep161 ep166 ep134 ep161 1045386 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3205730082) qz272 0 2 ep165 ep131 ep161 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3205730082) qz273 0 2 ep166 ep134 ep161 rfl rfl rfl rfl) rfl rfl

noncomputable def ep168 := @Enclosure.Real.IsNear.sin_image qz289 qz563 Bool.false 217067 1024 837 1048576 Bool.true 1045386 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz289 Bool.false 59666922855554199111 281474976710656000 378250000103393881 474562500000000000000 217067 1024 837 1048576 (ep159 rfl) rfl) (Enclosure.sfrac_false_div 217067 1024) (BSN.sin_reduce2 qz563 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 220296093827105030144) (@Nat.cast Real Real.instNatCast 147573952589676412928)) 226375608064910080 72057594037927936 Bool.false 1045386 1048576 33 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q2 217067 1024 226375608064910080 72057594037927936 33 220296093827105030144 147573952589676412928 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1045386 1048576 220296093827105030144 147573952589676412928 3205730082 2147483648 273615 273348 (ep167 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz564 := (@Enclosure.Real.IsNear.recentre' qz288 Bool.false 396325 1048576 1 1048576 396325 1048576 1 1048576 (ep157 rfl rfl) rfl)

noncomputable def ep169 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz288 (Real.cos qz289)) (@HMul.hMul Real Real Real qz0 qz288 (@Neg.neg Real Real.instNeg (Real.sin qz289))) Bool.true 16193443175 549755813888 5720613805837 18784331526832128 Bool.false 207156303225 549755813888 2868538675433 9392165763416064 (@Enclosure.Real.IsNear.mulLit_ft qz288 (Real.cos qz289) 396325 1048576 1 1048576 40859 524288 57722357 71656538112 16193443175 549755813888 5720613805837 18784331526832128 qz564 (@Enclosure.Real.IsNear.recentre' (Real.cos qz289) Bool.true 81718 1048576 115444714 143313076224 40859 524288 57722357 71656538112 (ep164 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz288 (@Neg.neg Real Real.instNeg (Real.sin qz289)) 396325 1048576 1 1048576 522693 524288 57722357 71656538112 207156303225 549755813888 2868538675433 9392165763416064 qz564 (@Enclosure.Real.IsNear.neg (Real.sin qz289) Bool.true 522693 524288 57722357 71656538112 (@Enclosure.Real.IsNear.recentre' (Real.sin qz289) Bool.true 1045386 1048576 115444714 143313076224 522693 524288 57722357 71656538112 (ep168 rfl rfl) rfl)) rfl)

noncomputable def ep170 := @ep73 16193443175 549755813888 5720613805837 18784331526832128 Bool.false 207156303225 549755813888 2868538675433 9392165763416064 Bool.false ep74 3799919578055 1099511627776 61000485896369 25045775369109504 Bool.false 33795137458287163736064 960515577 8589934592 15237220866485 6261443842277376 (ep75 (BSN.head_sum_c_succ qz12 6 7 rfl rfl) (ep155 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep156 ep169) rfl rfl

noncomputable abbrev qz827 := (@Nat.cast Real Real.instNatCast 8)

noncomputable abbrev qz291 := (@Inv.inv Real Real.instInv (Real.sqrt qz827))

noncomputable abbrev qz292 := (@HMul.hMul Real Real Real qz0 qz9 (Real.log (Enclosure.sfrac Bool.false 8 1)))

noncomputable def ep171 := @Enclosure.Complex.IsNear.of_eq qz816 (Complex.mk (@HMul.hMul Real Real Real qz0 qz291 (Real.cos qz292)) (@HMul.hMul Real Real Real qz0 qz291 (@Neg.neg Real Real.instNeg (Real.sin qz292)))) Bool.false 183793471155 549755813888 1192614008417 4174295894851584 Bool.true 15808911461 137438953472 74384051123 260893493428224 (BSN.cpow_neg_s_mk qz9 108936 1000 8 (@Eq.refl Real qz9) rfl)

noncomputable abbrev qz828 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8) qz265)

noncomputable def ep172 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz827) 2965821 1048576 1 1048576 185363 185364 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz827) (Real.sqrt qz828) Bool.false 2965821 1048576 1 1048576 (BSN.sqrt_natCast_div_one 8) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz828) Bool.false 2965821 1048576 1 1048576 2965821 1048576 1 1048576 (BSN.sqrt_enclosure 8 1 1482910 1482911 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep173 := BSN.log_dyadic_bound 0 16 1 0 1 524288 136674 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz293 := (Real.log (Enclosure.sfrac Bool.false 8 1))

noncomputable def ep174 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz293 108936 1000 0 1 9364972152248037 4503599627370496 500000000205011 68337000000000000000 127522825797161519829 562949953421312000 756500000310181643 949125000000000000000 qz270 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 500000000205011 68337000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz828) Bool.false 39279540158062550581248 18889465931478580854784 1000000000410022 136674000000000000000 9364972152248037 4503599627370496 500000000205011 68337000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 524288 24973259072661432 36028797018963968 136674 1000000000000000 rfl rfl rfl rfl (ep173 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep175 := nat_lit 256437814783419770179653249787322001

noncomputable def ep176 := BSN.cos_dyadic_bound_f 711615693 2147483648 2 1 1048576 273615 ep175 ep91 ep175 ep175 ep92 ep175 991530 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 711615693) qz266 0 1 ep175 ep91 ep175 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 711615693) qz267 0 1 ep175 ep92 ep175 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz565 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 59382443) (@Nat.cast Real Real.instNatCast 262144))

noncomputable abbrev qz566 := (@Nat.cast Real Real.instNatCast 37778931862957161709568)

noncomputable def ep177 := @Enclosure.Real.IsNear.cos_image qz292 qz565 Bool.false 59382443 262144 837 1048576 Bool.false 991530 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz292 Bool.false 127522825797161519829 562949953421312000 756500000310181643 949125000000000000000 59382443 262144 837 1048576 (ep174 rfl) rfl) (Enclosure.sfrac_false_div 59382443 262144) (BSN.cos_reduce0 qz565 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 12518875667029521596416) qz566) 226375608064910080 72057594037927936 Bool.false 991530 1048576 36 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q0 59382443 262144 226375608064910080 72057594037927936 36 12518875667029521596416 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 991530 1048576 12518875667029521596416 37778931862957161709568 711615693 2147483648 273615 273348 (ep176 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep178 := BSN.sin_dyadic_bound_f 711615693 2147483648 2 1 1048576 273615 ep175 ep105 ep175 ep175 ep106 ep175 341144 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 711615693) qz272 0 1 ep175 ep105 ep175 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 711615693) qz273 0 1 ep175 ep106 ep175 rfl rfl rfl rfl) rfl rfl

noncomputable def ep179 := @Enclosure.Real.IsNear.sin_image qz292 qz565 Bool.false 59382443 262144 837 1048576 Bool.false 341144 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz292 Bool.false 127522825797161519829 562949953421312000 756500000310181643 949125000000000000000 59382443 262144 837 1048576 (ep174 rfl) rfl) (Enclosure.sfrac_false_div 59382443 262144) (BSN.sin_reduce0 qz565 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 12518875667029521596416) qz566) 226375608064910080 72057594037927936 Bool.false 341144 1048576 36 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q0 59382443 262144 226375608064910080 72057594037927936 36 12518875667029521596416 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 341144 1048576 12518875667029521596416 37778931862957161709568 711615693 2147483648 273615 273348 (ep178 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz567 := (@Enclosure.Real.IsNear.recentre' qz291 Bool.false 370727 1048576 1 1048576 370727 1048576 1 1048576 (ep172 rfl rfl) rfl)

noncomputable def ep180 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz291 (Real.cos qz292)) (@HMul.hMul Real Real Real qz0 qz291 (@Neg.neg Real Real.instNeg (Real.sin qz292))) Bool.false 183793471155 549755813888 1192614008417 4174295894851584 Bool.true 15808911461 137438953472 74384051123 260893493428224 (@Enclosure.Real.IsNear.mulLit_ff qz291 (Real.cos qz292) 370727 1048576 1 1048576 495765 524288 57722357 71656538112 183793471155 549755813888 1192614008417 4174295894851584 qz567 (@Enclosure.Real.IsNear.recentre' (Real.cos qz292) Bool.false 991530 1048576 115444714 143313076224 495765 524288 57722357 71656538112 (ep177 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz291 (@Neg.neg Real Real.instNeg (Real.sin qz292)) 370727 1048576 1 1048576 42643 131072 57722357 71656538112 15808911461 137438953472 74384051123 260893493428224 qz567 (@Enclosure.Real.IsNear.neg (Real.sin qz292) Bool.false 42643 131072 57722357 71656538112 (@Enclosure.Real.IsNear.recentre' (Real.sin qz292) Bool.false 341144 1048576 115444714 143313076224 42643 131072 57722357 71656538112 (ep179 rfl rfl) rfl)) rfl)

noncomputable def ep181 := @ep70 183793471155 549755813888 1192614008417 4174295894851584 Bool.true 15808911461 137438953472 74384051123 260893493428224 Bool.false ep71 4167506520365 1099511627776 68156169946871 25045775369109504 Bool.true 3785259724274925568 440662229 137438953472 17022438093437 6261443842277376 (ep72 (BSN.head_sum_c_succ qz12 7 8 rfl rfl) (ep170 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep171 ep180) rfl rfl

theorem EMRow34.d7 : Enclosure.Complex.IsNear (BSN.headSumC qz12 9) Bool.false 4167506520365 1099511627776 68156169946871 25045775369109504 Bool.true 440662229 137438953472 17022438093437 6261443842277376 := ep69 (BSN.head_sum_c_succ qz12 8 9 rfl rfl) (ep181 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz829 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 16) qz15)

noncomputable def ep182 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 17) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 16) qz829) Bool.false 2492766653827 549755813888 171820405640045 37568663053664256 Bool.false 151694378923 1099511627776 343265896525459 75137326107328512

noncomputable def ep183 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 16) qz829 Bool.false 296065792283 68719476736 20527779144653 4696082881708032 Bool.false 269229862975 1099511627776 328103687121383 75137326107328512 Bool.false

noncomputable abbrev qz830 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 15) qz15)

noncomputable def ep184 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 16) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 15) qz830) Bool.false 296065792283 68719476736 20527779144653 4696082881708032 Bool.false 269229862975 1099511627776 328103687121383 75137326107328512

noncomputable def ep185 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 15) qz830 Bool.false 2233163689753 549755813888 26062355574925 6261443842277376 Bool.false 183774256699 1099511627776 104151417041719 25045775369109504 Bool.false

noncomputable def ep186 := nat_lit 1302111124807489717010432

noncomputable abbrev qz831 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 14) qz15)

noncomputable def ep187 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 15) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 14) qz831) Bool.false 2233163689753 549755813888 26062355574925 6261443842277376 Bool.false 183774256699 1099511627776 104151417041719 25045775369109504

noncomputable def ep188 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 14) qz831 Bool.false 4456794913861 1099511627776 296569598200937 75137326107328512 Bool.true 109927133133 1099511627776 296206288093961 75137326107328512 Bool.false

noncomputable def ep189 := nat_lit 4910778887221158562758656

noncomputable abbrev qz832 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 13) qz15)

noncomputable def ep190 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 14) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 13) qz832) Bool.false 4456794913861 1099511627776 296569598200937 75137326107328512 Bool.true 109927133133 1099511627776 296206288093961 75137326107328512

noncomputable def ep191 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 13) qz832 Bool.false 4756450208371 1099511627776 93244004364589 25045775369109504 Bool.true 26674486299 549755813888 11642742531659 3130721921138688 Bool.true

noncomputable def ep192 := nat_lit 2450148915201552907501568

noncomputable abbrev qz833 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 12) qz15)

noncomputable def ep193 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 13) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 12) qz833) Bool.false 4756450208371 1099511627776 93244004364589 25045775369109504 Bool.true 26674486299 549755813888 11642742531659 3130721921138688

noncomputable def ep194 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 12) qz833 Bool.false 4480802212291 1099511627776 262197340668901 75137326107328512 Bool.false 104008365549 1099511627776 261917853682843 75137326107328512 Bool.false

noncomputable abbrev qz834 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 11) qz15)

noncomputable def ep195 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 12) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 11) qz834) Bool.false 4480802212291 1099511627776 262197340668901 75137326107328512 Bool.false 104008365549 1099511627776 261917853682843 75137326107328512

noncomputable def ep196 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 11) qz834 Bool.false 2388571087687 549755813888 30485487769499 9392165763416064 Bool.true 44599967673 1099511627776 243636347204935 75137326107328512 Bool.true

noncomputable def ep197 := nat_lit 2463347067089189662097408

noncomputable abbrev qz835 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 10) qz15)

noncomputable def ep198 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 11) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 10) qz835) Bool.false 2388571087687 549755813888 30485487769499 9392165763416064 Bool.true 44599967673 1099511627776 243636347204935 75137326107328512

noncomputable def ep199 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 10) qz835 Bool.false 2235434002995 549755813888 28087910723015 9392165763416064 Bool.true 209186157357 1099511627776 224484931233163 75137326107328512 Bool.false

noncomputable abbrev qz836 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 9) qz15)

noncomputable def ep200 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 10) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 9) qz836) Bool.false 2235434002995 549755813888 28087910723015 9392165763416064 Bool.true 209186157357 1099511627776 224484931233163 75137326107328512

noncomputable def ep201 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 9) qz836 Bool.false 4167506520365 1099511627776 68156169946871 25045775369109504 Bool.true 440662229 137438953472 17022438093437 6261443842277376 Bool.false

noncomputable def ep202 := nat_lit 4915771358837704218378240

noncomputable abbrev qz837 := (@Nat.cast Real Real.instNatCast 9)

noncomputable abbrev qz294 := (@Inv.inv Real Real.instInv (Real.sqrt qz837))

noncomputable abbrev qz295 := (@HMul.hMul Real Real Real qz0 qz9 (Real.log (Enclosure.sfrac Bool.false 9 1)))

noncomputable def ep203 := @Enclosure.Complex.IsNear.of_eq qz836 (Complex.mk (@HMul.hMul Real Real Real qz0 qz294 (Real.cos qz295)) (@HMul.hMul Real Real Real qz0 qz294 (@Neg.neg Real Real.instNeg (Real.sin qz295)))) Bool.false 303361485625 1099511627776 20234775943507 75137326107328512 Bool.true 205660859525 1099511627776 20215674111919 75137326107328512 (BSN.cpow_neg_s_mk qz9 108936 1000 9 (@Eq.refl Real qz9) rfl)

noncomputable abbrev qz838 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9) qz265)

noncomputable def ep204 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz837) 3145729 1048576 1 1048576 174762 174763 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz837) (Real.sqrt qz838) Bool.false 3145729 1048576 1 1048576 (BSN.sqrt_natCast_div_one 9) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz838) Bool.false 3145729 1048576 1 1048576 3145729 1048576 1 1048576 (BSN.sqrt_enclosure 9 1 1572864 1572865 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep205 := BSN.log_dyadic_bound 1 17 2 1 867 524288 136674 1 1 61752 18 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1) (BSN.artanhQ 17) 0 1 1 867 1 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz296 := (Real.log (Enclosure.sfrac Bool.false 9 1))

noncomputable def ep206 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz296 108936 1000 0 1 9895417793173221 4503599627370496 500000000205011 68337000000000000000 134745904089639750357 562949953421312000 756500000310181643 949125000000000000000 qz270 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 500000000205011 68337000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz838) Bool.false 41504390431577613533184 18889465931478580854784 1000000000410022 136674000000000000000 9895417793173221 4503599627370496 500000000205011 68337000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 61752 524288 24973259072661432 36028797018963968 136674 1000000000000000 rfl rfl rfl rfl (ep205 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep207 := nat_lit 2679306671623717507607283302105760000

noncomputable def ep208 := BSN.cos_dyadic_bound_f 1279397820 2147483648 2 1 1048576 273615 ep207 ep91 ep207 ep207 ep92 ep207 867925 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1279397820) qz266 0 1 ep207 ep91 ep207 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1279397820) qz267 0 1 ep207 ep92 ep207 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz568 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 62745951) (@Nat.cast Real Real.instNatCast 262144))

noncomputable def ep209 := @Enclosure.Real.IsNear.cos_image qz295 qz568 Bool.false 62745951 262144 837 1048576 Bool.false 867925 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz295 Bool.false 134745904089639750357 562949953421312000 756500000310181643 949125000000000000000 62745951 262144 837 1048576 (ep206 rfl) rfl) (Enclosure.sfrac_false_div 62745951 262144) (BSN.cos_reduce0 qz568 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 22507404477133049823232) qz566) 226375608064910080 72057594037927936 Bool.false 867925 1048576 38 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q0 62745951 262144 226375608064910080 72057594037927936 38 22507404477133049823232 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 867925 1048576 22507404477133049823232 37778931862957161709568 1279397820 2147483648 273615 273348 (ep208 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep210 := BSN.sin_dyadic_bound_f 1279397820 2147483648 2 1 1048576 273615 ep207 ep105 ep207 ep207 ep106 ep207 588401 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1279397820) qz272 0 1 ep207 ep105 ep207 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1279397820) qz273 0 1 ep207 ep106 ep207 rfl rfl rfl rfl) rfl rfl

noncomputable def ep211 := @Enclosure.Real.IsNear.sin_image qz295 qz568 Bool.false 62745951 262144 837 1048576 Bool.false 588401 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz295 Bool.false 134745904089639750357 562949953421312000 756500000310181643 949125000000000000000 62745951 262144 837 1048576 (ep206 rfl) rfl) (Enclosure.sfrac_false_div 62745951 262144) (BSN.sin_reduce0 qz568 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 22507404477133049823232) qz566) 226375608064910080 72057594037927936 Bool.false 588401 1048576 38 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q0 62745951 262144 226375608064910080 72057594037927936 38 22507404477133049823232 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 588401 1048576 22507404477133049823232 37778931862957161709568 1279397820 2147483648 273615 273348 (ep210 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz569 := (@Enclosure.Real.IsNear.recentre' qz294 Bool.false 349525 1048576 1 1048576 349525 1048576 1 1048576 (ep204 rfl rfl) rfl)

noncomputable def ep212 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz294 (Real.cos qz295)) (@HMul.hMul Real Real Real qz0 qz294 (@Neg.neg Real Real.instNeg (Real.sin qz295))) Bool.false 303361485625 1099511627776 20234775943507 75137326107328512 Bool.true 205660859525 1099511627776 20215674111919 75137326107328512 (@Enclosure.Real.IsNear.mulLit_ff qz294 (Real.cos qz295) 349525 1048576 1 1048576 867925 1048576 57722357 71656538112 303361485625 1099511627776 20234775943507 75137326107328512 qz569 (@Enclosure.Real.IsNear.recentre' (Real.cos qz295) Bool.false 867925 1048576 115444714 143313076224 867925 1048576 57722357 71656538112 (ep209 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz294 (@Neg.neg Real Real.instNeg (Real.sin qz295)) 349525 1048576 1 1048576 588401 1048576 57722357 71656538112 205660859525 1099511627776 20215674111919 75137326107328512 qz569 (@Enclosure.Real.IsNear.neg (Real.sin qz295) Bool.false 588401 1048576 57722357 71656538112 (@Enclosure.Real.IsNear.recentre' (Real.sin qz295) Bool.false 588401 1048576 115444714 143313076224 588401 1048576 57722357 71656538112 (ep211 rfl rfl) rfl)) rfl)

noncomputable def ep213 := @ep201 303361485625 1099511627776 20234775943507 75137326107328512 Bool.true 205660859525 1099511627776 20215674111919 75137326107328512 Bool.false ep202 2235434002995 549755813888 28087910723015 9392165763416064 Bool.true 28750326547975193493504 209186157357 1099511627776 224484931233163 75137326107328512 EMRow34.d7 (ep203 ep212) rfl rfl

noncomputable abbrev qz839 := (@Nat.cast Real Real.instNatCast 10)

noncomputable abbrev qz297 := (@Inv.inv Real Real.instInv (Real.sqrt qz839))

noncomputable abbrev qz298 := (@HMul.hMul Real Real Real qz0 qz9 (Real.log (Enclosure.sfrac Bool.false 10 1)))

noncomputable def ep214 := @Enclosure.Complex.IsNear.of_eq qz835 (Complex.mk (@HMul.hMul Real Real Real qz0 qz297 (Real.cos qz298)) (@HMul.hMul Real Real Real qz0 qz297 (@Neg.neg Real Real.instNeg (Real.sin qz298)))) Bool.false 38284271173 137438953472 199798087207 782680480284672 Bool.false 41146547421 274877906944 1595951330981 6261443842277376 (BSN.cpow_neg_s_mk qz9 108936 1000 10 (@Eq.refl Real qz9) rfl)

noncomputable abbrev qz840 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 10) qz265)

noncomputable def ep215 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz839) 3315889 1048576 1 1048576 165794 165795 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz839) (Real.sqrt qz840) Bool.false 3315889 1048576 1 1048576 (BSN.sqrt_natCast_div_one 10) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz840) Bool.false 3315889 1048576 1 1048576 3315889 1048576 1 1048576 (BSN.sqrt_enclosure 10 1 1657944 1657945 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep216 := BSN.log_dyadic_bound 2 18 3 2 1574640 524288 136674 6528 48 116991 20 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 2) (BSN.artanhQ 18) 0 2 6528 1574640 48 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz299 := (Real.log (Enclosure.sfrac Bool.false 10 1))

noncomputable def ep217 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz299 108936 1000 0 1 10369917190100709 4503599627370496 500000000205011 68337000000000000000 141207162377601354453 562949953421312000 756500000310181643 949125000000000000000 qz270 (BSN.isNear_log_sfrac 10 1 10369917190100709 4503599627370496 500000000205011 68337000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz840) Bool.false 43494585150108164161536 18889465931478580854784 1000000000410022 136674000000000000000 10369917190100709 4503599627370496 500000000205011 68337000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 116991 524288 24973259072661432 36028797018963968 136674 1000000000000000 rfl rfl rfl rfl (ep216 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep218 := nat_lit 1845840189485549877534310027064337855594009148234037078619847033482635618017825

noncomputable def ep219 := nat_lit 822997159768651253242473038710212978279365700252680900839175388586662158881

noncomputable def ep220 := nat_lit 4833010881822529005798895590724877848400428796145878484450621660873000594170401

noncomputable def ep221 := BSN.sin_dyadic_bound_f 2314327373 2147483648 3 2 1048576 273615 ep218 ep131 ep219 ep220 ep134 ep219 923656 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2314327373) qz272 0 2 ep218 ep131 ep219 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2314327373) qz273 0 2 ep220 ep134 ep219 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz570 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 65754709) (@Nat.cast Real Real.instNatCast 262144))

noncomputable def ep222 := @Enclosure.Real.IsNear.cos_image qz298 qz570 Bool.false 65754709 262144 209 262144 Bool.false 923656 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz298 Bool.false 141207162377601354453 562949953421312000 756500000310181643 949125000000000000000 65754709 262144 209 262144 (ep217 rfl) rfl) (Enclosure.sfrac_false_div 65754709 262144) (BSN.cos_reduce3 qz570 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 40714077717894495469568) qz566) 226375608064910080 72057594037927936 Bool.false 923656 1048576 39 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q3 65754709 262144 226375608064910080 72057594037927936 39 40714077717894495469568 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 923656 1048576 40714077717894495469568 37778931862957161709568 2314327373 2147483648 273615 273348 (ep221 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep223 := nat_lit 1025832548451869332520502225275170014431462578219021790744732429885280526524961

noncomputable def ep224 := nat_lit 3075851651036070695055021729748089617337829003256560010432518938878668255257121

noncomputable def ep225 := BSN.cos_dyadic_bound_f 2314327373 2147483648 3 2 1048576 273615 ep223 ep138 ep219 ep224 ep140 ep219 496356 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2314327373) qz266 0 2 ep223 ep138 ep219 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2314327373) qz267 0 2 ep224 ep140 ep219 rfl rfl rfl rfl) rfl rfl

noncomputable def ep226 := @Enclosure.Real.IsNear.sin_image qz298 qz570 Bool.false 65754709 262144 209 262144 Bool.true 496356 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz298 Bool.false 141207162377601354453 562949953421312000 756500000310181643 949125000000000000000 65754709 262144 209 262144 (ep217 rfl) rfl) (Enclosure.sfrac_false_div 65754709 262144) (BSN.sin_reduce3 qz570 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 40714077717894495469568) qz566) 226375608064910080 72057594037927936 Bool.false 496356 1048576 39 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q3 65754709 262144 226375608064910080 72057594037927936 39 40714077717894495469568 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 496356 1048576 40714077717894495469568 37778931862957161709568 2314327373 2147483648 273615 273348 (ep225 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz571 := (@Enclosure.Real.IsNear.recentre' qz297 Bool.false 331589 1048576 1 1048576 331589 1048576 1 1048576 (ep215 rfl rfl) rfl)

noncomputable def ep227 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz297 (Real.cos qz298)) (@HMul.hMul Real Real Real qz0 qz297 (@Neg.neg Real Real.instNeg (Real.sin qz298))) Bool.false 38284271173 137438953472 199798087207 782680480284672 Bool.false 41146547421 274877906944 1595951330981 6261443842277376 (@Enclosure.Real.IsNear.mulLit_ff qz297 (Real.cos qz298) 331589 1048576 1 1048576 115457 131072 14413505 17914134528 38284271173 137438953472 199798087207 782680480284672 qz571 (@Enclosure.Real.IsNear.recentre' (Real.cos qz298) Bool.false 923656 1048576 28827010 35828269056 115457 131072 14413505 17914134528 (ep222 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz297 (@Neg.neg Real Real.instNeg (Real.sin qz298)) 331589 1048576 1 1048576 124089 262144 14413505 17914134528 41146547421 274877906944 1595951330981 6261443842277376 qz571 (@Enclosure.Real.IsNear.neg (Real.sin qz298) Bool.true 124089 262144 14413505 17914134528 (@Enclosure.Real.IsNear.recentre' (Real.sin qz298) Bool.true 496356 1048576 28827010 35828269056 124089 262144 14413505 17914134528 (ep226 rfl rfl) rfl)) rfl)

noncomputable def ep228 := @ep199 38284271173 137438953472 199798087207 782680480284672 Bool.false 41146547421 274877906944 1595951330981 6261443842277376 Bool.false 328282710585178025099264 2388571087687 549755813888 30485487769499 9392165763416064 Bool.true 12259545763724302221312 44599967673 1099511627776 243636347204935 75137326107328512 (ep200 (BSN.head_sum_c_succ qz12 9 10 rfl rfl) (ep213 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep214 ep227) rfl rfl

noncomputable abbrev qz841 := (@Nat.cast Real Real.instNatCast 11)

noncomputable abbrev qz300 := (@Inv.inv Real Real.instInv (Real.sqrt qz841))

noncomputable abbrev qz301 := (@HMul.hMul Real Real Real qz0 qz9 (Real.log (Enclosure.sfrac Bool.false 11 1)))

noncomputable def ep229 := @Enclosure.Complex.IsNear.of_eq qz834 (Complex.mk (@HMul.hMul Real Real Real qz0 qz300 (Real.cos qz301)) (@HMul.hMul Real Real Real qz0 qz300 (@Neg.neg Real Real.instNeg (Real.sin qz301)))) Bool.true 296339963083 1099511627776 6104479504303 25045775369109504 Bool.false 74304166611 549755813888 1523458873159 6261443842277376 (BSN.cpow_neg_s_mk qz9 108936 1000 11 (@Eq.refl Real qz9) rfl)

noncomputable abbrev qz842 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11) qz265)

noncomputable def ep230 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz841) 3477733 1048576 1 1048576 158078 158079 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz841) (Real.sqrt qz842) Bool.false 3477733 1048576 1 1048576 (BSN.sqrt_natCast_div_one 11) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz842) Bool.false 3477733 1048576 1 1048576 3477733 1048576 1 1048576 (BSN.sqrt_enclosure 11 1 1738866 1738867 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep231 := BSN.log_dyadic_bound 3 19 4 3 4939817505 524288 136674 41676111 10935 166961 22 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 3) (BSN.artanhQ 19) 0 3 41676111 4939817505 10935 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz302 := (Real.log (Enclosure.sfrac Bool.false 11 1))

noncomputable def ep232 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz302 108936 1000 0 1 10799156221662949 4503599627370496 500000000205011 68337000000000000000 147052110270384376533 562949953421312000 756500000310181643 949125000000000000000 qz270 (BSN.isNear_log_sfrac 11 1 10799156221662949 4503599627370496 500000000205011 68337000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz842) Bool.false 45294944137145793642496 18889465931478580854784 1000000000410022 136674000000000000000 10799156221662949 4503599627370496 500000000205011 68337000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 166961 524288 24973259072661432 36028797018963968 136674 1000000000000000 rfl rfl rfl rfl (ep231 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep233 := nat_lit 992884720388610825999709072144204816

noncomputable def ep234 := BSN.cos_dyadic_bound_f 998216414 2147483648 2 1 1048576 273615 ep233 ep91 ep233 ep233 ep92 ep233 937319 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 998216414) qz266 0 1 ep233 ep91 ep233 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 998216414) qz267 0 1 ep233 ep92 ep233 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz843 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 273905899) qz268)

noncomputable def ep235 := @Enclosure.Real.IsNear.cos_image qz301 qz843 Bool.false 273905899 1048576 837 1048576 Bool.true 937319 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz301 Bool.false 147052110270384376533 562949953421312000 756500000310181643 949125000000000000000 273905899 1048576 837 1048576 (ep232 rfl) rfl) (Enclosure.sfrac_false_div 273905899 1048576) (BSN.cos_reduce2 qz843 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 70243235494371574939648) qz271) 226375608064910080 72057594037927936 Bool.false 937319 1048576 41 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q2 273905899 1048576 226375608064910080 72057594037927936 41 70243235494371574939648 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 937319 1048576 70243235494371574939648 151115727451828646838272 998216414 2147483648 273615 273348 (ep234 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep236 := BSN.sin_dyadic_bound_f 998216414 2147483648 2 1 1048576 273615 ep233 ep105 ep233 ep233 ep106 ep233 470046 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 998216414) qz272 0 1 ep233 ep105 ep233 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 998216414) qz273 0 1 ep233 ep106 ep233 rfl rfl rfl rfl) rfl rfl

noncomputable def ep237 := @Enclosure.Real.IsNear.sin_image qz301 qz843 Bool.false 273905899 1048576 837 1048576 Bool.true 470046 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz301 Bool.false 147052110270384376533 562949953421312000 756500000310181643 949125000000000000000 273905899 1048576 837 1048576 (ep232 rfl) rfl) (Enclosure.sfrac_false_div 273905899 1048576) (BSN.sin_reduce2 qz843 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 70243235494371574939648) qz271) 226375608064910080 72057594037927936 Bool.false 470046 1048576 41 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q2 273905899 1048576 226375608064910080 72057594037927936 41 70243235494371574939648 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 470046 1048576 70243235494371574939648 151115727451828646838272 998216414 2147483648 273615 273348 (ep236 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz572 := (@Enclosure.Real.IsNear.recentre' qz300 Bool.false 316157 1048576 1 1048576 316157 1048576 1 1048576 (ep230 rfl rfl) rfl)

noncomputable def ep238 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz300 (Real.cos qz301)) (@HMul.hMul Real Real Real qz0 qz300 (@Neg.neg Real Real.instNeg (Real.sin qz301))) Bool.true 296339963083 1099511627776 6104479504303 25045775369109504 Bool.false 74304166611 549755813888 1523458873159 6261443842277376 (@Enclosure.Real.IsNear.mulLit_ft qz300 (Real.cos qz301) 316157 1048576 1 1048576 937319 1048576 57722357 71656538112 296339963083 1099511627776 6104479504303 25045775369109504 qz572 (@Enclosure.Real.IsNear.recentre' (Real.cos qz301) Bool.true 937319 1048576 115444714 143313076224 937319 1048576 57722357 71656538112 (ep235 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz300 (@Neg.neg Real Real.instNeg (Real.sin qz301)) 316157 1048576 1 1048576 235023 524288 57722357 71656538112 74304166611 549755813888 1523458873159 6261443842277376 qz572 (@Enclosure.Real.IsNear.neg (Real.sin qz301) Bool.true 235023 524288 57722357 71656538112 (@Enclosure.Real.IsNear.recentre' (Real.sin qz301) Bool.true 470046 1048576 115444714 143313076224 235023 524288 57722357 71656538112 (ep237 rfl rfl) rfl)) rfl)

noncomputable def ep239 := @ep196 296339963083 1099511627776 6104479504303 25045775369109504 Bool.false 74304166611 549755813888 1523458873159 6261443842277376 Bool.false ep197 4480802212291 1099511627776 262197340668901 75137326107328512 Bool.false 57179203653551114944512 104008365549 1099511627776 261917853682843 75137326107328512 (ep198 (BSN.head_sum_c_succ qz12 10 11 rfl rfl) (ep228 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep229 ep238) rfl rfl

noncomputable abbrev qz844 := (@Nat.cast Real Real.instNatCast 12)

noncomputable abbrev qz303 := (@Inv.inv Real Real.instInv (Real.sqrt qz844))

noncomputable abbrev qz304 := (@HMul.hMul Real Real Real qz0 qz9 (Real.log (Enclosure.sfrac Bool.false 12 1)))

noncomputable def ep240 := @Enclosure.Complex.IsNear.of_eq qz833 (Complex.mk (@HMul.hMul Real Real Real qz0 qz303 (Real.cos qz304)) (@HMul.hMul Real Real Real qz0 qz303 (@Neg.neg Real Real.instNeg (Real.sin qz304)))) Bool.false 17227999755 68719476736 8767336212433 37568663053664256 Bool.true 157357338147 1099511627776 17507967076973 75137326107328512 (BSN.cpow_neg_s_mk qz9 108936 1000 12 (@Eq.refl Real qz9) rfl)

noncomputable abbrev qz845 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 12) qz265)

noncomputable def ep241 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz844) 3632373 1048576 1 1048576 151348 151349 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz844) (Real.sqrt qz845) Bool.false 3632373 1048576 1 1048576 (BSN.sqrt_natCast_div_one 12) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz845) Bool.false 3632373 1048576 1 1048576 3632373 1048576 1 1048576 (BSN.sqrt_enclosure 12 1 1816186 1816187 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep242 := BSN.log_dyadic_bound 4 20 4 3 6720000000 524288 136674 91811840 61440 212580 24 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 4) (BSN.artanhQ 20) 0 3 91811840 6720000000 61440 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz305 := (Real.log (Enclosure.sfrac Bool.false 12 1))

noncomputable def ep243 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz305 108936 1000 0 1 11191020447815397 4503599627370496 500000000205011 68337000000000000000 152388125437902260949 562949953421312000 756500000310181643 949125000000000000000 qz270 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 500000000205011 68337000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz845) Bool.false 46938541828353910898688 18889465931478580854784 1000000000410022 136674000000000000000 11191020447815397 4503599627370496 500000000205011 68337000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 212580 524288 24973259072661432 36028797018963968 136674 1000000000000000 rfl rfl rfl rfl (ep242 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep244 := nat_lit 1539754792874567397023868883094811201

noncomputable def ep245 := BSN.cos_dyadic_bound_f 1113942801 2147483648 2 1 1048576 273615 ep244 ep91 ep244 ep244 ep92 ep244 910640 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1113942801) qz266 0 1 ep244 ep91 ep244 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1113942801) qz267 0 1 ep244 ep92 ep244 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz306 := (@Nat.cast Real Real.instNatCast 524288)

noncomputable abbrev qz307 := (@Nat.cast Real Real.instNatCast 75557863725914323419136)

noncomputable abbrev qz846 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 141922501) qz306)

noncomputable def ep246 := @Enclosure.Real.IsNear.cos_image qz304 qz846 Bool.false 141922501 524288 837 1048576 Bool.false 910640 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz304 Bool.false 152388125437902260949 562949953421312000 756500000310181643 949125000000000000000 141922501 524288 837 1048576 (ep243 rfl) rfl) (Enclosure.sfrac_false_div 141922501 524288) (BSN.cos_reduce0 qz846 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 39193378015523993812992) qz307) 226375608064910080 72057594037927936 Bool.false 910640 1048576 43 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q0 141922501 524288 226375608064910080 72057594037927936 43 39193378015523993812992 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 910640 1048576 39193378015523993812992 75557863725914323419136 1113942801 2147483648 273615 273348 (ep245 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep247 := BSN.sin_dyadic_bound_f 1113942801 2147483648 2 1 1048576 273615 ep244 ep105 ep244 ep244 ep106 ep244 519851 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1113942801) qz272 0 1 ep244 ep105 ep244 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1113942801) qz273 0 1 ep244 ep106 ep244 rfl rfl rfl rfl) rfl rfl

noncomputable def ep248 := @Enclosure.Real.IsNear.sin_image qz304 qz846 Bool.false 141922501 524288 837 1048576 Bool.false 519851 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz304 Bool.false 152388125437902260949 562949953421312000 756500000310181643 949125000000000000000 141922501 524288 837 1048576 (ep243 rfl) rfl) (Enclosure.sfrac_false_div 141922501 524288) (BSN.sin_reduce0 qz846 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 39193378015523993812992) qz307) 226375608064910080 72057594037927936 Bool.false 519851 1048576 43 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q0 141922501 524288 226375608064910080 72057594037927936 43 39193378015523993812992 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 519851 1048576 39193378015523993812992 75557863725914323419136 1113942801 2147483648 273615 273348 (ep247 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz573 := (@Enclosure.Real.IsNear.recentre' qz303 Bool.false 302697 1048576 1 1048576 302697 1048576 1 1048576 (ep241 rfl rfl) rfl)

noncomputable def ep249 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz303 (Real.cos qz304)) (@HMul.hMul Real Real Real qz0 qz303 (@Neg.neg Real Real.instNeg (Real.sin qz304))) Bool.false 17227999755 68719476736 8767336212433 37568663053664256 Bool.true 157357338147 1099511627776 17507967076973 75137326107328512 (@Enclosure.Real.IsNear.mulLit_ff qz303 (Real.cos qz304) 302697 1048576 1 1048576 56915 65536 57722357 71656538112 17227999755 68719476736 8767336212433 37568663053664256 qz573 (@Enclosure.Real.IsNear.recentre' (Real.cos qz304) Bool.false 910640 1048576 115444714 143313076224 56915 65536 57722357 71656538112 (ep246 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz303 (@Neg.neg Real Real.instNeg (Real.sin qz304)) 302697 1048576 1 1048576 519851 1048576 57722357 71656538112 157357338147 1099511627776 17507967076973 75137326107328512 qz573 (@Enclosure.Real.IsNear.neg (Real.sin qz304) Bool.false 519851 1048576 57722357 71656538112 (@Enclosure.Real.IsNear.recentre' (Real.sin qz304) Bool.false 519851 1048576 115444714 143313076224 519851 1048576 57722357 71656538112 (ep248 rfl rfl) rfl)) rfl)

noncomputable def ep250 := @ep194 17227999755 68719476736 8767336212433 37568663053664256 Bool.true 157357338147 1099511627776 17507967076973 75137326107328512 Bool.false 326860769440093286957056 4756450208371 1099511627776 93244004364589 25045775369109504 Bool.true 58657815701404199682048 26674486299 549755813888 11642742531659 3130721921138688 (ep195 (BSN.head_sum_c_succ qz12 11 12 rfl rfl) (ep239 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep240 ep249) rfl rfl

noncomputable abbrev qz847 := (@Nat.cast Real Real.instNatCast 13)

noncomputable abbrev qz308 := (@Inv.inv Real Real.instInv (Real.sqrt qz847))

noncomputable abbrev qz309 := (@HMul.hMul Real Real Real qz0 qz9 (Real.log (Enclosure.sfrac Bool.false 13 1)))

noncomputable def ep251 := @Enclosure.Complex.IsNear.of_eq qz832 (Complex.mk (@HMul.hMul Real Real Real qz0 qz308 (Real.cos qz309)) (@HMul.hMul Real Real Real qz0 qz308 (@Neg.neg Real Real.instNeg (Real.sin qz309)))) Bool.true 149827647255 549755813888 8418792553585 37568663053664256 Bool.true 56578160535 1099511627776 16780467334145 75137326107328512 (BSN.cpow_neg_s_mk qz9 108936 1000 13 (@Eq.refl Real qz9) rfl)

noncomputable abbrev qz848 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13) qz265)

noncomputable def ep252 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz847) 3780695 1048576 1 1048576 145411 145412 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz847) (Real.sqrt qz848) Bool.false 3780695 1048576 1 1048576 (BSN.sqrt_natCast_div_one 13) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz848) Bool.false 3780695 1048576 1 1048576 3780695 1048576 1 1048576 (BSN.sqrt_enclosure 13 1 1890347 1890348 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep253 := BSN.log_dyadic_bound 5 21 5 4 35742602096145 524288 136674 699352521000 41015625 254545 26 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 5) (BSN.artanhQ 21) 0 4 699352521000 35742602096145 41015625 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz310 := (Real.log (Enclosure.sfrac Bool.false 13 1))

noncomputable def ep254 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz310 108936 1000 0 1 11551497052968677 4503599627370496 500000000205011 68337000000000000000 157296735370274474709 562949953421312000 756500000310181643 949125000000000000000 qz270 (BSN.isNear_log_sfrac 13 1 11551497052968677 4503599627370496 500000000205011 68337000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz848) Bool.false 48450490295254733815808 18889465931478580854784 1000000000410022 136674000000000000000 11551497052968677 4503599627370496 500000000205011 68337000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 254545 524288 24973259072661432 36028797018963968 136674 1000000000000000 rfl rfl rfl rfl (ep253 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep255 := nat_lit 5027129078545467275300924802620857079513392321956705569426288576816466812739840

noncomputable def ep256 := nat_lit 6095141820678660330948778316540522944942763005891822100423264966602208583936

noncomputable def ep257 := nat_lit 13156422118957029794776124080065941028243263036448499255572927653144819028992256

noncomputable def ep258 := BSN.sin_dyadic_bound_f 2972507622 2147483648 3 2 1048576 273615 ep255 ep131 ep256 ep257 ep134 ep256 1030370 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2972507622) qz272 0 2 ep255 ep131 ep256 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2972507622) qz273 0 2 ep257 ep134 ep256 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz849 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 292988001) qz268)

noncomputable def ep259 := @Enclosure.Real.IsNear.cos_image qz309 qz849 Bool.false 292988001 1048576 209 262144 Bool.true 1030370 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz309 Bool.false 157296735370274474709 562949953421312000 756500000310181643 949125000000000000000 292988001 1048576 209 262144 (ep254 rfl) rfl) (Enclosure.sfrac_false_div 292988001 1048576) (BSN.cos_reduce1 qz849 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 209171628482054389235712) qz271) 226375608064910080 72057594037927936 Bool.false 1030370 1048576 44 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q1 292988001 1048576 226375608064910080 72057594037927936 44 209171628482054389235712 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1030370 1048576 209171628482054389235712 151115727451828646838272 2972507622 2147483648 273615 273348 (ep258 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep260 := nat_lit 2795558440001116779758713236263383054371859184645232792837015104883193655337216

noncomputable def ep261 := nat_lit 8374485036361993018614242152157068117225692027923914734310198784716376548843776

noncomputable def ep262 := BSN.cos_dyadic_bound_f 2972507622 2147483648 3 2 1048576 273615 ep260 ep138 ep256 ep261 ep140 ep256 194545 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2972507622) qz266 0 2 ep260 ep138 ep256 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2972507622) qz267 0 2 ep261 ep140 ep256 rfl rfl rfl rfl) rfl rfl

noncomputable def ep263 := @Enclosure.Real.IsNear.sin_image qz309 qz849 Bool.false 292988001 1048576 209 262144 Bool.false 194545 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz309 Bool.false 157296735370274474709 562949953421312000 756500000310181643 949125000000000000000 292988001 1048576 209 262144 (ep254 rfl) rfl) (Enclosure.sfrac_false_div 292988001 1048576) (BSN.sin_reduce1 qz849 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 209171628482054389235712) qz271) 226375608064910080 72057594037927936 Bool.false 194545 1048576 44 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q1 292988001 1048576 226375608064910080 72057594037927936 44 209171628482054389235712 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 194545 1048576 209171628482054389235712 151115727451828646838272 2972507622 2147483648 273615 273348 (ep262 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz574 := (@Enclosure.Real.IsNear.recentre' qz308 Bool.false 290823 1048576 1 1048576 290823 1048576 1 1048576 (ep252 rfl rfl) rfl)

noncomputable def ep264 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz308 (Real.cos qz309)) (@HMul.hMul Real Real Real qz0 qz308 (@Neg.neg Real Real.instNeg (Real.sin qz309))) Bool.true 149827647255 549755813888 8418792553585 37568663053664256 Bool.true 56578160535 1099511627776 16780467334145 75137326107328512 (@Enclosure.Real.IsNear.mulLit_ft qz308 (Real.cos qz309) 290823 1048576 1 1048576 515185 524288 14413505 17914134528 149827647255 549755813888 8418792553585 37568663053664256 qz574 (@Enclosure.Real.IsNear.recentre' (Real.cos qz309) Bool.true 1030370 1048576 28827010 35828269056 515185 524288 14413505 17914134528 (ep259 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz308 (@Neg.neg Real Real.instNeg (Real.sin qz309)) 290823 1048576 1 1048576 194545 1048576 14413505 17914134528 56578160535 1099511627776 16780467334145 75137326107328512 qz574 (@Enclosure.Real.IsNear.neg (Real.sin qz309) Bool.false 194545 1048576 14413505 17914134528 (@Enclosure.Real.IsNear.recentre' (Real.sin qz309) Bool.false 194545 1048576 28827010 35828269056 194545 1048576 14413505 17914134528 (ep263 rfl rfl) rfl)) rfl)

noncomputable def ep265 := @ep191 149827647255 549755813888 8418792553585 37568663053664256 Bool.true 56578160535 1099511627776 16780467334145 75137326107328512 Bool.false ep192 4456794913861 1099511627776 296569598200937 75137326107328512 Bool.true 60433080543906946351104 109927133133 1099511627776 296206288093961 75137326107328512 (ep193 (BSN.head_sum_c_succ qz12 12 13 rfl rfl) (ep250 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep251 ep264) rfl rfl

noncomputable abbrev qz850 := (@Nat.cast Real Real.instNatCast 14)

noncomputable abbrev qz311 := (@Inv.inv Real Real.instInv (Real.sqrt qz850))

noncomputable abbrev qz312 := (@HMul.hMul Real Real Real qz0 qz9 (Real.log (Enclosure.sfrac Bool.false 14 1)))

noncomputable def ep266 := @Enclosure.Complex.IsNear.of_eq qz831 (Complex.mk (@HMul.hMul Real Real Real qz0 qz311 (Real.cos qz312)) (@HMul.hMul Real Real Real qz0 qz311 (@Neg.neg Real Real.instNeg (Real.sin qz312)))) Bool.false 9532465645 1099511627776 16178668698163 75137326107328512 Bool.false 36712673729 137438953472 4061990757799 18784331526832128 (BSN.cpow_neg_s_mk qz9 108936 1000 14 (@Eq.refl Real qz9) rfl)

noncomputable abbrev qz851 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14) qz265)

noncomputable def ep267 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz850) 3923413 1048576 1 1048576 140121 140122 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz850) (Real.sqrt qz851) Bool.false 3923413 1048576 1 1048576 (BSN.sqrt_natCast_div_one 14) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz851) Bool.false 3923413 1048576 1 1048576 3923413 1048576 1 1048576 (BSN.sqrt_enclosure 14 1 1961706 1961707 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep268 := BSN.log_dyadic_bound 6 22 5 4 51857700491520 524288 136674 1346332575744 176359680 293399 28 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 6) (BSN.artanhQ 22) 0 4 1346332575744 51857700491520 176359680 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz313 := (Real.log (Enclosure.sfrac Bool.false 14 1))

noncomputable def ep269 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz313 108936 1000 0 1 11885250371606245 4503599627370496 500000000205011 68337000000000000000 32368290862032447633 112589990684262400 756500000310181643 949125000000000000000 qz270 (BSN.isNear_log_sfrac 14 1 11885250371606245 4503599627370496 500000000205011 68337000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz851) Bool.false 49850353174629559828480 18889465931478580854784 1000000000410022 136674000000000000000 11885250371606245 4503599627370496 500000000205011 68337000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 293399 524288 24973259072661432 36028797018963968 136674 1000000000000000 rfl rfl rfl rfl (ep268 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep270 := BSN.sin_dyadic_bound_f 69676570 2147483648 1 0 1048576 273615 0 1 1 0 1 1 34015 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 69676570) qz272 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 69676570) qz273 0 0 rfl) rfl rfl

noncomputable abbrev qz852 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 301453199) qz268)

noncomputable def ep271 := @Enclosure.Real.IsNear.cos_image qz312 qz852 Bool.false 301453199 1048576 837 1048576 Bool.false 34015 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz312 Bool.false 32368290862032447633 112589990684262400 756500000310181643 949125000000000000000 301453199 1048576 837 1048576 (ep269 rfl) rfl) (Enclosure.sfrac_false_div 301453199 1048576) (BSN.cos_reduce3 qz852 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4903052737786452901888) qz271) 226375608064910080 72057594037927936 Bool.false 34015 1048576 45 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q3 301453199 1048576 226375608064910080 72057594037927936 45 4903052737786452901888 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 34015 1048576 4903052737786452901888 151115727451828646838272 69676570 2147483648 273615 273348 (ep270 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep272 := BSN.cos_dyadic_bound_f 69676570 2147483648 1 0 1048576 273615 0 1 1 0 1 1 1048024 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 69676570) qz266 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 69676570) qz267 0 0 rfl) rfl rfl

noncomputable def ep273 := @Enclosure.Real.IsNear.sin_image qz312 qz852 Bool.false 301453199 1048576 837 1048576 Bool.true 1048024 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz312 Bool.false 32368290862032447633 112589990684262400 756500000310181643 949125000000000000000 301453199 1048576 837 1048576 (ep269 rfl) rfl) (Enclosure.sfrac_false_div 301453199 1048576) (BSN.sin_reduce3 qz852 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4903052737786452901888) qz271) 226375608064910080 72057594037927936 Bool.false 1048024 1048576 45 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q3 301453199 1048576 226375608064910080 72057594037927936 45 4903052737786452901888 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1048024 1048576 4903052737786452901888 151115727451828646838272 69676570 2147483648 273615 273348 (ep272 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz575 := (@Enclosure.Real.IsNear.recentre' qz311 Bool.false 280243 1048576 1 1048576 280243 1048576 1 1048576 (ep267 rfl rfl) rfl)

noncomputable def ep274 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz311 (Real.cos qz312)) (@HMul.hMul Real Real Real qz0 qz311 (@Neg.neg Real Real.instNeg (Real.sin qz312))) Bool.false 9532465645 1099511627776 16178668698163 75137326107328512 Bool.false 36712673729 137438953472 4061990757799 18784331526832128 (@Enclosure.Real.IsNear.mulLit_ff qz311 (Real.cos qz312) 280243 1048576 1 1048576 34015 1048576 57722357 71656538112 9532465645 1099511627776 16178668698163 75137326107328512 qz575 (@Enclosure.Real.IsNear.recentre' (Real.cos qz312) Bool.false 34015 1048576 115444714 143313076224 34015 1048576 57722357 71656538112 (ep271 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz311 (@Neg.neg Real Real.instNeg (Real.sin qz312)) 280243 1048576 1 1048576 131003 131072 57722357 71656538112 36712673729 137438953472 4061990757799 18784331526832128 qz575 (@Enclosure.Real.IsNear.neg (Real.sin qz312) Bool.true 131003 131072 57722357 71656538112 (@Enclosure.Real.IsNear.recentre' (Real.sin qz312) Bool.true 1048024 1048576 115444714 143313076224 131003 131072 57722357 71656538112 (ep273 rfl rfl) rfl)) rfl)

noncomputable def ep275 := @ep188 9532465645 1099511627776 16178668698163 75137326107328512 Bool.false 36712673729 137438953472 4061990757799 18784331526832128 Bool.false ep189 2233163689753 549755813888 26062355574925 6261443842277376 Bool.false 25257741515805245308928 183774256699 1099511627776 104151417041719 25045775369109504 (ep190 (BSN.head_sum_c_succ qz12 13 14 rfl rfl) (ep265 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep266 ep274) rfl rfl

noncomputable abbrev qz853 := (@Nat.cast Real Real.instNatCast 15)

noncomputable abbrev qz314 := (@Inv.inv Real Real.instInv (Real.sqrt qz853))

noncomputable abbrev qz315 := (@HMul.hMul Real Real Real qz0 qz9 (Real.log (Enclosure.sfrac Bool.false 15 1)))

noncomputable def ep276 := @Enclosure.Complex.IsNear.of_eq qz830 (Complex.mk (@HMul.hMul Real Real Real qz0 qz314 (Real.cos qz315)) (@HMul.hMul Real Real Real qz0 qz314 (@Neg.neg Real Real.instNeg (Real.sin qz315)))) Bool.false 135362648511 549755813888 3924049853837 18784331526832128 Bool.false 21363901569 274877906944 7824717998113 37568663053664256 (BSN.cpow_neg_s_mk qz9 108936 1000 15 (@Eq.refl Real qz9) rfl)

noncomputable abbrev qz854 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 15) qz265)

noncomputable def ep277 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz853) 4061117 1048576 1 1048576 135370 135371 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz853) (Real.sqrt qz854) Bool.false 4061117 1048576 1 1048576 (BSN.sqrt_natCast_div_one 15) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz854) Bool.false 4061117 1048576 1 1048576 4061117 1048576 1 1048576 (BSN.sqrt_enclosure 15 1 2030558 2030559 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep278 := BSN.log_dyadic_bound 7 23 6 5 430628584065881355 524288 136674 14087658153505881 266939110305 329571 30 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 7) (BSN.artanhQ 23) 0 5 14087658153505881 430628584065881355 266939110305 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz316 := (Real.log (Enclosure.sfrac Bool.false 15 1))

noncomputable def ep279 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz316 108936 1000 0 1 12195965485668069 4503599627370496 500000000205011 68337000000000000000 166072462018342095573 562949953421312000 756500000310181643 949125000000000000000 qz270 (BSN.isNear_log_sfrac 15 1 12195965485668069 4503599627370496 500000000205011 68337000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz854) Bool.false 51153586820399524478976 18889465931478580854784 1000000000410022 136674000000000000000 12195965485668069 4503599627370496 500000000205011 68337000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 329571 524288 24973259072661432 36028797018963968 136674 1000000000000000 rfl rfl rfl rfl (ep278 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep280 := nat_lit 3505945932698409673409010195828581569608079692059668815694794665151802511947905

noncomputable def ep281 := nat_lit 2966693148507442031272302524354180194331616161985670999391822700968322496641

noncomputable def ep282 := nat_lit 9177436130064918048020585832606854485801767053036870097582589743405534056773761

noncomputable def ep283 := BSN.sin_dyadic_bound_f 2716652433 2147483648 3 2 1048576 273615 ep280 ep131 ep281 ep282 ep134 ep281 999942 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2716652433) qz272 0 2 ep280 ep131 ep281 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2716652433) qz273 0 2 ep282 ep134 ep281 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz855 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 309334065) qz268)

noncomputable def ep284 := @Enclosure.Real.IsNear.cos_image qz315 qz855 Bool.false 309334065 1048576 837 1048576 Bool.false 999942 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz315 Bool.false 166072462018342095573 562949953421312000 756500000310181643 949125000000000000000 309334065 1048576 837 1048576 (ep279 rfl) rfl) (Enclosure.sfrac_false_div 309334065 1048576) (BSN.cos_reduce3 qz855 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 191167420119319807262720) qz271) 226375608064910080 72057594037927936 Bool.false 999942 1048576 46 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q3 309334065 1048576 226375608064910080 72057594037927936 46 191167420119319807262720 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 999942 1048576 191167420119319807262720 151115727451828646838272 2716652433 2147483648 273615 273348 (ep283 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep285 := nat_lit 1949066270676230903907793354360036063201969436105142973607948957395876205525121

noncomputable def ep286 := nat_lit 5841265425731677827660835458031399829217245075991457578825063226785691971582081

noncomputable def ep287 := BSN.cos_dyadic_bound_f 2716652433 2147483648 3 2 1048576 273615 ep285 ep138 ep281 ep286 ep140 ep281 315636 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2716652433) qz266 0 2 ep285 ep138 ep281 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2716652433) qz267 0 2 ep286 ep140 ep281 rfl rfl rfl rfl) rfl rfl

noncomputable def ep288 := @Enclosure.Real.IsNear.sin_image qz315 qz855 Bool.false 309334065 1048576 837 1048576 Bool.true 315636 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz315 Bool.false 166072462018342095573 562949953421312000 756500000310181643 949125000000000000000 309334065 1048576 837 1048576 (ep279 rfl) rfl) (Enclosure.sfrac_false_div 309334065 1048576) (BSN.sin_reduce3 qz855 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 191167420119319807262720) qz271) 226375608064910080 72057594037927936 Bool.false 315636 1048576 46 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q3 309334065 1048576 226375608064910080 72057594037927936 46 191167420119319807262720 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 315636 1048576 191167420119319807262720 151115727451828646838272 2716652433 2147483648 273615 273348 (ep287 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz576 := (@Enclosure.Real.IsNear.recentre' qz314 Bool.false 270741 1048576 1 1048576 270741 1048576 1 1048576 (ep277 rfl rfl) rfl)

noncomputable def ep289 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz314 (Real.cos qz315)) (@HMul.hMul Real Real Real qz0 qz314 (@Neg.neg Real Real.instNeg (Real.sin qz315))) Bool.false 135362648511 549755813888 3924049853837 18784331526832128 Bool.false 21363901569 274877906944 7824717998113 37568663053664256 (@Enclosure.Real.IsNear.mulLit_ff qz314 (Real.cos qz315) 270741 1048576 1 1048576 499971 524288 57722357 71656538112 135362648511 549755813888 3924049853837 18784331526832128 qz576 (@Enclosure.Real.IsNear.recentre' (Real.cos qz315) Bool.false 999942 1048576 115444714 143313076224 499971 524288 57722357 71656538112 (ep284 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz314 (@Neg.neg Real Real.instNeg (Real.sin qz315)) 270741 1048576 1 1048576 78909 262144 57722357 71656538112 21363901569 274877906944 7824717998113 37568663053664256 qz576 (@Enclosure.Real.IsNear.neg (Real.sin qz315) Bool.true 78909 262144 57722357 71656538112 (@Enclosure.Real.IsNear.recentre' (Real.sin qz315) Bool.true 315636 1048576 115444714 143313076224 78909 262144 57722357 71656538112 (ep288 rfl rfl) rfl)) rfl)

noncomputable def ep290 := @ep185 135362648511 549755813888 3924049853837 18784331526832128 Bool.false 21363901569 274877906944 7824717998113 37568663053664256 Bool.false ep186 296065792283 68719476736 20527779144653 4696082881708032 Bool.false 74005341221387920998400 269229862975 1099511627776 328103687121383 75137326107328512 (ep187 (BSN.head_sum_c_succ qz12 14 15 rfl rfl) (ep275 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep276 ep289) rfl rfl

noncomputable abbrev qz856 := (@Nat.cast Real Real.instNatCast 16)

noncomputable abbrev qz317 := (@Inv.inv Real Real.instInv (Real.sqrt qz856))

noncomputable abbrev qz318 := (@HMul.hMul Real Real Real qz0 qz9 (Real.log (Enclosure.sfrac Bool.false 16 1)))

noncomputable def ep291 := @Enclosure.Complex.IsNear.of_eq qz829 (Complex.mk (@HMul.hMul Real Real Real qz0 qz317 (Real.cos qz318)) (@HMul.hMul Real Real Real qz0 qz317 (@Neg.neg Real Real.instNeg (Real.sin qz318)))) Bool.false 124240315563 549755813888 7598172482821 37568663053664256 Bool.true 29383871013 274877906944 3790552351019 18784331526832128 (BSN.cpow_neg_s_mk qz9 108936 1000 16 (@Eq.refl Real qz9) rfl)

noncomputable abbrev qz857 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16) qz265)

noncomputable def ep292 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz856) 4194305 1048576 1 1048576 131071 131072 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz856) (Real.sqrt qz857) Bool.false 4194305 1048576 1 1048576 (BSN.sqrt_natCast_div_one 16) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz857) Bool.false 4194305 1048576 1 1048576 4194305 1048576 1 1048576 (BSN.sqrt_enclosure 16 1 2097152 2097153 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep293 := BSN.log_dyadic_bound 0 32 1 0 1 524288 136674 0 1 0 32 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 32) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz319 := (Real.log (Enclosure.sfrac Bool.false 16 1))

noncomputable def ep294 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz319 108936 1000 0 1 3121657384082679 1125899906842624 125000000068337 17084250000000000000 42507608599053839943 140737488355328000 189125000103393881 237281250000000000000 qz270 (BSN.isNear_log_sfrac 16 1 3121657384082679 1125899906842624 125000000068337 17084250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz857) Bool.false 52372720210750067441664 18889465931478580854784 1000000000546696 136674000000000000000 3121657384082679 1125899906842624 125000000068337 17084250000000000000 (BSN.log_rat_reduce_isNear 16 1 4 32 32 0 524288 24973259072661432 36028797018963968 136674 1000000000000000 rfl rfl rfl rfl (ep293 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep295 := nat_lit 810472460897114743408745917422823696

noncomputable def ep296 := BSN.cos_dyadic_bound_f 948821606 2147483648 2 1 1048576 273615 ep295 ep91 ep295 ep295 ep92 ep295 947882 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 948821606) qz266 0 1 ep295 ep91 ep295 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 948821606) qz267 0 1 ep295 ep92 ep295 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz858 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 316706363) qz268)

noncomputable def ep297 := @Enclosure.Real.IsNear.cos_image qz318 qz858 Bool.false 316706363 1048576 837 1048576 Bool.false 947882 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz318 Bool.false 42507608599053839943 140737488355328000 189125000103393881 237281250000000000000 316706363 1048576 837 1048576 (ep294 rfl) rfl) (Enclosure.sfrac_false_div 316706363 1048576) (BSN.cos_reduce0 qz858 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 66767384929220140466176) qz271) 226375608064910080 72057594037927936 Bool.false 947882 1048576 48 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q0 316706363 1048576 226375608064910080 72057594037927936 48 66767384929220140466176 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 947882 1048576 66767384929220140466176 151115727451828646838272 948821606 2147483648 273615 273348 (ep296 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep298 := BSN.sin_dyadic_bound_f 948821606 2147483648 2 1 1048576 273615 ep295 ep105 ep295 ep295 ep106 ep295 448364 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 948821606) qz272 0 1 ep295 ep105 ep295 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 948821606) qz273 0 1 ep295 ep106 ep295 rfl rfl rfl rfl) rfl rfl

noncomputable def ep299 := @Enclosure.Real.IsNear.sin_image qz318 qz858 Bool.false 316706363 1048576 837 1048576 Bool.false 448364 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz318 Bool.false 42507608599053839943 140737488355328000 189125000103393881 237281250000000000000 316706363 1048576 837 1048576 (ep294 rfl) rfl) (Enclosure.sfrac_false_div 316706363 1048576) (BSN.sin_reduce0 qz858 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 66767384929220140466176) qz271) 226375608064910080 72057594037927936 Bool.false 448364 1048576 48 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q0 316706363 1048576 226375608064910080 72057594037927936 48 66767384929220140466176 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 448364 1048576 66767384929220140466176 151115727451828646838272 948821606 2147483648 273615 273348 (ep298 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz577 := (@Enclosure.Real.IsNear.recentre' qz317 Bool.false 262143 1048576 1 1048576 262143 1048576 1 1048576 (ep292 rfl rfl) rfl)

noncomputable def ep300 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz317 (Real.cos qz318)) (@HMul.hMul Real Real Real qz0 qz317 (@Neg.neg Real Real.instNeg (Real.sin qz318))) Bool.false 124240315563 549755813888 7598172482821 37568663053664256 Bool.true 29383871013 274877906944 3790552351019 18784331526832128 (@Enclosure.Real.IsNear.mulLit_ff qz317 (Real.cos qz318) 262143 1048576 1 1048576 473941 524288 57722357 71656538112 124240315563 549755813888 7598172482821 37568663053664256 qz577 (@Enclosure.Real.IsNear.recentre' (Real.cos qz318) Bool.false 947882 1048576 115444714 143313076224 473941 524288 57722357 71656538112 (ep297 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz317 (@Neg.neg Real Real.instNeg (Real.sin qz318)) 262143 1048576 1 1048576 112091 262144 57722357 71656538112 29383871013 274877906944 3790552351019 18784331526832128 qz577 (@Enclosure.Real.IsNear.neg (Real.sin qz318) Bool.false 112091 262144 57722357 71656538112 (@Enclosure.Real.IsNear.recentre' (Real.sin qz318) Bool.false 448364 1048576 115444714 143313076224 112091 262144 57722357 71656538112 (ep299 rfl rfl) rfl)) rfl)

noncomputable def ep301 := @ep183 124240315563 549755813888 7598172482821 37568663053664256 Bool.true 29383871013 274877906944 3790552351019 18784331526832128 Bool.false 171301620075941091868672 2492766653827 549755813888 171820405640045 37568663053664256 Bool.false 41697433373524268941312 151694378923 1099511627776 343265896525459 75137326107328512 (ep184 (BSN.head_sum_c_succ qz12 15 16 rfl rfl) (ep290 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep291 ep300) rfl rfl

theorem EMRow34.d8 : Enclosure.Complex.IsNear (BSN.headSumC qz12 17) Bool.false 2492766653827 549755813888 171820405640045 37568663053664256 Bool.false 151694378923 1099511627776 343265896525459 75137326107328512 := ep182 (BSN.head_sum_c_succ qz12 16 17 rfl rfl) (ep301 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz859 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 24) qz15)

noncomputable def ep302 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 25) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 24) qz859) Bool.false 5732092807383 1099511627776 451498841158823 75137326107328512 Bool.true 131548070893 1099511627776 451107585045719 75137326107328512

noncomputable def ep303 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 24) qz859 Bool.false 693829219221 137438953472 219543006391499 37568663053664256 Bool.false 528118681 1099511627776 438710523314197 75137326107328512 Bool.false

noncomputable abbrev qz860 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 23) qz15)

noncomputable def ep304 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 24) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 23) qz860) Bool.false 693829219221 137438953472 219543006391499 37568663053664256 Bool.false 528118681 1099511627776 438710523314197 75137326107328512

noncomputable def ep305 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 23) qz860 Bool.false 2849618546217 549755813888 106604729924249 18784331526832128 Bool.false 175110181321 1099511627776 426035310562529 75137326107328512 Bool.true

noncomputable def ep306 := nat_lit 1525746588448465713364992

noncomputable abbrev qz861 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 22) qz15)

noncomputable def ep307 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 23) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 22) qz861) Bool.false 2849618546217 549755813888 106604729924249 18784331526832128 Bool.false 175110181321 1099511627776 426035310562529 75137326107328512

noncomputable def ep308 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 22) qz861 Bool.false 2947960376289 549755813888 68909083777481 12522887684554752 Bool.false 11892448759 274877906944 68848671546023 12522887684554752 Bool.true

noncomputable abbrev qz862 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 21) qz15)

noncomputable def ep309 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 22) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 21) qz862) Bool.false 2947960376289 549755813888 68909083777481 12522887684554752 Bool.false 11892448759 274877906944 68848671546023 12522887684554752

noncomputable def ep310 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 21) qz862 Bool.false 2921786114087 549755813888 200107602465887 37568663053664256 Bool.true 23322858477 137438953472 199872069564881 37568663053664256 Bool.false

noncomputable abbrev qz863 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 20) qz15)

noncomputable def ep311 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 21) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 20) qz863) Bool.false 2921786114087 549755813888 200107602465887 37568663053664256 Bool.true 23322858477 137438953472 199872069564881 37568663053664256

noncomputable def ep312 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 20) qz863 Bool.false 350968399011 68719476736 671233667695 130446746714112 Bool.true 278380529413 1099511627776 42911027359609 8348591789703168 Bool.false

noncomputable abbrev qz864 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 19) qz15)

noncomputable def ep313 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 20) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 19) qz864) Bool.false 350968399011 68719476736 671233667695 130446746714112 Bool.true 278380529413 1099511627776 42911027359609 8348591789703168

noncomputable def ep314 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 19) qz864 Bool.false 2687750830031 549755813888 186346582703209 37568663053664256 Bool.true 25090439199 137438953472 186153967351639 37568663053664256 Bool.false

noncomputable def ep315 := nat_lit 1543575342778085114118144

noncomputable abbrev qz865 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 18) qz15)

noncomputable def ep316 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 19) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 18) qz865) Bool.false 2687750830031 549755813888 186346582703209 37568663053664256 Bool.true 25090439199 137438953472 186153967351639 37568663053664256

noncomputable def ep317 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 18) qz865 Bool.false 5178330771037 1099511627776 358372451878979 75137326107328512 Bool.true 32539976753 1099511627776 357995236149221 75137326107328512 Bool.false

noncomputable def ep318 := nat_lit 5910426580367359829082112

noncomputable abbrev qz866 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 17) qz15)

noncomputable def ep319 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 18) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 17) qz866) Bool.false 5178330771037 1099511627776 358372451878979 75137326107328512 Bool.true 32539976753 1099511627776 357995236149221 75137326107328512

noncomputable def ep320 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 17) qz866 Bool.false 2492766653827 549755813888 171820405640045 37568663053664256 Bool.false 151694378923 1099511627776 343265896525459 75137326107328512 Bool.false

noncomputable def ep321 := nat_lit 2846817447612720512761856

noncomputable abbrev qz867 := (@Nat.cast Real Real.instNatCast 17)

noncomputable abbrev qz320 := (@Inv.inv Real Real.instInv (Real.sqrt qz867))

noncomputable abbrev qz321 := (@HMul.hMul Real Real Real qz0 qz9 (Real.log (Enclosure.sfrac Bool.false 17 1)))

noncomputable def ep322 := @Enclosure.Complex.IsNear.of_eq qz866 (Complex.mk (@HMul.hMul Real Real Real qz0 qz320 (Real.cos qz321)) (@HMul.hMul Real Real Real qz0 qz320 (@Neg.neg Real Real.instNeg (Real.sin qz321)))) Bool.false 192797463383 1099511627776 14731640598889 75137326107328512 Bool.true 46058588919 274877906944 7364669811881 37568663053664256 (BSN.cpow_neg_s_mk qz9 108936 1000 17 (@Eq.refl Real qz9) rfl)

noncomputable abbrev qz868 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 17) qz265)

noncomputable def ep323 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz867) 4323389 1048576 1 1048576 127158 127159 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz867) (Real.sqrt qz868) Bool.false 4323389 1048576 1 1048576 (BSN.sqrt_natCast_div_one 17) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz868) Bool.false 4323389 1048576 1 1048576 4323389 1048576 1 1048576 (BSN.sqrt_enclosure 17 1 2161694 2161695 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep324 := BSN.log_dyadic_bound 1 33 2 1 3267 524288 136674 1 1 31784 34 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1) (BSN.artanhQ 33) 0 1 1 3267 1 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz322 := (Real.log (Enclosure.sfrac Bool.false 17 1))

noncomputable def ep325 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz322 108936 1000 0 1 3189913004350711 1125899906842624 125000000068337 17084250000000000000 43437045380243631687 140737488355328000 189125000103393881 237281250000000000000 qz270 (BSN.isNear_log_sfrac 17 1 3189913004350711 1125899906842624 125000000068337 17084250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz868) Bool.false 53517859495200818200576 18889465931478580854784 1000000000546696 136674000000000000000 3189913004350711 1125899906842624 125000000068337 17084250000000000000 (BSN.log_rat_reduce_isNear 17 1 4 34 32 31784 524288 24973259072661432 36028797018963968 136674 1000000000000000 rfl rfl rfl rfl (ep324 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep326 := nat_lit 257174553898381162771088089370286100468374774448580891108818580282243264839936

noncomputable def ep327 := nat_lit 51787336659829062669242129188196127559813038181897473307659710332037529856

noncomputable def ep328 := nat_lit 771420087021823830187925783852481909150004697269378878379840421426065719460096

noncomputable def ep329 := BSN.cos_dyadic_bound_f 1637864414 2147483648 3 2 1048576 273615 ep326 ep138 ep327 ep328 ep140 ep327 758099 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1637864414) qz266 0 2 ep326 ep138 ep327 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1637864414) qz267 0 2 ep328 ep140 ep327 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz869 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 323631207) qz268)

noncomputable def ep330 := @Enclosure.Real.IsNear.cos_image qz321 qz869 Bool.false 323631207 1048576 837 1048576 Bool.false 758099 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz321 Bool.false 43437045380243631687 140737488355328000 189125000103393881 237281250000000000000 323631207 1048576 837 1048576 (ep325 rfl) rfl) (Enclosure.sfrac_false_div 323631207 1048576) (BSN.cos_reduce0 qz869 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 115254461976097612365824) qz271) 226375608064910080 72057594037927936 Bool.false 758099 1048576 49 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q0 323631207 1048576 226375608064910080 72057594037927936 49 115254461976097612365824 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 758099 1048576 115254461976097612365824 151115727451828646838272 1637864414 2147483648 273615 273348 (ep329 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep331 := nat_lit 7196341894311933166827998047839052816

noncomputable def ep332 := BSN.sin_dyadic_bound_f 1637864414 2147483648 2 1 1048576 273615 ep331 ep105 ep331 ep331 ep106 ep331 724428 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1637864414) qz272 0 1 ep331 ep105 ep331 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1637864414) qz273 0 1 ep331 ep106 ep331 rfl rfl rfl rfl) rfl rfl

noncomputable def ep333 := @Enclosure.Real.IsNear.sin_image qz321 qz869 Bool.false 323631207 1048576 837 1048576 Bool.false 724428 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz321 Bool.false 43437045380243631687 140737488355328000 189125000103393881 237281250000000000000 323631207 1048576 837 1048576 (ep325 rfl) rfl) (Enclosure.sfrac_false_div 323631207 1048576) (BSN.sin_reduce0 qz869 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 115254461976097612365824) qz271) 226375608064910080 72057594037927936 Bool.false 724428 1048576 49 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q0 323631207 1048576 226375608064910080 72057594037927936 49 115254461976097612365824 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 724428 1048576 115254461976097612365824 151115727451828646838272 1637864414 2147483648 273615 273348 (ep332 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz578 := (@Enclosure.Real.IsNear.recentre' qz320 Bool.false 254317 1048576 1 1048576 254317 1048576 1 1048576 (ep323 rfl rfl) rfl)

noncomputable def ep334 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz320 (Real.cos qz321)) (@HMul.hMul Real Real Real qz0 qz320 (@Neg.neg Real Real.instNeg (Real.sin qz321))) Bool.false 192797463383 1099511627776 14731640598889 75137326107328512 Bool.true 46058588919 274877906944 7364669811881 37568663053664256 (@Enclosure.Real.IsNear.mulLit_ff qz320 (Real.cos qz321) 254317 1048576 1 1048576 758099 1048576 57722357 71656538112 192797463383 1099511627776 14731640598889 75137326107328512 qz578 (@Enclosure.Real.IsNear.recentre' (Real.cos qz321) Bool.false 758099 1048576 115444714 143313076224 758099 1048576 57722357 71656538112 (ep330 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz320 (@Neg.neg Real Real.instNeg (Real.sin qz321)) 254317 1048576 1 1048576 181107 262144 57722357 71656538112 46058588919 274877906944 7364669811881 37568663053664256 qz578 (@Enclosure.Real.IsNear.neg (Real.sin qz321) Bool.false 181107 262144 57722357 71656538112 (@Enclosure.Real.IsNear.recentre' (Real.sin qz321) Bool.false 724428 1048576 115444714 143313076224 181107 262144 57722357 71656538112 (ep333 rfl rfl) rfl)) rfl)

noncomputable def ep335 := @ep320 192797463383 1099511627776 14731640598889 75137326107328512 Bool.true 46058588919 274877906944 7364669811881 37568663053664256 Bool.false ep321 5178330771037 1099511627776 358372451878979 75137326107328512 Bool.true 8944520701871057272832 32539976753 1099511627776 357995236149221 75137326107328512 EMRow34.d8 (ep322 ep334) rfl rfl

noncomputable abbrev qz870 := (@Nat.cast Real Real.instNatCast 18)

noncomputable abbrev qz323 := (@Inv.inv Real Real.instInv (Real.sqrt qz870))

noncomputable abbrev qz324 := (@HMul.hMul Real Real Real qz0 qz9 (Real.log (Enclosure.sfrac Bool.false 18 1)))

noncomputable def ep336 := @Enclosure.Complex.IsNear.of_eq qz865 (Complex.mk (@HMul.hMul Real Real Real qz0 qz323 (Real.cos qz324)) (@HMul.hMul Real Real Real qz0 qz323 (@Neg.neg Real Real.instNeg (Real.sin qz324)))) Bool.false 197170889025 1099511627776 4773571175813 25045775369109504 Bool.true 168183536839 1099511627776 4770899518019 25045775369109504 (BSN.cpow_neg_s_mk qz9 108936 1000 18 (@Eq.refl Real qz9) rfl)

noncomputable abbrev qz871 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 18) qz265)

noncomputable def ep337 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz870) 4448731 1048576 1 1048576 123575 123576 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz870) (Real.sqrt qz871) Bool.false 4448731 1048576 1 1048576 (BSN.sqrt_natCast_div_one 18) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz871) Bool.false 4448731 1048576 1 1048576 4448731 1048576 1 1048576 (BSN.sqrt_enclosure 18 1 2224365 2224366 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep338 := BSN.log_dyadic_bound 2 34 2 1 3468 524288 136674 4 4 61752 36 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 2) (BSN.artanhQ 34) 0 1 4 3468 4 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz325 := (Real.log (Enclosure.sfrac Bool.false 18 1))

noncomputable def ep339 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz325 108936 1000 0 1 3254268794313975 1125899906842624 125000000068337 17084250000000000000 1772535126886935903 5629499534213120 189125000103393881 237281250000000000000 qz270 (BSN.isNear_log_sfrac 18 1 3254268794313975 1125899906842624 125000000068337 17084250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz871) Bool.false 54597570484265130393600 18889465931478580854784 1000000000546696 136674000000000000000 3254268794313975 1125899906842624 125000000068337 17084250000000000000 (BSN.log_rat_reduce_isNear 18 1 4 36 32 61752 524288 24973259072661432 36028797018963968 136674 1000000000000000 rfl rfl rfl rfl (ep338 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep340 := nat_lit 189052109071954109208971269910038263642447892371927753000691036646965436557921

noncomputable def ep341 := nat_lit 27988328658988070549423596740466419177502454591637262038164570774647417441

noncomputable def ep342 := nat_lit 567100350558544351485814962536633858088988672206599984477996780799347014838881

noncomputable def ep343 := BSN.cos_dyadic_bound_f 1516603733 2147483648 3 2 1048576 273615 ep340 ep138 ep341 ep342 ep140 ep341 797775 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1516603733) qz266 0 2 ep340 ep138 ep341 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1516603733) qz267 0 2 ep342 ep140 ep341 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz872 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 330160395) qz268)

noncomputable def ep344 := @Enclosure.Real.IsNear.cos_image qz324 qz872 Bool.false 330160395 1048576 837 1048576 Bool.false 797775 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz324 Bool.false 1772535126886935903 5629499534213120 189125000103393881 237281250000000000000 330160395 1048576 837 1048576 (ep339 rfl) rfl) (Enclosure.sfrac_false_div 330160395 1048576) (BSN.cos_reduce0 qz872 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 106721500169634253373440) qz271) 226375608064910080 72057594037927936 Bool.false 797775 1048576 50 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q0 330160395 1048576 226375608064910080 72057594037927936 50 106721500169634253373440 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 797775 1048576 106721500169634253373440 151115727451828646838272 1516603733 2147483648 273615 273348 (ep343 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep345 := nat_lit 5290399669116509249351575061056313521

noncomputable def ep346 := BSN.sin_dyadic_bound_f 1516603733 2147483648 2 1 1048576 273615 ep345 ep105 ep345 ep345 ep106 ep345 680489 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1516603733) qz272 0 1 ep345 ep105 ep345 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1516603733) qz273 0 1 ep345 ep106 ep345 rfl rfl rfl rfl) rfl rfl

noncomputable def ep347 := @Enclosure.Real.IsNear.sin_image qz324 qz872 Bool.false 330160395 1048576 837 1048576 Bool.false 680489 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz324 Bool.false 1772535126886935903 5629499534213120 189125000103393881 237281250000000000000 330160395 1048576 837 1048576 (ep339 rfl) rfl) (Enclosure.sfrac_false_div 330160395 1048576) (BSN.sin_reduce0 qz872 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 106721500169634253373440) qz271) 226375608064910080 72057594037927936 Bool.false 680489 1048576 50 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q0 330160395 1048576 226375608064910080 72057594037927936 50 106721500169634253373440 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 680489 1048576 106721500169634253373440 151115727451828646838272 1516603733 2147483648 273615 273348 (ep346 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz579 := (@Enclosure.Real.IsNear.recentre' qz323 Bool.false 247151 1048576 1 1048576 247151 1048576 1 1048576 (ep337 rfl rfl) rfl)

noncomputable def ep348 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz323 (Real.cos qz324)) (@HMul.hMul Real Real Real qz0 qz323 (@Neg.neg Real Real.instNeg (Real.sin qz324))) Bool.false 197170889025 1099511627776 4773571175813 25045775369109504 Bool.true 168183536839 1099511627776 4770899518019 25045775369109504 (@Enclosure.Real.IsNear.mulLit_ff qz323 (Real.cos qz324) 247151 1048576 1 1048576 797775 1048576 57722357 71656538112 197170889025 1099511627776 4773571175813 25045775369109504 qz579 (@Enclosure.Real.IsNear.recentre' (Real.cos qz324) Bool.false 797775 1048576 115444714 143313076224 797775 1048576 57722357 71656538112 (ep344 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz323 (@Neg.neg Real Real.instNeg (Real.sin qz324)) 247151 1048576 1 1048576 680489 1048576 57722357 71656538112 168183536839 1099511627776 4770899518019 25045775369109504 qz579 (@Enclosure.Real.IsNear.neg (Real.sin qz324) Bool.false 680489 1048576 57722357 71656538112 (@Enclosure.Real.IsNear.recentre' (Real.sin qz324) Bool.false 680489 1048576 115444714 143313076224 680489 1048576 57722357 71656538112 (ep347 rfl rfl) rfl)) rfl)

noncomputable def ep349 := @ep317 197170889025 1099511627776 4773571175813 25045775369109504 Bool.true 168183536839 1099511627776 4770899518019 25045775369109504 Bool.false ep318 2687750830031 549755813888 186346582703209 37568663053664256 Bool.true 220697837162457980731392 25090439199 137438953472 186153967351639 37568663053664256 (ep319 (BSN.head_sum_c_succ qz12 17 18 rfl rfl) (ep335 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep336 ep348) rfl rfl

noncomputable abbrev qz873 := (@Nat.cast Real Real.instNatCast 19)

noncomputable abbrev qz326 := (@Inv.inv Real Real.instInv (Real.sqrt qz873))

noncomputable abbrev qz327 := (@HMul.hMul Real Real Real qz0 qz9 (Real.log (Enclosure.sfrac Bool.false 19 1)))

noncomputable def ep350 := @Enclosure.Complex.IsNear.of_eq qz864 (Complex.mk (@HMul.hMul Real Real Real qz0 qz326 (Real.cos qz327)) (@HMul.hMul Real Real Real qz0 qz326 (@Neg.neg Real Real.instNeg (Real.sin qz327)))) Bool.false 119996362057 549755813888 6968713592951 37568663053664256 Bool.true 77657015821 1099511627776 13891311533203 75137326107328512 (BSN.cpow_neg_s_mk qz9 108936 1000 19 (@Eq.refl Real qz9) rfl)

noncomputable abbrev qz874 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 19) qz265)

noncomputable def ep351 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz873) 4570637 1048576 1 1048576 120279 120280 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz873) (Real.sqrt qz874) Bool.false 4570637 1048576 1 1048576 (BSN.sqrt_natCast_div_one 19) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz874) Bool.false 4570637 1048576 1 1048576 4570637 1048576 1 1048576 (BSN.sqrt_enclosure 19 1 2285318 2285319 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep352 := BSN.log_dyadic_bound 3 35 3 2 22509375 524288 136674 55368 243 90099 38 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 3) (BSN.artanhQ 35) 0 2 55368 22509375 243 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz328 := (Real.log (Enclosure.sfrac Bool.false 19 1))

noncomputable def ep353 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz328 108936 1000 0 1 3315143513283831 1125899906842624 125000000068337 17084250000000000000 45142309220385926727 140737488355328000 189125000103393881 237281250000000000000 qz270 (BSN.isNear_log_sfrac 19 1 3315143513283831 1125899906842624 125000000068337 17084250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz874) Bool.false 55618878793361701994496 18889465931478580854784 1000000000546696 136674000000000000000 3315143513283831 1125899906842624 125000000068337 17084250000000000000 (BSN.log_rat_reduce_isNear 19 1 4 38 32 90099 524288 24973259072661432 36028797018963968 136674 1000000000000000 rfl rfl rfl rfl (ep352 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep354 := nat_lit 203989892938841987489521415732307601

noncomputable def ep355 := BSN.cos_dyadic_bound_f 672050893 2147483648 2 1 1048576 273615 ep354 ep91 ep354 ep354 ep92 ep354 997646 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 672050893) qz266 0 1 ep354 ep91 ep354 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 672050893) qz267 0 1 ep354 ep92 ep354 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz875 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 336336413) qz268)

noncomputable def ep356 := @Enclosure.Real.IsNear.cos_image qz327 qz875 Bool.false 336336413 1048576 209 262144 Bool.false 997646 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz327 Bool.false 45142309220385926727 140737488355328000 189125000103393881 237281250000000000000 336336413 1048576 209 262144 (ep353 rfl) rfl) (Enclosure.sfrac_false_div 336336413 1048576) (BSN.cos_reduce0 qz875 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 47291377390420876066816) qz271) 226375608064910080 72057594037927936 Bool.false 997646 1048576 51 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q0 336336413 1048576 226375608064910080 72057594037927936 51 47291377390420876066816 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 997646 1048576 47291377390420876066816 151115727451828646838272 672050893 2147483648 273615 273348 (ep355 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep357 := BSN.sin_dyadic_bound_f 672050893 2147483648 2 1 1048576 273615 ep354 ep105 ep354 ep354 ep106 ep354 322819 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 672050893) qz272 0 1 ep354 ep105 ep354 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 672050893) qz273 0 1 ep354 ep106 ep354 rfl rfl rfl rfl) rfl rfl

noncomputable def ep358 := @Enclosure.Real.IsNear.sin_image qz327 qz875 Bool.false 336336413 1048576 209 262144 Bool.false 322819 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz327 Bool.false 45142309220385926727 140737488355328000 189125000103393881 237281250000000000000 336336413 1048576 209 262144 (ep353 rfl) rfl) (Enclosure.sfrac_false_div 336336413 1048576) (BSN.sin_reduce0 qz875 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 47291377390420876066816) qz271) 226375608064910080 72057594037927936 Bool.false 322819 1048576 51 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q0 336336413 1048576 226375608064910080 72057594037927936 51 47291377390420876066816 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 322819 1048576 47291377390420876066816 151115727451828646838272 672050893 2147483648 273615 273348 (ep357 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz580 := (@Enclosure.Real.IsNear.recentre' qz326 Bool.false 240559 1048576 1 1048576 240559 1048576 1 1048576 (ep351 rfl rfl) rfl)

noncomputable def ep359 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz326 (Real.cos qz327)) (@HMul.hMul Real Real Real qz0 qz326 (@Neg.neg Real Real.instNeg (Real.sin qz327))) Bool.false 119996362057 549755813888 6968713592951 37568663053664256 Bool.true 77657015821 1099511627776 13891311533203 75137326107328512 (@Enclosure.Real.IsNear.mulLit_ff qz326 (Real.cos qz327) 240559 1048576 1 1048576 498823 524288 14413505 17914134528 119996362057 549755813888 6968713592951 37568663053664256 qz580 (@Enclosure.Real.IsNear.recentre' (Real.cos qz327) Bool.false 997646 1048576 28827010 35828269056 498823 524288 14413505 17914134528 (ep356 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz326 (@Neg.neg Real Real.instNeg (Real.sin qz327)) 240559 1048576 1 1048576 322819 1048576 14413505 17914134528 77657015821 1099511627776 13891311533203 75137326107328512 qz580 (@Enclosure.Real.IsNear.neg (Real.sin qz327) Bool.false 322819 1048576 14413505 17914134528 (@Enclosure.Real.IsNear.recentre' (Real.sin qz327) Bool.false 322819 1048576 28827010 35828269056 322819 1048576 14413505 17914134528 (ep358 rfl rfl) rfl)) rfl)

noncomputable def ep360 := @ep314 119996362057 549755813888 6968713592951 37568663053664256 Bool.true 77657015821 1099511627776 13891311533203 75137326107328512 Bool.false ep315 350968399011 68719476736 671233667695 130446746714112 Bool.true 38260328629504034471936 278380529413 1099511627776 42911027359609 8348591789703168 (ep316 (BSN.head_sum_c_succ qz12 18 19 rfl rfl) (ep349 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep350 ep359) rfl rfl

noncomputable abbrev qz876 := (@Nat.cast Real Real.instNatCast 20)

noncomputable abbrev qz329 := (@Inv.inv Real Real.instInv (Real.sqrt qz876))

noncomputable abbrev qz330 := (@HMul.hMul Real Real Real qz0 qz9 (Real.log (Enclosure.sfrac Bool.false 20 1)))

noncomputable def ep361 := @Enclosure.Complex.IsNear.of_eq qz863 (Complex.mk (@HMul.hMul Real Real Real qz0 qz329 (Real.cos qz330)) (@HMul.hMul Real Real Real qz0 qz329 (@Neg.neg Real Real.instNeg (Real.sin qz330)))) Bool.false 114038921999 549755813888 6792306169727 37568663053664256 Bool.false 91797661597 1099511627776 13544892893281 75137326107328512 (BSN.cpow_neg_s_mk qz9 108936 1000 20 (@Eq.refl Real qz9) rfl)

noncomputable abbrev qz877 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 20) qz265)

noncomputable def ep362 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz876) 4689375 1048576 1 1048576 117234 117235 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz876) (Real.sqrt qz877) Bool.false 4689375 1048576 1 1048576 (BSN.sqrt_natCast_div_one 20) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz877) Bool.false 4689375 1048576 1 1048576 4689375 1048576 1 1048576 (BSN.sqrt_enclosure 20 1 2344687 2344688 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep363 := BSN.log_dyadic_bound 4 36 3 2 25194240 524288 136674 104448 768 116991 40 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 4) (BSN.artanhQ 36) 0 2 104448 25194240 768 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz331 := (Real.log (Enclosure.sfrac Bool.false 20 1))

noncomputable def ep364 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz331 108936 1000 0 1 3372893643545847 1125899906842624 125000000068337 17084250000000000000 45928692744163798599 140737488355328000 189125000103393881 237281250000000000000 qz270 (BSN.isNear_log_sfrac 20 1 3372893643545847 1125899906842624 125000000068337 17084250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz877) Bool.false 56587765202795681021952 18889465931478580854784 1000000000546696 136674000000000000000 3372893643545847 1125899906842624 125000000068337 17084250000000000000 (BSN.log_rat_reduce_isNear 20 1 4 40 32 116991 524288 24973259072661432 36028797018963968 136674 1000000000000000 rfl rfl rfl rfl (ep363 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep365 := nat_lit 2727673096275532962494004435724790490310714254351241689362453995926170483564800

noncomputable def ep366 := nat_lit 1796428375361092317437322057798097597841761817325771502615842348972443443456

noncomputable def ep367 := nat_lit 7140997225256763609446541667376111507083936385120438889706953863622586358046976

noncomputable def ep368 := BSN.sin_dyadic_bound_f 2551533286 2147483648 3 2 1048576 273615 ep365 ep131 ep366 ep367 ep134 ep366 972742 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2551533286) qz272 0 2 ep365 ep131 ep366 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2551533286) qz273 0 2 ep367 ep134 ep366 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz878 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 342195427) qz268)

noncomputable def ep369 := @Enclosure.Real.IsNear.cos_image qz330 qz878 Bool.false 342195427 1048576 209 262144 Bool.false 972742 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz330 Bool.false 45928692744163798599 140737488355328000 189125000103393881 237281250000000000000 342195427 1048576 209 262144 (ep364 rfl) rfl) (Enclosure.sfrac_false_div 342195427 1048576) (BSN.cos_reduce3 qz878 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 179548193132680035958784) qz271) 226375608064910080 72057594037927936 Bool.false 972742 1048576 51 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q3 342195427 1048576 226375608064910080 72057594037927936 51 179548193132680035958784 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 972742 1048576 179548193132680035958784 151115727451828646838272 2551533286 2147483648 273615 273348 (ep368 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep370 := nat_lit 1516172354986567686859974607428349426882770924336167948091414816558526910177536

noncomputable def ep371 := nat_lit 4544924208208980875945049178169452085452629249373852301269012764977635843645696

noncomputable def ep372 := BSN.cos_dyadic_bound_f 2551533286 2147483648 3 2 1048576 273615 ep370 ep138 ep366 ep371 ep140 ep366 391513 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2551533286) qz266 0 2 ep370 ep138 ep366 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2551533286) qz267 0 2 ep371 ep140 ep366 rfl rfl rfl rfl) rfl rfl

noncomputable def ep373 := @Enclosure.Real.IsNear.sin_image qz330 qz878 Bool.false 342195427 1048576 209 262144 Bool.true 391513 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz330 Bool.false 45928692744163798599 140737488355328000 189125000103393881 237281250000000000000 342195427 1048576 209 262144 (ep364 rfl) rfl) (Enclosure.sfrac_false_div 342195427 1048576) (BSN.sin_reduce3 qz878 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 179548193132680035958784) qz271) 226375608064910080 72057594037927936 Bool.false 391513 1048576 51 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q3 342195427 1048576 226375608064910080 72057594037927936 51 179548193132680035958784 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 391513 1048576 179548193132680035958784 151115727451828646838272 2551533286 2147483648 273615 273348 (ep372 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz581 := (@Enclosure.Real.IsNear.recentre' qz329 Bool.false 234469 1048576 1 1048576 234469 1048576 1 1048576 (ep362 rfl rfl) rfl)

noncomputable def ep374 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz329 (Real.cos qz330)) (@HMul.hMul Real Real Real qz0 qz329 (@Neg.neg Real Real.instNeg (Real.sin qz330))) Bool.false 114038921999 549755813888 6792306169727 37568663053664256 Bool.false 91797661597 1099511627776 13544892893281 75137326107328512 (@Enclosure.Real.IsNear.mulLit_ff qz329 (Real.cos qz330) 234469 1048576 1 1048576 486371 524288 14413505 17914134528 114038921999 549755813888 6792306169727 37568663053664256 qz581 (@Enclosure.Real.IsNear.recentre' (Real.cos qz330) Bool.false 972742 1048576 28827010 35828269056 486371 524288 14413505 17914134528 (ep369 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz329 (@Neg.neg Real Real.instNeg (Real.sin qz330)) 234469 1048576 1 1048576 391513 1048576 14413505 17914134528 91797661597 1099511627776 13544892893281 75137326107328512 qz581 (@Enclosure.Real.IsNear.neg (Real.sin qz330) Bool.true 391513 1048576 14413505 17914134528 (@Enclosure.Real.IsNear.recentre' (Real.sin qz330) Bool.true 391513 1048576 28827010 35828269056 391513 1048576 14413505 17914134528 (ep373 rfl rfl) rfl)) rfl)

noncomputable def ep375 := @ep312 114038921999 549755813888 6792306169727 37568663053664256 Bool.false 91797661597 1099511627776 13544892893281 75137326107328512 Bool.false 200783612894569438380032 2921786114087 549755813888 200107602465887 37568663053664256 Bool.true 205150032707484402057216 23322858477 137438953472 199872069564881 37568663053664256 (ep313 (BSN.head_sum_c_succ qz12 19 20 rfl rfl) (ep360 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep361 ep374) rfl rfl

noncomputable abbrev qz879 := (@Nat.cast Real Real.instNatCast 21)

noncomputable abbrev qz332 := (@Inv.inv Real Real.instInv (Real.sqrt qz879))

noncomputable abbrev qz333 := (@HMul.hMul Real Real Real qz0 qz9 (Real.log (Enclosure.sfrac Bool.false 21 1)))

noncomputable def ep376 := @Enclosure.Complex.IsNear.of_eq qz862 (Complex.mk (@HMul.hMul Real Real Real qz0 qz332 (Real.cos qz333)) (@HMul.hMul Real Real Real qz0 qz332 (@Neg.neg Real Real.instNeg (Real.sin qz333)))) Bool.false 13087131101 274877906944 1654912216639 9392165763416064 Bool.false 58538165713 274877906944 1668486268297 9392165763416064 (BSN.cpow_neg_s_mk qz9 108936 1000 21 (@Eq.refl Real qz9) rfl)

noncomputable abbrev qz880 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 21) qz265)

noncomputable def ep377 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz879) 4805179 1048576 1 1048576 114408 114410 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz879) (Real.sqrt qz880) Bool.false 4805179 1048576 1 1048576 (BSN.sqrt_natCast_div_one 21) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz880) Bool.false 4805179 1048576 1 1048576 4805179 1048576 1 1048576 (BSN.sqrt_enclosure 21 1 2402589 2402590 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep378 := BSN.log_dyadic_bound 5 37 3 2 28112415 524288 136674 173000 1875 142571 42 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 5) (BSN.artanhQ 37) 0 2 173000 28112415 1875 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz334 := (Real.log (Enclosure.sfrac Bool.false 21 1))

noncomputable def ep379 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz334 108936 1000 0 1 3427826275261687 1125899906842624 125000000068337 17084250000000000000 46676710390238391879 140737488355328000 189125000103393881 237281250000000000000 qz270 (BSN.isNear_log_sfrac 21 1 3427826275261687 1125899906842624 125000000068337 17084250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz880) Bool.false 57509381830540779323392 18889465931478580854784 1000000000546696 136674000000000000000 3427826275261687 1125899906842624 125000000068337 17084250000000000000 (BSN.log_rat_reduce_isNear 21 1 4 42 32 142571 524288 24973259072661432 36028797018963968 136674 1000000000000000 rfl rfl rfl rfl (ep378 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep380 := nat_lit 49774821795372267525801086364800016

noncomputable def ep381 := BSN.sin_dyadic_bound_f 472337502 2147483648 2 1 1048576 273615 ep380 ep105 ep380 ep380 ep106 ep380 228778 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 472337502) qz272 0 1 ep380 ep105 ep380 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 472337502) qz273 0 1 ep380 ep106 ep380 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz582 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 21735537) (@Nat.cast Real Real.instNatCast 65536))

noncomputable abbrev qz583 := (@Nat.cast Real Real.instNatCast 9444732965739290427392)

noncomputable def ep382 := @Enclosure.Real.IsNear.cos_image qz333 qz582 Bool.false 21735537 65536 837 1048576 Bool.false 228778 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz333 Bool.false 46676710390238391879 140737488355328000 189125000103393881 237281250000000000000 21735537 65536 837 1048576 (ep379 rfl) rfl) (Enclosure.sfrac_false_div 21735537 65536) (BSN.cos_reduce3 qz582 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2077362304773294915584) qz583) 226375608064910080 72057594037927936 Bool.false 228778 1048576 52 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q3 21735537 65536 226375608064910080 72057594037927936 52 2077362304773294915584 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 228778 1048576 2077362304773294915584 9444732965739290427392 472337502 2147483648 273615 273348 (ep381 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep383 := BSN.cos_dyadic_bound_f 472337502 2147483648 2 1 1048576 273615 ep380 ep91 ep380 ep380 ep92 ep380 1023314 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 472337502) qz266 0 1 ep380 ep91 ep380 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 472337502) qz267 0 1 ep380 ep92 ep380 rfl rfl rfl rfl) rfl rfl

noncomputable def ep384 := @Enclosure.Real.IsNear.sin_image qz333 qz582 Bool.false 21735537 65536 837 1048576 Bool.true 1023314 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz333 Bool.false 46676710390238391879 140737488355328000 189125000103393881 237281250000000000000 21735537 65536 837 1048576 (ep379 rfl) rfl) (Enclosure.sfrac_false_div 21735537 65536) (BSN.sin_reduce3 qz582 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2077362304773294915584) qz583) 226375608064910080 72057594037927936 Bool.false 1023314 1048576 52 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q3 21735537 65536 226375608064910080 72057594037927936 52 2077362304773294915584 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1023314 1048576 2077362304773294915584 9444732965739290427392 472337502 2147483648 273615 273348 (ep383 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz584 := (@Enclosure.Real.IsNear.recentre' qz332 Bool.false 228818 1048576 2 1048576 114409 524288 1 524288 (ep377 rfl rfl) rfl)

noncomputable def ep385 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz332 (Real.cos qz333)) (@HMul.hMul Real Real Real qz0 qz332 (@Neg.neg Real Real.instNeg (Real.sin qz333))) Bool.false 13087131101 274877906944 1654912216639 9392165763416064 Bool.false 58538165713 274877906944 1668486268297 9392165763416064 (@Enclosure.Real.IsNear.mulLit_ff qz332 (Real.cos qz333) 114409 524288 1 524288 114389 524288 57722357 71656538112 13087131101 274877906944 1654912216639 9392165763416064 qz584 (@Enclosure.Real.IsNear.recentre' (Real.cos qz333) Bool.false 228778 1048576 115444714 143313076224 114389 524288 57722357 71656538112 (ep382 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz332 (@Neg.neg Real Real.instNeg (Real.sin qz333)) 114409 524288 1 524288 511657 524288 57722357 71656538112 58538165713 274877906944 1668486268297 9392165763416064 qz584 (@Enclosure.Real.IsNear.neg (Real.sin qz333) Bool.true 511657 524288 57722357 71656538112 (@Enclosure.Real.IsNear.recentre' (Real.sin qz333) Bool.true 1023314 1048576 115444714 143313076224 511657 524288 57722357 71656538112 (ep384 rfl rfl) rfl)) rfl)

noncomputable def ep386 := @ep310 13087131101 274877906944 1654912216639 9392165763416064 Bool.false 58538165713 274877906944 1668486268297 9392165763416064 Bool.false 810329177988166966050816 2947960376289 549755813888 68909083777481 12522887684554752 Bool.false 1634485711656345141248 11892448759 274877906944 68848671546023 12522887684554752 (ep311 (BSN.head_sum_c_succ qz12 20 21 rfl rfl) (ep375 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep376 ep385) rfl rfl

noncomputable abbrev qz881 := (@Nat.cast Real Real.instNatCast 22)

noncomputable abbrev qz335 := (@Inv.inv Real Real.instInv (Real.sqrt qz881))

noncomputable abbrev qz336 := (@HMul.hMul Real Real Real qz0 qz9 (Real.log (Enclosure.sfrac Bool.false 22 1)))

noncomputable def ep387 := @Enclosure.Complex.IsNear.of_eq qz861 (Complex.mk (@HMul.hMul Real Real Real qz0 qz335 (Real.cos qz336)) (@HMul.hMul Real Real Real qz0 qz335 (@Neg.neg Real Real.instNeg (Real.sin qz336)))) Bool.true 12292728759 68719476736 6482208516055 37568663053664256 Bool.false 127540386285 1099511627776 12943281286391 75137326107328512 (BSN.cpow_neg_s_mk qz9 108936 1000 22 (@Eq.refl Real qz9) rfl)

noncomputable abbrev qz882 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 22) qz265)

noncomputable def ep388 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz881) 4918257 1048576 1 1048576 111778 111779 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz881) (Real.sqrt qz882) Bool.false 4918257 1048576 1 1048576 (BSN.sqrt_natCast_div_one 22) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz882) Bool.false 4918257 1048576 1 1048576 4918257 1048576 1 1048576 (BSN.sqrt_enclosure 22 1 2459128 2459129 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep389 := BSN.log_dyadic_bound 6 38 4 3 316148320320 524288 136674 2667271104 699840 166961 44 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 6) (BSN.artanhQ 38) 0 3 2667271104 316148320320 699840 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz337 := (Real.log (Enclosure.sfrac Bool.false 22 1))

noncomputable def ep390 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz337 108936 1000 0 1 3480203401436407 1125899906842624 125000000068337 17084250000000000000 47389929717359554119 140737488355328000 189125000103393881 237281250000000000000 qz270 (BSN.isNear_log_sfrac 22 1 3480203401436407 1125899906842624 125000000068337 17084250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz882) Bool.false 58388124189833310502912 18889465931478580854784 1000000000546696 136674000000000000000 3480203401436407 1125899906842624 125000000068337 17084250000000000000 (BSN.log_rat_reduce_isNear 22 1 4 44 32 166961 524288 24973259072661432 36028797018963968 136674 1000000000000000 rfl rfl rfl rfl (ep389 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep391 := nat_lit 2329495010646102759992769154178093056

noncomputable def ep392 := BSN.cos_dyadic_bound_f 1235422328 2147483648 2 1 1048576 273615 ep391 ep91 ep391 ep391 ep92 ep391 879792 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1235422328) qz266 0 1 ep391 ep91 ep391 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1235422328) qz267 0 1 ep391 ep92 ep391 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz883 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 176541245) qz306)

noncomputable def ep393 := @Enclosure.Real.IsNear.cos_image qz336 qz883 Bool.false 176541245 524288 837 1048576 Bool.true 879792 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz336 Bool.false 47389929717359554119 140737488355328000 189125000103393881 237281250000000000000 176541245 524288 837 1048576 (ep390 rfl) rfl) (Enclosure.sfrac_false_div 176541245 524288) (BSN.cos_reduce2 qz883 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 43467558877736814510080) qz307) 226375608064910080 72057594037927936 Bool.false 879792 1048576 53 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q2 176541245 524288 226375608064910080 72057594037927936 53 43467558877736814510080 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 879792 1048576 43467558877736814510080 75557863725914323419136 1235422328 2147483648 273615 273348 (ep392 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep394 := BSN.sin_dyadic_bound_f 1235422328 2147483648 2 1 1048576 273615 ep391 ep105 ep391 ep391 ep106 ep391 570505 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1235422328) qz272 0 1 ep391 ep105 ep391 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1235422328) qz273 0 1 ep391 ep106 ep391 rfl rfl rfl rfl) rfl rfl

noncomputable def ep395 := @Enclosure.Real.IsNear.sin_image qz336 qz883 Bool.false 176541245 524288 837 1048576 Bool.true 570505 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz336 Bool.false 47389929717359554119 140737488355328000 189125000103393881 237281250000000000000 176541245 524288 837 1048576 (ep390 rfl) rfl) (Enclosure.sfrac_false_div 176541245 524288) (BSN.sin_reduce2 qz883 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 43467558877736814510080) qz307) 226375608064910080 72057594037927936 Bool.false 570505 1048576 53 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q2 176541245 524288 226375608064910080 72057594037927936 53 43467558877736814510080 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 570505 1048576 43467558877736814510080 75557863725914323419136 1235422328 2147483648 273615 273348 (ep394 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz585 := (@Enclosure.Real.IsNear.recentre' qz335 Bool.false 223557 1048576 1 1048576 223557 1048576 1 1048576 (ep388 rfl rfl) rfl)

noncomputable def ep396 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz335 (Real.cos qz336)) (@HMul.hMul Real Real Real qz0 qz335 (@Neg.neg Real Real.instNeg (Real.sin qz336))) Bool.true 12292728759 68719476736 6482208516055 37568663053664256 Bool.false 127540386285 1099511627776 12943281286391 75137326107328512 (@Enclosure.Real.IsNear.mulLit_ft qz335 (Real.cos qz336) 223557 1048576 1 1048576 54987 65536 57722357 71656538112 12292728759 68719476736 6482208516055 37568663053664256 qz585 (@Enclosure.Real.IsNear.recentre' (Real.cos qz336) Bool.true 879792 1048576 115444714 143313076224 54987 65536 57722357 71656538112 (ep393 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz335 (@Neg.neg Real Real.instNeg (Real.sin qz336)) 223557 1048576 1 1048576 570505 1048576 57722357 71656538112 127540386285 1099511627776 12943281286391 75137326107328512 qz585 (@Enclosure.Real.IsNear.neg (Real.sin qz336) Bool.true 570505 1048576 57722357 71656538112 (@Enclosure.Real.IsNear.recentre' (Real.sin qz336) Bool.true 570505 1048576 115444714 143313076224 570505 1048576 57722357 71656538112 (ep395 rfl rfl) rfl)) rfl)

noncomputable def ep397 := @ep308 12292728759 68719476736 6482208516055 37568663053664256 Bool.false 127540386285 1099511627776 12943281286391 75137326107328512 Bool.false 195824295393233272307712 2849618546217 549755813888 106604729924249 18784331526832128 Bool.false 48133920126100804993024 175110181321 1099511627776 426035310562529 75137326107328512 (ep309 (BSN.head_sum_c_succ qz12 21 22 rfl rfl) (ep386 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep387 ep396) rfl rfl

noncomputable abbrev qz884 := (@Nat.cast Real Real.instNatCast 23)

noncomputable abbrev qz338 := (@Inv.inv Real Real.instInv (Real.sqrt qz884))

noncomputable abbrev qz339 := (@HMul.hMul Real Real Real qz0 qz9 (Real.log (Enclosure.sfrac Bool.false 23 1)))

noncomputable def ep398 := @Enclosure.Complex.IsNear.of_eq qz860 (Complex.mk (@HMul.hMul Real Real Real qz0 qz338 (Real.cos qz339)) (@HMul.hMul Real Real Real qz0 qz338 (@Neg.neg Real Real.instNeg (Real.sin qz339)))) Bool.true 74301669333 549755813888 6333546543001 37568663053664256 Bool.true 10911378915 68719476736 3168803187917 18784331526832128 (BSN.cpow_neg_s_mk qz9 108936 1000 23 (@Eq.refl Real qz9) rfl)

noncomputable abbrev qz885 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 23) qz265)

noncomputable def ep399 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz884) 5028793 1048576 1 1048576 109321 109322 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz884) (Real.sqrt qz885) Bool.false 5028793 1048576 1 1048576 (BSN.sqrt_natCast_div_one 23) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz885) Bool.false 5028793 1048576 1 1048576 5028793 1048576 1 1048576 (BSN.sqrt_enclosure 23 1 2514396 2514397 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep400 := BSN.log_dyadic_bound 7 39 4 3 369468094905 524288 136674 4046006391 1764735 190266 46 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 7) (BSN.artanhQ 39) 0 3 4046006391 369468094905 1764735 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz340 := (Real.log (Enclosure.sfrac Bool.false 23 1))

noncomputable def ep401 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz340 108936 1000 0 1 3530250507853047 1125899906842624 125000000068337 17084250000000000000 48071421165434940999 140737488355328000 189125000103393881 237281250000000000000 qz270 (BSN.isNear_log_sfrac 23 1 3530250507853047 1125899906842624 125000000068337 17084250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz885) Bool.false 59227775304360265777152 18889465931478580854784 1000000000546696 136674000000000000000 3530250507853047 1125899906842624 125000000068337 17084250000000000000 (BSN.log_rat_reduce_isNear 23 1 4 46 32 190266 524288 24973259072661432 36028797018963968 136674 1000000000000000 rfl rfl rfl rfl (ep400 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep402 := nat_lit 5259417037983377740863346153107650625

noncomputable def ep403 := BSN.sin_dyadic_bound_f 1514378385 2147483648 2 1 1048576 273615 ep402 ep105 ep402 ep402 ep106 ep402 679662 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1514378385) qz272 0 1 ep402 ep105 ep402 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1514378385) qz273 0 1 ep402 ep106 ep402 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz886 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 358159997) qz268)

noncomputable def ep404 := @Enclosure.Real.IsNear.cos_image qz339 qz886 Bool.false 358159997 1048576 837 1048576 Bool.true 679662 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz339 Bool.false 48071421165434940999 140737488355328000 189125000103393881 237281250000000000000 358159997 1048576 837 1048576 (ep401 rfl) rfl) (Enclosure.sfrac_false_div 358159997 1048576) (BSN.cos_reduce1 qz886 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 106564905210134893953024) qz271) 226375608064910080 72057594037927936 Bool.false 679662 1048576 54 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q1 358159997 1048576 226375608064910080 72057594037927936 54 106564905210134893953024 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 679662 1048576 106564905210134893953024 151115727451828646838272 1514378385 2147483648 273615 273348 (ep403 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep405 := nat_lit 187944783690055414507311182522436827478296163423518080672090635446475971690625

noncomputable def ep406 := nat_lit 27661467579429846658173539474191074762844153726729953914935179907062890625

noncomputable def ep407 := nat_lit 563779028135007383828617200488362100285362801963100782108442035979613789290625

noncomputable def ep408 := BSN.cos_dyadic_bound_f 1514378385 2147483648 3 2 1048576 273615 ep405 ep138 ep406 ep407 ep140 ep406 798480 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1514378385) qz266 0 2 ep405 ep138 ep406 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1514378385) qz267 0 2 ep407 ep140 ep406 rfl rfl rfl rfl) rfl rfl

noncomputable def ep409 := @Enclosure.Real.IsNear.sin_image qz339 qz886 Bool.false 358159997 1048576 837 1048576 Bool.false 798480 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz339 Bool.false 48071421165434940999 140737488355328000 189125000103393881 237281250000000000000 358159997 1048576 837 1048576 (ep401 rfl) rfl) (Enclosure.sfrac_false_div 358159997 1048576) (BSN.sin_reduce1 qz886 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 106564905210134893953024) qz271) 226375608064910080 72057594037927936 Bool.false 798480 1048576 54 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q1 358159997 1048576 226375608064910080 72057594037927936 54 106564905210134893953024 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 798480 1048576 106564905210134893953024 151115727451828646838272 1514378385 2147483648 273615 273348 (ep408 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz586 := (@Enclosure.Real.IsNear.recentre' qz338 Bool.false 218643 1048576 1 1048576 218643 1048576 1 1048576 (ep399 rfl rfl) rfl)

noncomputable def ep410 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz338 (Real.cos qz339)) (@HMul.hMul Real Real Real qz0 qz338 (@Neg.neg Real Real.instNeg (Real.sin qz339))) Bool.true 74301669333 549755813888 6333546543001 37568663053664256 Bool.true 10911378915 68719476736 3168803187917 18784331526832128 (@Enclosure.Real.IsNear.mulLit_ft qz338 (Real.cos qz339) 218643 1048576 1 1048576 339831 524288 57722357 71656538112 74301669333 549755813888 6333546543001 37568663053664256 qz586 (@Enclosure.Real.IsNear.recentre' (Real.cos qz339) Bool.true 679662 1048576 115444714 143313076224 339831 524288 57722357 71656538112 (ep404 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz338 (@Neg.neg Real Real.instNeg (Real.sin qz339)) 218643 1048576 1 1048576 49905 65536 57722357 71656538112 10911378915 68719476736 3168803187917 18784331526832128 qz586 (@Enclosure.Real.IsNear.neg (Real.sin qz339) Bool.false 49905 65536 57722357 71656538112 (@Enclosure.Real.IsNear.recentre' (Real.sin qz339) Bool.false 798480 1048576 115444714 143313076224 49905 65536 57722357 71656538112 (ep409 rfl rfl) rfl)) rfl)

noncomputable def ep411 := @ep305 74301669333 549755813888 6333546543001 37568663053664256 Bool.true 10911378915 68719476736 3168803187917 18784331526832128 Bool.false ep306 693829219221 137438953472 219543006391499 37568663053664256 Bool.false 36292039412826505216 528118681 1099511627776 438710523314197 75137326107328512 (ep307 (BSN.head_sum_c_succ qz12 22 23 rfl rfl) (ep397 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep398 ep410) rfl rfl

noncomputable abbrev qz887 := (@Nat.cast Real Real.instNatCast 24)

noncomputable abbrev qz341 := (@Inv.inv Real Real.instInv (Real.sqrt qz887))

noncomputable abbrev qz342 := (@HMul.hMul Real Real Real qz0 qz9 (Real.log (Enclosure.sfrac Bool.false 24 1)))

noncomputable def ep412 := @Enclosure.Complex.IsNear.of_eq qz859 (Complex.mk (@HMul.hMul Real Real Real qz0 qz341 (Real.cos qz342)) (@HMul.hMul Real Real Real qz0 qz341 (@Neg.neg Real Real.instNeg (Real.sin qz342)))) Bool.false 181459053615 1099511627776 12412828375825 75137326107328512 Bool.true 66038094787 549755813888 6198530865761 37568663053664256 (BSN.cpow_neg_s_mk qz9 108936 1000 24 (@Eq.refl Real qz9) rfl)

noncomputable abbrev qz888 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 24) qz265)

noncomputable def ep413 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz887) 5136953 1048576 1 1048576 107019 107020 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz887) (Real.sqrt qz888) Bool.false 5136953 1048576 1 1048576 (BSN.sqrt_natCast_div_one 24) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz888) Bool.false 5136953 1048576 1 1048576 5136953 1048576 1 1048576 (BSN.sqrt_enclosure 24 1 2568476 2568477 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep414 := BSN.log_dyadic_bound 8 40 4 3 430080000000 524288 136674 5875957760 3932160 212580 48 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 8) (BSN.artanhQ 40) 0 3 5875957760 430080000000 3932160 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz343 := (Real.log (Enclosure.sfrac Bool.false 24 1))

noncomputable def ep415 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz343 108936 1000 0 1 3578169457974519 1125899906842624 125000000068337 17084250000000000000 48723933509239025223 140737488355328000 189125000103393881 237281250000000000000 qz270 (BSN.isNear_log_sfrac 24 1 3578169457974519 1125899906842624 125000000068337 17084250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz888) Bool.false 60031721881041427759104 18889465931478580854784 1000000000546696 136674000000000000000 3578169457974519 1125899906842624 125000000068337 17084250000000000000 (BSN.log_rat_reduce_isNear 24 1 4 48 32 212580 524288 24973259072661432 36028797018963968 136674 1000000000000000 rfl rfl rfl rfl (ep414 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep416 := nat_lit 3332825766096630115784112435569000625

noncomputable def ep417 := BSN.cos_dyadic_bound_f 1351148715 2147483648 2 1 1048576 273615 ep416 ep91 ep416 ep416 ep92 ep416 847785 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1351148715) qz266 0 1 ep416 ep91 ep416 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1351148715) qz267 0 1 ep416 ep92 ep416 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz889 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 363021593) qz268)

noncomputable def ep418 := @Enclosure.Real.IsNear.cos_image qz342 qz889 Bool.false 363021593 1048576 837 1048576 Bool.false 847785 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz342 Bool.false 48723933509239025223 140737488355328000 189125000103393881 237281250000000000000 363021593 1048576 837 1048576 (ep415 rfl) rfl) (Enclosure.sfrac_false_div 363021593 1048576) (BSN.cos_reduce0 qz889 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 95078638292150041706496) qz271) 226375608064910080 72057594037927936 Bool.false 847785 1048576 55 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q0 363021593 1048576 226375608064910080 72057594037927936 55 95078638292150041706496 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 847785 1048576 95078638292150041706496 151115727451828646838272 1351148715 2147483648 273615 273348 (ep417 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep419 := BSN.sin_dyadic_bound_f 1351148715 2147483648 2 1 1048576 273615 ep416 ep105 ep416 ep416 ep106 ep416 617066 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1351148715) qz272 0 1 ep416 ep105 ep416 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1351148715) qz273 0 1 ep416 ep106 ep416 rfl rfl rfl rfl) rfl rfl

noncomputable def ep420 := @Enclosure.Real.IsNear.sin_image qz342 qz889 Bool.false 363021593 1048576 837 1048576 Bool.false 617066 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz342 Bool.false 48723933509239025223 140737488355328000 189125000103393881 237281250000000000000 363021593 1048576 837 1048576 (ep415 rfl) rfl) (Enclosure.sfrac_false_div 363021593 1048576) (BSN.sin_reduce0 qz889 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 95078638292150041706496) qz271) 226375608064910080 72057594037927936 Bool.false 617066 1048576 55 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q0 363021593 1048576 226375608064910080 72057594037927936 55 95078638292150041706496 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 617066 1048576 95078638292150041706496 151115727451828646838272 1351148715 2147483648 273615 273348 (ep419 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz587 := (@Enclosure.Real.IsNear.recentre' qz341 Bool.false 214039 1048576 1 1048576 214039 1048576 1 1048576 (ep413 rfl rfl) rfl)

noncomputable def ep421 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz341 (Real.cos qz342)) (@HMul.hMul Real Real Real qz0 qz341 (@Neg.neg Real Real.instNeg (Real.sin qz342))) Bool.false 181459053615 1099511627776 12412828375825 75137326107328512 Bool.true 66038094787 549755813888 6198530865761 37568663053664256 (@Enclosure.Real.IsNear.mulLit_ff qz341 (Real.cos qz342) 214039 1048576 1 1048576 847785 1048576 57722357 71656538112 181459053615 1099511627776 12412828375825 75137326107328512 qz587 (@Enclosure.Real.IsNear.recentre' (Real.cos qz342) Bool.false 847785 1048576 115444714 143313076224 847785 1048576 57722357 71656538112 (ep418 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz341 (@Neg.neg Real Real.instNeg (Real.sin qz342)) 214039 1048576 1 1048576 308533 524288 57722357 71656538112 66038094787 549755813888 6198530865761 37568663053664256 qz587 (@Enclosure.Real.IsNear.neg (Real.sin qz342) Bool.false 308533 524288 57722357 71656538112 (@Enclosure.Real.IsNear.recentre' (Real.sin qz342) Bool.false 617066 1048576 115444714 143313076224 308533 524288 57722357 71656538112 (ep420 rfl rfl) rfl)) rfl)

noncomputable def ep422 := @ep303 181459053615 1099511627776 12412828375825 75137326107328512 Bool.true 66038094787 549755813888 6198530865761 37568663053664256 Bool.false 787812836651097995083776 5732092807383 1099511627776 451498841158823 75137326107328512 Bool.true 72319316779177537961984 131548070893 1099511627776 451107585045719 75137326107328512 (ep304 (BSN.head_sum_c_succ qz12 23 24 rfl rfl) (ep411 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep412 ep421) rfl rfl

theorem EMRow34.d9 : Enclosure.Complex.IsNear (BSN.headSumC qz12 25) Bool.false 5732092807383 1099511627776 451498841158823 75137326107328512 Bool.true 131548070893 1099511627776 451107585045719 75137326107328512 := ep302 (BSN.head_sum_c_succ qz12 24 25 rfl rfl) (ep422 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

theorem EMRow34.d10 : @Eq Nat (BSN.factNat (Nat.mul 2 1)) 2 := @Eq.refl Nat 2

theorem EMRow34.d11 : @Eq Nat (Nat.pow 28 1) 28 := @Eq.refl Nat 28

theorem EMRow34.d12 : @Eq Nat (BSN.factNat (Nat.mul 2 2)) 24 := @Eq.refl Nat 24

noncomputable abbrev qz18 := (@HAdd.hAdd Complex Complex Complex qz260 qz259 qz551)

noncomputable def ep423 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz3 (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 2)) qz18) Bool.true 6674982429 125000 0 1 Bool.true 10094709415077 7812500 0 1

noncomputable def ep424 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.re qz18)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.im qz18)) 741643881 25000 0 1 370845378 15625 0 1

noncomputable def ep425 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.re qz18) 741643881 62500 0 1 5 2 0 1 741643881 25000

noncomputable abbrev qz588 := (@Nat.cast Complex Complex.instNatCast 1)

noncomputable abbrev qz19 := (@HAdd.hAdd Complex Complex Complex qz260 qz259 qz588)

noncomputable def ep426 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz3 (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)) qz19) Bool.true 741643881 62500 0 1 Bool.false 27234 125 0 1

noncomputable def ep427 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.re qz19)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.im qz19)) 3 4 0 1 185422689 15625 0 1

noncomputable def ep428 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.re qz19) 1 2 0 1 3 2 0 1 3 4

noncomputable def ep429 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)) qz12 Bool.false 1 2 0 1 Bool.false 108936 1000 0 1 (BSN.ascPochhammer_one_eval qz12)

noncomputable abbrev qz344 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz345 := (Enclosure.Real.IsNear.const Bool.false 1 2)

noncomputable def ep430 := ep429 (@Enclosure.Complex.IsNear.of_eq qz12 (Complex.mk qz344 qz9) Bool.false 1 2 0 1 Bool.false 108936 1000 0 1 (BSN.s_crit_mk qz9 Bool.false 108936 1000 (@Eq.refl Real qz9)) (@Enclosure.Complex.IsNear.mk qz344 qz9 Bool.false 1 2 0 1 Bool.false 108936 1000 0 1 qz345 qz270))

noncomputable def ep431 := @ep428 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 108936 1000 0 1 ep430)

noncomputable def ep432 := @Enclosure.Complex.IsNear.of_eq qz19 (Complex.mk (Enclosure.sfrac Bool.false 3 2) qz9) Bool.false 3 2 0 1 Bool.false 108936 1000 0 1 (BSN.s_add_nat_mk qz9 Bool.false 108936 1000 1 (@Eq.refl Real qz9))

noncomputable abbrev qz589 := (ep432 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz9 Bool.false 3 2 0 1 Bool.false 108936 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz270))

noncomputable def ep433 := ep431 (@Enclosure.Complex.IsNear.re_isNear qz19 Bool.false 3 2 0 1 Bool.false 108936 1000 0 1 qz589)

noncomputable def ep434 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.im qz19) 108936 1000 0 1 108936 1000 0 1 185422689 15625

noncomputable def ep435 := @ep434 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 108936 1000 0 1 ep430)

noncomputable def ep436 := ep435 (@Enclosure.Complex.IsNear.im_isNear qz19 Bool.false 3 2 0 1 Bool.false 108936 1000 0 1 qz589)

noncomputable def ep437 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)) qz19 Bool.true 741643881 62500 0 1 Bool.false 27234 125 0 1 (@ep427 741643881 741643881 62500 0 1 (ep433 rfl) (ep436 rfl) rfl rfl)

noncomputable def ep438 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.im qz19)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.re qz19)) 13617 250 0 1 40851 250 0 1

noncomputable def ep439 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.im qz19) 1 2 0 1 108936 1000 0 1 13617 250

noncomputable def ep440 := @ep439 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 108936 1000 0 1 ep430)

noncomputable def ep441 := ep440 (@Enclosure.Complex.IsNear.im_isNear qz19 Bool.false 3 2 0 1 Bool.false 108936 1000 0 1 qz589)

noncomputable def ep442 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.re qz19) 108936 1000 0 1 3 2 0 1 40851 250

noncomputable def ep443 := @ep442 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 108936 1000 0 1 ep430)

noncomputable def ep444 := ep443 (@Enclosure.Complex.IsNear.re_isNear qz19 Bool.false 3 2 0 1 Bool.false 108936 1000 0 1 qz589)

noncomputable abbrev qz590 := (ep426 (BSN.ascPochhammer_succ_eval_c 1 2 qz12 rfl) (ep437 (@ep438 13617000 27234 125 0 1 (ep441 rfl) (ep444 rfl) rfl rfl)))

noncomputable def ep445 := @ep425 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 741643881 62500 0 1 Bool.false 27234 125 0 1 qz590)

noncomputable def ep446 := @Enclosure.Complex.IsNear.of_eq qz18 (Complex.mk (Enclosure.sfrac Bool.false 5 2) qz9) Bool.false 5 2 0 1 Bool.false 108936 1000 0 1 (BSN.s_add_nat_mk qz9 Bool.false 108936 1000 2 (@Eq.refl Real qz9))

noncomputable abbrev qz591 := (ep446 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz9 Bool.false 5 2 0 1 Bool.false 108936 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz270))

noncomputable def ep447 := ep445 (@Enclosure.Complex.IsNear.re_isNear qz18 Bool.false 5 2 0 1 Bool.false 108936 1000 0 1 qz591)

noncomputable def ep448 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.im qz18) 27234 125 0 1 108936 1000 0 1 370845378 15625

noncomputable def ep449 := @ep448 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 741643881 62500 0 1 Bool.false 27234 125 0 1 qz590)

noncomputable def ep450 := ep449 (@Enclosure.Complex.IsNear.im_isNear qz18 Bool.false 5 2 0 1 Bool.false 108936 1000 0 1 qz591)

noncomputable def ep451 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 2)) qz18 Bool.true 6674982429 125000 0 1 Bool.true 10094709415077 7812500 0 1 (@ep424 20859320090625 6674982429 125000 0 1 (ep447 rfl) (ep450 rfl) rfl rfl)

noncomputable def ep452 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.im qz18)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.re qz18)) 10098964727577 7812500 0 1 13617 25 0 1

noncomputable def ep453 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.im qz18) 741643881 62500 0 1 108936 1000 0 1 10098964727577 7812500

noncomputable def ep454 := @ep453 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 741643881 62500 0 1 Bool.false 27234 125 0 1 qz590)

noncomputable def ep455 := ep454 (@Enclosure.Complex.IsNear.im_isNear qz18 Bool.false 5 2 0 1 Bool.false 108936 1000 0 1 qz591)

noncomputable def ep456 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.re qz18) 27234 125 0 1 5 2 0 1 13617 25

noncomputable def ep457 := @ep456 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 741643881 62500 0 1 Bool.false 27234 125 0 1 qz590)

noncomputable def ep458 := ep457 (@Enclosure.Complex.IsNear.re_isNear qz18 Bool.false 5 2 0 1 Bool.false 108936 1000 0 1 qz591)

noncomputable abbrev qz592 := (ep451 (@ep452 252367735376925 10094709415077 7812500 0 1 (ep455 rfl) (ep458 rfl) rfl rfl))

theorem EMRow34.d13 : Enclosure.Complex.IsNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 6674982429 125000 0 1 Bool.true 10094709415077 7812500 0 1 := ep423 (BSN.ascPochhammer_succ_eval_c 2 3 qz12 rfl) qz592

theorem EMRow34.d14 : @Eq Nat (Nat.pow 28 3) 21952 := @Eq.refl Nat 21952

noncomputable def ep459 := nat_lit 17414828329244880285720302694383478842039

noncomputable def ep460 := nat_lit 3352106608095355649687835115520000000000

noncomputable def ep461 := nat_lit 918251322649878589867370689471124918117710970063

noncomputable def ep462 := nat_lit 109579087809033679520171752816476589916160000000000

noncomputable abbrev qz593 := (@instHSub Complex Complex.instSub)

noncomputable abbrev qz20 := qz593

noncomputable abbrev qz21 := (Complex.Stirling.logGammaStirling 2 qz255)

noncomputable abbrev qz594 := (@HAdd.hAdd Complex Complex Complex qz811 qz812 (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I (@HDiv.hDiv Complex Complex Complex qz813 (↑(Enclosure.sfrac Bool.false 108936 1000)) (2 : Complex))))

noncomputable abbrev qz346 := qz594

noncomputable abbrev qz22 := qz346

noncomputable abbrev qz347 := (@instHSub Real Real.instSub)

noncomputable abbrev qz348 := (@HMul.hMul Real Real Real qz0 (@HDiv.hDiv Real Real Real qz1 qz9 (2 : Real)) (Real.log Real.pi))

noncomputable def ep463 := Complex.re (@HMul.hMul Complex Complex Complex qz3 (Complex.exp (@HMul.hMul Complex Complex Complex qz3 Complex.I ↑(@HSub.hSub Real Real Real qz347 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz21 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz22 (@Nat.cast Complex Complex.instNatCast j))))) qz348))) (zetaApproximant qz12 2 28))

noncomputable def ep464 := @Enclosure.Real.IsNear.of_eq ep463 (@HSub.hSub Real Real Real qz347 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz347 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz21 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz22 (@Nat.cast Complex Complex.instNatCast j))))) qz348)) (Complex.re (zetaApproximant qz12 2 28))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz347 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz21 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz22 (@Nat.cast Complex Complex.instNatCast j))))) qz348)) (Complex.im (zetaApproximant qz12 2 28))))

noncomputable def ep465 := nat_lit 43537067792303761825462013426349156951

noncomputable def ep466 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz347 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz21 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz22 (@Nat.cast Complex Complex.instNatCast j))))) qz348)) (Complex.re (zetaApproximant qz12 2 28))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz347 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz21 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz22 (@Nat.cast Complex Complex.instNatCast j))))) qz348)) (Complex.im (zetaApproximant qz12 2 28))) ep465

noncomputable def ep467 := nat_lit 8380266520238389124219587788800000000

noncomputable def ep468 := nat_lit 11469352102051945777256117776773149405608800971

noncomputable def ep469 := nat_lit 1369738597612920994002146910205957373952000000000

noncomputable def ep470 := nat_lit 1212323375555535497323843816061639

noncomputable def ep471 := nat_lit 703154485722927686881267329272965669006892383

noncomputable def ep472 := nat_lit 145940902803269912813673040991955874085058750959432561882010928493363200000000

noncomputable def ep473 := @Enclosure.Real.IsNear.mulLit_ff (Real.cos (@HSub.hSub Real Real Real qz347 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz21 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz22 (@Nat.cast Complex Complex.instNatCast j))))) qz348)) (Complex.re (zetaApproximant qz12 2 28)) 1048575 1048576 24647249

noncomputable def ep474 := nat_lit 1038005574048202604140428997123457

noncomputable def ep475 := nat_lit 199801123624763229470720000000000

noncomputable def ep476 := nat_lit 1258586205425053068667858014982269889

noncomputable def ep477 := nat_lit 191153331392036227372768296960000000000

noncomputable def ep478 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz347 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz21 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz22 (@Nat.cast Complex Complex.instNatCast j))))) qz348)) Bool.false 1048575 1048576 49294498

noncomputable abbrev qz890 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 105413727) qz268)

noncomputable def ep479 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz347 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz21 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz22 (@Nat.cast Complex Complex.instNatCast j))))) qz348) qz890 Bool.false 105413727 1048576 353

noncomputable def ep480 := nat_lit 4527485135369278518805355069

noncomputable def ep481 := nat_lit 45035996273704960000000000

noncomputable def ep482 := nat_lit 403655052891298405528064987096833

noncomputable def ep483 := nat_lit 1202197217717256192000000000000000000

noncomputable def ep484 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz347 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz21 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz22 (@Nat.cast Complex Complex.instNatCast j))))) qz348) Bool.false ep480 ep481 ep482 ep483

noncomputable def ep485 := nat_lit 7335530512127974372885355069

noncomputable def ep486 := nat_lit 153863800546695781528064987096833

noncomputable def ep487 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz21 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz22 (@Nat.cast Complex Complex.instNatCast j))))) qz348 ep485 ep481 ep486 ep483 1021560957 16384000

noncomputable def ep488 := nat_lit 74178316457890259252106937450496000

noncomputable def ep489 := nat_lit 61709160405909274585724607

noncomputable def ep490 := nat_lit 520069879572229621976107637743231

noncomputable def ep491 := nat_lit 2404394435434512384000000000000000000

noncomputable def ep492 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz20 qz21 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz22 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true ep489 720575940379279360000000 ep490 ep491 Bool.false ep485 ep481

noncomputable def ep493 := nat_lit 50184733075978861465724607

noncomputable def ep494 := nat_lit 55830854830546327155172040588359

noncomputable def ep495 := nat_lit 267154937270501376000000000000000000

noncomputable def ep496 := nat_lit 7612716719896029092885355069

noncomputable def ep497 := nat_lit 45423871499958462364210158237611

noncomputable def ep498 := @Enclosure.Complex.IsNear.subLitP qz21 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz22 (@Nat.cast Complex Complex.instNatCast j))) Bool.true ep493 720575940379279360000000 ep494 ep495 Bool.false ep496 ep481 ep497

noncomputable def ep499 := nat_lit 400732405905752064000000000000000000

noncomputable def ep500 := nat_lit 138956675904699587356928841103417106497536

noncomputable def ep501 := nat_lit 1032384140030764033581669062367734117957632

noncomputable abbrev qz349 := (@HSub.hSub Complex Complex Complex qz593 qz542 qz548)

noncomputable abbrev qz350 := (Complex.log qz542)

noncomputable abbrev qz23 := (@HSub.hSub Complex Complex Complex qz593 (@HMul.hMul Complex Complex Complex qz253 qz349 qz350) qz255)

noncomputable abbrev qz351 := qz548

noncomputable abbrev qz24 := qz351

noncomputable abbrev qz595 := qz813

noncomputable abbrev qz352 := qz595

noncomputable abbrev qz25 := qz352

noncomputable abbrev qz26 := (@instHMul Nat instMulNat)

noncomputable abbrev qz596 := (@instHPow Complex Int (@ZPow.toPow Complex (@DivInvMonoid.toZPow Complex Complex.instDivInvMonoid)))

noncomputable abbrev qz27 := qz596

noncomputable abbrev qz28 := (@instHSub Int Int.instSub)

noncomputable abbrev qz891 := (@OfNat.ofNat Int 1 (@instOfNat 1))

noncomputable abbrev qz353 := qz891

noncomputable abbrev qz29 := qz353

noncomputable abbrev qz30 := (@instHMul Int Int.instMul)

noncomputable abbrev qz597 := (@OfNat.ofNat Int 2 (@instOfNat 2))

noncomputable abbrev qz31 := qz597

noncomputable abbrev qz892 := (@HMul.hMul Complex Complex Complex qz3 qz24 ↑qz251)

noncomputable def ep502 := @Enclosure.Complex.IsNear.of_eq qz21 (@HAdd.hAdd Complex Complex Complex qz13 (@HAdd.hAdd Complex Complex Complex qz13 qz23 qz892) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz20 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz27 qz5 (@HSub.hSub Int Int Int qz28 qz29 (@HMul.hMul Int Int Int qz30 qz31 (@Nat.cast Int instNatCastInt k)))))) Bool.true ep493

noncomputable def ep503 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz13 qz23 qz892) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz20 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz27 qz5 (@HSub.hSub Int Int Int qz28 qz29 (@HMul.hMul Int Int Int qz30 qz31 (@Nat.cast Int instNatCastInt k))))) Bool.true 313655116120505437817 4503599627370496000

noncomputable def ep504 := nat_lit 6485183463413514240000000

noncomputable def ep505 := nat_lit 226011945180666206022639877627526692995072000

noncomputable def ep506 := nat_lit 17142314091500450597677116318654305887322112000

noncomputable def ep507 := @ep503 19041684971401736269 91116000000000000000000 Bool.false 380639260325564695509 2251799813685248000 2582000006866706771 22779000000000000000000 Bool.false 85503302008584995393 720575940379279360000000 1069585269462931 ep504 Bool.true 68486615264817294644931 ep481 95190830961691953 ep481 Bool.true ep505 ep493 720575940379279360000000 ep494 ep495 Bool.false ep506

noncomputable def ep508 := @Enclosure.Complex.IsNear.addLitP qz23 qz892 Bool.true 317793643527715933817 4503599627370496000 4695250001090180161 22779000000000000000000

noncomputable def ep509 := nat_lit 41111403380146888745549824

noncomputable def ep510 := @ep508 Bool.false 380639260325564695509 2251799813685248000 2582000006866706771 22779000000000000000000 Bool.false 120447 131072 3 1048576 Bool.false 0 1 0 1 Bool.true ep509 313655116120505437817 4503599627370496000 19041684971401736269 91116000000000000000000 Bool.false 380639260325564695509 380639260325564695509 2251799813685248000

noncomputable abbrev qz32 := (@HMul.hMul Complex Complex Complex qz253 qz349 qz350)

noncomputable def ep511 := @Enclosure.Complex.IsNear.subLitP qz32 qz5 Bool.true 298653345111391325817 4503599627370496000 4695250001090180161 22779000000000000000000 Bool.false 503290292577372783573

noncomputable def ep512 := nat_lit 1271174574110863735268000

noncomputable def ep513 := nat_lit 1522557041302258782036000

noncomputable def ep514 := @ep511 2251799813685248000 2582000006866706771 22779000000000000000000 Bool.false 17000 4000 0 1 Bool.false 217872 4000 0 1 Bool.true ep512 317793643527715933817 4503599627370496000 4695250001090180161 22779000000000000000000 Bool.false ep513 380639260325564695509 2251799813685248000 2582000006866706771 22779000000000000000000

noncomputable abbrev qz33 := qz349

noncomputable abbrev qz34 := qz350

noncomputable def ep515 := @Enclosure.Complex.IsNear.mul qz33 qz34 Bool.true 298653345111391325817 4503599627370496000 4695250001090180161 22779000000000000000000 Bool.false 503290292577372783573 2251799813685248000 2582000006866706771

noncomputable def ep516 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re qz33) (Complex.re qz34)) (@HMul.hMul Real Real Real qz0 (Complex.im qz33) (Complex.im qz34)) 540519538989706035 36028797018963968 250000000751707 36446400000000000000 11444321483909518131 140737488355328000

noncomputable def ep517 := nat_lit 336253773439153529537716677727223808

noncomputable def ep518 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz33) (Complex.re qz34) 15000 4000 0 1 36034635932647069 9007199254740992 250000000751707 136674000000000000000

noncomputable def ep519 := @Enclosure.Complex.IsNear.re_isNear qz33 Bool.false 15000 4000 0 1 Bool.false 217872 4000 0 1

noncomputable def ep520 := @Enclosure.Complex.IsNear.of_eq qz33 (Complex.mk (Enclosure.sfrac Bool.false 15000 4000) qz258) Bool.false 15000 4000 0 1 Bool.false 217872 4000 0

noncomputable abbrev qz598 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 17000 4000) qz258))

noncomputable def ep521 := @Enclosure.Complex.IsNear.of_eq qz34 qz598 Bool.false 36034635932647069 9007199254740992 250000000751707 136674000000000000000 Bool.false 840443672167843 562949953421312 500000000068337 136674000000000000000

noncomputable def ep522 := nat_lit 28627303561969250708547560593489152685623032616582811591072473415680

noncomputable def ep523 := nat_lit 337682016071015087217381866034256576986376815191306717755066023936

noncomputable def ep524 := nat_lit 170123160762718372967061970043986561726669704215213893736202240

noncomputable def ep525 := BSN.log_dyadic_bound 14989208384 80525208384 4 3 ep522 1048576 273348 ep523 ep524 394975 95514416768 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 14989208384) (BSN.artanhQ 80525208384) 0 3 ep523 ep522 ep524 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz599 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable def ep526 := @Enclosure.Real.IsNear.mulLit_ff qz344 (Real.log (Enclosure.sfrac Bool.false 47757208384 16000000)) 1 2 0 1 36034635932647069 4503599627370496 250000000751707 68337000000000000000 36034635932647069 9007199254740992 250000000751707 136674000000000000000 qz345 (BSN.isNear_log_sfrac 47757208384 16000000 36034635932647069 4503599627370496 250000000751707 68337000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 47757208384) qz599)) Bool.false 302280435261690664189952 37778931862957161709568 1000000003006828 273348000000000000000 36034635932647069 4503599627370496 250000000751707 68337000000000000000 (BSN.log_rat_reduce_isNear 47757208384 16000000 11 95514416768 65536000000 394975 1048576 24973259072661432 36028797018963968 273348 1000000000000000 rfl rfl rfl rfl (ep525 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep527 := BSN.arctan_dyadic_bound_f 17000 217872 1 0 1048576 273348 0 1 1 0 1 1 81651 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 17000) (BSN.arctanEvenQ 217872) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 17000) (BSN.arctanOddQ 217872) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz354 := (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz355 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 2) Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable abbrev qz600 := (@Nat.cast Real Real.instNatCast 17000)

noncomputable abbrev qz601 := (@Nat.cast Real Real.instNatCast 217872)

noncomputable def ep528 := @Enclosure.Real.IsNear.subLit_ff_p qz354 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz600 qz601)) 884279719003555 562949953421312 1 2000000000000000 81651 1048576 1 273348 881269063987068141568 840443672167843 562949953421312 500000000068337 136674000000000000000 qz355 (ep527 rfl) rfl rfl

noncomputable abbrev qz602 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 217872) (@Nat.cast Real Real.instNatCast 17000)))

noncomputable def ep529 := @Enclosure.Complex.IsNear.re_isNear qz34 Bool.false 36034635932647069 9007199254740992 250000000751707 136674000000000000000 Bool.false 840443672167843 562949953421312 500000000068337 136674000000000000000 (ep521 (@congrArg Complex Complex qz5 qz544 Complex.log (BSN.w_shift_mk qz9 Bool.false 108936 1000 4 (@Eq.refl Real qz9) rfl)) (@Enclosure.Complex.IsNear.of_parts qz598 Bool.false 36034635932647069 9007199254740992 250000000751707 136674000000000000000 Bool.false 840443672167843 562949953421312 500000000068337 136674000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz598) (@HMul.hMul Real Real Real qz0 qz344 (Real.log (Enclosure.sfrac Bool.false 47757208384 16000000))) Bool.false 36034635932647069 9007199254740992 250000000751707 136674000000000000000 (Enclosure.clog_re_eq 17000 217872 4000 47757208384 16000000 rfl rfl rfl) (ep526 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz598) qz602 Bool.false 840443672167843 562949953421312 500000000068337 136674000000000000000 (Enclosure.clog_im_eq 17000 217872 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz602 (@HSub.hSub Real Real Real qz347 qz354 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz600 qz601))) Bool.false 840443672167843 562949953421312 500000000068337 136674000000000000000 (BSN.arctan_recip 217872 17000 rfl rfl) ep528))))

noncomputable def ep530 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz33) (Complex.im qz34) 217872 4000 0 1 840443672167843 562949953421312 500000000068337 136674000000000000000

noncomputable def ep531 := @Enclosure.Complex.IsNear.im_isNear qz33 Bool.false 15000 4000 0 1 Bool.false 217872 4000 0 1

noncomputable def ep532 := @Enclosure.Complex.IsNear.im_isNear qz34 Bool.false 36034635932647069 9007199254740992 250000000751707 136674000000000000000 Bool.false 840443672167843 562949953421312 500000000068337 136674000000000000000 (ep521 (@congrArg Complex Complex qz5 qz544 Complex.log (BSN.w_shift_mk qz9 Bool.false 108936 1000 4 (@Eq.refl Real qz9) rfl)) (@Enclosure.Complex.IsNear.of_parts qz598 Bool.false 36034635932647069 9007199254740992 250000000751707 136674000000000000000 Bool.false 840443672167843 562949953421312 500000000068337 136674000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz598) (@HMul.hMul Real Real Real qz0 qz344 (Real.log (Enclosure.sfrac Bool.false 47757208384 16000000))) Bool.false 36034635932647069 9007199254740992 250000000751707 136674000000000000000 (Enclosure.clog_re_eq 17000 217872 4000 47757208384 16000000 rfl rfl rfl) (ep526 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz598) qz602 Bool.false 840443672167843 562949953421312 500000000068337 136674000000000000000 (Enclosure.clog_im_eq 17000 217872 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz602 (@HSub.hSub Real Real Real qz347 qz354 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz600 qz601))) Bool.false 840443672167843 562949953421312 500000000068337 136674000000000000000 (BSN.arctan_recip 217872 17000 rfl rfl) ep528))))

noncomputable abbrev qz356 := (@ep520 1 (BSN.w_sub_half_mk qz9 Bool.false 108936 1000 4 (@Eq.refl Real qz9) rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 15000 4000) (Enclosure.sfrac Bool.false 217872 4000) Bool.false 15000 4000 0 1 Bool.false 217872 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 15000 4000) (Enclosure.Real.IsNear.const Bool.false 217872 4000)))

noncomputable def ep533 := @ep516 756500000103393881 3796500000000000000000 ep517 298653345111391325817 4503599627370496000 4695250001090180161 22779000000000000000000 (@ep518 540519538989706035 36028797018963968 250000000751707 36446400000000000000 (ep519 qz356) ep529 rfl) (@ep530 11444321483909518131 140737488355328000 756500000103393881 3796500000000000000000 (ep531 qz356) ep532 rfl) rfl

noncomputable def ep534 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re qz33) (Complex.im qz34)) (@HMul.hMul Real Real Real qz0 (Complex.im qz33) (Complex.re qz34)) 12606655082517645 2251799813685248 500000000068337 36446400000000000000 490683637494855138573 2251799813685248000

noncomputable def ep535 := nat_lit 1133308987055321988489030417046831104

noncomputable def ep536 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz33) (Complex.im qz34) 15000 4000 0 1 840443672167843 562949953421312 500000000068337 136674000000000000000

noncomputable def ep537 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz33) (Complex.re qz34) 217872 4000 0 1 36034635932647069 9007199254740992 250000000751707 136674000000000000000

noncomputable def ep538 := @ep534 378250001137332691 3796500000000000000000 ep535 503290292577372783573 2251799813685248000 2582000006866706771 22779000000000000000000 (@ep536 12606655082517645 2251799813685248 500000000068337 36446400000000000000 (ep519 qz356) ep532 rfl) (@ep537 490683637494855138573 2251799813685248000 378250001137332691 3796500000000000000000 (ep531 qz356) ep529 rfl) rfl

noncomputable def ep539 := ep514 (@ep515 22779000000000000000000 (ep533 rfl) (ep538 rfl)) qz11 rfl rfl rfl rfl rfl rfl

noncomputable def ep540 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re qz24) (Complex.re ↑qz251)) (@HMul.hMul Real Real Real qz0 (Complex.im qz24) (Complex.im ↑qz251)) 120447 131072 3 1048576 0 1 0 1 120447 120447

noncomputable def ep541 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz24) (Complex.re ↑qz251) 1 2 0 1 120447 65536 3 524288 120447 131072 3 1048576

noncomputable abbrev qz357 := (@Enclosure.Complex.IsNear.of_eq qz24 (Complex.mk (Enclosure.sfrac Bool.false 1 2) (Enclosure.sfrac Bool.false 0 1)) Bool.false 1 2 0 1 Bool.false 0 1 0 1 BSN.half_c_mk (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 2) (Enclosure.sfrac Bool.false 0 1) Bool.false 1 2 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 2) (Enclosure.Real.IsNear.const Bool.false 0 1)))

noncomputable def ep542 := ep541 (@Enclosure.Complex.IsNear.re_isNear qz24 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz357) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz251) qz251 Bool.false 120447 65536 3 524288 (Complex.ofReal_re qz251) EMRow34.d4)

noncomputable def ep543 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz24) (Complex.im ↑qz251) 0 1 0 1 0 1 0 1 0 1 0 1

noncomputable def ep544 := ep543 (@Enclosure.Complex.IsNear.im_isNear qz24 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz357) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz251) qz262 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz251) (0 : Real) qz262 (Complex.ofReal_im qz251) Enclosure.sfrac_zero_eq) qz274)

noncomputable def ep545 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re qz24) (Complex.im ↑qz251)) (@HMul.hMul Real Real Real qz0 (Complex.im qz24) (Complex.re ↑qz251)) 0 1 0 1 0 1 0 1 0 0

noncomputable def ep546 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz24) (Complex.im ↑qz251) 1 2 0 1 0 1 0 1 0 1 0 1

noncomputable def ep547 := ep546 (@Enclosure.Complex.IsNear.re_isNear qz24 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz357) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz251) qz262 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz251) (0 : Real) qz262 (Complex.ofReal_im qz251) Enclosure.sfrac_zero_eq) qz274)

noncomputable def ep548 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz24) (Complex.re ↑qz251) 0 1 0 1 120447 65536 3 524288 0 1 0 1

noncomputable def ep549 := ep548 (@Enclosure.Complex.IsNear.im_isNear qz24 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz357) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz251) qz251 Bool.false 120447 65536 3 524288 (Complex.ofReal_re qz251) EMRow34.d4)

noncomputable def ep550 := @ep510 2582000006866706771 22779000000000000000000 (ep539 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz24 (↑qz251) Bool.false 120447 131072 3 1048576 Bool.false 0 1 0 1 (@ep540 131072 3 1048576 (ep542 rfl) (ep544 rfl) rfl rfl) (@ep545 1 0 1 (ep547 rfl) (ep549 rfl) rfl rfl))

noncomputable abbrev qz35 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)

noncomputable abbrev qz36 := (@HMul.hMul Complex Complex Complex qz253 (@HMul.hMul Complex Complex Complex qz253 (2 : Complex) qz551) (@HSub.hSub Complex Complex Complex qz593 (@HMul.hMul Complex Complex Complex qz253 (2 : Complex) qz551) (1 : Complex)))

noncomputable abbrev qz37 := (@HPow.hPow Complex Int Complex qz596 qz255 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) qz353 (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) qz597 (@Nat.cast Int instNatCastInt 2))))

noncomputable def ep551 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz20 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz27 qz5 (@HSub.hSub Int Int Int qz28 qz29 (@HMul.hMul Int Int Int qz30 qz31 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz13 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz20 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz27 qz5 (@HSub.hSub Int Int Int qz28 qz29 (@HMul.hMul Int Int Int qz30 qz31 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz35)) qz36) qz37)) Bool.false 85503302008584995393 720575940379279360000000 1069585269462931 ep504

noncomputable def ep552 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz20 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz27 qz5 (@HSub.hSub Int Int Int qz28 qz29 (@HMul.hMul Int Int Int qz30 qz31 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz35)) qz36) qz37) Bool.false 12230939 103079215104 17 103079215104 Bool.true

noncomputable def ep553 := nat_lit 2161727821137838080000000

noncomputable def ep554 := nat_lit 26440839779535623984345688047616

noncomputable def ep555 := nat_lit 147073886388062329957587288588288000

noncomputable def ep556 := @ep552 3265660713 2147483648000 4539 2147483648000 Bool.false 8524168474986179 ep553 37749462931 ep504 Bool.true 746308923534644931 ep481 1101681691953 ep481 Bool.false ep554 85503302008584995393 720575940379279360000000 1069585269462931 ep504 Bool.true ep555 68486615264817294644931 ep481 95190830961691953

noncomputable abbrev qz38 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)

noncomputable abbrev qz39 := (@HMul.hMul Complex Complex Complex qz253 (@HMul.hMul Complex Complex Complex qz253 (2 : Complex) qz588) (@HSub.hSub Complex Complex Complex qz593 (@HMul.hMul Complex Complex Complex qz253 (2 : Complex) qz588) (1 : Complex)))

noncomputable abbrev qz40 := (@HPow.hPow Complex Int Complex qz596 qz255 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) qz353 (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) qz597 (@Nat.cast Int instNatCastInt 1))))

noncomputable def ep557 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz20 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz27 qz5 (@HSub.hSub Int Int Int qz28 qz29 (@HMul.hMul Int Int Int qz30 qz31 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz13 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz20 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz27 qz5 (@HSub.hSub Int Int Int qz28 qz29 (@HMul.hMul Int Int Int qz30 qz31 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz38)) qz39) qz40)) Bool.false 12230939 103079215104 17 103079215104

noncomputable def ep558 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz20 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz27 qz5 (@HSub.hSub Int Int Int qz28 qz29 (@HMul.hMul Int Int Int qz30 qz31 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz38)) qz39) qz40) Bool.false 0 1 0 1 Bool.false

noncomputable def ep559 := @ep558 0 1 0 1 Bool.false 12230939 103079215104 17 103079215104 Bool.true 3265660713 2147483648000 4539 2147483648000 Bool.false 12230939 12230939 103079215104 17 103079215104 Bool.true 3265660713 3265660713 2147483648000 4539

noncomputable def ep560 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz20 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz27 qz5 (@HSub.hSub Int Int Int qz28 qz29 (@HMul.hMul Int Int Int qz30 qz31 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz262 qz262) Bool.false 0 1 0 1 Bool.false

noncomputable def ep561 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz38)) qz39) qz40 Bool.false 12230939 103079215104 17 103079215104 Bool.true 3265660713 2147483648000 4539 2147483648000

noncomputable def ep562 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz38)) qz39)) (Complex.re qz40)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz38)) qz39)) (Complex.im qz40)) 12230939 103079215104 17 103079215104 0 1 0

noncomputable def ep563 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz38)) qz39)) (Complex.re qz40) 1 12 0 1 12230939 8589934592 17 8589934592 12230939

noncomputable def ep564 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz38)) qz39) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz262) Bool.false 1 12 0 1 Bool.false 0 1 0 1

noncomputable abbrev qz603 := (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 12) qz262 Bool.false 1 12 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 12) qz274)

noncomputable def ep565 := @Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz38)) qz39) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep564 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz603)

noncomputable def ep566 := @Enclosure.Complex.IsNear.re_isNear qz40 Bool.false 12230939 8589934592 17 8589934592 Bool.true 9796982139 536870912000 13617 536870912000

noncomputable def ep567 := @Enclosure.Complex.IsNear.of_eq qz40 (@Inv.inv Complex Complex.instInv qz6) Bool.false 12230939 8589934592 17 8589934592 Bool.true 9796982139 536870912000 13617

noncomputable def ep568 := @Enclosure.Complex.IsNear.of_parts (@Inv.inv Complex Complex.instInv qz6) Bool.false 12230939 8589934592 17 8589934592 Bool.true 9796982139 536870912000 13617

noncomputable abbrev qz358 := (@MonoidWithZeroHom Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz359 := (@MonoidWithZeroHom.funLike Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable def ep569 := @Enclosure.Real.IsNear.mulLit_ff qz7 (@Inv.inv Real Real.instInv (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz6)) 17000 4000 0 1 719467 2147483648 1 2147483648

noncomputable def ep570 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz6)) Bool.false 719467 2147483648 1 2147483648 719467 2147483648 1

noncomputable abbrev qz604 := (@instHAdd Real Real.instAdd)

noncomputable def ep571 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz6) (@HAdd.hAdd Real Real Real qz604 (@HMul.hMul Real Real Real qz0 qz7 qz7) (@HMul.hMul Real Real Real qz0 qz8 qz8)) Bool.false 746206381 250000 0 1

noncomputable def ep572 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz7 qz7) (@HMul.hMul Real Real Real qz0 qz8 qz8) 289 16 0 1 185422689 62500

noncomputable def ep573 := @Enclosure.Real.IsNear.mulLit_ff qz7 qz7 17000 4000 0 1 17000 4000 0 1

noncomputable def ep574 := @Enclosure.Real.IsNear.mulLit_ff qz8 qz8 217872 4000 0 1 217872 4000 0 1

noncomputable def ep575 := @ep572 0 1 2984825524 746206381 250000 0 1 (@ep573 289 16 0 1 (ep32 qz10) (ep32 qz10) rfl) (@ep574 185422689 62500 0 1 (ep37 qz10) (ep37 qz10) rfl)

noncomputable def ep576 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz6) 746206381 250000 0 1 359733 359734 1073741824 (ep571 (Enclosure.Complex.normSq_eq_mul_add_mul qz6) (ep575 rfl rfl)) rfl

noncomputable def ep577 := @Enclosure.Real.IsNear.of_eq (Complex.re (@Inv.inv Complex Complex.instInv qz6)) (@HMul.hMul Real Real Real qz0 qz7 (@Inv.inv Real Real.instInv (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz6))) Bool.false 12230939 8589934592 17 8589934592 (Enclosure.Complex.inv_re_eq_mul qz6) (@ep569 12230939 8589934592 17 8589934592 (ep32 qz10) (@ep570 2147483648 (ep576 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep578 := @Enclosure.Real.IsNear.of_eq (Complex.im (@Inv.inv Complex Complex.instInv qz6)) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz8) (@Inv.inv Real Real.instInv (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz6))) Bool.true 9796982139 536870912000 13617 536870912000 (Enclosure.Complex.inv_im_eq_mul qz6)

noncomputable def ep579 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz8) (@Inv.inv Real Real.instInv (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz6)) 217872 4000 0 1 719467 2147483648 1

noncomputable def ep580 := @ep579 2147483648 9796982139 536870912000 13617 536870912000 (@Enclosure.Real.IsNear.neg qz8 Bool.false 217872 4000 0 1 (ep37 qz10)) (@ep570 2147483648 (ep576 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep581 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz38)) qz39)) (Complex.im qz40) 0 1 0 1 9796982139 536870912000 13617 536870912000 0

noncomputable def ep582 := @Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz38)) qz39) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep564 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz603)

noncomputable def ep583 := @Enclosure.Complex.IsNear.im_isNear qz40 Bool.false 12230939 8589934592 17 8589934592 Bool.true 9796982139 536870912000 13617 536870912000

noncomputable abbrev qz605 := (@ep567 536870912000 (BSN.zpow_one_sub_two_mul qz5 1 1 rfl rfl) (@ep568 536870912000 ep577 (ep578 ep580)))

noncomputable def ep584 := @ep562 1 12230939 12230939 103079215104 17 103079215104 (@ep563 103079215104 17 103079215104 ep565 (ep566 qz605) rfl) (@ep581 1 0 1 ep582 (ep583 qz605) rfl) rfl

noncomputable def ep585 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz38)) qz39)) (Complex.im qz40)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz38)) qz39)) (Complex.re qz40)) 3265660713 2147483648000 4539 2147483648000 0 1 0

noncomputable def ep586 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz38)) qz39)) (Complex.im qz40) 1 12 0 1 9796982139 536870912000 13617 536870912000 3265660713

noncomputable def ep587 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz38)) qz39)) (Complex.re qz40) 0 1 0 1 12230939 8589934592 17 8589934592 0

noncomputable def ep588 := @ep585 1 3265660713 3265660713 2147483648000 4539 2147483648000 (@ep586 2147483648000 4539 2147483648000 ep565 (ep583 qz605) rfl) (@ep587 1 0 1 ep582 (ep566 qz605) rfl) rfl

noncomputable abbrev qz360 := (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 0 1) (Enclosure.sfrac Bool.false 0 1) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 0 1) (Enclosure.Real.IsNear.const Bool.false 0 1))

noncomputable def ep589 := @ep559 2147483648000 (@ep560 0 1 0 1 (BSN.stirling_sum_base qz5) qz360) (ep561 (ep584 rfl) (ep588 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep590 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz35)) qz36) qz37 Bool.false 8524168474986179 ep553 37749462931 ep504 Bool.true 746308923534644931 ep481 1101681691953 ep481

noncomputable def ep591 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz35)) qz36)) (Complex.re qz37)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz35)) qz36)) (Complex.im qz37)) 8524168474986179 ep553 37749462931 ep504 0 1 0

noncomputable def ep592 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz35)) qz36)) (Complex.re qz37) 1 360 0 1 25572505424958537 18014398509481984000000 37749462931 18014398509481984000000 8524168474986179

noncomputable def ep593 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz35)) qz36) (Complex.mk (Enclosure.sfrac Bool.true 1 360) qz262) Bool.true 1 360 0 1 Bool.false 0 1 0 1

noncomputable def ep594 := @Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz35)) qz36) Bool.true 1 360 0 1 Bool.false 0 1 0 1 (ep593 (BSN.stirling_coeff_mk 2 1 30 Bool.true BSN.bern_real_2 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 1 360) qz262 Bool.true 1 360 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.true 1 360) qz274))

noncomputable def ep595 := @Enclosure.Complex.IsNear.re_isNear qz37 Bool.true 25572505424958537 18014398509481984000000 37749462931 18014398509481984000000 Bool.false 6716780311811804379 1125899906842624000000000 9915135227577 1125899906842624000000000

noncomputable def ep596 := @Enclosure.Complex.IsNear.of_eq qz37 (@Inv.inv Complex Complex.instInv qz2) Bool.true 25572505424958537 18014398509481984000000 37749462931 18014398509481984000000 Bool.false 6716780311811804379 1125899906842624000000000 9915135227577

noncomputable def ep597 := @Enclosure.Complex.IsNear.of_parts (@Inv.inv Complex Complex.instInv qz2) Bool.true 25572505424958537 18014398509481984000000 37749462931 18014398509481984000000 Bool.false 6716780311811804379 1125899906842624000000000 9915135227577

noncomputable abbrev qz41 := (Complex.re qz252)

noncomputable def ep598 := @Enclosure.Real.IsNear.mulLit_tf qz41 (@Inv.inv Real Real.instInv (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz2)) 37749462931 1000000 0 1 677427 18014398509481984 1 18014398509481984

noncomputable def ep599 := @Enclosure.Complex.IsNear.re_isNear qz2 Bool.true 37749462931 1000000 0 1 Bool.true 9915135227577 62500000 0 1

noncomputable def ep600 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz2)) Bool.false 677427 18014398509481984 1 18014398509481984 677427 18014398509481984 1

noncomputable def ep601 := nat_lit 415505594317974616430804341

noncomputable abbrev qz42 := (Complex.im qz252)

noncomputable def ep602 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz2) (@HAdd.hAdd Real Real Real qz604 (@HMul.hMul Real Real Real qz0 qz41 qz41) (@HMul.hMul Real Real Real qz0 qz42 qz42)) Bool.false ep601 15625000000000000 0 1

noncomputable def ep603 := nat_lit 98309906581138407581290929

noncomputable def ep604 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz41 qz41) (@HMul.hMul Real Real Real qz0 qz42 qz42) 1425021951578943110761 1000000000000 0 1 ep603 3906250000000000

noncomputable def ep605 := nat_lit 103876398579493654107701085250000000000

noncomputable def ep606 := @Enclosure.Real.IsNear.mulLit_tt qz41 qz41 37749462931 1000000 0 1 37749462931 1000000 0 1

noncomputable def ep607 := @Enclosure.Real.IsNear.mulLit_tt qz42 qz42 9915135227577 62500000 0 1 9915135227577 62500000 0 1

noncomputable def ep608 := @Enclosure.Complex.IsNear.im_isNear qz2 Bool.true 37749462931 1000000 0 1 Bool.true 9915135227577 62500000 0 1

noncomputable def ep609 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz2) ep601 15625000000000000 0 1 338713 338714 9007199254740992 (ep602 (Enclosure.Complex.normSq_eq_mul_add_mul qz2) (@ep604 0 1 ep605 ep601 15625000000000000 0 1 (@ep606 1425021951578943110761 1000000000000 0 1 (ep599 EMRow34.d5) (ep599 EMRow34.d5) rfl) (@ep607 ep603 3906250000000000 0 1 (ep608 EMRow34.d5) (ep608 EMRow34.d5) rfl) rfl rfl)) rfl

noncomputable def ep610 := @Enclosure.Real.IsNear.of_eq (Complex.re (@Inv.inv Complex Complex.instInv qz2)) (@HMul.hMul Real Real Real qz0 qz41 (@Inv.inv Real Real.instInv (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz2))) Bool.true 25572505424958537 18014398509481984000000 37749462931 18014398509481984000000 (Enclosure.Complex.inv_re_eq_mul qz2) (@ep598 25572505424958537 18014398509481984000000 37749462931 18014398509481984000000 (ep599 EMRow34.d5) (@ep600 18014398509481984 (ep609 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep611 := @Enclosure.Real.IsNear.of_eq (Complex.im (@Inv.inv Complex Complex.instInv qz2)) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz42) (@Inv.inv Real Real.instInv (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz2))) Bool.false 6716780311811804379 1125899906842624000000000 9915135227577 1125899906842624000000000 (Enclosure.Complex.inv_im_eq_mul qz2)

noncomputable def ep612 := @Enclosure.Real.IsNear.mulLit_ff (@Neg.neg Real Real.instNeg qz42) (@Inv.inv Real Real.instInv (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz2)) 9915135227577 62500000 0 1 677427 18014398509481984 1

noncomputable def ep613 := @ep612 18014398509481984 6716780311811804379 1125899906842624000000000 9915135227577 1125899906842624000000000 (@Enclosure.Real.IsNear.neg qz42 Bool.true 9915135227577 62500000 0 1 (ep608 EMRow34.d5)) (@ep600 18014398509481984 (ep609 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep614 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz35)) qz36)) (Complex.im qz37) 0 1 0 1 6716780311811804379 1125899906842624000000000 9915135227577 1125899906842624000000000 0

noncomputable def ep615 := @Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz35)) qz36) Bool.true 1 360 0 1 Bool.false 0 1 0 1 (ep593 (BSN.stirling_coeff_mk 2 1 30 Bool.true BSN.bern_real_2 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 1 360) qz262 Bool.true 1 360 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.true 1 360) qz274))

noncomputable def ep616 := @Enclosure.Complex.IsNear.im_isNear qz37 Bool.true 25572505424958537 18014398509481984000000 37749462931 18014398509481984000000 Bool.false 6716780311811804379 1125899906842624000000000 9915135227577 1125899906842624000000000

noncomputable abbrev qz606 := (@ep596 1125899906842624000000000 (BSN.zpow_one_sub_two_mul qz5 2 3 rfl rfl) (@ep597 1125899906842624000000000 ep610 (ep611 ep613)))

noncomputable def ep617 := @ep591 1 8524168474986179 8524168474986179 ep553 37749462931 ep504 (@ep592 ep553 37749462931 ep504 ep594 (ep595 qz606) rfl) (@ep614 1 0 1 ep615 (ep616 qz606) rfl) rfl

noncomputable def ep618 := @Enclosure.Real.IsNear.addLit_tt (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz35)) qz36)) (Complex.im qz37)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz35)) qz36)) (Complex.re qz37)) 746308923534644931 ep481 1101681691953 ep481 0 1 0

noncomputable def ep619 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz35)) qz36)) (Complex.im qz37) 1 360 0 1 6716780311811804379 1125899906842624000000000 9915135227577 1125899906842624000000000 746308923534644931

noncomputable def ep620 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz35)) qz36)) (Complex.re qz37) 0 1 0 1 25572505424958537 18014398509481984000000 37749462931 18014398509481984000000 0

noncomputable def ep621 := @ep618 1 746308923534644931 746308923534644931 ep481 1101681691953 ep481 (@ep619 ep481 1101681691953 ep481 ep594 (ep616 qz606) rfl) (@ep620 1 0 1 ep615 (ep595 qz606) rfl) rfl

noncomputable def ep622 := @ep556 ep481 (@ep557 Bool.true 3265660713 2147483648000 4539 2147483648000 (BSN.stirling_sum_succ qz5 0 1 rfl) (ep589 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep590 (ep617 rfl) (ep621 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep623 := @ep507 ep496 ep481 ep497 ep499 (ep550 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep551 Bool.true 68486615264817294644931 ep481 95190830961691953 ep481 (BSN.stirling_sum_succ qz5 1 2 rfl) (ep622 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep624 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz22 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz9 4) Bool.false 36013835406032541 2251799813685248 250000000751707 34168500000000000000 Bool.false 866206899275171 140737488355328

noncomputable def ep625 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz9 4) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.logSumC qz9 3) (Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz22 qz550))) Bool.false 36013835406032541 2251799813685248 250000000751707 34168500000000000000 Bool.false 866206899275171 140737488355328 500000000068337 34168500000000000000

noncomputable def ep626 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz9 3) (Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz22 qz550)) Bool.false 108032040110177239 9007199254740992 250000000751707 45558000000000000000 Bool.false 2614098015129833 562949953421312 500000000068337 45558000000000000000 Bool.false

noncomputable def ep627 := nat_lit 1297535165718324217280445114482688

noncomputable def ep628 := nat_lit 1950524534400706438657535377408

noncomputable def ep629 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz9 3) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.logSumC qz9 2) (Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz22 qz551))) Bool.false 108032040110177239 9007199254740992 250000000751707 45558000000000000000 Bool.false 2614098015129833 562949953421312 500000000068337 45558000000000000000

noncomputable def ep630 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz9 2) (Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz22 qz551)) Bool.false 36008531121421981 4503599627370496 250000000751707 68337000000000000000 Bool.false 876529718953379 281474976710656 500000000068337 68337000000000000000 Bool.false

noncomputable def ep631 := nat_lit 486533055584268691196950079340544

noncomputable def ep632 := nat_lit 735803177928041819599114600448

noncomputable def ep633 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz9 2) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.logSumC qz9 1) (Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz22 qz588))) Bool.false 36008531121421981 4503599627370496 250000000751707 68337000000000000000 Bool.false 876529718953379 281474976710656 500000000068337 68337000000000000000

noncomputable def ep634 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz9 1) (Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz22 qz588)) Bool.false 36007392955088541 9007199254740992 250000000751707 136674000000000000000 Bool.false 881696296175011 562949953421312 500000000068337 136674000000000000000 Bool.false

noncomputable def ep635 := nat_lit 648672029362379768350253781090304

noncomputable def ep636 := nat_lit 986884728914400812385746026496

noncomputable abbrev qz893 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz22 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep637 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz9 1) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.logSumC qz9 0) qz893) Bool.false 36007392955088541 9007199254740992 250000000751707 136674000000000000000 Bool.false 881696296175011 562949953421312 500000000068337 136674000000000000000

noncomputable def ep638 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz9 0) qz893 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz894 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz258))

noncomputable def ep639 := @Enclosure.Complex.IsNear.of_eq qz893 qz894 Bool.false 36007392955088541 9007199254740992 250000000751707 136674000000000000000 Bool.false 881696296175011 562949953421312 500000000068337 136674000000000000000

noncomputable def ep640 := nat_lit 28018453524893305644363184271211022133738686364492823571421913415680

noncomputable def ep641 := nat_lit 319995306887877471064617236529747364118692992977899473991354023936

noncomputable def ep642 := nat_lit 151429141631443991164890372286733957426182360989953943656202240

noncomputable def ep643 := BSN.log_dyadic_bound 14701208384 80237208384 4 3 ep640 1048576 273348 ep641 ep642 388632 94938416768 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 14701208384) (BSN.artanhQ 80237208384) 0 3 ep641 ep640 ep642 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep644 := @Enclosure.Real.IsNear.mulLit_ff qz344 (Real.log (Enclosure.sfrac Bool.false 47469208384 16000000)) 1 2 0 1 36007392955088541 4503599627370496 250000000751707 68337000000000000000 36007392955088541 9007199254740992 250000000751707 136674000000000000000 qz345 (BSN.isNear_log_sfrac 47469208384 16000000 36007392955088541 4503599627370496 250000000751707 68337000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 47469208384) qz599)) Bool.false 302051904602199375740928 37778931862957161709568 1000000003006828 273348000000000000000 36007392955088541 4503599627370496 250000000751707 68337000000000000000 (BSN.log_rat_reduce_isNear 47469208384 16000000 11 94938416768 65536000000 388632 1048576 24973259072661432 36028797018963968 273348 1000000000000000 rfl rfl rfl rfl (ep643 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep645 := BSN.arctan_dyadic_bound_f 1000 217872 1 0 1048576 273348 0 1 1 0 1 1 4812 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 217872) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 217872) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz895 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable def ep646 := @Enclosure.Real.IsNear.subLit_ff_p qz354 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz895 qz601)) 884279719003555 562949953421312 1 2000000000000000 4812 1048576 1 273348 924525575458008334336 881696296175011 562949953421312 500000000068337 136674000000000000000 qz355 (ep645 rfl) rfl rfl

noncomputable abbrev qz896 := (@HAdd.hAdd Complex Complex Complex qz13 qz22 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz897 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz258)

noncomputable def ep647 := @ep638 36007392955088541 9007199254740992 250000000751707 136674000000000000000 Bool.false 881696296175011 562949953421312 500000000068337 136674000000000000000 Bool.false 36007392955088541 36007392955088541 9007199254740992 250000000751707 136674000000000000000 Bool.false 881696296175011 881696296175011 562949953421312 500000000068337 136674000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz9 0) (Complex.mk qz262 qz262) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz9) qz360) (ep639 (@congrArg Complex Complex qz896 qz897 Complex.log (BSN.w_shift_mk qz9 Bool.false 108936 1000 0 (@Eq.refl Real qz9) rfl)) (@Enclosure.Complex.IsNear.of_parts qz894 Bool.false 36007392955088541 9007199254740992 250000000751707 136674000000000000000 Bool.false 881696296175011 562949953421312 500000000068337 136674000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz894) (@HMul.hMul Real Real Real qz0 qz344 (Real.log (Enclosure.sfrac Bool.false 47469208384 16000000))) Bool.false 36007392955088541 9007199254740992 250000000751707 136674000000000000000 (Enclosure.clog_re_eq 1000 217872 4000 47469208384 16000000 rfl rfl rfl) (ep644 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz894) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz601 qz895)) Bool.false 881696296175011 562949953421312 500000000068337 136674000000000000000 (Enclosure.clog_im_eq 1000 217872 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz601 qz895)) (@HSub.hSub Real Real Real qz347 qz354 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz895 qz601))) Bool.false 881696296175011 562949953421312 500000000068337 136674000000000000000 (BSN.arctan_recip 217872 1000 rfl rfl) ep646)))) rfl rfl

noncomputable abbrev qz898 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz258))

noncomputable def ep648 := @Enclosure.Complex.IsNear.of_eq (Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz22 qz588)) qz898 Bool.false 36009669287755421 9007199254740992 250000000751707 136674000000000000000 Bool.false 871363141731747 562949953421312 500000000068337 136674000000000000000

noncomputable def ep649 := nat_lit 28068775260152363103135491978130891293472617596112324706392793415680

noncomputable def ep650 := nat_lit 321442974472602406048748701223795146543382053282211837638330023936

noncomputable def ep651 := nat_lit 152918474053102564867825544509463359545614850830458939496202240

noncomputable def ep652 := BSN.log_dyadic_bound 14725208384 80261208384 4 3 ep649 1048576 273348 ep650 ep651 389162 94986416768 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 14725208384) (BSN.artanhQ 80261208384) 0 3 ep650 ep649 ep651 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep653 := @Enclosure.Real.IsNear.mulLit_ff qz344 (Real.log (Enclosure.sfrac Bool.false 47493208384 16000000)) 1 2 0 1 36009669287755421 4503599627370496 250000000751707 68337000000000000000 36009669287755421 9007199254740992 250000000751707 136674000000000000000 qz345 (BSN.isNear_log_sfrac 47493208384 16000000 36009669287755421 4503599627370496 250000000751707 68337000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 47493208384) qz599)) Bool.false 302070999864619426643968 37778931862957161709568 1000000003006828 273348000000000000000 36009669287755421 4503599627370496 250000000751707 68337000000000000000 (BSN.log_rat_reduce_isNear 47493208384 16000000 11 94986416768 65536000000 389162 1048576 24973259072661432 36028797018963968 273348 1000000000000000 rfl rfl rfl rfl (ep652 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep654 := BSN.arctan_dyadic_bound_f 5000 217872 1 0 1048576 273348 0 1 1 0 1 1 24059 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 217872) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 217872) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz899 := (@Nat.cast Real Real.instNatCast 5000)

noncomputable def ep655 := @Enclosure.Real.IsNear.subLit_ff_p qz354 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz899 qz601)) 884279719003555 562949953421312 1 2000000000000000 24059 1048576 1 273348 913690477704508342272 871363141731747 562949953421312 500000000068337 136674000000000000000 qz355 (ep654 rfl) rfl rfl

noncomputable abbrev qz900 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz258)

noncomputable def ep656 := @ep634 36009669287755421 9007199254740992 250000000751707 136674000000000000000 Bool.false 871363141731747 562949953421312 500000000068337 136674000000000000000 Bool.false ep635 36008531121421981 4503599627370496 250000000751707 68337000000000000000 Bool.false ep636 876529718953379 281474976710656 500000000068337 68337000000000000000 (ep637 (BSN.log_sum_c_succ qz9 0 1 rfl) (ep647 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep648 (@congrArg Complex Complex (@HAdd.hAdd Complex Complex Complex qz13 qz22 qz588) qz900 Complex.log (BSN.w_shift_mk qz9 Bool.false 108936 1000 1 (@Eq.refl Real qz9) rfl)) (@Enclosure.Complex.IsNear.of_parts qz898 Bool.false 36009669287755421 9007199254740992 250000000751707 136674000000000000000 Bool.false 871363141731747 562949953421312 500000000068337 136674000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz898) (@HMul.hMul Real Real Real qz0 qz344 (Real.log (Enclosure.sfrac Bool.false 47493208384 16000000))) Bool.false 36009669287755421 9007199254740992 250000000751707 136674000000000000000 (Enclosure.clog_re_eq 5000 217872 4000 47493208384 16000000 rfl rfl rfl) (ep653 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz898) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz601 qz899)) Bool.false 871363141731747 562949953421312 500000000068337 136674000000000000000 (Enclosure.clog_im_eq 5000 217872 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz601 qz899)) (@HSub.hSub Real Real Real qz347 qz354 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz899 qz601))) Bool.false 871363141731747 562949953421312 500000000068337 136674000000000000000 (BSN.arctan_recip 217872 5000 rfl rfl) ep655)))) rfl rfl

noncomputable abbrev qz901 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 9000 4000) qz258))

noncomputable def ep657 := @Enclosure.Complex.IsNear.of_eq (Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz22 qz551)) qz901 Bool.false 36014977867333277 9007199254740992 250000000751707 136674000000000000000 Bool.false 861038577223075 562949953421312 500000000068337 136674000000000000000

noncomputable def ep658 := nat_lit 28186485605114653279788827848682179689932239458239576687991513415680

noncomputable def ep659 := nat_lit 324839288243988827346945215827999839625881106646917219481274023936

noncomputable def ep660 := nat_lit 156441113016275734593584902220316132234147662612970596456202240

noncomputable def ep661 := BSN.log_dyadic_bound 14781208384 80317208384 4 3 ep658 1048576 273348 ep659 ep660 390398 95098416768 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 14781208384) (BSN.artanhQ 80317208384) 0 3 ep659 ep658 ep660 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep662 := @Enclosure.Real.IsNear.mulLit_ff qz344 (Real.log (Enclosure.sfrac Bool.false 47549208384 16000000)) 1 2 0 1 36014977867333277 4503599627370496 250000000751707 68337000000000000000 36014977867333277 9007199254740992 250000000751707 136674000000000000000 qz345 (BSN.isNear_log_sfrac 47549208384 16000000 36014977867333277 4503599627370496 250000000751707 68337000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 47549208384) qz599)) Bool.false 302115531457734866108416 37778931862957161709568 1000000003006828 273348000000000000000 36014977867333277 4503599627370496 250000000751707 68337000000000000000 (BSN.log_rat_reduce_isNear 47549208384 16000000 11 95098416768 65536000000 390398 1048576 24973259072661432 36028797018963968 273348 1000000000000000 rfl rfl rfl rfl (ep661 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep663 := BSN.arctan_dyadic_bound_f 9000 217872 1 0 1048576 273348 0 1 1 0 1 1 43290 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 217872) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 217872) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz902 := (@Nat.cast Real Real.instNatCast 9000)

noncomputable def ep664 := @Enclosure.Real.IsNear.subLit_ff_p qz354 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz902 qz601)) 884279719003555 562949953421312 1 2000000000000000 43290 1048576 1 273348 902864387150263091200 861038577223075 562949953421312 500000000068337 136674000000000000000 qz355 (ep663 rfl) rfl rfl

noncomputable abbrev qz903 := (Complex.mk (Enclosure.sfrac Bool.false 9000 4000) qz258)

noncomputable def ep665 := @ep630 36014977867333277 9007199254740992 250000000751707 136674000000000000000 Bool.false 861038577223075 562949953421312 500000000068337 136674000000000000000 Bool.false ep631 108032040110177239 9007199254740992 250000000751707 45558000000000000000 Bool.false ep632 2614098015129833 562949953421312 500000000068337 45558000000000000000 (ep633 (BSN.log_sum_c_succ qz9 1 2 rfl) (ep656 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep657 (@congrArg Complex Complex (@HAdd.hAdd Complex Complex Complex qz13 qz22 qz551) qz903 Complex.log (BSN.w_shift_mk qz9 Bool.false 108936 1000 2 (@Eq.refl Real qz9) rfl)) (@Enclosure.Complex.IsNear.of_parts qz901 Bool.false 36014977867333277 9007199254740992 250000000751707 136674000000000000000 Bool.false 861038577223075 562949953421312 500000000068337 136674000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz901) (@HMul.hMul Real Real Real qz0 qz344 (Real.log (Enclosure.sfrac Bool.false 47549208384 16000000))) Bool.false 36014977867333277 9007199254740992 250000000751707 136674000000000000000 (Enclosure.clog_re_eq 9000 217872 4000 47549208384 16000000 rfl rfl rfl) (ep662 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz901) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz601 qz902)) Bool.false 861038577223075 562949953421312 500000000068337 136674000000000000000 (Enclosure.clog_im_eq 9000 217872 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz601 qz902)) (@HSub.hSub Real Real Real qz347 qz354 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz902 qz601))) Bool.false 861038577223075 562949953421312 500000000068337 136674000000000000000 (BSN.arctan_recip 217872 9000 rfl rfl) ep664)))) rfl rfl

noncomputable abbrev qz607 := (Enclosure.sfrac Bool.false 13000 4000)

noncomputable def ep666 := @Enclosure.Complex.IsNear.of_eq (Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz22 qz550)) (Complex.log (Complex.mk qz607 qz258)) Bool.false 36023301513952925 9007199254740992 250000000751707 136674000000000000000 Bool.false 850729581970851 562949953421312 500000000068337 136674000000000000000

noncomputable def ep667 := nat_lit 28372289985527104135245807219947230480638607609310777916218073415680

noncomputable def ep668 := nat_lit 330228736578713088136105309591153555594721944723159299520186023936

noncomputable def ep669 := nat_lit 162113188030517319117713291042837405386592801508688914536202240

noncomputable def ep670 := BSN.log_dyadic_bound 14869208384 80405208384 4 3 ep667 1048576 273348 ep668 ep669 392336 95274416768 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 14869208384) (BSN.artanhQ 80405208384) 0 3 ep668 ep667 ep669 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep671 := @Enclosure.Real.IsNear.mulLit_ff qz344 (Real.log (Enclosure.sfrac Bool.false 47637208384 16000000)) 1 2 0 1 36023301513952925 4503599627370496 250000000751707 68337000000000000000 36023301513952925 9007199254740992 250000000751707 136674000000000000000 qz345 (BSN.isNear_log_sfrac 47637208384 16000000 36023301513952925 4503599627370496 250000000751707 68337000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 47637208384) qz599)) Bool.false 302185355266357618278400 37778931862957161709568 1000000003006828 273348000000000000000 36023301513952925 4503599627370496 250000000751707 68337000000000000000 (BSN.log_rat_reduce_isNear 47637208384 16000000 11 95274416768 65536000000 392336 1048576 24973259072661432 36028797018963968 273348 1000000000000000 rfl rfl rfl rfl (ep670 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep672 := BSN.arctan_dyadic_bound_f 13000 217872 1 0 1048576 273348 0 1 1 0 1 1 62492 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 13000) (BSN.arctanEvenQ 217872) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 13000) (BSN.arctanOddQ 217872) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz904 := (@Nat.cast Real Real.instNatCast 13000)

noncomputable def ep673 := @Enclosure.Real.IsNear.subLit_ff_p qz354 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz904 qz601)) 884279719003555 562949953421312 1 2000000000000000 62492 1048576 1 273348 892054622144667058176 850729581970851 562949953421312 500000000068337 136674000000000000000 qz355 (ep672 rfl) rfl rfl

noncomputable def ep674 := @ep626 36023301513952925 9007199254740992 250000000751707 136674000000000000000 Bool.false 850729581970851 562949953421312 500000000068337 136674000000000000000 Bool.false ep627 36013835406032541 2251799813685248 250000000751707 34168500000000000000 Bool.false ep628 866206899275171 140737488355328 500000000068337 34168500000000000000 (ep629 (BSN.log_sum_c_succ qz9 2 3 rfl) (ep665 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep666 (@congrArg Complex Complex (@HAdd.hAdd Complex Complex Complex qz13 qz22 qz550) (Complex.mk qz607 qz258) Complex.log (BSN.w_shift_mk qz9 Bool.false 108936 1000 3 (@Eq.refl Real qz9) rfl)) (@Enclosure.Complex.IsNear.of_parts (Complex.log (Complex.mk qz607 qz258)) Bool.false 36023301513952925 9007199254740992 250000000751707 136674000000000000000 Bool.false 850729581970851 562949953421312 500000000068337 136674000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re (Complex.log (Complex.mk qz607 qz258))) (@HMul.hMul Real Real Real qz0 qz344 (Real.log (Enclosure.sfrac Bool.false 47637208384 16000000))) Bool.false 36023301513952925 9007199254740992 250000000751707 136674000000000000000 (Enclosure.clog_re_eq 13000 217872 4000 47637208384 16000000 rfl rfl rfl) (ep671 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im (Complex.log (Complex.mk qz607 qz258))) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz601 qz904)) Bool.false 850729581970851 562949953421312 500000000068337 136674000000000000000 (Enclosure.clog_im_eq 13000 217872 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz601 qz904)) (@HSub.hSub Real Real Real qz347 qz354 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz904 qz601))) Bool.false 850729581970851 562949953421312 500000000068337 136674000000000000000 (BSN.arctan_recip 217872 13000 rfl rfl) ep673)))) rfl rfl

noncomputable def ep675 := @ep498 ep499 Bool.false 36013835406032541 2251799813685248 250000000751707 34168500000000000000 Bool.false 866206899275171 140737488355328 500000000068337 34168500000000000000 Bool.true ep500 ep489 720575940379279360000000 ep490 ep491 Bool.false ep501 ep485 ep481 ep486 ep483 (@ep502 720575940379279360000000 ep494 ep495 Bool.false ep496 ep481 ep497 ep499 (BSN.logGammaStirling_unfold 2 qz5) (ep623 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep624 500000000068337 34168500000000000000 (BSN.log_sum_c_eq qz9 4) (ep625 (BSN.log_sum_c_succ qz9 3 4 rfl) (ep674 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable def ep676 := @Enclosure.Real.IsNear.mulLit_ff (@HDiv.hDiv Real Real Real qz1 qz9 (2 : Real)) (Real.log Real.pi) 108936 2000 0 1 75021 65536 1 262144 1021560957 16384000 13617 65536000 (@Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real qz1 qz9 (2 : Real)) (Enclosure.sfrac Bool.false 108936 2000) Bool.false 108936 2000 0 1 (BSN.t_half_eq qz9 Bool.false 108936 1000 (@Eq.refl Real qz9)) (Enclosure.Real.IsNear.const Bool.false 108936 2000)) EMRow34.d6 rfl

noncomputable def ep677 := @ep487 13617 65536000 ep488 ep480 ep481 ep482 ep483 (@ep492 ep486 ep483 (ep675 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep676 rfl rfl

noncomputable def ep678 := nat_lit 8331202634812780906132958373243277863350327957336236037842387684932423013121985

noncomputable def ep679 := nat_lit 16713547384548618900405798890211000181018206841189943384391880847193996017601

noncomputable def ep680 := nat_lit 21792756395410871275938043493624433737053019934328215428869618986784698564624321

noncomputable def ep681 := BSN.sin_dyadic_bound_f 3371969049 2147483648 3 2 1048576 273615 ep678 ep131 ep679 ep680 ep134 ep679 1048575 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3371969049) qz272 0 2 ep678 ep131 ep679 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3371969049) qz273 0 2 ep680 ep134 ep679 rfl rfl rfl rfl) rfl rfl

noncomputable def ep682 := @ep479 1048576 Bool.false 1048575 1048576 1 136674 (@ep484 105413727 1048576 353 1048576 ep677 rfl) (Enclosure.sfrac_false_div 105413727 1048576) (BSN.cos_reduce3 qz890 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 237281227438843603451904) qz271) 226375608064910080 72057594037927936 Bool.false 1048575 1048576 15 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q3 105413727 1048576 226375608064910080 72057594037927936 15 237281227438843603451904 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1048575 1048576 237281227438843603451904 151115727451828646838272 3371969049 2147483648 273615 273348 (ep681 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep683 := nat_lit 1927382155096240854250944063691

noncomputable def ep684 := nat_lit 3196817977996211671531520000000000

noncomputable def ep685 := nat_lit 10060888745932056584840808289486582091

noncomputable def ep686 := nat_lit 1529226651136289818982146375680000000000

noncomputable abbrev qz608 := (@Nat.cast Complex Complex.instNatCast 28)

noncomputable abbrev qz43 := (@HPow.hPow Complex Complex Complex (@instHPow Complex Complex Complex.instPow) qz608 (@Neg.neg Complex Complex.instNeg qz259))

noncomputable abbrev qz44 := (@HAdd.hAdd Complex Complex Complex qz260 (@HDiv.hDiv Complex Complex Complex qz352 qz608 (@HSub.hSub Complex Complex Complex qz593 qz259 (1 : Complex))) qz351)

noncomputable abbrev qz45 := (@instHSub Nat instSubNat)

noncomputable abbrev qz46 := qz254

noncomputable abbrev qz47 := qz608

noncomputable def ep687 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz12 2 28) (@HAdd.hAdd Complex Complex Complex qz13 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 28, @HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast n) qz15) (@HMul.hMul Complex Complex Complex qz3 qz43 (@HAdd.hAdd Complex Complex Complex qz13 qz44 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1))))))) Bool.false ep474 ep475 ep476

noncomputable def ep688 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 28, @HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast n) qz15) (@HMul.hMul Complex Complex Complex qz3 qz43 (@HAdd.hAdd Complex Complex Complex qz13 qz44 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))))) Bool.false 5727903306599 1099511627776 487236226552475 75137326107328512

noncomputable def ep689 := nat_lit 2857921854389434373226002876543

noncomputable def ep690 := nat_lit 19031476696073146436453764982269889

noncomputable def ep691 := nat_lit 314012297202498924717290944063691

noncomputable def ep692 := nat_lit 152690217320573455458509889486582091

noncomputable def ep693 := nat_lit 1141299198362300547165485243918163427702341632

noncomputable def ep694 := nat_lit 8278043323032354201546907330678186049536

noncomputable def ep695 := @ep688 Bool.true 419290217 4294967296 243415697544655 37568663053664256 Bool.true ep689 ep475 ep690 ep477 Bool.false ep691 ep684 ep692 ep686 Bool.false ep693 ep474 ep475 ep476 ep477 Bool.false ep694 ep683 ep684

noncomputable def ep696 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 28, @HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast n) qz15) (BSN.headSumC qz12 28) Bool.false 5727903306599 1099511627776 487236226552475 75137326107328512 Bool.true 419290217 4294967296 243415697544655

noncomputable abbrev qz905 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 27) qz15)

noncomputable def ep697 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 28) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 27) qz905) Bool.false 5727903306599 1099511627776 487236226552475 75137326107328512 Bool.true 419290217 4294967296 243415697544655 37568663053664256

noncomputable def ep698 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 27) qz905 Bool.false 2797653517935 549755813888 118885738162237 18784331526832128 Bool.false 28782896639 549755813888 118781795125105 18784331526832128 Bool.false

noncomputable def ep699 := nat_lit 3148948144191099646246912

noncomputable abbrev qz906 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 26) qz15)

noncomputable def ep700 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 27) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 26) qz906) Bool.false 2797653517935 549755813888 118885738162237 18784331526832128 Bool.false 28782896639 549755813888 118781795125105 18784331526832128

noncomputable def ep701 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 26) qz906 Bool.false 2905157097759 549755813888 115903825141609 18784331526832128 Bool.false 18492895133 274877906944 231632762711177 37568663053664256 Bool.true

noncomputable abbrev qz907 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 25) qz15)

noncomputable def ep702 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 26) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 25) qz907) Bool.false 2905157097759 549755813888 115903825141609 18784331526832128 Bool.false 18492895133 274877906944 231632762711177 37568663053664256

noncomputable def ep703 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 25) qz907 Bool.false 5732092807383 1099511627776 451498841158823 75137326107328512 Bool.true 131548070893 1099511627776 451107585045719 75137326107328512 Bool.false

noncomputable def ep704 := nat_lit 6388508019003996103507968

noncomputable abbrev qz908 := (@Nat.cast Real Real.instNatCast 25)

noncomputable abbrev qz361 := (@Inv.inv Real Real.instInv (Real.sqrt qz908))

noncomputable abbrev qz362 := (@HMul.hMul Real Real Real qz0 qz9 (Real.log (Enclosure.sfrac Bool.false 25 1)))

noncomputable def ep705 := @Enclosure.Complex.IsNear.of_eq qz907 (Complex.mk (@HMul.hMul Real Real Real qz0 qz361 (Real.cos qz362)) (@HMul.hMul Real Real Real qz0 qz361 (@Neg.neg Real Real.instNeg (Real.sin qz362)))) Bool.false 78221388135 1099511627776 12116459407613 75137326107328512 Bool.false 205519651425 1099511627776 12157940376635 75137326107328512 (BSN.cpow_neg_s_mk qz9 108936 1000 25 (@Eq.refl Real qz9) rfl)

noncomputable abbrev qz909 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 25) qz265)

noncomputable def ep706 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz908) 5242881 1048576 1 1048576 104857 104858 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz908) (Real.sqrt qz909) Bool.false 5242881 1048576 1 1048576 (BSN.sqrt_natCast_div_one 25) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz909) Bool.false 5242881 1048576 1 1048576 5242881 1048576 1 1048576 (BSN.sqrt_enclosure 25 1 2621440 2621441 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep707 := BSN.log_dyadic_bound 9 41 5 4 7545754341519345 524288 136674 124828057765224 4519905705 233982 50 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 9) (BSN.artanhQ 41) 0 4 124828057765224 7545754341519345 4519905705 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz363 := (Real.log (Enclosure.sfrac Bool.false 25 1))

noncomputable def ep708 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz363 108936 1000 0 1 3624129903009015 1125899906842624 125000000068337 17084250000000000000 9869955377854751451 28147497671065600 189125000103393881 237281250000000000000 qz270 (BSN.isNear_log_sfrac 25 1 3624129903009015 1125899906842624 125000000068337 17084250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz909) Bool.false 60802810194841294602240 18889465931478580854784 1000000000546696 136674000000000000000 3624129903009015 1125899906842624 125000000068337 17084250000000000000 (BSN.log_rat_reduce_isNear 25 1 4 50 32 233982 524288 24973259072661432 36028797018963968 136674 1000000000000000 rfl rfl rfl rfl (ep707 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep709 := nat_lit 372020966224472340202673483589796096

noncomputable def ep710 := BSN.sin_dyadic_bound_f 780983492 2147483648 2 1 1048576 273615 ep709 ep105 ep709 ep709 ep106 ep709 372989 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 780983492) qz272 0 1 ep709 ep105 ep709 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 780983492) qz273 0 1 ep709 ep106 ep709 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz910 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 183842245) qz306)

noncomputable def ep711 := @Enclosure.Real.IsNear.cos_image qz362 qz910 Bool.false 183842245 524288 209 262144 Bool.false 372989 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz362 Bool.false 9869955377854751451 28147497671065600 189125000103393881 237281250000000000000 183842245 524288 209 262144 (ep708 rfl) rfl) (Enclosure.sfrac_false_div 183842245 524288) (BSN.cos_reduce3 qz910 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 27478413809340351774720) qz307) 226375608064910080 72057594037927936 Bool.false 372989 1048576 55 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q3 183842245 524288 226375608064910080 72057594037927936 55 27478413809340351774720 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 372989 1048576 27478413809340351774720 75557863725914323419136 780983492 2147483648 273615 273348 (ep710 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep712 := BSN.cos_dyadic_bound_f 780983492 2147483648 2 1 1048576 273615 ep709 ep91 ep709 ep709 ep92 ep709 979995 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 780983492) qz266 0 1 ep709 ep91 ep709 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 780983492) qz267 0 1 ep709 ep92 ep709 rfl rfl rfl rfl) rfl rfl

noncomputable def ep713 := @Enclosure.Real.IsNear.sin_image qz362 qz910 Bool.false 183842245 524288 209 262144 Bool.true 979995 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz362 Bool.false 9869955377854751451 28147497671065600 189125000103393881 237281250000000000000 183842245 524288 209 262144 (ep708 rfl) rfl) (Enclosure.sfrac_false_div 183842245 524288) (BSN.sin_reduce3 qz910 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 27478413809340351774720) qz307) 226375608064910080 72057594037927936 Bool.false 979995 1048576 55 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q3 183842245 524288 226375608064910080 72057594037927936 55 27478413809340351774720 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 979995 1048576 27478413809340351774720 75557863725914323419136 780983492 2147483648 273615 273348 (ep712 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz609 := (@Enclosure.Real.IsNear.recentre' qz361 Bool.false 209715 1048576 1 1048576 209715 1048576 1 1048576 (ep706 rfl rfl) rfl)

noncomputable def ep714 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz361 (Real.cos qz362)) (@HMul.hMul Real Real Real qz0 qz361 (@Neg.neg Real Real.instNeg (Real.sin qz362))) Bool.false 78221388135 1099511627776 12116459407613 75137326107328512 Bool.false 205519651425 1099511627776 12157940376635 75137326107328512 (@Enclosure.Real.IsNear.mulLit_ff qz361 (Real.cos qz362) 209715 1048576 1 1048576 372989 1048576 14413505 17914134528 78221388135 1099511627776 12116459407613 75137326107328512 qz609 (@Enclosure.Real.IsNear.recentre' (Real.cos qz362) Bool.false 372989 1048576 28827010 35828269056 372989 1048576 14413505 17914134528 (ep711 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz361 (@Neg.neg Real Real.instNeg (Real.sin qz362)) 209715 1048576 1 1048576 979995 1048576 14413505 17914134528 205519651425 1099511627776 12157940376635 75137326107328512 qz609 (@Enclosure.Real.IsNear.neg (Real.sin qz362) Bool.true 979995 1048576 14413505 17914134528 (@Enclosure.Real.IsNear.recentre' (Real.sin qz362) Bool.true 979995 1048576 28827010 35828269056 979995 1048576 14413505 17914134528 (ep713 rfl rfl) rfl)) rfl)

noncomputable def ep715 := @ep703 78221388135 1099511627776 12116459407613 75137326107328512 Bool.false 205519651425 1099511627776 12157940376635 75137326107328512 Bool.false ep704 2905157097759 549755813888 115903825141609 18784331526832128 Bool.false 81332612919902792056832 18492895133 274877906944 231632762711177 37568663053664256 EMRow34.d9 (ep705 ep714) rfl rfl

noncomputable abbrev qz911 := (@Nat.cast Real Real.instNatCast 26)

noncomputable abbrev qz364 := (@Inv.inv Real Real.instInv (Real.sqrt qz911))

noncomputable abbrev qz365 := (@HMul.hMul Real Real Real qz0 qz9 (Real.log (Enclosure.sfrac Bool.false 26 1)))

noncomputable def ep716 := @Enclosure.Complex.IsNear.of_eq qz906 (Complex.mk (@HMul.hMul Real Real Real qz0 qz364 (Real.cos qz365)) (@HMul.hMul Real Real Real qz0 qz364 (@Neg.neg Real Real.instNeg (Real.sin qz365)))) Bool.true 6718973739 34359738368 248492751719 1565360960569344 Bool.true 8202893627 549755813888 1976942513011 12522887684554752 (BSN.cpow_neg_s_mk qz9 108936 1000 26 (@Eq.refl Real qz9) rfl)

noncomputable abbrev qz912 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26) qz265)

noncomputable def ep717 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz911) 5346709 1048576 1 1048576 102821 102822 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz911) (Real.sqrt qz912) Bool.false 5346709 1048576 1 1048576 (BSN.sqrt_natCast_div_one 26) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz912) Bool.false 5346709 1048576 1 1048576 5346709 1048576 1 1048576 (BSN.sqrt_enclosure 26 1 2673354 2673355 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep718 := BSN.log_dyadic_bound 10 42 5 4 9150106136613120 524288 136674 179034245376000 10500000000 254545 52 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 10) (BSN.artanhQ 42) 0 4 179034245376000 9150106136613120 10500000000 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz366 := (Real.log (Enclosure.sfrac Bool.false 26 1))

noncomputable def ep719 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz366 108936 1000 0 1 3668288609262839 1125899906842624 125000000068337 17084250000000000000 49951085992332078663 140737488355328000 189125000103393881 237281250000000000000 qz270 (BSN.isNear_log_sfrac 26 1 3668288609262839 1125899906842624 125000000068337 17084250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz912) Bool.false 61543670347942250676224 18889465931478580854784 1000000000546696 136674000000000000000 3668288609262839 1125899906842624 125000000068337 17084250000000000000 (BSN.log_rat_reduce_isNear 26 1 4 52 32 254545 524288 24973259072661432 36028797018963968 136674 1000000000000000 rfl rfl rfl rfl (ep718 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep720 := nat_lit 6837265920335911575725190178674084922826540255657564651131668213679753317580800

noncomputable def ep721 := nat_lit 11264973903973739588402981338604505439551153638324611661040814887734089875456

noncomputable def ep722 := nat_lit 17888886500273334738994274212455338931929284516069667572179350668866832067198976

noncomputable def ep723 := BSN.sin_dyadic_bound_f 3209713536 2147483648 3 2 1048576 273615 ep720 ep131 ep721 ep722 ep134 ep721 1045536 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3209713536) qz272 0 2 ep720 ep131 ep721 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3209713536) qz273 0 2 ep722 ep134 ep721 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz610 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 23260287) (@Nat.cast Real Real.instNatCast 65536))

noncomputable def ep724 := @Enclosure.Real.IsNear.cos_image qz365 qz610 Bool.false 23260287 65536 209 262144 Bool.true 1045536 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz365 Bool.false 49951085992332078663 140737488355328000 189125000103393881 237281250000000000000 23260287 65536 209 262144 (ep719 rfl) rfl) (Enclosure.sfrac_false_div 23260287 65536) (BSN.cos_reduce1 qz610 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14116469421447277707264) qz583) 226375608064910080 72057594037927936 Bool.false 1045536 1048576 56 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q1 23260287 65536 226375608064910080 72057594037927936 56 14116469421447277707264 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1045536 1048576 14116469421447277707264 9444732965739290427392 3209713536 2147483648 273615 273348 (ep723 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep725 := nat_lit 3803487721921716981886618090969426959543433988093457966922500480883300327489536

noncomputable def ep726 := nat_lit 11387933217957203466483048310231071867751199657003724677445419812874432802717696

noncomputable def ep727 := BSN.cos_dyadic_bound_f 3209713536 2147483648 3 2 1048576 273615 ep725 ep138 ep721 ep726 ep140 ep721 79778 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3209713536) qz266 0 2 ep725 ep138 ep721 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3209713536) qz267 0 2 ep726 ep140 ep721 rfl rfl rfl rfl) rfl rfl

noncomputable def ep728 := @Enclosure.Real.IsNear.sin_image qz365 qz610 Bool.false 23260287 65536 209 262144 Bool.false 79778 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz365 Bool.false 49951085992332078663 140737488355328000 189125000103393881 237281250000000000000 23260287 65536 209 262144 (ep719 rfl) rfl) (Enclosure.sfrac_false_div 23260287 65536) (BSN.sin_reduce1 qz610 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14116469421447277707264) qz583) 226375608064910080 72057594037927936 Bool.false 79778 1048576 56 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q1 23260287 65536 226375608064910080 72057594037927936 56 14116469421447277707264 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 79778 1048576 14116469421447277707264 9444732965739290427392 3209713536 2147483648 273615 273348 (ep727 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz611 := (@Enclosure.Real.IsNear.recentre' qz364 Bool.false 205643 1048576 1 1048576 205643 1048576 1 1048576 (ep717 rfl rfl) rfl)

noncomputable def ep729 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz364 (Real.cos qz365)) (@HMul.hMul Real Real Real qz0 qz364 (@Neg.neg Real Real.instNeg (Real.sin qz365))) Bool.true 6718973739 34359738368 248492751719 1565360960569344 Bool.true 8202893627 549755813888 1976942513011 12522887684554752 (@Enclosure.Real.IsNear.mulLit_ft qz364 (Real.cos qz365) 205643 1048576 1 1048576 32673 32768 14413505 17914134528 6718973739 34359738368 248492751719 1565360960569344 qz611 (@Enclosure.Real.IsNear.recentre' (Real.cos qz365) Bool.true 1045536 1048576 28827010 35828269056 32673 32768 14413505 17914134528 (ep724 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz364 (@Neg.neg Real Real.instNeg (Real.sin qz365)) 205643 1048576 1 1048576 39889 524288 14413505 17914134528 8202893627 549755813888 1976942513011 12522887684554752 qz611 (@Enclosure.Real.IsNear.neg (Real.sin qz365) Bool.false 39889 524288 14413505 17914134528 (@Enclosure.Real.IsNear.recentre' (Real.sin qz365) Bool.false 79778 1048576 28827010 35828269056 39889 524288 14413505 17914134528 (ep728 rfl rfl) rfl)) rfl)

noncomputable def ep730 := @ep701 6718973739 34359738368 248492751719 1565360960569344 Bool.true 8202893627 549755813888 1976942513011 12522887684554752 Bool.false 96126642920561395630080 2797653517935 549755813888 118885738162237 18784331526832128 Bool.false 7911782383913812361216 28782896639 549755813888 118781795125105 18784331526832128 (ep702 (BSN.head_sum_c_succ qz12 25 26 rfl rfl) (ep715 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep716 ep729) rfl rfl

noncomputable abbrev qz913 := (@Nat.cast Real Real.instNatCast 27)

noncomputable abbrev qz367 := (@Inv.inv Real Real.instInv (Real.sqrt qz913))

noncomputable abbrev qz368 := (@HMul.hMul Real Real Real qz0 qz9 (Real.log (Enclosure.sfrac Bool.false 27 1)))

noncomputable def ep731 := @Enclosure.Complex.IsNear.of_eq qz905 (Complex.mk (@HMul.hMul Real Real Real qz0 qz367 (Real.cos qz368)) (@HMul.hMul Real Real Real qz0 qz367 (@Neg.neg Real Real.instNeg (Real.sin qz368)))) Bool.false 132596270729 1099511627776 11693273903527 75137326107328512 Bool.true 82452044415 549755813888 5852107294445 37568663053664256 (BSN.cpow_neg_s_mk qz9 108936 1000 27 (@Eq.refl Real qz9) rfl)

noncomputable abbrev qz914 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 27) qz265)

noncomputable def ep732 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz913) 5448561 1048576 1 1048576 100899 100900 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz913) (Real.sqrt qz914) Bool.false 5448561 1048576 1 1048576 (BSN.sqrt_natCast_div_one 27) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz914) Bool.false 5448561 1048576 1 1048576 5448561 1048576 1 1048576 (BSN.sqrt_enclosure 27 1 2724280 2724281 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep733 := BSN.log_dyadic_bound 11 43 5 4 11045349262332945 524288 136674 250863800262504 22507682505 274332 54 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 11) (BSN.artanhQ 43) 0 4 250863800262504 11045349262332945 22507682505 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz369 := (Real.log (Enclosure.sfrac Bool.false 27 1))

noncomputable def ep734 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz369 108936 1000 0 1 3710780868205815 1125899906842624 125000000068337 17084250000000000000 10105940616471716571 28147497671065600 189125000103393881 237281250000000000000 qz270 (BSN.isNear_log_sfrac 27 1 3710780868205815 1125899906842624 125000000068337 17084250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz914) Bool.false 62256572154556490711040 18889465931478580854784 1000000000546696 136674000000000000000 3710780868205815 1125899906842624 125000000068337 17084250000000000000 (BSN.log_rat_reduce_isNear 27 1 4 54 32 274332 524288 24973259072661432 36028797018963968 136674 1000000000000000 rfl rfl rfl rfl (ep733 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep735 := nat_lit 484652903336903012390493412659431128365714758577429795694298950410156147876096

noncomputable def ep736 := nat_lit 183854635793537740761386615522861280056083743907488012476322959071434383616

noncomputable def ep737 := nat_lit 1453591000739121961689957464747247662537032108244474411057944205312325574861056

noncomputable def ep738 := BSN.cos_dyadic_bound_f 1918930842 2147483648 3 2 1048576 273615 ep735 ep138 ep736 ep737 ep140 ep736 657071 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1918930842) qz266 0 2 ep735 ep138 ep736 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1918930842) qz267 0 2 ep737 ep140 ep736 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz915 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 376475625) qz268)

noncomputable def ep739 := @Enclosure.Real.IsNear.cos_image qz368 qz915 Bool.false 376475625 1048576 837 1048576 Bool.false 657071 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz368 Bool.false 10105940616471716571 28147497671065600 189125000103393881 237281250000000000000 376475625 1048576 837 1048576 (ep734 rfl) rfl) (Enclosure.sfrac_false_div 376475625 1048576) (BSN.cos_reduce0 qz915 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 135032753532564154613760) qz271) 226375608064910080 72057594037927936 Bool.false 657071 1048576 57 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q0 376475625 1048576 226375608064910080 72057594037927936 57 135032753532564154613760 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 657071 1048576 135032753532564154613760 151115727451828646838272 1918930842 2147483648 273615 273348 (ep738 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep740 := nat_lit 872228142297790592110279033494557742034241698444247641839757052371023918670080

noncomputable def ep741 := nat_lit 2284109369941023918232355223679661834683875550816226938512497280942756512276736

noncomputable def ep742 := BSN.sin_dyadic_bound_f 1918930842 2147483648 3 2 1048576 273615 ep740 ep131 ep736 ep741 ep134 ep736 817170 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1918930842) qz272 0 2 ep740 ep131 ep736 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1918930842) qz273 0 2 ep741 ep134 ep736 rfl rfl rfl rfl) rfl rfl

noncomputable def ep743 := @Enclosure.Real.IsNear.sin_image qz368 qz915 Bool.false 376475625 1048576 837 1048576 Bool.false 817170 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz368 Bool.false 10105940616471716571 28147497671065600 189125000103393881 237281250000000000000 376475625 1048576 837 1048576 (ep734 rfl) rfl) (Enclosure.sfrac_false_div 376475625 1048576) (BSN.sin_reduce0 qz915 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 135032753532564154613760) qz271) 226375608064910080 72057594037927936 Bool.false 817170 1048576 57 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q0 376475625 1048576 226375608064910080 72057594037927936 57 135032753532564154613760 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 817170 1048576 135032753532564154613760 151115727451828646838272 1918930842 2147483648 273615 273348 (ep742 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz612 := (@Enclosure.Real.IsNear.recentre' qz367 Bool.false 201799 1048576 1 1048576 201799 1048576 1 1048576 (ep732 rfl rfl) rfl)

noncomputable def ep744 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz367 (Real.cos qz368)) (@HMul.hMul Real Real Real qz0 qz367 (@Neg.neg Real Real.instNeg (Real.sin qz368))) Bool.false 132596270729 1099511627776 11693273903527 75137326107328512 Bool.true 82452044415 549755813888 5852107294445 37568663053664256 (@Enclosure.Real.IsNear.mulLit_ff qz367 (Real.cos qz368) 201799 1048576 1 1048576 657071 1048576 57722357 71656538112 132596270729 1099511627776 11693273903527 75137326107328512 qz612 (@Enclosure.Real.IsNear.recentre' (Real.cos qz368) Bool.false 657071 1048576 115444714 143313076224 657071 1048576 57722357 71656538112 (ep739 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz367 (@Neg.neg Real Real.instNeg (Real.sin qz368)) 201799 1048576 1 1048576 408585 524288 57722357 71656538112 82452044415 549755813888 5852107294445 37568663053664256 qz612 (@Enclosure.Real.IsNear.neg (Real.sin qz368) Bool.false 408585 524288 57722357 71656538112 (@Enclosure.Real.IsNear.recentre' (Real.sin qz368) Bool.false 817170 1048576 115444714 143313076224 408585 524288 57722357 71656538112 (ep743 rfl rfl) rfl)) rfl)

noncomputable def ep745 := @ep698 132596270729 1099511627776 11693273903527 75137326107328512 Bool.true 82452044415 549755813888 5852107294445 37568663053664256 Bool.false ep699 5727903306599 1099511627776 487236226552475 75137326107328512 Bool.true 29504926016270225113088 419290217 4294967296 243415697544655 37568663053664256 (ep700 (BSN.head_sum_c_succ qz12 26 27 rfl rfl) (ep730 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep731 ep744) rfl rfl

noncomputable def ep746 := @Enclosure.Complex.IsNear.mul qz43 (@HAdd.hAdd Complex Complex Complex qz13 qz44 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1))))) Bool.true ep689 ep475 ep690 ep477 Bool.false

noncomputable def ep747 := nat_lit 173348483154843372456964370583

noncomputable def ep748 := nat_lit 12787271911984846686126080000000

noncomputable def ep749 := nat_lit 469453872610400575057537317129533

noncomputable def ep750 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re qz43) (Complex.re (@HAdd.hAdd Complex Complex Complex qz13 qz44 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 (Complex.im qz43) (Complex.im (@HAdd.hAdd Complex Complex Complex qz13 qz44 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1))))))) ep747 ep748 ep749

noncomputable def ep751 := nat_lit 6116906604545159275928585502720000000

noncomputable def ep752 := nat_lit 6361705032781556648989795619317

noncomputable def ep753 := nat_lit 228344141285443690823680000000000

noncomputable def ep754 := nat_lit 2492024672570359123374699326841133

noncomputable def ep755 := nat_lit 109230475081163558498724741120000000000

noncomputable def ep756 := nat_lit 41765741548893326952495420367212617864501914433340047360000000

noncomputable def ep757 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz43) (Complex.re (@HAdd.hAdd Complex Complex Complex qz13 qz44 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))))) 14796236721 549755813888 5724349095053 37568663053664256 82010000580870242161

noncomputable abbrev qz370 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 28)))

noncomputable abbrev qz371 := (@HMul.hMul Real Real Real qz0 qz9 (Real.log (Enclosure.sfrac Bool.false 28 1)))

noncomputable abbrev qz916 := (@Neg.neg Real Real.instNeg (Real.sin qz371))

noncomputable def ep758 := @Enclosure.Complex.IsNear.of_eq qz43 (Complex.mk (@HMul.hMul Real Real Real qz0 qz370 (Real.cos qz371)) (@HMul.hMul Real Real Real qz0 qz370 qz916)) Bool.false 14796236721 549755813888 5724349095053 37568663053664256 Bool.false 205670801581 1099511627776 11509419236467 75137326107328512 (BSN.cpow_neg_s_mk qz9 108936 1000 28 (@Eq.refl Real qz9) rfl)

noncomputable abbrev qz613 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 28) qz265)

noncomputable def ep759 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 28)) 5548543 1048576 1 1048576 99081 99082 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 28)) (Real.sqrt qz613) Bool.false 5548543 1048576 1 1048576 (BSN.sqrt_natCast_div_one 28) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz613) Bool.false 5548543 1048576 1 1048576 5548543 1048576 1 1048576 (BSN.sqrt_enclosure 28 1 2774271 2774272 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep760 := BSN.log_dyadic_bound 12 44 5 4 13275571325829120 524288 136674 344661139390464 45148078080 293399 56 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 12) (BSN.artanhQ 44) 0 4 344661139390464 13275571325829120 45148078080 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz372 := (Real.log (Enclosure.sfrac Bool.false 28 1))

noncomputable def ep761 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz372 108936 1000 0 1 3751726938922231 1125899906842624 125000000068337 17084250000000000000 51087265727304019527 140737488355328000 189125000103393881 237281250000000000000 qz270 (BSN.isNear_log_sfrac 28 1 3751726938922231 1125899906842624 125000000068337 17084250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz613) Bool.false 62943533227317076688896 18889465931478580854784 1000000000546696 136674000000000000000 3751726938922231 1125899906842624 125000000068337 17084250000000000000 (BSN.log_rat_reduce_isNear 28 1 4 56 32 293399 524288 24973259072661432 36028797018963968 136674 1000000000000000 rfl rfl rfl rfl (ep760 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep762 := BSN.sin_dyadic_bound_f 306882483 2147483648 1 0 1048576 273615 0 1 1 0 1 1 149334 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 306882483) qz272 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 306882483) qz273 0 0 rfl) rfl rfl

noncomputable abbrev qz917 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 190314895) qz306)

noncomputable def ep763 := @Enclosure.Real.IsNear.cos_image qz371 qz917 Bool.false 190314895 524288 837 1048576 Bool.false 149334 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz371 Bool.false 51087265727304019527 140737488355328000 189125000103393881 237281250000000000000 190314895 524288 837 1048576 (ep761 rfl) rfl) (Enclosure.sfrac_false_div 190314895 524288) (BSN.cos_reduce3 qz917 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 10797467499444253491200) qz307) 226375608064910080 72057594037927936 Bool.false 149334 1048576 57 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q3 190314895 524288 226375608064910080 72057594037927936 57 10797467499444253491200 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 149334 1048576 10797467499444253491200 75557863725914323419136 306882483 2147483648 273615 273348 (ep762 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep764 := nat_lit 8869280652865947585210479182693521

noncomputable def ep765 := BSN.cos_dyadic_bound_f 306882483 2147483648 2 1 1048576 273615 ep764 ep91 ep764 ep764 ep92 ep764 1037887 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 306882483) qz266 0 1 ep764 ep91 ep764 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 306882483) qz267 0 1 ep764 ep92 ep764 rfl rfl rfl rfl) rfl rfl

noncomputable def ep766 := @Enclosure.Real.IsNear.sin_image qz371 qz917 Bool.false 190314895 524288 837 1048576 Bool.true 1037887 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz371 Bool.false 51087265727304019527 140737488355328000 189125000103393881 237281250000000000000 190314895 524288 837 1048576 (ep761 rfl) rfl) (Enclosure.sfrac_false_div 190314895 524288) (BSN.sin_reduce3 qz917 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 10797467499444253491200) qz307) 226375608064910080 72057594037927936 Bool.false 1037887 1048576 57 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q3 190314895 524288 226375608064910080 72057594037927936 57 10797467499444253491200 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1037887 1048576 10797467499444253491200 75557863725914323419136 306882483 2147483648 273615 273348 (ep765 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz614 := (@Enclosure.Real.IsNear.recentre' qz370 Bool.false 198163 1048576 1 1048576 198163 1048576 1 1048576 (ep759 rfl rfl) rfl)

noncomputable def ep767 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz370 (Real.cos qz371)) (@HMul.hMul Real Real Real qz0 qz370 qz916) Bool.false 14796236721 549755813888 5724349095053 37568663053664256 Bool.false 205670801581 1099511627776 11509419236467 75137326107328512 (@Enclosure.Real.IsNear.mulLit_ff qz370 (Real.cos qz371) 198163 1048576 1 1048576 74667 524288 57722357 71656538112 14796236721 549755813888 5724349095053 37568663053664256 qz614 (@Enclosure.Real.IsNear.recentre' (Real.cos qz371) Bool.false 149334 1048576 115444714 143313076224 74667 524288 57722357 71656538112 (ep763 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz370 qz916 198163 1048576 1 1048576 1037887 1048576 57722357 71656538112 205670801581 1099511627776 11509419236467 75137326107328512 qz614 (@Enclosure.Real.IsNear.neg (Real.sin qz371) Bool.true 1037887 1048576 57722357 71656538112 (@Enclosure.Real.IsNear.recentre' (Real.sin qz371) Bool.true 1037887 1048576 115444714 143313076224 1037887 1048576 57722357 71656538112 (ep766 rfl rfl) rfl)) rfl)

noncomputable def ep768 := @ep757 162819384757120000000 0 1 ep747 ep748 ep749 ep751 (@Enclosure.Complex.IsNear.re_isNear qz43 Bool.false 14796236721 549755813888 5724349095053 37568663053664256 Bool.false 205670801581 1099511627776 11509419236467 75137326107328512 (ep758 ep767))

noncomputable def ep769 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz13 qz44 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1))))) Bool.false 82010000580870242161 162819384757120000000 0 1 Bool.false

noncomputable def ep770 := @Enclosure.Complex.IsNear.addLitP qz44 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) Bool.false 739956381 1483412762 0 1 Bool.true 190638000

noncomputable def ep771 := @ep770 741706381 0 1 Bool.false 1068331381 219520000000 0 1 Bool.false 795693482779 1960000000000 0 1 Bool.false 164020001161740484322 82010000580870242161 162819384757120000000 0 1 Bool.false 216520453497297912799 216520453497297912799 1453744506760000000000 0 1

noncomputable abbrev qz48 := (@HDiv.hDiv Complex Complex Complex qz352 qz608 (@HSub.hSub Complex Complex Complex qz593 qz259 (1 : Complex)))

noncomputable def ep772 := @Enclosure.Complex.IsNear.addLitP qz48 qz24 Bool.true 56000000 47469208384 0 1 Bool.true 12200832000 47469208384 0 1

noncomputable def ep773 := @Enclosure.Complex.IsNear.of_eq qz48 (Complex.mk (Enclosure.sfrac Bool.true 56000000 47469208384) (Enclosure.sfrac Bool.true 12200832000 47469208384)) Bool.true 56000000 47469208384 0 1 Bool.true 12200832000 47469208384 0 1

noncomputable def ep774 := @ep772 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 47357208384 739956381 1483412762 0 1 Bool.true 12200832000 190638000 741706381 0 1 (ep773 (BSN.N_div_s_sub_one_mk qz9 108936 1000 28 (@Eq.refl Real qz9) rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 56000000 47469208384) (Enclosure.sfrac Bool.true 12200832000 47469208384) Bool.true 56000000 47469208384 0 1 Bool.true 12200832000 47469208384 0 1 (Enclosure.Real.IsNear.const Bool.true 56000000 47469208384) (Enclosure.Real.IsNear.const Bool.true 12200832000 47469208384))) qz357 rfl

noncomputable abbrev qz49 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)))

noncomputable abbrev qz50 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz254 qz608 3))

noncomputable def ep775 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz13 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) qz50)) Bool.false 1068331381 219520000000 0 1

noncomputable def ep776 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) qz50) Bool.false 1 672 0 1 Bool.false

noncomputable def ep777 := @ep776 4539 14000 0 1 Bool.false 2224994143 658560000000 0 1 Bool.false 160233482779 1960000000000 0 1 Bool.false 2153756064096 1068331381 219520000000 0 1 Bool.false 11139708758906000 795693482779 1960000000000 0

noncomputable abbrev qz51 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)))

noncomputable abbrev qz52 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz254 qz608 1))

noncomputable def ep778 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz13 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) qz52)) Bool.false 1 672 0 1

noncomputable def ep779 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) qz52) Bool.false 0 1 0 1 Bool.false

noncomputable def ep780 := @ep779 0 1 0 1 Bool.false 1 672 0 1 Bool.false 4539 14000 0 1 Bool.false 1 1 672 0 1 Bool.false 4539 4539 14000 0

noncomputable def ep781 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (Complex.mk qz262 qz262) Bool.false 0 1 0 1 Bool.false

noncomputable def ep782 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) qz52 Bool.false 1 672 0 1 Bool.false 4539 14000 0 1

noncomputable def ep783 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz52)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz52)) 1 672 0 1 0 1 0

noncomputable def ep784 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz52) 1 24 0 1 1 28 0 1 1

noncomputable def ep785 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep786 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep787 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz262) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 1 1 6 2 Bool.false BSN.bern_real_1 EMRow34.d10 rfl) qz603

noncomputable def ep788 := @ep786 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep787) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 108936 1000 0 1 ep430)

noncomputable def ep789 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 108936 1000 0 1 0 1 0

noncomputable def ep790 := @ep789 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep787) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 108936 1000 0 1 ep430)

noncomputable def ep791 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)))) 4539 500 0 1 0 1 0 1 4539

noncomputable def ep792 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 108936 1000 0 1 4539 500 0

noncomputable def ep793 := @ep792 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep787) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 108936 1000 0 1 ep430)

noncomputable def ep794 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep795 := @ep794 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep787) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 108936 1000 0 1 ep430)

noncomputable def ep796 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 4539 500 0 1 (@ep785 1 24 0 1 (ep788 rfl) (ep790 rfl) rfl rfl) (@ep791 4539 500 0 1 (ep793 rfl) (ep795 rfl) rfl rfl)

noncomputable def ep797 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 4539 500 0 1 ep796

noncomputable abbrev qz53 := (@Enclosure.Complex.IsNear.of_eq (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz254 qz608 1)) (Complex.mk (Enclosure.sfrac Bool.false 1 28) qz262) Bool.false 1 28 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 28 1 28 EMRow34.d11 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 28) qz262 Bool.false 1 28 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 28) qz274))

noncomputable abbrev qz918 := (@Enclosure.Complex.IsNear.re_isNear qz52 Bool.false 1 28 0 1 Bool.false 0 1 0 1 qz53)

noncomputable def ep798 := @ep784 672 0 1 ep797 qz918

noncomputable def ep799 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz52) 4539 500 0 1 0 1 0 1 0

noncomputable def ep800 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 4539 500 0 1 ep796

noncomputable abbrev qz919 := (@Enclosure.Complex.IsNear.im_isNear qz52 Bool.false 1 28 0 1 Bool.false 0 1 0 1 qz53)

noncomputable def ep801 := @ep799 1 0 1 ep800 qz919

noncomputable def ep802 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz52)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz52)) 0 1 0 1 4539 14000 0

noncomputable def ep803 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz52) 1 24 0 1 0 1 0 1 0

noncomputable def ep804 := @ep803 1 0 1 ep797 qz919

noncomputable def ep805 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz52) 4539 500 0 1 1 28 0 1 4539

noncomputable def ep806 := @ep805 14000 0 1 ep800 qz918

noncomputable def ep807 := @ep780 1 (@ep781 0 1 0 1 (BSN.bern_sum_base qz12 28) qz360) (ep782 (@ep783 1 1 1 672 0 1 (ep798 rfl) (ep801 rfl) rfl rfl) (@ep802 1 4539 4539 14000 0 1 (ep804 rfl) (ep806 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep808 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) qz50 Bool.false 2224994143 658560000000 0 1 Bool.false 160233482779 1960000000000 0 1

noncomputable def ep809 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.re qz50)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.im qz50)) 2224994143 658560000000 0 1 0 1 0

noncomputable def ep810 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.re qz50) 2224994143 30000000 0 1 1 21952 0 1 2224994143

noncomputable def ep811 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)))) 2224994143 30000000 0 1 0 1 0 1 2224994143

noncomputable def ep812 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 6674982429 125000 0 1 2224994143 30000000 0

noncomputable def ep813 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (Complex.mk (Enclosure.sfrac Bool.true 1 720) qz262) Bool.true 1 720 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 2 1 30 24 Bool.true BSN.bern_real_2 EMRow34.d12 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 1 720) qz262 Bool.true 1 720 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.true 1 720) qz274)

noncomputable def ep814 := @ep812 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep813) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 6674982429 125000 0 1 Bool.true 10094709415077 7812500 0 1 EMRow34.d13)

noncomputable def ep815 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 10094709415077 7812500 0 1 0 1 0

noncomputable def ep816 := @ep815 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep813) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 6674982429 125000 0 1 Bool.true 10094709415077 7812500 0 1 EMRow34.d13)

noncomputable def ep817 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)))) 1121634379453 625000000 0 1 0 1 0 1 1121634379453

noncomputable def ep818 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 10094709415077 7812500 0 1 1121634379453 625000000 0

noncomputable def ep819 := @ep818 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep813) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 6674982429 125000 0 1 Bool.true 10094709415077 7812500 0 1 EMRow34.d13)

noncomputable def ep820 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 6674982429 125000 0 1 0 1 0

noncomputable def ep821 := @ep820 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep813) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 6674982429 125000 0 1 Bool.true 10094709415077 7812500 0 1 EMRow34.d13)

noncomputable def ep822 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 2224994143 30000000 0 1 Bool.false 1121634379453 625000000 0 1 (@ep811 2224994143 30000000 0 1 (ep814 rfl) (ep816 rfl) rfl rfl) (@ep817 1121634379453 625000000 0 1 (ep819 rfl) (ep821 rfl) rfl rfl)

noncomputable def ep823 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 2224994143 30000000 0 1 Bool.false 1121634379453 625000000 0 1 ep822

noncomputable abbrev qz54 := (@Enclosure.Complex.IsNear.of_eq (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz254 qz608 3)) (Complex.mk (Enclosure.sfrac Bool.false 1 21952) qz262) Bool.false 1 21952 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 28 3 21952 EMRow34.d14 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 21952) qz262 Bool.false 1 21952 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 21952) qz274))

noncomputable abbrev qz920 := (@Enclosure.Complex.IsNear.re_isNear qz50 Bool.false 1 21952 0 1 Bool.false 0 1 0 1 qz54)

noncomputable def ep824 := @ep810 658560000000 0 1 ep823 qz920

noncomputable def ep825 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.im qz50) 1121634379453 625000000 0 1 0 1 0 1 0

noncomputable def ep826 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 2224994143 30000000 0 1 Bool.false 1121634379453 625000000 0 1 ep822

noncomputable abbrev qz921 := (@Enclosure.Complex.IsNear.im_isNear qz50 Bool.false 1 21952 0 1 Bool.false 0 1 0 1 qz54)

noncomputable def ep827 := @ep825 1 0 1 ep826 qz921

noncomputable def ep828 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.im qz50)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.re qz50)) 0 1 0 1 160233482779 1960000000000 0

noncomputable def ep829 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.im qz50) 2224994143 30000000 0 1 0 1 0 1 0

noncomputable def ep830 := @ep829 1 0 1 ep823 qz921

noncomputable def ep831 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.re qz50) 1121634379453 625000000 0 1 1 21952 0 1 160233482779

noncomputable def ep832 := @ep831 1960000000000 0 1 ep826 qz920

noncomputable def ep833 := @ep777 1 (@ep778 Bool.false 4539 14000 0 1 (BSN.bern_sum_succ qz12 28 0 1 1 rfl rfl) (ep807 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep808 (@ep809 1 2224994143 2224994143 658560000000 0 1 (ep824 rfl) (ep827 rfl) rfl rfl) (@ep828 1 160233482779 160233482779 1960000000000 0 1 (ep830 rfl) (ep832 rfl) rfl rfl)) rfl rfl rfl rfl

noncomputable def ep834 := ep771 (ep774 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep775 Bool.false 795693482779 1960000000000 0 1 (BSN.bern_sum_succ qz12 28 1 2 3 rfl rfl) (ep833 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep835 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz43) (Complex.im (@HAdd.hAdd Complex Complex Complex qz13 qz44 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))))) 205670801581 1099511627776 11509419236467 75137326107328512 216520453497297912799

noncomputable def ep836 := @ep835 1453744506760000000000 0 1 ep752 ep753 ep754 ep755 (@Enclosure.Complex.IsNear.im_isNear qz43 Bool.false 14796236721 549755813888 5724349095053 37568663053664256 Bool.false 205670801581 1099511627776 11509419236467 75137326107328512 (ep758 ep767))

noncomputable def ep837 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz13 qz44 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1))))) Bool.false 82010000580870242161 162819384757120000000 0 1 Bool.false

noncomputable def ep838 := nat_lit 457669697840613178804745670297

noncomputable def ep839 := nat_lit 114172070642721845411840000000000

noncomputable def ep840 := nat_lit 1239438662037722476111701356283347

noncomputable def ep841 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re qz43) (Complex.im (@HAdd.hAdd Complex Complex Complex qz13 qz44 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 (Complex.im qz43) (Complex.re (@HAdd.hAdd Complex Complex Complex qz13 qz44 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1))))))) ep838 ep839 ep840

noncomputable def ep842 := nat_lit 54615237540581779249362370560000000000

noncomputable def ep843 := nat_lit 2409580365303694045686064522363

noncomputable def ep844 := nat_lit 25574543823969693372252160000000

noncomputable def ep845 := nat_lit 943887478268137809019058012085187

noncomputable def ep846 := nat_lit 12233813209090318551857171005440000000

noncomputable def ep847 := nat_lit 286811473431096596381988350885570475490771035464684011520000000

noncomputable def ep848 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz43) (Complex.im (@HAdd.hAdd Complex Complex Complex qz13 qz44 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))))) 14796236721 549755813888 5724349095053 37568663053664256 216520453497297912799

noncomputable def ep849 := @ep848 1453744506760000000000 0 1 ep838 ep839 ep840 ep842 (@Enclosure.Complex.IsNear.re_isNear qz43 Bool.false 14796236721 549755813888 5724349095053 37568663053664256 Bool.false 205670801581 1099511627776 11509419236467 75137326107328512 (ep758 ep767))

noncomputable def ep850 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz43) (Complex.re (@HAdd.hAdd Complex Complex Complex qz13 qz44 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))))) 205670801581 1099511627776 11509419236467 75137326107328512 82010000580870242161

noncomputable def ep851 := @ep850 162819384757120000000 0 1 ep843 ep844 ep845 ep846 (@Enclosure.Complex.IsNear.im_isNear qz43 Bool.false 14796236721 549755813888 5724349095053 37568663053664256 Bool.false 205670801581 1099511627776 11509419236467 75137326107328512 (ep758 ep767))

noncomputable abbrev qz922 := (ep834 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep852 := @ep746 ep691 ep684 ep692 ep686 (@ep750 ep751 ep752 ep753 ep754 ep755 ep756 ep689 ep475 ep690 ep477 (ep768 (@ep769 216520453497297912799 1453744506760000000000 0 1 qz922) rfl) (ep836 (@ep837 216520453497297912799 1453744506760000000000 0 1 qz922) rfl) rfl rfl) (@ep841 ep842 ep843 ep844 ep845 ep846 ep847 ep691 ep684 ep692 ep686 (ep849 (@ep837 216520453497297912799 1453744506760000000000 0 1 qz922) rfl) (ep851 (@ep769 216520453497297912799 1453744506760000000000 0 1 qz922) rfl) rfl rfl)

noncomputable def ep853 := @ep695 ep685 ep686 (@ep696 37568663053664256 (BSN.head_sum_c_eq qz12 28) (ep697 (BSN.head_sum_c_succ qz12 27 28 rfl rfl) (ep745 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep852 rfl rfl rfl

noncomputable def ep854 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz12 2 28) Bool.false ep474 ep475 ep476 ep477 Bool.false ep683 ep684 ep685 ep686 (@ep687 ep477 Bool.false ep683 ep684 ep685 ep686 (BSN.zetaApproximant_eq_folded' qz12 2 28 rfl) (ep853 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep855 := @Enclosure.Real.IsNear.mulLit_tf (Real.sin (@HSub.hSub Real Real Real qz347 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz21 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz22 (@Nat.cast Complex Complex.instNatCast j))))) qz348)) (Complex.im (zetaApproximant qz12 2 28)) 629 1048576 24647249

noncomputable def ep856 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz347 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz21 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz22 (@Nat.cast Complex Complex.instNatCast j))))) qz348)) Bool.true 629 1048576 49294498

noncomputable def ep857 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz347 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz21 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz22 (@Nat.cast Complex Complex.instNatCast j))))) qz348) qz890 Bool.false 105413727 1048576 353

noncomputable def ep858 := nat_lit 4635874151511344334029601673530803701941745846005104440305500660894543449964481

noncomputable def ep859 := nat_lit 13874195359764935764287993422811989105463201124332933434147718220989242357858241

noncomputable def ep860 := BSN.cos_dyadic_bound_f 3371969049 2147483648 3 2 1048576 273615 ep858 ep138 ep679 ep859 ep140 ep679 629 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3371969049) qz266 0 2 ep858 ep138 ep679 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3371969049) qz267 0 2 ep859 ep140 ep679 rfl rfl rfl rfl) rfl rfl

noncomputable def ep861 := @ep857 1048576 Bool.true 629 1048576 1 136674 (@ep484 105413727 1048576 353 1048576 ep677 rfl) (Enclosure.sfrac_false_div 105413727 1048576) (BSN.sin_reduce3 qz890 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 237281227438843603451904) qz271) 226375608064910080 72057594037927936 Bool.false 629 1048576 15 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q3 105413727 1048576 226375608064910080 72057594037927936 15 237281227438843603451904 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 629 1048576 237281227438843603451904 151115727451828646838272 3371969049 2147483648 273615 273348 (ep860 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep862 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz12 2 28) Bool.false ep474 ep475 ep476 ep477 Bool.false ep683 ep684 ep685 ep686 (@ep687 ep477 Bool.false ep683 ep684 ep685 ep686 (BSN.zetaApproximant_eq_folded' qz12 2 28 rfl) (ep853 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow34.d15 : Enclosure.Real.IsNear (hardyZApproximantEM 2 28 qz9) Bool.false ep459 ep460 ep461 ep462 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 2 28 qz9) ep463 Bool.false ep459 ep460 ep461 ep462 (@Eq.refl Real ep463) (@ep464 Bool.false ep459 ep460 ep461 ep462 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz347 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz21 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz22 (@Nat.cast Complex Complex.instNatCast j))))) qz348) (zetaApproximant qz12 2 28)) (@ep466 ep467 ep468 ep469 ep470 ep460 ep471 ep462 ep472 ep459 ep460 ep461 ep462 (@ep473 71656538112 ep474 ep475 ep476 ep477 ep465 ep467 ep468 ep469 (@ep478 143313076224 1048575 1048576 24647249 71656538112 (ep682 rfl rfl) rfl) ep854 rfl) (@ep855 71656538112 ep683 ep684 ep685 ep686 ep470 ep460 ep471 ep462 (@ep856 143313076224 629 1048576 24647249 71656538112 (ep861 rfl rfl) rfl) ep862 rfl) rfl rfl))

noncomputable abbrev qz615 := (@HAdd.hAdd Complex Complex Complex qz811 (@HAdd.hAdd Complex Complex Complex qz811 qz812 (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I (@HDiv.hDiv Complex Complex Complex qz813 (↑(Enclosure.sfrac Bool.false 111131 1000)) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 4))

noncomputable abbrev qz373 := (@HPow.hPow Complex Nat Complex qz541 qz615 3)

noncomputable abbrev qz55 := qz373

noncomputable def ep863 := Enclosure.Complex.IsNear qz55 Bool.true 628626807211 16000000 0 1 Bool.true 1348391225611091 8000000000 0 1

noncomputable abbrev qz374 := qz615

noncomputable abbrev qz56 := (@HPow.hPow Complex Nat Complex qz254 qz374 2)

noncomputable abbrev qz57 := qz374

noncomputable def ep864 := @Enclosure.Complex.IsNear.of_eq qz55 (@HMul.hMul Complex Complex Complex qz3 qz56 qz57) Bool.true 628626807211 16000000 0 1 Bool.true 1348391225611091 8000000000

noncomputable def ep865 := @Enclosure.Complex.IsNear.mul qz56 qz57 Bool.true 628626807211 16000000 0 1 Bool.true 1348391225611091 8000000000 0

noncomputable def ep866 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re qz56) (Complex.re qz57)) (@HMul.hMul Real Real Real qz0 (Complex.im qz56) (Complex.im qz57)) 208723435737 16000000 0 1 209951685737 8000000

noncomputable def ep867 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re qz56) (Complex.re qz57) 12277849161 4000000 0 1 17000 4000 0 1

noncomputable def ep868 := @Enclosure.Complex.IsNear.re_isNear qz56 Bool.true 12277849161 4000000 0 1 Bool.false 1889227 4000 0 1

noncomputable abbrev qz375 := (@HPow.hPow Complex Nat Complex qz541 qz615 1)

noncomputable abbrev qz58 := qz375

noncomputable def ep869 := @Enclosure.Complex.IsNear.of_eq qz56 (@HMul.hMul Complex Complex Complex qz3 qz58 qz57) Bool.true 12277849161 4000000 0 1 Bool.false 1889227 4000

noncomputable def ep870 := @Enclosure.Complex.IsNear.mul qz58 qz57 Bool.true 12277849161 4000000 0 1 Bool.false 1889227 4000 0

noncomputable abbrev qz59 := (Complex.re qz375)

noncomputable abbrev qz60 := (Complex.im qz375)

noncomputable def ep871 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz59 (Complex.re qz57)) (@HMul.hMul Real Real Real qz0 qz60 (Complex.im qz57)) 289 16 0 1 12350099161 4000000

noncomputable def ep872 := @Enclosure.Real.IsNear.mulLit_ff qz59 (Complex.re qz57) 17000 4000 0 1 17000 4000 0 1

noncomputable def ep873 := @Enclosure.Complex.IsNear.re_isNear qz58 Bool.false 17000 4000 0 1 Bool.false 222262 4000 0 1

noncomputable def ep874 := @Enclosure.Complex.IsNear.of_eq qz58 qz57 Bool.false 17000 4000 0 1 Bool.false 222262 4000 0

noncomputable abbrev qz376 := (Enclosure.sfrac Bool.false 111131 1000)

noncomputable abbrev qz61 := qz376

noncomputable abbrev qz377 := (Enclosure.sfrac Bool.false 222262 4000)

noncomputable abbrev qz616 := (Complex.mk (Enclosure.sfrac Bool.false 17000 4000) qz377)

noncomputable def ep875 := @Enclosure.Complex.IsNear.of_eq qz57 qz616 Bool.false 17000 4000 0 1 Bool.false 222262 4000 0 1 (BSN.w_shift_mk qz61 Bool.false 111131 1000 4 (@Eq.refl Real qz61) rfl)

noncomputable abbrev qz62 := (@ep874 1 (BSN.pow_one_c qz374) (ep875 (@Enclosure.Complex.IsNear.mk qz545 qz377 Bool.false 17000 4000 0 1 Bool.false 222262 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 17000 4000) (Enclosure.Real.IsNear.const Bool.false 222262 4000))))

noncomputable abbrev qz63 := (ep875 (@Enclosure.Complex.IsNear.mk qz545 qz377 Bool.false 17000 4000 0 1 Bool.false 222262 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 17000 4000) (Enclosure.Real.IsNear.const Bool.false 222262 4000)))

noncomputable abbrev qz617 := (@Enclosure.Complex.IsNear.re_isNear qz57 Bool.false 17000 4000 0 1 Bool.false 222262 4000 0 1 qz63)

noncomputable def ep876 := @ep872 289 16 0 1 (ep873 qz62) qz617

noncomputable def ep877 := @Enclosure.Real.IsNear.mulLit_ff qz60 (Complex.im qz57) 222262 4000 0 1 222262 4000 0 1

noncomputable def ep878 := @Enclosure.Complex.IsNear.im_isNear qz58 Bool.false 17000 4000 0 1 Bool.false 222262 4000 0 1

noncomputable abbrev qz618 := (@Enclosure.Complex.IsNear.im_isNear qz57 Bool.false 17000 4000 0 1 Bool.false 222262 4000 0 1 qz63)

noncomputable def ep879 := @ep877 12350099161 4000000 0 1 (ep878 qz62) qz618

noncomputable def ep880 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz59 (Complex.im qz57)) (@HMul.hMul Real Real Real qz0 qz60 (Complex.re qz57)) 1889227 8000 0 1 1889227 8000

noncomputable def ep881 := @Enclosure.Real.IsNear.mulLit_ff qz59 (Complex.im qz57) 17000 4000 0 1 222262 4000 0 1

noncomputable def ep882 := @ep881 1889227 8000 0 1 (ep873 qz62) qz618

noncomputable def ep883 := @Enclosure.Real.IsNear.mulLit_ff qz60 (Complex.re qz57) 222262 4000 0 1 17000 4000 0 1

noncomputable def ep884 := @ep883 1889227 8000 0 1 (ep878 qz62) qz617

noncomputable abbrev qz619 := (@ep869 0 1 (BSN.pow_succ_c qz57 1 2 rfl) (@ep870 1 (@ep871 0 1 196445586576 12277849161 4000000 0 1 (ep876 rfl) (ep879 rfl) rfl rfl) (@ep880 0 1 30227632000 1889227 4000 0 1 (ep882 rfl) (ep884 rfl) rfl rfl)))

noncomputable def ep885 := @ep867 208723435737 16000000 0 1 (ep868 qz619) qz617

noncomputable def ep886 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz56) (Complex.im qz57) 1889227 4000 0 1 222262 4000 0 1

noncomputable def ep887 := @Enclosure.Complex.IsNear.im_isNear qz56 Bool.true 12277849161 4000000 0 1 Bool.false 1889227 4000 0 1

noncomputable def ep888 := @ep886 209951685737 8000000 0 1 (ep887 qz619) qz618

noncomputable def ep889 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re qz56) (Complex.im qz57)) (@HMul.hMul Real Real Real qz0 (Complex.im qz56) (Complex.re qz57)) 1364449655111091 8000000000 0 1 32116859 16000

noncomputable def ep890 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re qz56) (Complex.im qz57) 12277849161 4000000 0 1 222262 4000 0 1

noncomputable def ep891 := @ep890 1364449655111091 8000000000 0 1 (ep868 qz619) qz618

noncomputable def ep892 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz56) (Complex.re qz57) 1889227 4000 0 1 17000 4000 0 1

noncomputable def ep893 := @ep892 32116859 16000 0 1 (ep887 qz619) qz617

theorem EMRow34.d16 : ep863 := @ep864 0 1 (BSN.pow_succ_c qz57 2 3 rfl) (@ep865 1 (@ep866 0 1 5029014457688000000 628626807211 16000000 0 1 (ep885 rfl) (ep888 rfl) rfl rfl) (@ep889 0 1 21574259609777456000 1348391225611091 8000000000 0 1 (ep891 rfl) (ep893 rfl) rfl rfl))

noncomputable abbrev qz378 := (@HAdd.hAdd Complex Complex Complex qz547 qz548 (@HMul.hMul Complex Complex Complex qz543 Complex.I ↑(Enclosure.sfrac Bool.false 111131 1000)))

noncomputable abbrev qz64 := qz378

noncomputable abbrev qz65 := (@Neg.neg Complex Complex.instNeg qz378)

noncomputable abbrev qz923 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 8) qz65)

noncomputable def ep894 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 9) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 8) qz923) Bool.true 1003345547239 1099511627776 69449993866733 25045775369109504 Bool.true 484384381091 1099511627776 69445426950581 25045775369109504

noncomputable def ep895 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 8) qz923 Bool.true 537112235821 549755813888 31088711887039 12522887684554752 Bool.true 866603176637 1099511627776 62153726848715 25045775369109504 Bool.false

noncomputable abbrev qz924 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 7) qz65)

noncomputable def ep896 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 8) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 7) qz924) Bool.true 537112235821 549755813888 31088711887039 12522887684554752 Bool.true 866603176637 1099511627776 62153726848715 25045775369109504

noncomputable def ep897 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 7) qz924 Bool.true 89174985899 137438953472 81579922501249 37568663053664256 Bool.true 82553125439 137438953472 81557709696073 37568663053664256 Bool.true

noncomputable abbrev qz925 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 6) qz65)

noncomputable def ep898 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 7) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 6) qz925) Bool.true 89174985899 137438953472 81579922501249 37568663053664256 Bool.true 82553125439 137438953472 81557709696073 37568663053664256

noncomputable def ep899 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 6) qz925 Bool.true 275285738981 549755813888 2873474002561 1565360960569344 Bool.true 539362055339 549755813888 2871698835091 1565360960569344 Bool.true

noncomputable def ep900 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 6) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 5) (@HPow.hPow Complex Complex Complex qz14 qz16 qz65)) Bool.true 275285738981 549755813888 2873474002561 1565360960569344 Bool.true 539362055339 549755813888 2871698835091 1565360960569344

noncomputable def ep901 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 5) (@HPow.hPow Complex Complex Complex qz14 qz16 qz65) Bool.true 69920900639 1099511627776 110243722612337 75137326107328512 Bool.true 487498561013 549755813888 13776680336581 9392165763416064 Bool.true

noncomputable def ep902 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 5) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 4) (@HPow.hPow Complex Complex Complex qz14 qz17 qz65)) Bool.true 69920900639 1099511627776 110243722612337 75137326107328512 Bool.true 487498561013 549755813888 13776680336581 9392165763416064

noncomputable def ep903 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 4) (@HPow.hPow Complex Complex Complex qz14 qz17 qz65) Bool.false 118934664729 274877906944 19834052110705 18784331526832128 Bool.true 1041973213415 1099511627776 79368321434197 75137326107328512 Bool.true

noncomputable def ep904 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 4) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 3) (@HPow.hPow Complex Complex Complex qz14 qz550 qz65)) Bool.false 118934664729 274877906944 19834052110705 18784331526832128 Bool.true 1041973213415 1099511627776 79368321434197 75137326107328512

noncomputable def ep905 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 3) (@HPow.hPow Complex Complex Complex qz14 qz550 qz65) Bool.false 1052146740921 1099511627776 4851591589457 8348591789703168 Bool.true 776026822285 1099511627776 4859053579835 8348591789703168 Bool.true

noncomputable def ep906 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 3) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 2) (@HPow.hPow Complex Complex Complex qz14 qz551 qz65)) Bool.false 1052146740921 1099511627776 4851591589457 8348591789703168 Bool.true 776026822285 1099511627776 4859053579835 8348591789703168

noncomputable def ep907 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 2) (@HPow.hPow Complex Complex Complex qz14 qz551 qz65) Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.true

noncomputable def ep908 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz262) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz64)

noncomputable abbrev qz379 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 2 1)))

noncomputable def ep909 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz14 qz551 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz263 (Real.cos qz379)) (@HMul.hMul Real Real Real qz0 qz263 (@Neg.neg Real Real.instNeg (Real.sin qz379)))) Bool.true 47364886855 1099511627776 4851591589457 8348591789703168 Bool.true 776026822285 1099511627776 4859053579835 8348591789703168 (BSN.cpow_neg_s_mk qz61 111131 1000 2 (@Eq.refl Real qz61) rfl)

noncomputable def ep910 := BSN.sin_dyadic_bound_f 130909943 2147483648 1 0 1048576 273615 0 1 1 0 1 1 63881 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 130909943) qz272 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 130909943) qz273 0 0 rfl) rfl rfl

noncomputable abbrev qz380 := (Enclosure.Real.IsNear.const Bool.false 111131 1000)

noncomputable abbrev qz620 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 20192947) (@Nat.cast Real Real.instNatCast 262144))

noncomputable def ep911 := @Enclosure.Real.IsNear.cos_image qz379 qz620 Bool.false 20192947 262144 427 524288 Bool.true 63881 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz379 Bool.false 2524118403 32768000 111131 136674000 20192947 262144 427 524288 (@Enclosure.Real.IsNear.mulLit_ff qz61 qz269 111131 1000 0 1 363408 524288 1 136674 2524118403 32768000 111131 136674000 qz380 qz552 rfl) rfl) (Enclosure.sfrac_false_div 20192947 262144) (BSN.cos_reduce1 qz620 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2302992082967990370304) qz566) 226375608064910080 72057594037927936 Bool.false 63881 1048576 12 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q1 20192947 262144 226375608064910080 72057594037927936 12 2302992082967990370304 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 63881 1048576 2302992082967990370304 37778931862957161709568 130909943 2147483648 273615 273348 (ep910 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep912 := BSN.cos_dyadic_bound_f 130909943 2147483648 1 0 1048576 273615 0 1 1 0 1 1 1046627 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 130909943) qz266 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 130909943) qz267 0 0 rfl) rfl rfl

noncomputable def ep913 := @Enclosure.Real.IsNear.sin_image qz379 qz620 Bool.false 20192947 262144 427 524288 Bool.false 1046627 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz379 Bool.false 2524118403 32768000 111131 136674000 20192947 262144 427 524288 (@Enclosure.Real.IsNear.mulLit_ff qz61 qz269 111131 1000 0 1 363408 524288 1 136674 2524118403 32768000 111131 136674000 qz380 qz552 rfl) rfl) (Enclosure.sfrac_false_div 20192947 262144) (BSN.sin_reduce1 qz620 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2302992082967990370304) qz566) 226375608064910080 72057594037927936 Bool.false 1046627 1048576 12 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q1 20192947 262144 226375608064910080 72057594037927936 12 2302992082967990370304 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1046627 1048576 2302992082967990370304 37778931862957161709568 130909943 2147483648 273615 273348 (ep912 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep914 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz263 (Real.cos qz379)) (@HMul.hMul Real Real Real qz0 qz263 (@Neg.neg Real Real.instNeg (Real.sin qz379))) Bool.true 47364886855 1099511627776 4851591589457 8348591789703168 Bool.true 776026822285 1099511627776 4859053579835 8348591789703168 (@Enclosure.Real.IsNear.mulLit_ft qz263 (Real.cos qz379) 741455 1048576 1 1048576 63881 1048576 29442043 35828269056 47364886855 1099511627776 4851591589457 8348591789703168 qz553 (@Enclosure.Real.IsNear.recentre' (Real.cos qz379) Bool.true 63881 1048576 58884086 71656538112 63881 1048576 29442043 35828269056 (ep911 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz263 (@Neg.neg Real Real.instNeg (Real.sin qz379)) 741455 1048576 1 1048576 1046627 1048576 29442043 35828269056 776026822285 1099511627776 4859053579835 8348591789703168 qz553 (@Enclosure.Real.IsNear.neg (Real.sin qz379) Bool.false 1046627 1048576 29442043 35828269056 (@Enclosure.Real.IsNear.recentre' (Real.sin qz379) Bool.false 1046627 1048576 58884086 71656538112 1046627 1048576 29442043 35828269056 (ep913 rfl rfl) rfl)) rfl)

noncomputable def ep915 := @ep907 47364886855 1099511627776 4851591589457 8348591789703168 Bool.true 776026822285 1099511627776 4859053579835 8348591789703168 Bool.false 1052146740921 1052146740921 1099511627776 4851591589457 8348591789703168 Bool.true 776026822285 776026822285 1099511627776 4859053579835 8348591789703168 (ep908 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz262 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz274)) (ep909 ep914) rfl rfl

noncomputable abbrev qz381 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 3 1)))

noncomputable def ep916 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz14 qz550 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz275 (Real.cos qz381)) (@HMul.hMul Real Real Real qz0 qz275 (@Neg.neg Real Real.instNeg (Real.sin qz381)))) Bool.true 576408082005 1099511627776 35671884137707 75137326107328512 Bool.true 132973195565 549755813888 17818419607841 37568663053664256 (BSN.cpow_neg_s_mk qz61 111131 1000 3 (@Eq.refl Real qz61) rfl)

noncomputable def ep917 := nat_lit 2299406386279153557335178946486744102073332161648201809563281872252236346807265

noncomputable def ep918 := nat_lit 1276869470466274645747422106719803660318868477674958925937159567738493064161

noncomputable def ep919 := nat_lit 6020187508731313919784734747863926299503925112495721472499935216598566205248481

noncomputable def ep920 := BSN.sin_dyadic_bound_f 2444940603 2147483648 3 2 1048576 273615 ep917 ep131 ep918 ep919 ep134 ep918 952119 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2444940603) qz272 0 2 ep917 ep131 ep918 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2444940603) qz273 0 2 ep919 ep134 ep918 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz926 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 128020467) qz268)

noncomputable def ep921 := @Enclosure.Real.IsNear.cos_image qz381 qz926 Bool.false 128020467 1048576 853 1048576 Bool.true 952119 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz381 Bool.false 64010233559 524288000 111131 136674000 128020467 1048576 853 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz61 qz277 111131 1000 0 1 575989 524288 1 136674 64010233559 524288000 111131 136674000 qz380 qz554 rfl) rfl) (Enclosure.sfrac_false_div 128020467 1048576) (BSN.cos_reduce1 qz926 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 172047399889021450584064) qz271) 226375608064910080 72057594037927936 Bool.false 952119 1048576 19 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q1 128020467 1048576 226375608064910080 72057594037927936 19 172047399889021450584064 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 952119 1048576 172047399889021450584064 151115727451828646838272 2444940603 2147483648 273615 273348 (ep920 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep922 := nat_lit 1278015489919736987250987157873399969445326253572412098168906444392459522921441

noncomputable def ep923 := nat_lit 3831492730818278412461466629406760301015341023761886376654845014041901582636001

noncomputable def ep924 := BSN.cos_dyadic_bound_f 2444940603 2147483648 3 2 1048576 273615 ep922 ep138 ep918 ep923 ep140 ep918 439294 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2444940603) qz266 0 2 ep922 ep138 ep918 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2444940603) qz267 0 2 ep923 ep140 ep918 rfl rfl rfl rfl) rfl rfl

noncomputable def ep925 := @Enclosure.Real.IsNear.sin_image qz381 qz926 Bool.false 128020467 1048576 853 1048576 Bool.false 439294 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz381 Bool.false 64010233559 524288000 111131 136674000 128020467 1048576 853 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz61 qz277 111131 1000 0 1 575989 524288 1 136674 64010233559 524288000 111131 136674000 qz380 qz554 rfl) rfl) (Enclosure.sfrac_false_div 128020467 1048576) (BSN.sin_reduce1 qz926 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 172047399889021450584064) qz271) 226375608064910080 72057594037927936 Bool.false 439294 1048576 19 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q1 128020467 1048576 226375608064910080 72057594037927936 19 172047399889021450584064 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 439294 1048576 172047399889021450584064 151115727451828646838272 2444940603 2147483648 273615 273348 (ep924 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep926 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz275 (Real.cos qz381)) (@HMul.hMul Real Real Real qz0 qz275 (@Neg.neg Real Real.instNeg (Real.sin qz381))) Bool.true 576408082005 1099511627776 35671884137707 75137326107328512 Bool.true 132973195565 549755813888 17818419607841 37568663053664256 (@Enclosure.Real.IsNear.mulLit_ft qz275 (Real.cos qz381) 605395 1048576 1 1048576 952119 1048576 58815749 71656538112 576408082005 1099511627776 35671884137707 75137326107328512 qz555 (@Enclosure.Real.IsNear.recentre' (Real.cos qz381) Bool.true 952119 1048576 117631498 143313076224 952119 1048576 58815749 71656538112 (ep921 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz275 (@Neg.neg Real Real.instNeg (Real.sin qz381)) 605395 1048576 1 1048576 219647 524288 58815749 71656538112 132973195565 549755813888 17818419607841 37568663053664256 qz555 (@Enclosure.Real.IsNear.neg (Real.sin qz381) Bool.false 219647 524288 58815749 71656538112 (@Enclosure.Real.IsNear.recentre' (Real.sin qz381) Bool.false 439294 1048576 117631498 143313076224 219647 524288 58815749 71656538112 (ep925 rfl rfl) rfl)) rfl)

noncomputable def ep927 := @ep905 576408082005 1099511627776 35671884137707 75137326107328512 Bool.true 132973195565 549755813888 17818419607841 37568663053664256 Bool.false 523080187260702415650816 118934664729 274877906944 19834052110705 18784331526832128 Bool.true 572830831990458044907520 1041973213415 1099511627776 79368321434197 75137326107328512 (ep906 (BSN.head_sum_c_succ qz64 2 3 rfl rfl) (ep915 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep916 ep926) rfl rfl

noncomputable abbrev qz382 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 4 1)))

noncomputable def ep928 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz14 qz17 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz278 (Real.cos qz382)) (@HMul.hMul Real Real Real qz0 qz278 (@Neg.neg Real Real.instNeg (Real.sin qz382)))) Bool.true 545659559555 1099511627776 30907514169517 75137326107328512 Bool.false 66976091389 1099511627776 30845121258451 75137326107328512 (BSN.cpow_neg_s_mk qz61 111131 1000 4 (@Eq.refl Real qz61) rfl)

noncomputable def ep929 := nat_lit 4732075722172885665773112258367041

noncomputable def ep930 := BSN.cos_dyadic_bound_f 262278639 2147483648 2 1 1048576 273615 ep929 ep91 ep929 ep929 ep92 ep929 1040765 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 262278639) qz266 0 1 ep929 ep91 ep929 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 262278639) qz267 0 1 ep929 ep92 ep929 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz621 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 20192975) (@Nat.cast Real Real.instNatCast 131072))

noncomputable def ep931 := @Enclosure.Real.IsNear.cos_image qz382 qz621 Bool.false 20192975 131072 853 1048576 Bool.true 1040765 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz382 Bool.false 80771900027 524288000 111131 136674000 20192975 131072 853 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz61 qz280 111131 1000 0 1 726817 524288 1 136674 80771900027 524288000 111131 136674000 qz380 qz556 rfl) rfl) (Enclosure.sfrac_false_div 20192975 131072) (BSN.cos_reduce2 qz621 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2307027308234114334720) qz560) 226375608064910080 72057594037927936 Bool.false 1040765 1048576 24 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q2 20192975 131072 226375608064910080 72057594037927936 24 2307027308234114334720 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1040765 1048576 2307027308234114334720 18889465931478580854784 262278639 2147483648 273615 273348 (ep930 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep932 := BSN.sin_dyadic_bound_f 262278639 2147483648 1 0 1048576 273615 0 1 1 0 1 1 127747 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 262278639) qz272 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 262278639) qz273 0 0 rfl) rfl rfl

noncomputable def ep933 := @Enclosure.Real.IsNear.sin_image qz382 qz621 Bool.false 20192975 131072 853 1048576 Bool.true 127747 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz382 Bool.false 80771900027 524288000 111131 136674000 20192975 131072 853 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz61 qz280 111131 1000 0 1 726817 524288 1 136674 80771900027 524288000 111131 136674000 qz380 qz556 rfl) rfl) (Enclosure.sfrac_false_div 20192975 131072) (BSN.sin_reduce2 qz621 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2307027308234114334720) qz560) 226375608064910080 72057594037927936 Bool.false 127747 1048576 24 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q2 20192975 131072 226375608064910080 72057594037927936 24 2307027308234114334720 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 127747 1048576 2307027308234114334720 18889465931478580854784 262278639 2147483648 273615 273348 (ep932 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep934 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz278 (Real.cos qz382)) (@HMul.hMul Real Real Real qz0 qz278 (@Neg.neg Real Real.instNeg (Real.sin qz382))) Bool.true 545659559555 1099511627776 30907514169517 75137326107328512 Bool.false 66976091389 1099511627776 30845121258451 75137326107328512 (@Enclosure.Real.IsNear.mulLit_ft qz278 (Real.cos qz382) 524287 1048576 1 1048576 1040765 1048576 58815749 71656538112 545659559555 1099511627776 30907514169517 75137326107328512 qz557 (@Enclosure.Real.IsNear.recentre' (Real.cos qz382) Bool.true 1040765 1048576 117631498 143313076224 1040765 1048576 58815749 71656538112 (ep931 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz278 (@Neg.neg Real Real.instNeg (Real.sin qz382)) 524287 1048576 1 1048576 127747 1048576 58815749 71656538112 66976091389 1099511627776 30845121258451 75137326107328512 qz557 (@Enclosure.Real.IsNear.neg (Real.sin qz382) Bool.true 127747 1048576 58815749 71656538112 (@Enclosure.Real.IsNear.recentre' (Real.sin qz382) Bool.true 127747 1048576 117631498 143313076224 127747 1048576 58815749 71656538112 (ep933 rfl rfl) rfl)) rfl)

noncomputable def ep935 := @ep903 545659559555 1099511627776 30907514169517 75137326107328512 Bool.false 66976091389 1099511627776 30845121258451 75137326107328512 Bool.true 19219710819287712137216 69920900639 1099511627776 110243722612337 75137326107328512 Bool.true 1072020672715722562994176 487498561013 549755813888 13776680336581 9392165763416064 (ep904 (BSN.head_sum_c_succ qz64 3 4 rfl rfl) (ep927 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep928 ep934) rfl rfl

noncomputable abbrev qz383 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 5 1)))

noncomputable def ep936 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz14 qz16 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz281 (Real.cos qz383)) (@HMul.hMul Real Real Real qz0 qz281 (@Neg.neg Real Real.instNeg (Real.sin qz383)))) Bool.true 480650577323 1099511627776 27683029510591 75137326107328512 Bool.true 25931747163 274877906944 3453512673965 9392165763416064 (BSN.cpow_neg_s_mk qz61 111131 1000 5 (@Eq.refl Real qz61) rfl)

noncomputable def ep937 := nat_lit 4660458366214177121882312546371883467567736775458058167011498635875994581641345

noncomputable def ep938 := nat_lit 5239353935325427915156407794641989501428097284785832932690943281965029435521

noncomputable def ep939 := nat_lit 12197479624189460816876755818354083955865569873452880041234330138171090047117441

noncomputable def ep940 := BSN.sin_dyadic_bound_f 2916820591 2147483648 3 2 1048576 273615 ep937 ep131 ep938 ep939 ep134 ep938 1024979 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2916820591) qz272 0 2 ep937 ep131 ep938 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2916820591) qz273 0 2 ep939 ep134 ep938 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz927 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 187546453) qz268)

noncomputable def ep941 := @Enclosure.Real.IsNear.cos_image qz383 qz927 Bool.false 187546453 1048576 427 524288 Bool.true 1024979 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz383 Bool.false 2930413339 16384000 111131 136674000 187546453 1048576 427 524288 (@Enclosure.Real.IsNear.mulLit_ff qz61 qz284 111131 1000 0 1 843808 524288 1 136674 2930413339 16384000 111131 136674000 qz380 qz559 rfl) rfl) (Enclosure.sfrac_false_div 187546453 1048576) (BSN.cos_reduce1 qz927 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 205253001998023551614976) qz271) 226375608064910080 72057594037927936 Bool.false 1024979 1048576 28 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q1 187546453 1048576 226375608064910080 72057594037927936 28 205253001998023551614976 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1024979 1048576 205253001998023551614976 151115727451828646838272 2916820591 2147483648 273615 273348 (ep940 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep942 := nat_lit 2591472138534687480119132040337553921760488474047714907420917439167537002883201

noncomputable def ep943 := nat_lit 7763937707733411584527083305423377786278609227573573056397370430938680949778561

noncomputable def ep944 := BSN.cos_dyadic_bound_f 2916820591 2147483648 3 2 1048576 273615 ep942 ep138 ep938 ep943 ep140 ep938 221196 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2916820591) qz266 0 2 ep942 ep138 ep938 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2916820591) qz267 0 2 ep943 ep140 ep938 rfl rfl rfl rfl) rfl rfl

noncomputable def ep945 := @Enclosure.Real.IsNear.sin_image qz383 qz927 Bool.false 187546453 1048576 427 524288 Bool.false 221196 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz383 Bool.false 2930413339 16384000 111131 136674000 187546453 1048576 427 524288 (@Enclosure.Real.IsNear.mulLit_ff qz61 qz284 111131 1000 0 1 843808 524288 1 136674 2930413339 16384000 111131 136674000 qz380 qz559 rfl) rfl) (Enclosure.sfrac_false_div 187546453 1048576) (BSN.sin_reduce1 qz927 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 205253001998023551614976) qz271) 226375608064910080 72057594037927936 Bool.false 221196 1048576 28 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q1 187546453 1048576 226375608064910080 72057594037927936 28 205253001998023551614976 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 221196 1048576 205253001998023551614976 151115727451828646838272 2916820591 2147483648 273615 273348 (ep944 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep946 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz281 (Real.cos qz383)) (@HMul.hMul Real Real Real qz0 qz281 (@Neg.neg Real Real.instNeg (Real.sin qz383))) Bool.true 480650577323 1099511627776 27683029510591 75137326107328512 Bool.true 25931747163 274877906944 3453512673965 9392165763416064 (@Enclosure.Real.IsNear.mulLit_ft qz281 (Real.cos qz383) 468937 1048576 1 1048576 1024979 1048576 29442043 35828269056 480650577323 1099511627776 27683029510591 75137326107328512 qz561 (@Enclosure.Real.IsNear.recentre' (Real.cos qz383) Bool.true 1024979 1048576 58884086 71656538112 1024979 1048576 29442043 35828269056 (ep941 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz281 (@Neg.neg Real Real.instNeg (Real.sin qz383)) 468937 1048576 1 1048576 55299 262144 29442043 35828269056 25931747163 274877906944 3453512673965 9392165763416064 qz561 (@Enclosure.Real.IsNear.neg (Real.sin qz383) Bool.false 55299 262144 29442043 35828269056 (@Enclosure.Real.IsNear.recentre' (Real.sin qz383) Bool.false 221196 1048576 58884086 71656538112 55299 262144 29442043 35828269056 (ep945 rfl rfl) rfl)) rfl)

noncomputable def ep947 := @ep901 480650577323 1099511627776 27683029510591 75137326107328512 Bool.true 25931747163 274877906944 3453512673965 9392165763416064 Bool.true 605359741941036731072512 275285738981 549755813888 2873474002561 1565360960569344 Bool.true 148258712856598220374016 539362055339 549755813888 2871698835091 1565360960569344 (ep902 (BSN.head_sum_c_succ qz64 4 5 rfl rfl) (ep935 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep936 ep946) rfl rfl

noncomputable abbrev qz384 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 6 1)))

noncomputable def ep948 := @Enclosure.Complex.IsNear.of_eq qz925 (Complex.mk (@HMul.hMul Real Real Real qz0 qz285 (Real.cos qz384)) (@HMul.hMul Real Real Real qz0 qz285 (@Neg.neg Real Real.instNeg (Real.sin qz384)))) Bool.true 81414204615 549755813888 12616546439785 37568663053664256 Bool.false 209149553583 549755813888 12636937653889 37568663053664256 (BSN.cpow_neg_s_mk qz61 111131 1000 6 (@Eq.refl Real qz61) rfl)

noncomputable def ep949 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz287 111131 1000 0 1 4034681531866359 2251799813685248 250000000068337 34168500000000000000 448378193317840342029 2251799813685248000 27782750007594359147 34168500000000000000000 qz380 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 250000000068337 34168500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz823) Bool.false 33845361775666394038272 18889465931478580854784 1000000000273348 136674000000000000000 4034681531866359 2251799813685248 250000000068337 34168500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 212580 524288 24973259072661432 36028797018963968 136674 1000000000000000 rfl rfl rfl rfl (ep147 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep950 := nat_lit 1575431983185295076197479037873063889395364807763844389657757441041676025390625

noncomputable def ep951 := nat_lit 1939420139293655872948452881951842167445975600479535320930540561676025390625

noncomputable def ep952 := nat_lit 4722417109277297916846540207855287983851202472090574098331411242001676025390625

noncomputable def ep953 := BSN.cos_dyadic_bound_f 2576077875 2147483648 3 2 1048576 273615 ep950 ep138 ep951 ep952 ep140 ep951 380370 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2576077875) qz266 0 2 ep950 ep138 ep951 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2576077875) qz267 0 2 ep952 ep140 ep951 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz928 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 104396183) qz306)

noncomputable def ep954 := @Enclosure.Real.IsNear.cos_image qz384 qz928 Bool.false 104396183 524288 427 524288 Bool.true 380370 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz384 Bool.false 448378193317840342029 2251799813685248000 27782750007594359147 34168500000000000000000 104396183 524288 427 524288 (ep949 rfl) rfl) (Enclosure.sfrac_false_div 104396183 524288) (BSN.cos_reduce2 qz928 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 90637682503384916033536) qz307) 226375608064910080 72057594037927936 Bool.false 380370 1048576 31 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q2 104396183 524288 226375608064910080 72057594037927936 31 90637682503384916033536 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 380370 1048576 90637682503384916033536 75557863725914323419136 2576077875 2147483648 273615 273348 (ep953 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep955 := nat_lit 2834226033622096212457103505865953527177699873494536273127218961425676025390625

noncomputable def ep956 := nat_lit 7419832931641871780260021210697194350527634755799199562908828785681676025390625

noncomputable def ep957 := BSN.sin_dyadic_bound_f 2576077875 2147483648 3 2 1048576 273615 ep955 ep131 ep951 ep956 ep134 ep951 977154 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2576077875) qz272 0 2 ep955 ep131 ep951 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2576077875) qz273 0 2 ep956 ep134 ep951 rfl rfl rfl rfl) rfl rfl

noncomputable def ep958 := @Enclosure.Real.IsNear.sin_image qz384 qz928 Bool.false 104396183 524288 427 524288 Bool.true 977154 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz384 Bool.false 448378193317840342029 2251799813685248000 27782750007594359147 34168500000000000000000 104396183 524288 427 524288 (ep949 rfl) rfl) (Enclosure.sfrac_false_div 104396183 524288) (BSN.sin_reduce2 qz928 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 90637682503384916033536) qz307) 226375608064910080 72057594037927936 Bool.false 977154 1048576 31 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q2 104396183 524288 226375608064910080 72057594037927936 31 90637682503384916033536 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 977154 1048576 90637682503384916033536 75557863725914323419136 2576077875 2147483648 273615 273348 (ep957 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep959 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz285 (Real.cos qz384)) (@HMul.hMul Real Real Real qz0 qz285 (@Neg.neg Real Real.instNeg (Real.sin qz384))) Bool.true 81414204615 549755813888 12616546439785 37568663053664256 Bool.false 209149553583 549755813888 12636937653889 37568663053664256 (@Enclosure.Real.IsNear.mulLit_ft qz285 (Real.cos qz384) 428079 1048576 1 1048576 190185 524288 29442043 35828269056 81414204615 549755813888 12616546439785 37568663053664256 qz562 (@Enclosure.Real.IsNear.recentre' (Real.cos qz384) Bool.true 380370 1048576 58884086 71656538112 190185 524288 29442043 35828269056 (ep954 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz285 (@Neg.neg Real Real.instNeg (Real.sin qz384)) 428079 1048576 1 1048576 488577 524288 29442043 35828269056 209149553583 549755813888 12636937653889 37568663053664256 qz562 (@Enclosure.Real.IsNear.neg (Real.sin qz384) Bool.true 488577 524288 29442043 35828269056 (@Enclosure.Real.IsNear.recentre' (Real.sin qz384) Bool.true 977154 1048576 58884086 71656538112 488577 524288 29442043 35828269056 (ep958 rfl rfl) rfl)) rfl)

noncomputable def ep960 := @ep899 81414204615 549755813888 12616546439785 37568663053664256 Bool.false 209149553583 549755813888 12636937653889 37568663053664256 Bool.true 196097867805422673461248 89174985899 137438953472 81579922501249 37568663053664256 Bool.true 181536242658862409187328 82553125439 137438953472 81557709696073 37568663053664256 (ep900 (BSN.head_sum_c_succ qz64 5 6 rfl rfl) (ep947 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep948 ep959) rfl rfl

noncomputable abbrev qz385 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 7 1)))

noncomputable def ep961 := @Enclosure.Complex.IsNear.of_eq qz924 (Complex.mk (@HMul.hMul Real Real Real qz0 qz288 (Real.cos qz385)) (@HMul.hMul Real Real Real qz0 qz288 (@Neg.neg Real Real.instNeg (Real.sin qz385)))) Bool.true 180412292225 549755813888 2921553289967 9392165763416064 Bool.true 206178173125 1099511627776 23345761153999 75137326107328512 (BSN.cpow_neg_s_mk qz61 111131 1000 7 (@Eq.refl Real qz61) rfl)

noncomputable def ep962 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz290 111131 1000 0 1 4381796493761783 2251799813685248 250000000068337 34168500000000000000 486953426148240706573 2251799813685248000 27782750007594359147 34168500000000000000000 qz380 (BSN.isNear_log_sfrac 7 1 4381796493761783 2251799813685248 250000000068337 34168500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz826) Bool.false 36757173121942042968064 18889465931478580854784 1000000000273348 136674000000000000000 4381796493761783 2251799813685248 250000000068337 34168500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 293399 524288 24973259072661432 36028797018963968 136674 1000000000000000 rfl rfl rfl rfl (ep158 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep963 := nat_lit 1673810890620175519722060708061001602679467472760536081262583318432967624294400

noncomputable def ep964 := nat_lit 676797894783352222474891671988886617690172101103114924884107611800202182656

noncomputable def ep965 := nat_lit 4382694659794619981388056791738450762017583102399618026761715374048191069618176

noncomputable def ep966 := BSN.sin_dyadic_bound_f 2258433852 2147483648 3 2 1048576 273615 ep963 ep131 ep964 ep965 ep134 ep964 910426 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2258433852) qz272 0 2 ep963 ep131 ep964 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2258433852) qz273 0 2 ep965 ep134 ep964 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz929 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 226755359) qz268)

noncomputable def ep967 := @Enclosure.Real.IsNear.cos_image qz385 qz929 Bool.false 226755359 1048576 853 1048576 Bool.true 910426 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz385 Bool.false 486953426148240706573 2251799813685248000 27782750007594359147 34168500000000000000000 226755359 1048576 853 1048576 (ep962 rfl) rfl) (Enclosure.sfrac_false_div 226755359 1048576) (BSN.cos_reduce1 qz929 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 158923153982069657305088) qz271) 226375608064910080 72057594037927936 Bool.false 910426 1048576 34 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q1 226755359 1048576 226375608064910080 72057594037927936 34 158923153982069657305088 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 910426 1048576 158923153982069657305088 151115727451828646838272 2258433852 2147483648 273615 273348 (ep966 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep968 := nat_lit 930195738297779000833355900776995951096455339134121429556939224734670992244736

noncomputable def ep969 := nat_lit 2789233619103770298055117918987010080053985673200158058821049458980412572368896

noncomputable def ep970 := BSN.cos_dyadic_bound_f 2258433852 2147483648 3 2 1048576 273615 ep968 ep138 ep964 ep969 ep140 ep964 520225 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2258433852) qz266 0 2 ep968 ep138 ep964 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2258433852) qz267 0 2 ep969 ep140 ep964 rfl rfl rfl rfl) rfl rfl

noncomputable def ep971 := @Enclosure.Real.IsNear.sin_image qz385 qz929 Bool.false 226755359 1048576 853 1048576 Bool.false 520225 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz385 Bool.false 486953426148240706573 2251799813685248000 27782750007594359147 34168500000000000000000 226755359 1048576 853 1048576 (ep962 rfl) rfl) (Enclosure.sfrac_false_div 226755359 1048576) (BSN.sin_reduce1 qz929 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 158923153982069657305088) qz271) 226375608064910080 72057594037927936 Bool.false 520225 1048576 34 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q1 226755359 1048576 226375608064910080 72057594037927936 34 158923153982069657305088 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 520225 1048576 158923153982069657305088 151115727451828646838272 2258433852 2147483648 273615 273348 (ep970 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep972 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz288 (Real.cos qz385)) (@HMul.hMul Real Real Real qz0 qz288 (@Neg.neg Real Real.instNeg (Real.sin qz385))) Bool.true 180412292225 549755813888 2921553289967 9392165763416064 Bool.true 206178173125 1099511627776 23345761153999 75137326107328512 (@Enclosure.Real.IsNear.mulLit_ft qz288 (Real.cos qz385) 396325 1048576 1 1048576 455213 524288 58815749 71656538112 180412292225 549755813888 2921553289967 9392165763416064 qz564 (@Enclosure.Real.IsNear.recentre' (Real.cos qz385) Bool.true 910426 1048576 117631498 143313076224 455213 524288 58815749 71656538112 (ep967 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz288 (@Neg.neg Real Real.instNeg (Real.sin qz385)) 396325 1048576 1 1048576 520225 1048576 58815749 71656538112 206178173125 1099511627776 23345761153999 75137326107328512 qz564 (@Enclosure.Real.IsNear.neg (Real.sin qz385) Bool.false 520225 1048576 58815749 71656538112 (@Enclosure.Real.IsNear.recentre' (Real.sin qz385) Bool.false 520225 1048576 117631498 143313076224 520225 1048576 58815749 71656538112 (ep971 rfl rfl) rfl)) rfl)

noncomputable def ep973 := @ep897 180412292225 549755813888 2921553289967 9392165763416064 Bool.true 206178173125 1099511627776 23345761153999 75137326107328512 Bool.true 73820143588244310720512 537112235821 549755813888 31088711887039 12522887684554752 Bool.true 119105033672500040433664 866603176637 1099511627776 62153726848715 25045775369109504 (ep898 (BSN.head_sum_c_succ qz64 6 7 rfl rfl) (ep960 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep961 ep972) rfl rfl

noncomputable abbrev qz386 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 8 1)))

noncomputable def ep974 := @Enclosure.Complex.IsNear.of_eq qz923 (Complex.mk (@HMul.hMul Real Real Real qz0 qz291 (Real.cos qz386)) (@HMul.hMul Real Real Real qz0 qz291 (@Neg.neg Real Real.instNeg (Real.sin qz386)))) Bool.false 70878924403 1099511627776 2424190030885 8348591789703168 Bool.false 191109397773 549755813888 1215283350311 4174295894851584 (BSN.cpow_neg_s_mk qz61 111131 1000 8 (@Eq.refl Real qz61) rfl)

noncomputable def ep975 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz293 111131 1000 0 1 9364972152248037 4503599627370496 500000000205011 68337000000000000000 1040738720251476599847 4503599627370496000 55565500022783077441 68337000000000000000000 qz380 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 500000000205011 68337000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz828) Bool.false 39279540158062550581248 18889465931478580854784 1000000000410022 136674000000000000000 9364972152248037 4503599627370496 500000000205011 68337000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 524288 24973259072661432 36028797018963968 136674 1000000000000000 rfl rfl rfl rfl (ep173 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep976 := nat_lit 24039046381703152571138610046818576

noncomputable def ep977 := BSN.sin_dyadic_bound_f 393757926 2147483648 2 1 1048576 273615 ep976 ep105 ep976 ep976 ep106 ep976 191189 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 393757926) qz272 0 1 ep976 ep105 ep976 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 393757926) qz273 0 1 ep976 ep106 ep976 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz930 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 121157933) qz306)

noncomputable def ep978 := @Enclosure.Real.IsNear.cos_image qz386 qz930 Bool.false 121157933 524288 853 1048576 Bool.false 191189 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz386 Bool.false 1040738720251476599847 4503599627370496000 55565500022783077441 68337000000000000000000 121157933 524288 853 1048576 (ep975 rfl) rfl) (Enclosure.sfrac_false_div 121157933 524288) (BSN.cos_reduce3 qz930 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13854125410014982045696) qz307) 226375608064910080 72057594037927936 Bool.false 191189 1048576 36 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q3 121157933 524288 226375608064910080 72057594037927936 36 13854125410014982045696 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 191189 1048576 13854125410014982045696 75557863725914323419136 393757926 2147483648 273615 273348 (ep977 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep979 := BSN.cos_dyadic_bound_f 393757926 2147483648 2 1 1048576 273615 ep976 ep91 ep976 ep976 ep92 ep976 1030998 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 393757926) qz266 0 1 ep976 ep91 ep976 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 393757926) qz267 0 1 ep976 ep92 ep976 rfl rfl rfl rfl) rfl rfl

noncomputable def ep980 := @Enclosure.Real.IsNear.sin_image qz386 qz930 Bool.false 121157933 524288 853 1048576 Bool.true 1030998 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz386 Bool.false 1040738720251476599847 4503599627370496000 55565500022783077441 68337000000000000000000 121157933 524288 853 1048576 (ep975 rfl) rfl) (Enclosure.sfrac_false_div 121157933 524288) (BSN.sin_reduce3 qz930 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13854125410014982045696) qz307) 226375608064910080 72057594037927936 Bool.false 1030998 1048576 36 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q3 121157933 524288 226375608064910080 72057594037927936 36 13854125410014982045696 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1030998 1048576 13854125410014982045696 75557863725914323419136 393757926 2147483648 273615 273348 (ep979 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep981 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz291 (Real.cos qz386)) (@HMul.hMul Real Real Real qz0 qz291 (@Neg.neg Real Real.instNeg (Real.sin qz386))) Bool.false 70878924403 1099511627776 2424190030885 8348591789703168 Bool.false 191109397773 549755813888 1215283350311 4174295894851584 (@Enclosure.Real.IsNear.mulLit_ff qz291 (Real.cos qz386) 370727 1048576 1 1048576 191189 1048576 58815749 71656538112 70878924403 1099511627776 2424190030885 8348591789703168 qz567 (@Enclosure.Real.IsNear.recentre' (Real.cos qz386) Bool.false 191189 1048576 117631498 143313076224 191189 1048576 58815749 71656538112 (ep978 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz291 (@Neg.neg Real Real.instNeg (Real.sin qz386)) 370727 1048576 1 1048576 515499 524288 58815749 71656538112 191109397773 549755813888 1215283350311 4174295894851584 qz567 (@Enclosure.Real.IsNear.neg (Real.sin qz386) Bool.true 515499 524288 58815749 71656538112 (@Enclosure.Real.IsNear.recentre' (Real.sin qz386) Bool.true 1030998 1048576 117631498 143313076224 515499 524288 58815749 71656538112 (ep980 rfl rfl) rfl)) rfl)

noncomputable def ep982 := @ep895 70878924403 1099511627776 2424190030885 8348591789703168 Bool.false 191109397773 549755813888 1215283350311 4174295894851584 Bool.true 551595047933277196255232 1003345547239 1099511627776 69449993866733 25045775369109504 Bool.true 266293129661317862391808 484384381091 1099511627776 69445426950581 25045775369109504 (ep896 (BSN.head_sum_c_succ qz64 7 8 rfl rfl) (ep973 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep974 ep981) rfl rfl

theorem EMRow34.d17 : Enclosure.Complex.IsNear (BSN.headSumC qz64 9) Bool.true 1003345547239 1099511627776 69449993866733 25045775369109504 Bool.true 484384381091 1099511627776 69445426950581 25045775369109504 := ep894 (BSN.head_sum_c_succ qz64 8 9 rfl rfl) (ep982 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz931 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 16) qz65)

noncomputable def ep983 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 17) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 16) qz931) Bool.true 637325009493 1099511627776 350251166078023 75137326107328512 Bool.false 200972922577 1099511627776 350207699509129 75137326107328512

noncomputable def ep984 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 16) qz931 Bool.true 452013993489 549755813888 83686382628881 18784331526832128 Bool.false 267506388835 1099511627776 334754245328123 75137326107328512 Bool.false

noncomputable abbrev qz932 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 15) qz65)

noncomputable def ep985 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 16) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 15) qz932) Bool.true 452013993489 549755813888 83686382628881 18784331526832128 Bool.false 267506388835 1099511627776 334754245328123 75137326107328512

noncomputable def ep986 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 15) qz932 Bool.true 282731161989 274877906944 53124310822361 12522887684554752 Bool.false 96881620261 1099511627776 106256261060731 25045775369109504 Bool.false

noncomputable abbrev qz933 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 14) qz65)

noncomputable def ep987 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 15) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 14) qz933) Bool.true 282731161989 274877906944 53124310822361 12522887684554752 Bool.false 96881620261 1099511627776 106256261060731 25045775369109504

noncomputable def ep988 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 14) qz933 Bool.true 7820247363 8589934592 151106134548577 37568663053664256 Bool.true 166687481725 1099511627776 302202600300035 75137326107328512 Bool.true

noncomputable abbrev qz934 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 13) qz65)

noncomputable def ep989 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 14) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 13) qz934) Bool.true 7820247363 8589934592 151106134548577 37568663053664256 Bool.true 166687481725 1099511627776 302202600300035 75137326107328512

noncomputable def ep990 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 13) qz934 Bool.true 797390260863 1099511627776 95013173941657 25045775369109504 Bool.false 30169274617 549755813888 47504058125975 12522887684554752 Bool.true

noncomputable abbrev qz935 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 12) qz65)

noncomputable def ep991 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 13) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 12) qz935) Bool.true 797390260863 1099511627776 95013173941657 25045775369109504 Bool.false 30169274617 549755813888 47504058125975 12522887684554752

noncomputable def ep992 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 12) qz935 Bool.true 549826142637 549755813888 133583936717219 37568663053664256 Bool.true 36516317947 1099511627776 267199073170147 75137326107328512 Bool.false

noncomputable abbrev qz936 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 11) qz65)

noncomputable def ep993 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 12) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 11) qz936) Bool.true 549826142637 549755813888 133583936717219 37568663053664256 Bool.true 36516317947 1099511627776 267199073170147 75137326107328512

noncomputable def ep994 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 11) qz936 Bool.true 204473449797 274877906944 62122574193781 18784331526832128 Bool.false 8635401971 68719476736 31068080102207 9392165763416064 Bool.true

noncomputable abbrev qz937 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 10) qz65)

noncomputable def ep995 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 11) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 10) qz937) Bool.true 204473449797 274877906944 62122574193781 18784331526832128 Bool.false 8635401971 68719476736 31068080102207 9392165763416064

noncomputable def ep996 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 10) qz937 Bool.true 382740426157 549755813888 114477060471071 37568663053664256 Bool.true 205556404741 1099511627776 228948429085075 75137326107328512 Bool.true

noncomputable abbrev qz938 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 9) qz65)

noncomputable def ep997 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 10) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 9) qz938) Bool.true 382740426157 549755813888 114477060471071 37568663053664256 Bool.true 205556404741 1099511627776 228948429085075 75137326107328512

noncomputable def ep998 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 9) qz938 Bool.true 1003345547239 1099511627776 69449993866733 25045775369109504 Bool.true 484384381091 1099511627776 69445426950581 25045775369109504 Bool.false

noncomputable abbrev qz387 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 9 1)))

noncomputable def ep999 := @Enclosure.Complex.IsNear.of_eq qz938 (Complex.mk (@HMul.hMul Real Real Real qz0 qz294 (Real.cos qz387)) (@HMul.hMul Real Real Real qz0 qz294 (@Neg.neg Real Real.instNeg (Real.sin qz387)))) Bool.false 237864694925 1099511627776 20604139341943 75137326107328512 Bool.false 139413988175 549755813888 5153037058333 18784331526832128 (BSN.cpow_neg_s_mk qz61 111131 1000 9 (@Eq.refl Real qz61) rfl)

noncomputable def ep1000 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz296 111131 1000 0 1 9895417793173221 4503599627370496 500000000205011 68337000000000000000 1099687674773133222951 4503599627370496000 55565500022783077441 68337000000000000000000 qz380 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 500000000205011 68337000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz838) Bool.false 41504390431577613533184 18889465931478580854784 1000000000410022 136674000000000000000 9895417793173221 4503599627370496 500000000205011 68337000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 61752 524288 24973259072661432 36028797018963968 136674 1000000000000000 rfl rfl rfl rfl (ep205 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1001 := nat_lit 5292223431275151865379245355895868081

noncomputable def ep1002 := BSN.sin_dyadic_bound_f 1516734421 2147483648 2 1 1048576 273615 ep1001 ep105 ep1001 ep1001 ep106 ep1001 680537 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1516734421) qz272 0 1 ep1001 ep105 ep1001 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1516734421) qz273 0 1 ep1001 ep106 ep1001 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz939 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 256040989) qz268)

noncomputable def ep1003 := @Enclosure.Real.IsNear.cos_image qz387 qz939 Bool.false 256040989 1048576 853 1048576 Bool.false 680537 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz387 Bool.false 1099687674773133222951 4503599627370496000 55565500022783077441 68337000000000000000000 256040989 1048576 853 1048576 (ep1000 rfl) rfl) (Enclosure.sfrac_false_div 256040989 1048576) (BSN.cos_reduce3 qz939 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 106730696511115921195008) qz271) 226375608064910080 72057594037927936 Bool.false 680537 1048576 38 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q3 256040989 1048576 226375608064910080 72057594037927936 38 106730696511115921195008 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 680537 1048576 106730696511115921195008 151115727451828646838272 1516734421 2147483648 273615 273348 (ep1002 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1004 := nat_lit 189117290753066252572775964303104523916338964884895173879386719463086892895841

noncomputable def ep1005 := nat_lit 28007628846537742059162508496161772467784912558530825772626607128554622561

noncomputable def ep1006 := nat_lit 567295857001505682234209567892321248204081324829568459986614905175003569442401

noncomputable def ep1007 := BSN.cos_dyadic_bound_f 1516734421 2147483648 3 2 1048576 273615 ep1004 ep138 ep1005 ep1006 ep140 ep1005 797734 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1516734421) qz266 0 2 ep1004 ep138 ep1005 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1516734421) qz267 0 2 ep1006 ep140 ep1005 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1008 := @Enclosure.Real.IsNear.sin_image qz387 qz939 Bool.false 256040989 1048576 853 1048576 Bool.true 797734 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz387 Bool.false 1099687674773133222951 4503599627370496000 55565500022783077441 68337000000000000000000 256040989 1048576 853 1048576 (ep1000 rfl) rfl) (Enclosure.sfrac_false_div 256040989 1048576) (BSN.sin_reduce3 qz939 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 106730696511115921195008) qz271) 226375608064910080 72057594037927936 Bool.false 797734 1048576 38 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q3 256040989 1048576 226375608064910080 72057594037927936 38 106730696511115921195008 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 797734 1048576 106730696511115921195008 151115727451828646838272 1516734421 2147483648 273615 273348 (ep1007 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1009 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz294 (Real.cos qz387)) (@HMul.hMul Real Real Real qz0 qz294 (@Neg.neg Real Real.instNeg (Real.sin qz387))) Bool.false 237864694925 1099511627776 20604139341943 75137326107328512 Bool.false 139413988175 549755813888 5153037058333 18784331526832128 (@Enclosure.Real.IsNear.mulLit_ff qz294 (Real.cos qz387) 349525 1048576 1 1048576 680537 1048576 58815749 71656538112 237864694925 1099511627776 20604139341943 75137326107328512 qz569 (@Enclosure.Real.IsNear.recentre' (Real.cos qz387) Bool.false 680537 1048576 117631498 143313076224 680537 1048576 58815749 71656538112 (ep1003 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz294 (@Neg.neg Real Real.instNeg (Real.sin qz387)) 349525 1048576 1 1048576 398867 524288 58815749 71656538112 139413988175 549755813888 5153037058333 18784331526832128 qz569 (@Enclosure.Real.IsNear.neg (Real.sin qz387) Bool.true 398867 524288 58815749 71656538112 (@Enclosure.Real.IsNear.recentre' (Real.sin qz387) Bool.true 797734 1048576 117631498 143313076224 398867 524288 58815749 71656538112 (ep1008 rfl rfl) rfl)) rfl)

noncomputable def ep1010 := @ep998 237864694925 1099511627776 20604139341943 75137326107328512 Bool.false 139413988175 549755813888 5153037058333 18784331526832128 Bool.true 841655097959125996273664 382740426157 549755813888 114477060471071 37568663053664256 Bool.true 113005828588279596843008 205556404741 1099511627776 228948429085075 75137326107328512 EMRow34.d17 (ep999 ep1009) rfl rfl

noncomputable abbrev qz388 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 10 1)))

noncomputable def ep1011 := @Enclosure.Complex.IsNear.of_eq qz937 (Complex.mk (@HMul.hMul Real Real Real qz0 qz297 (Real.cos qz388)) (@HMul.hMul Real Real Real qz0 qz297 (@Neg.neg Real Real.instNeg (Real.sin qz388)))) Bool.true 26206473437 549755813888 3256029305497 12522887684554752 Bool.false 343722836277 1099511627776 6532070577527 25045775369109504 (BSN.cpow_neg_s_mk qz61 111131 1000 10 (@Eq.refl Real qz61) rfl)

noncomputable def ep1012 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz299 111131 1000 0 1 10369917190100709 4503599627370496 500000000205011 68337000000000000000 1152419267253081891879 4503599627370496000 55565500022783077441 68337000000000000000000 qz380 (BSN.isNear_log_sfrac 10 1 10369917190100709 4503599627370496 500000000205011 68337000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz840) Bool.false 43494585150108164161536 18889465931478580854784 1000000000410022 136674000000000000000 10369917190100709 4503599627370496 500000000205011 68337000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 116991 524288 24973259072661432 36028797018963968 136674 1000000000000000 rfl rfl rfl rfl (ep216 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1013 := nat_lit 3092485999706298257700215416995818663137349515278473958225289440857882095657216

noncomputable def ep1014 := nat_lit 7455237952824153409151448505822171127500981658607027209043219600910284103936

noncomputable def ep1015 := nat_lit 9262547523213246466282343353975811647157046582518207820257781883371825718763776

noncomputable def ep1016 := BSN.cos_dyadic_bound_f 3048299878 2147483648 3 2 1048576 273615 ep1013 ep138 ep1014 ep1015 ep140 ep1014 158066 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3048299878) qz266 0 2 ep1013 ep138 ep1014 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3048299878) qz267 0 2 ep1015 ep140 ep1014 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz940 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 268318519) qz268)

noncomputable def ep1017 := @Enclosure.Real.IsNear.cos_image qz388 qz940 Bool.false 268318519 1048576 427 524288 Bool.true 158066 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz388 Bool.false 1152419267253081891879 4503599627370496000 55565500022783077441 68337000000000000000000 268318519 1048576 427 524288 (ep1012 rfl) rfl) (Enclosure.sfrac_false_div 268318519 1048576) (BSN.cos_reduce2 qz940 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 214505034352180601028608) qz271) 226375608064910080 72057594037927936 Bool.false 158066 1048576 40 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q2 268318519 1048576 226375608064910080 72057594037927936 40 214505034352180601028608 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 158066 1048576 214505034352180601028608 151115727451828646838272 3048299878 2147483648 273615 273348 (ep1016 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1018 := nat_lit 5560510609109077541133066591787815856745228342174367503038286417863459544899840

noncomputable def ep1019 := nat_lit 14551171686219202073638453014244377062031072640152265416285632548383777395712256

noncomputable def ep1020 := BSN.sin_dyadic_bound_f 3048299878 2147483648 3 2 1048576 273615 ep1018 ep131 ep1014 ep1019 ep134 ep1014 1036593 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3048299878) qz272 0 2 ep1018 ep131 ep1014 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3048299878) qz273 0 2 ep1019 ep134 ep1014 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1021 := @Enclosure.Real.IsNear.sin_image qz388 qz940 Bool.false 268318519 1048576 427 524288 Bool.true 1036593 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz388 Bool.false 1152419267253081891879 4503599627370496000 55565500022783077441 68337000000000000000000 268318519 1048576 427 524288 (ep1012 rfl) rfl) (Enclosure.sfrac_false_div 268318519 1048576) (BSN.sin_reduce2 qz940 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 214505034352180601028608) qz271) 226375608064910080 72057594037927936 Bool.false 1036593 1048576 40 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q2 268318519 1048576 226375608064910080 72057594037927936 40 214505034352180601028608 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1036593 1048576 214505034352180601028608 151115727451828646838272 3048299878 2147483648 273615 273348 (ep1020 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1022 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz297 (Real.cos qz388)) (@HMul.hMul Real Real Real qz0 qz297 (@Neg.neg Real Real.instNeg (Real.sin qz388))) Bool.true 26206473437 549755813888 3256029305497 12522887684554752 Bool.false 343722836277 1099511627776 6532070577527 25045775369109504 (@Enclosure.Real.IsNear.mulLit_ft qz297 (Real.cos qz388) 331589 1048576 1 1048576 79033 524288 29442043 35828269056 26206473437 549755813888 3256029305497 12522887684554752 qz571 (@Enclosure.Real.IsNear.recentre' (Real.cos qz388) Bool.true 158066 1048576 58884086 71656538112 79033 524288 29442043 35828269056 (ep1017 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz297 (@Neg.neg Real Real.instNeg (Real.sin qz388)) 331589 1048576 1 1048576 1036593 1048576 29442043 35828269056 343722836277 1099511627776 6532070577527 25045775369109504 qz571 (@Enclosure.Real.IsNear.neg (Real.sin qz388) Bool.true 1036593 1048576 29442043 35828269056 (@Enclosure.Real.IsNear.recentre' (Real.sin qz388) Bool.true 1036593 1048576 58884086 71656538112 1036593 1048576 29442043 35828269056 (ep1021 rfl rfl) rfl)) rfl)

noncomputable def ep1023 := @ep996 26206473437 549755813888 3256029305497 12522887684554752 Bool.false 343722836277 1099511627776 6532070577527 25045775369109504 Bool.true 224820935623273686761472 204473449797 274877906944 62122574193781 18784331526832128 Bool.false 151915598042148619943936 8635401971 68719476736 31068080102207 9392165763416064 (ep997 (BSN.head_sum_c_succ qz64 9 10 rfl rfl) (ep1010 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1011 ep1022) rfl rfl

noncomputable abbrev qz389 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 11 1)))

noncomputable def ep1024 := @Enclosure.Complex.IsNear.of_eq qz936 (Complex.mk (@HMul.hMul Real Real Real qz0 qz300 (Real.cos qz389)) (@HMul.hMul Real Real Real qz0 qz300 (@Neg.neg Real Real.instNeg (Real.sin qz389)))) Bool.true 140879243043 549755813888 3112929443219 12522887684554752 Bool.true 174682749483 1099511627776 6218144117497 25045775369109504 (BSN.cpow_neg_s_mk qz61 111131 1000 11 (@Eq.refl Real qz61) rfl)

noncomputable def ep1025 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz302 111131 1000 0 1 10799156221662949 4503599627370496 500000000205011 68337000000000000000 1200121030069625185319 4503599627370496000 55565500022783077441 68337000000000000000000 qz380 (BSN.isNear_log_sfrac 11 1 10799156221662949 4503599627370496 500000000205011 68337000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz842) Bool.false 45294944137145793642496 18889465931478580854784 1000000000410022 136674000000000000000 10799156221662949 4503599627370496 500000000205011 68337000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 166961 524288 24973259072661432 36028797018963968 136674 1000000000000000 rfl rfl rfl rfl (ep231 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1026 := nat_lit 1456936009017093812395090261407357345819120489620333225905856092471466341072705

noncomputable def ep1027 := nat_lit 512829106638357208082388530312146504019208297564356994783340103725781778241

noncomputable def ep1028 := nat_lit 3814954490776878835078817293684478144710236849857197108904735786781141532311361

noncomputable def ep1029 := BSN.sin_dyadic_bound_f 2181456631 2147483648 3 2 1048576 273615 ep1026 ep131 ep1027 ep1028 ep134 ep1027 891198 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2181456631) qz272 0 2 ep1026 ep131 ep1027 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2181456631) qz273 0 2 ep1028 ep134 ep1027 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz941 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 279424951) qz268)

noncomputable def ep1030 := @Enclosure.Real.IsNear.cos_image qz389 qz941 Bool.false 279424951 1048576 427 524288 Bool.true 891198 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz389 Bool.false 1200121030069625185319 4503599627370496000 55565500022783077441 68337000000000000000000 279424951 1048576 427 524288 (ep1025 rfl) rfl) (Enclosure.sfrac_false_div 279424951 1048576) (BSN.cos_reduce1 qz941 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 153506363667986620874752) qz271) 226375608064910080 72057594037927936 Bool.false 891198 1048576 42 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q1 279424951 1048576 226375608064910080 72057594037927936 42 153506363667986620874752 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 891198 1048576 153506363667986620874752 151115727451828646838272 2181456631 2147483648 273615 273348 (ep1029 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1031 := nat_lit 809636817945780276756420095684226146123519920143547061945379313641359425830721

noncomputable def ep1032 := nat_lit 2427884795624064115853095509992054145362521343835512471846571260716626713935681

noncomputable def ep1033 := BSN.cos_dyadic_bound_f 2181456631 2147483648 3 2 1048576 273615 ep1031 ep138 ep1027 ep1032 ep140 ep1027 552519 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2181456631) qz266 0 2 ep1031 ep138 ep1027 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2181456631) qz267 0 2 ep1032 ep140 ep1027 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1034 := @Enclosure.Real.IsNear.sin_image qz389 qz941 Bool.false 279424951 1048576 427 524288 Bool.false 552519 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz389 Bool.false 1200121030069625185319 4503599627370496000 55565500022783077441 68337000000000000000000 279424951 1048576 427 524288 (ep1025 rfl) rfl) (Enclosure.sfrac_false_div 279424951 1048576) (BSN.sin_reduce1 qz941 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 153506363667986620874752) qz271) 226375608064910080 72057594037927936 Bool.false 552519 1048576 42 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q1 279424951 1048576 226375608064910080 72057594037927936 42 153506363667986620874752 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 552519 1048576 153506363667986620874752 151115727451828646838272 2181456631 2147483648 273615 273348 (ep1033 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1035 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz300 (Real.cos qz389)) (@HMul.hMul Real Real Real qz0 qz300 (@Neg.neg Real Real.instNeg (Real.sin qz389))) Bool.true 140879243043 549755813888 3112929443219 12522887684554752 Bool.true 174682749483 1099511627776 6218144117497 25045775369109504 (@Enclosure.Real.IsNear.mulLit_ft qz300 (Real.cos qz389) 316157 1048576 1 1048576 445599 524288 29442043 35828269056 140879243043 549755813888 3112929443219 12522887684554752 qz572 (@Enclosure.Real.IsNear.recentre' (Real.cos qz389) Bool.true 891198 1048576 58884086 71656538112 445599 524288 29442043 35828269056 (ep1030 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz300 (@Neg.neg Real Real.instNeg (Real.sin qz389)) 316157 1048576 1 1048576 552519 1048576 29442043 35828269056 174682749483 1099511627776 6218144117497 25045775369109504 qz572 (@Enclosure.Real.IsNear.neg (Real.sin qz389) Bool.false 552519 1048576 29442043 35828269056 (@Enclosure.Real.IsNear.recentre' (Real.sin qz389) Bool.false 552519 1048576 58884086 71656538112 552519 1048576 29442043 35828269056 (ep1034 rfl rfl) rfl)) rfl)

noncomputable def ep1036 := @ep994 140879243043 549755813888 3112929443219 12522887684554752 Bool.true 174682749483 1099511627776 6218144117497 25045775369109504 Bool.true 151135059271151756771328 549826142637 549755813888 133583936717219 37568663053664256 Bool.true 2509382261643245780992 36516317947 1099511627776 267199073170147 75137326107328512 (ep995 (BSN.head_sum_c_succ qz64 10 11 rfl rfl) (ep1023 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1024 ep1035) rfl rfl

noncomputable abbrev qz390 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 12 1)))

noncomputable def ep1037 := @Enclosure.Complex.IsNear.of_eq qz935 (Complex.mk (@HMul.hMul Real Real Real qz0 qz303 (Real.cos qz390)) (@HMul.hMul Real Real Real qz0 qz303 (@Neg.neg Real Real.instNeg (Real.sin qz390)))) Bool.false 302262024411 1099511627776 17871648390533 75137326107328512 Bool.false 96854867181 1099511627776 17825275585703 75137326107328512 (BSN.cpow_neg_s_mk qz61 111131 1000 12 (@Eq.refl Real qz61) rfl)

noncomputable def ep1038 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz305 111131 1000 0 1 11191020447815397 4503599627370496 500000000205011 68337000000000000000 1243669293386172884007 4503599627370496000 55565500022783077441 68337000000000000000000 qz380 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 500000000205011 68337000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz845) Bool.false 46938541828353910898688 18889465931478580854784 1000000000410022 136674000000000000000 11191020447815397 4503599627370496 500000000205011 68337000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 212580 524288 24973259072661432 36028797018963968 136674 1000000000000000 rfl rfl rfl rfl (ep242 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1039 := nat_lit 3458038893708408117517878171833516745769203697349651146050676333235496892241505

noncomputable def ep1040 := nat_lit 2886236949717903131512989045694719357363161541555282477354395739192517727841

noncomputable def ep1041 := nat_lit 9052095576079620845571993229680466693293135993419901591836054708229513498596961

noncomputable def ep1042 := BSN.sin_dyadic_bound_f 2707331883 2147483648 3 2 1048576 273615 ep1039 ep131 ep1040 ep1041 ep134 ep1040 998563 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2707331883) qz272 0 2 ep1039 ep131 ep1040 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2707331883) qz273 0 2 ep1041 ep134 ep1040 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz942 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 144782161) qz306)

noncomputable def ep1043 := @Enclosure.Real.IsNear.cos_image qz390 qz942 Bool.false 144782161 524288 853 1048576 Bool.false 998563 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz390 Bool.false 1243669293386172884007 4503599627370496000 55565500022783077441 68337000000000000000000 144782161 524288 853 1048576 (ep1038 rfl) rfl) (Enclosure.sfrac_false_div 144782161 524288) (BSN.cos_reduce3 qz942 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 95255772345119268667392) qz307) 226375608064910080 72057594037927936 Bool.false 998563 1048576 43 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q3 144782161 524288 226375608064910080 72057594037927936 43 95255772345119268667392 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 998563 1048576 95255772345119268667392 75557863725914323419136 2707331883 2147483648 273615 273348 (ep1042 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1044 := nat_lit 1922415490704545800012826979483373622919496792546052984462533249903806059124321

noncomputable def ep1045 := nat_lit 5761473998214201593775454960358731430043764054555048388432890958233033141917281

noncomputable def ep1046 := BSN.cos_dyadic_bound_f 2707331883 2147483648 3 2 1048576 273615 ep1044 ep138 ep1040 ep1045 ep140 ep1040 319973 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2707331883) qz266 0 2 ep1044 ep138 ep1040 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2707331883) qz267 0 2 ep1045 ep140 ep1040 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1047 := @Enclosure.Real.IsNear.sin_image qz390 qz942 Bool.false 144782161 524288 853 1048576 Bool.true 319973 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz390 Bool.false 1243669293386172884007 4503599627370496000 55565500022783077441 68337000000000000000000 144782161 524288 853 1048576 (ep1038 rfl) rfl) (Enclosure.sfrac_false_div 144782161 524288) (BSN.sin_reduce3 qz942 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 95255772345119268667392) qz307) 226375608064910080 72057594037927936 Bool.false 319973 1048576 43 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q3 144782161 524288 226375608064910080 72057594037927936 43 95255772345119268667392 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 319973 1048576 95255772345119268667392 75557863725914323419136 2707331883 2147483648 273615 273348 (ep1046 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1048 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz303 (Real.cos qz390)) (@HMul.hMul Real Real Real qz0 qz303 (@Neg.neg Real Real.instNeg (Real.sin qz390))) Bool.false 302262024411 1099511627776 17871648390533 75137326107328512 Bool.false 96854867181 1099511627776 17825275585703 75137326107328512 (@Enclosure.Real.IsNear.mulLit_ff qz303 (Real.cos qz390) 302697 1048576 1 1048576 998563 1048576 58815749 71656538112 302262024411 1099511627776 17871648390533 75137326107328512 qz573 (@Enclosure.Real.IsNear.recentre' (Real.cos qz390) Bool.false 998563 1048576 117631498 143313076224 998563 1048576 58815749 71656538112 (ep1043 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz303 (@Neg.neg Real Real.instNeg (Real.sin qz390)) 302697 1048576 1 1048576 319973 1048576 58815749 71656538112 96854867181 1099511627776 17825275585703 75137326107328512 qz573 (@Enclosure.Real.IsNear.neg (Real.sin qz390) Bool.true 319973 1048576 58815749 71656538112 (@Enclosure.Real.IsNear.recentre' (Real.sin qz390) Bool.true 319973 1048576 117631498 143313076224 319973 1048576 58815749 71656538112 (ep1047 rfl rfl) rfl)) rfl)

noncomputable def ep1049 := @ep992 302262024411 1099511627776 17871648390533 75137326107328512 Bool.false 96854867181 1099511627776 17825275585703 75137326107328512 Bool.true 438369931847103198265344 797390260863 1099511627776 95013173941657 25045775369109504 Bool.false 66342936485917657923584 30169274617 549755813888 47504058125975 12522887684554752 (ep993 (BSN.head_sum_c_succ qz64 11 12 rfl rfl) (ep1036 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1037 ep1048) rfl rfl

noncomputable abbrev qz391 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 13 1)))

noncomputable def ep1050 := @Enclosure.Complex.IsNear.of_eq qz934 (Complex.mk (@HMul.hMul Real Real Real qz0 qz308 (Real.cos qz391)) (@HMul.hMul Real Real Real qz0 qz308 (@Neg.neg Real Real.instNeg (Real.sin qz391)))) Bool.true 203601401601 1099511627776 17172747272183 75137326107328512 Bool.true 227026030959 1099511627776 17178251544185 75137326107328512 (BSN.cpow_neg_s_mk qz61 111131 1000 13 (@Eq.refl Real qz61) rfl)

noncomputable def ep1051 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz310 111131 1000 0 1 11551497052968677 4503599627370496 500000000205011 68337000000000000000 1283729418993462043687 4503599627370496000 55565500022783077441 68337000000000000000000 qz380 (BSN.isNear_log_sfrac 13 1 11551497052968677 4503599627370496 500000000205011 68337000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz848) Bool.false 48450490295254733815808 18889465931478580854784 1000000000410022 136674000000000000000 11551497052968677 4503599627370496 500000000205011 68337000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 254545 524288 24973259072661432 36028797018963968 136674 1000000000000000 rfl rfl rfl rfl (ep253 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1052 := nat_lit 6074649719671118907240163723322455056

noncomputable def ep1053 := BSN.sin_dyadic_bound_f 1569930078 2147483648 2 1 1048576 273615 ep1052 ep105 ep1052 ep1052 ep106 ep1052 700087 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1569930078) qz272 0 1 ep1052 ep105 ep1052 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1569930078) qz273 0 1 ep1052 ep106 ep1052 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz943 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 149445773) qz306)

noncomputable def ep1054 := @Enclosure.Real.IsNear.cos_image qz391 qz943 Bool.false 149445773 524288 427 524288 Bool.true 700087 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz391 Bool.false 1283729418993462043687 4503599627370496000 55565500022783077441 68337000000000000000000 149445773 524288 427 524288 (ep1051 rfl) rfl) (Enclosure.sfrac_false_div 149445773 524288) (BSN.cos_reduce1 qz943 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 55237004031124167458816) qz307) 226375608064910080 72057594037927936 Bool.false 700087 1048576 45 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q1 149445773 524288 226375608064910080 72057594037927936 45 55237004031124167458816 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 700087 1048576 55237004031124167458816 75557863725914323419136 1569930078 2147483648 273615 273348 (ep1053 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1055 := nat_lit 217082000775873584969715497717314211721720218237148416832581472020905893724416

noncomputable def ep1056 := nat_lit 36901369216700403524014495842444722184693170033478792326602244239139963136

noncomputable def ep1057 := nat_lit 651172199589187354102098464160257745720791268371378292913091211574239401246976

noncomputable def ep1058 := BSN.cos_dyadic_bound_f 1569930078 2147483648 3 2 1048576 273615 ep1055 ep138 ep1056 ep1057 ep140 ep1056 780633 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1569930078) qz266 0 2 ep1055 ep138 ep1056 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1569930078) qz267 0 2 ep1057 ep140 ep1056 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1059 := @Enclosure.Real.IsNear.sin_image qz391 qz943 Bool.false 149445773 524288 427 524288 Bool.false 780633 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz391 Bool.false 1283729418993462043687 4503599627370496000 55565500022783077441 68337000000000000000000 149445773 524288 427 524288 (ep1051 rfl) rfl) (Enclosure.sfrac_false_div 149445773 524288) (BSN.sin_reduce1 qz943 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 55237004031124167458816) qz307) 226375608064910080 72057594037927936 Bool.false 780633 1048576 45 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q1 149445773 524288 226375608064910080 72057594037927936 45 55237004031124167458816 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 780633 1048576 55237004031124167458816 75557863725914323419136 1569930078 2147483648 273615 273348 (ep1058 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1060 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz308 (Real.cos qz391)) (@HMul.hMul Real Real Real qz0 qz308 (@Neg.neg Real Real.instNeg (Real.sin qz391))) Bool.true 203601401601 1099511627776 17172747272183 75137326107328512 Bool.true 227026030959 1099511627776 17178251544185 75137326107328512 (@Enclosure.Real.IsNear.mulLit_ft qz308 (Real.cos qz391) 290823 1048576 1 1048576 700087 1048576 29442043 35828269056 203601401601 1099511627776 17172747272183 75137326107328512 qz574 (@Enclosure.Real.IsNear.recentre' (Real.cos qz391) Bool.true 700087 1048576 58884086 71656538112 700087 1048576 29442043 35828269056 (ep1054 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz308 (@Neg.neg Real Real.instNeg (Real.sin qz391)) 290823 1048576 1 1048576 780633 1048576 29442043 35828269056 227026030959 1099511627776 17178251544185 75137326107328512 qz574 (@Enclosure.Real.IsNear.neg (Real.sin qz391) Bool.false 780633 1048576 29442043 35828269056 (@Enclosure.Real.IsNear.recentre' (Real.sin qz391) Bool.false 780633 1048576 58884086 71656538112 780633 1048576 29442043 35828269056 (ep1059 rfl rfl) rfl)) rfl)

noncomputable def ep1061 := @ep990 203601401601 1099511627776 17172747272183 75137326107328512 Bool.true 227026030959 1099511627776 17178251544185 75137326107328512 Bool.true 1100601972185996999000064 7820247363 8589934592 151106134548577 37568663053664256 Bool.true 91637412180668501196800 166687481725 1099511627776 302202600300035 75137326107328512 (ep991 (BSN.head_sum_c_succ qz64 12 13 rfl rfl) (ep1049 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1050 ep1060) rfl rfl

noncomputable abbrev qz392 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 14 1)))

noncomputable def ep1062 := @Enclosure.Complex.IsNear.of_eq qz933 (Complex.mk (@HMul.hMul Real Real Real qz0 qz311 (Real.cos qz392)) (@HMul.hMul Real Real Real qz0 qz311 (@Neg.neg Real Real.instNeg (Real.sin qz392)))) Bool.true 32483246373 274877906944 4133398959253 18784331526832128 Bool.false 131784550993 549755813888 8283091441079 37568663053664256 (BSN.cpow_neg_s_mk qz61 111131 1000 14 (@Eq.refl Real qz61) rfl)

noncomputable def ep1063 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz313 111131 1000 0 1 11885250371606245 4503599627370496 500000000205011 68337000000000000000 264163951809394722619 900719925474099200 55565500022783077441 68337000000000000000000 qz380 (BSN.isNear_log_sfrac 14 1 11885250371606245 4503599627370496 500000000205011 68337000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz851) Bool.false 49850353174629559828480 18889465931478580854784 1000000000410022 136674000000000000000 11885250371606245 4503599627370496 500000000205011 68337000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 293399 524288 24973259072661432 36028797018963968 136674 1000000000000000 rfl rfl rfl rfl (ep268 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1064 := nat_lit 1166240635062988537403940131563978920637443935371558413539118534613123063715361

noncomputable def ep1065 := nat_lit 1063472929072396563282292379037366647887978648792163726081572874940094453281

noncomputable def ep1066 := nat_lit 3496594959330820819085255809933862028616555848817090913165192458089489002239521

noncomputable def ep1067 := BSN.cos_dyadic_bound_f 2389685811 2147483648 3 2 1048576 273615 ep1064 ep138 ep1065 ep1066 ep140 ep1065 463644 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2389685811) qz266 0 2 ep1064 ep138 ep1065 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2389685811) qz267 0 2 ep1066 ep140 ep1065 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz944 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 153763657) qz306)

noncomputable def ep1068 := @Enclosure.Real.IsNear.cos_image qz392 qz944 Bool.false 153763657 524288 427 524288 Bool.true 463644 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz392 Bool.false 264163951809394722619 900719925474099200 55565500022783077441 68337000000000000000000 153763657 524288 427 524288 (ep1063 rfl) rfl) (Enclosure.sfrac_false_div 153763657 524288) (BSN.cos_reduce2 qz944 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 84079594775175143358464) qz307) 226375608064910080 72057594037927936 Bool.false 463644 1048576 46 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q2 153763657 524288 226375608064910080 72057594037927936 46 84079594775175143358464 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 463644 1048576 84079594775175143358464 75557863725914323419136 2389685811 2147483648 273615 273348 (ep1067 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1069 := nat_lit 2098382364770121450076466402911932163829088700749771413389548104003669439125025

noncomputable def ep1070 := nat_lit 5494041522988962774812097819965190406884366060341833055701827249640659806688801

noncomputable def ep1071 := BSN.sin_dyadic_bound_f 2389685811 2147483648 3 2 1048576 273615 ep1069 ep131 ep1065 ep1070 ep134 ep1065 940502 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2389685811) qz272 0 2 ep1069 ep131 ep1065 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2389685811) qz273 0 2 ep1070 ep134 ep1065 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1072 := @Enclosure.Real.IsNear.sin_image qz392 qz944 Bool.false 153763657 524288 427 524288 Bool.true 940502 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz392 Bool.false 264163951809394722619 900719925474099200 55565500022783077441 68337000000000000000000 153763657 524288 427 524288 (ep1063 rfl) rfl) (Enclosure.sfrac_false_div 153763657 524288) (BSN.sin_reduce2 qz944 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 84079594775175143358464) qz307) 226375608064910080 72057594037927936 Bool.false 940502 1048576 46 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q2 153763657 524288 226375608064910080 72057594037927936 46 84079594775175143358464 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 940502 1048576 84079594775175143358464 75557863725914323419136 2389685811 2147483648 273615 273348 (ep1071 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1073 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz311 (Real.cos qz392)) (@HMul.hMul Real Real Real qz0 qz311 (@Neg.neg Real Real.instNeg (Real.sin qz392))) Bool.true 32483246373 274877906944 4133398959253 18784331526832128 Bool.false 131784550993 549755813888 8283091441079 37568663053664256 (@Enclosure.Real.IsNear.mulLit_ft qz311 (Real.cos qz392) 280243 1048576 1 1048576 115911 262144 29442043 35828269056 32483246373 274877906944 4133398959253 18784331526832128 qz575 (@Enclosure.Real.IsNear.recentre' (Real.cos qz392) Bool.true 463644 1048576 58884086 71656538112 115911 262144 29442043 35828269056 (ep1068 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz311 (@Neg.neg Real Real.instNeg (Real.sin qz392)) 280243 1048576 1 1048576 470251 524288 29442043 35828269056 131784550993 549755813888 8283091441079 37568663053664256 qz575 (@Enclosure.Real.IsNear.neg (Real.sin qz392) Bool.true 470251 524288 29442043 35828269056 (@Enclosure.Real.IsNear.recentre' (Real.sin qz392) Bool.true 940502 1048576 58884086 71656538112 470251 524288 29442043 35828269056 (ep1072 rfl rfl) rfl)) rfl)

noncomputable def ep1074 := @ep988 32483246373 274877906944 4133398959253 18784331526832128 Bool.false 131784550993 549755813888 8283091441079 37568663053664256 Bool.true 2428642188605666623488 282731161989 274877906944 53124310822361 12522887684554752 Bool.false 53261233997374205984768 96881620261 1099511627776 106256261060731 25045775369109504 (ep989 (BSN.head_sum_c_succ qz64 13 14 rfl rfl) (ep1061 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1062 ep1073) rfl rfl

noncomputable abbrev qz393 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 15 1)))

noncomputable def ep1075 := @Enclosure.Complex.IsNear.of_eq qz932 (Complex.mk (@HMul.hMul Real Real Real qz0 qz314 (Real.cos qz393)) (@HMul.hMul Real Real Real qz0 qz314 (@Neg.neg Real Real.instNeg (Real.sin qz393)))) Bool.false 113448330489 549755813888 7999832790679 37568663053664256 Bool.false 85312384287 549755813888 7992731072965 37568663053664256 (BSN.cpow_neg_s_mk qz61 111131 1000 15 (@Eq.refl Real qz61) rfl)

noncomputable def ep1076 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz316 111131 1000 0 1 12195965485668069 4503599627370496 500000000205011 68337000000000000000 1355349840387778176039 4503599627370496000 55565500022783077441 68337000000000000000000 qz380 (BSN.isNear_log_sfrac 15 1 12195965485668069 4503599627370496 500000000205011 68337000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz854) Bool.false 51153586820399524478976 18889465931478580854784 1000000000410022 136674000000000000000 12195965485668069 4503599627370496 500000000205011 68337000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 329571 524288 24973259072661432 36028797018963968 136674 1000000000000000 rfl rfl rfl rfl (ep278 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1077 := nat_lit 1006025917014010465599965214956815763428809068959226172994455933722673806401345

noncomputable def ep1078 := nat_lit 244570828653818503898495788275737011223286677111312771632798277361965555521

noncomputable def ep1079 := nat_lit 2634433810837921227565025617420166282390614621225507375259979105396035834437441

noncomputable def ep1080 := BSN.sin_dyadic_bound_f 1988614409 2147483648 3 2 1048576 273615 ep1077 ep131 ep1078 ep1079 ep134 ep1078 838058 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1988614409) qz272 0 2 ep1077 ep131 ep1078 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1988614409) qz273 0 2 ep1079 ep134 ep1078 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz945 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 315566975) qz268)

noncomputable def ep1081 := @Enclosure.Real.IsNear.cos_image qz393 qz945 Bool.false 315566975 1048576 427 524288 Bool.false 838058 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz393 Bool.false 1355349840387778176039 4503599627370496000 55565500022783077441 68337000000000000000000 315566975 1048576 427 524288 (ep1076 rfl) rfl) (Enclosure.sfrac_false_div 315566975 1048576) (BSN.cos_reduce3 qz945 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 139936298620118022225920) qz271) 226375608064910080 72057594037927936 Bool.false 838058 1048576 47 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q3 315566975 1048576 226375608064910080 72057594037927936 47 139936298620118022225920 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 838058 1048576 139936298620118022225920 151115727451828646838272 1988614409 2147483648 273615 273348 (ep1080 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1082 := nat_lit 559011985376074178001713339770797973909882054611619568450978984635868543803201

noncomputable def ep1083 := nat_lit 1676546814470914896997343027735842447707199590480636079809671357352881700298561

noncomputable def ep1084 := BSN.cos_dyadic_bound_f 1988614409 2147483648 3 2 1048576 273615 ep1082 ep138 ep1078 ep1083 ep140 ep1078 630214 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1988614409) qz266 0 2 ep1082 ep138 ep1078 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1988614409) qz267 0 2 ep1083 ep140 ep1078 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1085 := @Enclosure.Real.IsNear.sin_image qz393 qz945 Bool.false 315566975 1048576 427 524288 Bool.true 630214 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz393 Bool.false 1355349840387778176039 4503599627370496000 55565500022783077441 68337000000000000000000 315566975 1048576 427 524288 (ep1076 rfl) rfl) (Enclosure.sfrac_false_div 315566975 1048576) (BSN.sin_reduce3 qz945 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 139936298620118022225920) qz271) 226375608064910080 72057594037927936 Bool.false 630214 1048576 47 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q3 315566975 1048576 226375608064910080 72057594037927936 47 139936298620118022225920 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 630214 1048576 139936298620118022225920 151115727451828646838272 1988614409 2147483648 273615 273348 (ep1084 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1086 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz314 (Real.cos qz393)) (@HMul.hMul Real Real Real qz0 qz314 (@Neg.neg Real Real.instNeg (Real.sin qz393))) Bool.false 113448330489 549755813888 7999832790679 37568663053664256 Bool.false 85312384287 549755813888 7992731072965 37568663053664256 (@Enclosure.Real.IsNear.mulLit_ff qz314 (Real.cos qz393) 270741 1048576 1 1048576 419029 524288 29442043 35828269056 113448330489 549755813888 7999832790679 37568663053664256 qz576 (@Enclosure.Real.IsNear.recentre' (Real.cos qz393) Bool.false 838058 1048576 58884086 71656538112 419029 524288 29442043 35828269056 (ep1081 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz314 (@Neg.neg Real Real.instNeg (Real.sin qz393)) 270741 1048576 1 1048576 315107 524288 29442043 35828269056 85312384287 549755813888 7992731072965 37568663053664256 qz576 (@Enclosure.Real.IsNear.neg (Real.sin qz393) Bool.true 315107 524288 29442043 35828269056 (@Enclosure.Real.IsNear.recentre' (Real.sin qz393) Bool.true 630214 1048576 58884086 71656538112 315107 524288 29442043 35828269056 (ep1085 rfl rfl) rfl)) rfl)

noncomputable def ep1087 := @ep986 113448330489 549755813888 7999832790679 37568663053664256 Bool.false 85312384287 549755813888 7992731072965 37568663053664256 Bool.true 124248660439655163887616 452013993489 549755813888 83686382628881 18784331526832128 Bool.false 147063192514225221140480 267506388835 1099511627776 334754245328123 75137326107328512 (ep987 (BSN.head_sum_c_succ qz64 14 15 rfl rfl) (ep1074 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1075 ep1086) rfl rfl

noncomputable abbrev qz394 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 16 1)))

noncomputable def ep1088 := @Enclosure.Complex.IsNear.of_eq qz931 (Complex.mk (@HMul.hMul Real Real Real qz0 qz317 (Real.cos qz394)) (@HMul.hMul Real Real Real qz0 qz317 (@Neg.neg Real Real.instNeg (Real.sin qz394)))) Bool.false 266702977485 1099511627776 15505635562499 75137326107328512 Bool.true 33266733129 549755813888 7726727090503 37568663053664256 (BSN.cpow_neg_s_mk qz61 111131 1000 16 (@Eq.refl Real qz61) rfl)

noncomputable def ep1089 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz319 111131 1000 0 1 3121657384082679 1125899906842624 125000000068337 17084250000000000000 346912906750492199949 1125899906842624000 13891375007594359147 17084250000000000000000 qz380 (BSN.isNear_log_sfrac 16 1 3121657384082679 1125899906842624 125000000068337 17084250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz857) Bool.false 52372720210750067441664 18889465931478580854784 1000000000546696 136674000000000000000 3121657384082679 1125899906842624 125000000068337 17084250000000000000 (BSN.log_rat_reduce_isNear 16 1 4 32 32 0 524288 24973259072661432 36028797018963968 136674 1000000000000000 rfl rfl rfl rfl (ep293 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1090 := nat_lit 75974862927002971140188496107136016

noncomputable def ep1091 := BSN.cos_dyadic_bound_f 525009886 2147483648 2 1 1048576 273615 ep1090 ep91 ep1090 ep1090 ep92 ep1090 1017395 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 525009886) qz266 0 1 ep1090 ep91 ep1090 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 525009886) qz267 0 1 ep1090 ep92 ep1090 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz946 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 323087821) qz268)

noncomputable def ep1092 := @Enclosure.Real.IsNear.cos_image qz394 qz946 Bool.false 323087821 1048576 427 524288 Bool.false 1017395 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz394 Bool.false 346912906750492199949 1125899906842624000 13891375007594359147 17084250000000000000000 323087821 1048576 427 524288 (ep1089 rfl) rfl) (Enclosure.sfrac_false_div 323087821 1048576) (BSN.cos_reduce0 qz946 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 36944286388310593503232) qz271) 226375608064910080 72057594037927936 Bool.false 1017395 1048576 49 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q0 323087821 1048576 226375608064910080 72057594037927936 49 36944286388310593503232 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1017395 1048576 36944286388310593503232 151115727451828646838272 525009886 2147483648 273615 273348 (ep1091 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1093 := BSN.sin_dyadic_bound_f 525009886 2147483648 2 1 1048576 273615 ep1090 ep105 ep1090 ep1090 ep106 ep1090 253806 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 525009886) qz272 0 1 ep1090 ep105 ep1090 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 525009886) qz273 0 1 ep1090 ep106 ep1090 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1094 := @Enclosure.Real.IsNear.sin_image qz394 qz946 Bool.false 323087821 1048576 427 524288 Bool.false 253806 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz394 Bool.false 346912906750492199949 1125899906842624000 13891375007594359147 17084250000000000000000 323087821 1048576 427 524288 (ep1089 rfl) rfl) (Enclosure.sfrac_false_div 323087821 1048576) (BSN.sin_reduce0 qz946 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 36944286388310593503232) qz271) 226375608064910080 72057594037927936 Bool.false 253806 1048576 49 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q0 323087821 1048576 226375608064910080 72057594037927936 49 36944286388310593503232 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 253806 1048576 36944286388310593503232 151115727451828646838272 525009886 2147483648 273615 273348 (ep1093 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1095 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz317 (Real.cos qz394)) (@HMul.hMul Real Real Real qz0 qz317 (@Neg.neg Real Real.instNeg (Real.sin qz394))) Bool.false 266702977485 1099511627776 15505635562499 75137326107328512 Bool.true 33266733129 549755813888 7726727090503 37568663053664256 (@Enclosure.Real.IsNear.mulLit_ff qz317 (Real.cos qz394) 262143 1048576 1 1048576 1017395 1048576 29442043 35828269056 266702977485 1099511627776 15505635562499 75137326107328512 qz577 (@Enclosure.Real.IsNear.recentre' (Real.cos qz394) Bool.false 1017395 1048576 58884086 71656538112 1017395 1048576 29442043 35828269056 (ep1092 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz317 (@Neg.neg Real Real.instNeg (Real.sin qz394)) 262143 1048576 1 1048576 126903 524288 29442043 35828269056 33266733129 549755813888 7726727090503 37568663053664256 qz577 (@Enclosure.Real.IsNear.neg (Real.sin qz394) Bool.false 126903 524288 29442043 35828269056 (@Enclosure.Real.IsNear.recentre' (Real.sin qz394) Bool.false 253806 1048576 58884086 71656538112 126903 524288 29442043 35828269056 (ep1094 rfl rfl) rfl)) rfl)

noncomputable def ep1096 := @ep984 266702977485 1099511627776 15505635562499 75137326107328512 Bool.true 33266733129 549755813888 7726727090503 37568663053664256 Bool.true 350373129305001541238784 637325009493 1099511627776 350251166078023 75137326107328512 Bool.false 110486032620768645349376 200972922577 1099511627776 350207699509129 75137326107328512 (ep985 (BSN.head_sum_c_succ qz64 15 16 rfl rfl) (ep1087 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1088 ep1095) rfl rfl

theorem EMRow34.d18 : Enclosure.Complex.IsNear (BSN.headSumC qz64 17) Bool.true 637325009493 1099511627776 350251166078023 75137326107328512 Bool.false 200972922577 1099511627776 350207699509129 75137326107328512 := ep983 (BSN.head_sum_c_succ qz64 16 17 rfl rfl) (ep1096 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz947 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 24) qz65)

noncomputable def ep1097 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 25) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 24) qz947) Bool.false 82834314697 1099511627776 460250574735509 75137326107328512 Bool.true 15465575669 137438953472 57520807946767 9392165763416064

noncomputable def ep1098 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 24) qz947 Bool.false 1720642235 68719476736 223814683924499 37568663053664256 Bool.false 46895408043 549755813888 223746733438571 37568663053664256 Bool.false

noncomputable abbrev qz948 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 23) qz65)

noncomputable def ep1099 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 24) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 23) qz948) Bool.false 1720642235 68719476736 223814683924499 37568663053664256 Bool.false 46895408043 549755813888 223746733438571 37568663053664256

noncomputable def ep1100 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 23) qz948 Bool.false 124353674065 549755813888 108675132049703 18784331526832128 Bool.false 77072077617 549755813888 217307446390327 37568663053664256 Bool.true

noncomputable abbrev qz949 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 22) qz65)

noncomputable def ep1101 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 23) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 22) qz949) Bool.false 124353674065 549755813888 108675132049703 18784331526832128 Bool.false 77072077617 549755813888 217307446390327 37568663053664256

noncomputable def ep1102 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 22) qz949 Bool.false 359826578537 1099511627776 140505943336561 25045775369109504 Bool.true 52262222397 1099511627776 140467689058447 25045775369109504 Bool.true

noncomputable abbrev qz950 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 21) qz65)

noncomputable def ep1103 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 22) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 21) qz950) Bool.false 359826578537 1099511627776 140505943336561 25045775369109504 Bool.true 52262222397 1099511627776 140467689058447 25045775369109504

noncomputable def ep1104 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 21) qz950 Bool.false 220516917323 1099511627776 407976400048801 75137326107328512 Bool.true 247609640629 1099511627776 407828165615185 75137326107328512 Bool.false

noncomputable abbrev qz951 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 20) qz65)

noncomputable def ep1105 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 21) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 20) qz951) Bool.false 220516917323 1099511627776 407976400048801 75137326107328512 Bool.true 247609640629 1099511627776 407828165615185 75137326107328512

noncomputable def ep1106 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 20) qz951 Bool.true 12171053737 549755813888 21895250342405 4174295894851584 Bool.true 269756175555 1099511627776 43781242471573 8348591789703168 Bool.false

noncomputable abbrev qz952 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 19) qz65)

noncomputable def ep1107 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 20) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 19) qz952) Bool.true 12171053737 549755813888 21895250342405 4174295894851584 Bool.true 269756175555 1099511627776 43781242471573 8348591789703168

noncomputable def ep1108 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 19) qz952 Bool.true 123285736955 549755813888 189943110220591 37568663053664256 Bool.true 37604856569 274877906944 94958031457175 18784331526832128 Bool.false

noncomputable abbrev qz953 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 18) qz65)

noncomputable def ep1109 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 19) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 18) qz953) Bool.true 123285736955 549755813888 189943110220591 37568663053664256 Bool.true 37604856569 274877906944 94958031457175 18784331526832128

noncomputable def ep1110 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 18) qz953 Bool.true 216545200993 549755813888 182640664262149 37568663053664256 Bool.false 29504771667 1099511627776 365229057347987 75137326107328512 Bool.false

noncomputable abbrev qz954 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 17) qz65)

noncomputable def ep1111 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 18) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 17) qz954) Bool.true 216545200993 549755813888 182640664262149 37568663053664256 Bool.false 29504771667 1099511627776 365229057347987 75137326107328512

noncomputable def ep1112 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 17) qz954 Bool.true 637325009493 1099511627776 350251166078023 75137326107328512 Bool.false 200972922577 1099511627776 350207699509129 75137326107328512 Bool.false

noncomputable abbrev qz395 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 17 1)))

noncomputable def ep1113 := @Enclosure.Complex.IsNear.of_eq qz954 (Complex.mk (@HMul.hMul Real Real Real qz0 qz320 (Real.cos qz395)) (@HMul.hMul Real Real Real qz0 qz320 (@Neg.neg Real Real.instNeg (Real.sin qz395)))) Bool.false 204234607507 1099511627776 15030162446275 75137326107328512 Bool.true 85734075455 549755813888 7510678919429 37568663053664256 (BSN.cpow_neg_s_mk qz61 111131 1000 17 (@Eq.refl Real qz61) rfl)

noncomputable def ep1114 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz322 111131 1000 0 1 3189913004350711 1125899906842624 125000000068337 17084250000000000000 354498222086498864141 1125899906842624000 13891375007594359147 17084250000000000000000 qz380 (BSN.isNear_log_sfrac 17 1 3189913004350711 1125899906842624 125000000068337 17084250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz868) Bool.false 53517859495200818200576 18889465931478580854784 1000000000546696 136674000000000000000 3189913004350711 1125899906842624 125000000068337 17084250000000000000 (BSN.log_rat_reduce_isNear 17 1 4 34 32 31784 524288 24973259072661432 36028797018963968 136674 1000000000000000 rfl rfl rfl rfl (ep324 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1115 := nat_lit 180816371382791292332328884320548844282534000994067260277913377942460750785121

noncomputable def ep1116 := nat_lit 25603244988452285836219481461441817236873701075369539766328777470717356641

noncomputable def ep1117 := nat_lit 542397907658396972425314213998723649213128255580051041754207476272440817642081

noncomputable def ep1118 := BSN.cos_dyadic_bound_f 1499812181 2147483648 3 2 1048576 273615 ep1115 ep138 ep1116 ep1117 ep140 ep1116 803071 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1499812181) qz266 0 2 ep1115 ep138 ep1116 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1499812181) qz267 0 2 ep1117 ep140 ep1116 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz622 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 82538049) (@Nat.cast Real Real.instNatCast 262144))

noncomputable def ep1119 := @Enclosure.Real.IsNear.cos_image qz395 qz622 Bool.false 82538049 262144 427 524288 Bool.false 803071 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz395 Bool.false 354498222086498864141 1125899906842624000 13891375007594359147 17084250000000000000000 82538049 262144 427 524288 (ep1114 rfl) rfl) (Enclosure.sfrac_false_div 82538049 262144) (BSN.cos_reduce0 qz622 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26384974935650077769728) qz566) 226375608064910080 72057594037927936 Bool.false 803071 1048576 50 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q0 82538049 262144 226375608064910080 72057594037927936 50 26384974935650077769728 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 803071 1048576 26384974935650077769728 37778931862957161709568 1499812181 2147483648 273615 273348 (ep1118 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1120 := nat_lit 5059964919685934525818890888612051121

noncomputable def ep1121 := BSN.sin_dyadic_bound_f 1499812181 2147483648 2 1 1048576 273615 ep1120 ep105 ep1120 ep1120 ep106 ep1120 674230 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1499812181) qz272 0 1 ep1120 ep105 ep1120 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1499812181) qz273 0 1 ep1120 ep106 ep1120 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1122 := @Enclosure.Real.IsNear.sin_image qz395 qz622 Bool.false 82538049 262144 427 524288 Bool.false 674230 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz395 Bool.false 354498222086498864141 1125899906842624000 13891375007594359147 17084250000000000000000 82538049 262144 427 524288 (ep1114 rfl) rfl) (Enclosure.sfrac_false_div 82538049 262144) (BSN.sin_reduce0 qz622 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26384974935650077769728) qz566) 226375608064910080 72057594037927936 Bool.false 674230 1048576 50 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q0 82538049 262144 226375608064910080 72057594037927936 50 26384974935650077769728 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 674230 1048576 26384974935650077769728 37778931862957161709568 1499812181 2147483648 273615 273348 (ep1121 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1123 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz320 (Real.cos qz395)) (@HMul.hMul Real Real Real qz0 qz320 (@Neg.neg Real Real.instNeg (Real.sin qz395))) Bool.false 204234607507 1099511627776 15030162446275 75137326107328512 Bool.true 85734075455 549755813888 7510678919429 37568663053664256 (@Enclosure.Real.IsNear.mulLit_ff qz320 (Real.cos qz395) 254317 1048576 1 1048576 803071 1048576 29442043 35828269056 204234607507 1099511627776 15030162446275 75137326107328512 qz578 (@Enclosure.Real.IsNear.recentre' (Real.cos qz395) Bool.false 803071 1048576 58884086 71656538112 803071 1048576 29442043 35828269056 (ep1119 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz320 (@Neg.neg Real Real.instNeg (Real.sin qz395)) 254317 1048576 1 1048576 337115 524288 29442043 35828269056 85734075455 549755813888 7510678919429 37568663053664256 qz578 (@Enclosure.Real.IsNear.neg (Real.sin qz395) Bool.false 337115 524288 29442043 35828269056 (@Enclosure.Real.IsNear.recentre' (Real.sin qz395) Bool.false 674230 1048576 58884086 71656538112 337115 524288 29442043 35828269056 (ep1122 rfl rfl) rfl)) rfl)

noncomputable def ep1124 := @ep1112 204234607507 1099511627776 15030162446275 75137326107328512 Bool.true 85734075455 549755813888 7510678919429 37568663053664256 Bool.true 476187932861789043163136 216545200993 549755813888 182640664262149 37568663053664256 Bool.false 16220419761371187511296 29504771667 1099511627776 365229057347987 75137326107328512 EMRow34.d18 (ep1113 ep1123) rfl rfl

noncomputable abbrev qz396 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 18 1)))

noncomputable def ep1125 := @Enclosure.Complex.IsNear.of_eq qz953 (Complex.mk (@HMul.hMul Real Real Real qz0 qz323 (Real.cos qz396)) (@HMul.hMul Real Real Real qz0 qz323 (@Neg.neg Real Real.instNeg (Real.sin qz396)))) Bool.false 46629732019 274877906944 1217074326407 6261443842277376 Bool.true 179924197943 1099511627776 4867689493571 25045775369109504 (BSN.cpow_neg_s_mk qz61 111131 1000 18 (@Eq.refl Real qz61) rfl)

noncomputable def ep1126 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz325 111131 1000 0 1 3254268794313975 1125899906842624 125000000068337 17084250000000000000 14466005815236254229 45035996273704960 13891375007594359147 17084250000000000000000 qz380 (BSN.isNear_log_sfrac 18 1 3254268794313975 1125899906842624 125000000068337 17084250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz871) Bool.false 54597570484265130393600 18889465931478580854784 1000000000546696 136674000000000000000 3254268794313975 1125899906842624 125000000068337 17084250000000000000 (BSN.log_rat_reduce_isNear 18 1 4 36 32 61752 524288 24973259072661432 36028797018963968 136674 1000000000000000 rfl rfl rfl rfl (ep338 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1127 := nat_lit 263592386618737623344230965821524339729059448248330434231782089878036301618721

noncomputable def ep1128 := nat_lit 54403763854731739963104883158635830136878185759624918169385410590710046241

noncomputable def ep1129 := nat_lit 790668352328503406552766687698255747526904588373472052859007498812927484763681

noncomputable def ep1130 := BSN.cos_dyadic_bound_f 1647986381 2147483648 3 2 1048576 273615 ep1127 ep138 ep1128 ep1129 ep140 ep1128 754676 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1647986381) qz266 0 2 ep1127 ep138 ep1128 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1647986381) qz267 0 2 ep1129 ep140 ep1128 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz623 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 21050809) (@Nat.cast Real Real.instNatCast 65536))

noncomputable def ep1131 := @Enclosure.Real.IsNear.cos_image qz396 qz623 Bool.false 21050809 65536 427 524288 Bool.false 754676 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz396 Bool.false 14466005815236254229 45035996273704960 13891375007594359147 17084250000000000000000 21050809 65536 427 524288 (ep1126 rfl) rfl) (Enclosure.sfrac_false_div 21050809 65536) (BSN.cos_reduce0 qz623 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 7247920754962284412928) qz583) 226375608064910080 72057594037927936 Bool.false 754676 1048576 51 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q0 21050809 65536 226375608064910080 72057594037927936 51 7247920754962284412928 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 754676 1048576 7247920754962284412928 9444732965739290427392 1647986381 2147483648 273615 273348 (ep1130 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1132 := nat_lit 7375890716024183337364966073124619921

noncomputable def ep1133 := BSN.sin_dyadic_bound_f 1647986381 2147483648 2 1 1048576 273615 ep1132 ep105 ep1132 ep1132 ep106 ep1132 727993 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1647986381) qz272 0 1 ep1132 ep105 ep1132 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1647986381) qz273 0 1 ep1132 ep106 ep1132 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1134 := @Enclosure.Real.IsNear.sin_image qz396 qz623 Bool.false 21050809 65536 427 524288 Bool.false 727993 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz396 Bool.false 14466005815236254229 45035996273704960 13891375007594359147 17084250000000000000000 21050809 65536 427 524288 (ep1126 rfl) rfl) (Enclosure.sfrac_false_div 21050809 65536) (BSN.sin_reduce0 qz623 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 7247920754962284412928) qz583) 226375608064910080 72057594037927936 Bool.false 727993 1048576 51 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q0 21050809 65536 226375608064910080 72057594037927936 51 7247920754962284412928 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 727993 1048576 7247920754962284412928 9444732965739290427392 1647986381 2147483648 273615 273348 (ep1133 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1135 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz323 (Real.cos qz396)) (@HMul.hMul Real Real Real qz0 qz323 (@Neg.neg Real Real.instNeg (Real.sin qz396))) Bool.false 46629732019 274877906944 1217074326407 6261443842277376 Bool.true 179924197943 1099511627776 4867689493571 25045775369109504 (@Enclosure.Real.IsNear.mulLit_ff qz323 (Real.cos qz396) 247151 1048576 1 1048576 188669 262144 29442043 35828269056 46629732019 274877906944 1217074326407 6261443842277376 qz579 (@Enclosure.Real.IsNear.recentre' (Real.cos qz396) Bool.false 754676 1048576 58884086 71656538112 188669 262144 29442043 35828269056 (ep1131 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz323 (@Neg.neg Real Real.instNeg (Real.sin qz396)) 247151 1048576 1 1048576 727993 1048576 29442043 35828269056 179924197943 1099511627776 4867689493571 25045775369109504 qz579 (@Enclosure.Real.IsNear.neg (Real.sin qz396) Bool.false 727993 1048576 29442043 35828269056 (@Enclosure.Real.IsNear.recentre' (Real.sin qz396) Bool.false 727993 1048576 58884086 71656538112 727993 1048576 29442043 35828269056 (ep1134 rfl rfl) rfl)) rfl)

noncomputable def ep1136 := @ep1110 46629732019 274877906944 1217074326407 6261443842277376 Bool.true 179924197943 1099511627776 4867689493571 25045775369109504 Bool.true 33888525330238951915520 123285736955 549755813888 189943110220591 37568663053664256 Bool.true 165387908233856785842176 37604856569 274877906944 94958031457175 18784331526832128 (ep1111 (BSN.head_sum_c_succ qz64 17 18 rfl rfl) (ep1124 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1125 ep1135) rfl rfl

noncomputable abbrev qz397 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 19 1)))

noncomputable def ep1137 := @Enclosure.Complex.IsNear.of_eq qz952 (Complex.mk (@HMul.hMul Real Real Real qz0 qz326 (Real.cos qz397)) (@HMul.hMul Real Real Real qz0 qz326 (@Neg.neg Real Real.instNeg (Real.sin qz397)))) Bool.false 55557341609 274877906944 3557071430527 18784331526832128 Bool.true 119336749279 1099511627776 14199056415457 75137326107328512 (BSN.cpow_neg_s_mk qz61 111131 1000 19 (@Eq.refl Real qz61) rfl)

noncomputable def ep1138 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz328 111131 1000 0 1 3315143513283831 1125899906842624 125000000068337 17084250000000000000 368415213774745422861 1125899906842624000 13891375007594359147 17084250000000000000000 qz380 (BSN.isNear_log_sfrac 19 1 3315143513283831 1125899906842624 125000000068337 17084250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz874) Bool.false 55618878793361701994496 18889465931478580854784 1000000000546696 136674000000000000000 3315143513283831 1125899906842624 125000000068337 17084250000000000000 (BSN.log_rat_reduce_isNear 19 1 4 38 32 90099 524288 24973259072661432 36028797018963968 136674 1000000000000000 rfl rfl rfl rfl (ep352 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1139 := nat_lit 1254363396422956952242283591611597056

noncomputable def ep1140 := BSN.cos_dyadic_bound_f 1058292804 2147483648 2 1 1048576 273615 ep1139 ep91 ep1139 ep1139 ep92 ep1139 923804 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1058292804) qz266 0 1 ep1139 ep91 ep1139 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1058292804) qz267 0 1 ep1139 ep92 ep1139 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz955 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 343113405) qz268)

noncomputable def ep1141 := @Enclosure.Real.IsNear.cos_image qz397 qz955 Bool.false 343113405 1048576 427 524288 Bool.false 923804 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz397 Bool.false 368415213774745422861 1125899906842624000 13891375007594359147 17084250000000000000000 343113405 1048576 427 524288 (ep1138 rfl) rfl) (Enclosure.sfrac_false_div 343113405 1048576) (BSN.cos_reduce0 qz955 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 74470735649906905579520) qz271) 226375608064910080 72057594037927936 Bool.false 923804 1048576 52 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q0 343113405 1048576 226375608064910080 72057594037927936 52 74470735649906905579520 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 923804 1048576 74470735649906905579520 151115727451828646838272 1058292804 2147483648 273615 273348 (ep1140 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1142 := BSN.sin_dyadic_bound_f 1058292804 2147483648 2 1 1048576 273615 ep1139 ep105 ep1139 ep1139 ep106 ep1139 496081 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1058292804) qz272 0 1 ep1139 ep105 ep1139 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1058292804) qz273 0 1 ep1139 ep106 ep1139 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1143 := @Enclosure.Real.IsNear.sin_image qz397 qz955 Bool.false 343113405 1048576 427 524288 Bool.false 496081 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz397 Bool.false 368415213774745422861 1125899906842624000 13891375007594359147 17084250000000000000000 343113405 1048576 427 524288 (ep1138 rfl) rfl) (Enclosure.sfrac_false_div 343113405 1048576) (BSN.sin_reduce0 qz955 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 74470735649906905579520) qz271) 226375608064910080 72057594037927936 Bool.false 496081 1048576 52 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q0 343113405 1048576 226375608064910080 72057594037927936 52 74470735649906905579520 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 496081 1048576 74470735649906905579520 151115727451828646838272 1058292804 2147483648 273615 273348 (ep1142 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1144 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz326 (Real.cos qz397)) (@HMul.hMul Real Real Real qz0 qz326 (@Neg.neg Real Real.instNeg (Real.sin qz397))) Bool.false 55557341609 274877906944 3557071430527 18784331526832128 Bool.true 119336749279 1099511627776 14199056415457 75137326107328512 (@Enclosure.Real.IsNear.mulLit_ff qz326 (Real.cos qz397) 240559 1048576 1 1048576 230951 262144 29442043 35828269056 55557341609 274877906944 3557071430527 18784331526832128 qz580 (@Enclosure.Real.IsNear.recentre' (Real.cos qz397) Bool.false 923804 1048576 58884086 71656538112 230951 262144 29442043 35828269056 (ep1141 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz326 (@Neg.neg Real Real.instNeg (Real.sin qz397)) 240559 1048576 1 1048576 496081 1048576 29442043 35828269056 119336749279 1099511627776 14199056415457 75137326107328512 qz580 (@Enclosure.Real.IsNear.neg (Real.sin qz397) Bool.false 496081 1048576 29442043 35828269056 (@Enclosure.Real.IsNear.recentre' (Real.sin qz397) Bool.false 496081 1048576 58884086 71656538112 496081 1048576 29442043 35828269056 (ep1143 rfl rfl) rfl)) rfl)

noncomputable def ep1145 := @ep1108 55557341609 274877906944 3557071430527 18784331526832128 Bool.true 119336749279 1099511627776 14199056415457 75137326107328512 Bool.true 3345553776529509449728 12171053737 549755813888 21895250342405 4174295894851584 Bool.true 74150012921776617553920 269756175555 1099511627776 43781242471573 8348591789703168 (ep1109 (BSN.head_sum_c_succ qz64 18 19 rfl rfl) (ep1136 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1137 ep1144) rfl rfl

noncomputable abbrev qz398 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 20 1)))

noncomputable def ep1146 := @Enclosure.Complex.IsNear.of_eq qz951 (Complex.mk (@HMul.hMul Real Real Real qz0 qz329 (Real.cos qz398)) (@HMul.hMul Real Real Real qz0 qz329 (@Neg.neg Real Real.instNeg (Real.sin qz398)))) Bool.false 244859024797 1099511627776 13861893885511 75137326107328512 Bool.false 11073267463 549755813888 3449245842757 18784331526832128 (BSN.cpow_neg_s_mk qz61 111131 1000 20 (@Eq.refl Real qz61) rfl)

noncomputable def ep1147 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz331 111131 1000 0 1 3372893643545847 1125899906842624 125000000068337 17084250000000000000 374833043500893522957 1125899906842624000 13891375007594359147 17084250000000000000000 qz380 (BSN.isNear_log_sfrac 20 1 3372893643545847 1125899906842624 125000000068337 17084250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz877) Bool.false 56587765202795681021952 18889465931478580854784 1000000000546696 136674000000000000000 3372893643545847 1125899906842624 125000000068337 17084250000000000000 (BSN.log_rat_reduce_isNear 20 1 4 40 32 116991 524288 24973259072661432 36028797018963968 136674 1000000000000000 rfl rfl rfl rfl (ep363 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1148 := nat_lit 6583481460047660995574288991419007881830481071314853486504547609514395164115200

noncomputable def ep1149 := nat_lit 10445506827148701001563793844570969275540336656995279911763678668964204544256

noncomputable def ep1150 := nat_lit 17225539670023728520120605977968096216443242260760909630511912068978426241515776

noncomputable def ep1151 := BSN.sin_dyadic_bound_f 3179553886 2147483648 3 2 1048576 273615 ep1148 ep131 ep1149 ep1150 ep134 ep1149 1044313 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3179553886) qz272 0 2 ep1148 ep131 ep1149 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3179553886) qz273 0 2 ep1150 ep134 ep1149 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz956 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 349090475) qz268)

noncomputable def ep1152 := @Enclosure.Real.IsNear.cos_image qz398 qz956 Bool.false 349090475 1048576 853 1048576 Bool.false 1044313 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz398 Bool.false 374833043500893522957 1125899906842624000 13891375007594359147 17084250000000000000000 349090475 1048576 853 1048576 (ep1147 rfl) rfl) (Enclosure.sfrac_false_div 349090475 1048576) (BSN.cos_reduce3 qz956 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 223741214035649306296320) qz271) 226375608064910080 72057594037927936 Bool.false 1044313 1048576 52 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q3 349090475 1048576 226375608064910080 72057594037927936 52 223741214035649306296320 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1044313 1048576 223741214035649306296320 151115727451828646838272 3179553886 2147483648 273615 273348 (ep1151 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1153 := nat_lit 3662132147505211086875300014719258142917174078133583172463310306916425848750336

noncomputable def ep1154 := nat_lit 10965505428861335858622772456468632490200441561086758957566403563411349137162496

noncomputable def ep1155 := BSN.cos_dyadic_bound_f 3179553886 2147483648 3 2 1048576 273615 ep1153 ep138 ep1149 ep1154 ep140 ep1149 94454 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3179553886) qz266 0 2 ep1153 ep138 ep1149 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3179553886) qz267 0 2 ep1154 ep140 ep1149 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1156 := @Enclosure.Real.IsNear.sin_image qz398 qz956 Bool.false 349090475 1048576 853 1048576 Bool.true 94454 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz398 Bool.false 374833043500893522957 1125899906842624000 13891375007594359147 17084250000000000000000 349090475 1048576 853 1048576 (ep1147 rfl) rfl) (Enclosure.sfrac_false_div 349090475 1048576) (BSN.sin_reduce3 qz956 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 223741214035649306296320) qz271) 226375608064910080 72057594037927936 Bool.false 94454 1048576 52 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q3 349090475 1048576 226375608064910080 72057594037927936 52 223741214035649306296320 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 94454 1048576 223741214035649306296320 151115727451828646838272 3179553886 2147483648 273615 273348 (ep1155 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1157 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz329 (Real.cos qz398)) (@HMul.hMul Real Real Real qz0 qz329 (@Neg.neg Real Real.instNeg (Real.sin qz398))) Bool.false 244859024797 1099511627776 13861893885511 75137326107328512 Bool.false 11073267463 549755813888 3449245842757 18784331526832128 (@Enclosure.Real.IsNear.mulLit_ff qz329 (Real.cos qz398) 234469 1048576 1 1048576 1044313 1048576 58815749 71656538112 244859024797 1099511627776 13861893885511 75137326107328512 qz581 (@Enclosure.Real.IsNear.recentre' (Real.cos qz398) Bool.false 1044313 1048576 117631498 143313076224 1044313 1048576 58815749 71656538112 (ep1152 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz329 (@Neg.neg Real Real.instNeg (Real.sin qz398)) 234469 1048576 1 1048576 47227 524288 58815749 71656538112 11073267463 549755813888 3449245842757 18784331526832128 qz581 (@Enclosure.Real.IsNear.neg (Real.sin qz398) Bool.true 47227 524288 58815749 71656538112 (@Enclosure.Real.IsNear.recentre' (Real.sin qz398) Bool.true 94454 1048576 117631498 143313076224 47227 524288 58815749 71656538112 (ep1156 rfl rfl) rfl)) rfl)

noncomputable def ep1158 := @ep1106 244859024797 1099511627776 13861893885511 75137326107328512 Bool.false 11073267463 549755813888 3449245842757 18784331526832128 Bool.false 121230457358978671181824 220516917323 1099511627776 407976400048801 75137326107328512 Bool.true 136124839510511087255552 247609640629 1099511627776 407828165615185 75137326107328512 (ep1107 (BSN.head_sum_c_succ qz64 19 20 rfl rfl) (ep1145 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1146 ep1157) rfl rfl

noncomputable abbrev qz399 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 21 1)))

noncomputable def ep1159 := @Enclosure.Complex.IsNear.of_eq qz950 (Complex.mk (@HMul.hMul Real Real Real qz0 qz332 (Real.cos qz399)) (@HMul.hMul Real Real Real qz0 qz332 (@Neg.neg Real Real.instNeg (Real.sin qz399)))) Bool.false 69654830607 549755813888 6770714980441 37568663053664256 Bool.false 24418427279 137438953472 3393725390039 18784331526832128 (BSN.cpow_neg_s_mk qz61 111131 1000 21 (@Eq.refl Real qz61) rfl)

noncomputable def ep1160 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz334 111131 1000 0 1 3427826275261687 1125899906842624 125000000068337 17084250000000000000 380937761796106537997 1125899906842624000 13891375007594359147 17084250000000000000000 qz380 (BSN.isNear_log_sfrac 21 1 3427826275261687 1125899906842624 125000000068337 17084250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz880) Bool.false 57509381830540779323392 18889465931478580854784 1000000000546696 136674000000000000000 3427826275261687 1125899906842624 125000000068337 17084250000000000000 (BSN.log_rat_reduce_isNear 21 1 4 42 32 142571 524288 24973259072661432 36028797018963968 136674 1000000000000000 rfl rfl rfl rfl (ep378 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1161 := nat_lit 3132230221173861028387372311052071601

noncomputable def ep1162 := BSN.sin_dyadic_bound_f 1330342357 2147483648 2 1 1048576 273615 ep1161 ep105 ep1161 ep1161 ep106 ep1161 608823 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1330342357) qz272 0 1 ep1161 ep105 ep1161 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1330342357) qz273 0 1 ep1161 ep106 ep1161 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz957 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 354775937) qz268)

noncomputable def ep1163 := @Enclosure.Real.IsNear.cos_image qz399 qz957 Bool.false 354775937 1048576 853 1048576 Bool.false 608823 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz399 Bool.false 380937761796106537997 1125899906842624000 13891375007594359147 17084250000000000000000 354775937 1048576 853 1048576 (ep1160 rfl) rfl) (Enclosure.sfrac_false_div 354775937 1048576) (BSN.cos_reduce3 qz957 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 93614521054696375844864) qz271) 226375608064910080 72057594037927936 Bool.false 608823 1048576 53 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q3 354775937 1048576 226375608064910080 72057594037927936 53 93614521054696375844864 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 608823 1048576 93614521054696375844864 151115727451828646838272 1330342357 2147483648 273615 273348 (ep1162 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1164 := BSN.cos_dyadic_bound_f 1330342357 2147483648 2 1 1048576 273615 ep1161 ep91 ep1161 ep1161 ep92 ep1161 853724 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1330342357) qz266 0 1 ep1161 ep91 ep1161 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1330342357) qz267 0 1 ep1161 ep92 ep1161 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1165 := @Enclosure.Real.IsNear.sin_image qz399 qz957 Bool.false 354775937 1048576 853 1048576 Bool.true 853724 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz399 Bool.false 380937761796106537997 1125899906842624000 13891375007594359147 17084250000000000000000 354775937 1048576 853 1048576 (ep1160 rfl) rfl) (Enclosure.sfrac_false_div 354775937 1048576) (BSN.sin_reduce3 qz957 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 93614521054696375844864) qz271) 226375608064910080 72057594037927936 Bool.false 853724 1048576 53 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q3 354775937 1048576 226375608064910080 72057594037927936 53 93614521054696375844864 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 853724 1048576 93614521054696375844864 151115727451828646838272 1330342357 2147483648 273615 273348 (ep1164 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1166 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz332 (Real.cos qz399)) (@HMul.hMul Real Real Real qz0 qz332 (@Neg.neg Real Real.instNeg (Real.sin qz399))) Bool.false 69654830607 549755813888 6770714980441 37568663053664256 Bool.false 24418427279 137438953472 3393725390039 18784331526832128 (@Enclosure.Real.IsNear.mulLit_ff qz332 (Real.cos qz399) 114409 524288 1 524288 608823 1048576 58815749 71656538112 69654830607 549755813888 6770714980441 37568663053664256 qz584 (@Enclosure.Real.IsNear.recentre' (Real.cos qz399) Bool.false 608823 1048576 117631498 143313076224 608823 1048576 58815749 71656538112 (ep1163 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz332 (@Neg.neg Real Real.instNeg (Real.sin qz399)) 114409 524288 1 524288 213431 262144 58815749 71656538112 24418427279 137438953472 3393725390039 18784331526832128 qz584 (@Enclosure.Real.IsNear.neg (Real.sin qz399) Bool.true 213431 262144 58815749 71656538112 (@Enclosure.Real.IsNear.recentre' (Real.sin qz399) Bool.true 853724 1048576 117631498 143313076224 213431 262144 58815749 71656538112 (ep1165 rfl rfl) rfl)) rfl)

noncomputable def ep1167 := @ep1104 69654830607 549755813888 6770714980441 37568663053664256 Bool.false 24418427279 137438953472 3393725390039 18784331526832128 Bool.false 197816753542142787321856 359826578537 1099511627776 140505943336561 25045775369109504 Bool.true 7182865152364599312384 52262222397 1099511627776 140467689058447 25045775369109504 (ep1105 (BSN.head_sum_c_succ qz64 20 21 rfl rfl) (ep1158 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1159 ep1166) rfl rfl

noncomputable abbrev qz400 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 22 1)))

noncomputable def ep1168 := @Enclosure.Complex.IsNear.of_eq qz949 (Complex.mk (@HMul.hMul Real Real Real qz0 qz335 (Real.cos qz400)) (@HMul.hMul Real Real Real qz0 qz335 (@Neg.neg Real Real.instNeg (Real.sin qz400)))) Bool.true 111119230407 1099511627776 13182698189129 75137326107328512 Bool.false 206406377631 1099511627776 13211825605313 75137326107328512 (BSN.cpow_neg_s_mk qz61 111131 1000 22 (@Eq.refl Real qz61) rfl)

noncomputable def ep1169 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz337 111131 1000 0 1 3480203401436407 1125899906842624 125000000068337 17084250000000000000 386758484205029346317 1125899906842624000 13891375007594359147 17084250000000000000000 qz380 (BSN.isNear_log_sfrac 22 1 3480203401436407 1125899906842624 125000000068337 17084250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz882) Bool.false 58388124189833310502912 18889465931478580854784 1000000000546696 136674000000000000000 3480203401436407 1125899906842624 125000000068337 17084250000000000000 (BSN.log_rat_reduce_isNear 22 1 4 44 32 166961 524288 24973259072661432 36028797018963968 136674 1000000000000000 rfl rfl rfl rfl (ep389 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1170 := nat_lit 1022966771085343954266137219683799871562007278132354101252854992615626620357761

noncomputable def ep1171 := nat_lit 818408979938159598297258672503602010875085612904823536135507971893392919681

noncomputable def ep1172 := nat_lit 3067263495296155543601817141706392410664271663171252656686293961903093075233921

noncomputable def ep1173 := BSN.cos_dyadic_bound_f 2312710639 2147483648 3 2 1048576 273615 ep1170 ep138 ep1171 ep1172 ep140 ep1171 497051 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2312710639) qz266 0 2 ep1170 ep138 ep1171 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2312710639) qz267 0 2 ep1172 ep140 ep1171 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz958 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 360196907) qz268)

noncomputable def ep1174 := @Enclosure.Real.IsNear.cos_image qz400 qz958 Bool.false 360196907 1048576 853 1048576 Bool.true 497051 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz400 Bool.false 386758484205029346317 1125899906842624000 13891375007594359147 17084250000000000000000 360196907 1048576 853 1048576 (ep1169 rfl) rfl) (Enclosure.sfrac_false_div 360196907 1048576) (BSN.cos_reduce2 qz958 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 162742543351455326142464) qz271) 226375608064910080 72057594037927936 Bool.false 497051 1048576 54 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q2 360196907 1048576 226375608064910080 72057594037927936 54 162742543351455326142464 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 497051 1048576 162742543351455326142464 151115727451828646838272 2312710639 2147483648 273615 273348 (ep1173 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1175 := nat_lit 1840685460769668590000409188492836887202913032147913523426230580330613202308225

noncomputable def ep1176 := nat_lit 4819517830333994048746685646297186015609069707490308561343527364149492893699201

noncomputable def ep1177 := BSN.sin_dyadic_bound_f 2312710639 2147483648 3 2 1048576 273615 ep1175 ep131 ep1171 ep1176 ep134 ep1171 923283 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2312710639) qz272 0 2 ep1175 ep131 ep1171 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2312710639) qz273 0 2 ep1176 ep134 ep1171 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1178 := @Enclosure.Real.IsNear.sin_image qz400 qz958 Bool.false 360196907 1048576 853 1048576 Bool.true 923283 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz400 Bool.false 386758484205029346317 1125899906842624000 13891375007594359147 17084250000000000000000 360196907 1048576 853 1048576 (ep1169 rfl) rfl) (Enclosure.sfrac_false_div 360196907 1048576) (BSN.sin_reduce2 qz958 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 162742543351455326142464) qz271) 226375608064910080 72057594037927936 Bool.false 923283 1048576 54 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q2 360196907 1048576 226375608064910080 72057594037927936 54 162742543351455326142464 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 923283 1048576 162742543351455326142464 151115727451828646838272 2312710639 2147483648 273615 273348 (ep1177 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1179 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz335 (Real.cos qz400)) (@HMul.hMul Real Real Real qz0 qz335 (@Neg.neg Real Real.instNeg (Real.sin qz400))) Bool.true 111119230407 1099511627776 13182698189129 75137326107328512 Bool.false 206406377631 1099511627776 13211825605313 75137326107328512 (@Enclosure.Real.IsNear.mulLit_ft qz335 (Real.cos qz400) 223557 1048576 1 1048576 497051 1048576 58815749 71656538112 111119230407 1099511627776 13182698189129 75137326107328512 qz585 (@Enclosure.Real.IsNear.recentre' (Real.cos qz400) Bool.true 497051 1048576 117631498 143313076224 497051 1048576 58815749 71656538112 (ep1174 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz335 (@Neg.neg Real Real.instNeg (Real.sin qz400)) 223557 1048576 1 1048576 923283 1048576 58815749 71656538112 206406377631 1099511627776 13211825605313 75137326107328512 qz585 (@Enclosure.Real.IsNear.neg (Real.sin qz400) Bool.true 923283 1048576 58815749 71656538112 (@Enclosure.Real.IsNear.recentre' (Real.sin qz400) Bool.true 923283 1048576 117631498 143313076224 923283 1048576 58815749 71656538112 (ep1178 rfl rfl) rfl)) rfl)

noncomputable def ep1180 := @ep1102 111119230407 1099511627776 13182698189129 75137326107328512 Bool.false 206406377631 1099511627776 13211825605313 75137326107328512 Bool.false 273456621182268609658880 124353674065 549755813888 108675132049703 18784331526832128 Bool.false 169483291033491770179584 77072077617 549755813888 217307446390327 37568663053664256 (ep1103 (BSN.head_sum_c_succ qz64 21 22 rfl rfl) (ep1167 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1168 ep1179) rfl rfl

noncomputable abbrev qz401 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 23 1)))

noncomputable def ep1181 := @Enclosure.Complex.IsNear.of_eq qz948 (Complex.mk (@HMul.hMul Real Real Real qz0 qz338 (Real.cos qz401)) (@HMul.hMul Real Real Real qz0 qz338 (@Neg.neg Real Real.instNeg (Real.sin qz401)))) Bool.true 110588536185 549755813888 6464419825093 37568663053664256 Bool.true 15088334787 274877906944 1609821762061 9392165763416064 (BSN.cpow_neg_s_mk qz61 111131 1000 23 (@Eq.refl Real qz61) rfl)

noncomputable def ep1182 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz340 111131 1000 0 1 3530250507853047 1125899906842624 125000000068337 17084250000000000000 392320269188216966157 1125899906842624000 13891375007594359147 17084250000000000000000 qz380 (BSN.isNear_log_sfrac 23 1 3530250507853047 1125899906842624 125000000068337 17084250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz885) Bool.false 59227775304360265777152 18889465931478580854784 1000000000546696 136674000000000000000 3530250507853047 1125899906842624 125000000068337 17084250000000000000 (BSN.log_rat_reduce_isNear 23 1 4 46 32 190266 524288 24973259072661432 36028797018963968 136674 1000000000000000 rfl rfl rfl rfl (ep400 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1183 := nat_lit 3963606406600679076951072710892957443773104456991145804466405600300302354425665

noncomputable def ep1184 := nat_lit 3790944235004539671052474119662031971490013772721260646755112393939472688961

noncomputable def ep1185 := nat_lit 10374736202811771184928248332335435729547146888868595065888696866434413686761281

noncomputable def ep1186 := BSN.sin_dyadic_bound_f 2801195529 2147483648 3 2 1048576 273615 ep1183 ep131 ep1184 ep1185 ep134 ep1184 1011590 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2801195529) qz272 0 2 ep1183 ep131 ep1184 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2801195529) qz273 0 2 ep1185 ep134 ep1184 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz959 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 365376723) qz268)

noncomputable def ep1187 := @Enclosure.Real.IsNear.cos_image qz401 qz959 Bool.false 365376723 1048576 853 1048576 Bool.true 1011590 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz401 Bool.false 392320269188216966157 1125899906842624000 13891375007594359147 17084250000000000000000 365376723 1048576 853 1048576 (ep1182 rfl) rfl) (Enclosure.sfrac_false_div 365376723 1048576) (BSN.cos_reduce1 qz959 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 197116611582969329483776) qz271) 226375608064910080 72057594037927936 Bool.false 1011590 1048576 55 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q1 365376723 1048576 226375608064910080 72057594037927936 55 197116611582969329483776 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1011590 1048576 197116611582969329483776 151115727451828646838272 2801195529 2147483648 273615 273348 (ep1186 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1188 := nat_lit 2203688423327045949271063716771492816305720260005179340546560939008585518098241

noncomputable def ep1189 := nat_lit 6603483381511128768471086202075154384974180752470095500346172592237877608916801

noncomputable def ep1190 := BSN.cos_dyadic_bound_f 2801195529 2147483648 3 2 1048576 273615 ep1188 ep138 ep1184 ep1189 ep140 ep1184 276036 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2801195529) qz266 0 2 ep1188 ep138 ep1184 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2801195529) qz267 0 2 ep1189 ep140 ep1184 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1191 := @Enclosure.Real.IsNear.sin_image qz401 qz959 Bool.false 365376723 1048576 853 1048576 Bool.false 276036 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz401 Bool.false 392320269188216966157 1125899906842624000 13891375007594359147 17084250000000000000000 365376723 1048576 853 1048576 (ep1182 rfl) rfl) (Enclosure.sfrac_false_div 365376723 1048576) (BSN.sin_reduce1 qz959 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 197116611582969329483776) qz271) 226375608064910080 72057594037927936 Bool.false 276036 1048576 55 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q1 365376723 1048576 226375608064910080 72057594037927936 55 197116611582969329483776 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 276036 1048576 197116611582969329483776 151115727451828646838272 2801195529 2147483648 273615 273348 (ep1190 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1192 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz338 (Real.cos qz401)) (@HMul.hMul Real Real Real qz0 qz338 (@Neg.neg Real Real.instNeg (Real.sin qz401))) Bool.true 110588536185 549755813888 6464419825093 37568663053664256 Bool.true 15088334787 274877906944 1609821762061 9392165763416064 (@Enclosure.Real.IsNear.mulLit_ft qz338 (Real.cos qz401) 218643 1048576 1 1048576 505795 524288 58815749 71656538112 110588536185 549755813888 6464419825093 37568663053664256 qz586 (@Enclosure.Real.IsNear.recentre' (Real.cos qz401) Bool.true 1011590 1048576 117631498 143313076224 505795 524288 58815749 71656538112 (ep1187 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz338 (@Neg.neg Real Real.instNeg (Real.sin qz401)) 218643 1048576 1 1048576 69009 262144 58815749 71656538112 15088334787 274877906944 1609821762061 9392165763416064 qz586 (@Enclosure.Real.IsNear.neg (Real.sin qz401) Bool.false 69009 262144 58815749 71656538112 (@Enclosure.Real.IsNear.recentre' (Real.sin qz401) Bool.false 276036 1048576 117631498 143313076224 69009 262144 58815749 71656538112 (ep1191 rfl rfl) rfl)) rfl)

noncomputable def ep1193 := @ep1100 110588536185 549755813888 6464419825093 37568663053664256 Bool.true 15088334787 274877906944 1609821762061 9392165763416064 Bool.false 7567464578499938877440 1720642235 68719476736 223814683924499 37568663053664256 Bool.false 12890511608144663150592 46895408043 549755813888 223746733438571 37568663053664256 (ep1101 (BSN.head_sum_c_succ qz64 22 23 rfl rfl) (ep1180 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1181 ep1192) rfl rfl

noncomputable abbrev qz402 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 24 1)))

noncomputable def ep1194 := @Enclosure.Complex.IsNear.of_eq qz947 (Complex.mk (@HMul.hMul Real Real Real qz0 qz341 (Real.cos qz402)) (@HMul.hMul Real Real Real qz0 qz341 (@Neg.neg Real Real.instNeg (Real.sin qz402)))) Bool.false 55304038937 1099511627776 12621206886511 75137326107328512 Bool.true 108757710719 549755813888 6336498348497 37568663053664256 (BSN.cpow_neg_s_mk qz61 111131 1000 24 (@Eq.refl Real qz61) rfl)

noncomputable def ep1195 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz343 111131 1000 0 1 3578169457974519 1125899906842624 125000000068337 17084250000000000000 397645550034166270989 1125899906842624000 13891375007594359147 17084250000000000000000 qz380 (BSN.isNear_log_sfrac 24 1 3578169457974519 1125899906842624 125000000068337 17084250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz888) Bool.false 60031721881041427759104 18889465931478580854784 1000000000546696 136674000000000000000 3578169457974519 1125899906842624 125000000068337 17084250000000000000 (BSN.log_rat_reduce_isNear 24 1 4 48 32 212580 524288 24973259072661432 36028797018963968 136674 1000000000000000 rfl rfl rfl rfl (ep414 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1196 := nat_lit 2323935597907284292729952322234234909976220161770674537062791094970960134308096

noncomputable def ep1197 := nat_lit 4215157536703191603547038371841829575321888341354432328264964353896059535616

noncomputable def ep1198 := nat_lit 6963376478648446494982762889959021070778016708629314746531843356205088283853056

noncomputable def ep1199 := BSN.cos_dyadic_bound_f 2838583842 2147483648 3 2 1048576 273615 ep1196 ep138 ep1197 ep1198 ep140 ep1197 258383 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2838583842) qz266 0 2 ep1196 ep138 ep1197 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2838583842) qz267 0 2 ep1198 ep140 ep1197 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz960 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 370336277) qz268)

noncomputable def ep1200 := @Enclosure.Real.IsNear.cos_image qz402 qz960 Bool.false 370336277 1048576 427 524288 Bool.false 258383 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz402 Bool.false 397645550034166270989 1125899906842624000 13891375007594359147 17084250000000000000000 370336277 1048576 427 524288 (ep1195 rfl) rfl) (Enclosure.sfrac_false_div 370336277 1048576) (BSN.cos_reduce0 qz960 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 199747580258519166746624) qz271) 226375608064910080 72057594037927936 Bool.false 258383 1048576 56 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q0 370336277 1048576 226375608064910080 72057594037927936 56 199747580258519166746624 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 258383 1048576 199747580258519166746624 151115727451828646838272 2838583842 2147483648 273615 273348 (ep1199 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1201 := nat_lit 4179711950203749173631076549324149374296938780514130620850411999464611394126080

noncomputable def ep1202 := nat_lit 10940040090712299811199457662294552065750985177365292068933888151548626697748736

noncomputable def ep1203 := BSN.sin_dyadic_bound_f 2838583842 2147483648 3 2 1048576 273615 ep1201 ep131 ep1197 ep1202 ep134 ep1197 1016242 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2838583842) qz272 0 2 ep1201 ep131 ep1197 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2838583842) qz273 0 2 ep1202 ep134 ep1197 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1204 := @Enclosure.Real.IsNear.sin_image qz402 qz960 Bool.false 370336277 1048576 427 524288 Bool.false 1016242 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz402 Bool.false 397645550034166270989 1125899906842624000 13891375007594359147 17084250000000000000000 370336277 1048576 427 524288 (ep1195 rfl) rfl) (Enclosure.sfrac_false_div 370336277 1048576) (BSN.sin_reduce0 qz960 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 199747580258519166746624) qz271) 226375608064910080 72057594037927936 Bool.false 1016242 1048576 56 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q0 370336277 1048576 226375608064910080 72057594037927936 56 199747580258519166746624 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1016242 1048576 199747580258519166746624 151115727451828646838272 2838583842 2147483648 273615 273348 (ep1203 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1205 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz341 (Real.cos qz402)) (@HMul.hMul Real Real Real qz0 qz341 (@Neg.neg Real Real.instNeg (Real.sin qz402))) Bool.false 55304038937 1099511627776 12621206886511 75137326107328512 Bool.true 108757710719 549755813888 6336498348497 37568663053664256 (@Enclosure.Real.IsNear.mulLit_ff qz341 (Real.cos qz402) 214039 1048576 1 1048576 258383 1048576 29442043 35828269056 55304038937 1099511627776 12621206886511 75137326107328512 qz587 (@Enclosure.Real.IsNear.recentre' (Real.cos qz402) Bool.false 258383 1048576 58884086 71656538112 258383 1048576 29442043 35828269056 (ep1200 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz341 (@Neg.neg Real Real.instNeg (Real.sin qz402)) 214039 1048576 1 1048576 508121 524288 29442043 35828269056 108757710719 549755813888 6336498348497 37568663053664256 qz587 (@Enclosure.Real.IsNear.neg (Real.sin qz402) Bool.false 508121 524288 29442043 35828269056 (@Enclosure.Real.IsNear.recentre' (Real.sin qz402) Bool.false 1016242 1048576 58884086 71656538112 508121 524288 29442043 35828269056 (ep1204 rfl rfl) rfl)) rfl)

noncomputable def ep1206 := @ep1098 55304038937 1099511627776 12621206886511 75137326107328512 Bool.true 108757710719 549755813888 6336498348497 37568663053664256 Bool.false 5692330761762994388992 82834314697 1099511627776 460250574735509 75137326107328512 Bool.true 34009160556630180364288 15465575669 137438953472 57520807946767 9392165763416064 (ep1099 (BSN.head_sum_c_succ qz64 23 24 rfl rfl) (ep1193 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1194 ep1205) rfl rfl

theorem EMRow34.d19 : Enclosure.Complex.IsNear (BSN.headSumC qz64 25) Bool.false 82834314697 1099511627776 460250574735509 75137326107328512 Bool.true 15465575669 137438953472 57520807946767 9392165763416064 := ep1097 (BSN.head_sum_c_succ qz64 24 25 rfl rfl) (ep1206 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz66 := (@HAdd.hAdd Complex Complex Complex qz260 qz378 qz551)

noncomputable def ep1207 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz3 (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2)) qz66) Bool.true 111147142449 2000000 0 1 Bool.true 1371839866611091 1000000000 0 1

noncomputable def ep1208 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.re qz66)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.im qz66)) 12349349161 400000 0 1 12350099161 500000 0 1

noncomputable def ep1209 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.re qz66) 12349349161 1000000 0 1 5 2 0 1 12349349161 400000

noncomputable abbrev qz67 := (@HAdd.hAdd Complex Complex Complex qz260 qz378 qz588)

noncomputable def ep1210 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz3 (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)) qz67) Bool.true 12349349161 1000000 0 1 Bool.false 111131 500 0 1

noncomputable def ep1211 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.re qz67)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.im qz67)) 3 4 0 1 12350099161 1000000 0 1

noncomputable def ep1212 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.re qz67) 1 2 0 1 3 2 0 1 3 4

noncomputable def ep1213 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)) qz64 Bool.false 1 2 0 1 Bool.false 111131 1000 0 1 (BSN.ascPochhammer_one_eval qz64)

noncomputable def ep1214 := ep1213 (@Enclosure.Complex.IsNear.of_eq qz64 (Complex.mk qz344 qz61) Bool.false 1 2 0 1 Bool.false 111131 1000 0 1 (BSN.s_crit_mk qz61 Bool.false 111131 1000 (@Eq.refl Real qz61)) (@Enclosure.Complex.IsNear.mk qz344 qz61 Bool.false 1 2 0 1 Bool.false 111131 1000 0 1 qz345 qz380))

noncomputable def ep1215 := @ep1212 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 111131 1000 0 1 ep1214)

noncomputable def ep1216 := @Enclosure.Complex.IsNear.of_eq qz67 (Complex.mk (Enclosure.sfrac Bool.false 3 2) qz61) Bool.false 3 2 0 1 Bool.false 111131 1000 0 1 (BSN.s_add_nat_mk qz61 Bool.false 111131 1000 1 (@Eq.refl Real qz61))

noncomputable abbrev qz624 := (ep1216 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz61 Bool.false 3 2 0 1 Bool.false 111131 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz380))

noncomputable def ep1217 := ep1215 (@Enclosure.Complex.IsNear.re_isNear qz67 Bool.false 3 2 0 1 Bool.false 111131 1000 0 1 qz624)

noncomputable def ep1218 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.im qz67) 111131 1000 0 1 111131 1000 0 1 12350099161 1000000

noncomputable def ep1219 := @ep1218 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 111131 1000 0 1 ep1214)

noncomputable def ep1220 := ep1219 (@Enclosure.Complex.IsNear.im_isNear qz67 Bool.false 3 2 0 1 Bool.false 111131 1000 0 1 qz624)

noncomputable def ep1221 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)) qz67 Bool.true 12349349161 1000000 0 1 Bool.false 111131 500 0 1 (@ep1211 49397396644 12349349161 1000000 0 1 (ep1217 rfl) (ep1220 rfl) rfl rfl)

noncomputable def ep1222 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.im qz67)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.re qz67)) 111131 2000 0 1 333393 2000 0 1

noncomputable def ep1223 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.im qz67) 1 2 0 1 111131 1000 0 1 111131 2000

noncomputable def ep1224 := @ep1223 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 111131 1000 0 1 ep1214)

noncomputable def ep1225 := ep1224 (@Enclosure.Complex.IsNear.im_isNear qz67 Bool.false 3 2 0 1 Bool.false 111131 1000 0 1 qz624)

noncomputable def ep1226 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.re qz67) 111131 1000 0 1 3 2 0 1 333393 2000

noncomputable def ep1227 := @ep1226 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 111131 1000 0 1 ep1214)

noncomputable def ep1228 := ep1227 (@Enclosure.Complex.IsNear.re_isNear qz67 Bool.false 3 2 0 1 Bool.false 111131 1000 0 1 qz624)

noncomputable abbrev qz625 := (ep1210 (BSN.ascPochhammer_succ_eval_c 1 2 qz64 rfl) (ep1221 (@ep1222 889048000 111131 500 0 1 (ep1225 rfl) (ep1228 rfl) rfl rfl)))

noncomputable def ep1229 := @ep1209 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 12349349161 1000000 0 1 Bool.false 111131 500 0 1 qz625)

noncomputable def ep1230 := @Enclosure.Complex.IsNear.of_eq qz66 (Complex.mk (Enclosure.sfrac Bool.false 5 2) qz61) Bool.false 5 2 0 1 Bool.false 111131 1000 0 1 (BSN.s_add_nat_mk qz61 Bool.false 111131 1000 2 (@Eq.refl Real qz61))

noncomputable abbrev qz626 := (ep1230 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz61 Bool.false 5 2 0 1 Bool.false 111131 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz380))

noncomputable def ep1231 := ep1229 (@Enclosure.Complex.IsNear.re_isNear qz66 Bool.false 5 2 0 1 Bool.false 111131 1000 0 1 qz626)

noncomputable def ep1232 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.im qz66) 111131 500 0 1 111131 1000 0 1 12350099161 500000

noncomputable def ep1233 := @ep1232 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 12349349161 1000000 0 1 Bool.false 111131 500 0 1 qz625)

noncomputable def ep1234 := ep1233 (@Enclosure.Complex.IsNear.im_isNear qz66 Bool.false 5 2 0 1 Bool.false 111131 1000 0 1 qz626)

noncomputable def ep1235 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2)) qz66 Bool.true 111147142449 2000000 0 1 Bool.true 1371839866611091 1000000000 0 1 (@ep1208 11114714244900000 111147142449 2000000 0 1 (ep1231 rfl) (ep1234 rfl) rfl rfl)

noncomputable def ep1236 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.im qz66)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.re qz66)) 1372395521611091 1000000000 0 1 111131 200 0 1

noncomputable def ep1237 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.im qz66) 12349349161 1000000 0 1 111131 1000 0 1 1372395521611091 1000000000

noncomputable def ep1238 := @ep1237 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 12349349161 1000000 0 1 Bool.false 111131 500 0 1 qz625)

noncomputable def ep1239 := ep1238 (@Enclosure.Complex.IsNear.im_isNear qz66 Bool.false 5 2 0 1 Bool.false 111131 1000 0 1 qz626)

noncomputable def ep1240 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.re qz66) 111131 500 0 1 5 2 0 1 111131 200

noncomputable def ep1241 := @ep1240 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 12349349161 1000000 0 1 Bool.false 111131 500 0 1 qz625)

noncomputable def ep1242 := ep1241 (@Enclosure.Complex.IsNear.re_isNear qz66 Bool.false 5 2 0 1 Bool.false 111131 1000 0 1 qz626)

noncomputable abbrev qz627 := (ep1235 (@ep1236 274367973322218200 1371839866611091 1000000000 0 1 (ep1239 rfl) (ep1242 rfl) rfl rfl))

theorem EMRow34.d20 : Enclosure.Complex.IsNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 111147142449 2000000 0 1 Bool.true 1371839866611091 1000000000 0 1 := ep1207 (BSN.ascPochhammer_succ_eval_c 2 3 qz64 rfl) qz627

noncomputable def ep1243 := nat_lit 4612956288838774603924712845029832096893203

noncomputable def ep1244 := nat_lit 32150484804966058555082605194117120000000000

noncomputable def ep1245 := nat_lit 7120082582650873793744951639586324534389554997564891

noncomputable def ep1246 := nat_lit 1050987098393071520412917881886705405877288960000000000

noncomputable abbrev qz68 := (Complex.Stirling.logGammaStirling 2 qz374)

noncomputable abbrev qz628 := (@HAdd.hAdd Complex Complex Complex qz811 qz812 (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I (@HDiv.hDiv Complex Complex Complex qz813 (↑(Enclosure.sfrac Bool.false 111131 1000)) (2 : Complex))))

noncomputable abbrev qz403 := qz628

noncomputable abbrev qz69 := qz403

noncomputable abbrev qz404 := (@HMul.hMul Real Real Real qz0 (@HDiv.hDiv Real Real Real qz1 qz61 (2 : Real)) (Real.log Real.pi))

noncomputable def ep1247 := Complex.re (@HMul.hMul Complex Complex Complex qz3 (Complex.exp (@HMul.hMul Complex Complex Complex qz3 Complex.I ↑(@HSub.hSub Real Real Real qz347 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz404))) (zetaApproximant qz64 2 28))

noncomputable def ep1248 := @Enclosure.Real.IsNear.of_eq ep1247 (@HSub.hSub Real Real Real qz347 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz347 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz404)) (Complex.re (zetaApproximant qz64 2 28))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz347 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz404)) (Complex.im (zetaApproximant qz64 2 28))))

noncomputable def ep1249 := nat_lit 61506854185825121913651161840195595796951

noncomputable def ep1250 := @Enclosure.Real.IsNear.subLit_tt_n (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz347 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz404)) (Complex.re (zetaApproximant qz64 2 28))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz347 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz404)) (Complex.im (zetaApproximant qz64 2 28))) ep1249

noncomputable def ep1251 := nat_lit 428673130732880780734434735921561600000000

noncomputable def ep1252 := nat_lit 7112653409833199085083030058084267956558794949767537

noncomputable def ep1253 := nat_lit 28887549054769799562146492418793939061

noncomputable def ep1254 := nat_lit 16075242402483029277541302597058560000000000

noncomputable def ep1255 := nat_lit 3714586408837354330960790751028288915380023898677

noncomputable def ep1256 := nat_lit 525493549196535760206458940943352702938644480000000000

noncomputable def ep1257 := nat_lit 988725207135224290643449349704844970860827390249160821760418991775230092902400000000

noncomputable def ep1258 := @Enclosure.Real.IsNear.mulLit_tf (Real.cos (@HSub.hSub Real Real Real qz347 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz404)) (Complex.re (zetaApproximant qz64 2 28)) 1048575 1048576 25057271

noncomputable def ep1259 := nat_lit 4399317229513276726532519979986810371

noncomputable def ep1260 := nat_lit 30661091618505533747751813120000000000

noncomputable def ep1261 := nat_lit 98490111077162337795790088780596631711333

noncomputable def ep1262 := nat_lit 14667009125536688618040809572270080000000000

noncomputable def ep1263 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz347 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz404)) Bool.true 1048575 1048576 50114542

noncomputable abbrev qz629 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6794273) (@Nat.cast Real Real.instNatCast 65536))

noncomputable def ep1264 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz347 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz404) qz629 Bool.false 6794273 65536 359

noncomputable def ep1265 := nat_lit 1075735033703237626529014696883

noncomputable def ep1266 := nat_lit 10376293541461622784000000000

noncomputable def ep1267 := nat_lit 5846779553567993742279463022430931

noncomputable def ep1268 := nat_lit 17097915985312088064000000000000000000

noncomputable def ep1269 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz347 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz404) Bool.false ep1265 ep1266 ep1267 ep1268

noncomputable def ep1270 := nat_lit 1735744848935640807408886696883

noncomputable def ep1271 := nat_lit 2222610201296498574279463022430931

noncomputable def ep1272 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz404 ep1270 ep1266 ep1271 ep1268 8337158751 131072000

noncomputable def ep1273 := nat_lit 140998742337550762184411014349848576000

noncomputable def ep1274 := nat_lit 1813103274779038508355890443

noncomputable def ep1275 := nat_lit 20752587082923245568000000

noncomputable def ep1276 := nat_lit 2825192488885296879181213237619197

noncomputable def ep1277 := nat_lit 12823436988984066048000000000000000000

noncomputable def ep1278 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz20 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz69 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true ep1274 ep1275 ep1276 ep1277 Bool.false ep1270 ep1266

noncomputable def ep1279 := nat_lit 1479546142870797734211890443

noncomputable def ep1280 := nat_lit 8194102489098887796270691353689591

noncomputable def ep1281 := nat_lit 38470310966952198144000000000000000000

noncomputable def ep1282 := nat_lit 1799634833931350972400886696883

noncomputable def ep1283 := nat_lit 17751691997675476680779549616726379

noncomputable def ep1284 := @Enclosure.Complex.IsNear.subLitP qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz69 (@Nat.cast Complex Complex.instNatCast j))) Bool.true ep1279 ep1275 ep1280 ep1281 Bool.false ep1282 ep1266 ep1283

noncomputable def ep1285 := nat_lit 153881243867808792576000000000000000000

noncomputable def ep1286 := nat_lit 4082745616339551922271379616769744373284864

noncomputable def ep1287 := nat_lit 244284370464900306587621879410915742134042624

noncomputable abbrev qz405 := (@HSub.hSub Complex Complex Complex qz593 qz615 qz548)

noncomputable abbrev qz406 := (Complex.log qz615)

noncomputable abbrev qz70 := (@HSub.hSub Complex Complex Complex qz593 (@HMul.hMul Complex Complex Complex qz253 qz405 qz406) qz374)

noncomputable def ep1288 := @Enclosure.Complex.IsNear.of_eq qz68 (@HAdd.hAdd Complex Complex Complex qz13 (@HAdd.hAdd Complex Complex Complex qz13 qz70 qz892) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz20 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz27 qz57 (@HSub.hSub Int Int Int qz28 qz29 (@HMul.hMul Int Int Int qz30 qz31 (@Nat.cast Int instNatCastInt k)))))) Bool.true ep1279

noncomputable def ep1289 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz13 qz70 qz892) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz20 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz27 qz57 (@HSub.hSub Int Int Int qz28 qz29 (@HMul.hMul Int Int Int qz30 qz31 (@Nat.cast Int instNatCastInt k))))) Bool.true 64216515174060879097 900719925474099200

noncomputable def ep1290 := nat_lit 103762935414616227840000000

noncomputable def ep1291 := nat_lit 15471322861480103113303117

noncomputable def ep1292 := nat_lit 51881467707308113920000000000

noncomputable def ep1293 := nat_lit 1332656691542075862547634803078846664513945600

noncomputable def ep1294 := nat_lit 259354712559878294090974413837509752969259646976

noncomputable def ep1295 := @ep1289 29111277457177604261 136674000000000000000000 Bool.false 24995143128530728507 144115188075855872 31532750084050478117 273348000000000000000000 Bool.false 2366739564920182989557 ep1275 17113388946807211 ep1290 Bool.true ep1291 ep1266 111869475868985611091 ep1292 Bool.true ep1293 ep1279 ep1275 ep1280 ep1281 Bool.false ep1294

noncomputable def ep1296 := @Enclosure.Complex.IsNear.addLitP qz70 qz892 Bool.true 65044220655502978297 900719925474099200 57440500013232161647 273348000000000000000000

noncomputable def ep1297 := nat_lit 8416987076894507545001984

noncomputable def ep1298 := @ep1296 Bool.false 24995143128530728507 144115188075855872 31532750084050478117 273348000000000000000000 Bool.false 120447 131072 3 1048576 Bool.false 0 1 0 1 Bool.true ep1297 64216515174060879097 900719925474099200 29111277457177604261 136674000000000000000000 Bool.false 24995143128530728507 24995143128530728507 144115188075855872

noncomputable abbrev qz71 := (@HMul.hMul Complex Complex Complex qz253 qz405 qz406)

noncomputable def ep1299 := @Enclosure.Complex.IsNear.subLitP qz71 qz57 Bool.true 61216160972238056697 900719925474099200 57440500013232161647 273348000000000000000000 Bool.false 4125371951444962245327

noncomputable def ep1300 := nat_lit 12497571564265364253500000

noncomputable def ep1301 := @ep1299 18014398509481984000 31532750084050478117 273348000000000000000000 Bool.false 17000 4000 0 1 Bool.false 222262 4000 0 1 Bool.true 260176882622011913188000 65044220655502978297 900719925474099200 57440500013232161647 273348000000000000000000 Bool.false ep1300 24995143128530728507 144115188075855872 31532750084050478117 273348000000000000000000

noncomputable abbrev qz72 := qz405

noncomputable abbrev qz73 := qz406

noncomputable def ep1302 := @Enclosure.Complex.IsNear.mul qz72 qz73 Bool.true 61216160972238056697 900719925474099200 57440500013232161647 273348000000000000000000 Bool.false 4125371951444962245327 18014398509481984000 31532750084050478117

noncomputable def ep1303 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re qz72) (Complex.re qz73)) (@HMul.hMul Real Real Real qz0 (Complex.im qz72) (Complex.im qz73)) 543198825488296755 36028797018963968 250000000751707 36446400000000000000 18699032902361368893 225179981368524800

noncomputable def ep1304 := nat_lit 551386159487247224542768726146023424

noncomputable def ep1305 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz72) (Complex.re qz73) 15000 4000 0 1 36213255032553117 9007199254740992 250000000751707 136674000000000000000

noncomputable def ep1306 := @Enclosure.Complex.IsNear.re_isNear qz72 Bool.false 15000 4000 0 1 Bool.false 222262 4000 0 1

noncomputable def ep1307 := @Enclosure.Complex.IsNear.of_eq qz72 (Complex.mk (Enclosure.sfrac Bool.false 15000 4000) qz377) Bool.false 15000 4000 0 1 Bool.false 222262 4000 0

noncomputable abbrev qz630 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 17000 4000) qz377))

noncomputable def ep1308 := @Enclosure.Complex.IsNear.of_eq qz73 qz630 Bool.false 36213255032553117 9007199254740992 250000000751707 136674000000000000000 Bool.false 841305886852515 562949953421312 500000000068337 136674000000000000000

noncomputable def ep1309 := nat_lit 2019615806948240243683879270693342133092548322167016510221876712100595619107097159043973120

noncomputable def ep1310 := nat_lit 29089100871046466822528570952431614021846820267585028433485390210444305085848158487445504

noncomputable def ep1311 := nat_lit 705795595761805310657761147873750365917032024664887151208546029725224322481422663680

noncomputable def ep1312 := BSN.log_dyadic_bound 16921396644 82457396644 5 4 ep1309 1048576 273348 ep1310 ep1311 436563 99378793288 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 16921396644) (BSN.artanhQ 82457396644) 0 4 ep1310 ep1309 ep1311 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1313 := @Enclosure.Real.IsNear.mulLit_ff qz344 (Real.log (Enclosure.sfrac Bool.false 49689396644 16000000)) 1 2 0 1 36213255032553117 4503599627370496 250000000751707 68337000000000000000 36213255032553117 9007199254740992 250000000751707 136674000000000000000 qz345 (BSN.isNear_log_sfrac 49689396644 16000000 36213255032553117 4503599627370496 250000000751707 68337000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 49689396644) qz599)) Bool.false 303778800872115337691136 37778931862957161709568 1000000003006828 273348000000000000000 36213255032553117 4503599627370496 250000000751707 68337000000000000000 (BSN.log_rat_reduce_isNear 49689396644 16000000 11 99378793288 65536000000 436563 1048576 24973259072661432 36028797018963968 273348 1000000000000000 rfl rfl rfl rfl (ep1312 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1314 := BSN.arctan_dyadic_bound_f 17000 222262 1 0 1048576 273348 0 1 1 0 1 1 80045 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 17000) (BSN.arctanEvenQ 222262) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 17000) (BSN.arctanOddQ 222262) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz631 := (@Nat.cast Real Real.instNatCast 222262)

noncomputable def ep1315 := @Enclosure.Real.IsNear.subLit_ff_p qz354 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz600 qz631)) 884279719003555 562949953421312 1 2000000000000000 80045 1048576 1 273348 882173161612262768640 841305886852515 562949953421312 500000000068337 136674000000000000000 qz355 (ep1314 rfl) rfl rfl

noncomputable abbrev qz632 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 222262) (@Nat.cast Real Real.instNatCast 17000)))

noncomputable def ep1316 := @Enclosure.Complex.IsNear.re_isNear qz73 Bool.false 36213255032553117 9007199254740992 250000000751707 136674000000000000000 Bool.false 841305886852515 562949953421312 500000000068337 136674000000000000000 (ep1308 (@congrArg Complex Complex qz57 qz616 Complex.log (BSN.w_shift_mk qz61 Bool.false 111131 1000 4 (@Eq.refl Real qz61) rfl)) (@Enclosure.Complex.IsNear.of_parts qz630 Bool.false 36213255032553117 9007199254740992 250000000751707 136674000000000000000 Bool.false 841305886852515 562949953421312 500000000068337 136674000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz630) (@HMul.hMul Real Real Real qz0 qz344 (Real.log (Enclosure.sfrac Bool.false 49689396644 16000000))) Bool.false 36213255032553117 9007199254740992 250000000751707 136674000000000000000 (Enclosure.clog_re_eq 17000 222262 4000 49689396644 16000000 rfl rfl rfl) (ep1313 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz630) qz632 Bool.false 841305886852515 562949953421312 500000000068337 136674000000000000000 (Enclosure.clog_im_eq 17000 222262 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz632 (@HSub.hSub Real Real Real qz347 qz354 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz600 qz631))) Bool.false 841305886852515 562949953421312 500000000068337 136674000000000000000 (BSN.arctan_recip 222262 17000 rfl rfl) ep1315))))

noncomputable def ep1317 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz72) (Complex.im qz73) 222262 4000 0 1 841305886852515 562949953421312 500000000068337 136674000000000000000

noncomputable def ep1318 := @Enclosure.Complex.IsNear.im_isNear qz72 Bool.false 15000 4000 0 1 Bool.false 222262 4000 0 1

noncomputable def ep1319 := @Enclosure.Complex.IsNear.im_isNear qz73 Bool.false 36213255032553117 9007199254740992 250000000751707 136674000000000000000 Bool.false 841305886852515 562949953421312 500000000068337 136674000000000000000 (ep1308 (@congrArg Complex Complex qz57 qz616 Complex.log (BSN.w_shift_mk qz61 Bool.false 111131 1000 4 (@Eq.refl Real qz61) rfl)) (@Enclosure.Complex.IsNear.of_parts qz630 Bool.false 36213255032553117 9007199254740992 250000000751707 136674000000000000000 Bool.false 841305886852515 562949953421312 500000000068337 136674000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz630) (@HMul.hMul Real Real Real qz0 qz344 (Real.log (Enclosure.sfrac Bool.false 49689396644 16000000))) Bool.false 36213255032553117 9007199254740992 250000000751707 136674000000000000000 (Enclosure.clog_re_eq 17000 222262 4000 49689396644 16000000 rfl rfl rfl) (ep1313 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz630) qz632 Bool.false 841305886852515 562949953421312 500000000068337 136674000000000000000 (Enclosure.clog_im_eq 17000 222262 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz632 (@HSub.hSub Real Real Real qz347 qz354 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz600 qz631))) Bool.false 841305886852515 562949953421312 500000000068337 136674000000000000000 (BSN.arctan_recip 222262 17000 rfl rfl) ep1315))))

noncomputable abbrev qz407 := (@ep1307 1 (BSN.w_sub_half_mk qz61 Bool.false 111131 1000 4 (@Eq.refl Real qz61) rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 15000 4000) (Enclosure.sfrac Bool.false 222262 4000) Bool.false 15000 4000 0 1 Bool.false 222262 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 15000 4000) (Enclosure.Real.IsNear.const Bool.false 222262 4000)))

noncomputable def ep1320 := @ep1303 55565500007594359147 273348000000000000000000 ep1304 61216160972238056697 900719925474099200 57440500013232161647 273348000000000000000000 (@ep1305 543198825488296755 36028797018963968 250000000751707 36446400000000000000 (ep1306 qz407) ep1316 rfl) (@ep1317 18699032902361368893 225179981368524800 55565500007594359147 273348000000000000000000 (ep1318 qz407) ep1319 rfl) rfl

noncomputable def ep1321 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re qz72) (Complex.im qz73)) (@HMul.hMul Real Real Real qz0 (Complex.im qz72) (Complex.re qz73)) 12619588302787725 2251799813685248 500000000068337 36446400000000000000 4024415245022660445327 18014398509481984000

noncomputable def ep1322 := nat_lit 9289511791646113942803156212536836096

noncomputable def ep1323 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz72) (Complex.im qz73) 15000 4000 0 1 841305886852515 562949953421312 500000000068337 136674000000000000000

noncomputable def ep1324 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz72) (Complex.re qz73) 222262 4000 0 1 36213255032553117 9007199254740992 250000000751707 136674000000000000000

noncomputable def ep1325 := @ep1321 27782750083537950617 273348000000000000000000 ep1322 4125371951444962245327 18014398509481984000 31532750084050478117 273348000000000000000000 (@ep1323 12619588302787725 2251799813685248 500000000068337 36446400000000000000 (ep1306 qz407) ep1319 rfl) (@ep1324 4024415245022660445327 18014398509481984000 27782750083537950617 273348000000000000000000 (ep1318 qz407) ep1316 rfl) rfl

noncomputable def ep1326 := ep1301 (@ep1302 273348000000000000000000 (ep1320 rfl) (ep1325 rfl)) qz63 rfl rfl rfl rfl rfl rfl

noncomputable def ep1327 := @ep1298 31532750084050478117 273348000000000000000000 (ep1326 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz24 (↑qz251) Bool.false 120447 131072 3 1048576 Bool.false 0 1 0 1 (@ep540 131072 3 1048576 (ep542 rfl) (ep544 rfl) rfl rfl) (@ep545 1 0 1 (ep547 rfl) (ep549 rfl) rfl rfl))

noncomputable abbrev qz74 := (@HPow.hPow Complex Int Complex qz596 qz374 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) qz353 (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) qz597 (@Nat.cast Int instNatCastInt 2))))

noncomputable def ep1328 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz20 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz27 qz57 (@HSub.hSub Int Int Int qz28 qz29 (@HMul.hMul Int Int Int qz30 qz31 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz13 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz20 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz27 qz57 (@HSub.hSub Int Int Int qz28 qz29 (@HMul.hMul Int Int Int qz30 qz31 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz35)) qz36) qz74)) Bool.false 2366739564920182989557 ep1275 17113388946807211 ep1290

noncomputable def ep1329 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz20 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz27 qz57 (@HSub.hSub Int Int Int qz28 qz29 (@HMul.hMul Int Int Int qz30 qz31 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz35)) qz36) qz74) Bool.false 3918449 34359738368 17 103079215104 Bool.true

noncomputable def ep1330 := nat_lit 81320552235851638323862596222976

noncomputable def ep1331 := nat_lit 265795302863656724105378680199446528000

noncomputable def ep1332 := @ep1329 25615362107 17179869184000 111131 51539607552000 Bool.false 75615632758989557 ep1275 628626807211 ep1290 Bool.true 162193935355081303117 ep1266 1348391225611091 ep1292 Bool.false ep1330 2366739564920182989557 ep1275 17113388946807211 ep1290 Bool.true ep1331 ep1291 ep1266 111869475868985611091

noncomputable abbrev qz75 := (@HPow.hPow Complex Int Complex qz596 qz374 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) qz353 (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) qz597 (@Nat.cast Int instNatCastInt 1))))

noncomputable def ep1333 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz20 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz27 qz57 (@HSub.hSub Int Int Int qz28 qz29 (@HMul.hMul Int Int Int qz30 qz31 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz13 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz20 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz27 qz57 (@HSub.hSub Int Int Int qz28 qz29 (@HMul.hMul Int Int Int qz30 qz31 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz38)) qz39) qz75)) Bool.false 3918449 34359738368 17 103079215104

noncomputable def ep1334 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz20 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz27 qz57 (@HSub.hSub Int Int Int qz28 qz29 (@HMul.hMul Int Int Int qz30 qz31 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz38)) qz39) qz75) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1335 := @ep1334 0 1 0 1 Bool.false 3918449 34359738368 17 103079215104 Bool.true 25615362107 17179869184000 111131 51539607552000 Bool.false 3918449 3918449 34359738368 17 103079215104 Bool.true 25615362107 25615362107 17179869184000 111131

noncomputable def ep1336 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz20 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz27 qz57 (@HSub.hSub Int Int Int qz28 qz29 (@HMul.hMul Int Int Int qz30 qz31 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz262 qz262) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1337 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz38)) qz39) qz75 Bool.false 3918449 34359738368 17 103079215104 Bool.true 25615362107 17179869184000 111131 51539607552000

noncomputable def ep1338 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz38)) qz39)) (Complex.re qz75)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz38)) qz39)) (Complex.im qz75)) 3918449 34359738368 17 103079215104 0 1 0

noncomputable def ep1339 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz38)) qz39)) (Complex.re qz75) 1 12 0 1 11755347 8589934592 17 8589934592 3918449

noncomputable def ep1340 := @Enclosure.Complex.IsNear.re_isNear qz75 Bool.false 11755347 8589934592 17 8589934592 Bool.true 76846086321 4294967296000 111131 4294967296000

noncomputable def ep1341 := @Enclosure.Complex.IsNear.of_eq qz75 (@Inv.inv Complex Complex.instInv qz58) Bool.false 11755347 8589934592 17 8589934592 Bool.true 76846086321 4294967296000 111131

noncomputable def ep1342 := @Enclosure.Complex.IsNear.of_parts (@Inv.inv Complex Complex.instInv qz58) Bool.false 11755347 8589934592 17 8589934592 Bool.true 76846086321 4294967296000 111131

noncomputable def ep1343 := @Enclosure.Real.IsNear.mulLit_ff qz59 (@Inv.inv Real Real.instInv (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz58)) 17000 4000 0 1 691491 2147483648 1 2147483648

noncomputable def ep1344 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz58)) Bool.false 691491 2147483648 1 2147483648 691491 2147483648 1

noncomputable def ep1345 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz58) (@HAdd.hAdd Real Real Real qz604 (@HMul.hMul Real Real Real qz0 qz59 qz59) (@HMul.hMul Real Real Real qz0 qz60 qz60)) Bool.false 12422349161 4000000 0 1

noncomputable def ep1346 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz59 qz59) (@HMul.hMul Real Real Real qz0 qz60 qz60) 289 16 0 1 12350099161 4000000

noncomputable def ep1347 := @Enclosure.Real.IsNear.mulLit_ff qz59 qz59 17000 4000 0 1 17000 4000 0 1

noncomputable def ep1348 := @Enclosure.Real.IsNear.mulLit_ff qz60 qz60 222262 4000 0 1 222262 4000 0 1

noncomputable def ep1349 := @ep1346 0 1 198757586576 12422349161 4000000 0 1 (@ep1347 289 16 0 1 (ep873 qz62) (ep873 qz62) rfl) (@ep1348 12350099161 4000000 0 1 (ep878 qz62) (ep878 qz62) rfl)

noncomputable def ep1350 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz58) 12422349161 4000000 0 1 345745 345746 1073741824 (ep1345 (Enclosure.Complex.normSq_eq_mul_add_mul qz58) (ep1349 rfl rfl)) rfl

noncomputable def ep1351 := @Enclosure.Real.IsNear.of_eq (Complex.re (@Inv.inv Complex Complex.instInv qz58)) (@HMul.hMul Real Real Real qz0 qz59 (@Inv.inv Real Real.instInv (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz58))) Bool.false 11755347 8589934592 17 8589934592 (Enclosure.Complex.inv_re_eq_mul qz58) (@ep1343 11755347 8589934592 17 8589934592 (ep873 qz62) (@ep1344 2147483648 (ep1350 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep1352 := @Enclosure.Real.IsNear.of_eq (Complex.im (@Inv.inv Complex Complex.instInv qz58)) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz60) (@Inv.inv Real Real.instInv (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz58))) Bool.true 76846086321 4294967296000 111131 4294967296000 (Enclosure.Complex.inv_im_eq_mul qz58)

noncomputable def ep1353 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz60) (@Inv.inv Real Real.instInv (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz58)) 222262 4000 0 1 691491 2147483648 1

noncomputable def ep1354 := @ep1353 2147483648 76846086321 4294967296000 111131 4294967296000 (@Enclosure.Real.IsNear.neg qz60 Bool.false 222262 4000 0 1 (ep878 qz62)) (@ep1344 2147483648 (ep1350 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep1355 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz38)) qz39)) (Complex.im qz75) 0 1 0 1 76846086321 4294967296000 111131 4294967296000 0

noncomputable def ep1356 := @Enclosure.Complex.IsNear.im_isNear qz75 Bool.false 11755347 8589934592 17 8589934592 Bool.true 76846086321 4294967296000 111131 4294967296000

noncomputable abbrev qz633 := (@ep1341 4294967296000 (BSN.zpow_one_sub_two_mul qz57 1 1 rfl rfl) (@ep1342 4294967296000 ep1351 (ep1352 ep1354)))

noncomputable def ep1357 := @ep1338 1 3918449 3918449 34359738368 17 103079215104 (@ep1339 34359738368 17 103079215104 ep565 (ep1340 qz633) rfl) (@ep1355 1 0 1 ep582 (ep1356 qz633) rfl) rfl

noncomputable def ep1358 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz38)) qz39)) (Complex.im qz75)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz38)) qz39)) (Complex.re qz75)) 25615362107 17179869184000 111131 51539607552000 0 1 0

noncomputable def ep1359 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz38)) qz39)) (Complex.im qz75) 1 12 0 1 76846086321 4294967296000 111131 4294967296000 25615362107

noncomputable def ep1360 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz38)) qz39)) (Complex.re qz75) 0 1 0 1 11755347 8589934592 17 8589934592 0

noncomputable def ep1361 := @ep1358 1 25615362107 25615362107 17179869184000 111131 51539607552000 (@ep1359 17179869184000 111131 51539607552000 ep565 (ep1356 qz633) rfl) (@ep1360 1 0 1 ep582 (ep1340 qz633) rfl) rfl

noncomputable def ep1362 := @ep1335 51539607552000 (@ep1336 0 1 0 1 (BSN.stirling_sum_base qz57) qz360) (ep1337 (ep1357 rfl) (ep1361 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep1363 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz35)) qz36) qz74 Bool.false 75615632758989557 ep1275 628626807211 ep1290 Bool.true 162193935355081303117 ep1266 1348391225611091 ep1292

noncomputable def ep1364 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz35)) qz36)) (Complex.re qz74)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz35)) qz36)) (Complex.im qz74)) 75615632758989557 ep1275 628626807211 ep1290 0 1 0

noncomputable def ep1365 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz35)) qz36)) (Complex.re qz74) 1 360 0 1 75615632758989557 57646075230342348800000 628626807211 288230376151711744000000 75615632758989557

noncomputable def ep1366 := nat_lit 28823037615171174400000000

noncomputable def ep1367 := nat_lit 144115188075855872000000000

noncomputable def ep1368 := @Enclosure.Complex.IsNear.re_isNear qz74 Bool.true 75615632758989557 57646075230342348800000 628626807211 288230376151711744000000 Bool.false 162193935355081303117 ep1366 1348391225611091 ep1367

noncomputable def ep1369 := @Enclosure.Complex.IsNear.of_eq qz74 (@Inv.inv Complex Complex.instInv qz55) Bool.true 75615632758989557 57646075230342348800000 628626807211 288230376151711744000000 Bool.false 162193935355081303117 ep1366 1348391225611091

noncomputable def ep1370 := @Enclosure.Complex.IsNear.of_parts (@Inv.inv Complex Complex.instInv qz55) Bool.true 75615632758989557 57646075230342348800000 628626807211 288230376151711744000000 Bool.false 162193935355081303117 ep1366 1348391225611091

noncomputable abbrev qz76 := (Complex.re qz373)

noncomputable def ep1371 := @Enclosure.Real.IsNear.mulLit_tf qz76 (@Inv.inv Real Real.instInv (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz55)) 628626807211 16000000 0 1 601435 18014398509481984 1 18014398509481984

noncomputable def ep1372 := @Enclosure.Complex.IsNear.re_isNear qz55 Bool.true 628626807211 16000000 0 1 Bool.true 1348391225611091 8000000000 0 1

noncomputable def ep1373 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz55)) Bool.false 601435 18014398509481984 1 18014398509481984 601435 18014398509481984 1

noncomputable def ep1374 := nat_lit 1916951812991054049926012460281

noncomputable abbrev qz77 := (Complex.im qz373)

noncomputable def ep1375 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz55) (@HAdd.hAdd Real Real Real qz604 (@HMul.hMul Real Real Real qz0 qz76 qz76) (@HMul.hMul Real Real Real qz0 qz77 qz77)) Bool.false ep1374 64000000000000000000 0 1

noncomputable def ep1376 := nat_lit 1818158897304980109526382210281

noncomputable def ep1377 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz76 qz76) (@HMul.hMul Real Real Real qz0 qz77 qz77) 395171662744295761598521 256000000000000 0 1 ep1376 64000000000000000000

noncomputable def ep1378 := nat_lit 490739664125709836781059189831936000000000000

noncomputable def ep1379 := @Enclosure.Real.IsNear.mulLit_tt qz76 qz76 628626807211 16000000 0 1 628626807211 16000000 0 1

noncomputable def ep1380 := @Enclosure.Real.IsNear.mulLit_tt qz77 qz77 1348391225611091 8000000000 0 1 1348391225611091 8000000000 0 1

noncomputable def ep1381 := @Enclosure.Complex.IsNear.im_isNear qz55 Bool.true 628626807211 16000000 0 1 Bool.true 1348391225611091 8000000000 0 1

noncomputable def ep1382 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz55) ep1374 64000000000000000000 0 1 300717 300718 9007199254740992 (ep1375 (Enclosure.Complex.normSq_eq_mul_add_mul qz55) (@ep1377 0 1 ep1378 ep1374 64000000000000000000 0 1 (@ep1379 395171662744295761598521 256000000000000 0 1 (ep1372 EMRow34.d16) (ep1372 EMRow34.d16) rfl) (@ep1380 ep1376 64000000000000000000 0 1 (ep1381 EMRow34.d16) (ep1381 EMRow34.d16) rfl) rfl rfl)) rfl

noncomputable def ep1383 := @Enclosure.Real.IsNear.of_eq (Complex.re (@Inv.inv Complex Complex.instInv qz55)) (@HMul.hMul Real Real Real qz0 qz76 (@Inv.inv Real Real.instInv (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz55))) Bool.true 75615632758989557 57646075230342348800000 628626807211 288230376151711744000000 (Enclosure.Complex.inv_re_eq_mul qz55) (@ep1371 75615632758989557 57646075230342348800000 628626807211 288230376151711744000000 (ep1372 EMRow34.d16) (@ep1373 18014398509481984 (ep1382 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep1384 := @Enclosure.Real.IsNear.of_eq (Complex.im (@Inv.inv Complex Complex.instInv qz55)) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz77) (@Inv.inv Real Real.instInv (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz55))) Bool.false 162193935355081303117 ep1366 1348391225611091 ep1367 (Enclosure.Complex.inv_im_eq_mul qz55)

noncomputable def ep1385 := @Enclosure.Real.IsNear.mulLit_ff (@Neg.neg Real Real.instNeg qz77) (@Inv.inv Real Real.instInv (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz55)) 1348391225611091 8000000000 0 1 601435 18014398509481984 1

noncomputable def ep1386 := @ep1385 18014398509481984 162193935355081303117 ep1366 1348391225611091 ep1367 (@Enclosure.Real.IsNear.neg qz77 Bool.true 1348391225611091 8000000000 0 1 (ep1381 EMRow34.d16)) (@ep1373 18014398509481984 (ep1382 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep1387 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz35)) qz36)) (Complex.im qz74) 0 1 0 1 162193935355081303117 ep1366 1348391225611091 ep1367 0

noncomputable def ep1388 := @Enclosure.Complex.IsNear.im_isNear qz74 Bool.true 75615632758989557 57646075230342348800000 628626807211 288230376151711744000000 Bool.false 162193935355081303117 ep1366 1348391225611091 ep1367

noncomputable abbrev qz634 := (@ep1369 ep1367 (BSN.zpow_one_sub_two_mul qz57 2 3 rfl rfl) (@ep1370 ep1367 ep1383 (ep1384 ep1386)))

noncomputable def ep1389 := @ep1364 1 75615632758989557 75615632758989557 ep1275 628626807211 ep1290 (@ep1365 ep1275 628626807211 ep1290 ep594 (ep1368 qz634) rfl) (@ep1387 1 0 1 ep615 (ep1388 qz634) rfl) rfl

noncomputable def ep1390 := @Enclosure.Real.IsNear.addLit_tt (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz35)) qz36)) (Complex.im qz74)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz35)) qz36)) (Complex.re qz74)) 162193935355081303117 ep1266 1348391225611091 ep1292 0 1 0

noncomputable def ep1391 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz35)) qz36)) (Complex.im qz74) 1 360 0 1 162193935355081303117 ep1366 1348391225611091 ep1367 162193935355081303117

noncomputable def ep1392 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz35)) qz36)) (Complex.re qz74) 0 1 0 1 75615632758989557 57646075230342348800000 628626807211 288230376151711744000000 0

noncomputable def ep1393 := @ep1390 1 162193935355081303117 162193935355081303117 ep1266 1348391225611091 ep1292 (@ep1391 ep1266 1348391225611091 ep1292 ep594 (ep1388 qz634) rfl) (@ep1392 1 0 1 ep615 (ep1368 qz634) rfl) rfl

noncomputable def ep1394 := @ep1332 ep1292 (@ep1333 Bool.true 25615362107 17179869184000 111131 51539607552000 (BSN.stirling_sum_succ qz57 0 1 rfl) (ep1362 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1363 (ep1389 rfl) (ep1393 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep1395 := @ep1295 ep1282 ep1266 ep1283 ep1285 (ep1327 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep1328 Bool.true ep1291 ep1266 111869475868985611091 ep1292 (BSN.stirling_sum_succ qz57 1 2 rfl) (ep1394 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep1396 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz69 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz61 4) Bool.false 36193265181015709 2251799813685248 250000000751707 34168500000000000000 Bool.false 866563381560739 140737488355328

noncomputable def ep1397 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz61 4) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.logSumC qz61 3) (Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz69 qz550))) Bool.false 36193265181015709 2251799813685248 250000000751707 34168500000000000000 Bool.false 866563381560739 140737488355328 500000000068337 34168500000000000000

noncomputable def ep1398 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz61 3) (Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz69 qz550)) Bool.false 108570697728572375 9007199254740992 250000000751707 45558000000000000000 Bool.false 2614862519308521 562949953421312 500000000068337 45558000000000000000 Bool.false

noncomputable def ep1399 := nat_lit 1303999804660351156080369112973312

noncomputable def ep1400 := nat_lit 1951327261144930552429540278272

noncomputable def ep1401 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz61 3) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.logSumC qz61 2) (Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz69 qz551))) Bool.false 108570697728572375 9007199254740992 250000000751707 45558000000000000000 Bool.false 2614862519308521 562949953421312 500000000068337 45558000000000000000

noncomputable def ep1402 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz61 2) (Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz69 qz551)) Bool.false 36188168128577181 4503599627370496 250000000751707 68337000000000000000 Bool.false 876682727163299 281474976710656 500000000068337 68337000000000000000 Bool.false

noncomputable def ep1403 := nat_lit 488958953833753304518149275648000

noncomputable def ep1404 := nat_lit 736018366723933223592212299776

noncomputable def ep1405 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz61 2) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.logSumC qz61 1) (Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz69 qz588))) Bool.false 36188168128577181 4503599627370496 250000000751707 68337000000000000000 Bool.false 876682727163299 281474976710656 500000000068337 68337000000000000000

noncomputable def ep1406 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz61 1) (Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz69 qz588)) Bool.false 36187072911916701 9007199254740992 250000000751707 136674000000000000000 Bool.false 881747298911651 562949953421312 500000000068337 136674000000000000000 Bool.false

noncomputable def ep1407 := nat_lit 651908081996324207725107273007104

noncomputable def ep1408 := nat_lit 987057000843695897043141656576

noncomputable abbrev qz961 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz69 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep1409 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz61 1) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.logSumC qz61 0) qz961) Bool.false 36187072911916701 9007199254740992 250000000751707 136674000000000000000 Bool.false 881747298911651 562949953421312 500000000068337 136674000000000000000

noncomputable def ep1410 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz61 0) qz961 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz962 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz377))

noncomputable def ep1411 := @Enclosure.Complex.IsNear.of_eq qz961 qz962 Bool.false 36187072911916701 9007199254740992 250000000751707 136674000000000000000 Bool.false 881747298911651 562949953421312 500000000068337 136674000000000000000

noncomputable def ep1412 := nat_lit 1963869352742286637537792420197133991578589731865290334665619242841473264739422709123973120

noncomputable def ep1413 := nat_lit 27504021971062857114995853460414424337339579798680892811593408982366195030761734423445504

noncomputable def ep1414 := nat_lit 615229073621964828606876180616615451692993332380096869782591018206584287542542663680

noncomputable def ep1415 := BSN.log_dyadic_bound 16633396644 82169396644 5 4 ep1412 1048576 273348 ep1413 ep1414 430467 98802793288 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 16633396644) (BSN.artanhQ 82169396644) 0 4 ep1413 ep1412 ep1414 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1416 := @Enclosure.Real.IsNear.mulLit_ff qz344 (Real.log (Enclosure.sfrac Bool.false 49401396644 16000000)) 1 2 0 1 36187072911916701 4503599627370496 250000000751707 68337000000000000000 36187072911916701 9007199254740992 250000000751707 136674000000000000000 qz345 (BSN.isNear_log_sfrac 49401396644 16000000 36187072911916701 4503599627370496 250000000751707 68337000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 49401396644) qz599)) Bool.false 303559169325487733342208 37778931862957161709568 1000000003006828 273348000000000000000 36187072911916701 4503599627370496 250000000751707 68337000000000000000 (BSN.log_rat_reduce_isNear 49401396644 16000000 11 98802793288 65536000000 430467 1048576 24973259072661432 36028797018963968 273348 1000000000000000 rfl rfl rfl rfl (ep1415 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1417 := BSN.arctan_dyadic_bound_f 1000 222262 1 0 1048576 273348 0 1 1 0 1 1 4717 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 222262) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 222262) 0 0 rfl) rfl rfl rfl

noncomputable def ep1418 := @Enclosure.Real.IsNear.subLit_ff_p qz354 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz895 qz631)) 884279719003555 562949953421312 1 2000000000000000 4717 1048576 1 273348 924579055703583358976 881747298911651 562949953421312 500000000068337 136674000000000000000 qz355 (ep1417 rfl) rfl rfl

noncomputable abbrev qz963 := (@HAdd.hAdd Complex Complex Complex qz13 qz69 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz964 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz377)

noncomputable def ep1419 := @ep1410 36187072911916701 9007199254740992 250000000751707 136674000000000000000 Bool.false 881747298911651 562949953421312 500000000068337 136674000000000000000 Bool.false 36187072911916701 36187072911916701 9007199254740992 250000000751707 136674000000000000000 Bool.false 881747298911651 881747298911651 562949953421312 500000000068337 136674000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz61 0) (Complex.mk qz262 qz262) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz61) qz360) (ep1411 (@congrArg Complex Complex qz963 qz964 Complex.log (BSN.w_shift_mk qz61 Bool.false 111131 1000 0 (@Eq.refl Real qz61) rfl)) (@Enclosure.Complex.IsNear.of_parts qz962 Bool.false 36187072911916701 9007199254740992 250000000751707 136674000000000000000 Bool.false 881747298911651 562949953421312 500000000068337 136674000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz962) (@HMul.hMul Real Real Real qz0 qz344 (Real.log (Enclosure.sfrac Bool.false 49401396644 16000000))) Bool.false 36187072911916701 9007199254740992 250000000751707 136674000000000000000 (Enclosure.clog_re_eq 1000 222262 4000 49401396644 16000000 rfl rfl rfl) (ep1416 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz962) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz631 qz895)) Bool.false 881747298911651 562949953421312 500000000068337 136674000000000000000 (Enclosure.clog_im_eq 1000 222262 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz631 qz895)) (@HSub.hSub Real Real Real qz347 qz354 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz895 qz631))) Bool.false 881747298911651 562949953421312 500000000068337 136674000000000000000 (BSN.arctan_recip 222262 1000 rfl rfl) ep1418)))) rfl rfl

noncomputable abbrev qz965 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz377))

noncomputable def ep1420 := @Enclosure.Complex.IsNear.of_eq (Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz69 qz588)) qz965 Bool.false 36189263345237661 9007199254740992 250000000751707 136674000000000000000 Bool.false 871618155414947 562949953421312 500000000068337 136674000000000000000

noncomputable def ep1421 := nat_lit 1968462895103236283417634348221487780947942723147500412076356579715769789753368913283973120

noncomputable def ep1422 := nat_lit 27633443041297929690376151484850333251763536782720733860757160721984679143373603095445504

noncomputable def ep1423 := nat_lit 622366656216742077394161355168970791893763768464934080139802301540783917120782663680

noncomputable def ep1424 := BSN.log_dyadic_bound 16657396644 82193396644 5 4 ep1421 1048576 273348 ep1422 ep1423 430977 98850793288 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 16657396644) (BSN.artanhQ 82193396644) 0 4 ep1422 ep1421 ep1423 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1425 := @Enclosure.Real.IsNear.mulLit_ff qz344 (Real.log (Enclosure.sfrac Bool.false 49425396644 16000000)) 1 2 0 1 36189263345237661 4503599627370496 250000000751707 68337000000000000000 36189263345237661 9007199254740992 250000000751707 136674000000000000000 qz345 (BSN.isNear_log_sfrac 49425396644 16000000 36189263345237661 4503599627370496 250000000751707 68337000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 49425396644) qz599)) Bool.false 303577544011967404965888 37778931862957161709568 1000000003006828 273348000000000000000 36189263345237661 4503599627370496 250000000751707 68337000000000000000 (BSN.log_rat_reduce_isNear 49425396644 16000000 11 98850793288 65536000000 430977 1048576 24973259072661432 36028797018963968 273348 1000000000000000 rfl rfl rfl rfl (ep1424 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1426 := BSN.arctan_dyadic_bound_f 5000 222262 1 0 1048576 273348 0 1 1 0 1 1 23584 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 222262) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 222262) 0 0 rfl) rfl rfl rfl

noncomputable def ep1427 := @Enclosure.Real.IsNear.subLit_ff_p qz354 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz899 qz631)) 884279719003555 562949953421312 1 2000000000000000 23584 1048576 1 273348 913957878932383465472 871618155414947 562949953421312 500000000068337 136674000000000000000 qz355 (ep1426 rfl) rfl rfl

noncomputable abbrev qz966 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz377)

noncomputable def ep1428 := @ep1406 36189263345237661 9007199254740992 250000000751707 136674000000000000000 Bool.false 871618155414947 562949953421312 500000000068337 136674000000000000000 Bool.false ep1407 36188168128577181 4503599627370496 250000000751707 68337000000000000000 Bool.false ep1408 876682727163299 281474976710656 500000000068337 68337000000000000000 (ep1409 (BSN.log_sum_c_succ qz61 0 1 rfl) (ep1419 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1420 (@congrArg Complex Complex (@HAdd.hAdd Complex Complex Complex qz13 qz69 qz588) qz966 Complex.log (BSN.w_shift_mk qz61 Bool.false 111131 1000 1 (@Eq.refl Real qz61) rfl)) (@Enclosure.Complex.IsNear.of_parts qz965 Bool.false 36189263345237661 9007199254740992 250000000751707 136674000000000000000 Bool.false 871618155414947 562949953421312 500000000068337 136674000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz965) (@HMul.hMul Real Real Real qz0 qz344 (Real.log (Enclosure.sfrac Bool.false 49425396644 16000000))) Bool.false 36189263345237661 9007199254740992 250000000751707 136674000000000000000 (Enclosure.clog_re_eq 5000 222262 4000 49425396644 16000000 rfl rfl rfl) (ep1425 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz965) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz631 qz899)) Bool.false 871618155414947 562949953421312 500000000068337 136674000000000000000 (Enclosure.clog_im_eq 5000 222262 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz631 qz899)) (@HSub.hSub Real Real Real qz347 qz354 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz899 qz631))) Bool.false 871618155414947 562949953421312 500000000068337 136674000000000000000 (BSN.arctan_recip 222262 5000 rfl rfl) ep1427)))) rfl rfl

noncomputable abbrev qz967 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 9000 4000) qz377))

noncomputable def ep1429 := @Enclosure.Complex.IsNear.of_eq (Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz69 qz551)) qz967 Bool.false 36194361471418013 9007199254740992 250000000751707 136674000000000000000 Bool.false 861497064981923 562949953421312 500000000068337 136674000000000000000

noncomputable def ep1430 := nat_lit 1979217739275760523387079303051256233226272286157227113117806744443348996430710056323973120

noncomputable def ep1431 := nat_lit 27937296845915831822212185393253278539154643915020055280072282419972845716961296663445504

noncomputable def ep1432 := nat_lit 639303466386942257372404317808876842448693604523725478033156261185210252803342663680

noncomputable def ep1433 := BSN.log_dyadic_bound 16713396644 82249396644 5 4 ep1430 1048576 273348 ep1431 ep1432 432164 98962793288 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 16713396644) (BSN.artanhQ 82249396644) 0 4 ep1431 ep1430 ep1432 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1434 := @Enclosure.Real.IsNear.mulLit_ff qz344 (Real.log (Enclosure.sfrac Bool.false 49481396644 16000000)) 1 2 0 1 36194361471418013 4503599627370496 250000000751707 68337000000000000000 36194361471418013 9007199254740992 250000000751707 136674000000000000000 qz345 (BSN.isNear_log_sfrac 49481396644 16000000 36194361471418013 4503599627370496 250000000751707 68337000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 49481396644) qz599)) Bool.false 303620310194028915195904 37778931862957161709568 1000000003006828 273348000000000000000 36194361471418013 4503599627370496 250000000751707 68337000000000000000 (BSN.log_rat_reduce_isNear 49481396644 16000000 11 98962793288 65536000000 432164 1048576 24973259072661432 36028797018963968 273348 1000000000000000 rfl rfl rfl rfl (ep1433 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1435 := BSN.arctan_dyadic_bound_f 9000 222262 1 0 1048576 273348 0 1 1 0 1 1 42436 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 222262) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 222262) 0 0 rfl) rfl rfl rfl

noncomputable def ep1436 := @Enclosure.Real.IsNear.subLit_ff_p qz354 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz902 qz631)) 884279719003555 562949953421312 1 2000000000000000 42436 1048576 1 273348 903345146410484891648 861497064981923 562949953421312 500000000068337 136674000000000000000 qz355 (ep1435 rfl) rfl rfl

noncomputable abbrev qz968 := (Complex.mk (Enclosure.sfrac Bool.false 9000 4000) qz377)

noncomputable def ep1437 := @ep1402 36194361471418013 9007199254740992 250000000751707 136674000000000000000 Bool.false 861497064981923 562949953421312 500000000068337 136674000000000000000 Bool.false ep1403 108570697728572375 9007199254740992 250000000751707 45558000000000000000 Bool.false ep1404 2614862519308521 562949953421312 500000000068337 45558000000000000000 (ep1405 (BSN.log_sum_c_succ qz61 1 2 rfl) (ep1428 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1429 (@congrArg Complex Complex (@HAdd.hAdd Complex Complex Complex qz13 qz69 qz551) qz968 Complex.log (BSN.w_shift_mk qz61 Bool.false 111131 1000 2 (@Eq.refl Real qz61) rfl)) (@Enclosure.Complex.IsNear.of_parts qz967 Bool.false 36194361471418013 9007199254740992 250000000751707 136674000000000000000 Bool.false 861497064981923 562949953421312 500000000068337 136674000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz967) (@HMul.hMul Real Real Real qz0 qz344 (Real.log (Enclosure.sfrac Bool.false 49481396644 16000000))) Bool.false 36194361471418013 9007199254740992 250000000751707 136674000000000000000 (Enclosure.clog_re_eq 9000 222262 4000 49481396644 16000000 rfl rfl rfl) (ep1434 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz967) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz631 qz902)) Bool.false 861497064981923 562949953421312 500000000068337 136674000000000000000 (Enclosure.clog_im_eq 9000 222262 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz631 qz902)) (@HSub.hSub Real Real Real qz347 qz354 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz902 qz631))) Bool.false 861497064981923 562949953421312 500000000068337 136674000000000000000 (BSN.arctan_recip 222262 9000 rfl rfl) ep1436)))) rfl rfl

noncomputable def ep1438 := @Enclosure.Complex.IsNear.of_eq (Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz69 qz550)) (Complex.log (Complex.mk qz607 qz377)) Bool.false 36202362995490461 9007199254740992 250000000751707 136674000000000000000 Bool.false 851391006934435 562949953421312 500000000068337 136674000000000000000

noncomputable def ep1439 := nat_lit 1996222097814185973492932615308649479921461438042296649930165087860716120718966138243973120

noncomputable def ep1440 := nat_lit 28420110402632670399956021170695748647136971270368284355576322943674239497508815127445504

noncomputable def ep1441 := nat_lit 666733653057852562804972738308974014296929741715767045503251033134968574590222663680

noncomputable def ep1442 := BSN.log_dyadic_bound 16801396644 82337396644 5 4 ep1439 1048576 273348 ep1440 ep1441 434027 99138793288 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 16801396644) (BSN.artanhQ 82337396644) 0 4 ep1440 ep1439 ep1441 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1443 := @Enclosure.Real.IsNear.mulLit_ff qz344 (Real.log (Enclosure.sfrac Bool.false 49569396644 16000000)) 1 2 0 1 36202362995490461 4503599627370496 250000000751707 68337000000000000000 36202362995490461 9007199254740992 250000000751707 136674000000000000000 qz345 (BSN.isNear_log_sfrac 49569396644 16000000 36202362995490461 4503599627370496 250000000751707 68337000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 49569396644) qz599)) Bool.false 303687431842875245068288 37778931862957161709568 1000000003006828 273348000000000000000 36202362995490461 4503599627370496 250000000751707 68337000000000000000 (BSN.log_rat_reduce_isNear 49569396644 16000000 11 99138793288 65536000000 434027 1048576 24973259072661432 36028797018963968 273348 1000000000000000 rfl rfl rfl rfl (ep1442 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1444 := BSN.arctan_dyadic_bound_f 13000 222262 1 0 1048576 273348 0 1 1 0 1 1 61260 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 13000) (BSN.arctanEvenQ 222262) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 13000) (BSN.arctanOddQ 222262) 0 0 rfl) rfl rfl rfl

noncomputable def ep1445 := @Enclosure.Real.IsNear.subLit_ff_p qz354 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz904 qz631)) 884279719003555 562949953421312 1 2000000000000000 61260 1048576 1 273348 892748176487282114560 851391006934435 562949953421312 500000000068337 136674000000000000000 qz355 (ep1444 rfl) rfl rfl

noncomputable def ep1446 := @ep1398 36202362995490461 9007199254740992 250000000751707 136674000000000000000 Bool.false 851391006934435 562949953421312 500000000068337 136674000000000000000 Bool.false ep1399 36193265181015709 2251799813685248 250000000751707 34168500000000000000 Bool.false ep1400 866563381560739 140737488355328 500000000068337 34168500000000000000 (ep1401 (BSN.log_sum_c_succ qz61 2 3 rfl) (ep1437 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1438 (@congrArg Complex Complex (@HAdd.hAdd Complex Complex Complex qz13 qz69 qz550) (Complex.mk qz607 qz377) Complex.log (BSN.w_shift_mk qz61 Bool.false 111131 1000 3 (@Eq.refl Real qz61) rfl)) (@Enclosure.Complex.IsNear.of_parts (Complex.log (Complex.mk qz607 qz377)) Bool.false 36202362995490461 9007199254740992 250000000751707 136674000000000000000 Bool.false 851391006934435 562949953421312 500000000068337 136674000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re (Complex.log (Complex.mk qz607 qz377))) (@HMul.hMul Real Real Real qz0 qz344 (Real.log (Enclosure.sfrac Bool.false 49569396644 16000000))) Bool.false 36202362995490461 9007199254740992 250000000751707 136674000000000000000 (Enclosure.clog_re_eq 13000 222262 4000 49569396644 16000000 rfl rfl rfl) (ep1443 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im (Complex.log (Complex.mk qz607 qz377))) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz631 qz904)) Bool.false 851391006934435 562949953421312 500000000068337 136674000000000000000 (Enclosure.clog_im_eq 13000 222262 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz631 qz904)) (@HSub.hSub Real Real Real qz347 qz354 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz904 qz631))) Bool.false 851391006934435 562949953421312 500000000068337 136674000000000000000 (BSN.arctan_recip 222262 13000 rfl rfl) ep1445)))) rfl rfl

noncomputable def ep1447 := @ep1284 ep1285 Bool.false 36193265181015709 2251799813685248 250000000751707 34168500000000000000 Bool.false 866563381560739 140737488355328 500000000068337 34168500000000000000 Bool.true ep1286 ep1274 ep1275 ep1276 ep1277 Bool.false ep1287 ep1270 ep1266 ep1271 ep1268 (@ep1288 ep1275 ep1280 ep1281 Bool.false ep1282 ep1266 ep1283 ep1285 (BSN.logGammaStirling_unfold 2 qz57) (ep1395 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep1396 500000000068337 34168500000000000000 (BSN.log_sum_c_eq qz61 4) (ep1397 (BSN.log_sum_c_succ qz61 3 4 rfl) (ep1446 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable def ep1448 := @Enclosure.Real.IsNear.mulLit_ff (@HDiv.hDiv Real Real Real qz1 qz61 (2 : Real)) (Real.log Real.pi) 111131 2000 0 1 75021 65536 1 262144 8337158751 131072000 111131 524288000 (@Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real qz1 qz61 (2 : Real)) (Enclosure.sfrac Bool.false 111131 2000) Bool.false 111131 2000 0 1 (BSN.t_half_eq qz61 Bool.false 111131 1000 (@Eq.refl Real qz61)) (Enclosure.Real.IsNear.const Bool.false 111131 2000)) EMRow34.d6 rfl

noncomputable def ep1449 := @ep1272 111131 524288000 ep1273 ep1265 ep1266 ep1267 ep1268 (@ep1278 ep1271 ep1268 (ep1447 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep1448 rfl rfl

noncomputable def ep1450 := nat_lit 8340177302352221293885160965755851914686334016922598877961530919278923004630625

noncomputable def ep1451 := nat_lit 16749503384780526626398509735866071452795934267406783628029486465611250390625

noncomputable def ep1452 := nat_lit 21816203262585220631351728751692971851350157579316719411644342762881427749590625

noncomputable def ep1453 := BSN.sin_dyadic_bound_f 3372874965 2147483648 3 2 1048576 273615 ep1450 ep131 ep1451 ep1452 ep134 ep1451 1048575 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3372874965) qz272 0 2 ep1450 ep131 ep1451 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3372874965) qz273 0 2 ep1452 ep134 ep1451 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1454 := @ep1264 1048576 Bool.true 1048575 1048576 1 136674 (@ep1269 6794273 65536 359 1048576 ep1449 rfl) (Enclosure.sfrac_false_div 6794273 65536) (BSN.cos_reduce1 qz629 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14834060974482947833856) qz583) 226375608064910080 72057594037927936 Bool.false 1048575 1048576 16 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q1 6794273 65536 226375608064910080 72057594037927936 16 14834060974482947833856 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1048575 1048576 14834060974482947833856 9444732965739290427392 3372874965 2147483648 273615 273348 (ep1453 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1455 := nat_lit 154478871950640639369767339137935503

noncomputable def ep1456 := nat_lit 15330545809252766873875906560000000000

noncomputable def ep1457 := nat_lit 49236997675826781501067769525582762100139

noncomputable def ep1458 := nat_lit 7333504562768344309020404786135040000000000

noncomputable abbrev qz78 := (@HPow.hPow Complex Complex Complex (@instHPow Complex Complex Complex.instPow) qz608 (@Neg.neg Complex Complex.instNeg qz378))

noncomputable abbrev qz79 := (@HAdd.hAdd Complex Complex Complex qz260 (@HDiv.hDiv Complex Complex Complex qz352 qz608 (@HSub.hSub Complex Complex Complex qz593 qz378 (1 : Complex))) qz351)

noncomputable def ep1459 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz64 2 28) (@HAdd.hAdd Complex Complex Complex qz13 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 28, @HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast n) qz65) (@HMul.hMul Complex Complex Complex qz3 qz78 (@HAdd.hAdd Complex Complex Complex qz13 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1))))))) Bool.false ep1259 ep1260 ep1261

noncomputable def ep1460 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 28, @HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast n) qz65) (@HMul.hMul Complex Complex Complex qz3 qz78 (@HAdd.hAdd Complex Complex Complex qz13 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))))) Bool.false 74500779689 1099511627776 496712419390499 75137326107328512

noncomputable def ep1461 := nat_lit 2321781008895977971974112299986810371

noncomputable def ep1462 := nat_lit 1530504375676509542412176496436631711333

noncomputable def ep1463 := nat_lit 1006762499565495585554359380862064497

noncomputable def ep1464 := nat_lit 763984778353033719863385615182762100139

noncomputable def ep1465 := nat_lit 4837100448125145481793307851394540814028448464896

noncomputable def ep1466 := nat_lit 169851315955449157719470277817951697495631331328

noncomputable def ep1467 := @ep1460 Bool.true 83284600987 1099511627776 496642846037495 75137326107328512 Bool.false ep1461 ep1260 ep1462 ep1262 Bool.false ep1463 ep1456 ep1464 ep1458 Bool.false ep1465 ep1259 ep1260 ep1261 ep1262 Bool.true ep1466 ep1455 ep1456

noncomputable def ep1468 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 28, @HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast n) qz65) (BSN.headSumC qz64 28) Bool.false 74500779689 1099511627776 496712419390499 75137326107328512 Bool.true 83284600987 1099511627776 496642846037495

noncomputable abbrev qz969 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 27) qz65)

noncomputable def ep1469 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 28) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 27) qz969) Bool.false 74500779689 1099511627776 496712419390499 75137326107328512 Bool.true 83284600987 1099511627776 496642846037495 75137326107328512

noncomputable def ep1470 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 27) qz969 Bool.false 131746312813 1099511627776 484810225268887 75137326107328512 Bool.false 120426242739 1099511627776 484691053057957 75137326107328512 Bool.true

noncomputable abbrev qz970 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 26) qz65)

noncomputable def ep1471 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 27) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 26) qz970) Bool.false 131746312813 1099511627776 484810225268887 75137326107328512 Bool.false 120426242739 1099511627776 484691053057957 75137326107328512

noncomputable def ep1472 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 26) qz970 Bool.false 70796122843 274877906944 236332397563175 37568663053664256 Bool.true 33078442327 1099511627776 472544936196907 75137326107328512 Bool.true

noncomputable abbrev qz971 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 25) qz65)

noncomputable def ep1473 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 26) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 25) qz971) Bool.false 70796122843 274877906944 236332397563175 37568663053664256 Bool.true 33078442327 1099511627776 472544936196907 75137326107328512

noncomputable def ep1474 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 25) qz971 Bool.false 82834314697 1099511627776 460250574735509 75137326107328512 Bool.true 15465575669 137438953472 57520807946767 9392165763416064 Bool.false

noncomputable abbrev qz408 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 25 1)))

noncomputable def ep1475 := @Enclosure.Complex.IsNear.of_eq qz971 (Complex.mk (@HMul.hMul Real Real Real qz0 qz361 (Real.cos qz408)) (@HMul.hMul Real Real Real qz0 qz361 (@Neg.neg Real Real.instNeg (Real.sin qz408)))) Bool.false 200350176675 1099511627776 12414220390841 75137326107328512 Bool.false 90646163025 1099511627776 12378472622771 75137326107328512 (BSN.cpow_neg_s_mk qz61 111131 1000 25 (@Eq.refl Real qz61) rfl)

noncomputable def ep1476 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz363 111131 1000 0 1 3624129903009015 1125899906842624 125000000068337 17084250000000000000 80550636050258969193 225179981368524800 13891375007594359147 17084250000000000000000 qz380 (BSN.isNear_log_sfrac 25 1 3624129903009015 1125899906842624 125000000068337 17084250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz909) Bool.false 60802810194841294602240 18889465931478580854784 1000000000546696 136674000000000000000 3624129903009015 1125899906842624 125000000068337 17084250000000000000 (BSN.log_rat_reduce_isNear 25 1 4 50 32 233982 524288 24973259072661432 36028797018963968 136674 1000000000000000 rfl rfl rfl rfl (ep707 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1477 := nat_lit 2359824967363086442008053231508639839747149526053445753157047493658499700817920

noncomputable def ep1478 := nat_lit 1344813171271949793571277499929539235039388660351998439159892467000289591296

noncomputable def ep1479 := nat_lit 6178316645578405143688643061808456516766756415166073736986008371778070176137216

noncomputable def ep1480 := BSN.sin_dyadic_bound_f 2460836412 2147483648 3 2 1048576 273615 ep1477 ep131 ep1478 ep1479 ep134 ep1478 955345 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2460836412) qz272 0 2 ep1477 ep131 ep1478 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2460836412) qz273 0 2 ep1479 ep134 ep1478 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz635 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 46886641) (@Nat.cast Real Real.instNatCast 131072))

noncomputable def ep1481 := @Enclosure.Real.IsNear.cos_image qz408 qz635 Bool.false 46886641 131072 427 524288 Bool.false 955345 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz408 Bool.false 80550636050258969193 225179981368524800 13891375007594359147 17084250000000000000000 46886641 131072 427 524288 (ep1476 rfl) rfl) (Enclosure.sfrac_false_div 46886641 131072) (BSN.cos_reduce3 qz635 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 21645745995691098898432) qz560) 226375608064910080 72057594037927936 Bool.false 955345 1048576 56 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q3 46886641 131072 226375608064910080 72057594037927936 56 21645745995691098898432 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 955345 1048576 21645745995691098898432 18889465931478580854784 2460836412 2147483648 273615 273348 (ep1480 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1482 := nat_lit 1311611565500057778801616807504768595075100576100959639949097448684499962494976

noncomputable def ep1483 := nat_lit 3932145070157629436817707867514446706755222950982174922968972561119499308302336

noncomputable def ep1484 := BSN.cos_dyadic_bound_f 2460836412 2147483648 3 2 1048576 273615 ep1482 ep138 ep1478 ep1483 ep140 ep1478 432235 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2460836412) qz266 0 2 ep1482 ep138 ep1478 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2460836412) qz267 0 2 ep1483 ep140 ep1478 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1485 := @Enclosure.Real.IsNear.sin_image qz408 qz635 Bool.false 46886641 131072 427 524288 Bool.true 432235 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz408 Bool.false 80550636050258969193 225179981368524800 13891375007594359147 17084250000000000000000 46886641 131072 427 524288 (ep1476 rfl) rfl) (Enclosure.sfrac_false_div 46886641 131072) (BSN.sin_reduce3 qz635 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 21645745995691098898432) qz560) 226375608064910080 72057594037927936 Bool.false 432235 1048576 56 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q3 46886641 131072 226375608064910080 72057594037927936 56 21645745995691098898432 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 432235 1048576 21645745995691098898432 18889465931478580854784 2460836412 2147483648 273615 273348 (ep1484 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1486 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz361 (Real.cos qz408)) (@HMul.hMul Real Real Real qz0 qz361 (@Neg.neg Real Real.instNeg (Real.sin qz408))) Bool.false 200350176675 1099511627776 12414220390841 75137326107328512 Bool.false 90646163025 1099511627776 12378472622771 75137326107328512 (@Enclosure.Real.IsNear.mulLit_ff qz361 (Real.cos qz408) 209715 1048576 1 1048576 955345 1048576 29442043 35828269056 200350176675 1099511627776 12414220390841 75137326107328512 qz609 (@Enclosure.Real.IsNear.recentre' (Real.cos qz408) Bool.false 955345 1048576 58884086 71656538112 955345 1048576 29442043 35828269056 (ep1481 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz361 (@Neg.neg Real Real.instNeg (Real.sin qz408)) 209715 1048576 1 1048576 432235 1048576 29442043 35828269056 90646163025 1099511627776 12378472622771 75137326107328512 qz609 (@Enclosure.Real.IsNear.neg (Real.sin qz408) Bool.true 432235 1048576 29442043 35828269056 (@Enclosure.Real.IsNear.recentre' (Real.sin qz408) Bool.true 432235 1048576 58884086 71656538112 432235 1048576 29442043 35828269056 (ep1485 rfl rfl) rfl)) rfl)

noncomputable def ep1487 := @ep1474 200350176675 1099511627776 12414220390841 75137326107328512 Bool.false 90646163025 1099511627776 12378472622771 75137326107328512 Bool.false 311364641069346347548672 70796122843 274877906944 236332397563175 37568663053664256 Bool.true 4546266495906788409344 33078442327 1099511627776 472544936196907 75137326107328512 EMRow34.d19 (ep1475 ep1486) rfl rfl

noncomputable abbrev qz409 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 26 1)))

noncomputable def ep1488 := @Enclosure.Complex.IsNear.of_eq qz970 (Complex.mk (@HMul.hMul Real Real Real qz0 qz364 (Real.cos qz409)) (@HMul.hMul Real Real Real qz0 qz364 (@Neg.neg Real Real.instNeg (Real.sin qz409)))) Bool.true 151438178559 1099511627776 4048476714179 25045775369109504 Bool.false 76752342533 549755813888 2024352810175 12522887684554752 (BSN.cpow_neg_s_mk qz61 111131 1000 26 (@Eq.refl Real qz61) rfl)

noncomputable def ep1489 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz366 111131 1000 0 1 3668288609262839 1125899906842624 125000000068337 17084250000000000000 407660581435988560909 1125899906842624000 13891375007594359147 17084250000000000000000 qz380 (BSN.isNear_log_sfrac 26 1 3668288609262839 1125899906842624 125000000068337 17084250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz912) Bool.false 61543670347942250676224 18889465931478580854784 1000000000546696 136674000000000000000 3668288609262839 1125899906842624 125000000068337 17084250000000000000 (BSN.log_rat_reduce_isNear 26 1 4 52 32 254545 524288 24973259072661432 36028797018963968 136674 1000000000000000 rfl rfl rfl rfl (ep718 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1490 := nat_lit 299320029736905653743239003517035935856841861138953696140028338096560943190625

noncomputable def ep1491 := nat_lit 70147224008393941840905313251692495367183927036513149353674333425250390625

noncomputable def ep1492 := nat_lit 897819794762700173346035199924604422579791215562788062121377665622832328790625

noncomputable def ep1493 := BSN.cos_dyadic_bound_f 1701184085 2147483648 3 2 1048576 273615 ep1490 ep138 ep1491 ep1492 ep140 ep1491 736413 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1701184085) qz266 0 2 ep1490 ep138 ep1491 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1701184085) qz267 0 2 ep1492 ep140 ep1491 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz972 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 189831751) qz306)

noncomputable def ep1494 := @Enclosure.Real.IsNear.cos_image qz409 qz972 Bool.false 189831751 524288 853 1048576 Bool.true 736413 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz409 Bool.false 407660581435988560909 1125899906842624000 13891375007594359147 17084250000000000000000 189831751 524288 853 1048576 (ep1489 rfl) rfl) (Enclosure.sfrac_false_div 189831751 524288) (BSN.cos_reduce2 qz972 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 59855093872858520092672) qz307) 226375608064910080 72057594037927936 Bool.false 736413 1048576 57 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q2 189831751 524288 226375608064910080 72057594037927936 57 59855093872858520092672 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 736413 1048576 59855093872858520092672 75557863725914323419136 1701184085 2147483648 273615 273348 (ep1493 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1495 := nat_lit 8375393961384380266154596776148200625

noncomputable def ep1496 := BSN.sin_dyadic_bound_f 1701184085 2147483648 2 1 1048576 273615 ep1495 ep105 ep1495 ep1495 ep106 ep1495 746462 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1701184085) qz272 0 1 ep1495 ep105 ep1495 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1701184085) qz273 0 1 ep1495 ep106 ep1495 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1497 := @Enclosure.Real.IsNear.sin_image qz409 qz972 Bool.false 189831751 524288 853 1048576 Bool.true 746462 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz409 Bool.false 407660581435988560909 1125899906842624000 13891375007594359147 17084250000000000000000 189831751 524288 853 1048576 (ep1489 rfl) rfl) (Enclosure.sfrac_false_div 189831751 524288) (BSN.sin_reduce2 qz972 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 59855093872858520092672) qz307) 226375608064910080 72057594037927936 Bool.false 746462 1048576 57 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q2 189831751 524288 226375608064910080 72057594037927936 57 59855093872858520092672 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 746462 1048576 59855093872858520092672 75557863725914323419136 1701184085 2147483648 273615 273348 (ep1496 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1498 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz364 (Real.cos qz409)) (@HMul.hMul Real Real Real qz0 qz364 (@Neg.neg Real Real.instNeg (Real.sin qz409))) Bool.true 151438178559 1099511627776 4048476714179 25045775369109504 Bool.false 76752342533 549755813888 2024352810175 12522887684554752 (@Enclosure.Real.IsNear.mulLit_ft qz364 (Real.cos qz409) 205643 1048576 1 1048576 736413 1048576 58815749 71656538112 151438178559 1099511627776 4048476714179 25045775369109504 qz611 (@Enclosure.Real.IsNear.recentre' (Real.cos qz409) Bool.true 736413 1048576 117631498 143313076224 736413 1048576 58815749 71656538112 (ep1494 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz364 (@Neg.neg Real Real.instNeg (Real.sin qz409)) 205643 1048576 1 1048576 373231 524288 58815749 71656538112 76752342533 549755813888 2024352810175 12522887684554752 qz611 (@Enclosure.Real.IsNear.neg (Real.sin qz409) Bool.true 373231 524288 58815749 71656538112 (@Enclosure.Real.IsNear.recentre' (Real.sin qz409) Bool.true 746462 1048576 117631498 143313076224 373231 524288 58815749 71656538112 (ep1497 rfl rfl) rfl)) rfl)

noncomputable def ep1499 := @ep1472 151438178559 1099511627776 4048476714179 25045775369109504 Bool.false 76752342533 549755813888 2024352810175 12522887684554752 Bool.false 36214150713626928873472 131746312813 1099511627776 484810225268887 75137326107328512 Bool.false 66205027090452795359232 120426242739 1099511627776 484691053057957 75137326107328512 (ep1473 (BSN.head_sum_c_succ qz64 25 26 rfl rfl) (ep1487 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1488 ep1498) rfl rfl

noncomputable abbrev qz410 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 27 1)))

noncomputable def ep1500 := @Enclosure.Complex.IsNear.of_eq qz969 (Complex.mk (@HMul.hMul Real Real Real qz0 qz367 (Real.cos qz410)) (@HMul.hMul Real Real Real qz0 qz367 (@Neg.neg Real Real.instNeg (Real.sin qz410)))) Bool.true 14311383281 274877906944 2975548530403 18784331526832128 Bool.true 101855421863 549755813888 5975896489769 37568663053664256 (BSN.cpow_neg_s_mk qz61 111131 1000 27 (@Eq.refl Real qz61) rfl)

noncomputable def ep1501 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz369 111131 1000 0 1 3710780868205815 1125899906842624 125000000068337 17084250000000000000 82476557732916085353 225179981368524800 13891375007594359147 17084250000000000000000 qz380 (BSN.isNear_log_sfrac 27 1 3710780868205815 1125899906842624 125000000068337 17084250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz914) Bool.false 62256572154556490711040 18889465931478580854784 1000000000546696 136674000000000000000 3710780868205815 1125899906842624 125000000068337 17084250000000000000 (BSN.log_rat_reduce_isNear 27 1 4 54 32 274332 524288 24973259072661432 36028797018963968 136674 1000000000000000 rfl rfl rfl rfl (ep733 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1502 := nat_lit 119783799219864110469430587318066241

noncomputable def ep1503 := BSN.sin_dyadic_bound_f 588300911 2147483648 2 1 1048576 273615 ep1502 ep105 ep1502 ep1502 ep106 ep1502 283676 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 588300911) qz272 0 1 ep1502 ep105 ep1502 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 588300911) qz273 0 1 ep1502 ep106 ep1502 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz636 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 48007675) (@Nat.cast Real Real.instNatCast 131072))

noncomputable def ep1504 := @Enclosure.Real.IsNear.cos_image qz410 qz636 Bool.false 48007675 131072 427 524288 Bool.true 283676 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz410 Bool.false 82476557732916085353 225179981368524800 13891375007594359147 17084250000000000000000 48007675 131072 427 524288 (ep1501 rfl) rfl) (Enclosure.sfrac_false_div 48007675 131072) (BSN.cos_reduce1 qz636 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 5174749543416746475520) qz560) 226375608064910080 72057594037927936 Bool.false 283676 1048576 58 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q1 48007675 131072 226375608064910080 72057594037927936 58 5174749543416746475520 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 283676 1048576 5174749543416746475520 18889465931478580854784 588300911 2147483648 273615 273348 (ep1503 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1505 := BSN.cos_dyadic_bound_f 588300911 2147483648 2 1 1048576 273615 ep1502 ep91 ep1502 ep1502 ep92 ep1502 1009474 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 588300911) qz266 0 1 ep1502 ep91 ep1502 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 588300911) qz267 0 1 ep1502 ep92 ep1502 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1506 := @Enclosure.Real.IsNear.sin_image qz410 qz636 Bool.false 48007675 131072 427 524288 Bool.false 1009474 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz410 Bool.false 82476557732916085353 225179981368524800 13891375007594359147 17084250000000000000000 48007675 131072 427 524288 (ep1501 rfl) rfl) (Enclosure.sfrac_false_div 48007675 131072) (BSN.sin_reduce1 qz636 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 5174749543416746475520) qz560) 226375608064910080 72057594037927936 Bool.false 1009474 1048576 58 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q1 48007675 131072 226375608064910080 72057594037927936 58 5174749543416746475520 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1009474 1048576 5174749543416746475520 18889465931478580854784 588300911 2147483648 273615 273348 (ep1505 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1507 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz367 (Real.cos qz410)) (@HMul.hMul Real Real Real qz0 qz367 (@Neg.neg Real Real.instNeg (Real.sin qz410))) Bool.true 14311383281 274877906944 2975548530403 18784331526832128 Bool.true 101855421863 549755813888 5975896489769 37568663053664256 (@Enclosure.Real.IsNear.mulLit_ft qz367 (Real.cos qz410) 201799 1048576 1 1048576 70919 262144 29442043 35828269056 14311383281 274877906944 2975548530403 18784331526832128 qz612 (@Enclosure.Real.IsNear.recentre' (Real.cos qz410) Bool.true 283676 1048576 58884086 71656538112 70919 262144 29442043 35828269056 (ep1504 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz367 (@Neg.neg Real Real.instNeg (Real.sin qz410)) 201799 1048576 1 1048576 504737 524288 29442043 35828269056 101855421863 549755813888 5975896489769 37568663053664256 qz612 (@Enclosure.Real.IsNear.neg (Real.sin qz410) Bool.false 504737 524288 29442043 35828269056 (@Enclosure.Real.IsNear.recentre' (Real.sin qz410) Bool.false 1009474 1048576 58884086 71656538112 504737 524288 29442043 35828269056 (ep1506 rfl rfl) rfl)) rfl)

noncomputable def ep1508 := @ep1470 14311383281 274877906944 2975548530403 18784331526832128 Bool.true 101855421863 549755813888 5975896489769 37568663053664256 Bool.false 20478618386608387260416 74500779689 1099511627776 496712419390499 75137326107328512 Bool.true 45786193599945513107456 83284600987 1099511627776 496642846037495 75137326107328512 (ep1471 (BSN.head_sum_c_succ qz64 26 27 rfl rfl) (ep1499 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1500 ep1507) rfl rfl

noncomputable def ep1509 := @Enclosure.Complex.IsNear.mul qz78 (@HAdd.hAdd Complex Complex Complex qz13 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1))))) Bool.false ep1461 ep1260 ep1462 ep1262 Bool.false

noncomputable def ep1510 := nat_lit 42741027938429375247459323723991

noncomputable def ep1511 := nat_lit 486683993944532281710346240000000

noncomputable def ep1512 := nat_lit 6099819888935233078467410665287139

noncomputable def ep1513 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re qz78) (Complex.re (@HAdd.hAdd Complex Complex Complex qz13 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 (Complex.im qz78) (Complex.im (@HAdd.hAdd Complex Complex Complex qz13 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1))))))) ep1510 ep1511 ep1512

noncomputable def ep1514 := nat_lit 77603222886437505915559839006720000000

noncomputable def ep1515 := nat_lit 370903751225072668615825094624622629

noncomputable def ep1516 := nat_lit 377638416667750490581835880697362440333

noncomputable def ep1517 := nat_lit 1129973654474060195004670842155121585863425722268469047632855040000000

noncomputable def ep1518 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz78) (Complex.re (@HAdd.hAdd Complex Complex Complex qz13 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))))) 95818349879 549755813888 5860625237039 37568663053664256 3122441535956537057703

noncomputable abbrev qz411 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 28 1)))

noncomputable abbrev qz973 := (@Neg.neg Real Real.instNeg (Real.sin qz411))

noncomputable def ep1519 := @Enclosure.Complex.IsNear.of_eq qz78 (Complex.mk (@HMul.hMul Real Real Real qz0 qz370 (Real.cos qz411)) (@HMul.hMul Real Real Real qz0 qz370 qz973)) Bool.false 95818349879 549755813888 5860625237039 37568663053664256 Bool.false 80321606953 1099511627776 11682863189383 75137326107328512 (BSN.cpow_neg_s_mk qz61 111131 1000 28 (@Eq.refl Real qz61) rfl)

noncomputable def ep1520 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz372 111131 1000 0 1 3751726938922231 1125899906842624 125000000068337 17084250000000000000 416933166449366453261 1125899906842624000 13891375007594359147 17084250000000000000000 qz380 (BSN.isNear_log_sfrac 28 1 3751726938922231 1125899906842624 125000000068337 17084250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz613) Bool.false 62943533227317076688896 18889465931478580854784 1000000000546696 136674000000000000000 3751726938922231 1125899906842624 125000000068337 17084250000000000000 (BSN.log_rat_reduce_isNear 28 1 4 56 32 293399 524288 24973259072661432 36028797018963968 136674 1000000000000000 rfl rfl rfl rfl (ep760 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1521 := nat_lit 2599104888723843840002191007427931079775965121438816623270838357689870646199905

noncomputable def ep1522 := nat_lit 1631172252050379984001253321728256240525489274868956645318765797020372780641

noncomputable def ep1523 := nat_lit 6804538524916271346698307752171307079785724525894731893045489125516390136497761

noncomputable def ep1524 := BSN.sin_dyadic_bound_f 2520939819 2147483648 3 2 1048576 273615 ep1521 ep131 ep1522 ep1523 ep134 ep1522 967066 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2520939819) qz272 0 2 ep1521 ep131 ep1522 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2520939819) qz273 0 2 ep1523 ep134 ep1522 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz974 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 194149635) qz306)

noncomputable def ep1525 := @Enclosure.Real.IsNear.cos_image qz411 qz974 Bool.false 194149635 524288 853 1048576 Bool.false 967066 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz411 Bool.false 416933166449366453261 1125899906842624000 13891375007594359147 17084250000000000000000 194149635 524288 853 1048576 (ep1520 rfl) rfl) (Enclosure.sfrac_false_div 194149635 524288) (BSN.cos_reduce3 qz974 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 88697684616909495992320) qz307) 226375608064910080 72057594037927936 Bool.false 967066 1048576 58 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q3 194149635 524288 226375608064910080 72057594037927936 58 88697684616909495992320 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 967066 1048576 88697684616909495992320 75557863725914323419136 2520939819 2147483648 273615 273348 (ep1524 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1526 := nat_lit 1444672125847491191105217783380729824871325284921506549215051872404159413569121

noncomputable def ep1527 := nat_lit 4330754033038372813347650843498732962132924876214781734354518085618437495146081

noncomputable def ep1528 := BSN.cos_dyadic_bound_f 2520939819 2147483648 3 2 1048576 273615 ep1526 ep138 ep1522 ep1527 ep140 ep1522 405331 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2520939819) qz266 0 2 ep1526 ep138 ep1522 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2520939819) qz267 0 2 ep1527 ep140 ep1522 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1529 := @Enclosure.Real.IsNear.sin_image qz411 qz974 Bool.false 194149635 524288 853 1048576 Bool.true 405331 1048576 1 136674 (@Enclosure.Real.IsNear.recentre' qz411 Bool.false 416933166449366453261 1125899906842624000 13891375007594359147 17084250000000000000000 194149635 524288 853 1048576 (ep1520 rfl) rfl) (Enclosure.sfrac_false_div 194149635 524288) (BSN.sin_reduce3 qz974 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 88697684616909495992320) qz307) 226375608064910080 72057594037927936 Bool.false 405331 1048576 58 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q3 194149635 524288 226375608064910080 72057594037927936 58 88697684616909495992320 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 405331 1048576 88697684616909495992320 75557863725914323419136 2520939819 2147483648 273615 273348 (ep1528 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1530 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz370 (Real.cos qz411)) (@HMul.hMul Real Real Real qz0 qz370 qz973) Bool.false 95818349879 549755813888 5860625237039 37568663053664256 Bool.false 80321606953 1099511627776 11682863189383 75137326107328512 (@Enclosure.Real.IsNear.mulLit_ff qz370 (Real.cos qz411) 198163 1048576 1 1048576 483533 524288 58815749 71656538112 95818349879 549755813888 5860625237039 37568663053664256 qz614 (@Enclosure.Real.IsNear.recentre' (Real.cos qz411) Bool.false 967066 1048576 117631498 143313076224 483533 524288 58815749 71656538112 (ep1525 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz370 qz973 198163 1048576 1 1048576 405331 1048576 58815749 71656538112 80321606953 1099511627776 11682863189383 75137326107328512 qz614 (@Enclosure.Real.IsNear.neg (Real.sin qz411) Bool.true 405331 1048576 58815749 71656538112 (@Enclosure.Real.IsNear.recentre' (Real.sin qz411) Bool.true 405331 1048576 117631498 143313076224 405331 1048576 58815749 71656538112 (ep1529 rfl rfl) rfl)) rfl)

noncomputable def ep1531 := @ep1518 6196911195023360000000 0 1 ep1510 ep1511 ep1512 ep1514 (@Enclosure.Complex.IsNear.re_isNear qz78 Bool.false 95818349879 549755813888 5860625237039 37568663053664256 Bool.false 80321606953 1099511627776 11682863189383 75137326107328512 (ep1519 ep1530))

noncomputable def ep1532 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz13 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1))))) Bool.false 3122441535956537057703 6196911195023360000000 0 1 Bool.false

noncomputable def ep1533 := nat_lit 32324132410532360285144651

noncomputable def ep1534 := nat_lit 195202702643235840000000000

noncomputable def ep1535 := @Enclosure.Complex.IsNear.addLitP qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) Bool.false 12322349161 24700698322 0 1 Bool.true 3111668000

noncomputable def ep1536 := @ep1535 12350349161 0 1 Bool.false 2510907023 501760000000 0 1 Bool.false 6599442106611091 15805440000000000 0 1 Bool.false 6244883071913074115406 3122441535956537057703 6196911195023360000000 0 1 Bool.false ep1533 ep1533 ep1534 0 1

noncomputable abbrev qz80 := (@HDiv.hDiv Complex Complex Complex qz352 qz608 (@HSub.hSub Complex Complex Complex qz593 qz378 (1 : Complex)))

noncomputable def ep1537 := @Enclosure.Complex.IsNear.addLitP qz80 qz24 Bool.true 56000000 49401396644 0 1 Bool.true 12446672000 49401396644 0 1

noncomputable def ep1538 := @Enclosure.Complex.IsNear.of_eq qz80 (Complex.mk (Enclosure.sfrac Bool.true 56000000 49401396644) (Enclosure.sfrac Bool.true 12446672000 49401396644)) Bool.true 56000000 49401396644 0 1 Bool.true 12446672000 49401396644 0 1

noncomputable def ep1539 := @ep1537 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 49289396644 12322349161 24700698322 0 1 Bool.true 12446672000 3111668000 12350349161 0 1 (ep1538 (BSN.N_div_s_sub_one_mk qz61 111131 1000 28 (@Eq.refl Real qz61) rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 56000000 49401396644) (Enclosure.sfrac Bool.true 12446672000 49401396644) Bool.true 56000000 49401396644 0 1 Bool.true 12446672000 49401396644 0 1 (Enclosure.Real.IsNear.const Bool.true 56000000 49401396644) (Enclosure.Real.IsNear.const Bool.true 12446672000 49401396644))) qz357 rfl

noncomputable def ep1540 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz13 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) qz50)) Bool.false 2510907023 501760000000 0 1

noncomputable def ep1541 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) qz50) Bool.false 1 672 0 1 Bool.false

noncomputable def ep1542 := @ep1541 111131 336000 0 1 Bool.false 5292721069 1505280000000 0 1 Bool.false 1371839866611091 15805440000000000 0 1 Bool.false 5061988558368 2510907023 501760000000 0 1 Bool.false 2217412547821326576000 6599442106611091 15805440000000000 0

noncomputable def ep1543 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz13 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) qz52)) Bool.false 1 672 0 1

noncomputable def ep1544 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) qz52) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1545 := @ep1544 0 1 0 1 Bool.false 1 672 0 1 Bool.false 111131 336000 0 1 Bool.false 1 1 672 0 1 Bool.false 111131 111131 336000 0

noncomputable def ep1546 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (Complex.mk qz262 qz262) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1547 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) qz52 Bool.false 1 672 0 1 Bool.false 111131 336000 0 1

noncomputable def ep1548 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz52)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz52)) 1 672 0 1 0 1 0

noncomputable def ep1549 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz52) 1 24 0 1 1 28 0 1 1

noncomputable def ep1550 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep1551 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep1552 := @ep1551 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep787) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 111131 1000 0 1 ep1214)

noncomputable def ep1553 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 111131 1000 0 1 0 1 0

noncomputable def ep1554 := @ep1553 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep787) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 111131 1000 0 1 ep1214)

noncomputable def ep1555 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)))) 111131 12000 0 1 0 1 0 1 111131

noncomputable def ep1556 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 111131 1000 0 1 111131 12000 0

noncomputable def ep1557 := @ep1556 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep787) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 111131 1000 0 1 ep1214)

noncomputable def ep1558 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep1559 := @ep1558 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep787) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 111131 1000 0 1 ep1214)

noncomputable def ep1560 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 111131 12000 0 1 (@ep1550 1 24 0 1 (ep1552 rfl) (ep1554 rfl) rfl rfl) (@ep1555 111131 12000 0 1 (ep1557 rfl) (ep1559 rfl) rfl rfl)

noncomputable def ep1561 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 111131 12000 0 1 ep1560

noncomputable def ep1562 := @ep1549 672 0 1 ep1561 qz918

noncomputable def ep1563 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz52) 111131 12000 0 1 0 1 0 1 0

noncomputable def ep1564 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 111131 12000 0 1 ep1560

noncomputable def ep1565 := @ep1563 1 0 1 ep1564 qz919

noncomputable def ep1566 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz52)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz52)) 0 1 0 1 111131 336000 0

noncomputable def ep1567 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz52) 1 24 0 1 0 1 0 1 0

noncomputable def ep1568 := @ep1567 1 0 1 ep1561 qz919

noncomputable def ep1569 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz52) 111131 12000 0 1 1 28 0 1 111131

noncomputable def ep1570 := @ep1569 336000 0 1 ep1564 qz918

noncomputable def ep1571 := @ep1545 1 (@ep1546 0 1 0 1 (BSN.bern_sum_base qz64 28) qz360) (ep1547 (@ep1548 1 1 1 672 0 1 (ep1562 rfl) (ep1565 rfl) rfl rfl) (@ep1566 1 111131 111131 336000 0 1 (ep1568 rfl) (ep1570 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep1572 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) qz50 Bool.false 5292721069 1505280000000 0 1 Bool.false 1371839866611091 15805440000000000 0 1

noncomputable def ep1573 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.re qz50)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.im qz50)) 5292721069 1505280000000 0 1 0 1 0

noncomputable def ep1574 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.re qz50) 37049047483 480000000 0 1 1 21952 0 1 5292721069

noncomputable def ep1575 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)))) 37049047483 480000000 0 1 0 1 0 1 37049047483

noncomputable def ep1576 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 111147142449 2000000 0 1 37049047483 480000000 0

noncomputable def ep1577 := @ep1576 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep813) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 111147142449 2000000 0 1 Bool.true 1371839866611091 1000000000 0 1 EMRow34.d20)

noncomputable def ep1578 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 1371839866611091 1000000000 0 1 0 1 0

noncomputable def ep1579 := @ep1578 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep813) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 111147142449 2000000 0 1 Bool.true 1371839866611091 1000000000 0 1 EMRow34.d20)

noncomputable def ep1580 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)))) 1371839866611091 720000000000 0 1 0 1 0 1 1371839866611091

noncomputable def ep1581 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 1371839866611091 1000000000 0 1 1371839866611091 720000000000 0

noncomputable def ep1582 := @ep1581 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep813) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 111147142449 2000000 0 1 Bool.true 1371839866611091 1000000000 0 1 EMRow34.d20)

noncomputable def ep1583 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 111147142449 2000000 0 1 0 1 0

noncomputable def ep1584 := @ep1583 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep813) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 111147142449 2000000 0 1 Bool.true 1371839866611091 1000000000 0 1 EMRow34.d20)

noncomputable def ep1585 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 37049047483 480000000 0 1 Bool.false 1371839866611091 720000000000 0 1 (@ep1575 37049047483 480000000 0 1 (ep1577 rfl) (ep1579 rfl) rfl rfl) (@ep1580 1371839866611091 720000000000 0 1 (ep1582 rfl) (ep1584 rfl) rfl rfl)

noncomputable def ep1586 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 37049047483 480000000 0 1 Bool.false 1371839866611091 720000000000 0 1 ep1585

noncomputable def ep1587 := @ep1574 1505280000000 0 1 ep1586 qz920

noncomputable def ep1588 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.im qz50) 1371839866611091 720000000000 0 1 0 1 0 1 0

noncomputable def ep1589 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 37049047483 480000000 0 1 Bool.false 1371839866611091 720000000000 0 1 ep1585

noncomputable def ep1590 := @ep1588 1 0 1 ep1589 qz921

noncomputable def ep1591 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.im qz50)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.re qz50)) 0 1 0 1 1371839866611091 15805440000000000 0

noncomputable def ep1592 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.im qz50) 37049047483 480000000 0 1 0 1 0 1 0

noncomputable def ep1593 := @ep1592 1 0 1 ep1586 qz921

noncomputable def ep1594 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.re qz50) 1371839866611091 720000000000 0 1 1 21952 0 1 1371839866611091

noncomputable def ep1595 := @ep1594 15805440000000000 0 1 ep1589 qz920

noncomputable def ep1596 := @ep1542 1 (@ep1543 Bool.false 111131 336000 0 1 (BSN.bern_sum_succ qz64 28 0 1 1 rfl rfl) (ep1571 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1572 (@ep1573 1 5292721069 5292721069 1505280000000 0 1 (ep1587 rfl) (ep1590 rfl) rfl rfl) (@ep1591 1 1371839866611091 1371839866611091 15805440000000000 0 1 (ep1593 rfl) (ep1595 rfl) rfl rfl)) rfl rfl rfl rfl

noncomputable def ep1597 := ep1536 (ep1539 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep1540 Bool.false 6599442106611091 15805440000000000 0 1 (BSN.bern_sum_succ qz64 28 1 2 3 rfl rfl) (ep1596 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep1598 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz78) (Complex.im (@HAdd.hAdd Complex Complex Complex qz13 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))))) 80321606953 1099511627776 11682863189383 75137326107328512 ep1533

noncomputable def ep1599 := @ep1598 ep1534 0 1 ep1515 ep1260 ep1516 ep1262 (@Enclosure.Complex.IsNear.im_isNear qz78 Bool.false 95818349879 549755813888 5860625237039 37568663053664256 Bool.false 80321606953 1099511627776 11682863189383 75137326107328512 (ep1519 ep1530))

noncomputable def ep1600 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz13 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1))))) Bool.false 3122441535956537057703 6196911195023360000000 0 1 Bool.false

noncomputable def ep1601 := nat_lit 442463575549644766064810625091906747

noncomputable def ep1602 := nat_lit 189439626170556236456306019897277928389

noncomputable def ep1603 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re qz78) (Complex.im (@HAdd.hAdd Complex Complex Complex qz13 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 (Complex.im qz78) (Complex.re (@HAdd.hAdd Complex Complex Complex qz13 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1))))))) ep1601 ep1456 ep1602

noncomputable def ep1604 := nat_lit 35828503112117512348542778144137

noncomputable def ep1605 := nat_lit 973367987889064563420692480000000

noncomputable def ep1606 := nat_lit 12159685760475713934541367095989083

noncomputable def ep1607 := nat_lit 155206445772875011831119678013440000000

noncomputable def ep1608 := nat_lit 979950388484231674912955504986796940116055097049246262162882560000000

noncomputable def ep1609 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz78) (Complex.im (@HAdd.hAdd Complex Complex Complex qz13 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))))) 95818349879 549755813888 5860625237039 37568663053664256 ep1533

noncomputable def ep1610 := @ep1609 ep1534 0 1 ep1601 ep1456 ep1602 ep1458 (@Enclosure.Complex.IsNear.re_isNear qz78 Bool.false 95818349879 549755813888 5860625237039 37568663053664256 Bool.false 80321606953 1099511627776 11682863189383 75137326107328512 (ep1519 ep1530))

noncomputable def ep1611 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz78) (Complex.re (@HAdd.hAdd Complex Complex Complex qz13 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))))) 80321606953 1099511627776 11682863189383 75137326107328512 3122441535956537057703

noncomputable def ep1612 := @ep1611 6196911195023360000000 0 1 ep1604 ep1605 ep1606 ep1607 (@Enclosure.Complex.IsNear.im_isNear qz78 Bool.false 95818349879 549755813888 5860625237039 37568663053664256 Bool.false 80321606953 1099511627776 11682863189383 75137326107328512 (ep1519 ep1530))

noncomputable abbrev qz975 := (ep1597 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep1613 := @ep1509 ep1463 ep1456 ep1464 ep1458 (@ep1513 ep1514 ep1515 ep1260 ep1516 ep1262 ep1517 ep1461 ep1260 ep1462 ep1262 (ep1531 (@ep1532 ep1533 ep1534 0 1 qz975) rfl) (ep1599 (@ep1600 ep1533 ep1534 0 1 qz975) rfl) rfl rfl) (@ep1603 ep1458 ep1604 ep1605 ep1606 ep1607 ep1608 ep1463 ep1456 ep1464 ep1458 (ep1610 (@ep1600 ep1533 ep1534 0 1 qz975) rfl) (ep1612 (@ep1532 ep1533 ep1534 0 1 qz975) rfl) rfl rfl)

noncomputable def ep1614 := @ep1467 ep1457 ep1458 (@ep1468 75137326107328512 (BSN.head_sum_c_eq qz64 28) (ep1469 (BSN.head_sum_c_succ qz64 27 28 rfl rfl) (ep1508 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep1613 rfl rfl rfl

noncomputable def ep1615 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz64 2 28) Bool.false ep1259 ep1260 ep1261 ep1262 Bool.true ep1455 ep1456 ep1457 ep1458 (@ep1459 ep1262 Bool.true ep1455 ep1456 ep1457 ep1458 (BSN.zetaApproximant_eq_folded' qz64 2 28 rfl) (ep1614 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep1616 := @Enclosure.Real.IsNear.mulLit_ft (Real.sin (@HSub.hSub Real Real Real qz347 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz404)) (Complex.im (zetaApproximant qz64 2 28)) 187 1048576 25057271

noncomputable def ep1617 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz347 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz404)) Bool.false 187 1048576 50114542

noncomputable def ep1618 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz347 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz404) qz629 Bool.false 6794273 65536 359

noncomputable def ep1619 := nat_lit 4640876058366692063992377651969191539915872646853624613813308060250784447190625

noncomputable def ep1620 := nat_lit 13889129168330515138724335936435842476842026072026060274183865207821130840790625

noncomputable def ep1621 := BSN.cos_dyadic_bound_f 3372874965 2147483648 3 2 1048576 273615 ep1619 ep138 ep1451 ep1620 ep140 ep1451 187 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3372874965) qz266 0 2 ep1619 ep138 ep1451 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3372874965) qz267 0 2 ep1620 ep140 ep1451 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1622 := @ep1618 1048576 Bool.false 187 1048576 1 136674 (@ep1269 6794273 65536 359 1048576 ep1449 rfl) (Enclosure.sfrac_false_div 6794273 65536) (BSN.sin_reduce1 qz629 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14834060974482947833856) qz583) 226375608064910080 72057594037927936 Bool.false 187 1048576 16 1000000000000000 273348 136674 (BSN.sin_reduce_arg_pos_rat_q1 6794273 65536 226375608064910080 72057594037927936 16 14834060974482947833856 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 187 1048576 14834060974482947833856 9444732965739290427392 3372874965 2147483648 273615 273348 (ep1621 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1623 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz64 2 28) Bool.false ep1259 ep1260 ep1261 ep1262 Bool.true ep1455 ep1456 ep1457 ep1458 (@ep1459 ep1262 Bool.true ep1455 ep1456 ep1457 ep1458 (BSN.zetaApproximant_eq_folded' qz64 2 28 rfl) (ep1614 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow34.d21 : Enclosure.Real.IsNear (hardyZApproximantEM 2 28 qz61) Bool.true ep1243 ep1244 ep1245 ep1246 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 2 28 qz61) ep1247 Bool.true ep1243 ep1244 ep1245 ep1246 (@Eq.refl Real ep1247) (@ep1248 Bool.true ep1243 ep1244 ep1245 ep1246 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz347 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz404) (zetaApproximant qz64 2 28)) (@ep1250 ep1251 ep1252 ep1246 ep1253 ep1254 ep1255 ep1256 ep1257 ep1243 ep1244 ep1245 ep1246 (@ep1258 71656538112 ep1259 ep1260 ep1261 ep1262 ep1249 ep1251 ep1252 ep1246 (@ep1263 143313076224 1048575 1048576 25057271 71656538112 (ep1454 rfl rfl) rfl) ep1615 rfl) (@ep1616 71656538112 ep1455 ep1456 ep1457 ep1458 ep1253 ep1254 ep1255 ep1256 (@ep1617 143313076224 187 1048576 25057271 71656538112 (ep1622 rfl rfl) rfl) ep1623 rfl) rfl rfl))

theorem EMRow34.d22 : @Eq Nat (Nat.mul (BSN.factNat (Nat.succ (Nat.mul 2 2))) (Nat.pow 4 (Nat.mul 2 2))) 30720 := @Eq.refl Nat 30720

theorem EMRow34.d23 : @Eq Nat (Nat.mul (Nat.mul 2 2) (Nat.pow (Nat.succ (Nat.mul 4 4)) (Nat.mul 2 2))) 334084 := @Eq.refl Nat 334084

theorem EMRow34.d177 : @Eq Nat (TangentNumbers.tangentNumber 3) 16 := Height20.tangent_three

noncomputable abbrev qz232 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 3)

theorem EMRow34.d178 : @Eq Real (@Rat.cast Real Real.instRatCast (bernoulli qz232)) (Enclosure.sfrac Bool.false 1 42) := BSN.bern_real_tangent_pos 2 16 1 42 EMRow34.d177 rfl rfl rfl

theorem EMRow34.d179 : @Eq Nat (BSN.factNat (Nat.mul 2 3)) 720 := @Eq.refl Nat 720

theorem EMRow34.d180 : @Eq Nat (Nat.pow 28 (Nat.succ (Nat.mul 2 5))) 8293509467471872 := @Eq.refl Nat 8293509467471872

noncomputable def ep1757 := nat_lit 1181671153346359170692730265957638242378174781758650

noncomputable def ep1758 := nat_lit 5986310706507378352962293074805895248510699696029696

noncomputable def ep1759 := nat_lit 2000000000000000000000000000000000000000000000000000

noncomputable def ep1760 := nat_lit 1499028120395240233173640088155429295548437777754679499662777369540625

noncomputable def ep1761 := nat_lit 4680297997409431328241185462095581837349556053595733828842639923095703125

noncomputable def ep1762 := nat_lit 13442882392639581675476766202062253719655739830178303899086159055189875

noncomputable def ep1763 := nat_lit 19584239746202378791298717228947477708711488730841665528714656829833984375

noncomputable def ep1764 := nat_lit 2442358029135994033939875

noncomputable def ep1765 := nat_lit 37260822860694382775919147000

noncomputable def ep1766 := nat_lit 116336546489037573337554931640625

noncomputable def ep1767 := nat_lit 57493278893883548332405996866302358825

noncomputable def ep1768 := nat_lit 40230676762013536063022911548614501953125

noncomputable def ep1769 := nat_lit 236310350532676991248348623960

noncomputable def ep1770 := nat_lit 344268321641720831394195556640625

noncomputable def ep1771 := nat_lit 81801971833623620377505564448994707675

noncomputable def ep1772 := nat_lit 56886557708273976459167897701263427734375

noncomputable def ep1773 := BSN.arctan_dyadic_bound_f 1 5 18 17 ep1758 ep1759 ep1760 ep1761 200200021673987500790625 ep1762 ep1763 ep1764 ep1757 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 17 8 ep1765 ep1766 151412625 ep1767 ep1768 1322214852783825 ep1760 ep1761 200200021673987500790625 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 8 ep1765 ep1766 151412625 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 8 17 ep1767 ep1768 1322214852783825 rfl rfl rfl rfl)) (@BSN.binarySplit_rec (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 17 8 ep1769 ep1770 1267389585 ep1771 ep1772 1927077560082675 ep1762 ep1763 ep1764 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 8 ep1769 ep1770 1267389585 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 8 17 ep1771 ep1772 1927077560082675 rfl rfl rfl rfl)) rfl

theorem EMRow34.d181 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz265 qz283)) Bool.false ep1757 ep1758 1 ep1759 := ep1773 rfl rfl rfl

noncomputable def ep1774 := nat_lit 25047178968060507272880539293402373975644382030403

noncomputable def ep1775 := nat_lit 4733915408010924740926662591654183582145509

noncomputable def ep1776 := nat_lit 77229300481955664312677298336960122659119574530232845

noncomputable def ep1777 := nat_lit 24516194103503660983641551147684725335332607

noncomputable def ep1778 := nat_lit 186647183216068817672719845704257068688983305564016735

noncomputable def ep1779 := BSN.arctan_dyadic_bound_f 1 239 6 5 ep1758 ep1759 ep1775 ep1776 9945 ep1777 ep1778 65835 ep1774 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 239) 0 5 ep1775 ep1776 9945 rfl rfl rfl rfl) (@BSN.binarySplit_of_base5 (BSN.arctanOddP 1) (BSN.arctanOddQ 239) 0 5 ep1777 ep1778 65835 rfl rfl rfl rfl) rfl rfl rfl

theorem EMRow34.d182 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz265 (@Nat.cast Real Real.instNatCast 239))) Bool.false ep1774 ep1758 1 ep1759 := ep1779 rfl

noncomputable def ep1780 := nat_lit 18806549737669504701992162098148602382148218980016788

noncomputable def ep1781 := nat_lit 100000000000000000000000000000000000000000000000000

theorem EMRow34.d183 : Enclosure.Real.IsNear Real.pi Bool.false ep1780 ep1758 1 ep1781 := BSN.pi_combine ep1757 ep1774 ep1758 ep1759 ep1781 ep1780 rfl rfl rfl rfl EMRow34.d181 EMRow34.d182

noncomputable def ep1782 := nat_lit 15046017163518321799789907

noncomputable def ep1783 := nat_lit 135580765036666000525754368

noncomputable abbrev qz534 := (@HAdd.hAdd Complex Complex Complex qz547 (@HAdd.hAdd Complex Complex Complex qz547 qz548 (@HMul.hMul Complex Complex Complex qz543 Complex.I ↑(Enclosure.sfrac Bool.false 108936 1000))) (@Nat.cast Complex Complex.instNatCast 5))

noncomputable abbrev qz233 := (@Norm.norm Complex Complex.instNorm qz534)

noncomputable abbrev qz234 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 3)))

noncomputable abbrev qz235 := (@HPow.hPow Complex Complex Complex (@instHPow Complex Complex Complex.instPow) qz608 (@HSub.hSub Complex Complex Complex qz593 (@Neg.neg Complex Complex.instNeg qz259) (@Nat.cast Complex Complex.instNatCast 5)))

noncomputable abbrev qz788 := (@HDiv.hDiv Real Real Real qz1 qz233 (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (Complex.re qz12) qz283))

noncomputable def ep1784 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 2 4) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz12 2 28))) (@HMul.hMul Real Real Real qz0 qz788 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235))) 54993027345 179359981764608 151623915 179359981764608 179648796719654643347 1623313478486440542208 61529601274993

noncomputable def ep1785 := nat_lit 32311075826182938213450755117940736

noncomputable def ep1786 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 2 4) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz12 2 28)) 10095 171051008 15 171051008 5447551 1048576 6915 1048576 54993027345 179359981764608

noncomputable abbrev qz535 := (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid)))

noncomputable abbrev qz536 := (@HMul.hMul Real Real Real qz0 (2 : Real) Real.pi)

noncomputable abbrev qz1096 := (@Inv.inv Real Real.instInv (@HPow.hPow Real Nat Real qz535 qz536 4))

noncomputable def ep1787 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 30720 334084) qz1096 30720 334084 0 1 673 1048576 1 1048576 10095 171051008 15 171051008

noncomputable def ep1788 := nat_lit 611446774371975769155682509262542103857872115376664175900625

noncomputable def ep1789 := nat_lit 392318858461667547739736838950479151006397215279002157056

noncomputable def ep1790 := nat_lit 19652562622312316682495810535216024035134795670488584765154486969712234385047

noncomputable def ep1791 := nat_lit 9903520314283042199192993792000000000000000000000000000000000000000000000000000000000000

noncomputable def ep1792 := nat_lit 691463075802508163054686763366652189853178875

noncomputable def ep1793 := nat_lit 2787593149816327892691964784081045188247552

noncomputable def ep1794 := nat_lit 2184744797947834540264818678394244808492865883128339

noncomputable def ep1795 := nat_lit 9223372036854775808000000000000000000000000000000000000000000000

noncomputable def ep1796 := @Enclosure.Real.IsNear.mulLit_ff (@HPow.hPow Real Nat Real qz535 qz536 3) qz536 ep1792 ep1793 ep1794 ep1795 884279719003555 140737488355328 1 500000000000000 ep1788 ep1789 ep1790 ep1791

noncomputable def ep1797 := nat_lit 781950621441006189802102638025

noncomputable def ep1798 := nat_lit 19807040628566084398385987584

noncomputable def ep1799 := nat_lit 26986075409044041160201671

noncomputable def ep1800 := nat_lit 1073741824000000000000000000000000000000

noncomputable def ep1801 := @Enclosure.Real.IsNear.mulLit_ff (@HPow.hPow Real Nat Real qz535 qz536 2) qz536 ep1797 ep1798 ep1799 ep1800 884279719003555 140737488355328 1 500000000000000 ep1792 ep1793 ep1794 ep1795

noncomputable def ep1802 := @Enclosure.Real.IsNear.mulLit_ff (@HPow.hPow Real Nat Real qz535 qz536 1) qz536 884279719003555 140737488355328 1 500000000000000 884279719003555 140737488355328 1 500000000000000 ep1797 ep1798 ep1799 ep1800

noncomputable abbrev qz537 := (@Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 (2 : Real) Real.pi) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 2 1) Real.pi) Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 2 1) Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) BSN.pi_near_15 rfl))

noncomputable def ep1803 := ep1802 (@Enclosure.Real.IsNear.of_eq (@HPow.hPow Real Nat Real qz535 qz536 1) qz536 Bool.false 884279719003555 140737488355328 1 500000000000000 (BSN.pow_one_r qz536) qz537) qz537 rfl

noncomputable def ep1804 := @Enclosure.Real.IsNear.of_eq (@HPow.hPow Real Nat Real qz535 qz536 3) (@HMul.hMul Real Real Real qz0 (@HPow.hPow Real Nat Real qz535 qz536 2) qz536) Bool.false ep1792 ep1793 ep1794 ep1795 (BSN.pow_succ_r qz536 2 3 rfl) (ep1801 (@Enclosure.Real.IsNear.of_eq (@HPow.hPow Real Nat Real qz535 qz536 2) (@HMul.hMul Real Real Real qz0 (@HPow.hPow Real Nat Real qz535 qz536 1) qz536) Bool.false ep1797 ep1798 ep1799 ep1800 (BSN.pow_succ_r qz536 1 2 rfl) ep1803) qz537 rfl)

noncomputable abbrev qz1097 := (@HPow.hPow Real Nat Real qz535 qz536 4)

noncomputable def ep1805 := @Enclosure.Real.IsNear.inv_image qz1097 ep1788 ep1789 ep1790 ep1791 336 337 524288 (@Enclosure.Real.IsNear.of_eq qz1097 (@HMul.hMul Real Real Real qz0 (@HPow.hPow Real Nat Real qz535 qz536 3) qz536) Bool.false ep1788 ep1789 ep1790 ep1791 (BSN.pow_succ_r qz536 3 4 rfl) (ep1796 ep1804 qz537 rfl))

noncomputable def ep1806 := ep1787 (Enclosure.Real.IsNear.const Bool.false 30720 334084) (@Enclosure.Real.IsNear.recentre' qz1096 Bool.false 673 1048576 1 1048576 673 1048576 1 1048576 (ep1805 rfl rfl rfl rfl rfl rfl) rfl)

noncomputable def ep1807 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz12 2 28)) (Real.sqrt (@HAdd.hAdd Real Real Real qz604 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz12 2 28)) (Complex.re (zetaApproximant qz12 2 28))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz12 2 28)) (Complex.im (zetaApproximant qz12 2 28))))) Bool.false 5447551 1048576 6915 1048576

noncomputable def ep1808 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz604 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz12 2 28)) (Complex.re (zetaApproximant qz12 2 28))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz12 2 28)) (Complex.im (zetaApproximant qz12 2 28))))) Bool.false 5447551 1048576 6915 1048576

noncomputable def ep1809 := nat_lit 14875354299216549864947919711282203877934571415043511472293

noncomputable def ep1810 := nat_lit 551142362866622677250004794593547124736000000000000000000

noncomputable def ep1811 := nat_lit 492938947771203878983309128809724307010870292315359782200406975934491680779

noncomputable def ep1812 := nat_lit 7195489693986190301272316235396968375095954325358029832192000000000000000000

noncomputable def ep1813 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz604 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz12 2 28)) (Complex.re (zetaApproximant qz12 2 28))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz12 2 28)) (Complex.im (zetaApproximant qz12 2 28)))) ep1809 ep1810 ep1811 ep1812 2720318 2727233

noncomputable def ep1814 := nat_lit 1077455571755138619560485046576675566995274576997155894380499630849

noncomputable def ep1815 := nat_lit 39920489001717919105042196135803535531337318400000000000000000000

noncomputable def ep1816 := nat_lit 2501334135231118581057140366213170070003411408459342663052746671795711536349

noncomputable def ep1817 := nat_lit 36539596102273622623648480882875230029784143058458745241600000000000000000000

noncomputable def ep1818 := nat_lit 3714801971783429835139713262549385126264677387329752664543481

noncomputable def ep1819 := nat_lit 10219645184439787290890802210765705096022353510400000000000000000000

noncomputable def ep1820 := nat_lit 119773370849671481918483425517515298314514861093998779756480183784257926839

noncomputable def ep1821 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz12 2 28)) (Complex.re (zetaApproximant qz12 2 28))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz12 2 28)) (Complex.im (zetaApproximant qz12 2 28))) ep1814 ep1815 ep1816 ep1817 ep1818 ep1819 ep1820

noncomputable def ep1822 := nat_lit 2338534150545511847913502776504014721906185155741359695462400000000000000000000

noncomputable def ep1823 := nat_lit 11011213793631931345741562360085401223339594454124411209606044820518236968010622922917117101571452225682334023680000000000000000000000

noncomputable def ep1824 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz12 2 28)) (Complex.re (zetaApproximant qz12 2 28)) ep474 ep475 ep476 ep477 ep474 ep475 ep476 ep477 ep1814

noncomputable def ep1825 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (zetaApproximant qz12 2 28)) (Complex.im (zetaApproximant qz12 2 28)) ep683 ep684 ep685 ep686 ep683 ep684 ep685 ep686 ep1818

noncomputable def ep1826 := @ep1784 1623313478486440542208 ep1785 ep1782 ep1783 119753690922189846193 ep1783 (@ep1786 151623915 179359981764608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 2 4) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 30720 334084) qz1096) Bool.false 10095 171051008 15 171051008 (BSN.theta_err_eq 2 4 30720 334084 EMRow34.d22 EMRow34.d23 rfl) (ep1806 rfl)) (ep1807 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz12 2 28)) (@ep1808 5447551 1048576 6915 1048576 (@ep1813 524288 (@ep1821 ep1822 ep1823 ep1809 ep1810 ep1811 ep1812 (@ep1824 ep1815 ep1816 ep1817 ep854 ep854 rfl) (@ep1825 ep1819 ep1820 ep1822 ep862 ep862 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable def ep1827 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz788 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz233 (Enclosure.sfrac Bool.false 2 11)) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235))) Bool.false 179648796719654643347 1623313478486440542208 61529601274993 1623313478486440542208 (BSN.zrb_shape_eq qz233 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235)) qz9 5)

noncomputable def ep1828 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz233 (Enclosure.sfrac Bool.false 2 11)) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235)) 114373169 5767168 1 5767168 1570725007363 281474976710656 524239 281474976710656

noncomputable def ep1829 := @Enclosure.Real.IsNear.mulLit_ff qz233 (Enclosure.sfrac Bool.false 2 11) 114373169 1048576 1 1048576 2 11 0 1 114373169 5767168

noncomputable abbrev qz236 := (Complex.re qz534)

noncomputable abbrev qz237 := (Complex.im qz534)

noncomputable abbrev qz238 := qz534

noncomputable abbrev qz1098 := (@HAdd.hAdd Real Real Real qz604 (@HMul.hMul Real Real Real qz0 qz236 qz236) (@HMul.hMul Real Real Real qz0 qz237 qz237))

noncomputable def ep1830 := @Enclosure.Real.IsNear.of_eq qz233 (Real.sqrt qz1098) Bool.false 114373169 1048576 1 1048576 (BSN.norm_eq_sqrt_mul_add qz238)

noncomputable def ep1831 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz1098) Bool.false 114373169 1048576 1 1048576 114373169

noncomputable def ep1832 := @Enclosure.Real.IsNear.sqrt_image qz1098 743581381 62500 0 1 57186584 57186585 524288

noncomputable def ep1833 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz236 qz236) (@HMul.hMul Real Real Real qz0 qz237 qz237) 121 4 0 1 185422689 15625 0 1

noncomputable def ep1834 := @Enclosure.Real.IsNear.mulLit_ff qz236 qz236 11 2 0 1 11 2 0 1 121 4

noncomputable def ep1835 := @Enclosure.Complex.IsNear.of_eq qz238 (Complex.mk (Enclosure.sfrac Bool.false 11 2) qz9) Bool.false 11 2 0 1 Bool.false 108936 1000 0 1 (BSN.s_add_nat_mk qz9 Bool.false 108936 1000 5 (@Eq.refl Real qz9))

noncomputable abbrev qz789 := (ep1835 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 11 2) qz9 Bool.false 11 2 0 1 Bool.false 108936 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 11 2) qz270))

noncomputable def ep1836 := @ep1834 0 1 (@Enclosure.Complex.IsNear.re_isNear qz238 Bool.false 11 2 0 1 Bool.false 108936 1000 0 1 qz789)

noncomputable def ep1837 := ep1836 (@Enclosure.Complex.IsNear.re_isNear qz238 Bool.false 11 2 0 1 Bool.false 108936 1000 0 1 qz789)

noncomputable def ep1838 := @Enclosure.Real.IsNear.mulLit_ff qz237 qz237 108936 1000 0 1 108936 1000 0 1 185422689 15625

noncomputable def ep1839 := @ep1838 0 1 (@Enclosure.Complex.IsNear.im_isNear qz238 Bool.false 11 2 0 1 Bool.false 108936 1000 0 1 qz789)

noncomputable def ep1840 := ep1839 (@Enclosure.Complex.IsNear.im_isNear qz238 Bool.false 11 2 0 1 Bool.false 108936 1000 0 1 qz789)

noncomputable def ep1841 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235)) (Real.sqrt (@HAdd.hAdd Real Real Real qz604 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235)) (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235)) (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235))))) Bool.false 1570725007363 281474976710656

noncomputable def ep1842 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz604 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235)) (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235)) (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235))))) Bool.false 1570725007363 281474976710656

noncomputable def ep1843 := nat_lit 11691925420338898061975564920870803497945933393304359506227676435316036769837358177

noncomputable def ep1844 := nat_lit 375461407512142770297795021651825749986591084934982533120000000000000000000000000000000

noncomputable def ep1845 := nat_lit 138399813347005770721897632793232881880436395619703528618818595079144265499072990144192939789

noncomputable def ep1846 := nat_lit 6658188250491663168309564010305152823487244951299649784843197488996286464000000000000000000000000000000

noncomputable def ep1847 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz604 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235)) (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235)) (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235)))) ep1843 ep1844 ep1845 ep1846

noncomputable def ep1848 := nat_lit 54660072718702565161136398320662721922057704704216147177464561553799130821833625121

noncomputable def ep1849 := nat_lit 1877307037560713851488975108259128749932955424674912665600000000000000000000000000000000

noncomputable def ep1850 := nat_lit 81049772651878355065101825168101559406043428746420246876585197074717071339904334269095459977

noncomputable def ep1851 := nat_lit 4161367656557289480193477506440720514679528094562281115526998430622679040000000000000000000000000000000

noncomputable def ep1852 := nat_lit 949888595747981287185356570922823891917990565576412588418455155695263256838291441

noncomputable def ep1853 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235)) (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235)) (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235))) ep1848 ep1849 ep1850 ep1851 ep1852

noncomputable def ep1854 := nat_lit 469326759390178462872243777064782187483238856168728166400000000000000000000000000000000

noncomputable def ep1855 := nat_lit 43600885520002013088673562621351934153834548127155668081411398797984756776130276568201019129

noncomputable def ep1856 := nat_lit 33290941252458315841547820051525764117436224756498248924215987444981432320000000000000000000000000000000

noncomputable def ep1857 := nat_lit 27436667342796525987915584879494669180196687393453557880096488481209698736906020153907460511189497484416395294909482296026808917126283264000000000000000000000000000000000

noncomputable def ep1858 := nat_lit 233794937324790172970357655483676871343761

noncomputable def ep1859 := nat_lit 43327901374988309621469347840000000000000000

noncomputable def ep1860 := nat_lit 11642231761835236677905477639232819075872011

noncomputable def ep1861 := nat_lit 6450866342249922542719480963247636480000000000000000

noncomputable def ep1862 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235)) (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235)) ep1858 ep1859 ep1860 ep1861 ep1858 ep1859 ep1860

noncomputable def ep1863 := nat_lit 30820262746251552473726164324565913279271

noncomputable def ep1864 := nat_lit 21663950687494154810734673920000000000000000

noncomputable def ep1865 := nat_lit 5938660938943037491230178500921325410563159

noncomputable def ep1866 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235) Bool.true ep1858 ep1859 ep1860 ep1861 Bool.false ep1863 ep1864 ep1865

noncomputable def ep1867 := nat_lit 12901732684499845085438961926495272960000000000000000

noncomputable def ep1868 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235 Bool.true ep1858 ep1859 ep1860 ep1861 Bool.false ep1863 ep1864 ep1865 ep1867

noncomputable def ep1869 := nat_lit 1262721686055469584561516292022081763

noncomputable def ep1870 := nat_lit 13864928439996259078870191308800000000000

noncomputable def ep1871 := nat_lit 1900891853718380017244690369156198259

noncomputable def ep1872 := nat_lit 64508663422499225427194809632476364800000000000

noncomputable def ep1873 := nat_lit 2122686987443870673411717802645052471903

noncomputable def ep1874 := nat_lit 386856262276681335905976320000000000000000

noncomputable def ep1875 := nat_lit 11452142576463398676181008602317199249972011

noncomputable def ep1876 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.re qz235)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.im qz235)) ep1869 ep1870 ep1871 ep1872 ep1873 ep1874 ep1875

noncomputable def ep1877 := nat_lit 28942411389657376587751344002548017180942138480744457398422094636646400000000000

noncomputable def ep1878 := nat_lit 39614081257132168796771975168

noncomputable def ep1879 := nat_lit 184310466921426358363413741807075328

noncomputable def ep1880 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.re qz235) 20357955847333043 350000000000 0 1 62025956610024289041 ep1878 93373414697104910913 ep1879 ep1869

noncomputable def ep1881 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5)))) 20357955847333043 350000000000 0 1 0 1 0 1 20357955847333043

noncomputable def ep1882 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) 1 30240 0 1 549664807877992161 312500000 0 1 20357955847333043 350000000000 0

noncomputable def ep1883 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (Complex.mk (Enclosure.sfrac Bool.false 1 30240) qz262) Bool.false 1 30240 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 3 1 42 720 Bool.false EMRow34.d178 EMRow34.d179 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 30240) qz262 Bool.false 1 30240 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 30240) qz274)

noncomputable abbrev qz239 := (@HAdd.hAdd Complex Complex Complex qz260 qz259 qz261)

noncomputable def ep1884 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5)) (@HMul.hMul Complex Complex Complex qz3 (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 4)) qz239) Bool.false 549664807877992161 312500000 0 1 Bool.false 7454492369154388256337 488281250000 0 1

noncomputable def ep1885 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.re qz239)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.im qz239)) 4941977005955179449 7812500000 0 1 274988849718582018 244140625 0 1

noncomputable def ep1886 := nat_lit 3354887743395948248291015625

noncomputable def ep1887 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.re qz239) 549108556217242161 3906250000 0 1 9 2 0 1 4941977005955179449 7812500000

noncomputable abbrev qz240 := (@HAdd.hAdd Complex Complex Complex qz260 qz259 qz550)

noncomputable def ep1888 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 4)) (@HMul.hMul Complex Complex Complex qz3 (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)) qz240) Bool.false 549108556217242161 3906250000 0 1 Bool.true 20194525205154 1953125 0 1

noncomputable def ep1889 := @Enclosure.Real.IsNear.subLit_tt_p (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.re qz240)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.im qz240)) 46724877003 250000 0 1 137459658105103509 976562500 0 1

noncomputable def ep1890 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.re qz240) 6674982429 125000 0 1 7 2 0 1 46724877003 250000

noncomputable abbrev qz790 := (ep423 (BSN.ascPochhammer_succ_eval_c 2 3 qz12 rfl) (ep451 (@ep452 252367735376925 10094709415077 7812500 0 1 (ep455 rfl) (ep458 rfl) rfl rfl)))

noncomputable def ep1891 := @ep1890 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 6674982429 125000 0 1 Bool.true 10094709415077 7812500 0 1 qz790)

noncomputable def ep1892 := @Enclosure.Complex.IsNear.of_eq qz240 (Complex.mk (Enclosure.sfrac Bool.false 7 2) qz9) Bool.false 7 2 0 1 Bool.false 108936 1000 0 1 (BSN.s_add_nat_mk qz9 Bool.false 108936 1000 3 (@Eq.refl Real qz9))

noncomputable abbrev qz791 := (ep1892 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz9 Bool.false 7 2 0 1 Bool.false 108936 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz270))

noncomputable def ep1893 := ep1891 (@Enclosure.Complex.IsNear.re_isNear qz240 Bool.false 7 2 0 1 Bool.false 108936 1000 0 1 qz791)

noncomputable def ep1894 := @Enclosure.Real.IsNear.mulLit_tf (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.im qz240) 10094709415077 7812500 0 1 108936 1000 0 1 137459658105103509 976562500

noncomputable def ep1895 := @ep1894 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 6674982429 125000 0 1 Bool.true 10094709415077 7812500 0 1 qz790)

noncomputable def ep1896 := ep1895 (@Enclosure.Complex.IsNear.im_isNear qz240 Bool.false 7 2 0 1 Bool.false 108936 1000 0 1 qz791)

noncomputable def ep1897 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)) qz240 Bool.false 549108556217242161 3906250000 0 1 Bool.true 20194525205154 1953125 0 1 (@ep1889 34319284763577635062500 549108556217242161 3906250000 0 1 (ep1893 rfl) (ep1896 rfl) rfl rfl)

noncomputable def ep1898 := @Enclosure.Real.IsNear.addLit_tt (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.im qz240)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.re qz240)) 90893235735693 15625000 0 1 70662965905539 15625000 0 1

noncomputable def ep1899 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.im qz240) 6674982429 125000 0 1 108936 1000 0 1 90893235735693 15625000

noncomputable def ep1900 := @ep1899 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 6674982429 125000 0 1 Bool.true 10094709415077 7812500 0 1 qz790)

noncomputable def ep1901 := ep1900 (@Enclosure.Complex.IsNear.im_isNear qz240 Bool.false 7 2 0 1 Bool.false 108936 1000 0 1 qz791)

noncomputable def ep1902 := @Enclosure.Real.IsNear.mulLit_tf (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.re qz240) 10094709415077 7812500 0 1 7 2 0 1 70662965905539 15625000

noncomputable def ep1903 := @ep1902 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 6674982429 125000 0 1 Bool.true 10094709415077 7812500 0 1 qz790)

noncomputable def ep1904 := ep1903 (@Enclosure.Complex.IsNear.re_isNear qz240 Bool.false 7 2 0 1 Bool.false 108936 1000 0 1 qz791)

noncomputable abbrev qz792 := (ep1888 (BSN.ascPochhammer_succ_eval_c 3 4 qz12 rfl) (ep1897 (@ep1898 2524315650644250000000 20194525205154 1953125 0 1 (ep1901 rfl) (ep1904 rfl) rfl rfl)))

noncomputable def ep1905 := @ep1887 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 4)) Bool.false 549108556217242161 3906250000 0 1 Bool.true 20194525205154 1953125 0 1 qz792)

noncomputable def ep1906 := @Enclosure.Complex.IsNear.of_eq qz239 (Complex.mk (Enclosure.sfrac Bool.false 9 2) qz9) Bool.false 9 2 0 1 Bool.false 108936 1000 0 1 (BSN.s_add_nat_mk qz9 Bool.false 108936 1000 4 (@Eq.refl Real qz9))

noncomputable abbrev qz793 := (ep1906 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9 2) qz9 Bool.false 9 2 0 1 Bool.false 108936 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 9 2) qz270))

noncomputable def ep1907 := ep1905 (@Enclosure.Complex.IsNear.re_isNear qz239 Bool.false 9 2 0 1 Bool.false 108936 1000 0 1 qz793)

noncomputable def ep1908 := @Enclosure.Real.IsNear.mulLit_tf (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.im qz239) 20194525205154 1953125 0 1 108936 1000 0 1 274988849718582018 244140625

noncomputable def ep1909 := @ep1908 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 4)) Bool.false 549108556217242161 3906250000 0 1 Bool.true 20194525205154 1953125 0 1 qz792)

noncomputable def ep1910 := ep1909 (@Enclosure.Complex.IsNear.im_isNear qz239 Bool.false 9 2 0 1 Bool.false 108936 1000 0 1 qz793)

noncomputable def ep1911 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 4)) qz239 Bool.false 549664807877992161 312500000 0 1 Bool.false 7454492369154388256337 488281250000 0 1 (@ep1885 ep1886 549664807877992161 312500000 0 1 (ep1907 rfl) (ep1910 rfl) rfl rfl)

noncomputable def ep1912 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.im qz239)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.re qz239)) 7477211210010186506337 488281250000 0 1 90875363423193 1953125 0 1

noncomputable def ep1913 := nat_lit 14559555408504664563158203125

noncomputable def ep1914 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.im qz239) 549108556217242161 3906250000 0 1 108936 1000 0 1 7477211210010186506337 488281250000

noncomputable def ep1915 := @ep1914 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 4)) Bool.false 549108556217242161 3906250000 0 1 Bool.true 20194525205154 1953125 0 1 qz792)

noncomputable def ep1916 := ep1915 (@Enclosure.Complex.IsNear.im_isNear qz239 Bool.false 9 2 0 1 Bool.false 108936 1000 0 1 qz793)

noncomputable def ep1917 := @Enclosure.Real.IsNear.mulLit_tf (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.re qz239) 20194525205154 1953125 0 1 9 2 0 1 90875363423193 1953125

noncomputable def ep1918 := @ep1917 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 4)) Bool.false 549108556217242161 3906250000 0 1 Bool.true 20194525205154 1953125 0 1 qz792)

noncomputable def ep1919 := ep1918 (@Enclosure.Complex.IsNear.re_isNear qz239 Bool.false 9 2 0 1 Bool.false 108936 1000 0 1 qz793)

noncomputable abbrev qz794 := (ep1884 (BSN.ascPochhammer_succ_eval_c 4 5 qz12 rfl) (ep1911 (@ep1912 ep1913 7454492369154388256337 488281250000 0 1 (ep1916 rfl) (ep1919 rfl) rfl rfl)))

noncomputable def ep1920 := @ep1882 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) Bool.false 1 30240 0 1 Bool.false 0 1 0 1 ep1883) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5)) Bool.false 549664807877992161 312500000 0 1 Bool.false 7454492369154388256337 488281250000 0 1 qz794)

noncomputable def ep1921 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) 0 1 0 1 7454492369154388256337 488281250000 0 1 0 1 0

noncomputable def ep1922 := @ep1921 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) Bool.false 1 30240 0 1 Bool.false 0 1 0 1 ep1883) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5)) Bool.false 549664807877992161 312500000 0 1 Bool.false 7454492369154388256337 488281250000 0 1 qz794)

noncomputable def ep1923 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5)))) 276092309968681046531 546875000000000 0 1 0 1 0 1 276092309968681046531

noncomputable def ep1924 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) 1 30240 0 1 7454492369154388256337 488281250000 0 1 276092309968681046531 546875000000000 0

noncomputable def ep1925 := @ep1924 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) Bool.false 1 30240 0 1 Bool.false 0 1 0 1 ep1883) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5)) Bool.false 549664807877992161 312500000 0 1 Bool.false 7454492369154388256337 488281250000 0 1 qz794)

noncomputable def ep1926 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) 0 1 0 1 549664807877992161 312500000 0 1 0 1 0

noncomputable def ep1927 := @ep1926 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) Bool.false 1 30240 0 1 Bool.false 0 1 0 1 ep1883) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5)) Bool.false 549664807877992161 312500000 0 1 Bool.false 7454492369154388256337 488281250000 0 1 qz794)

noncomputable def ep1928 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5)) Bool.false 20357955847333043 350000000000 0 1 Bool.false 276092309968681046531 546875000000000 0 1 (@ep1881 20357955847333043 350000000000 0 1 (ep1920 rfl) (ep1922 rfl) rfl rfl) (@ep1923 276092309968681046531 546875000000000 0 1 (ep1925 rfl) (ep1927 rfl) rfl rfl)

noncomputable def ep1929 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) Bool.false 20357955847333043 350000000000 0 1 Bool.false 276092309968681046531 546875000000000 0 1 ep1928

noncomputable def ep1930 := nat_lit 4951760157141521099596496896

noncomputable def ep1931 := nat_lit 11795869882971286935258479475652820992

noncomputable def ep1932 := @Enclosure.Complex.IsNear.re_isNear qz235 Bool.false 62025956610024289041 ep1878 93373414697104910913 ep1879 Bool.false 53818264310920599091 ep1930 41479397154388291313081 ep1931

noncomputable abbrev qz538 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 8293509467471872)))

noncomputable def ep1933 := @Enclosure.Complex.IsNear.of_eq qz235 (Complex.mk (@HMul.hMul Real Real Real qz0 qz538 (Real.cos qz371)) (@HMul.hMul Real Real Real qz0 qz538 qz916)) Bool.false 62025956610024289041 ep1878 93373414697104910913 ep1879 Bool.false 53818264310920599091 ep1930 41479397154388291313081

noncomputable def ep1934 := nat_lit 2262996807475479579721728

noncomputable abbrev qz539 := (Real.sqrt (@Nat.cast Real Real.instNatCast 8293509467471872))

noncomputable def ep1935 := @Enclosure.Real.IsNear.inv_image qz539 25633562294430545220073 281474976710656 1 281474976710656 1545398 1545399 140737488355328 (@Enclosure.Real.IsNear.of_eq qz539 (Real.sqrt (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8293509467471872) qz265)) Bool.false 25633562294430545220073 281474976710656 1 281474976710656 (BSN.sqrt_natCast_div_one 8293509467471872) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8293509467471872) qz265)) Bool.false 25633562294430545220073 281474976710656 1 281474976710656 25633562294430545220073 281474976710656 1 281474976710656 (BSN.sqrt_enclosure 8293509467471872 1 12816781147215272610036 12816781147215272610037 140737488355328 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep1936 := nat_lit 18538469846839128717080395776

noncomputable def ep1937 := nat_lit 13957950890625000000000000

noncomputable def ep1938 := nat_lit 16896284189627229735777967538176

noncomputable def ep1939 := nat_lit 5070602400912917605986812821504

noncomputable def ep1940 := nat_lit 65861875408896000000000000000

noncomputable def ep1941 := nat_lit 21918609655457519559609792048813734163111991050240000

noncomputable def ep1942 := nat_lit 569057034653488104001530221467611848327147657625600

noncomputable def ep1943 := nat_lit 25139617364453040909348401707587993600

noncomputable def ep1944 := BSN.log_dyadic_bound 12 44 13 12 ep1941 140737488355328 65861875408896 ep1942 ep1943 78758920438019 56 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base12 (BSN.artanhP 12) (BSN.artanhQ 44) 0 12 ep1942 ep1941 ep1943 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1945 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz372 108936 1000 0 1 3751728747586831 1125899906842624 19278678919 1004972464125000000000000 51087290355889877727 140737488355328000 29168641204447 ep1937 qz270 (BSN.isNear_log_sfrac 28 1 3751728747586831 1125899906842624 19278678919 1004972464125000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz613) Bool.false ep1938 ep1939 1263447501635584 ep1940 3751728747586831 1125899906842624 19278678919 1004972464125000000000000 (BSN.log_rat_reduce_isNear 28 1 4 56 32 78758920438019 140737488355328 24973259072661432 36028797018963968 65861875408896 1000000000000000 rfl rfl rfl rfl (ep1944 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1946 := nat_lit 482175380027484022497232705158632647016346760706951550406431342592

noncomputable def ep1947 := nat_lit 3369993333393829974333376885877453834204643052817571560137951281152

noncomputable def ep1948 := nat_lit 15454101462166148909002942065344019444263943231322440324795176495920133738823435295313648372073209782244185064603216119167415946150607068012800

noncomputable def ep1949 := nat_lit 4425078570072918987983414073231813238398637867227596606342854990268964439777017766520533901092499869119054674864593887954297505525391144421666324480

noncomputable def ep1950 := nat_lit 2141735676103110366645825705962068295289809173427410654354647499205816862567838657677839373675163682375970682826580595689584844868362496

noncomputable def ep1951 := nat_lit 40475024171434533451876635601707003177342611327105824825322498057980589649405505425511252353213706336564998941436841450022267790114222057922816

noncomputable def ep1952 := nat_lit 81126440451336848113029258009249909370641694232505937782952341488264348062578659052876454853362497600516002372517554612495454267965504314397215948800

noncomputable def ep1953 := BSN.sin_dyadic_bound_f 82479445748016166 576460752303423488 3 2 281474976710656 131852387293201 ep1948 ep1949 ep1950 ep1951 ep1952 ep1950 40135898028906 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 82479445748016166) (BSN.sinEvenQ 576460752303423488) 0 2 ep1948 ep1949 ep1950 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 82479445748016166) (BSN.sinOddQ 576460752303423488) 0 2 ep1951 ep1952 ep1950 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz795 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 102174580711779755) (@Nat.cast Real Real.instNatCast 281474976710656))

noncomputable def ep1954 := @Enclosure.Real.IsNear.cos_image qz371 qz795 Bool.false 102174580711779755 281474976710656 589 281474976710656 Bool.false 40135898028906 281474976710656 1 65861875408896 (@Enclosure.Real.IsNear.recentre' qz371 Bool.false 51087290355889877727 140737488355328000 29168641204447 ep1937 102174580711779755 281474976710656 589 281474976710656 (ep1945 rfl) rfl) (Enclosure.sfrac_false_div 102174580711779755 281474976710656) (BSN.cos_reduce3 qz795 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1946) (@Nat.cast Real Real.instNatCast ep1947)) ep1780 ep1758 Bool.false 40135898028906 281474976710656 57 ep1781 131723750817792 65861875408896 (BSN.sin_reduce_arg_pos_rat_q3 102174580711779755 281474976710656 ep1780 ep1758 57 ep1946 ep1947 rfl rfl rfl rfl) EMRow34.d183 (@BSN.sin_arg_round Bool.false 40135898028906 281474976710656 ep1946 ep1947 82479445748016166 576460752303423488 131852387293201 131723750817792 (ep1953 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1955 := nat_lit 8585612875308160995272908545558102341065877479538766148179833322021185057487180749769208063524838179097294980766534655795495832121379423723776

noncomputable def ep1956 := nat_lit 491675396674768776442601563692423693155404207469732956260317221140996048864113085168948211232499985457672741651621543106033056169487904935740702720

noncomputable def ep1957 := nat_lit 25756834342453130779597992345022895099061041858997951589718191256768556760827817113630308834895767186964520190358238314225296117194448534446336

noncomputable def ep1958 := nat_lit 22125392850364594939917070366159066191993189336137983031714274951344822198885088832602669505462499345595273374322969439771487527626955722108331622400

noncomputable def ep1959 := BSN.cos_dyadic_bound_f 82479445748016166 576460752303423488 3 2 281474976710656 131852387293201 ep1955 ep1956 ep1950 ep1957 ep1958 ep1950 278598765617648 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 82479445748016166) (BSN.cosEvenQ 576460752303423488) 0 2 ep1955 ep1956 ep1950 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 82479445748016166) (BSN.cosOddQ 576460752303423488) 0 2 ep1957 ep1958 ep1950 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1960 := @Enclosure.Real.IsNear.sin_image qz371 qz795 Bool.false 102174580711779755 281474976710656 589 281474976710656 Bool.true 278598765617648 281474976710656 1 65861875408896 (@Enclosure.Real.IsNear.recentre' qz371 Bool.false 51087290355889877727 140737488355328000 29168641204447 ep1937 102174580711779755 281474976710656 589 281474976710656 (ep1945 rfl) rfl) (Enclosure.sfrac_false_div 102174580711779755 281474976710656) (BSN.sin_reduce3 qz795 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1946) (@Nat.cast Real Real.instNatCast ep1947)) ep1780 ep1758 Bool.false 278598765617648 281474976710656 57 ep1781 131723750817792 65861875408896 (BSN.sin_reduce_arg_pos_rat_q3 102174580711779755 281474976710656 ep1780 ep1758 57 ep1946 ep1947 rfl rfl rfl rfl) EMRow34.d183 (@BSN.cos_arg_round Bool.false 278598765617648 281474976710656 ep1946 ep1947 82479445748016166 576460752303423488 131852387293201 131723750817792 (ep1959 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz796 := (@Enclosure.Real.IsNear.recentre' qz538 Bool.false 3090797 281474976710656 1 281474976710656 3090797 281474976710656 1 281474976710656 (ep1935 rfl rfl) rfl)

noncomputable def ep1961 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz538 (Real.cos qz371)) (@HMul.hMul Real Real Real qz0 qz538 qz916) Bool.false 62025956610024289041 ep1878 93373414697104910913 ep1879 Bool.false 53818264310920599091 ep1930 41479397154388291313081 ep1931 (@Enclosure.Real.IsNear.mulLit_ff qz538 (Real.cos qz371) 3090797 281474976710656 1 281474976710656 20067949014453 140737488355328 4769789989325 ep1934 62025956610024289041 ep1878 93373414697104910913 ep1879 qz796 (@Enclosure.Real.IsNear.recentre' (Real.cos qz371) Bool.false 40135898028906 281474976710656 39074119592550400 ep1936 20067949014453 140737488355328 4769789989325 ep1934 (ep1954 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz538 qz916 3090797 281474976710656 1 281474976710656 17412422851103 17592186044416 4769789989325 ep1934 53818264310920599091 ep1930 41479397154388291313081 ep1931 qz796 (@Enclosure.Real.IsNear.neg (Real.sin qz371) Bool.true 17412422851103 17592186044416 4769789989325 ep1934 (@Enclosure.Real.IsNear.recentre' (Real.sin qz371) Bool.true 278598765617648 281474976710656 39074119592550400 ep1936 17412422851103 17592186044416 4769789989325 ep1934 (ep1960 rfl rfl) rfl)) rfl)

noncomputable def ep1962 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.im qz235) 276092309968681046531 546875000000000 0 1 53818264310920599091 ep1930 41479397154388291313081 ep1931 ep1873

noncomputable def ep1963 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) Bool.false 20357955847333043 350000000000 0 1 Bool.false 276092309968681046531 546875000000000 0 1 ep1928

noncomputable def ep1964 := @Enclosure.Complex.IsNear.im_isNear qz235 Bool.false 62025956610024289041 ep1878 93373414697104910913 ep1879 Bool.false 53818264310920599091 ep1930 41479397154388291313081 ep1931

noncomputable def ep1965 := nat_lit 156518549803117318916895466308580559

noncomputable def ep1966 := nat_lit 247588007857076054979824844800000000000

noncomputable def ep1967 := nat_lit 844435735843028699711965591238389435483

noncomputable def ep1968 := nat_lit 4128554459039950427340467816478487347200000000000

noncomputable def ep1969 := nat_lit 17124889638478787068497811022565114366771

noncomputable def ep1970 := nat_lit 25779681753387287536174109596104362692803

noncomputable def ep1971 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.im qz235)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.re qz235)) ep1965 ep1966 ep1967 ep1968 ep1969 ep1864 ep1970

noncomputable def ep1972 := nat_lit 100794786597655039729991890050744320000000000000000

noncomputable def ep1973 := nat_lit 7630727454976077805624723936470084389131864556217881482865966632140800000000000

noncomputable def ep1974 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.im qz235) 20357955847333043 350000000000 0 1 53818264310920599091 ep1930 41479397154388291313081 ep1931 ep1965

noncomputable def ep1975 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.re qz235) 276092309968681046531 546875000000000 0 1 62025956610024289041 ep1878 93373414697104910913 ep1879 ep1969

noncomputable abbrev qz797 := (@ep1933 ep1931 (BSN.cpow_neg_s_sub_mk qz9 108936 1000 28 5 8293509467471872 (@Eq.refl Real qz9) rfl EMRow34.d180) ep1961)

noncomputable def ep1976 := ep1868 (@ep1876 ep1861 ep1877 ep1858 ep1859 ep1860 ep1861 (@ep1880 ep1870 ep1871 ep1872 ep1929 (ep1932 qz797) rfl) (@ep1962 ep1874 ep1875 ep1861 ep1963 (ep1964 qz797) rfl) rfl rfl) (@ep1971 ep1972 ep1973 ep1863 ep1864 ep1865 ep1867 (@ep1974 ep1966 ep1967 ep1968 ep1929 (ep1964 qz797) rfl) (@ep1975 ep1864 ep1970 ep1972 ep1963 (ep1932 qz797) rfl) rfl rfl)

noncomputable def ep1977 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235)) (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235)) ep1863 ep1864 ep1865 ep1867 ep1863 ep1864 ep1865

noncomputable def ep1978 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235) Bool.true ep1858 ep1859 ep1860 ep1861 Bool.false ep1863 ep1864 ep1865

noncomputable def ep1979 := @ep1828 179648796719654643347 1623313478486440542208 61529601274993 1623313478486440542208 (@ep1829 1 5767168 (ep1830 (@ep1831 1048576 1 1048576 (ep1832 (@ep1833 743581381 743581381 62500 0 1 (ep1837 rfl) (ep1840 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 11) rfl) (@ep1841 524239 281474976710656 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235)) (@ep1842 524239 281474976710656 1570725007363 281474976710656 524239 281474976710656 (@ep1847 785362241562 785362765801 140737488355328 (@ep1853 ep1854 ep1855 ep1856 ep1857 ep1843 ep1844 ep1845 ep1846 (@ep1862 ep1861 ep1848 ep1849 ep1850 ep1851 (@ep1866 ep1867 ep1976) (@ep1866 ep1867 ep1976) rfl) (@ep1977 ep1867 ep1852 ep1854 ep1855 ep1856 (@ep1978 ep1867 ep1976) (@ep1978 ep1867 ep1976) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow34.d184 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz604 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 2 4) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz12 2 28))) (@HMul.hMul Real Real Real qz0 qz788 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235)))) Bool.false ep1782 ep1783 119753690922189846193 ep1783 := ep1826 (ep1827 ep1979) rfl rfl

noncomputable def ep1980 := nat_lit 4236898907395812516429824

noncomputable def ep1981 := nat_lit 16947595629583250065719296

noncomputable abbrev qz540 := (@HAdd.hAdd Complex Complex Complex qz547 (@HAdd.hAdd Complex Complex Complex qz547 qz548 (@HMul.hMul Complex Complex Complex qz543 Complex.I ↑(Enclosure.sfrac Bool.false 111131 1000))) (@Nat.cast Complex Complex.instNatCast 5))

noncomputable abbrev qz241 := (@Norm.norm Complex Complex.instNorm qz540)

noncomputable abbrev qz242 := (@HPow.hPow Complex Complex Complex (@instHPow Complex Complex Complex.instPow) qz608 (@HSub.hSub Complex Complex Complex qz593 (@Neg.neg Complex Complex.instNeg qz378) (@Nat.cast Complex Complex.instNatCast 5)))

noncomputable abbrev qz798 := (@HDiv.hDiv Real Real Real qz1 qz241 (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (Complex.re qz64) qz283))

noncomputable def ep1982 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 2 4) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz64 2 28))) (@HMul.hMul Real Real Real qz0 qz798 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242))) 760244355 89679990882304 40851825 89679990882304 6327119626217751375 50728546202701266944 8880685583805

noncomputable def ep1983 := nat_lit 567454596481342596146858683269120

noncomputable def ep1984 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 2 4) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz64 2 28)) 10095 171051008 15 171051008 75309 524288 3929 524288 760244355 89679990882304

noncomputable def ep1985 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz64 2 28)) (Real.sqrt (@HAdd.hAdd Real Real Real qz604 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz64 2 28)) (Complex.re (zetaApproximant qz64 2 28))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz64 2 28)) (Complex.im (zetaApproximant qz64 2 28))))) Bool.false 75309 524288 3929 524288

noncomputable def ep1986 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz604 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz64 2 28)) (Complex.re (zetaApproximant qz64 2 28))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz64 2 28)) (Complex.im (zetaApproximant qz64 2 28))))) Bool.false 150618 1048576 7858 1048576

noncomputable def ep1987 := nat_lit 1574809482700822116701067665712161212233655870644647840116007557

noncomputable def ep1988 := nat_lit 76119511034315630636110568142826035049031270400000000000000000000

noncomputable def ep1989 := nat_lit 463040526076241335491379703054597062932093541383417747906591385678884048153583113671

noncomputable def ep1990 := nat_lit 215121156688576499341464421910479774638847266137087746882484463206400000000000000000000

noncomputable def ep1991 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz604 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz64 2 28)) (Complex.re (zetaApproximant qz64 2 28))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz64 2 28)) (Complex.im (zetaApproximant qz64 2 28)))) ep1987 ep1988 ep1989 ep1990 71380 79238

noncomputable def ep1992 := nat_lit 19353992085892372733821926151485359415790372547904603610057599126313157641

noncomputable def ep1993 := nat_lit 940102539238390291035874051565984850136759944247404134400000000000000000000

noncomputable def ep1994 := nat_lit 424235919580282940964344848069753707035499763346505694305542558506924959982595346763

noncomputable def ep1995 := nat_lit 23863721879142427296837245386764819804075542518561842814899236987863009

noncomputable def ep1996 := nat_lit 235025634809597572758968512891496212534189986061851033600000000000000000000

noncomputable def ep1997 := nat_lit 9701151623989598631758713746210838974148444509228013400262206792989772042746941727

noncomputable def ep1998 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz64 2 28)) (Complex.re (zetaApproximant qz64 2 28))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz64 2 28)) (Complex.im (zetaApproximant qz64 2 28))) ep1992 ep1993 ep1994 ep1990 ep1995 ep1996 ep1997

noncomputable def ep1999 := nat_lit 53780289172144124835366105477619943659711816534271936720621115801600000000000000000000

noncomputable def ep2000 := nat_lit 4571118621621042900113909966939632993673450605010608286779119031617200920822972384578321959693560505309553194299222990423012147200000000000000000000

noncomputable def ep2001 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz64 2 28)) (Complex.re (zetaApproximant qz64 2 28)) ep1259 ep1260 ep1261 ep1262 ep1259 ep1260 ep1261 ep1262 ep1992

noncomputable def ep2002 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (zetaApproximant qz64 2 28)) (Complex.im (zetaApproximant qz64 2 28)) ep1455 ep1456 ep1457 ep1458 ep1455 ep1456 ep1457 ep1458 ep1995

noncomputable def ep2003 := @ep1982 202914184810805067776 ep1983 528483275772391442346255 ep1980 8461842844349246205 ep1981 (@ep1984 40851825 89679990882304 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 2 4) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 30720 334084) qz1096) Bool.false 10095 171051008 15 171051008 (BSN.theta_err_eq 2 4 30720 334084 EMRow34.d22 EMRow34.d23 rfl) (ep1806 rfl)) (ep1985 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz64 2 28)) (@ep1986 75309 524288 3929 524288 (@ep1991 524288 (@ep1998 ep1999 ep2000 ep1987 ep1988 ep1989 ep1990 (@ep2001 ep1993 ep1994 ep1990 ep1615 ep1615 rfl) (@ep2002 ep1996 ep1997 ep1999 ep1623 ep1623 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable def ep2004 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz798 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz241 (Enclosure.sfrac Bool.false 2 11)) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242))) Bool.false 6327119626217751375 50728546202701266944 8880685583805 202914184810805067776 (BSN.zrb_shape_eq qz241 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242)) qz61 5)

noncomputable def ep2005 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz241 (Enclosure.sfrac Bool.false 2 11)) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242)) 116671925 5767168 1 5767168 54230009715 8796093022208 148515 70368744177664

noncomputable def ep2006 := @Enclosure.Real.IsNear.mulLit_ff qz241 (Enclosure.sfrac Bool.false 2 11) 116671925 1048576 1 1048576 2 11 0 1 116671925 5767168

noncomputable abbrev qz243 := (Complex.re qz540)

noncomputable abbrev qz244 := (Complex.im qz540)

noncomputable abbrev qz245 := qz540

noncomputable abbrev qz1099 := (@HAdd.hAdd Real Real Real qz604 (@HMul.hMul Real Real Real qz0 qz243 qz243) (@HMul.hMul Real Real Real qz0 qz244 qz244))

noncomputable def ep2007 := @Enclosure.Real.IsNear.of_eq qz241 (Real.sqrt qz1099) Bool.false 116671925 1048576 1 1048576 (BSN.norm_eq_sqrt_mul_add qz245)

noncomputable def ep2008 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz1099) Bool.false 116671925 1048576 1 1048576 116671925

noncomputable def ep2009 := @Enclosure.Real.IsNear.sqrt_image qz1099 12380349161 1000000 0 1 58335962 58335963 524288

noncomputable def ep2010 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz243 qz243) (@HMul.hMul Real Real Real qz0 qz244 qz244) 121 4 0 1 12350099161 1000000 0 1

noncomputable def ep2011 := @Enclosure.Real.IsNear.mulLit_ff qz243 qz243 11 2 0 1 11 2 0 1 121 4

noncomputable def ep2012 := @Enclosure.Complex.IsNear.of_eq qz245 (Complex.mk (Enclosure.sfrac Bool.false 11 2) qz61) Bool.false 11 2 0 1 Bool.false 111131 1000 0 1 (BSN.s_add_nat_mk qz61 Bool.false 111131 1000 5 (@Eq.refl Real qz61))

noncomputable abbrev qz799 := (ep2012 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 11 2) qz61 Bool.false 11 2 0 1 Bool.false 111131 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 11 2) qz380))

noncomputable def ep2013 := @ep2011 0 1 (@Enclosure.Complex.IsNear.re_isNear qz245 Bool.false 11 2 0 1 Bool.false 111131 1000 0 1 qz799)

noncomputable def ep2014 := ep2013 (@Enclosure.Complex.IsNear.re_isNear qz245 Bool.false 11 2 0 1 Bool.false 111131 1000 0 1 qz799)

noncomputable def ep2015 := @Enclosure.Real.IsNear.mulLit_ff qz244 qz244 111131 1000 0 1 111131 1000 0 1 12350099161 1000000

noncomputable def ep2016 := @ep2015 0 1 (@Enclosure.Complex.IsNear.im_isNear qz245 Bool.false 11 2 0 1 Bool.false 111131 1000 0 1 qz799)

noncomputable def ep2017 := ep2016 (@Enclosure.Complex.IsNear.im_isNear qz245 Bool.false 11 2 0 1 Bool.false 111131 1000 0 1 qz799)

noncomputable def ep2018 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242)) (Real.sqrt (@HAdd.hAdd Real Real Real qz604 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242)) (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242)) (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242))))) Bool.false 54230009715 8796093022208

noncomputable def ep2019 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz604 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242)) (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242)) (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242))))) Bool.false 1735360310880 281474976710656

noncomputable def ep2020 := nat_lit 54545947128475048654018663210038520258238771914224952237780921537234818225982755732663591413

noncomputable def ep2021 := nat_lit 1435035846974384790815860697512966733117390328522878571745011302400000000000000000000000000000000

noncomputable def ep2022 := nat_lit 3311256251076703779514585207390617547716594515810999712969891353768536038934428158786267698699048777559

noncomputable def ep2023 := nat_lit 127239958943719029465354657163180937270321520823433814164129473350291759621891686400000000000000000000000000000000

noncomputable def ep2024 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz604 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242)) (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242)) (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242)))) ep2020 ep2021 ep2022 ep2023

noncomputable def ep2025 := nat_lit 4290396935705152533791939543163117695771874730347953071656716772891035763739432661785208209

noncomputable def ep2026 := nat_lit 142612502153296611096577146435266516179141483267468696644778269930971207725964431057154359744360331869

noncomputable def ep2027 := nat_lit 42413319647906343155118219054393645756773840274477938054709824450097253207297228800000000000000000000000000000000

noncomputable def ep2028 := nat_lit 256405868330458653674626141157527564094218863183045914112878595736447869705323076892236649

noncomputable def ep2029 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242)) (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242)) (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242))) ep2025 ep2021 ep2026 ep2027 ep2028

noncomputable def ep2030 := nat_lit 7321611464155024442938064783229422107741787390422849855841894400000000000000000000000000000000

noncomputable def ep2031 := nat_lit 45053417884637717909763340126325281237174532281384275359930570999619100246195857275231322179155746593

noncomputable def ep2032 := nat_lit 1988124358495609835396166518174702144848773762866153346314523021098308744092057600000000000000000000000000000000

noncomputable def ep2033 := nat_lit 399364231819036752131341793026201629921572683817791387057636307855845290907665870837454659398930321341277419854708043059943180856805717010663669809492787200000000000000000000000000000000

noncomputable def ep2034 := nat_lit 2071327336686587674455462530633293756849519703

noncomputable def ep2035 := nat_lit 1197929817215676784414384529080320000000000000000

noncomputable def ep2036 := nat_lit 346832362768918926776934917317728959005018850359

noncomputable def ep2037 := nat_lit 356707105261051716922216419343741306798080000000000000000

noncomputable def ep2038 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242)) (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242)) ep2034 ep2035 ep2036 ep2037 ep2034 ep2035 ep2036

noncomputable def ep2039 := nat_lit 506365350641667279626152582729742936304901907

noncomputable def ep2040 := nat_lit 85566415515405484601027466362880000000000000000

noncomputable def ep2041 := nat_lit 170743924341200113754687615577995876951509788181

noncomputable def ep2042 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242) Bool.true ep2034 ep2035 ep2036 ep2037 Bool.false ep2039 ep2040 ep2041

noncomputable def ep2043 := nat_lit 89176776315262929230554104835935326699520000000000000000

noncomputable def ep2044 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242 Bool.true ep2034 ep2035 ep2036 ep2037 Bool.false ep2039 ep2040 ep2041 ep2043

noncomputable def ep2045 := nat_lit 30573561199122374215666707535879460570329

noncomputable def ep2046 := nat_lit 47917192688627071376575381163212800000000000

noncomputable def ep2047 := nat_lit 368187533044204211599536399150322565414669

noncomputable def ep2048 := nat_lit 1783535526305258584611082096718706533990400000000000

noncomputable def ep2049 := nat_lit 945222122221549009949043406343426757035914901

noncomputable def ep2050 := nat_lit 399309939071892261471461509693440000000000000000

noncomputable def ep2051 := nat_lit 10118328005928817942852875462506090589706853717

noncomputable def ep2052 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.re qz242)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.im qz242)) ep2045 ep2046 ep2047 ep2048 ep2049 ep2050 ep2051

noncomputable def ep2053 := nat_lit 13211374268927841367489497012731159511040000000000000000

noncomputable def ep2054 := nat_lit 33084063704410647715480830033554088798247690792042066507984934034053710793932800000000000

noncomputable def ep2055 := nat_lit 737241867685705433453654967228301312

noncomputable def ep2056 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.re qz242) 152407625707003403921 2419200000000000 0 1 200603880923246114249 ep1798 2415807813659059801789 ep2055 ep2045

noncomputable def ep2057 := nat_lit 16871344335410862913144651

noncomputable def ep2058 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)))) 152407625707003403921 2419200000000000 0 1 0 1 0 1 152407625707003403921

noncomputable def ep2059 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) 1 30240 0 1 152407625707003403921 80000000000 0 1 152407625707003403921 2419200000000000 0

noncomputable abbrev qz246 := (@HAdd.hAdd Complex Complex Complex qz260 qz378 qz261)

noncomputable def ep2060 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)) (@HMul.hMul Complex Complex Complex qz3 (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4)) qz246) Bool.false 152407625707003403921 80000000000 0 1 Bool.false ep2057 1000000000000000 0 1

noncomputable def ep2061 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.re qz246)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.im qz246)) 1370334858453642635289 2000000000000 0 1 152490986513840153921 125000000000 0 1

noncomputable def ep2062 := nat_lit 476273830334385637253125000000000

noncomputable def ep2063 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.re qz246) 152259428717071403921 1000000000000 0 1 9 2 0 1 1370334858453642635289 2000000000000

noncomputable abbrev qz247 := (@HAdd.hAdd Complex Complex Complex qz260 qz378 qz550)

noncomputable def ep2064 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4)) (@HMul.hMul Complex Complex Complex qz3 (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) qz247) Bool.false 152259428717071403921 1000000000000 0 1 Bool.true 1372173259611091 125000000 0 1

noncomputable def ep2065 := @Enclosure.Real.IsNear.subLit_tt_p (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.re qz247)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.im qz247)) 778029997143 4000000 0 1 152453936216357153921 1000000000000 0 1

noncomputable def ep2066 := nat_lit 609037714868285615684000000

noncomputable def ep2067 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.re qz247) 111147142449 2000000 0 1 7 2 0 1 778029997143 4000000

noncomputable abbrev qz800 := (ep1207 (BSN.ascPochhammer_succ_eval_c 2 3 qz64 rfl) (ep1235 (@ep1236 274367973322218200 1371839866611091 1000000000 0 1 (ep1239 rfl) (ep1242 rfl) rfl rfl)))

noncomputable def ep2068 := @ep2067 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 111147142449 2000000 0 1 Bool.true 1371839866611091 1000000000 0 1 qz800)

noncomputable def ep2069 := @Enclosure.Complex.IsNear.of_eq qz247 (Complex.mk (Enclosure.sfrac Bool.false 7 2) qz61) Bool.false 7 2 0 1 Bool.false 111131 1000 0 1 (BSN.s_add_nat_mk qz61 Bool.false 111131 1000 3 (@Eq.refl Real qz61))

noncomputable abbrev qz801 := (ep2069 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz61 Bool.false 7 2 0 1 Bool.false 111131 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz380))

noncomputable def ep2070 := ep2068 (@Enclosure.Complex.IsNear.re_isNear qz247 Bool.false 7 2 0 1 Bool.false 111131 1000 0 1 qz801)

noncomputable def ep2071 := @Enclosure.Real.IsNear.mulLit_tf (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.im qz247) 1371839866611091 1000000000 0 1 111131 1000 0 1 152453936216357153921 1000000000000

noncomputable def ep2072 := @ep2071 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 111147142449 2000000 0 1 Bool.true 1371839866611091 1000000000 0 1 qz800)

noncomputable def ep2073 := ep2072 (@Enclosure.Complex.IsNear.im_isNear qz247 Bool.false 7 2 0 1 Bool.false 111131 1000 0 1 qz801)

noncomputable def ep2074 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) qz247 Bool.false 152259428717071403921 1000000000000 0 1 Bool.true 1372173259611091 125000000 0 1 (@ep2065 ep2066 152259428717071403921 1000000000000 0 1 (ep2070 rfl) (ep2073 rfl) rfl rfl)

noncomputable def ep2075 := @Enclosure.Real.IsNear.addLit_tt (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.im qz247)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.re qz247)) 12351893087499819 2000000000 0 1 9602879066277637 2000000000 0 1

noncomputable def ep2076 := nat_lit 43909544307554912000000000

noncomputable def ep2077 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.im qz247) 111147142449 2000000 0 1 111131 1000 0 1 12351893087499819 2000000000

noncomputable def ep2078 := @ep2077 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 111147142449 2000000 0 1 Bool.true 1371839866611091 1000000000 0 1 qz800)

noncomputable def ep2079 := ep2078 (@Enclosure.Complex.IsNear.im_isNear qz247 Bool.false 7 2 0 1 Bool.false 111131 1000 0 1 qz801)

noncomputable def ep2080 := @Enclosure.Real.IsNear.mulLit_tf (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.re qz247) 1371839866611091 1000000000 0 1 7 2 0 1 9602879066277637 2000000000

noncomputable def ep2081 := @ep2080 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 111147142449 2000000 0 1 Bool.true 1371839866611091 1000000000 0 1 qz800)

noncomputable def ep2082 := ep2081 (@Enclosure.Complex.IsNear.re_isNear qz247 Bool.false 7 2 0 1 Bool.false 111131 1000 0 1 qz801)

noncomputable abbrev qz802 := (ep2064 (BSN.ascPochhammer_succ_eval_c 3 4 qz64 rfl) (ep2074 (@ep2075 ep2076 1372173259611091 125000000 0 1 (ep2079 rfl) (ep2082 rfl) rfl rfl)))

noncomputable def ep2083 := @ep2063 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4)) Bool.false 152259428717071403921 1000000000000 0 1 Bool.true 1372173259611091 125000000 0 1 qz802)

noncomputable def ep2084 := @Enclosure.Complex.IsNear.of_eq qz246 (Complex.mk (Enclosure.sfrac Bool.false 9 2) qz61) Bool.false 9 2 0 1 Bool.false 111131 1000 0 1 (BSN.s_add_nat_mk qz61 Bool.false 111131 1000 4 (@Eq.refl Real qz61))

noncomputable abbrev qz803 := (ep2084 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9 2) qz61 Bool.false 9 2 0 1 Bool.false 111131 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 9 2) qz380))

noncomputable def ep2085 := ep2083 (@Enclosure.Complex.IsNear.re_isNear qz246 Bool.false 9 2 0 1 Bool.false 111131 1000 0 1 qz803)

noncomputable def ep2086 := @Enclosure.Real.IsNear.mulLit_tf (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.im qz246) 1372173259611091 125000000 0 1 111131 1000 0 1 152490986513840153921 125000000000

noncomputable def ep2087 := @ep2086 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4)) Bool.false 152259428717071403921 1000000000000 0 1 Bool.true 1372173259611091 125000000 0 1 qz802)

noncomputable def ep2088 := ep2087 (@Enclosure.Complex.IsNear.im_isNear qz246 Bool.false 9 2 0 1 Bool.false 111131 1000 0 1 qz803)

noncomputable def ep2089 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4)) qz246 Bool.false 152407625707003403921 80000000000 0 1 Bool.false ep2057 1000000000000000 0 1 (@ep2061 ep2062 152407625707003403921 80000000000 0 1 (ep2085 rfl) (ep2088 rfl) rfl rfl)

noncomputable def ep2090 := nat_lit 16920742572756862189144651

noncomputable def ep2091 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.im qz246)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.re qz246)) ep2090 1000000000000000 0 1 12349559336499819 250000000 0 1

noncomputable def ep2092 := nat_lit 4217836083852715728286162750000000

noncomputable def ep2093 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.im qz246) 152259428717071403921 1000000000000 0 1 111131 1000 0 1 ep2090 1000000000000000

noncomputable def ep2094 := @ep2093 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4)) Bool.false 152259428717071403921 1000000000000 0 1 Bool.true 1372173259611091 125000000 0 1 qz802)

noncomputable def ep2095 := ep2094 (@Enclosure.Complex.IsNear.im_isNear qz246 Bool.false 9 2 0 1 Bool.false 111131 1000 0 1 qz803)

noncomputable def ep2096 := @Enclosure.Real.IsNear.mulLit_tf (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.re qz246) 1372173259611091 125000000 0 1 9 2 0 1 12349559336499819 250000000

noncomputable def ep2097 := @ep2096 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4)) Bool.false 152259428717071403921 1000000000000 0 1 Bool.true 1372173259611091 125000000 0 1 qz802)

noncomputable def ep2098 := ep2097 (@Enclosure.Complex.IsNear.re_isNear qz246 Bool.false 9 2 0 1 Bool.false 111131 1000 0 1 qz803)

noncomputable abbrev qz804 := (ep2060 (BSN.ascPochhammer_succ_eval_c 4 5 qz64 rfl) (ep2089 (@ep2091 ep2092 ep2057 1000000000000000 0 1 (ep2095 rfl) (ep2098 rfl) rfl rfl)))

noncomputable def ep2099 := @ep2059 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) Bool.false 1 30240 0 1 Bool.false 0 1 0 1 ep1883) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)) Bool.false 152407625707003403921 80000000000 0 1 Bool.false ep2057 1000000000000000 0 1 qz804)

noncomputable def ep2100 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) 0 1 0 1 ep2057 1000000000000000 0 1 0 1 0

noncomputable def ep2101 := @ep2100 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) Bool.false 1 30240 0 1 Bool.false 0 1 0 1 ep1883) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)) Bool.false 152407625707003403921 80000000000 0 1 Bool.false ep2057 1000000000000000 0 1 qz804)

noncomputable def ep2102 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)))) ep2057 30240000000000000000 0 1 0 1 0 1 ep2057

noncomputable def ep2103 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) 1 30240 0 1 ep2057 1000000000000000 0 1 ep2057 30240000000000000000 0

noncomputable def ep2104 := @ep2103 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) Bool.false 1 30240 0 1 Bool.false 0 1 0 1 ep1883) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)) Bool.false 152407625707003403921 80000000000 0 1 Bool.false ep2057 1000000000000000 0 1 qz804)

noncomputable def ep2105 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) 0 1 0 1 152407625707003403921 80000000000 0 1 0 1 0

noncomputable def ep2106 := @ep2105 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) Bool.false 1 30240 0 1 Bool.false 0 1 0 1 ep1883) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)) Bool.false 152407625707003403921 80000000000 0 1 Bool.false ep2057 1000000000000000 0 1 qz804)

noncomputable def ep2107 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)) Bool.false 152407625707003403921 2419200000000000 0 1 Bool.false ep2057 30240000000000000000 0 1 (@ep2058 152407625707003403921 2419200000000000 0 1 (ep2099 rfl) (ep2101 rfl) rfl rfl) (@ep2102 ep2057 30240000000000000000 0 1 (ep2104 rfl) (ep2106 rfl) rfl rfl)

noncomputable def ep2108 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) Bool.false 152407625707003403921 2419200000000000 0 1 Bool.false ep2057 30240000000000000000 0 1 ep2107

noncomputable def ep2109 := @Enclosure.Complex.IsNear.re_isNear qz242 Bool.false 200603880923246114249 ep1798 2415807813659059801789 ep2055 Bool.false 168075899009003948253 ep1878 16192832694824199973509 ep1931

noncomputable def ep2110 := @Enclosure.Complex.IsNear.of_eq qz242 (Complex.mk (@HMul.hMul Real Real Real qz0 qz538 (Real.cos qz411)) (@HMul.hMul Real Real Real qz0 qz538 qz973)) Bool.false 200603880923246114249 ep1798 2415807813659059801789 ep2055 Bool.false 168075899009003948253 ep1878 16192832694824199973509

noncomputable def ep2111 := nat_lit 9269234923419564358540197888

noncomputable def ep2112 := nat_lit 1004972464125000000000000000

noncomputable def ep2113 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz372 111131 1000 0 1 3751728747586831 1125899906842624 19278678919 1004972464125000000000000 416933367448072115861 1125899906842624000 2142458866947389 ep2112 qz380 (BSN.isNear_log_sfrac 28 1 3751728747586831 1125899906842624 19278678919 1004972464125000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz613) Bool.false ep1938 ep1939 1263447501635584 ep1940 3751728747586831 1125899906842624 19278678919 1004972464125000000000000 (BSN.log_rat_reduce_isNear 28 1 4 56 32 78758920438019 140737488355328 24973259072661432 36028797018963968 65861875408896 1000000000000000 rfl rfl rfl rfl (ep1944 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep2114 := nat_lit 989162653494962939526612143836131406991805235871411958132951220224

noncomputable def ep2115 := nat_lit 842498333348457493583344221469363458551160763204392890034487820288

noncomputable def ep2116 := nat_lit 838051404823506469362323538700647848434107485628876285522130534848065968159089097142843408709080278323545351532797498336987871112836621468540219612437474336615686670015062005191905231410844334373283243295495881098334453466972539468877266479203160469728073134477354666697503328176389402136942739456

noncomputable def ep2117 := nat_lit 52891321971172767596247250737880688851123773729959232653830066926421887024034431815363097947056912641878280075923682769184803106963825615327895103932397588487159726851292057237883449642301316355768873203215599328703548150308222295450928827049722111507143599254812955041773912982649933098895015936000

noncomputable def ep2118 := nat_lit 1938627972447960668957972088315174025425114841925017588773838145255214046861331843516097456491247174104796183015397495575917030879380939599398139726118636663652982784300257585955510094045165356843880037672030935903630971619221278358969935261877350320189513326534280262998368299029364736

noncomputable def ep2119 := nat_lit 6821483355492220634392802975784962120121899376672532278272915566088243287877624839822344016795595255742496750909193314606694056096180736661368584381878047810379279998466866207078701037922822785374482754362870047659621232502240975082303833865587484432175356477548064378112247610673919758150265733120

noncomputable def ep2120 := nat_lit 3014805352356847752986093292059199264514055102607676261268313814806047560369962613475696582982244020587061964327649917843533777096938060073690020924146662543768104430523647262559356629611175032278825772583289161736102244567568670840702943141834160355907185157524338437381113040011046186637015908352000

noncomputable def ep2121 := BSN.sin_dyadic_bound_f 676812552397437848 576460752303423488 5 4 281474976710656 131852387293201 ep2116 ep2117 ep2118 ep2119 ep2120 ep2118 259614437212468 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.sinEvenP 676812552397437848) (BSN.sinEvenQ 576460752303423488) 0 4 ep2116 ep2117 ep2118 rfl rfl rfl rfl) (@BSN.binarySplit_of_base4 (BSN.sinOddP 676812552397437848) (BSN.sinOddQ 576460752303423488) 0 4 ep2119 ep2120 ep2118 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz805 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26058335465504507) (@Nat.cast Real Real.instNatCast 70368744177664))

noncomputable def ep2122 := @Enclosure.Real.IsNear.cos_image qz411 qz805 Bool.false 26058335465504507 70368744177664 301 140737488355328 Bool.false 259614437212468 281474976710656 1 65861875408896 (@Enclosure.Real.IsNear.recentre' qz411 Bool.false 416933367448072115861 1125899906842624000 2142458866947389 ep2112 26058335465504507 70368744177664 301 140737488355328 (ep2113 rfl) rfl) (Enclosure.sfrac_false_div 26058335465504507 70368744177664) (BSN.cos_reduce3 qz805 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep2114) (@Nat.cast Real Real.instNatCast ep2115)) ep1780 ep1758 Bool.false 259614437212468 281474976710656 58 ep1781 131723750817792 65861875408896 (BSN.sin_reduce_arg_pos_rat_q3 26058335465504507 70368744177664 ep1780 ep1758 58 ep2114 ep2115 rfl rfl rfl rfl) EMRow34.d183 (@BSN.sin_arg_round Bool.false 259614437212468 281474976710656 ep2114 ep2115 676812552397437848 576460752303423488 131852387293201 131723750817792 (ep2121 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep2123 := nat_lit 246609563548755855401458222663700641105307518600962161347980591063630016991373948568461520500714931471299478956738062779398515748738247204860600794905124417240922206831499219836227813330385836430602366743125409834396457332973295032828027649548678364401899348185005465224965090862207522060648841216

noncomputable def ep2124 := nat_lit 3111254233598398093896897102228275814771986689997601920813533348613052177884378342080182232179818390698722357407275457010870770997872095019287947290141034616891748638311297484581379390723606844456992541365623489923738126488718958555936989826454241853361388191459585590692583116626466652876177408000

noncomputable def ep2125 := nat_lit 2513522587570755070713194461893133251056038712830211313096811498192685391122947484026289086715259773739568341234252590817557583038250538012013620291379349613781306846874565233701953243991022030183125286675588899293744206024512420742352766985428872077373514650539850331718541731456349110568889614336

noncomputable def ep2126 := nat_lit 476021897740554908366225256640926199660113963569633093884470602337796983216309886338267881523512213776904520683313144922663227962674430537951055935391578296384437541661628515140951046780711847201919858828940393958331933352774000659058359443447499003564292393293316595375965216843849397890055143424000

noncomputable def ep2127 := BSN.cos_dyadic_bound_f 676812552397437848 576460752303423488 5 4 281474976710656 131852387293201 ep2123 ep2124 ep2118 ep2125 ep2126 ep2118 108758937587298 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.cosEvenP 676812552397437848) (BSN.cosEvenQ 576460752303423488) 0 4 ep2123 ep2124 ep2118 rfl rfl rfl rfl) (@BSN.binarySplit_of_base4 (BSN.cosOddP 676812552397437848) (BSN.cosOddQ 576460752303423488) 0 4 ep2125 ep2126 ep2118 rfl rfl rfl rfl) rfl rfl

noncomputable def ep2128 := @Enclosure.Real.IsNear.sin_image qz411 qz805 Bool.false 26058335465504507 70368744177664 301 140737488355328 Bool.true 108758937587298 281474976710656 1 65861875408896 (@Enclosure.Real.IsNear.recentre' qz411 Bool.false 416933367448072115861 1125899906842624000 2142458866947389 ep2112 26058335465504507 70368744177664 301 140737488355328 (ep2113 rfl) rfl) (Enclosure.sfrac_false_div 26058335465504507 70368744177664) (BSN.sin_reduce3 qz805 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep2114) (@Nat.cast Real Real.instNatCast ep2115)) ep1780 ep1758 Bool.false 108758937587298 281474976710656 58 ep1781 131723750817792 65861875408896 (BSN.sin_reduce_arg_pos_rat_q3 26058335465504507 70368744177664 ep1780 ep1758 58 ep2114 ep2115 rfl rfl rfl rfl) EMRow34.d183 (@BSN.cos_arg_round Bool.false 108758937587298 281474976710656 ep2114 ep2115 676812552397437848 576460752303423488 131852387293201 131723750817792 (ep2127 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep2129 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz538 (Real.cos qz411)) (@HMul.hMul Real Real Real qz0 qz538 qz973) Bool.false 200603880923246114249 ep1798 2415807813659059801789 ep2055 Bool.false 168075899009003948253 ep1878 16192832694824199973509 ep1931 (@Enclosure.Real.IsNear.mulLit_ff qz538 (Real.cos qz411) 3090797 281474976710656 1 281474976710656 64903609303117 70368744177664 2437153562797 1131498403737739789860864 200603880923246114249 ep1798 2415807813659059801789 ep2055 qz796 (@Enclosure.Real.IsNear.recentre' (Real.cos qz411) Bool.false 259614437212468 281474976710656 19965161986433024 ep2111 64903609303117 70368744177664 2437153562797 1131498403737739789860864 (ep2122 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz538 qz973 3090797 281474976710656 1 281474976710656 54379468793649 140737488355328 2437153562797 1131498403737739789860864 168075899009003948253 ep1878 16192832694824199973509 ep1931 qz796 (@Enclosure.Real.IsNear.neg (Real.sin qz411) Bool.true 54379468793649 140737488355328 2437153562797 1131498403737739789860864 (@Enclosure.Real.IsNear.recentre' (Real.sin qz411) Bool.true 108758937587298 281474976710656 19965161986433024 ep2111 54379468793649 140737488355328 2437153562797 1131498403737739789860864 (ep2128 rfl rfl) rfl)) rfl)

noncomputable def ep2130 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.im qz242) ep2057 30240000000000000000 0 1 168075899009003948253 ep1878 16192832694824199973509 ep1931 ep2049

noncomputable def ep2131 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) Bool.false 152407625707003403921 2419200000000000 0 1 Bool.false ep2057 30240000000000000000 0 1 ep2107

noncomputable def ep2132 := @Enclosure.Complex.IsNear.im_isNear qz242 Bool.false 200603880923246114249 ep1798 2415807813659059801789 ep2055 Bool.false 168075899009003948253 ep1878 16192832694824199973509 ep1931

noncomputable def ep2133 := nat_lit 8538682902177459361770217055866513766671

noncomputable def ep2134 := nat_lit 31944795125751380917716920775475200000000000

noncomputable def ep2135 := nat_lit 91404117944033109068575495780794852841807

noncomputable def ep2136 := nat_lit 1056909941514227309399159761018492760883200000000000

noncomputable def ep2137 := nat_lit 3384457150075843594349876509310703421009232099

noncomputable def ep2138 := nat_lit 598964908607838392207192264540160000000000000000

noncomputable def ep2139 := nat_lit 40757925472418080044256639530372827810745580639

noncomputable def ep2140 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.im qz242)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.re qz242)) ep2133 ep2134 ep2135 ep2136 ep2137 ep2138 ep2139

noncomputable def ep2141 := nat_lit 22294194078815732307638526208983831674880000000000000000

noncomputable def ep2142 := nat_lit 113230161695191252585571020302850086698972363119043418531654579316582551178444800000000000

noncomputable def ep2143 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.im qz242) 152407625707003403921 2419200000000000 0 1 168075899009003948253 ep1878 16192832694824199973509 ep1931 ep2133

noncomputable def ep2144 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.re qz242) ep2057 30240000000000000000 0 1 200603880923246114249 ep1798 2415807813659059801789 ep2055 ep2137

noncomputable abbrev qz806 := (@ep2110 ep1931 (BSN.cpow_neg_s_sub_mk qz61 111131 1000 28 5 8293509467471872 (@Eq.refl Real qz61) rfl EMRow34.d180) ep2129)

noncomputable def ep2145 := ep2044 (@ep2052 ep2053 ep2054 ep2034 ep2035 ep2036 ep2037 (@ep2056 ep2046 ep2047 ep2048 ep2108 (ep2109 qz806) rfl) (@ep2130 ep2050 ep2051 ep2053 ep2131 (ep2132 qz806) rfl) rfl rfl) (@ep2140 ep2141 ep2142 ep2039 ep2040 ep2041 ep2043 (@ep2143 ep2134 ep2135 ep2136 ep2108 (ep2132 qz806) rfl) (@ep2144 ep2138 ep2139 ep2141 ep2131 (ep2109 qz806) rfl) rfl rfl)

noncomputable def ep2146 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242)) (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242)) ep2039 ep2040 ep2041 ep2043 ep2039 ep2040 ep2041

noncomputable def ep2147 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242) Bool.true ep2034 ep2035 ep2036 ep2037 Bool.false ep2039 ep2040 ep2041

noncomputable def ep2148 := @ep2005 6327119626217751375 50728546202701266944 8880685583805 202914184810805067776 (@ep2006 1 5767168 (ep2007 (@ep2008 1048576 1 1048576 (ep2009 (@ep2010 49521396644 12380349161 1000000 0 1 (ep2014 rfl) (ep2017 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 11) rfl) (@ep2018 148515 70368744177664 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242)) (@ep2019 594060 281474976710656 54230009715 8796093022208 148515 70368744177664 (@ep2024 867679858410 867680452470 140737488355328 (@ep2029 ep2030 ep2031 ep2032 ep2033 ep2020 ep2021 ep2022 ep2023 (@ep2038 ep2037 ep2025 ep2021 ep2026 ep2027 (@ep2042 ep2043 ep2145) (@ep2042 ep2043 ep2145) rfl) (@ep2146 ep2043 ep2028 ep2030 ep2031 ep2032 (@ep2147 ep2043 ep2145) (@ep2147 ep2043 ep2145) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow34.d185 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz604 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 2 4) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz64 2 28))) (@HMul.hMul Real Real Real qz0 qz798 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242)))) Bool.false 528483275772391442346255 ep1980 8461842844349246205 ep1981 := ep2003 (ep2004 ep2148) rfl rfl

noncomputable def EMRow34.d186 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J))

noncomputable abbrev qz248 := (@Enclosure.dec_le_dec qz257 qz376 108936 1000 111131 1000 (@Eq.refl Real qz257) (@Eq.refl Real qz376) rfl rfl rfl)

noncomputable abbrev qz807 := (EMRow34.d3 qz9 qz61 qz248 28 28 2 2)

noncomputable def ep2149 := @Zeta.Certificates.ZIntervalEM.Certificate.mk qz807 (@Enclosure.dec_nonneg qz9 108936 1000 (@Eq.refl Real qz9)) (@Enclosure.pos_of_ble 2 rfl) (@Enclosure.pos_of_ble 28 rfl)

noncomputable def ep2150 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalEM.fstVal qz807) ep459 ep460

noncomputable def ep2151 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalEM.fstVal qz807) (hardyZApproximantEM 2 28 qz9) Bool.false

noncomputable def ep2152 := BSN.mul_neg_of_pos_neg_r (Zeta.Certificates.ZIntervalEM.fstVal qz807) (Zeta.Certificates.ZIntervalEM.sndVal qz807) (@ep2150 ep461 ep462 (@ep2151 ep459 ep460 ep461 ep462 (@Eq.refl Real (hardyZApproximantEM 2 28 qz9)) EMRow34.d15) rfl rfl rfl)

noncomputable def ep2153 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalEM.sndVal qz807) ep1243 ep1244

noncomputable def ep2154 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalEM.sndVal qz807) (hardyZApproximantEM 2 28 qz61) Bool.true

noncomputable def ep2155 := BSN.gt_trans_le (@Norm.norm Real Real.norm (Zeta.Certificates.ZIntervalEM.fstVal qz807)) (BSN.hardyZErrorBoundStrong 2 28 qz9)

noncomputable def ep2156 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalEM.fstVal qz807) (BSN.hardyZErrorBoundStrong 2 28 qz9) Bool.false

noncomputable def ep2157 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 2 28 qz9) (@HAdd.hAdd Real Real Real qz604 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 2 4) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz12 2 28))) (@HMul.hMul Real Real Real qz0 qz788 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235)))) Bool.false ep1782 ep1783 119753690922189846193 ep1783 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz604 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 2 4) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz12 2 28))) (@HMul.hMul Real Real Real qz0 qz788 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235)))))

noncomputable def ep2158 := BSN.gt_trans_le (@Norm.norm Real Real.norm (Zeta.Certificates.ZIntervalEM.sndVal qz807)) (BSN.hardyZErrorBoundStrong 2 28 qz61)

noncomputable def ep2159 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalEM.sndVal qz807) (BSN.hardyZErrorBoundStrong 2 28 qz61) Bool.true

noncomputable def ep2160 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 2 28 qz61) (@HAdd.hAdd Real Real Real qz604 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 2 4) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz64 2 28))) (@HMul.hMul Real Real Real qz0 qz798 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242)))) Bool.false 528483275772391442346255 ep1980 8461842844349246205 ep1981 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz604 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 2 4) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz64 2 28))) (@HMul.hMul Real Real Real qz0 qz798 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242)))))

noncomputable def ep2161 := @List.cons EMRow34.d0 (@PSigma.mk Zeta.Certificates.ZIntervalEM Zeta.Certificates.ZIntervalEM.Certificate qz807 (ep2149 (@Enclosure.pos_of_ble 2 rfl) (@Enclosure.pos_of_ble 28 rfl) (ep2152 (@ep2153 ep1245 ep1246 (@ep2154 ep1243 ep1244 ep1245 ep1246 (@Eq.refl Real (hardyZApproximantEM 2 28 qz61)) EMRow34.d21) rfl rfl rfl)) (ep2155 (hardyZErrorBoundEM 2 28 qz9) (BSN.hardyZErrorBoundEM_le_strong 2 28 qz9 rfl) (@ep2156 Bool.false ep459 ep460 ep461 ep462 ep1782 ep1783 119753690922189846193 ep1783 (@ep2151 ep459 ep460 ep461 ep462 (@Eq.refl Real (hardyZApproximantEM 2 28 qz9)) EMRow34.d15) (ep2157 EMRow34.d184) rfl rfl rfl rfl rfl)) (ep2158 (hardyZErrorBoundEM 2 28 qz61) (BSN.hardyZErrorBoundEM_le_strong 2 28 qz61 rfl) (@ep2159 Bool.false ep1243 ep1244 ep1245 ep1246 528483275772391442346255 ep1980 8461842844349246205 ep1981 (@ep2154 ep1243 ep1244 ep1245 ep1246 (@Eq.refl Real (hardyZApproximantEM 2 28 qz61)) EMRow34.d21) (ep2160 EMRow34.d185) rfl rfl rfl rfl rfl)))) (@List.nil EMRow34.d0)

noncomputable abbrev qz808 := (@NonemptyInterval Real Real.instLE)

noncomputable abbrev qz809 := (Zeta.Certificates.CertifiedZeroIntervals.intervals (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep2161 (@List.IsChain.singleton EMRow34.d1 EMRow34.d186 (EMRow34.d2 qz9 qz61 qz248))))

noncomputable def ep2162 := And (@Eq (Option Real) (@Option.map qz808 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz808 qz809)) (@Option.some Real qz9))

noncomputable def ep2163 := ep2162 (@Eq (Option Real) (@Option.map qz808 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz808 qz809)) (@Option.some Real qz61))

noncomputable def ep2164 := @And.intro (@Eq Nat (@List.length qz808 qz809) 1) ep2163

noncomputable def ep2165 := @And.intro (@Eq (Option Real) (@Option.map qz808 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz808 qz809)) (@Option.some Real qz9))

noncomputable def ep2166 := @ep2165 (@Eq (Option Real) (@Option.map qz808 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz808 qz809)) (@Option.some Real qz61))

noncomputable abbrev qz810 := (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep2161 (@List.IsChain.singleton EMRow34.d1 EMRow34.d186 (EMRow34.d2 qz9 qz61 qz248)))

theorem EMRow34.d187 : Zeta.Certificates.BatchSpec 1 108936 1000 111131 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz808 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 1) (And (@Eq (Option Real) (@Option.map qz808 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz808 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz9)) (@Eq (Option Real) (@Option.map qz808 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz808 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz61)))) qz810 (ep2164 (@Eq.refl Nat 1) (ep2166 (@Eq.refl (Option Real) (@Option.some Real qz9)) (@Eq.refl (Option Real) (@Option.some Real qz61))))

theorem solution : Zeta.Certificates.BatchSpec 1 108936 1000 111131 1000 := EMRow34.d187
#print axioms solution
#check solution
