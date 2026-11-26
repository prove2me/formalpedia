-- Prove2me | solution 1 for RHHeight1000.em_main_0040_0040
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T10:22:15.845855+00:00
-- url     : https://prove2.me/submissions/a2991e99-11fa-4ffe-ae87-26903cae666b

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

noncomputable def EMRow40.d0 := @PSigma Zeta.Certificates.ZIntervalEM fun (I : Zeta.Certificates.ZIntervalEM) => Zeta.Certificates.ZIntervalEM.Certificate I

noncomputable def EMRow40.d1 := @NonemptyInterval Real Real.instLE

noncomputable def EMRow40.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h

noncomputable def EMRow40.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) (fc sc fb sb : Nat) => Zeta.Certificates.ZIntervalEM.mk (EMRow40.d2 a b h) fc sc fb sb

noncomputable def ep0 := nat_lit 26986075409044028275299783

noncomputable def ep1 := nat_lit 4294967296000000000000000

noncomputable def ep2 := nat_lit 26986075409044045455168967

noncomputable abbrev qz0 := (@instHMul Real Real.instMul)

noncomputable abbrev qz251 := (Enclosure.sfrac Bool.false 2 1)

noncomputable def ep3 := @BSN.isNear_log_image_fff (@HMul.hMul Real Real Real qz0 qz251 Real.pi) 884279719003555 140737488355328 1 500000000000000 ep0 ep1 ep2 ep1 4138529546116343 2251799813685248 31250000023663 11831500000000000000 4138529546116343 2251799813685248 31250000023663 11831500000000000000 963576 524288

noncomputable abbrev qz252 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 2 1) Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) BSN.pi_near_15 rfl)

noncomputable def ep4 := @ep3 2 524288 qz252 rfl rfl rfl rfl

noncomputable def ep5 := nat_lit 53972150818088056550599566

noncomputable def ep6 := nat_lit 34359738368000000000000000

noncomputable def ep7 := nat_lit 9806206225044028275299783

noncomputable def ep8 := nat_lit 44165944593044028275299783

noncomputable def ep9 := nat_lit 13681445815609410487519367394620474863599256634174726093703677122907123617368241606644861540940610176751640793056574796245399519365549113997355475306157239709119582688278313060810592403844863400465080549957745

noncomputable def ep10 := nat_lit 231714499556395493334623298703961145503103241611736774613091488581016477543539392410113701224645713379230392133956226737605624599560350113120270717249177907454870984269546186598262646369758174842349131395304

noncomputable def ep11 := nat_lit 8978369550011295664474073352761810093897501552430546263638635096022803738134167562509900960712119243631997923545019968443113540909076206607473711060286601587364321108377403290080403445693385008949995305

noncomputable def ep12 := BSN.log_dyadic_bound ep7 ep8 5 4 ep9 1048576 378608 ep10 ep11 473518 ep5 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep7) (BSN.artanhQ ep8) 0 4 ep10 ep9 ep11 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz1 := (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))

noncomputable def ep13 := ep4 rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep1 4138529546116343 2251799813685248 31250000023663 11831500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep0) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 69433004117575847641088 37778931862957161709568 1000000000757216 378608000000000000000 4138529546116343 2251799813685248 31250000023663 11831500000000000000 (BSN.log_rat_reduce_isNear ep0 ep1 2 ep5 ep6 473518 1048576 24973259072661432 36028797018963968 378608 1000000000000000 rfl rfl rfl rfl (ep12 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep14 := nat_lit 53972150818088090910337934

noncomputable def ep15 := nat_lit 9806206225044045455168967

noncomputable def ep16 := nat_lit 44165944593044045455168967

noncomputable def ep17 := nat_lit 13681445815609453062485491347592146866046743284321690683909457683007658987562290830600045658905080811372395010565947827677605470036294121079488508864180301737865471494204890974265645509835068840465080549957745

noncomputable def ep18 := nat_lit 231714499556396865510889920206523150079811393376960301632499817942333196803513131357563499488546302200815366867712007119763002650772307103678175657719139104636874731038771518520299266622696414842349131395304

noncomputable def ep19 := nat_lit 8978369550011421500876706511871067098718760264493934208903156435737864998391937547068187824077011975074541700434630537294838404525415248443919841847024664017658842168336182958576672102333385008949995305

noncomputable def ep20 := BSN.log_dyadic_bound ep15 ep16 5 4 ep17 1048576 378608 ep18 ep19 473518 ep14 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep15) (BSN.artanhQ ep16) 0 4 ep18 ep17 ep19 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep21 := ep13 (BSN.isNear_log_sfrac ep2 ep1 4138529546116343 2251799813685248 31250000023663 11831500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep2) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 69433004117575847641088 37778931862957161709568 1000000000757216 378608000000000000000 4138529546116343 2251799813685248 31250000023663 11831500000000000000 (BSN.log_rat_reduce_isNear ep2 ep1 2 ep14 ep6 473518 1048576 24973259072661432 36028797018963968 378608 1000000000000000 rfl rfl rfl rfl (ep20 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable abbrev qz253 := (Real.log (@HMul.hMul Real Real Real qz0 (2 : Real) Real.pi))

theorem EMRow40.d4 : Enclosure.Real.IsNear qz253 Bool.false 120447 65536 1 262144 := @Enclosure.Real.IsNear.of_eq qz253 (Real.log (@HMul.hMul Real Real Real qz0 qz251 Real.pi)) Bool.false 120447 65536 1 262144 BSN.log_two_pi_eq (@Enclosure.Real.IsNear.recentre' (Real.log (@HMul.hMul Real Real Real qz0 qz251 Real.pi)) Bool.false 963576 524288 2 524288 120447 65536 1 262144 (ep21 rfl rfl rfl rfl rfl rfl rfl rfl) rfl)

noncomputable abbrev qz545 := (@instHPow Complex Nat (@NPow.toPow Complex (@Monoid.toNPow Complex (@Semiring.toMonoid Complex Complex.instSemiring))))

noncomputable abbrev qz820 := (@instHAdd Complex Complex.instAdd)

noncomputable abbrev qz821 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (4 : Complex))

noncomputable abbrev qz822 := (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid))

noncomputable abbrev qz546 := (@HAdd.hAdd Complex Complex Complex qz820 (@HAdd.hAdd Complex Complex Complex qz820 qz821 (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I (@HDiv.hDiv Complex Complex Complex qz822 (↑(Enclosure.sfrac Bool.false 121891 1000)) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 4))

noncomputable abbrev qz254 := (@HPow.hPow Complex Nat Complex qz545 qz546 3)

noncomputable abbrev qz2 := qz254

noncomputable def ep22 := Enclosure.Complex.IsNear qz2 Bool.true 756499959931 16000000 0 1 Bool.true 1784565404900971 8000000000 0 1

noncomputable abbrev qz547 := (@instHMul Complex Complex.instMul)

noncomputable abbrev qz255 := qz547

noncomputable abbrev qz3 := qz255

noncomputable abbrev qz256 := qz545

noncomputable abbrev qz257 := qz546

noncomputable abbrev qz4 := (@HPow.hPow Complex Nat Complex qz256 qz257 2)

noncomputable abbrev qz5 := qz257

noncomputable def ep23 := @Enclosure.Complex.IsNear.of_eq qz2 (@HMul.hMul Complex Complex Complex qz3 qz4 qz5) Bool.true 756499959931 16000000 0 1 Bool.true 1784565404900971 8000000000

noncomputable def ep24 := @Enclosure.Complex.IsNear.mul qz4 qz5 Bool.true 756499959931 16000000 0 1 Bool.true 1784565404900971 8000000000 0

noncomputable abbrev qz6 := (Complex.re qz257)

noncomputable abbrev qz7 := (Complex.im qz257)

noncomputable def ep25 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re qz4) qz6) (@HMul.hMul Real Real Real qz0 (Complex.im qz4) qz7) 251347819977 16000000 0 1 252576069977 8000000

noncomputable def ep26 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re qz4) qz6 14785165881 4000000 0 1 17000 4000 0 1

noncomputable def ep27 := @Enclosure.Complex.IsNear.re_isNear qz4 Bool.true 14785165881 4000000 0 1 Bool.false 2072147 4000 0 1

noncomputable abbrev qz258 := (@HPow.hPow Complex Nat Complex qz545 qz546 1)

noncomputable abbrev qz8 := qz258

noncomputable def ep28 := @Enclosure.Complex.IsNear.of_eq qz4 (@HMul.hMul Complex Complex Complex qz3 qz8 qz5) Bool.true 14785165881 4000000 0 1 Bool.false 2072147 4000

noncomputable def ep29 := @Enclosure.Complex.IsNear.mul qz8 qz5 Bool.true 14785165881 4000000 0 1 Bool.false 2072147 4000 0

noncomputable abbrev qz9 := (Complex.re qz258)

noncomputable abbrev qz10 := (Complex.im qz258)

noncomputable def ep30 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz9 qz6) (@HMul.hMul Real Real Real qz0 qz10 qz7) 289 16 0 1 14857415881 4000000

noncomputable def ep31 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz6 17000 4000 0 1 17000 4000 0 1

noncomputable def ep32 := @Enclosure.Complex.IsNear.re_isNear qz8 Bool.false 17000 4000 0 1 Bool.false 243782 4000 0 1

noncomputable def ep33 := @Enclosure.Complex.IsNear.of_eq qz8 qz5 Bool.false 17000 4000 0 1 Bool.false 243782 4000 0

noncomputable abbrev qz259 := (Enclosure.sfrac Bool.false 121891 1000)

noncomputable abbrev qz11 := qz259

noncomputable abbrev qz260 := (Enclosure.sfrac Bool.false 243782 4000)

noncomputable abbrev qz548 := (Complex.mk (Enclosure.sfrac Bool.false 17000 4000) qz260)

noncomputable def ep34 := @Enclosure.Complex.IsNear.of_eq qz5 qz548 Bool.false 17000 4000 0 1 Bool.false 243782 4000 0 1 (BSN.w_shift_mk qz11 Bool.false 121891 1000 4 (@Eq.refl Real qz11) rfl)

noncomputable abbrev qz549 := (Enclosure.sfrac Bool.false 17000 4000)

noncomputable abbrev qz12 := (@ep33 1 (BSN.pow_one_c qz257) (ep34 (@Enclosure.Complex.IsNear.mk qz549 qz260 Bool.false 17000 4000 0 1 Bool.false 243782 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 17000 4000) (Enclosure.Real.IsNear.const Bool.false 243782 4000))))

noncomputable abbrev qz13 := (ep34 (@Enclosure.Complex.IsNear.mk qz549 qz260 Bool.false 17000 4000 0 1 Bool.false 243782 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 17000 4000) (Enclosure.Real.IsNear.const Bool.false 243782 4000)))

noncomputable abbrev qz823 := (@Enclosure.Complex.IsNear.re_isNear qz5 Bool.false 17000 4000 0 1 Bool.false 243782 4000 0 1 qz13)

noncomputable def ep35 := @ep31 289 16 0 1 (ep32 qz12) qz823

noncomputable def ep36 := @Enclosure.Real.IsNear.mulLit_ff qz10 qz7 243782 4000 0 1 243782 4000 0 1

noncomputable def ep37 := @Enclosure.Complex.IsNear.im_isNear qz8 Bool.false 17000 4000 0 1 Bool.false 243782 4000 0 1

noncomputable abbrev qz824 := (@Enclosure.Complex.IsNear.im_isNear qz5 Bool.false 17000 4000 0 1 Bool.false 243782 4000 0 1 qz13)

noncomputable def ep38 := @ep36 14857415881 4000000 0 1 (ep37 qz12) qz824

noncomputable def ep39 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz9 qz7) (@HMul.hMul Real Real Real qz0 qz10 qz6) 2072147 8000 0 1 2072147 8000

noncomputable def ep40 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz7 17000 4000 0 1 243782 4000 0 1

noncomputable def ep41 := @ep40 2072147 8000 0 1 (ep32 qz12) qz824

noncomputable def ep42 := @Enclosure.Real.IsNear.mulLit_ff qz10 qz6 243782 4000 0 1 17000 4000 0 1

noncomputable def ep43 := @ep42 2072147 8000 0 1 (ep37 qz12) qz823

noncomputable abbrev qz550 := (@ep28 0 1 (BSN.pow_succ_c qz5 1 2 rfl) (@ep29 1 (@ep30 0 1 236562654096 14785165881 4000000 0 1 (ep35 rfl) (ep38 rfl) rfl rfl) (@ep39 0 1 33154352000 2072147 4000 0 1 (ep41 rfl) (ep43 rfl) rfl rfl)))

noncomputable def ep44 := @ep26 251347819977 16000000 0 1 (ep27 qz550) qz823

noncomputable def ep45 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz4) qz7 2072147 4000 0 1 243782 4000 0 1

noncomputable def ep46 := @Enclosure.Complex.IsNear.im_isNear qz4 Bool.true 14785165881 4000000 0 1 Bool.false 2072147 4000 0 1

noncomputable def ep47 := @ep45 252576069977 8000000 0 1 (ep46 qz550) qz824

noncomputable def ep48 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re qz4) qz7) (@HMul.hMul Real Real Real qz0 (Complex.im qz4) qz6) 1802178654400971 8000000000 0 1 35226499 16000

noncomputable def ep49 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re qz4) qz7 14785165881 4000000 0 1 243782 4000 0 1

noncomputable def ep50 := @ep49 1802178654400971 8000000000 0 1 (ep27 qz550) qz824

noncomputable def ep51 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz4) qz6 2072147 4000 0 1 17000 4000 0 1

noncomputable def ep52 := @ep51 35226499 16000 0 1 (ep46 qz550) qz823

theorem EMRow40.d5 : ep22 := @ep23 0 1 (BSN.pow_succ_c qz5 2 3 rfl) (@ep24 1 (@ep25 0 1 6051999679448000000 756499959931 16000000 0 1 (ep44 rfl) (ep47 rfl) rfl rfl) (@ep48 0 1 28553046478415536000 1784565404900971 8000000000 0 1 (ep50 rfl) (ep52 rfl) rfl rfl))

noncomputable def ep53 := nat_lit 8589934592000000000000000

noncomputable def ep54 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 ep0 ep53 ep2 ep53 1200336 1048576 1 378608 1200336 1048576 1 378608 600168 524288 2 524288 BSN.pi_near_15 rfl rfl rfl

noncomputable def ep55 := nat_lit 17179869184000000000000000

noncomputable def ep56 := nat_lit 18396140817044028275299783

noncomputable def ep57 := nat_lit 35576010001044028275299783

noncomputable def ep58 := nat_lit 145019262663961446558303139663424756232419223153299357158415217874016130572233056993847515999529612750616182853355499335896178729185698845314776375864537073527142908641610750276034469165612529925303649396973267518946591078603565291376312767403717761600170009932259137778521478520425507632472584532570900560707662248426541531715360699177249902784721815296292248142738824858695953661559845440650653128788875447728828657762006237171740033404723254477174341920697506370253193455781322964835857351124092897592956162654178130575

noncomputable def ep59 := nat_lit 15500762873619990602332184736899274490522931101512051618692838888825382235673431503644115344741331161500627469184702974962114537943617674254904297224139410345221262767191485292268260077615645253784097850065864022184521411511133693085443040736512010941548648374196772723338837137976260321103066698629790037694560548409922339907589559883712609967105556007429010014773911317423638534096849366294542840133852248768895750397896505791271178551667935288585787166713880920071720072716082683081155281219708172458141800988558163320

noncomputable def ep60 := nat_lit 12900190794487083783367107939442176642390171280542213571554777169279725287102813254708993369099729304728646904879886535518616983985412662170766446331701281703998252143668221340329975389245922410714088123244705567402747658401492589451585970559635763980329972215329212888079422466283203384882259392047898400615815810081169907384366653346471604103896809335921621947903075223769953790093549808584241881353287841076643853121427928248525828402335494512605306631304432120211393210317325496757155861061354331245840675149075

noncomputable def ep61 := BSN.log_dyadic_bound ep56 ep57 11 10 ep58 1048576 378608 ep59 ep60 1200336 ep5 ep55 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep56) (BSN.artanhQ ep57) 0 10 ep59 ep58 ep60 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep62 := nat_lit 18396140817044045455168967

noncomputable def ep63 := nat_lit 35576010001044045455168967

noncomputable def ep64 := nat_lit 145019262663962847171784895425483977818796535899227200426399035286881207006285364467913811844950531107314785650583974625982406238691319033447632878979985852280879486690814033867010958364699188952871572448188560932645032521756218245629809291975913196623825614492380080480004685076434733043183791438169545293975334857826316990371107134320667652578346815517853870648072772035977941843998949310557583393428557296298890786965786350523173236912472938174255438182435383147950274229549088258679583524155427309880956162654178130575

noncomputable def ep65 := nat_lit 15500762873620157189619721156942591192100275120160672416764593300158228469749443299607348495591439275767946573253526107895503597951484257520435868240203420954375895980141891044871083424251900562230440202302413072793440172565998181227591194192658878334739610458454844032013325963992941389843551995646587189684848765634635122388286241104146031552341815777883628509454807838726994150833304950745987647656768534710890974432620160470644835720379148964170536679305861738540146791997074363921127776563807649880221800988558163320

noncomputable def ep66 := nat_lit 12900190794487324729109480814509220959173684627296055849229843377126536688487849343376525559792931631054411655715865486295286288812423905434305314401904993536755333953308594664509631000767632482919425633906965368325056855874260596615770736441041599390097968820060635361729170158825410327022636428624381203910573184452046894301676992229743752846881064485858738985580654099214803581683226335297196686880535448467637789069028262446657986458573827723305156755787640135484017403116612632808333639900906331245840675149075

noncomputable def ep67 := BSN.log_dyadic_bound ep62 ep63 11 10 ep64 1048576 378608 ep65 ep66 1200336 ep14 ep55 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep62) (BSN.artanhQ ep63) 0 10 ep65 ep64 ep66 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep68 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 600168 524288 2 524288 75021 65536 1 262144 (ep54 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep53 1200336 1048576 1 378608 Bool.false (BSN.logfrac_isNear ep5 ep55 1 ep0 ep53 1200336 1048576 378608 rfl rfl rfl (ep61 rfl))) (BSN.isNear_log_sfrac ep2 ep53 1200336 1048576 1 378608 Bool.false (BSN.logfrac_isNear ep14 ep55 1 ep2 ep53 1200336 1048576 378608 rfl rfl rfl (ep67 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl

theorem EMRow40.d6 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 75021 65536 1 262144 := ep68

noncomputable abbrev qz551 := qz820

noncomputable abbrev qz552 := (@HDiv.hDiv Complex Complex Complex qz822 (1 : Complex) (2 : Complex))

noncomputable abbrev qz261 := (@HAdd.hAdd Complex Complex Complex qz551 qz552 (@HMul.hMul Complex Complex Complex qz547 Complex.I ↑(Enclosure.sfrac Bool.false 121891 1000)))

noncomputable abbrev qz14 := qz261

noncomputable abbrev qz262 := qz551

noncomputable abbrev qz15 := qz262

noncomputable abbrev qz16 := (@instHPow Complex Complex Complex.instPow)

noncomputable abbrev qz17 := (@Neg.neg Complex Complex.instNeg qz261)

noncomputable abbrev qz825 := (@Nat.cast Complex Complex.instNatCast 8)

noncomputable def ep69 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 9) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz14 8) (@HPow.hPow Complex Complex Complex qz16 qz825 qz17)) Bool.false 454985951451 1099511627776 57127195223025 26017743648063488 Bool.true 449240310407 1099511627776 57197104669639 26017743648063488

noncomputable def ep70 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz14 8) (@HPow.hPow Complex Complex Complex qz16 qz825 qz17) Bool.false 331888401381 549755813888 25563134502561 13008871824031744 Bool.true 121335986177 1099511627776 51188575600825 26017743648063488 Bool.true

noncomputable abbrev qz826 := (@Nat.cast Complex Complex.instNatCast 7)

noncomputable def ep71 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 8) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz14 7) (@HPow.hPow Complex Complex Complex qz16 qz826 qz17)) Bool.false 331888401381 549755813888 25563134502561 13008871824031744 Bool.true 121335986177 1099511627776 51188575600825 26017743648063488

noncomputable def ep72 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz14 7) (@HPow.hPow Complex Complex Complex qz16 qz826 qz17) Bool.false 332201498131 549755813888 22367289585411 13008871824031744 Bool.true 536912076727 1099511627776 44772110747503 26017743648063488 Bool.true

noncomputable abbrev qz827 := (@Nat.cast Complex Complex.instNatCast 6)

noncomputable def ep73 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 7) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz14 6) (@HPow.hPow Complex Complex Complex qz16 qz827 qz17)) Bool.false 332201498131 549755813888 22367289585411 13008871824031744 Bool.true 536912076727 1099511627776 44772110747503 26017743648063488

noncomputable def ep74 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz14 6) (@HPow.hPow Complex Complex Complex qz16 qz827 qz17) Bool.false 159534231245 274877906944 9454810034657 6504435912015872 Bool.true 985015756189 1099511627776 37833453721849 26017743648063488 Bool.false

noncomputable abbrev qz18 := (@Nat.cast Complex Complex.instNatCast 5)

noncomputable def ep75 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 6) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz14 5) (@HPow.hPow Complex Complex Complex qz16 qz18 qz17)) Bool.false 159534231245 274877906944 9454810034657 6504435912015872 Bool.true 985015756189 1099511627776 37833453721849 26017743648063488

noncomputable def ep76 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz14 5) (@HPow.hPow Complex Complex Complex qz16 qz18 qz17) Bool.false 553119115817 1099511627776 30241168530617 26017743648063488 Bool.true 250352797259 549755813888 15117616723973 13008871824031744 Bool.false

noncomputable abbrev qz553 := (@Nat.cast Complex Complex.instNatCast 4)

noncomputable abbrev qz263 := qz553

noncomputable abbrev qz19 := qz263

noncomputable def ep77 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 5) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz14 4) (@HPow.hPow Complex Complex Complex qz16 qz19 qz17)) Bool.false 553119115817 1099511627776 30241168530617 26017743648063488 Bool.true 250352797259 549755813888 15117616723973 13008871824031744

noncomputable def ep78 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz14 4) (@HPow.hPow Complex Complex Complex qz16 qz19 qz17) Bool.false 7623460711 68719476736 1359623394399 1626108978003968 Bool.true 210449844175 274877906944 5438025878401 6504435912015872 Bool.false

noncomputable abbrev qz554 := (@Nat.cast Complex Complex.instNatCast 3)

noncomputable def ep79 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 4) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz14 3) (@HPow.hPow Complex Complex Complex qz16 qz554 qz17)) Bool.false 7623460711 68719476736 1359623394399 1626108978003968 Bool.true 210449844175 274877906944 5438025878401 6504435912015872

noncomputable def ep80 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz14 3) (@HPow.hPow Complex Complex Complex qz16 qz554 qz17) Bool.false 91300322039 274877906944 2995272168473 6504435912015872 Bool.true 127720813935 549755813888 5982902962671 13008871824031744 Bool.true

noncomputable abbrev qz555 := (@Nat.cast Complex Complex.instNatCast 2)

noncomputable def ep81 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 3) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz14 2) (@HPow.hPow Complex Complex Complex qz16 qz555 qz17)) Bool.false 91300322039 274877906944 2995272168473 6504435912015872 Bool.true 127720813935 549755813888 5982902962671 13008871824031744

noncomputable def ep82 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz14 2) (@HPow.hPow Complex Complex Complex qz16 qz555 qz17) Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.true

noncomputable abbrev qz828 := (Enclosure.sfrac Bool.false 0 1)

noncomputable abbrev qz264 := qz828

noncomputable def ep83 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz264) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz14)

noncomputable abbrev qz265 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2)))

noncomputable abbrev qz266 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 2 1)))

noncomputable def ep84 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz555 qz17) (Complex.mk (@HMul.hMul Real Real Real qz0 qz265 (Real.cos qz266)) (@HMul.hMul Real Real Real qz0 qz265 (@Neg.neg Real Real.instNeg (Real.sin qz266)))) Bool.true 183577584905 274877906944 2995272168473 6504435912015872 Bool.true 127720813935 549755813888 5982902962671 13008871824031744 (BSN.cpow_neg_s_mk qz11 121891 1000 2 (@Eq.refl Real qz11) rfl)

noncomputable abbrev qz267 := (@Nat.cast Real Real.instNatCast 1)

noncomputable def ep85 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 2)) 1482911 1048576 1 1048576 370727 370728 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 2)) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2) qz267)) Bool.false 1482911 1048576 1 1048576 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2) qz267)) Bool.false 1482911 1048576 1 1048576 1482911 1048576 1 1048576 (BSN.sqrt_enclosure 2 1 741455 741456 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep86 := BSN.log_dyadic_bound 1 3 6 5 613814355 524288 189304 24381081 945 363408 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 1) (BSN.artanhQ 3) 0 5 24381081 613814355 945 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep87 := nat_lit 3194939705726343685706566568366050159169921218616892521677388970403911246329985

noncomputable def ep88 := nat_lit 164135286493895707012911871249815109382010203263545499525931125331216861264609280

noncomputable def ep89 := nat_lit 2464067980215566598231588645392985899451260949740948910662489129479031273601

noncomputable def ep90 := nat_lit 8363709785886741592834347011723304630179253531030376020442565178181563404040321

noncomputable def ep91 := nat_lit 3009146919054754628570050972913277005336853726498334157975403964405642456517836800

noncomputable abbrev qz268 := (BSN.sinEvenQ 2147483648)

noncomputable abbrev qz269 := (BSN.sinOddQ 2147483648)

noncomputable def ep92 := BSN.sin_dyadic_bound_f 2654340207 2147483648 3 2 1048576 378978 ep87 ep88 ep89 ep90 ep91 ep89 990364 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2654340207) qz268 0 2 ep87 ep88 ep89 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2654340207) qz269 0 2 ep90 ep91 ep89 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz270 := (@Nat.cast Real Real.instNatCast 1048576)

noncomputable abbrev qz271 := (Real.log (Enclosure.sfrac Bool.false 2 1))

noncomputable abbrev qz272 := (Enclosure.Real.IsNear.const Bool.false 121891 1000)

noncomputable abbrev qz273 := (@Nat.cast Real Real.instNatCast 151115727451828646838272)

noncomputable abbrev qz556 := (BSN.isNear_log_sfrac 2 1 363408 524288 1 189304 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 363408 524288 189304 rfl rfl rfl (ep86 rfl)))

noncomputable abbrev qz829 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 88592329) qz270)

noncomputable def ep93 := @Enclosure.Real.IsNear.cos_image qz266 qz829 Bool.false 88592329 1048576 169 262144 Bool.true 990364 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz266 Bool.false 2768510283 32768000 121891 189304000 88592329 1048576 169 262144 (@Enclosure.Real.IsNear.mulLit_ff qz11 qz271 121891 1000 0 1 363408 524288 1 189304 2768510283 32768000 121891 189304000 qz272 qz556 rfl) rfl) (Enclosure.sfrac_false_div 88592329 1048576) (BSN.cos_reduce1 qz829 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 186782586992729310363648) qz273) 226375608064910080 72057594037927936 Bool.false 990364 1048576 13 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q1 88592329 1048576 226375608064910080 72057594037927936 13 186782586992729310363648 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 990364 1048576 186782586992729310363648 151115727451828646838272 2654340207 2147483648 378978 378608 (ep92 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep94 := nat_lit 1776061644505842299436195466267980304383045681875936267114399423170830261860481

noncomputable def ep95 := nat_lit 18237254054877300779212430138868345486890022584838388836214569481246317918289920

noncomputable def ep96 := nat_lit 5323256797557095765112123221513154941350234523728326903521873291253532723034241

noncomputable def ep97 := nat_lit 820676432469478535064559356249075546910051016317727497629655626656084306323046400

noncomputable abbrev qz274 := (BSN.cosEvenQ 2147483648)

noncomputable abbrev qz275 := (BSN.cosOddQ 2147483648)

noncomputable def ep98 := BSN.cos_dyadic_bound_f 2654340207 2147483648 3 2 1048576 378978 ep94 ep95 ep89 ep96 ep97 ep89 344514 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2654340207) qz274 0 2 ep94 ep95 ep89 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2654340207) qz275 0 2 ep96 ep97 ep89 rfl rfl rfl rfl) rfl rfl

noncomputable def ep99 := @Enclosure.Real.IsNear.sin_image qz266 qz829 Bool.false 88592329 1048576 169 262144 Bool.false 344514 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz266 Bool.false 2768510283 32768000 121891 189304000 88592329 1048576 169 262144 (@Enclosure.Real.IsNear.mulLit_ff qz11 qz271 121891 1000 0 1 363408 524288 1 189304 2768510283 32768000 121891 189304000 qz272 qz556 rfl) rfl) (Enclosure.sfrac_false_div 88592329 1048576) (BSN.sin_reduce1 qz829 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 186782586992729310363648) qz273) 226375608064910080 72057594037927936 Bool.false 344514 1048576 13 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q1 88592329 1048576 226375608064910080 72057594037927936 13 186782586992729310363648 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 344514 1048576 186782586992729310363648 151115727451828646838272 2654340207 2147483648 378978 378608 (ep98 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz557 := (@Enclosure.Real.IsNear.recentre' qz265 Bool.false 741455 1048576 1 1048576 741455 1048576 1 1048576 (ep85 rfl rfl) rfl)

noncomputable def ep100 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz265 (Real.cos qz266)) (@HMul.hMul Real Real Real qz0 qz265 (@Neg.neg Real Real.instNeg (Real.sin qz266))) Bool.true 183577584905 274877906944 2995272168473 6504435912015872 Bool.true 127720813935 549755813888 5982902962671 13008871824031744 (@Enclosure.Real.IsNear.mulLit_ft qz265 (Real.cos qz266) 741455 1048576 1 1048576 247591 262144 4031815 6203113472 183577584905 274877906944 2995272168473 6504435912015872 qz557 (@Enclosure.Real.IsNear.recentre' (Real.cos qz266) Bool.true 990364 1048576 32254520 49624907776 247591 262144 4031815 6203113472 (ep93 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz265 (@Neg.neg Real Real.instNeg (Real.sin qz266)) 741455 1048576 1 1048576 172257 524288 4031815 6203113472 127720813935 549755813888 5982902962671 13008871824031744 qz557 (@Enclosure.Real.IsNear.neg (Real.sin qz266) Bool.false 172257 524288 4031815 6203113472 (@Enclosure.Real.IsNear.recentre' (Real.sin qz266) Bool.false 344514 1048576 32254520 49624907776 172257 524288 4031815 6203113472 (ep99 rfl rfl) rfl)) rfl)

noncomputable abbrev qz830 := (Enclosure.Real.IsNear.const Bool.false 0 1)

noncomputable abbrev qz276 := qz830

noncomputable def ep101 := @ep82 183577584905 274877906944 2995272168473 6504435912015872 Bool.true 127720813935 549755813888 5982902962671 13008871824031744 Bool.false 91300322039 91300322039 274877906944 2995272168473 6504435912015872 Bool.true 127720813935 127720813935 549755813888 5982902962671 13008871824031744 (ep83 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz264 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz276)) (ep84 ep100) rfl rfl

noncomputable abbrev qz277 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 3)))

noncomputable abbrev qz278 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 3 1)))

noncomputable def ep102 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz554 qz17) (Complex.mk (@HMul.hMul Real Real Real qz0 qz277 (Real.cos qz278)) (@HMul.hMul Real Real Real qz0 qz277 (@Neg.neg Real Real.instNeg (Real.sin qz278)))) Bool.true 60806479195 274877906944 2443221409123 6504435912015872 Bool.true 293178874415 549755813888 4893148794131 13008871824031744 (BSN.cpow_neg_s_mk qz11 121891 1000 3 (@Eq.refl Real qz11) rfl)

noncomputable def ep103 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 3)) 1816187 1048576 1 1048576 302697 302698 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 3)) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3) qz267)) Bool.false 1816187 1048576 1 1048576 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3) qz267)) Bool.false 1816187 1048576 1 1048576 1816187 1048576 1 1048576 (BSN.sqrt_enclosure 3 1 908093 908094 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep104 := BSN.log_dyadic_bound 1 2 10 9 171633298636800 524288 189304 16925142283965 34459425 575989 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP 1) (BSN.artanhQ 2) 0 9 16925142283965 171633298636800 34459425 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep105 := nat_lit 508396706287251244427448708483152656

noncomputable def ep106 := nat_lit 2552117751907038475975309555738261585920

noncomputable def ep107 := nat_lit 17864824263349269331827166890167831101440

noncomputable def ep108 := BSN.sin_dyadic_bound_f 844404778 2147483648 2 1 1048576 378978 ep105 ep106 ep105 ep105 ep107 ep105 401764 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 844404778) qz268 0 1 ep105 ep106 ep105 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 844404778) qz269 0 1 ep105 ep107 ep105 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz279 := (@Nat.cast Real Real.instNatCast 524288)

noncomputable abbrev qz280 := (Real.log (Enclosure.sfrac Bool.false 3 1))

noncomputable abbrev qz281 := (@Nat.cast Real Real.instNatCast 75557863725914323419136)

noncomputable abbrev qz558 := (BSN.isNear_log_sfrac 3 1 575989 524288 1 189304 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 575989 524288 189304 rfl rfl rfl (ep104 rfl)))

noncomputable abbrev qz831 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 70207875) qz279)

noncomputable def ep109 := @Enclosure.Real.IsNear.cos_image qz278 qz831 Bool.false 70207875 524288 169 262144 Bool.true 401764 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz278 Bool.false 70207875199 524288000 121891 189304000 70207875 524288 169 262144 (@Enclosure.Real.IsNear.mulLit_ff qz11 qz280 121891 1000 0 1 575989 524288 1 189304 70207875199 524288000 121891 189304000 qz272 qz558 rfl) rfl) (Enclosure.sfrac_false_div 70207875 524288) (BSN.cos_reduce1 qz831 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 29709851934655617433600) qz281) 226375608064910080 72057594037927936 Bool.false 401764 1048576 21 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q1 70207875 524288 226375608064910080 72057594037927936 21 29709851934655617433600 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 401764 1048576 29709851934655617433600 75557863725914323419136 844404778 2147483648 378978 378608 (ep108 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep110 := nat_lit 510423550381407695195061911147652317184

noncomputable def ep111 := nat_lit 7656353255721115427925928667214784757760

noncomputable def ep112 := BSN.cos_dyadic_bound_f 844404778 2147483648 2 1 1048576 378978 ep105 ep110 ep105 ep105 ep111 ep105 968554 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 844404778) qz274 0 1 ep105 ep110 ep105 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 844404778) qz275 0 1 ep105 ep111 ep105 rfl rfl rfl rfl) rfl rfl

noncomputable def ep113 := @Enclosure.Real.IsNear.sin_image qz278 qz831 Bool.false 70207875 524288 169 262144 Bool.false 968554 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz278 Bool.false 70207875199 524288000 121891 189304000 70207875 524288 169 262144 (@Enclosure.Real.IsNear.mulLit_ff qz11 qz280 121891 1000 0 1 575989 524288 1 189304 70207875199 524288000 121891 189304000 qz272 qz558 rfl) rfl) (Enclosure.sfrac_false_div 70207875 524288) (BSN.sin_reduce1 qz831 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 29709851934655617433600) qz281) 226375608064910080 72057594037927936 Bool.false 968554 1048576 21 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q1 70207875 524288 226375608064910080 72057594037927936 21 29709851934655617433600 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 968554 1048576 29709851934655617433600 75557863725914323419136 844404778 2147483648 378978 378608 (ep112 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz559 := (@Enclosure.Real.IsNear.recentre' qz277 Bool.false 605395 1048576 1 1048576 605395 1048576 1 1048576 (ep103 rfl rfl) rfl)

noncomputable def ep114 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz277 (Real.cos qz278)) (@HMul.hMul Real Real Real qz0 qz277 (@Neg.neg Real Real.instNeg (Real.sin qz278))) Bool.true 60806479195 274877906944 2443221409123 6504435912015872 Bool.true 293178874415 549755813888 4893148794131 13008871824031744 (@Enclosure.Real.IsNear.mulLit_ft qz277 (Real.cos qz278) 605395 1048576 1 1048576 100441 262144 4031815 6203113472 60806479195 274877906944 2443221409123 6504435912015872 qz559 (@Enclosure.Real.IsNear.recentre' (Real.cos qz278) Bool.true 401764 1048576 32254520 49624907776 100441 262144 4031815 6203113472 (ep109 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz277 (@Neg.neg Real Real.instNeg (Real.sin qz278)) 605395 1048576 1 1048576 484277 524288 4031815 6203113472 293178874415 549755813888 4893148794131 13008871824031744 qz559 (@Enclosure.Real.IsNear.neg (Real.sin qz278) Bool.false 484277 524288 4031815 6203113472 (@Enclosure.Real.IsNear.recentre' (Real.sin qz278) Bool.false 968554 1048576 32254520 49624907776 484277 524288 4031815 6203113472 (ep113 rfl rfl) rfl)) rfl)

noncomputable def ep115 := @ep80 60806479195 274877906944 2443221409123 6504435912015872 Bool.true 293178874415 549755813888 4893148794131 13008871824031744 Bool.false 8382083695637992308736 7623460711 68719476736 1359623394399 1626108978003968 Bool.true 231392050734059801804800 210449844175 274877906944 5438025878401 6504435912015872 (ep81 (BSN.head_sum_c_succ qz14 2 3 rfl rfl) (ep101 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep102 ep114) rfl rfl

noncomputable abbrev qz282 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 4)))

noncomputable abbrev qz283 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 4 1)))

noncomputable def ep116 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz19 qz17) (Complex.mk (@HMul.hMul Real Real Real qz0 qz282 (Real.cos qz283)) (@HMul.hMul Real Real Real qz0 qz282 (@Neg.neg Real Real.instNeg (Real.sin qz283)))) Bool.false 431143744441 1099511627776 8487194220233 26017743648063488 Bool.false 170546891091 549755813888 4241564967171 13008871824031744 (BSN.cpow_neg_s_mk qz11 121891 1000 4 (@Eq.refl Real qz11) rfl)

noncomputable def ep117 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 4)) 2097153 1048576 1 1048576 262143 262144 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 4)) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4) qz267)) Bool.false 2097153 1048576 1 1048576 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4) qz267)) Bool.false 2097153 1048576 1 1048576 2097153 1048576 1 1048576 (BSN.sqrt_enclosure 4 1 1048576 1048577 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep118 := nat_lit 318077276165597140789031982421875

noncomputable def ep119 := nat_lit 49379992292270016474244603430625

noncomputable def ep120 := nat_lit 20095619060363156210525625

noncomputable def ep121 := BSN.log_dyadic_bound 3 5 14 13 ep118 524288 189304 ep119 ep120 726817 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base13 (BSN.artanhP 3) (BSN.artanhQ 5) 0 13 ep119 ep118 ep120 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep122 := nat_lit 903534009143033965062466672133268118836840641319844201463011780069438431232000

noncomputable def ep123 := nat_lit 197286256952053160915495520879656289210970046507706722286439046088826617856

noncomputable def ep124 := nat_lit 2366079179530023727188787624743801820104431537667150907233709951250099695845376

noncomputable def ep125 := BSN.sin_dyadic_bound_f 1935918652 2147483648 3 2 1048576 378978 ep122 ep88 ep123 ep124 ep91 ep123 822343 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1935918652) qz268 0 2 ep122 ep88 ep123 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1935918652) qz269 0 2 ep124 ep91 ep123 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz284 := (Real.log (Enclosure.sfrac Bool.false 4 1))

noncomputable abbrev qz560 := (BSN.isNear_log_sfrac 4 1 726817 524288 1 189304 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 726817 524288 189304 rfl rfl rfl (ep121 rfl)))

noncomputable abbrev qz832 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 177184901) qz270)

noncomputable def ep126 := @Enclosure.Real.IsNear.cos_image qz283 qz832 Bool.false 177184901 1048576 677 1048576 Bool.false 822343 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz283 Bool.false 88592450947 524288000 121891 189304000 177184901 1048576 677 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz11 qz284 121891 1000 0 1 726817 524288 1 189304 88592450947 524288000 121891 189304000 qz272 qz560 rfl) rfl) (Enclosure.sfrac_false_div 177184901 1048576) (BSN.cos_reduce3 qz832 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 136228164373889901658112) qz273) 226375608064910080 72057594037927936 Bool.false 822343 1048576 26 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q3 177184901 1048576 226375608064910080 72057594037927936 26 136228164373889901658112 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 822343 1048576 136228164373889901658112 151115727451828646838272 1935918652 2147483648 378978 378608 (ep125 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep127 := nat_lit 502051021193664226439555038083317691037894120753916870467133850725727495847936

noncomputable def ep128 := nat_lit 1505758491067088572996834123208193760535260422168735197956828674085004834308096

noncomputable def ep129 := BSN.cos_dyadic_bound_f 1935918652 2147483648 3 2 1048576 378978 ep127 ep95 ep123 ep128 ep97 ep123 650586 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1935918652) qz274 0 2 ep127 ep95 ep123 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1935918652) qz275 0 2 ep128 ep97 ep123 rfl rfl rfl rfl) rfl rfl

noncomputable def ep130 := @Enclosure.Real.IsNear.sin_image qz283 qz832 Bool.false 177184901 1048576 677 1048576 Bool.true 650586 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz283 Bool.false 88592450947 524288000 121891 189304000 177184901 1048576 677 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz11 qz284 121891 1000 0 1 726817 524288 1 189304 88592450947 524288000 121891 189304000 qz272 qz560 rfl) rfl) (Enclosure.sfrac_false_div 177184901 1048576) (BSN.sin_reduce3 qz832 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 136228164373889901658112) qz273) 226375608064910080 72057594037927936 Bool.false 650586 1048576 26 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q3 177184901 1048576 226375608064910080 72057594037927936 26 136228164373889901658112 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 650586 1048576 136228164373889901658112 151115727451828646838272 1935918652 2147483648 378978 378608 (ep129 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz561 := (@Enclosure.Real.IsNear.recentre' qz282 Bool.false 524287 1048576 1 1048576 524287 1048576 1 1048576 (ep117 rfl rfl) rfl)

noncomputable def ep131 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz282 (Real.cos qz283)) (@HMul.hMul Real Real Real qz0 qz282 (@Neg.neg Real Real.instNeg (Real.sin qz283))) Bool.false 431143744441 1099511627776 8487194220233 26017743648063488 Bool.false 170546891091 549755813888 4241564967171 13008871824031744 (@Enclosure.Real.IsNear.mulLit_ff qz282 (Real.cos qz283) 524287 1048576 1 1048576 822343 1048576 16150923 24812453888 431143744441 1099511627776 8487194220233 26017743648063488 qz561 (@Enclosure.Real.IsNear.recentre' (Real.cos qz283) Bool.false 822343 1048576 129207384 198499631104 822343 1048576 16150923 24812453888 (ep126 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz282 (@Neg.neg Real Real.instNeg (Real.sin qz283)) 524287 1048576 1 1048576 325293 524288 16150923 24812453888 170546891091 549755813888 4241564967171 13008871824031744 qz561 (@Enclosure.Real.IsNear.neg (Real.sin qz283) Bool.true 325293 524288 16150923 24812453888 (@Enclosure.Real.IsNear.recentre' (Real.sin qz283) Bool.true 650586 1048576 129207384 198499631104 325293 524288 16150923 24812453888 (ep130 rfl rfl) rfl)) rfl)

noncomputable def ep132 := @ep78 431143744441 1099511627776 8487194220233 26017743648063488 Bool.false 170546891091 549755813888 4241564967171 13008871824031744 Bool.false 38010056211623221133312 553119115817 1099511627776 30241168530617 26017743648063488 Bool.true 68816452908129500266496 250352797259 549755813888 15117616723973 13008871824031744 (ep79 (BSN.head_sum_c_succ qz14 3 4 rfl rfl) (ep115 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep116 ep131) rfl rfl

noncomputable abbrev qz833 := (@Nat.cast Real Real.instNatCast 5)

noncomputable abbrev qz285 := (@Inv.inv Real Real.instInv (Real.sqrt qz833))

noncomputable abbrev qz286 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 5 1)))

noncomputable def ep133 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz18 qz17) (Complex.mk (@HMul.hMul Real Real Real qz0 qz285 (Real.cos qz286)) (@HMul.hMul Real Real Real qz0 qz285 (@Neg.neg Real Real.instNeg (Real.sin qz286)))) Bool.false 85017809163 1099511627776 7578071608011 26017743648063488 Bool.true 484310161671 1099511627776 7598220273903 26017743648063488 (BSN.cpow_neg_s_mk qz11 121891 1000 5 (@Eq.refl Real qz11) rfl)

noncomputable def ep134 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz833) 2344687 1048576 1 1048576 234468 234469 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz833) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz833 qz267)) Bool.false 2344687 1048576 1 1048576 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz833 qz267)) Bool.false 2344687 1048576 1 1048576 2344687 1048576 1 1048576 (BSN.sqrt_enclosure 5 1 1172343 1172344 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep135 := nat_lit 3696382175741467532940033205863946875

noncomputable def ep136 := nat_lit 765440954430599474856563326857688500

noncomputable def ep137 := nat_lit 108794268166472120024432640000

noncomputable def ep138 := BSN.log_dyadic_bound 2 3 18 17 ep135 524288 189304 ep136 ep137 843808 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.artanhP 2) (BSN.artanhQ 3) 0 17 8 307084260767580 1483365253795425 132843110400 1663129201793174588340 2491889415829100854875 818968088287641600 ep136 ep135 ep137 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.artanhP 2) (BSN.artanhQ 3) 0 8 307084260767580 1483365253795425 132843110400 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.artanhP 2) (BSN.artanhQ 3) 8 17 1663129201793174588340 2491889415829100854875 818968088287641600 rfl rfl rfl rfl)) rfl rfl

noncomputable def ep139 := nat_lit 2900983528644570663247712150391455483546057197348180811335344598086321435650881

noncomputable def ep140 := nat_lit 6562448931244795662149371340301105140789758321064969719838005094959669128001

noncomputable def ep141 := nat_lit 8689825688071222398418837708493764240356592075402412494566357784069044968696641

noncomputable def ep142 := BSN.cos_dyadic_bound_f 3000082807 2147483648 3 2 1048576 378978 ep139 ep95 ep140 ep141 ep97 ep140 181299 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3000082807) qz274 0 2 ep139 ep95 ep140 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3000082807) qz275 0 2 ep141 ep97 ep140 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz287 := (Real.log (Enclosure.sfrac Bool.false 5 1))

noncomputable abbrev qz562 := (BSN.isNear_log_sfrac 5 1 843808 524288 1 189304 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 843808 524288 189304 rfl rfl rfl (ep138 rfl rfl)))

noncomputable abbrev qz834 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 205705201) qz270)

noncomputable def ep143 := @Enclosure.Real.IsNear.cos_image qz286 qz834 Bool.false 205705201 1048576 677 1048576 Bool.false 181299 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz286 Bool.false 3214143779 16384000 121891 189304000 205705201 1048576 677 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz11 qz287 121891 1000 0 1 843808 524288 1 189304 3214143779 16384000 121891 189304000 qz272 qz562 rfl) rfl) (Enclosure.sfrac_false_div 205705201 1048576) (BSN.cos_reduce0 qz834 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 211112059615112543076352) qz273) 226375608064910080 72057594037927936 Bool.false 181299 1048576 31 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q0 205705201 1048576 226375608064910080 72057594037927936 31 211112059615112543076352 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 181299 1048576 211112059615112543076352 151115727451828646838272 3000082807 2147483648 378978 378608 (ep142 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep144 := nat_lit 5216520392415231357316162373632378986270271148569873484627749872479410848869185

noncomputable def ep145 := nat_lit 13651690396151209599994088186867171746194193399448896794478654800625665139878721

noncomputable def ep146 := BSN.sin_dyadic_bound_f 3000082807 2147483648 3 2 1048576 378978 ep144 ep88 ep140 ep145 ep91 ep140 1032783 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3000082807) qz268 0 2 ep144 ep88 ep140 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3000082807) qz269 0 2 ep145 ep91 ep140 rfl rfl rfl rfl) rfl rfl

noncomputable def ep147 := @Enclosure.Real.IsNear.sin_image qz286 qz834 Bool.false 205705201 1048576 677 1048576 Bool.false 1032783 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz286 Bool.false 3214143779 16384000 121891 189304000 205705201 1048576 677 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz11 qz287 121891 1000 0 1 843808 524288 1 189304 3214143779 16384000 121891 189304000 qz272 qz562 rfl) rfl) (Enclosure.sfrac_false_div 205705201 1048576) (BSN.sin_reduce0 qz834 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 211112059615112543076352) qz273) 226375608064910080 72057594037927936 Bool.false 1032783 1048576 31 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q0 205705201 1048576 226375608064910080 72057594037927936 31 211112059615112543076352 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1032783 1048576 211112059615112543076352 151115727451828646838272 3000082807 2147483648 378978 378608 (ep146 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz563 := (@Enclosure.Real.IsNear.recentre' qz285 Bool.false 468937 1048576 1 1048576 468937 1048576 1 1048576 (ep134 rfl rfl) rfl)

noncomputable def ep148 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz285 (Real.cos qz286)) (@HMul.hMul Real Real Real qz0 qz285 (@Neg.neg Real Real.instNeg (Real.sin qz286))) Bool.false 85017809163 1099511627776 7578071608011 26017743648063488 Bool.true 484310161671 1099511627776 7598220273903 26017743648063488 (@Enclosure.Real.IsNear.mulLit_ff qz285 (Real.cos qz286) 468937 1048576 1 1048576 181299 1048576 16150923 24812453888 85017809163 1099511627776 7578071608011 26017743648063488 qz563 (@Enclosure.Real.IsNear.recentre' (Real.cos qz286) Bool.false 181299 1048576 129207384 198499631104 181299 1048576 16150923 24812453888 (ep143 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz285 (@Neg.neg Real Real.instNeg (Real.sin qz286)) 468937 1048576 1 1048576 1032783 1048576 16150923 24812453888 484310161671 1099511627776 7598220273903 26017743648063488 qz563 (@Enclosure.Real.IsNear.neg (Real.sin qz286) Bool.false 1032783 1048576 16150923 24812453888 (@Enclosure.Real.IsNear.recentre' (Real.sin qz286) Bool.false 1032783 1048576 129207384 198499631104 1032783 1048576 16150923 24812453888 (ep147 rfl rfl) rfl)) rfl)

noncomputable def ep149 := @ep76 85017809163 1099511627776 7578071608011 26017743648063488 Bool.true 484310161671 1099511627776 7598220273903 26017743648063488 Bool.false 701638969128730996244480 159534231245 274877906944 9454810034657 6504435912015872 Bool.true 541518138736187468152832 985015756189 1099511627776 37833453721849 26017743648063488 (ep77 (BSN.head_sum_c_succ qz14 4 5 rfl rfl) (ep132 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep133 ep148) rfl rfl

noncomputable abbrev qz835 := (@Nat.cast Real Real.instNatCast 6)

noncomputable abbrev qz288 := (@Inv.inv Real Real.instInv (Real.sqrt qz835))

noncomputable abbrev qz289 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 6 1)))

noncomputable def ep150 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz827 qz17) (Complex.mk (@HMul.hMul Real Real Real qz0 qz288 (Real.cos qz289)) (@HMul.hMul Real Real Real qz0 qz288 (@Neg.neg Real Real.instNeg (Real.sin qz289)))) Bool.false 13133035641 549755813888 3457669516097 13008871824031744 Bool.false 224051839731 549755813888 3469328512827 13008871824031744 (BSN.cpow_neg_s_mk qz11 121891 1000 6 (@Eq.refl Real qz11) rfl)

noncomputable abbrev qz836 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6) qz267)

noncomputable def ep151 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz835) 2568477 1048576 1 1048576 214039 214040 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz835) (Real.sqrt qz836) Bool.false 2568477 1048576 1 1048576 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz836) Bool.false 2568477 1048576 1 1048576 2568477 1048576 1 1048576 (BSN.sqrt_enclosure 6 1 1284238 1284239 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep152 := BSN.log_dyadic_bound 2 10 4 3 105000000 524288 189304 1434560 960 212580 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 2) (BSN.artanhQ 10) 0 3 1434560 105000000 960 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz290 := (Real.log (Enclosure.sfrac Bool.false 6 1))

noncomputable def ep153 := @Enclosure.Real.IsNear.mulLit_ff qz11 qz290 121891 1000 0 1 4034681531866359 2251799813685248 62500000023663 11831500000000000000 491791366600722364869 2251799813685248000 7618187502884306733 11831500000000000000000 qz272 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 62500000023663 11831500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz836) Bool.false 33845361775666394038272 18889465931478580854784 1000000000378608 189304000000000000000 4034681531866359 2251799813685248 62500000023663 11831500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 212580 524288 24973259072661432 36028797018963968 189304 1000000000000000 rfl rfl rfl rfl (ep152 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep154 := BSN.sin_dyadic_bound_f 125733367 2147483648 1 0 1048576 378978 0 1 1 0 1 1 61358 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 125733367) qz268 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 125733367) qz269 0 0 rfl) rfl rfl

noncomputable abbrev qz564 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 28626025) (@Nat.cast Real Real.instNatCast 131072))

noncomputable abbrev qz565 := (@Nat.cast Real Real.instNatCast 18889465931478580854784)

noncomputable def ep155 := @Enclosure.Real.IsNear.cos_image qz289 qz564 Bool.false 28626025 131072 677 1048576 Bool.false 61358 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz289 Bool.false 491791366600722364869 2251799813685248000 7618187502884306733 11831500000000000000000 28626025 131072 677 1048576 (ep153 rfl) rfl) (Enclosure.sfrac_false_div 28626025 131072) (BSN.cos_reduce3 qz564 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 1105962399690821468160) qz565) 226375608064910080 72057594037927936 Bool.false 61358 1048576 34 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q3 28626025 131072 226375608064910080 72057594037927936 34 1105962399690821468160 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 61358 1048576 1105962399690821468160 18889465931478580854784 125733367 2147483648 378978 378608 (ep154 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep156 := BSN.cos_dyadic_bound_f 125733367 2147483648 1 0 1048576 378978 0 1 1 0 1 1 1046778 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 125733367) qz274 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 125733367) qz275 0 0 rfl) rfl rfl

noncomputable def ep157 := @Enclosure.Real.IsNear.sin_image qz289 qz564 Bool.false 28626025 131072 677 1048576 Bool.true 1046778 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz289 Bool.false 491791366600722364869 2251799813685248000 7618187502884306733 11831500000000000000000 28626025 131072 677 1048576 (ep153 rfl) rfl) (Enclosure.sfrac_false_div 28626025 131072) (BSN.sin_reduce3 qz564 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 1105962399690821468160) qz565) 226375608064910080 72057594037927936 Bool.false 1046778 1048576 34 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q3 28626025 131072 226375608064910080 72057594037927936 34 1105962399690821468160 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1046778 1048576 1105962399690821468160 18889465931478580854784 125733367 2147483648 378978 378608 (ep156 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz566 := (@Enclosure.Real.IsNear.recentre' qz288 Bool.false 428079 1048576 1 1048576 428079 1048576 1 1048576 (ep151 rfl rfl) rfl)

noncomputable def ep158 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz288 (Real.cos qz289)) (@HMul.hMul Real Real Real qz0 qz288 (@Neg.neg Real Real.instNeg (Real.sin qz289))) Bool.false 13133035641 549755813888 3457669516097 13008871824031744 Bool.false 224051839731 549755813888 3469328512827 13008871824031744 (@Enclosure.Real.IsNear.mulLit_ff qz288 (Real.cos qz289) 428079 1048576 1 1048576 30679 524288 16150923 24812453888 13133035641 549755813888 3457669516097 13008871824031744 qz566 (@Enclosure.Real.IsNear.recentre' (Real.cos qz289) Bool.false 61358 1048576 129207384 198499631104 30679 524288 16150923 24812453888 (ep155 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz288 (@Neg.neg Real Real.instNeg (Real.sin qz289)) 428079 1048576 1 1048576 523389 524288 16150923 24812453888 224051839731 549755813888 3469328512827 13008871824031744 qz566 (@Enclosure.Real.IsNear.neg (Real.sin qz289) Bool.true 523389 524288 16150923 24812453888 (@Enclosure.Real.IsNear.recentre' (Real.sin qz289) Bool.true 1046778 1048576 129207384 198499631104 523389 524288 16150923 24812453888 (ep157 rfl rfl) rfl)) rfl)

noncomputable def ep159 := @ep74 13133035641 549755813888 3457669516097 13008871824031744 Bool.false 224051839731 549755813888 3469328512827 13008871824031744 Bool.false 91314852489910407921664 332201498131 549755813888 22367289585411 13008871824031744 Bool.true 295170535727348188184576 536912076727 1099511627776 44772110747503 26017743648063488 (ep75 (BSN.head_sum_c_succ qz14 5 6 rfl rfl) (ep149 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep150 ep158) rfl rfl

noncomputable abbrev qz837 := (@Nat.cast Real Real.instNatCast 7)

noncomputable abbrev qz291 := (@Inv.inv Real Real.instInv (Real.sqrt qz837))

noncomputable abbrev qz292 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 7 1)))

noncomputable def ep160 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz826 qz17) (Complex.mk (@HMul.hMul Real Real Real qz0 qz291 (Real.cos qz292)) (@HMul.hMul Real Real Real qz0 qz291 (@Neg.neg Real Real.instNeg (Real.sin qz292)))) Bool.true 156548375 274877906944 1597922458575 6504435912015872 Bool.false 207788045275 549755813888 3208232426661 13008871824031744 (BSN.cpow_neg_s_mk qz11 121891 1000 7 (@Eq.refl Real qz11) rfl)

noncomputable abbrev qz838 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 7) qz267)

noncomputable def ep161 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz837) 2774271 1048576 1 1048576 198162 198163 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz837) (Real.sqrt qz838) Bool.false 2774271 1048576 1 1048576 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz838) Bool.false 2774271 1048576 1 1048576 2774271 1048576 1 1048576 (BSN.sqrt_enclosure 7 1 1387135 1387136 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep162 := BSN.log_dyadic_bound 3 11 5 4 202569142545 524288 189304 5259111624 688905 293399 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 3) (BSN.artanhQ 11) 0 4 5259111624 202569142545 688905 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz293 := (Real.log (Enclosure.sfrac Bool.false 7 1))

noncomputable def ep163 := @Enclosure.Real.IsNear.mulLit_ff qz11 qz293 121891 1000 0 1 4381796493761783 2251799813685248 62500000023663 11831500000000000000 534101556421117491653 2251799813685248000 7618187502884306733 11831500000000000000000 qz272 (BSN.isNear_log_sfrac 7 1 4381796493761783 2251799813685248 62500000023663 11831500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz838) Bool.false 36757173121942042968064 18889465931478580854784 1000000000378608 189304000000000000000 4381796493761783 2251799813685248 62500000023663 11831500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 293399 524288 24973259072661432 36028797018963968 189304 1000000000000000 rfl rfl rfl rfl (ep162 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep164 := nat_lit 4625138312430903642093739781418920964364121388952690462670526717443610190544896

noncomputable def ep165 := nat_lit 16636502768107539587344834641291365044798203006808538399418739717710247100416

noncomputable def ep166 := nat_lit 13842141931756495847106529674974180163002767760844454311212742672895410077433856

noncomputable def ep167 := BSN.cos_dyadic_bound_f 3370022144 2147483648 3 2 1048576 378978 ep164 ep95 ep165 ep166 ep97 ep165 1580 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3370022144) qz274 0 2 ep164 ep95 ep165 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3370022144) qz275 0 2 ep166 ep97 ep165 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz839 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 124355209) qz279)

noncomputable def ep168 := @Enclosure.Real.IsNear.cos_image qz292 qz839 Bool.false 124355209 524288 169 262144 Bool.true 1580 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz292 Bool.false 534101556421117491653 2251799813685248000 7618187502884306733 11831500000000000000000 124355209 524288 169 262144 (ep163 rfl) rfl) (Enclosure.sfrac_false_div 124355209 524288) (BSN.cos_reduce2 qz839 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 118572113077028412981248) qz281) 226375608064910080 72057594037927936 Bool.false 1580 1048576 37 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q2 124355209 524288 226375608064910080 72057594037927936 37 118572113077028412981248 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1580 1048576 118572113077028412981248 75557863725914323419136 3370022144 2147483648 378978 378608 (ep167 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep169 := nat_lit 8311939760161140524098855738841024643819579937709396002087413099624330145300480

noncomputable def ep170 := nat_lit 21742430748321289165688921012307259476121607508180251895677499206139809980481536

noncomputable def ep171 := BSN.sin_dyadic_bound_f 3370022144 2147483648 3 2 1048576 378978 ep169 ep88 ep165 ep170 ep91 ep165 1048574 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3370022144) qz268 0 2 ep169 ep88 ep165 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3370022144) qz269 0 2 ep170 ep91 ep165 rfl rfl rfl rfl) rfl rfl

noncomputable def ep172 := @Enclosure.Real.IsNear.sin_image qz292 qz839 Bool.false 124355209 524288 169 262144 Bool.true 1048574 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz292 Bool.false 534101556421117491653 2251799813685248000 7618187502884306733 11831500000000000000000 124355209 524288 169 262144 (ep163 rfl) rfl) (Enclosure.sfrac_false_div 124355209 524288) (BSN.sin_reduce2 qz839 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 118572113077028412981248) qz281) 226375608064910080 72057594037927936 Bool.false 1048574 1048576 37 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q2 124355209 524288 226375608064910080 72057594037927936 37 118572113077028412981248 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1048574 1048576 118572113077028412981248 75557863725914323419136 3370022144 2147483648 378978 378608 (ep171 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz567 := (@Enclosure.Real.IsNear.recentre' qz291 Bool.false 396325 1048576 1 1048576 396325 1048576 1 1048576 (ep161 rfl rfl) rfl)

noncomputable def ep173 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz291 (Real.cos qz292)) (@HMul.hMul Real Real Real qz0 qz291 (@Neg.neg Real Real.instNeg (Real.sin qz292))) Bool.true 156548375 274877906944 1597922458575 6504435912015872 Bool.false 207788045275 549755813888 3208232426661 13008871824031744 (@Enclosure.Real.IsNear.mulLit_ft qz291 (Real.cos qz292) 396325 1048576 1 1048576 395 262144 4031815 6203113472 156548375 274877906944 1597922458575 6504435912015872 qz567 (@Enclosure.Real.IsNear.recentre' (Real.cos qz292) Bool.true 1580 1048576 32254520 49624907776 395 262144 4031815 6203113472 (ep168 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz291 (@Neg.neg Real Real.instNeg (Real.sin qz292)) 396325 1048576 1 1048576 524287 524288 4031815 6203113472 207788045275 549755813888 3208232426661 13008871824031744 qz567 (@Enclosure.Real.IsNear.neg (Real.sin qz292) Bool.true 524287 524288 4031815 6203113472 (@Enclosure.Real.IsNear.recentre' (Real.sin qz292) Bool.true 1048574 1048576 32254520 49624907776 524287 524288 4031815 6203113472 (ep172 rfl rfl) rfl)) rfl)

noncomputable def ep174 := @ep72 156548375 274877906944 1597922458575 6504435912015872 Bool.false 207788045275 549755813888 3208232426661 13008871824031744 Bool.false 91228789110599439089664 331888401381 549755813888 25563134502561 13008871824031744 Bool.true 66705163834639752626176 121335986177 1099511627776 51188575600825 26017743648063488 (ep73 (BSN.head_sum_c_succ qz14 6 7 rfl rfl) (ep159 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep160 ep173) rfl rfl

noncomputable abbrev qz840 := (@Nat.cast Real Real.instNatCast 8)

noncomputable abbrev qz294 := (@Inv.inv Real Real.instInv (Real.sqrt qz840))

noncomputable abbrev qz295 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 8 1)))

noncomputable def ep175 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz825 qz17) (Complex.mk (@HMul.hMul Real Real Real qz0 qz294 (Real.cos qz295)) (@HMul.hMul Real Real Real qz0 qz294 (@Neg.neg Real Real.instNeg (Real.sin qz295)))) Bool.true 208790851311 1099511627776 6000926217903 26017743648063488 Bool.true 163952162115 549755813888 3004264534407 13008871824031744 (BSN.cpow_neg_s_mk qz11 121891 1000 8 (@Eq.refl Real qz11) rfl)

noncomputable abbrev qz841 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8) qz267)

noncomputable def ep176 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz840) 2965821 1048576 1 1048576 185363 185364 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz840) (Real.sqrt qz841) Bool.false 2965821 1048576 1 1048576 (BSN.sqrt_natCast_div_one 8) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz841) Bool.false 2965821 1048576 1 1048576 2965821 1048576 1 1048576 (BSN.sqrt_enclosure 8 1 1482910 1482911 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep177 := BSN.log_dyadic_bound 0 16 1 0 1 524288 189304 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz296 := (Real.log (Enclosure.sfrac Bool.false 8 1))

noncomputable def ep178 := @Enclosure.Real.IsNear.mulLit_ff qz11 qz296 121891 1000 0 1 9364972152248037 4503599627370496 125000000070989 23663000000000000000 1141505820609665477967 4503599627370496000 15236375008652920199 23663000000000000000000 qz272 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 125000000070989 23663000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz841) Bool.false 39279540158062550581248 18889465931478580854784 1000000000567912 189304000000000000000 9364972152248037 4503599627370496 125000000070989 23663000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 524288 24973259072661432 36028797018963968 189304 1000000000000000 rfl rfl rfl rfl (ep177 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep179 := nat_lit 2198112821913205406670730096730443776

noncomputable def ep180 := BSN.sin_dyadic_bound_f 1217622024 2147483648 2 1 1048576 378978 ep179 ep106 ep179 ep179 ep107 ep179 563193 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1217622024) qz268 0 1 ep179 ep106 ep179 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1217622024) qz269 0 1 ep179 ep107 ep179 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz842 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 132888767) qz279)

noncomputable def ep181 := @Enclosure.Real.IsNear.cos_image qz295 qz842 Bool.false 132888767 524288 677 1048576 Bool.true 563193 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz295 Bool.false 1141505820609665477967 4503599627370496000 15236375008652920199 23663000000000000000000 132888767 524288 677 1048576 (ep178 rfl) rfl) (Enclosure.sfrac_false_div 132888767 524288) (BSN.cos_reduce1 qz842 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 42841266390761560080384) qz281) 226375608064910080 72057594037927936 Bool.false 563193 1048576 40 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q1 132888767 524288 226375608064910080 72057594037927936 40 42841266390761560080384 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 563193 1048576 42841266390761560080384 75557863725914323419136 1217622024 2147483648 378978 378608 (ep180 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep182 := BSN.cos_dyadic_bound_f 1217622024 2147483648 2 1 1048576 378978 ep179 ep110 ep179 ep179 ep111 ep179 884490 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1217622024) qz274 0 1 ep179 ep110 ep179 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1217622024) qz275 0 1 ep179 ep111 ep179 rfl rfl rfl rfl) rfl rfl

noncomputable def ep183 := @Enclosure.Real.IsNear.sin_image qz295 qz842 Bool.false 132888767 524288 677 1048576 Bool.false 884490 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz295 Bool.false 1141505820609665477967 4503599627370496000 15236375008652920199 23663000000000000000000 132888767 524288 677 1048576 (ep178 rfl) rfl) (Enclosure.sfrac_false_div 132888767 524288) (BSN.sin_reduce1 qz842 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 42841266390761560080384) qz281) 226375608064910080 72057594037927936 Bool.false 884490 1048576 40 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q1 132888767 524288 226375608064910080 72057594037927936 40 42841266390761560080384 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 884490 1048576 42841266390761560080384 75557863725914323419136 1217622024 2147483648 378978 378608 (ep182 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz568 := (@Enclosure.Real.IsNear.recentre' qz294 Bool.false 370727 1048576 1 1048576 370727 1048576 1 1048576 (ep176 rfl rfl) rfl)

noncomputable def ep184 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz294 (Real.cos qz295)) (@HMul.hMul Real Real Real qz0 qz294 (@Neg.neg Real Real.instNeg (Real.sin qz295))) Bool.true 208790851311 1099511627776 6000926217903 26017743648063488 Bool.true 163952162115 549755813888 3004264534407 13008871824031744 (@Enclosure.Real.IsNear.mulLit_ft qz294 (Real.cos qz295) 370727 1048576 1 1048576 563193 1048576 16150923 24812453888 208790851311 1099511627776 6000926217903 26017743648063488 qz568 (@Enclosure.Real.IsNear.recentre' (Real.cos qz295) Bool.true 563193 1048576 129207384 198499631104 563193 1048576 16150923 24812453888 (ep181 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz294 (@Neg.neg Real Real.instNeg (Real.sin qz295)) 370727 1048576 1 1048576 442245 524288 16150923 24812453888 163952162115 549755813888 3004264534407 13008871824031744 qz568 (@Enclosure.Real.IsNear.neg (Real.sin qz295) Bool.false 442245 524288 16150923 24812453888 (@Enclosure.Real.IsNear.recentre' (Real.sin qz295) Bool.false 884490 1048576 129207384 198499631104 442245 524288 16150923 24812453888 (ep183 rfl rfl) rfl)) rfl)

noncomputable def ep185 := @ep70 208790851311 1099511627776 6000926217903 26017743648063488 Bool.true 163952162115 549755813888 3004264534407 13008871824031744 Bool.false 250131172047550559551488 454985951451 1099511627776 57127195223025 26017743648063488 Bool.true 246972472479098041532416 449240310407 1099511627776 57197104669639 26017743648063488 (ep71 (BSN.head_sum_c_succ qz14 7 8 rfl rfl) (ep174 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep175 ep184) rfl rfl

theorem EMRow40.d7 : Enclosure.Complex.IsNear (BSN.headSumC qz14 9) Bool.false 454985951451 1099511627776 57127195223025 26017743648063488 Bool.true 449240310407 1099511627776 57197104669639 26017743648063488 := ep69 (BSN.head_sum_c_succ qz14 8 9 rfl rfl) (ep185 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz843 := (@HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast 16) qz17)

noncomputable def ep186 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 17) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz14 16) qz843) Bool.true 315889795643 1099511627776 96010922354725 26017743648063488 Bool.false 101254527637 549755813888 48061997183739 13008871824031744

noncomputable def ep187 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz14 16) qz843 Bool.true 379197854429 1099511627776 91777543247459 26017743648063488 Bool.true 16244497981 274877906944 11484023066015 3252217956007936 Bool.false

noncomputable abbrev qz844 := (@HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast 15) qz17)

noncomputable def ep188 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 16) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz14 15) qz844) Bool.true 379197854429 1099511627776 91777543247459 26017743648063488 Bool.true 16244497981 274877906944 11484023066015 3252217956007936

noncomputable def ep189 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz14 15) qz844 Bool.true 51058185475 549755813888 43693499728371 13008871824031744 Bool.true 126790598893 1099511627776 87500455425333 26017743648063488 Bool.true

noncomputable abbrev qz845 := (@HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast 14) qz17)

noncomputable def ep190 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 15) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz14 14) qz845) Bool.true 51058185475 549755813888 43693499728371 13008871824031744 Bool.true 126790598893 1099511627776 87500455425333 26017743648063488

noncomputable def ep191 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz14 14) qz845 Bool.true 199034208855 1099511627776 82852616697925 26017743648063488 Bool.false 9413924221 68719476736 10368854010679 3252217956007936 Bool.false

noncomputable abbrev qz846 := (@HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast 13) qz17)

noncomputable def ep192 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 14) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz14 13) qz846) Bool.true 199034208855 1099511627776 82852616697925 26017743648063488 Bool.false 9413924221 68719476736 10368854010679 3252217956007936

noncomputable def ep193 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz14 13) qz846 Bool.true 53991989919 274877906944 9770130576273 3252217956007936 Bool.true 153856388075 1099511627776 78235863679701 26017743648063488 Bool.false

noncomputable abbrev qz847 := (@HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast 12) qz17)

noncomputable def ep194 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 13) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz14 12) qz847) Bool.true 53991989919 274877906944 9770130576273 3252217956007936 Bool.true 153856388075 1099511627776 78235863679701 26017743648063488

noncomputable def ep195 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz14 12) qz847 Bool.true 2363105871 8589934592 18318148117989 6504435912015872 Bool.false 151527350497 1099511627776 73330301299433 26017743648063488 Bool.false

noncomputable abbrev qz848 := (@HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast 11) qz17)

noncomputable def ep196 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 12) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz14 11) qz848) Bool.true 2363105871 8589934592 18318148117989 6504435912015872 Bool.false 151527350497 1099511627776 73330301299433 26017743648063488

noncomputable def ep197 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz14 11) qz848 Bool.false 13449618655 549755813888 34074588880097 13008871824031744 Bool.false 28484940231 274877906944 34114362880973 13008871824031744 Bool.true

noncomputable abbrev qz849 := (@HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast 10) qz17)

noncomputable def ep198 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 11) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz14 10) qz849) Bool.false 13449618655 549755813888 34074588880097 13008871824031744 Bool.false 28484940231 274877906944 34114362880973 13008871824031744

noncomputable def ep199 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz14 10) qz849 Bool.false 49026778619 274877906944 31390809057851 13008871824031744 Bool.true 189805379157 1099511627776 62851565210149 26017743648063488 Bool.true

noncomputable abbrev qz850 := (@Nat.cast Complex Complex.instNatCast 9)

noncomputable def ep200 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 10) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz14 9) (@HPow.hPow Complex Complex Complex qz16 qz850 qz17)) Bool.false 49026778619 274877906944 31390809057851 13008871824031744 Bool.true 189805379157 1099511627776 62851565210149 26017743648063488

noncomputable def ep201 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz14 9) (@HPow.hPow Complex Complex Complex qz16 qz850 qz17) Bool.false 454985951451 1099511627776 57127195223025 26017743648063488 Bool.true 449240310407 1099511627776 57197104669639 26017743648063488 Bool.true

noncomputable abbrev qz851 := (@Nat.cast Real Real.instNatCast 9)

noncomputable abbrev qz297 := (@Inv.inv Real Real.instInv (Real.sqrt qz851))

noncomputable abbrev qz298 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 9 1)))

noncomputable def ep202 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz850 qz17) (Complex.mk (@HMul.hMul Real Real Real qz0 qz297 (Real.cos qz298)) (@HMul.hMul Real Real Real qz0 qz297 (@Neg.neg Real Real.instNeg (Real.sin qz298)))) Bool.true 258878836975 1099511627776 5654422892677 26017743648063488 Bool.false 129717465625 549755813888 2827230270255 13008871824031744 (BSN.cpow_neg_s_mk qz11 121891 1000 9 (@Eq.refl Real qz11) rfl)

noncomputable abbrev qz852 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9) qz267)

noncomputable def ep203 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz851) 3145729 1048576 1 1048576 174762 174763 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz851) (Real.sqrt qz852) Bool.false 3145729 1048576 1 1048576 (BSN.sqrt_natCast_div_one 9) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz852) Bool.false 3145729 1048576 1 1048576 3145729 1048576 1 1048576 (BSN.sqrt_enclosure 9 1 1572864 1572865 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep204 := BSN.log_dyadic_bound 1 17 3 2 1252815 524288 189304 1448 3 61752 18 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 1) (BSN.artanhQ 17) 0 2 1448 1252815 3 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz299 := (Real.log (Enclosure.sfrac Bool.false 9 1))

noncomputable def ep205 := @Enclosure.Real.IsNear.mulLit_ff qz11 qz299 121891 1000 0 1 9895417793173221 4503599627370496 125000000070989 23663000000000000000 1206162370227677080911 4503599627370496000 15236375008652920199 23663000000000000000000 qz272 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 125000000070989 23663000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz852) Bool.false 41504390431577613533184 18889465931478580854784 1000000000567912 189304000000000000000 9895417793173221 4503599627370496 125000000070989 23663000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 61752 524288 24973259072661432 36028797018963968 189304 1000000000000000 rfl rfl rfl rfl (ep204 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep206 := nat_lit 290789585486353048206084823928631359049095882590924512205169283357084911190625

noncomputable def ep207 := nat_lit 66206773920526342076830926704904685466324759178637958327141403017250390625

noncomputable def ep208 := nat_lit 872236342911218091934100809932484267776354998254416260698853567265220232790625

noncomputable def ep209 := BSN.cos_dyadic_bound_f 1688934485 2147483648 3 2 1048576 378978 ep206 ep95 ep207 ep208 ep97 ep207 740659 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1688934485) qz274 0 2 ep206 ep95 ep207 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1688934485) qz275 0 2 ep208 ep97 ep207 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz853 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 280831561) qz270)

noncomputable def ep210 := @Enclosure.Real.IsNear.cos_image qz298 qz853 Bool.false 280831561 1048576 169 262144 Bool.true 740659 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz298 Bool.false 1206162370227677080911 4503599627370496000 15236375008652920199 23663000000000000000000 280831561 1048576 169 262144 (ep205 rfl) rfl) (Enclosure.sfrac_false_div 280831561 1048576) (BSN.cos_reduce2 qz853 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 118848198765095096942592) qz273) 226375608064910080 72057594037927936 Bool.false 740659 1048576 42 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q2 280831561 1048576 226375608064910080 72057594037927936 42 118848198765095096942592 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 740659 1048576 118848198765095096942592 151115727451828646838272 1688934485 2147483648 378978 378608 (ep209 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep211 := nat_lit 8136754507819831114216434086221800625

noncomputable def ep212 := BSN.sin_dyadic_bound_f 1688934485 2147483648 2 1 1048576 378978 ep211 ep106 ep211 ep211 ep107 ep211 742250 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1688934485) qz268 0 1 ep211 ep106 ep211 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1688934485) qz269 0 1 ep211 ep107 ep211 rfl rfl rfl rfl) rfl rfl

noncomputable def ep213 := @Enclosure.Real.IsNear.sin_image qz298 qz853 Bool.false 280831561 1048576 169 262144 Bool.true 742250 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz298 Bool.false 1206162370227677080911 4503599627370496000 15236375008652920199 23663000000000000000000 280831561 1048576 169 262144 (ep205 rfl) rfl) (Enclosure.sfrac_false_div 280831561 1048576) (BSN.sin_reduce2 qz853 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 118848198765095096942592) qz273) 226375608064910080 72057594037927936 Bool.false 742250 1048576 42 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q2 280831561 1048576 226375608064910080 72057594037927936 42 118848198765095096942592 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 742250 1048576 118848198765095096942592 151115727451828646838272 1688934485 2147483648 378978 378608 (ep212 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz569 := (@Enclosure.Real.IsNear.recentre' qz297 Bool.false 349525 1048576 1 1048576 349525 1048576 1 1048576 (ep203 rfl rfl) rfl)

noncomputable def ep214 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz297 (Real.cos qz298)) (@HMul.hMul Real Real Real qz0 qz297 (@Neg.neg Real Real.instNeg (Real.sin qz298))) Bool.true 258878836975 1099511627776 5654422892677 26017743648063488 Bool.false 129717465625 549755813888 2827230270255 13008871824031744 (@Enclosure.Real.IsNear.mulLit_ft qz297 (Real.cos qz298) 349525 1048576 1 1048576 740659 1048576 4031815 6203113472 258878836975 1099511627776 5654422892677 26017743648063488 qz569 (@Enclosure.Real.IsNear.recentre' (Real.cos qz298) Bool.true 740659 1048576 32254520 49624907776 740659 1048576 4031815 6203113472 (ep210 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz297 (@Neg.neg Real Real.instNeg (Real.sin qz298)) 349525 1048576 1 1048576 371125 524288 4031815 6203113472 129717465625 549755813888 2827230270255 13008871824031744 qz569 (@Enclosure.Real.IsNear.neg (Real.sin qz298) Bool.true 371125 524288 4031815 6203113472 (@Enclosure.Real.IsNear.recentre' (Real.sin qz298) Bool.true 742250 1048576 32254520 49624907776 371125 524288 4031815 6203113472 (ep213 rfl rfl) rfl)) rfl)

noncomputable def ep215 := @ep201 258878836975 1099511627776 5654422892677 26017743648063488 Bool.false 129717465625 549755813888 2827230270255 13008871824031744 Bool.false 215622052655961133285376 49026778619 274877906944 31390809057851 13008871824031744 Bool.true 104346610698776966332416 189805379157 1099511627776 62851565210149 26017743648063488 EMRow40.d7 (ep202 ep214) rfl rfl

noncomputable abbrev qz854 := (@Nat.cast Real Real.instNatCast 10)

noncomputable abbrev qz300 := (@Inv.inv Real Real.instInv (Real.sqrt qz854))

noncomputable abbrev qz301 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 10 1)))

noncomputable def ep216 := @Enclosure.Complex.IsNear.of_eq qz849 (Complex.mk (@HMul.hMul Real Real Real qz0 qz300 (Real.cos qz301)) (@HMul.hMul Real Real Real qz0 qz300 (@Neg.neg Real Real.instNeg (Real.sin qz301)))) Bool.true 84603938583 549755813888 1341889911123 6504435912015872 Bool.false 303745140081 1099511627776 5377160551797 26017743648063488 (BSN.cpow_neg_s_mk qz11 121891 1000 10 (@Eq.refl Real qz11) rfl)

noncomputable abbrev qz855 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 10) qz267)

noncomputable def ep217 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz854) 3315889 1048576 1 1048576 165794 165795 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz854) (Real.sqrt qz855) Bool.false 3315889 1048576 1 1048576 (BSN.sqrt_natCast_div_one 10) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz855) Bool.false 3315889 1048576 1 1048576 3315889 1048576 1 1048576 (BSN.sqrt_enclosure 10 1 1657944 1657945 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep218 := BSN.log_dyadic_bound 2 18 3 2 1574640 524288 189304 6528 48 116991 20 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 2) (BSN.artanhQ 18) 0 2 6528 1574640 48 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz302 := (Real.log (Enclosure.sfrac Bool.false 10 1))

noncomputable def ep219 := @Enclosure.Real.IsNear.mulLit_ff qz11 qz302 121891 1000 0 1 10369917190100709 4503599627370496 125000000070989 23663000000000000000 1263999576218565520719 4503599627370496000 15236375008652920199 23663000000000000000000 qz272 (BSN.isNear_log_sfrac 10 1 10369917190100709 4503599627370496 125000000070989 23663000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz855) Bool.false 43494585150108164161536 18889465931478580854784 1000000000567912 189304000000000000000 10369917190100709 4503599627370496 125000000070989 23663000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 116991 524288 24973259072661432 36028797018963968 189304 1000000000000000 rfl rfl rfl rfl (ep218 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep220 := nat_lit 969299303772193697236105669748922265723417475635416375491554230290591948800000

noncomputable def ep221 := nat_lit 734851463503666059838706622251531575200840838576065219462518280217600000000

noncomputable def ep222 := nat_lit 2906428208389573759588639596002263734019850745229096996035737654311340646400000

noncomputable def ep223 := BSN.cos_dyadic_bound_f 2281786180 2147483648 3 2 1048576 378978 ep220 ep95 ep221 ep222 ep97 ep221 510294 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2281786180) qz274 0 2 ep220 ep95 ep221 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2281786180) qz275 0 2 ep222 ep97 ep221 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz856 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 147148917) qz279)

noncomputable def ep224 := @Enclosure.Real.IsNear.cos_image qz301 qz856 Bool.false 147148917 524288 677 1048576 Bool.true 510294 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz301 Bool.false 1263999576218565520719 4503599627370496000 15236375008652920199 23663000000000000000000 147148917 524288 677 1048576 (ep219 rfl) rfl) (Enclosure.sfrac_false_div 147148917 524288) (BSN.cos_reduce2 qz856 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 80283214011372880789504) qz281) 226375608064910080 72057594037927936 Bool.false 510294 1048576 44 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q2 147148917 524288 226375608064910080 72057594037927936 44 80283214011372880789504 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 510294 1048576 80283214011372880789504 75557863725914323419136 2281786180 2147483648 378978 378608 (ep223 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep225 := nat_lit 1744150865619145722177119240250258853041990783472888623709227599898891427840000

noncomputable def ep226 := nat_lit 4566824412347328098747954389933699278273936404880823242216466303471982387200000

noncomputable def ep227 := BSN.sin_dyadic_bound_f 2281786180 2147483648 3 2 1048576 378978 ep225 ep88 ep221 ep226 ep91 ep221 916029 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2281786180) qz268 0 2 ep225 ep88 ep221 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2281786180) qz269 0 2 ep226 ep91 ep221 rfl rfl rfl rfl) rfl rfl

noncomputable def ep228 := @Enclosure.Real.IsNear.sin_image qz301 qz856 Bool.false 147148917 524288 677 1048576 Bool.true 916029 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz301 Bool.false 1263999576218565520719 4503599627370496000 15236375008652920199 23663000000000000000000 147148917 524288 677 1048576 (ep219 rfl) rfl) (Enclosure.sfrac_false_div 147148917 524288) (BSN.sin_reduce2 qz856 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 80283214011372880789504) qz281) 226375608064910080 72057594037927936 Bool.false 916029 1048576 44 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q2 147148917 524288 226375608064910080 72057594037927936 44 80283214011372880789504 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 916029 1048576 80283214011372880789504 75557863725914323419136 2281786180 2147483648 378978 378608 (ep227 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz570 := (@Enclosure.Real.IsNear.recentre' qz300 Bool.false 331589 1048576 1 1048576 331589 1048576 1 1048576 (ep217 rfl rfl) rfl)

noncomputable def ep229 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz300 (Real.cos qz301)) (@HMul.hMul Real Real Real qz0 qz300 (@Neg.neg Real Real.instNeg (Real.sin qz301))) Bool.true 84603938583 549755813888 1341889911123 6504435912015872 Bool.false 303745140081 1099511627776 5377160551797 26017743648063488 (@Enclosure.Real.IsNear.mulLit_ft qz300 (Real.cos qz301) 331589 1048576 1 1048576 255147 524288 16150923 24812453888 84603938583 549755813888 1341889911123 6504435912015872 qz570 (@Enclosure.Real.IsNear.recentre' (Real.cos qz301) Bool.true 510294 1048576 129207384 198499631104 255147 524288 16150923 24812453888 (ep224 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz300 (@Neg.neg Real Real.instNeg (Real.sin qz301)) 331589 1048576 1 1048576 916029 1048576 16150923 24812453888 303745140081 1099511627776 5377160551797 26017743648063488 qz570 (@Enclosure.Real.IsNear.neg (Real.sin qz301) Bool.true 916029 1048576 16150923 24812453888 (@Enclosure.Real.IsNear.recentre' (Real.sin qz301) Bool.true 916029 1048576 129207384 198499631104 916029 1048576 16150923 24812453888 (ep228 rfl rfl) rfl)) rfl)

noncomputable def ep230 := @ep199 84603938583 549755813888 1341889911123 6504435912015872 Bool.false 303745140081 1099511627776 5377160551797 26017743648063488 Bool.false 3697003025081376440320 13449618655 549755813888 34074588880097 13008871824031744 Bool.false 125278092001955517825024 28484940231 274877906944 34114362880973 13008871824031744 (ep200 (BSN.head_sum_c_succ qz14 9 10 rfl rfl) (ep215 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep216 ep229) rfl rfl

noncomputable abbrev qz857 := (@Nat.cast Real Real.instNatCast 11)

noncomputable abbrev qz303 := (@Inv.inv Real Real.instInv (Real.sqrt qz857))

noncomputable abbrev qz304 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 11 1)))

noncomputable def ep231 := @Enclosure.Complex.IsNear.of_eq qz848 (Complex.mk (@HMul.hMul Real Real Real qz0 qz303 (Real.cos qz304)) (@HMul.hMul Real Real Real qz0 qz303 (@Neg.neg Real Real.instNeg (Real.sin qz304)))) Bool.true 164688394399 549755813888 2561707355881 13008871824031744 Bool.false 37587589573 1099511627776 5101575537487 26017743648063488 (BSN.cpow_neg_s_mk qz11 121891 1000 11 (@Eq.refl Real qz11) rfl)

noncomputable abbrev qz858 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11) qz267)

noncomputable def ep232 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz857) 3477733 1048576 1 1048576 158078 158079 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz857) (Real.sqrt qz858) Bool.false 3477733 1048576 1 1048576 (BSN.sqrt_natCast_div_one 11) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz858) Bool.false 3477733 1048576 1 1048576 3477733 1048576 1 1048576 (BSN.sqrt_enclosure 11 1 1738866 1738867 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep233 := BSN.log_dyadic_bound 3 19 4 3 4939817505 524288 189304 41676111 10935 166961 22 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 3) (BSN.artanhQ 19) 0 3 41676111 4939817505 10935 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz305 := (Real.log (Enclosure.sfrac Bool.false 11 1))

noncomputable def ep234 := @Enclosure.Real.IsNear.mulLit_ff qz11 qz305 121891 1000 0 1 10799156221662949 4503599627370496 125000000070989 23663000000000000000 1316319951014718516559 4503599627370496000 15236375008652920199 23663000000000000000000 qz272 (BSN.isNear_log_sfrac 11 1 10799156221662949 4503599627370496 125000000070989 23663000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz858) Bool.false 45294944137145793642496 18889465931478580854784 1000000000567912 189304000000000000000 10799156221662949 4503599627370496 125000000070989 23663000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 166961 524288 24973259072661432 36028797018963968 189304 1000000000000000 rfl rfl rfl rfl (ep233 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep235 := nat_lit 3545148191700962376696988866945681

noncomputable def ep236 := BSN.cos_dyadic_bound_f 244010547 2147483648 2 1 1048576 378978 ep235 ep110 ep235 ep235 ep111 ep235 1041814 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 244010547) qz274 0 1 ep235 ep110 ep235 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 244010547) qz275 0 1 ep235 ep111 ep235 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz859 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 306479621) qz270)

noncomputable def ep237 := @Enclosure.Real.IsNear.cos_image qz304 qz859 Bool.false 306479621 1048576 169 262144 Bool.true 1041814 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz304 Bool.false 1316319951014718516559 4503599627370496000 15236375008652920199 23663000000000000000000 306479621 1048576 169 262144 (ep234 rfl) rfl) (Enclosure.sfrac_false_div 306479621 1048576) (BSN.cos_reduce2 qz859 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 17170715809592620613632) qz273) 226375608064910080 72057594037927936 Bool.false 1041814 1048576 46 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q2 306479621 1048576 226375608064910080 72057594037927936 46 17170715809592620613632 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1041814 1048576 17170715809592620613632 151115727451828646838272 244010547 2147483648 378978 378608 (ep236 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep238 := BSN.sin_dyadic_bound_f 244010547 2147483648 1 0 1048576 378978 0 1 1 0 1 1 118889 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 244010547) qz268 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 244010547) qz269 0 0 rfl) rfl rfl

noncomputable def ep239 := @Enclosure.Real.IsNear.sin_image qz304 qz859 Bool.false 306479621 1048576 169 262144 Bool.true 118889 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz304 Bool.false 1316319951014718516559 4503599627370496000 15236375008652920199 23663000000000000000000 306479621 1048576 169 262144 (ep234 rfl) rfl) (Enclosure.sfrac_false_div 306479621 1048576) (BSN.sin_reduce2 qz859 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 17170715809592620613632) qz273) 226375608064910080 72057594037927936 Bool.false 118889 1048576 46 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q2 306479621 1048576 226375608064910080 72057594037927936 46 17170715809592620613632 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 118889 1048576 17170715809592620613632 151115727451828646838272 244010547 2147483648 378978 378608 (ep238 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz571 := (@Enclosure.Real.IsNear.recentre' qz303 Bool.false 316157 1048576 1 1048576 316157 1048576 1 1048576 (ep232 rfl rfl) rfl)

noncomputable def ep240 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz303 (Real.cos qz304)) (@HMul.hMul Real Real Real qz0 qz303 (@Neg.neg Real Real.instNeg (Real.sin qz304))) Bool.true 164688394399 549755813888 2561707355881 13008871824031744 Bool.false 37587589573 1099511627776 5101575537487 26017743648063488 (@Enclosure.Real.IsNear.mulLit_ft qz303 (Real.cos qz304) 316157 1048576 1 1048576 520907 524288 4031815 6203113472 164688394399 549755813888 2561707355881 13008871824031744 qz571 (@Enclosure.Real.IsNear.recentre' (Real.cos qz304) Bool.true 1041814 1048576 32254520 49624907776 520907 524288 4031815 6203113472 (ep237 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz303 (@Neg.neg Real Real.instNeg (Real.sin qz304)) 316157 1048576 1 1048576 118889 1048576 4031815 6203113472 37587589573 1099511627776 5101575537487 26017743648063488 qz571 (@Enclosure.Real.IsNear.neg (Real.sin qz304) Bool.true 118889 1048576 4031815 6203113472 (@Enclosure.Real.IsNear.recentre' (Real.sin qz304) Bool.true 118889 1048576 32254520 49624907776 118889 1048576 4031815 6203113472 (ep239 rfl rfl) rfl)) rfl)

noncomputable def ep241 := @ep197 164688394399 549755813888 2561707355881 13008871824031744 Bool.false 37587589573 1099511627776 5101575537487 26017743648063488 Bool.true 83144396250567432732672 2363105871 8589934592 18318148117989 6504435912015872 Bool.false 41651520949385238151168 151527350497 1099511627776 73330301299433 26017743648063488 (ep198 (BSN.head_sum_c_succ qz14 10 11 rfl rfl) (ep230 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep231 ep240) rfl rfl

noncomputable abbrev qz860 := (@Nat.cast Real Real.instNatCast 12)

noncomputable abbrev qz306 := (@Inv.inv Real Real.instInv (Real.sqrt qz860))

noncomputable abbrev qz307 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 12 1)))

noncomputable def ep242 := @Enclosure.Complex.IsNear.of_eq qz847 (Complex.mk (@HMul.hMul Real Real Real qz0 qz306 (Real.cos qz307)) (@HMul.hMul Real Real Real qz0 qz306 (@Neg.neg Real Real.instNeg (Real.sin qz307)))) Bool.false 21627397953 274877906944 1222113034557 6504435912015872 Bool.true 76345934643 274877906944 1226390595067 6504435912015872 (BSN.cpow_neg_s_mk qz11 121891 1000 12 (@Eq.refl Real qz11) rfl)

noncomputable abbrev qz861 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 12) qz267)

noncomputable def ep243 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz860) 3632373 1048576 1 1048576 151348 151349 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz860) (Real.sqrt qz861) Bool.false 3632373 1048576 1 1048576 (BSN.sqrt_natCast_div_one 12) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz861) Bool.false 3632373 1048576 1 1048576 3632373 1048576 1 1048576 (BSN.sqrt_enclosure 12 1 1816186 1816187 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep244 := BSN.log_dyadic_bound 4 20 4 3 6720000000 524288 189304 91811840 61440 212580 24 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 4) (BSN.artanhQ 20) 0 3 91811840 6720000000 61440 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz308 := (Real.log (Enclosure.sfrac Bool.false 12 1))

noncomputable def ep245 := @Enclosure.Real.IsNear.mulLit_ff qz11 qz308 121891 1000 0 1 11191020447815397 4503599627370496 125000000070989 23663000000000000000 1364084673404666555727 4503599627370496000 15236375008652920199 23663000000000000000000 qz272 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 125000000070989 23663000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz861) Bool.false 46938541828353910898688 18889465931478580854784 1000000000567912 189304000000000000000 11191020447815397 4503599627370496 125000000070989 23663000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 212580 524288 24973259072661432 36028797018963968 189304 1000000000000000 rfl rfl rfl rfl (ep244 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep246 := nat_lit 2139015518460308628683421817458719806660261149731485277538933932716526712791296

noncomputable def ep247 := nat_lit 3572059347270240348129124413333635238520599166953155984155203411987466690816

noncomputable def ep248 := nat_lit 6409902436686385405354007203549492149503742250860549520648491391325605204992256

noncomputable def ep249 := BSN.cos_dyadic_bound_f 2780448358 2147483648 3 2 1048576 378978 ep246 ep95 ep247 ep248 ep97 ep247 285796 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2780448358) qz274 0 2 ep246 ep95 ep247 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2780448358) qz275 0 2 ep248 ep97 ep247 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz572 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 39700089) (@Nat.cast Real Real.instNatCast 131072))

noncomputable def ep250 := @Enclosure.Real.IsNear.cos_image qz307 qz572 Bool.false 39700089 131072 169 262144 Bool.false 285796 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz307 Bool.false 1364084673404666555727 4503599627370496000 15236375008652920199 23663000000000000000000 39700089 131072 169 262144 (ep245 rfl) rfl) (Enclosure.sfrac_false_div 39700089 131072) (BSN.cos_reduce0 qz572 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 24457082408709220466688) qz565) 226375608064910080 72057594037927936 Bool.false 285796 1048576 48 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q0 39700089 131072 226375608064910080 72057594037927936 48 24457082408709220466688 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 285796 1048576 24457082408709220466688 18889465931478580854784 2780448358 2147483648 378978 378608 (ep249 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep251 := nat_lit 3847370285750739339351655971895028743797653590183110974782756916160158109671680

noncomputable def ep252 := nat_lit 10070662652308736928214508963055868443369583194685461729028112070133386769735936

noncomputable def ep253 := BSN.sin_dyadic_bound_f 2780448358 2147483648 3 2 1048576 378978 ep251 ep88 ep247 ep252 ep91 ep247 1008876 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2780448358) qz268 0 2 ep251 ep88 ep247 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2780448358) qz269 0 2 ep252 ep91 ep247 rfl rfl rfl rfl) rfl rfl

noncomputable def ep254 := @Enclosure.Real.IsNear.sin_image qz307 qz572 Bool.false 39700089 131072 169 262144 Bool.false 1008876 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz307 Bool.false 1364084673404666555727 4503599627370496000 15236375008652920199 23663000000000000000000 39700089 131072 169 262144 (ep245 rfl) rfl) (Enclosure.sfrac_false_div 39700089 131072) (BSN.sin_reduce0 qz572 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 24457082408709220466688) qz565) 226375608064910080 72057594037927936 Bool.false 1008876 1048576 48 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q0 39700089 131072 226375608064910080 72057594037927936 48 24457082408709220466688 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1008876 1048576 24457082408709220466688 18889465931478580854784 2780448358 2147483648 378978 378608 (ep253 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz573 := (@Enclosure.Real.IsNear.recentre' qz306 Bool.false 302697 1048576 1 1048576 302697 1048576 1 1048576 (ep243 rfl rfl) rfl)

noncomputable def ep255 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz306 (Real.cos qz307)) (@HMul.hMul Real Real Real qz0 qz306 (@Neg.neg Real Real.instNeg (Real.sin qz307))) Bool.false 21627397953 274877906944 1222113034557 6504435912015872 Bool.true 76345934643 274877906944 1226390595067 6504435912015872 (@Enclosure.Real.IsNear.mulLit_ff qz306 (Real.cos qz307) 302697 1048576 1 1048576 71449 262144 4031815 6203113472 21627397953 274877906944 1222113034557 6504435912015872 qz573 (@Enclosure.Real.IsNear.recentre' (Real.cos qz307) Bool.false 285796 1048576 32254520 49624907776 71449 262144 4031815 6203113472 (ep250 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz306 (@Neg.neg Real Real.instNeg (Real.sin qz307)) 302697 1048576 1 1048576 252219 262144 4031815 6203113472 76345934643 274877906944 1226390595067 6504435912015872 qz573 (@Enclosure.Real.IsNear.neg (Real.sin qz307) Bool.false 252219 262144 4031815 6203113472 (@Enclosure.Real.IsNear.recentre' (Real.sin qz307) Bool.false 1008876 1048576 32254520 49624907776 252219 262144 4031815 6203113472 (ep254 rfl rfl) rfl)) rfl)

noncomputable def ep256 := @ep195 21627397953 274877906944 1222113034557 6504435912015872 Bool.true 76345934643 274877906944 1226390595067 6504435912015872 Bool.true 463787661896133378048 53991989919 274877906944 9770130576273 3252217956007936 Bool.true 42291721924019801292800 153856388075 1099511627776 78235863679701 26017743648063488 (ep196 (BSN.head_sum_c_succ qz14 11 12 rfl rfl) (ep241 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep242 ep255) rfl rfl

noncomputable abbrev qz862 := (@Nat.cast Real Real.instNatCast 13)

noncomputable abbrev qz309 := (@Inv.inv Real Real.instInv (Real.sqrt qz862))

noncomputable abbrev qz310 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 13 1)))

noncomputable def ep257 := @Enclosure.Complex.IsNear.of_eq qz846 (Complex.mk (@HMul.hMul Real Real Real qz0 qz309 (Real.cos qz310)) (@HMul.hMul Real Real Real qz0 qz309 (@Neg.neg Real Real.instNeg (Real.sin qz310)))) Bool.false 16933750821 1099511627776 4691572087741 26017743648063488 Bool.false 304479175611 1099511627776 4714968405731 26017743648063488 (BSN.cpow_neg_s_mk qz11 121891 1000 13 (@Eq.refl Real qz11) rfl)

noncomputable abbrev qz863 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13) qz267)

noncomputable def ep258 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz862) 3780695 1048576 1 1048576 145411 145412 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz862) (Real.sqrt qz863) Bool.false 3780695 1048576 1 1048576 (BSN.sqrt_natCast_div_one 13) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz863) Bool.false 3780695 1048576 1 1048576 3780695 1048576 1 1048576 (BSN.sqrt_enclosure 13 1 1890347 1890348 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep259 := BSN.log_dyadic_bound 5 21 5 4 35742602096145 524288 189304 699352521000 41015625 254545 26 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 5) (BSN.artanhQ 21) 0 4 699352521000 35742602096145 41015625 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz311 := (Real.log (Enclosure.sfrac Bool.false 13 1))

noncomputable def ep260 := @Enclosure.Real.IsNear.mulLit_ff qz11 qz311 121891 1000 0 1 11551497052968677 4503599627370496 125000000070989 23663000000000000000 1408023527283405008207 4503599627370496000 15236375008652920199 23663000000000000000000 qz272 (BSN.isNear_log_sfrac 13 1 11551497052968677 4503599627370496 125000000070989 23663000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz863) Bool.false 48450490295254733815808 18889465931478580854784 1000000000567912 189304000000000000000 11551497052968677 4503599627370496 125000000070989 23663000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 254545 524288 24973259072661432 36028797018963968 189304 1000000000000000 rfl rfl rfl rfl (ep259 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep261 := BSN.sin_dyadic_bound_f 119311352 2147483648 1 0 1048576 378978 0 1 1 0 1 1 58227 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 119311352) qz268 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 119311352) qz269 0 0 rfl) rfl rfl

noncomputable abbrev qz574 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 20489439) (@Nat.cast Real Real.instNatCast 65536))

noncomputable abbrev qz864 := (@Nat.cast Real Real.instNatCast 9444732965739290427392)

noncomputable def ep262 := @Enclosure.Real.IsNear.cos_image qz310 qz574 Bool.false 20489439 65536 169 262144 Bool.false 58227 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz310 Bool.false 1408023527283405008207 4503599627370496000 15236375008652920199 23663000000000000000000 20489439 65536 169 262144 (ep260 rfl) rfl) (Enclosure.sfrac_false_div 20489439 65536) (BSN.cos_reduce3 qz574 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 524736875528808562688) qz864) 226375608064910080 72057594037927936 Bool.false 58227 1048576 49 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q3 20489439 65536 226375608064910080 72057594037927936 49 524736875528808562688 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 58227 1048576 524736875528808562688 9444732965739290427392 119311352 2147483648 378978 378608 (ep261 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep263 := BSN.cos_dyadic_bound_f 119311352 2147483648 1 0 1048576 378978 0 1 1 0 1 1 1046957 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 119311352) qz274 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 119311352) qz275 0 0 rfl) rfl rfl

noncomputable def ep264 := @Enclosure.Real.IsNear.sin_image qz310 qz574 Bool.false 20489439 65536 169 262144 Bool.true 1046957 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz310 Bool.false 1408023527283405008207 4503599627370496000 15236375008652920199 23663000000000000000000 20489439 65536 169 262144 (ep260 rfl) rfl) (Enclosure.sfrac_false_div 20489439 65536) (BSN.sin_reduce3 qz574 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 524736875528808562688) qz864) 226375608064910080 72057594037927936 Bool.false 1046957 1048576 49 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q3 20489439 65536 226375608064910080 72057594037927936 49 524736875528808562688 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1046957 1048576 524736875528808562688 9444732965739290427392 119311352 2147483648 378978 378608 (ep263 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz575 := (@Enclosure.Real.IsNear.recentre' qz309 Bool.false 290823 1048576 1 1048576 290823 1048576 1 1048576 (ep258 rfl rfl) rfl)

noncomputable def ep265 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz309 (Real.cos qz310)) (@HMul.hMul Real Real Real qz0 qz309 (@Neg.neg Real Real.instNeg (Real.sin qz310))) Bool.false 16933750821 1099511627776 4691572087741 26017743648063488 Bool.false 304479175611 1099511627776 4714968405731 26017743648063488 (@Enclosure.Real.IsNear.mulLit_ff qz309 (Real.cos qz310) 290823 1048576 1 1048576 58227 1048576 4031815 6203113472 16933750821 1099511627776 4691572087741 26017743648063488 qz575 (@Enclosure.Real.IsNear.recentre' (Real.cos qz310) Bool.false 58227 1048576 32254520 49624907776 58227 1048576 4031815 6203113472 (ep262 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz309 (@Neg.neg Real Real.instNeg (Real.sin qz310)) 290823 1048576 1 1048576 1046957 1048576 4031815 6203113472 304479175611 1099511627776 4714968405731 26017743648063488 qz575 (@Enclosure.Real.IsNear.neg (Real.sin qz310) Bool.true 1046957 1048576 4031815 6203113472 (@Enclosure.Real.IsNear.recentre' (Real.sin qz310) Bool.true 1046957 1048576 32254520 49624907776 1046957 1048576 4031815 6203113472 (ep264 rfl rfl) rfl)) rfl)

noncomputable def ep266 := @ep193 16933750821 1099511627776 4691572087741 26017743648063488 Bool.false 304479175611 1099511627776 4714968405731 26017743648063488 Bool.true 54710106740317350789120 199034208855 1099511627776 82852616697925 26017743648063488 Bool.false 165611506303865964199936 9413924221 68719476736 10368854010679 3252217956007936 (ep194 (BSN.head_sum_c_succ qz14 12 13 rfl rfl) (ep256 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep257 ep265) rfl rfl

noncomputable abbrev qz865 := (@Nat.cast Real Real.instNatCast 14)

noncomputable abbrev qz312 := (@Inv.inv Real Real.instInv (Real.sqrt qz865))

noncomputable abbrev qz313 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 14 1)))

noncomputable def ep267 := @Enclosure.Complex.IsNear.of_eq qz845 (Complex.mk (@HMul.hMul Real Real Real qz0 qz312 (Real.cos qz313)) (@HMul.hMul Real Real Real qz0 qz312 (@Neg.neg Real Real.instNeg (Real.sin qz313)))) Bool.false 96917837905 1099511627776 4534382758817 26017743648063488 Bool.true 277413386429 1099511627776 4549623339901 26017743648063488 (BSN.cpow_neg_s_mk qz11 121891 1000 14 (@Eq.refl Real qz11) rfl)

noncomputable abbrev qz866 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14) qz267)

noncomputable def ep268 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz865) 3923413 1048576 1 1048576 140121 140122 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz865) (Real.sqrt qz866) Bool.false 3923413 1048576 1 1048576 (BSN.sqrt_natCast_div_one 14) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz866) Bool.false 3923413 1048576 1 1048576 3923413 1048576 1 1048576 (BSN.sqrt_enclosure 14 1 1961706 1961707 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep269 := BSN.log_dyadic_bound 6 22 5 4 51857700491520 524288 189304 1346332575744 176359680 293399 28 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 6) (BSN.artanhQ 22) 0 4 1346332575744 51857700491520 176359680 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz314 := (Real.log (Enclosure.sfrac Bool.false 14 1))

noncomputable def ep270 := @Enclosure.Real.IsNear.mulLit_ff qz11 qz314 121891 1000 0 1 11885250371606245 4503599627370496 125000000070989 23663000000000000000 289741010609091361859 900719925474099200 15236375008652920199 23663000000000000000000 qz272 (BSN.isNear_log_sfrac 14 1 11885250371606245 4503599627370496 125000000070989 23663000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz866) Bool.false 49850353174629559828480 18889465931478580854784 1000000000567912 189304000000000000000 11885250371606245 4503599627370496 125000000070989 23663000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 293399 524288 24973259072661432 36028797018963968 189304 1000000000000000 rfl rfl rfl rfl (ep269 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep271 := nat_lit 1768396617897830227337189854997782207947834635004563068808549763431307516272161

noncomputable def ep272 := nat_lit 2442874517320855409987657546149760081316646229639487720906677589722288578081

noncomputable def ep273 := nat_lit 5300304104658848971191594249901047103680870612554410230983835935114477971660321

noncomputable def ep274 := BSN.cos_dyadic_bound_f 2651475661 2147483648 3 2 1048576 378978 ep271 ep95 ep272 ep273 ep97 ep272 345835 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2651475661) qz274 0 2 ep271 ep95 ep272 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2651475661) qz275 0 2 ep273 ep97 ep272 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz867 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 337302929) qz270)

noncomputable def ep275 := @Enclosure.Real.IsNear.cos_image qz313 qz867 Bool.false 337302929 1048576 677 1048576 Bool.false 345835 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz313 Bool.false 289741010609091361859 900719925474099200 15236375008652920199 23663000000000000000000 337302929 1048576 677 1048576 (ep270 rfl) rfl) (Enclosure.sfrac_false_div 337302929 1048576) (BSN.cos_reduce0 qz867 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 186581012508744790048768) qz273) 226375608064910080 72057594037927936 Bool.false 345835 1048576 51 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q0 337302929 1048576 226375608064910080 72057594037927936 51 186581012508744790048768 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 345835 1048576 186581012508744790048768 151115727451828646838272 2651475661 2147483648 378978 378608 (ep274 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep276 := nat_lit 3181159612602237724878951612959088166241049026024501933678664232104575698427425

noncomputable def ep277 := nat_lit 8327653379025436465923940874103845585737758593311422084276938367985766933421601

noncomputable def ep278 := BSN.sin_dyadic_bound_f 2651475661 2147483648 3 2 1048576 378978 ep276 ep88 ep272 ep277 ep91 ep272 989903 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2651475661) qz268 0 2 ep276 ep88 ep272 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2651475661) qz269 0 2 ep277 ep91 ep272 rfl rfl rfl rfl) rfl rfl

noncomputable def ep279 := @Enclosure.Real.IsNear.sin_image qz313 qz867 Bool.false 337302929 1048576 677 1048576 Bool.false 989903 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz313 Bool.false 289741010609091361859 900719925474099200 15236375008652920199 23663000000000000000000 337302929 1048576 677 1048576 (ep270 rfl) rfl) (Enclosure.sfrac_false_div 337302929 1048576) (BSN.sin_reduce0 qz867 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 186581012508744790048768) qz273) 226375608064910080 72057594037927936 Bool.false 989903 1048576 51 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q0 337302929 1048576 226375608064910080 72057594037927936 51 186581012508744790048768 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 989903 1048576 186581012508744790048768 151115727451828646838272 2651475661 2147483648 378978 378608 (ep278 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz576 := (@Enclosure.Real.IsNear.recentre' qz312 Bool.false 280243 1048576 1 1048576 280243 1048576 1 1048576 (ep268 rfl rfl) rfl)

noncomputable def ep280 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz312 (Real.cos qz313)) (@HMul.hMul Real Real Real qz0 qz312 (@Neg.neg Real Real.instNeg (Real.sin qz313))) Bool.false 96917837905 1099511627776 4534382758817 26017743648063488 Bool.true 277413386429 1099511627776 4549623339901 26017743648063488 (@Enclosure.Real.IsNear.mulLit_ff qz312 (Real.cos qz313) 280243 1048576 1 1048576 345835 1048576 16150923 24812453888 96917837905 1099511627776 4534382758817 26017743648063488 qz576 (@Enclosure.Real.IsNear.recentre' (Real.cos qz313) Bool.false 345835 1048576 129207384 198499631104 345835 1048576 16150923 24812453888 (ep275 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz312 (@Neg.neg Real Real.instNeg (Real.sin qz313)) 280243 1048576 1 1048576 989903 1048576 16150923 24812453888 277413386429 1099511627776 4549623339901 26017743648063488 qz576 (@Enclosure.Real.IsNear.neg (Real.sin qz313) Bool.false 989903 1048576 16150923 24812453888 (@Enclosure.Real.IsNear.recentre' (Real.sin qz313) Bool.false 989903 1048576 129207384 198499631104 989903 1048576 16150923 24812453888 (ep279 rfl rfl) rfl)) rfl)

noncomputable def ep281 := @ep191 96917837905 1099511627776 4534382758817 26017743648063488 Bool.true 277413386429 1099511627776 4549623339901 26017743648063488 Bool.true 112278137245812339507200 51058185475 549755813888 43693499728371 13008871824031744 Bool.true 8712983610971020853248 126790598893 1099511627776 87500455425333 26017743648063488 (ep192 (BSN.head_sum_c_succ qz14 13 14 rfl rfl) (ep266 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep267 ep280) rfl rfl

noncomputable abbrev qz868 := (@Nat.cast Real Real.instNatCast 15)

noncomputable abbrev qz315 := (@Inv.inv Real Real.instInv (Real.sqrt qz868))

noncomputable abbrev qz316 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 15 1)))

noncomputable def ep282 := @Enclosure.Complex.IsNear.of_eq qz844 (Complex.mk (@HMul.hMul Real Real Real qz0 qz315 (Real.cos qz316)) (@HMul.hMul Real Real Real qz0 qz315 (@Neg.neg Real Real.instNeg (Real.sin qz316)))) Bool.true 277081483479 1099511627776 4390543790717 26017743648063488 Bool.false 61812606969 1099511627776 4371729102787 26017743648063488 (BSN.cpow_neg_s_mk qz11 121891 1000 15 (@Eq.refl Real qz11) rfl)

noncomputable abbrev qz869 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 15) qz267)

noncomputable def ep283 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz868) 4061117 1048576 1 1048576 135370 135371 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz868) (Real.sqrt qz869) Bool.false 4061117 1048576 1 1048576 (BSN.sqrt_natCast_div_one 15) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz869) Bool.false 4061117 1048576 1 1048576 4061117 1048576 1 1048576 (BSN.sqrt_enclosure 15 1 2030558 2030559 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep284 := BSN.log_dyadic_bound 7 23 6 5 430628584065881355 524288 189304 14087658153505881 266939110305 329571 30 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 7) (BSN.artanhQ 23) 0 5 14087658153505881 430628584065881355 266939110305 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz317 := (Real.log (Enclosure.sfrac Bool.false 15 1))

noncomputable def ep285 := @Enclosure.Real.IsNear.mulLit_ff qz11 qz317 121891 1000 0 1 12195965485668069 4503599627370496 125000000070989 23663000000000000000 1486578429013566598479 4503599627370496000 15236375008652920199 23663000000000000000000 qz272 (BSN.isNear_log_sfrac 15 1 12195965485668069 4503599627370496 125000000070989 23663000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz869) Bool.false 51153586820399524478976 18889465931478580854784 1000000000567912 189304000000000000000 12195965485668069 4503599627370496 125000000070989 23663000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 329571 524288 24973259072661432 36028797018963968 189304 1000000000000000 rfl rfl rfl rfl (ep284 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep286 := nat_lit 49361167887160620046067656122433536

noncomputable def ep287 := BSN.cos_dyadic_bound_f 471353088 2147483648 2 1 1048576 378978 ep286 ep110 ep286 ep286 ep111 ep286 1023419 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 471353088) qz274 0 1 ep286 ep110 ep286 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 471353088) qz275 0 1 ep286 ep111 ep286 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz577 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 86530253) (@Nat.cast Real Real.instNatCast 262144))

noncomputable abbrev qz578 := (@Nat.cast Real Real.instNatCast 37778931862957161709568)

noncomputable def ep288 := @Enclosure.Real.IsNear.cos_image qz316 qz577 Bool.false 86530253 262144 169 262144 Bool.true 1023419 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz316 Bool.false 1486578429013566598479 4503599627370496000 15236375008652920199 23663000000000000000000 86530253 262144 169 262144 (ep285 rfl) rfl) (Enclosure.sfrac_false_div 86530253 262144) (BSN.cos_reduce2 qz577 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8292131227156313276416) qz578) 226375608064910080 72057594037927936 Bool.false 1023419 1048576 52 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q2 86530253 262144 226375608064910080 72057594037927936 52 8292131227156313276416 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1023419 1048576 8292131227156313276416 37778931862957161709568 471353088 2147483648 378978 378608 (ep287 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep289 := BSN.sin_dyadic_bound_f 471353088 2147483648 2 1 1048576 378978 ep286 ep106 ep286 ep286 ep107 ep286 228309 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 471353088) qz268 0 1 ep286 ep106 ep286 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 471353088) qz269 0 1 ep286 ep107 ep286 rfl rfl rfl rfl) rfl rfl

noncomputable def ep290 := @Enclosure.Real.IsNear.sin_image qz316 qz577 Bool.false 86530253 262144 169 262144 Bool.true 228309 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz316 Bool.false 1486578429013566598479 4503599627370496000 15236375008652920199 23663000000000000000000 86530253 262144 169 262144 (ep285 rfl) rfl) (Enclosure.sfrac_false_div 86530253 262144) (BSN.sin_reduce2 qz577 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8292131227156313276416) qz578) 226375608064910080 72057594037927936 Bool.false 228309 1048576 52 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q2 86530253 262144 226375608064910080 72057594037927936 52 8292131227156313276416 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 228309 1048576 8292131227156313276416 37778931862957161709568 471353088 2147483648 378978 378608 (ep289 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz579 := (@Enclosure.Real.IsNear.recentre' qz315 Bool.false 270741 1048576 1 1048576 270741 1048576 1 1048576 (ep283 rfl rfl) rfl)

noncomputable def ep291 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz315 (Real.cos qz316)) (@HMul.hMul Real Real Real qz0 qz315 (@Neg.neg Real Real.instNeg (Real.sin qz316))) Bool.true 277081483479 1099511627776 4390543790717 26017743648063488 Bool.false 61812606969 1099511627776 4371729102787 26017743648063488 (@Enclosure.Real.IsNear.mulLit_ft qz315 (Real.cos qz316) 270741 1048576 1 1048576 1023419 1048576 4031815 6203113472 277081483479 1099511627776 4390543790717 26017743648063488 qz579 (@Enclosure.Real.IsNear.recentre' (Real.cos qz316) Bool.true 1023419 1048576 32254520 49624907776 1023419 1048576 4031815 6203113472 (ep288 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz315 (@Neg.neg Real Real.instNeg (Real.sin qz316)) 270741 1048576 1 1048576 228309 1048576 4031815 6203113472 61812606969 1099511627776 4371729102787 26017743648063488 qz579 (@Enclosure.Real.IsNear.neg (Real.sin qz316) Bool.true 228309 1048576 4031815 6203113472 (@Enclosure.Real.IsNear.recentre' (Real.sin qz316) Bool.true 228309 1048576 32254520 49624907776 228309 1048576 4031815 6203113472 (ep290 rfl rfl) rfl)) rfl)

noncomputable def ep292 := @ep189 277081483479 1099511627776 4390543790717 26017743648063488 Bool.false 61812606969 1099511627776 4371729102787 26017743648063488 Bool.true 208466225086198240509952 379197854429 1099511627776 91777543247459 26017743648063488 Bool.true 71444057669973022081024 16244497981 274877906944 11484023066015 3252217956007936 (ep190 (BSN.head_sum_c_succ qz14 14 15 rfl rfl) (ep281 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep282 ep291) rfl rfl

noncomputable abbrev qz870 := (@Nat.cast Real Real.instNatCast 16)

noncomputable abbrev qz318 := (@Inv.inv Real Real.instInv (Real.sqrt qz870))

noncomputable abbrev qz319 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 16 1)))

noncomputable def ep293 := @Enclosure.Complex.IsNear.of_eq qz843 (Complex.mk (@HMul.hMul Real Real Real qz0 qz318 (Real.cos qz319)) (@HMul.hMul Real Real Real qz0 qz318 (@Neg.neg Real Real.instNeg (Real.sin qz319)))) Bool.false 31654029393 549755813888 2116689553633 13008871824031744 Bool.false 133743523599 549755813888 2125904919679 13008871824031744 (BSN.cpow_neg_s_mk qz11 121891 1000 16 (@Eq.refl Real qz11) rfl)

noncomputable abbrev qz871 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16) qz267)

noncomputable def ep294 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz870) 4194305 1048576 1 1048576 131071 131072 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz870) (Real.sqrt qz871) Bool.false 4194305 1048576 1 1048576 (BSN.sqrt_natCast_div_one 16) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz871) Bool.false 4194305 1048576 1 1048576 4194305 1048576 1 1048576 (BSN.sqrt_enclosure 16 1 2097152 2097153 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep295 := BSN.log_dyadic_bound 0 32 1 0 1 524288 189304 0 1 0 32 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 32) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz320 := (Real.log (Enclosure.sfrac Bool.false 16 1))

noncomputable def ep296 := @Enclosure.Real.IsNear.mulLit_ff qz11 qz320 121891 1000 0 1 3121657384082679 1125899906842624 31250000023663 5915750000000000000 380501940203221825989 1125899906842624000 3809093752884306733 5915750000000000000000 qz272 (BSN.isNear_log_sfrac 16 1 3121657384082679 1125899906842624 31250000023663 5915750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz871) Bool.false 52372720210750067441664 18889465931478580854784 1000000000757216 189304000000000000000 3121657384082679 1125899906842624 31250000023663 5915750000000000000 (BSN.log_rat_reduce_isNear 16 1 4 32 32 0 524288 24973259072661432 36028797018963968 189304 1000000000000000 rfl rfl rfl rfl (ep295 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep297 := nat_lit 62040069194151175945193759764632241

noncomputable def ep298 := BSN.sin_dyadic_bound_f 499077589 2147483648 2 1 1048576 378978 ep297 ep106 ep297 ep297 ep107 ep297 241502 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 499077589) qz268 0 1 ep297 ep106 ep297 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 499077589) qz269 0 1 ep297 ep107 ep297 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz872 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 177185023) qz279)

noncomputable def ep299 := @Enclosure.Real.IsNear.cos_image qz319 qz872 Bool.false 177185023 524288 169 262144 Bool.false 241502 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz319 Bool.false 380501940203221825989 1125899906842624000 3809093752884306733 5915750000000000000000 177185023 524288 169 262144 (ep296 rfl) rfl) (Enclosure.sfrac_false_div 177185023 524288) (BSN.cos_reduce3 qz872 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 17559731625699580051456) qz281) 226375608064910080 72057594037927936 Bool.false 241502 1048576 53 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q3 177185023 524288 226375608064910080 72057594037927936 53 17559731625699580051456 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 241502 1048576 17559731625699580051456 75557863725914323419136 499077589 2147483648 378978 378608 (ep298 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep300 := BSN.cos_dyadic_bound_f 499077589 2147483648 2 1 1048576 378978 ep297 ep110 ep297 ep297 ep111 ep297 1020386 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 499077589) qz274 0 1 ep297 ep110 ep297 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 499077589) qz275 0 1 ep297 ep111 ep297 rfl rfl rfl rfl) rfl rfl

noncomputable def ep301 := @Enclosure.Real.IsNear.sin_image qz319 qz872 Bool.false 177185023 524288 169 262144 Bool.true 1020386 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz319 Bool.false 380501940203221825989 1125899906842624000 3809093752884306733 5915750000000000000000 177185023 524288 169 262144 (ep296 rfl) rfl) (Enclosure.sfrac_false_div 177185023 524288) (BSN.sin_reduce3 qz872 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 17559731625699580051456) qz281) 226375608064910080 72057594037927936 Bool.false 1020386 1048576 53 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q3 177185023 524288 226375608064910080 72057594037927936 53 17559731625699580051456 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1020386 1048576 17559731625699580051456 75557863725914323419136 499077589 2147483648 378978 378608 (ep300 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz580 := (@Enclosure.Real.IsNear.recentre' qz318 Bool.false 262143 1048576 1 1048576 262143 1048576 1 1048576 (ep294 rfl rfl) rfl)

noncomputable def ep302 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz318 (Real.cos qz319)) (@HMul.hMul Real Real Real qz0 qz318 (@Neg.neg Real Real.instNeg (Real.sin qz319))) Bool.false 31654029393 549755813888 2116689553633 13008871824031744 Bool.false 133743523599 549755813888 2125904919679 13008871824031744 (@Enclosure.Real.IsNear.mulLit_ff qz318 (Real.cos qz319) 262143 1048576 1 1048576 120751 524288 4031815 6203113472 31654029393 549755813888 2116689553633 13008871824031744 qz580 (@Enclosure.Real.IsNear.recentre' (Real.cos qz319) Bool.false 241502 1048576 32254520 49624907776 120751 524288 4031815 6203113472 (ep299 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz318 (@Neg.neg Real Real.instNeg (Real.sin qz319)) 262143 1048576 1 1048576 510193 524288 4031815 6203113472 133743523599 549755813888 2125904919679 13008871824031744 qz580 (@Enclosure.Real.IsNear.neg (Real.sin qz319) Bool.true 510193 524288 4031815 6203113472 (@Enclosure.Real.IsNear.recentre' (Real.sin qz319) Bool.true 1020386 1048576 32254520 49624907776 510193 524288 4031815 6203113472 (ep301 rfl rfl) rfl)) rfl)

noncomputable def ep303 := @ep187 31654029393 549755813888 2116689553633 13008871824031744 Bool.false 133743523599 549755813888 2125904919679 13008871824031744 Bool.true 173662251702631461289984 315889795643 1099511627776 96010922354725 26017743648063488 Bool.false 27832632625461962211328 101254527637 549755813888 48061997183739 13008871824031744 (ep188 (BSN.head_sum_c_succ qz14 15 16 rfl rfl) (ep292 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep293 ep302) rfl rfl

theorem EMRow40.d8 : Enclosure.Complex.IsNear (BSN.headSumC qz14 17) Bool.true 315889795643 1099511627776 96010922354725 26017743648063488 Bool.false 101254527637 549755813888 48061997183739 13008871824031744 := ep186 (BSN.head_sum_c_succ qz14 16 17 rfl rfl) (ep303 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz873 := (@HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast 24) qz17)

noncomputable def ep304 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 25) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz14 24) qz873) Bool.false 485967511519 549755813888 63105837126949 13008871824031744 Bool.false 160003348715 1099511627776 126262687256917 26017743648063488

noncomputable def ep305 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz14 24) qz873 Bool.false 1100626185827 1099511627776 122745568121085 26017743648063488 Bool.true 23871991171 1099511627776 122790480258455 26017743648063488 Bool.true

noncomputable abbrev qz874 := (@Nat.cast Complex Complex.instNatCast 23)

noncomputable def ep306 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 24) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz14 23) (@HPow.hPow Complex Complex Complex qz16 qz874 qz17)) Bool.false 1100626185827 1099511627776 122745568121085 26017743648063488 Bool.true 23871991171 1099511627776 122790480258455 26017743648063488

noncomputable def ep307 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz14 23) (@HPow.hPow Complex Complex Complex qz16 qz874 qz17) Bool.false 993784972019 1099511627776 119207876418717 26017743648063488 Bool.true 113359345175 549755813888 931581235967 203263622250496 Bool.false

noncomputable abbrev qz875 := (@Nat.cast Complex Complex.instNatCast 22)

noncomputable def ep308 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 23) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz14 22) (@HPow.hPow Complex Complex Complex qz16 qz875 qz17)) Bool.false 993784972019 1099511627776 119207876418717 26017743648063488 Bool.true 113359345175 549755813888 931581235967 203263622250496

noncomputable def ep309 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz14 22) (@HPow.hPow Complex Complex Complex qz16 qz875 qz17) Bool.false 47816781251 68719476736 28894572327315 6504435912015872 Bool.true 139048727159 549755813888 14453947735923 3252217956007936 Bool.false

noncomputable abbrev qz876 := (@Nat.cast Complex Complex.instNatCast 21)

noncomputable def ep310 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 22) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz14 21) (@HPow.hPow Complex Complex Complex qz16 qz876 qz17)) Bool.false 47816781251 68719476736 28894572327315 6504435912015872 Bool.true 139048727159 549755813888 14453947735923 3252217956007936

noncomputable def ep311 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz14 21) (@HPow.hPow Complex Complex Complex qz16 qz876 qz17) Bool.false 4244673675 8589934592 27960546370387 6504435912015872 Bool.true 93237533015 549755813888 13990299020821 3252217956007936 Bool.false

noncomputable abbrev qz877 := (@Nat.cast Complex Complex.instNatCast 20)

noncomputable def ep312 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 21) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz14 20) (@HPow.hPow Complex Complex Complex qz16 qz877 qz17)) Bool.false 4244673675 8589934592 27960546370387 6504435912015872 Bool.true 93237533015 549755813888 13990299020821 3252217956007936

noncomputable def ep313 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz14 20) (@HPow.hPow Complex Complex Complex qz16 qz877 qz17) Bool.false 179886776255 549755813888 54021151598159 13008871824031744 Bool.true 22897064773 1099511627776 108124524951429 26017743648063488 Bool.false

noncomputable abbrev qz878 := (@Nat.cast Complex Complex.instNatCast 19)

noncomputable def ep314 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 20) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz14 19) (@HPow.hPow Complex Complex Complex qz16 qz878 qz17)) Bool.false 179886776255 549755813888 54021151598159 13008871824031744 Bool.true 22897064773 1099511627776 108124524951429 26017743648063488

noncomputable def ep315 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz14 19) (@HPow.hPow Complex Complex Complex qz16 qz878 qz17) Bool.false 88385830543 549755813888 52072364117375 13008871824031744 Bool.false 150704262049 1099511627776 104227874692575 26017743648063488 Bool.false

noncomputable abbrev qz879 := (@Nat.cast Complex Complex.instNatCast 18)

noncomputable def ep316 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 19) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz14 18) (@HPow.hPow Complex Complex Complex qz16 qz879 qz17)) Bool.false 88385830543 549755813888 52072364117375 13008871824031744 Bool.false 150704262049 1099511627776 104227874692575 26017743648063488

noncomputable def ep317 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz14 18) (@HPow.hPow Complex Complex Complex qz16 qz879 qz17) Bool.true 56373538895 1099511627776 100136521629777 26017743648063488 Bool.false 65966266515 274877906944 25057788941053 6504435912015872 Bool.false

noncomputable abbrev qz880 := (@Nat.cast Complex Complex.instNatCast 17)

noncomputable def ep318 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 18) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz14 17) (@HPow.hPow Complex Complex Complex qz16 qz880 qz17)) Bool.true 56373538895 1099511627776 100136521629777 26017743648063488 Bool.false 65966266515 274877906944 25057788941053 6504435912015872

noncomputable def ep319 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz14 17) (@HPow.hPow Complex Complex Complex qz16 qz880 qz17) Bool.true 315889795643 1099511627776 96010922354725 26017743648063488 Bool.false 101254527637 549755813888 48061997183739 13008871824031744 Bool.false

noncomputable abbrev qz881 := (@Nat.cast Real Real.instNatCast 17)

noncomputable abbrev qz321 := (@Inv.inv Real Real.instInv (Real.sqrt qz881))

noncomputable abbrev qz322 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 17 1)))

noncomputable def ep320 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz880 qz17) (Complex.mk (@HMul.hMul Real Real Real qz0 qz321 (Real.cos qz322)) (@HMul.hMul Real Real Real qz0 qz321 (@Neg.neg Real Real.instNeg (Real.sin qz322)))) Bool.false 64879064187 274877906944 1031399818763 6504435912015872 Bool.false 30678005393 549755813888 2053580698367 13008871824031744 (BSN.cpow_neg_s_mk qz11 121891 1000 17 (@Eq.refl Real qz11) rfl)

noncomputable abbrev qz882 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 17) qz267)

noncomputable def ep321 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz881) 4323389 1048576 1 1048576 127158 127159 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz881) (Real.sqrt qz882) Bool.false 4323389 1048576 1 1048576 (BSN.sqrt_natCast_div_one 17) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz882) Bool.false 4323389 1048576 1 1048576 4323389 1048576 1 1048576 (BSN.sqrt_enclosure 17 1 2161694 2161695 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep322 := BSN.log_dyadic_bound 1 33 2 1 3267 524288 189304 1 1 31784 34 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1) (BSN.artanhQ 33) 0 1 1 3267 1 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz323 := (Real.log (Enclosure.sfrac Bool.false 17 1))

noncomputable def ep323 := @Enclosure.Real.IsNear.mulLit_ff qz11 qz323 121891 1000 0 1 3189913004350711 1125899906842624 31250000023663 5915750000000000000 388821686013312514501 1125899906842624000 3809093752884306733 5915750000000000000000 qz272 (BSN.isNear_log_sfrac 17 1 3189913004350711 1125899906842624 31250000023663 5915750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz882) Bool.false 53517859495200818200576 18889465931478580854784 1000000000757216 189304000000000000000 3189913004350711 1125899906842624 31250000023663 5915750000000000000 (BSN.log_rat_reduce_isNear 17 1 4 34 32 31784 524288 24973259072661432 36028797018963968 189304 1000000000000000 rfl rfl rfl rfl (ep322 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep324 := nat_lit 4396727607552763561016672286238769736204755615109337965164672535959140418417185

noncomputable def ep325 := nat_lit 4663744977240775338331481105591426838425181476701613483976798116791164564001

noncomputable def ep326 := nat_lit 11507688146960752833067319304073439379940719174324082534552465635322943972274721

noncomputable def ep327 := BSN.sin_dyadic_bound_f 2874695501 2147483648 3 2 1048576 378978 ep324 ep88 ep325 ep326 ep91 ep325 1020444 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2874695501) qz268 0 2 ep324 ep88 ep325 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2874695501) qz269 0 2 ep326 ep91 ep325 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz883 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 362118413) qz270)

noncomputable def ep328 := @Enclosure.Real.IsNear.cos_image qz322 qz883 Bool.false 362118413 1048576 169 262144 Bool.false 1020444 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz322 Bool.false 388821686013312514501 1125899906842624000 3809093752884306733 5915750000000000000000 362118413 1048576 169 262144 (ep323 rfl) rfl) (Enclosure.sfrac_false_div 362118413 1048576) (BSN.cos_reduce3 qz883 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 202288712328069687279616) qz273) 226375608064910080 72057594037927936 Bool.false 1020444 1048576 54 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q3 362118413 1048576 226375608064910080 72057594037927936 54 202288712328069687279616 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1020444 1048576 202288712328069687279616 151115727451828646838272 2874695501 2147483648 378978 378608 (ep327 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep329 := nat_lit 2444699224185864545159631928401801598708608755717055142195474430251429638926881

noncomputable def ep330 := nat_lit 7324770182603112084802232822994221942448975904197762199618469694520706587652641

noncomputable def ep331 := BSN.cos_dyadic_bound_f 2874695501 2147483648 3 2 1048576 378978 ep329 ep95 ep325 ep330 ep97 ep325 241258 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2874695501) qz274 0 2 ep329 ep95 ep325 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2874695501) qz275 0 2 ep330 ep97 ep325 rfl rfl rfl rfl) rfl rfl

noncomputable def ep332 := @Enclosure.Real.IsNear.sin_image qz322 qz883 Bool.false 362118413 1048576 169 262144 Bool.true 241258 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz322 Bool.false 388821686013312514501 1125899906842624000 3809093752884306733 5915750000000000000000 362118413 1048576 169 262144 (ep323 rfl) rfl) (Enclosure.sfrac_false_div 362118413 1048576) (BSN.sin_reduce3 qz883 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 202288712328069687279616) qz273) 226375608064910080 72057594037927936 Bool.false 241258 1048576 54 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q3 362118413 1048576 226375608064910080 72057594037927936 54 202288712328069687279616 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 241258 1048576 202288712328069687279616 151115727451828646838272 2874695501 2147483648 378978 378608 (ep331 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz581 := (@Enclosure.Real.IsNear.recentre' qz321 Bool.false 254317 1048576 1 1048576 254317 1048576 1 1048576 (ep321 rfl rfl) rfl)

noncomputable def ep333 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz321 (Real.cos qz322)) (@HMul.hMul Real Real Real qz0 qz321 (@Neg.neg Real Real.instNeg (Real.sin qz322))) Bool.false 64879064187 274877906944 1031399818763 6504435912015872 Bool.false 30678005393 549755813888 2053580698367 13008871824031744 (@Enclosure.Real.IsNear.mulLit_ff qz321 (Real.cos qz322) 254317 1048576 1 1048576 255111 262144 4031815 6203113472 64879064187 274877906944 1031399818763 6504435912015872 qz581 (@Enclosure.Real.IsNear.recentre' (Real.cos qz322) Bool.false 1020444 1048576 32254520 49624907776 255111 262144 4031815 6203113472 (ep328 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz321 (@Neg.neg Real Real.instNeg (Real.sin qz322)) 254317 1048576 1 1048576 120629 524288 4031815 6203113472 30678005393 549755813888 2053580698367 13008871824031744 qz581 (@Enclosure.Real.IsNear.neg (Real.sin qz322) Bool.true 120629 524288 4031815 6203113472 (@Enclosure.Real.IsNear.recentre' (Real.sin qz322) Bool.true 241258 1048576 32254520 49624907776 120629 524288 4031815 6203113472 (ep332 rfl rfl) rfl)) rfl)

noncomputable def ep334 := @ep319 64879064187 274877906944 1031399818763 6504435912015872 Bool.false 30678005393 549755813888 2053580698367 13008871824031744 Bool.true 15495840378483774586880 56373538895 1099511627776 100136521629777 26017743648063488 Bool.false 72530677074213092720640 65966266515 274877906944 25057788941053 6504435912015872 EMRow40.d8 (ep320 ep333) rfl rfl

noncomputable abbrev qz884 := (@Nat.cast Real Real.instNatCast 18)

noncomputable abbrev qz324 := (@Inv.inv Real Real.instInv (Real.sqrt qz884))

noncomputable abbrev qz325 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 18 1)))

noncomputable def ep335 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz879 qz17) (Complex.mk (@HMul.hMul Real Real Real qz0 qz324 (Real.cos qz325)) (@HMul.hMul Real Real Real qz0 qz324 (@Neg.neg Real Real.instNeg (Real.sin qz325)))) Bool.false 233145199981 1099511627776 4008206604973 26017743648063488 Bool.true 113160804011 1099511627776 3996718928363 26017743648063488 (BSN.cpow_neg_s_mk qz11 121891 1000 18 (@Eq.refl Real qz11) rfl)

noncomputable abbrev qz885 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 18) qz267)

noncomputable def ep336 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz884) 4448731 1048576 1 1048576 123575 123576 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz884) (Real.sqrt qz885) Bool.false 4448731 1048576 1 1048576 (BSN.sqrt_natCast_div_one 18) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz885) Bool.false 4448731 1048576 1 1048576 4448731 1048576 1 1048576 (BSN.sqrt_enclosure 18 1 2224365 2224366 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep337 := BSN.log_dyadic_bound 2 34 3 2 20045040 524288 189304 23168 48 61752 36 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 2) (BSN.artanhQ 34) 0 2 23168 20045040 48 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz326 := (Real.log (Enclosure.sfrac Bool.false 18 1))

noncomputable def ep338 := @Enclosure.Real.IsNear.mulLit_ff qz11 qz326 121891 1000 0 1 3254268794313975 1125899906842624 31250000023663 5915750000000000000 15866643104308989069 45035996273704960 3809093752884306733 5915750000000000000000 qz272 (BSN.isNear_log_sfrac 18 1 3254268794313975 1125899906842624 31250000023663 5915750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz885) Bool.false 54597570484265130393600 18889465931478580854784 1000000000757216 189304000000000000000 3254268794313975 1125899906842624 31250000023663 5915750000000000000 (BSN.log_rat_reduce_isNear 18 1 4 36 32 61752 524288 24973259072661432 36028797018963968 189304 1000000000000000 rfl rfl rfl rfl (ep337 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep339 := nat_lit 886710135913904411387213500108416016

noncomputable def ep340 := BSN.cos_dyadic_bound_f 970388002 2147483648 2 1 1048576 378978 ep339 ep110 ep339 ep339 ep111 ep339 943331 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 970388002) qz274 0 1 ep339 ep110 ep339 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 970388002) qz275 0 1 ep339 ep111 ep339 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz582 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 46178009) (@Nat.cast Real Real.instNatCast 131072))

noncomputable def ep341 := @Enclosure.Real.IsNear.cos_image qz325 qz582 Bool.false 46178009 131072 169 262144 Bool.false 943331 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz325 Bool.false 15866643104308989069 45035996273704960 3809093752884306733 5915750000000000000000 46178009 131072 169 262144 (ep338 rfl) rfl) (Enclosure.sfrac_false_div 46178009 131072) (BSN.cos_reduce0 qz582 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8535623139972882628608) qz565) 226375608064910080 72057594037927936 Bool.false 943331 1048576 56 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q0 46178009 131072 226375608064910080 72057594037927936 56 8535623139972882628608 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 943331 1048576 8535623139972882628608 18889465931478580854784 970388002 2147483648 378978 378608 (ep340 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep342 := BSN.sin_dyadic_bound_f 970388002 2147483648 2 1 1048576 378978 ep339 ep106 ep339 ep339 ep107 ep339 457861 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 970388002) qz268 0 1 ep339 ep106 ep339 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 970388002) qz269 0 1 ep339 ep107 ep339 rfl rfl rfl rfl) rfl rfl

noncomputable def ep343 := @Enclosure.Real.IsNear.sin_image qz325 qz582 Bool.false 46178009 131072 169 262144 Bool.false 457861 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz325 Bool.false 15866643104308989069 45035996273704960 3809093752884306733 5915750000000000000000 46178009 131072 169 262144 (ep338 rfl) rfl) (Enclosure.sfrac_false_div 46178009 131072) (BSN.sin_reduce0 qz582 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8535623139972882628608) qz565) 226375608064910080 72057594037927936 Bool.false 457861 1048576 56 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q0 46178009 131072 226375608064910080 72057594037927936 56 8535623139972882628608 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 457861 1048576 8535623139972882628608 18889465931478580854784 970388002 2147483648 378978 378608 (ep342 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz583 := (@Enclosure.Real.IsNear.recentre' qz324 Bool.false 247151 1048576 1 1048576 247151 1048576 1 1048576 (ep336 rfl rfl) rfl)

noncomputable def ep344 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz324 (Real.cos qz325)) (@HMul.hMul Real Real Real qz0 qz324 (@Neg.neg Real Real.instNeg (Real.sin qz325))) Bool.false 233145199981 1099511627776 4008206604973 26017743648063488 Bool.true 113160804011 1099511627776 3996718928363 26017743648063488 (@Enclosure.Real.IsNear.mulLit_ff qz324 (Real.cos qz325) 247151 1048576 1 1048576 943331 1048576 4031815 6203113472 233145199981 1099511627776 4008206604973 26017743648063488 qz583 (@Enclosure.Real.IsNear.recentre' (Real.cos qz325) Bool.false 943331 1048576 32254520 49624907776 943331 1048576 4031815 6203113472 (ep341 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz324 (@Neg.neg Real Real.instNeg (Real.sin qz325)) 247151 1048576 1 1048576 457861 1048576 4031815 6203113472 113160804011 1099511627776 3996718928363 26017743648063488 qz583 (@Enclosure.Real.IsNear.neg (Real.sin qz325) Bool.false 457861 1048576 4031815 6203113472 (@Enclosure.Real.IsNear.recentre' (Real.sin qz325) Bool.false 457861 1048576 32254520 49624907776 457861 1048576 4031815 6203113472 (ep343 rfl rfl) rfl)) rfl)

noncomputable def ep345 := @ep317 233145199981 1099511627776 4008206604973 26017743648063488 Bool.true 113160804011 1099511627776 3996718928363 26017743648063488 Bool.false 194362496825335255924736 88385830543 549755813888 52072364117375 13008871824031744 Bool.false 41425272119569212768256 150704262049 1099511627776 104227874692575 26017743648063488 (ep318 (BSN.head_sum_c_succ qz14 17 18 rfl rfl) (ep334 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep335 ep344) rfl rfl

noncomputable abbrev qz886 := (@Nat.cast Real Real.instNatCast 19)

noncomputable abbrev qz327 := (@Inv.inv Real Real.instInv (Real.sqrt qz886))

noncomputable abbrev qz328 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 19 1)))

noncomputable def ep346 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz878 qz17) (Complex.mk (@HMul.hMul Real Real Real qz0 qz327 (Real.cos qz328)) (@HMul.hMul Real Real Real qz0 qz327 (@Neg.neg Real Real.instNeg (Real.sin qz328)))) Bool.false 5718809107 34359738368 121799217549 813054489001984 Bool.true 86800663411 549755813888 1948325129427 13008871824031744 (BSN.cpow_neg_s_mk qz11 121891 1000 19 (@Eq.refl Real qz11) rfl)

noncomputable abbrev qz887 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 19) qz267)

noncomputable def ep347 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz886) 4570637 1048576 1 1048576 120279 120280 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz886) (Real.sqrt qz887) Bool.false 4570637 1048576 1 1048576 (BSN.sqrt_natCast_div_one 19) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz887) Bool.false 4570637 1048576 1 1048576 4570637 1048576 1 1048576 (BSN.sqrt_enclosure 19 1 2285318 2285319 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep348 := BSN.log_dyadic_bound 3 35 3 2 22509375 524288 189304 55368 243 90099 38 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 3) (BSN.artanhQ 35) 0 2 55368 22509375 243 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz329 := (Real.log (Enclosure.sfrac Bool.false 19 1))

noncomputable def ep349 := @Enclosure.Real.IsNear.mulLit_ff qz11 qz329 121891 1000 0 1 3315143513283831 1125899906842624 31250000023663 5915750000000000000 404086157977679444421 1125899906842624000 3809093752884306733 5915750000000000000000 qz272 (BSN.isNear_log_sfrac 19 1 3315143513283831 1125899906842624 31250000023663 5915750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz887) Bool.false 55618878793361701994496 18889465931478580854784 1000000000757216 189304000000000000000 3315143513283831 1125899906842624 31250000023663 5915750000000000000 (BSN.log_rat_reduce_isNear 19 1 4 38 32 90099 524288 24973259072661432 36028797018963968 189304 1000000000000000 rfl rfl rfl rfl (ep348 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep350 := nat_lit 252289294460326331277092653754610940749153840396542141173361954093614640800000

noncomputable def ep351 := nat_lit 49838911951397371957041978986340702137793538812546862721264162208100000000

noncomputable def ep352 := nat_lit 756768205557076199087363877305860140843185934112001329794643333956427722400000

noncomputable def ep353 := BSN.cos_dyadic_bound_f 1630031770 2147483648 3 2 1048576 378978 ep350 ep95 ep351 ep352 ep97 ep351 760736 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1630031770) qz274 0 2 ep350 ep95 ep351 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1630031770) qz275 0 2 ep352 ep97 ep351 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz888 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 376334561) qz270)

noncomputable def ep354 := @Enclosure.Real.IsNear.cos_image qz328 qz888 Bool.false 376334561 1048576 169 262144 Bool.false 760736 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz328 Bool.false 404086157977679444421 1125899906842624000 3809093752884306733 5915750000000000000000 376334561 1048576 169 262144 (ep349 rfl) rfl) (Enclosure.sfrac_false_div 376334561 1048576) (BSN.cos_reduce0 qz888 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 114703288641831621885952) qz273) 226375608064910080 72057594037927936 Bool.false 760736 1048576 57 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q0 376334561 1048576 226375608064910080 72057594037927936 57 114703288641831621885952 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 760736 1048576 114703288641831621885952 151115727451828646838272 1630031770 2147483648 378978 378608 (ep353 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep355 := nat_lit 7059667977419148566699392063022410000

noncomputable def ep356 := BSN.sin_dyadic_bound_f 1630031770 2147483648 2 1 1048576 378978 ep355 ep106 ep355 ep355 ep107 ep355 721658 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1630031770) qz268 0 1 ep355 ep106 ep355 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1630031770) qz269 0 1 ep355 ep107 ep355 rfl rfl rfl rfl) rfl rfl

noncomputable def ep357 := @Enclosure.Real.IsNear.sin_image qz328 qz888 Bool.false 376334561 1048576 169 262144 Bool.false 721658 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz328 Bool.false 404086157977679444421 1125899906842624000 3809093752884306733 5915750000000000000000 376334561 1048576 169 262144 (ep349 rfl) rfl) (Enclosure.sfrac_false_div 376334561 1048576) (BSN.sin_reduce0 qz888 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 114703288641831621885952) qz273) 226375608064910080 72057594037927936 Bool.false 721658 1048576 57 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q0 376334561 1048576 226375608064910080 72057594037927936 57 114703288641831621885952 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 721658 1048576 114703288641831621885952 151115727451828646838272 1630031770 2147483648 378978 378608 (ep356 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz584 := (@Enclosure.Real.IsNear.recentre' qz327 Bool.false 240559 1048576 1 1048576 240559 1048576 1 1048576 (ep347 rfl rfl) rfl)

noncomputable def ep358 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz327 (Real.cos qz328)) (@HMul.hMul Real Real Real qz0 qz327 (@Neg.neg Real Real.instNeg (Real.sin qz328))) Bool.false 5718809107 34359738368 121799217549 813054489001984 Bool.true 86800663411 549755813888 1948325129427 13008871824031744 (@Enclosure.Real.IsNear.mulLit_ff qz327 (Real.cos qz328) 240559 1048576 1 1048576 23773 32768 4031815 6203113472 5718809107 34359738368 121799217549 813054489001984 qz584 (@Enclosure.Real.IsNear.recentre' (Real.cos qz328) Bool.false 760736 1048576 32254520 49624907776 23773 32768 4031815 6203113472 (ep354 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz327 (@Neg.neg Real Real.instNeg (Real.sin qz328)) 240559 1048576 1 1048576 360829 524288 4031815 6203113472 86800663411 549755813888 1948325129427 13008871824031744 qz584 (@Enclosure.Real.IsNear.neg (Real.sin qz328) Bool.false 360829 524288 4031815 6203113472 (@Enclosure.Real.IsNear.recentre' (Real.sin qz328) Bool.false 721658 1048576 32254520 49624907776 360829 524288 4031815 6203113472 (ep357 rfl rfl) rfl)) rfl)

noncomputable def ep359 := @ep315 5718809107 34359738368 121799217549 813054489001984 Bool.true 86800663411 549755813888 1948325129427 13008871824031744 Bool.false 6180862567984754851840 179886776255 549755813888 54021151598159 13008871824031744 Bool.true 12587794479926868967424 22897064773 1099511627776 108124524951429 26017743648063488 (ep316 (BSN.head_sum_c_succ qz14 18 19 rfl rfl) (ep345 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep346 ep358) rfl rfl

noncomputable abbrev qz889 := (@Nat.cast Real Real.instNatCast 20)

noncomputable abbrev qz330 := (@Inv.inv Real Real.instInv (Real.sqrt qz889))

noncomputable abbrev qz331 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 20 1)))

noncomputable def ep360 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz877 qz17) (Complex.mk (@HMul.hMul Real Real Real qz0 qz330 (Real.cos qz331)) (@HMul.hMul Real Real Real qz0 qz330 (@Neg.neg Real Real.instNeg (Real.sin qz331)))) Bool.false 91772338945 549755813888 1899941142615 13008871824031744 Bool.true 163578001257 1099511627776 3797867215139 26017743648063488 (BSN.cpow_neg_s_mk qz11 121891 1000 20 (@Eq.refl Real qz11) rfl)

noncomputable abbrev qz890 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 20) qz267)

noncomputable def ep361 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz889) 4689375 1048576 1 1048576 117234 117235 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz889) (Real.sqrt qz890) Bool.false 4689375 1048576 1 1048576 (BSN.sqrt_natCast_div_one 20) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz890) Bool.false 4689375 1048576 1 1048576 4689375 1048576 1 1048576 (BSN.sqrt_enclosure 20 1 2344687 2344688 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep362 := BSN.log_dyadic_bound 4 36 3 2 25194240 524288 189304 104448 768 116991 40 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 4) (BSN.artanhQ 36) 0 2 104448 25194240 768 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz332 := (Real.log (Enclosure.sfrac Bool.false 20 1))

noncomputable def ep363 := @Enclosure.Real.IsNear.mulLit_ff qz11 qz332 121891 1000 0 1 3372893643545847 1125899906842624 31250000023663 5915750000000000000 411125379105446836677 1125899906842624000 3809093752884306733 5915750000000000000000 qz272 (BSN.isNear_log_sfrac 20 1 3372893643545847 1125899906842624 31250000023663 5915750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz890) Bool.false 56587765202795681021952 18889465931478580854784 1000000000757216 189304000000000000000 3372893643545847 1125899906842624 31250000023663 5915750000000000000 (BSN.log_rat_reduce_isNear 20 1 4 40 32 116991 524288 24973259072661432 36028797018963968 189304 1000000000000000 rfl rfl rfl rfl (ep362 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep364 := nat_lit 213405643995892786509304176375416341158394776423639276307792879662132819690625

noncomputable def ep365 := nat_lit 35662283805620329606681147246890351709581654046000093548770004509062890625

noncomputable def ep366 := nat_lit 640145607420067118868699166831755242771765165962825828736281098977380333290625

noncomputable def ep367 := BSN.cos_dyadic_bound_f 1563241745 2147483648 3 2 1048576 378978 ep364 ep95 ep365 ep366 ep97 ep365 782810 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1563241745) qz274 0 2 ep364 ep95 ep365 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1563241745) qz275 0 2 ep366 ep97 ep365 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz891 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 191445173) qz279)

noncomputable def ep368 := @Enclosure.Real.IsNear.cos_image qz331 qz891 Bool.false 191445173 524288 169 262144 Bool.false 782810 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz331 Bool.false 411125379105446836677 1125899906842624000 3809093752884306733 5915750000000000000000 191445173 524288 169 262144 (ep363 rfl) rfl) (Enclosure.sfrac_false_div 191445173 524288) (BSN.cos_reduce0 qz891 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 55001679246310900760576) qz281) 226375608064910080 72057594037927936 Bool.false 782810 1048576 58 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q0 191445173 524288 226375608064910080 72057594037927936 58 55001679246310900760576 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 782810 1048576 55001679246310900760576 75557863725914323419136 1563241745 2147483648 378978 378608 (ep367 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep369 := nat_lit 5971790669943172883074107981557250625

noncomputable def ep370 := BSN.sin_dyadic_bound_f 1563241745 2147483648 2 1 1048576 378978 ep369 ep106 ep369 ep369 ep107 ep369 697653 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1563241745) qz268 0 1 ep369 ep106 ep369 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1563241745) qz269 0 1 ep369 ep107 ep369 rfl rfl rfl rfl) rfl rfl

noncomputable def ep371 := @Enclosure.Real.IsNear.sin_image qz331 qz891 Bool.false 191445173 524288 169 262144 Bool.false 697653 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz331 Bool.false 411125379105446836677 1125899906842624000 3809093752884306733 5915750000000000000000 191445173 524288 169 262144 (ep363 rfl) rfl) (Enclosure.sfrac_false_div 191445173 524288) (BSN.sin_reduce0 qz891 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 55001679246310900760576) qz281) 226375608064910080 72057594037927936 Bool.false 697653 1048576 58 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q0 191445173 524288 226375608064910080 72057594037927936 58 55001679246310900760576 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 697653 1048576 55001679246310900760576 75557863725914323419136 1563241745 2147483648 378978 378608 (ep370 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz585 := (@Enclosure.Real.IsNear.recentre' qz330 Bool.false 234469 1048576 1 1048576 234469 1048576 1 1048576 (ep361 rfl rfl) rfl)

noncomputable def ep372 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz330 (Real.cos qz331)) (@HMul.hMul Real Real Real qz0 qz330 (@Neg.neg Real Real.instNeg (Real.sin qz331))) Bool.false 91772338945 549755813888 1899941142615 13008871824031744 Bool.true 163578001257 1099511627776 3797867215139 26017743648063488 (@Enclosure.Real.IsNear.mulLit_ff qz330 (Real.cos qz331) 234469 1048576 1 1048576 391405 524288 4031815 6203113472 91772338945 549755813888 1899941142615 13008871824031744 qz585 (@Enclosure.Real.IsNear.recentre' (Real.cos qz331) Bool.false 782810 1048576 32254520 49624907776 391405 524288 4031815 6203113472 (ep368 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz330 (@Neg.neg Real Real.instNeg (Real.sin qz331)) 234469 1048576 1 1048576 697653 1048576 4031815 6203113472 163578001257 1099511627776 3797867215139 26017743648063488 qz585 (@Enclosure.Real.IsNear.neg (Real.sin qz331) Bool.false 697653 1048576 4031815 6203113472 (@Enclosure.Real.IsNear.recentre' (Real.sin qz331) Bool.false 697653 1048576 32254520 49624907776 697653 1048576 4031815 6203113472 (ep371 rfl rfl) rfl)) rfl)

noncomputable def ep373 := @ep313 91772338945 549755813888 1899941142615 13008871824031744 Bool.true 163578001257 1099511627776 3797867215139 26017743648063488 Bool.false 149346177976869951897600 4244673675 8589934592 27960546370387 6504435912015872 Bool.true 205031503390282382049280 93237533015 549755813888 13990299020821 3252217956007936 (ep314 (BSN.head_sum_c_succ qz14 19 20 rfl rfl) (ep359 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep360 ep372) rfl rfl

noncomputable abbrev qz892 := (@Nat.cast Real Real.instNatCast 21)

noncomputable abbrev qz333 := (@Inv.inv Real Real.instInv (Real.sqrt qz892))

noncomputable abbrev qz334 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 21 1)))

noncomputable def ep374 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz876 qz17) (Complex.mk (@HMul.hMul Real Real Real qz0 qz333 (Real.cos qz334)) (@HMul.hMul Real Real Real qz0 qz333 (@Neg.neg Real Real.instNeg (Real.sin qz334)))) Bool.false 13859391851 68719476736 14594155577 101631811125248 Bool.true 1431599817 17179869184 231824357551 1626108978003968 (BSN.cpow_neg_s_mk qz11 121891 1000 21 (@Eq.refl Real qz11) rfl)

noncomputable abbrev qz893 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 21) qz267)

noncomputable def ep375 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz892) 4805179 1048576 1 1048576 114408 114410 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz892) (Real.sqrt qz893) Bool.false 4805179 1048576 1 1048576 (BSN.sqrt_natCast_div_one 21) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz893) Bool.false 4805179 1048576 1 1048576 4805179 1048576 1 1048576 (BSN.sqrt_enclosure 21 1 2402589 2402590 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep376 := BSN.log_dyadic_bound 5 37 4 3 269401272945 524288 189304 1658093375 234375 142571 42 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 5) (BSN.artanhQ 37) 0 3 1658093375 269401272945 234375 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz335 := (Real.log (Enclosure.sfrac Bool.false 21 1))

noncomputable def ep377 := @Enclosure.Real.IsNear.mulLit_ff qz11 qz335 121891 1000 0 1 3427826275261687 1125899906842624 31250000023663 5915750000000000000 417821172517922290117 1125899906842624000 3809093752884306733 5915750000000000000000 qz272 (BSN.isNear_log_sfrac 21 1 3427826275261687 1125899906842624 31250000023663 5915750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz893) Bool.false 57509381830540779323392 18889465931478580854784 1000000000757216 189304000000000000000 3427826275261687 1125899906842624 31250000023663 5915750000000000000 (BSN.log_rat_reduce_isNear 21 1 4 42 32 142571 524288 24973259072661432 36028797018963968 189304 1000000000000000 rfl rfl rfl rfl (ep376 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep378 := nat_lit 501240157575730295610881814839038881

noncomputable def ep379 := BSN.cos_dyadic_bound_f 841417353 2147483648 2 1 1048576 378978 ep378 ep110 ep378 ep378 ep111 ep378 969112 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 841417353) qz274 0 1 ep378 ep110 ep378 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 841417353) qz275 0 1 ep378 ep111 ep378 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz894 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 194563145) qz279)

noncomputable def ep380 := @Enclosure.Real.IsNear.cos_image qz334 qz894 Bool.false 194563145 524288 169 262144 Bool.false 969112 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz334 Bool.false 417821172517922290117 1125899906842624000 3809093752884306733 5915750000000000000000 194563145 524288 169 262144 (ep377 rfl) rfl) (Enclosure.sfrac_false_div 194563145 524288) (BSN.cos_reduce0 qz894 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 29604741237021081600000) qz281) 226375608064910080 72057594037927936 Bool.false 969112 1048576 59 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q0 194563145 524288 226375608064910080 72057594037927936 59 29604741237021081600000 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 969112 1048576 29604741237021081600000 75557863725914323419136 841417353 2147483648 378978 378608 (ep379 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep381 := BSN.sin_dyadic_bound_f 841417353 2147483648 2 1 1048576 378978 ep378 ep106 ep378 ep378 ep107 ep378 400416 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 841417353) qz268 0 1 ep378 ep106 ep378 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 841417353) qz269 0 1 ep378 ep107 ep378 rfl rfl rfl rfl) rfl rfl

noncomputable def ep382 := @Enclosure.Real.IsNear.sin_image qz334 qz894 Bool.false 194563145 524288 169 262144 Bool.false 400416 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz334 Bool.false 417821172517922290117 1125899906842624000 3809093752884306733 5915750000000000000000 194563145 524288 169 262144 (ep377 rfl) rfl) (Enclosure.sfrac_false_div 194563145 524288) (BSN.sin_reduce0 qz894 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 29604741237021081600000) qz281) 226375608064910080 72057594037927936 Bool.false 400416 1048576 59 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q0 194563145 524288 226375608064910080 72057594037927936 59 29604741237021081600000 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 400416 1048576 29604741237021081600000 75557863725914323419136 841417353 2147483648 378978 378608 (ep381 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz586 := (@Enclosure.Real.IsNear.recentre' qz333 Bool.false 228818 1048576 2 1048576 114409 524288 1 524288 (ep375 rfl rfl) rfl)

noncomputable def ep383 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz333 (Real.cos qz334)) (@HMul.hMul Real Real Real qz0 qz333 (@Neg.neg Real Real.instNeg (Real.sin qz334))) Bool.false 13859391851 68719476736 14594155577 101631811125248 Bool.true 1431599817 17179869184 231824357551 1626108978003968 (@Enclosure.Real.IsNear.mulLit_ff qz333 (Real.cos qz334) 114409 524288 1 524288 121139 131072 4031815 6203113472 13859391851 68719476736 14594155577 101631811125248 qz586 (@Enclosure.Real.IsNear.recentre' (Real.cos qz334) Bool.false 969112 1048576 32254520 49624907776 121139 131072 4031815 6203113472 (ep380 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz333 (@Neg.neg Real Real.instNeg (Real.sin qz334)) 114409 524288 1 524288 12513 32768 4031815 6203113472 1431599817 17179869184 231824357551 1626108978003968 qz586 (@Enclosure.Real.IsNear.neg (Real.sin qz334) Bool.false 12513 32768 4031815 6203113472 (@Enclosure.Real.IsNear.recentre' (Real.sin qz334) Bool.false 400416 1048576 32254520 49624907776 12513 32768 4031815 6203113472 (ep382 rfl rfl) rfl)) rfl)

noncomputable def ep384 := @ep311 13859391851 68719476736 14594155577 101631811125248 Bool.true 1431599817 17179869184 231824357551 1626108978003968 Bool.false 410743023346061934592 47816781251 68719476736 28894572327315 6504435912015872 Bool.true 2388838942793327968256 139048727159 549755813888 14453947735923 3252217956007936 (ep312 (BSN.head_sum_c_succ qz14 20 21 rfl rfl) (ep373 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep374 ep383) rfl rfl

noncomputable abbrev qz895 := (@Nat.cast Real Real.instNatCast 22)

noncomputable abbrev qz336 := (@Inv.inv Real Real.instInv (Real.sqrt qz895))

noncomputable abbrev qz337 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 22 1)))

noncomputable def ep385 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz875 qz17) (Complex.mk (@HMul.hMul Real Real Real qz0 qz336 (Real.cos qz337)) (@HMul.hMul Real Real Real qz0 qz336 (@Neg.neg Real Real.instNeg (Real.sin qz337)))) Bool.false 228716472003 1099511627776 3629587109457 26017743648063488 Bool.false 802793187 17179869184 451352039549 3252217956007936 (BSN.cpow_neg_s_mk qz11 121891 1000 22 (@Eq.refl Real qz11) rfl)

noncomputable abbrev qz896 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 22) qz267)

noncomputable def ep386 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz895) 4918257 1048576 1 1048576 111778 111779 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz895) (Real.sqrt qz896) Bool.false 4918257 1048576 1 1048576 (BSN.sqrt_natCast_div_one 22) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz896) Bool.false 4918257 1048576 1 1048576 4918257 1048576 1 1048576 (BSN.sqrt_enclosure 22 1 2459128 2459129 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep387 := BSN.log_dyadic_bound 6 38 4 3 316148320320 524288 189304 2667271104 699840 166961 44 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 6) (BSN.artanhQ 38) 0 3 2667271104 316148320320 699840 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz338 := (Real.log (Enclosure.sfrac Bool.false 22 1))

noncomputable def ep388 := @Enclosure.Real.IsNear.mulLit_ff qz11 qz338 121891 1000 0 1 3480203401436407 1125899906842624 31250000023663 5915750000000000000 424205472804485085637 1125899906842624000 3809093752884306733 5915750000000000000000 qz272 (BSN.isNear_log_sfrac 22 1 3480203401436407 1125899906842624 31250000023663 5915750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz896) Bool.false 58388124189833310502912 18889465931478580854784 1000000000757216 189304000000000000000 3480203401436407 1125899906842624 31250000023663 5915750000000000000 (BSN.log_rat_reduce_isNear 22 1 4 44 32 166961 524288 24973259072661432 36028797018963968 189304 1000000000000000 rfl rfl rfl rfl (ep387 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep389 := nat_lit 4545756278449193310612206295179604828286570763018786328035509289534015700107520

noncomputable def ep390 := nat_lit 4984903708383818256764894919266508857869173502623371018654230376143972106496

noncomputable def ep391 := nat_lit 11897481361362884869663873324172533535933040003187812067967560337694379450204416

noncomputable def ep392 := BSN.sin_dyadic_bound_f 2898725538 2147483648 3 2 1048576 378978 ep389 ep88 ep390 ep391 ep91 ep390 1023079 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2898725538) qz268 0 2 ep389 ep88 ep390 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2898725538) qz269 0 2 ep391 ep91 ep390 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz897 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 395072133) qz270)

noncomputable def ep393 := @Enclosure.Real.IsNear.cos_image qz337 qz897 Bool.false 395072133 1048576 169 262144 Bool.false 1023079 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz337 Bool.false 424205472804485085637 1125899906842624000 3809093752884306733 5915750000000000000000 395072133 1048576 169 262144 (ep388 rfl) rfl) (Enclosure.sfrac_false_div 395072133 1048576) (BSN.cos_reduce3 qz897 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 203979675881739812601856) qz273) 226375608064910080 72057594037927936 Bool.false 1023079 1048576 59 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q3 395072133 1048576 226375608064910080 72057594037927936 59 203979675881739812601856 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1023079 1048576 203979675881739812601856 151115727451828646838272 2898725538 2147483648 378978 378608 (ep392 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep394 := nat_lit 2527635667453277980676454561730565575207147834344936124916907041019406043218176

noncomputable def ep395 := nat_lit 7572937194943066305515833895353163707905705156029561632713412662305930185441536

noncomputable def ep396 := BSN.cos_dyadic_bound_f 2898725538 2147483648 3 2 1048576 378978 ep394 ep95 ep390 ep395 ep97 ep390 229824 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2898725538) qz274 0 2 ep394 ep95 ep390 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2898725538) qz275 0 2 ep395 ep97 ep390 rfl rfl rfl rfl) rfl rfl

noncomputable def ep397 := @Enclosure.Real.IsNear.sin_image qz337 qz897 Bool.false 395072133 1048576 169 262144 Bool.true 229824 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz337 Bool.false 424205472804485085637 1125899906842624000 3809093752884306733 5915750000000000000000 395072133 1048576 169 262144 (ep388 rfl) rfl) (Enclosure.sfrac_false_div 395072133 1048576) (BSN.sin_reduce3 qz897 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 203979675881739812601856) qz273) 226375608064910080 72057594037927936 Bool.false 229824 1048576 59 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q3 395072133 1048576 226375608064910080 72057594037927936 59 203979675881739812601856 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 229824 1048576 203979675881739812601856 151115727451828646838272 2898725538 2147483648 378978 378608 (ep396 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz587 := (@Enclosure.Real.IsNear.recentre' qz336 Bool.false 223557 1048576 1 1048576 223557 1048576 1 1048576 (ep386 rfl rfl) rfl)

noncomputable def ep398 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz336 (Real.cos qz337)) (@HMul.hMul Real Real Real qz0 qz336 (@Neg.neg Real Real.instNeg (Real.sin qz337))) Bool.false 228716472003 1099511627776 3629587109457 26017743648063488 Bool.false 802793187 17179869184 451352039549 3252217956007936 (@Enclosure.Real.IsNear.mulLit_ff qz336 (Real.cos qz337) 223557 1048576 1 1048576 1023079 1048576 4031815 6203113472 228716472003 1099511627776 3629587109457 26017743648063488 qz587 (@Enclosure.Real.IsNear.recentre' (Real.cos qz337) Bool.false 1023079 1048576 32254520 49624907776 1023079 1048576 4031815 6203113472 (ep393 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz336 (@Neg.neg Real Real.instNeg (Real.sin qz337)) 223557 1048576 1 1048576 3591 16384 4031815 6203113472 802793187 17179869184 451352039549 3252217956007936 qz587 (@Enclosure.Real.IsNear.neg (Real.sin qz337) Bool.true 3591 16384 4031815 6203113472 (@Enclosure.Real.IsNear.recentre' (Real.sin qz337) Bool.true 229824 1048576 32254520 49624907776 3591 16384 4031815 6203113472 (ep397 rfl rfl) rfl)) rfl)

noncomputable def ep399 := @ep309 228716472003 1099511627776 3629587109457 26017743648063488 Bool.false 802793187 17179869184 451352039549 3252217956007936 Bool.false 68292383265246081449984 993784972019 1099511627776 119207876418717 26017743648063488 Bool.true 1947498720890401587200 113359345175 549755813888 931581235967 203263622250496 (ep310 (BSN.head_sum_c_succ qz14 21 22 rfl rfl) (ep384 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep385 ep398) rfl rfl

noncomputable abbrev qz898 := (@Nat.cast Real Real.instNatCast 23)

noncomputable abbrev qz339 := (@Inv.inv Real Real.instInv (Real.sqrt qz898))

noncomputable abbrev qz340 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 23 1)))

noncomputable def ep400 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz874 qz17) (Complex.mk (@HMul.hMul Real Real Real qz0 qz339 (Real.cos qz340)) (@HMul.hMul Real Real Real qz0 qz339 (@Neg.neg Real Real.instNeg (Real.sin qz340)))) Bool.false 6677575863 68719476736 110552865699 813054489001984 Bool.false 202846699179 1099511627776 3548082054679 26017743648063488 (BSN.cpow_neg_s_mk qz11 121891 1000 23 (@Eq.refl Real qz11) rfl)

noncomputable abbrev qz899 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 23) qz267)

noncomputable def ep401 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz898) 5028793 1048576 1 1048576 109321 109322 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz898) (Real.sqrt qz899) Bool.false 5028793 1048576 1 1048576 (BSN.sqrt_natCast_div_one 23) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz899) Bool.false 5028793 1048576 1 1048576 5028793 1048576 1 1048576 (BSN.sqrt_enclosure 23 1 2514396 2514397 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep402 := BSN.log_dyadic_bound 7 39 4 3 369468094905 524288 189304 4046006391 1764735 190266 46 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 7) (BSN.artanhQ 39) 0 3 4046006391 369468094905 1764735 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz341 := (Real.log (Enclosure.sfrac Bool.false 23 1))

noncomputable def ep403 := @Enclosure.Real.IsNear.mulLit_ff qz11 qz341 121891 1000 0 1 3530250507853047 1125899906842624 31250000023663 5915750000000000000 430305764652715751877 1125899906842624000 3809093752884306733 5915750000000000000000 qz272 (BSN.isNear_log_sfrac 23 1 3530250507853047 1125899906842624 31250000023663 5915750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz899) Bool.false 59227775304360265777152 18889465931478580854784 1000000000757216 189304000000000000000 3530250507853047 1125899906842624 31250000023663 5915750000000000000 (BSN.log_rat_reduce_isNear 23 1 4 46 32 190266 524288 24973259072661432 36028797018963968 189304 1000000000000000 rfl rfl rfl rfl (ep402 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep404 := nat_lit 1174680891376554692009025902634727696

noncomputable def ep405 := BSN.sin_dyadic_bound_f 1041070106 2147483648 2 1 1048576 378978 ep404 ep106 ep404 ep404 ep107 ep404 488656 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1041070106) qz268 0 1 ep404 ep106 ep404 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1041070106) qz269 0 1 ep404 ep107 ep404 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz588 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6261773) (@Nat.cast Real Real.instNatCast 16384))

noncomputable def ep406 := @Enclosure.Real.IsNear.cos_image qz340 qz588 Bool.false 6261773 16384 169 262144 Bool.false 488656 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz340 Bool.false 430305764652715751877 1125899906842624000 3809093752884306733 5915750000000000000000 6261773 16384 169 262144 (ep403 rfl) rfl) (Enclosure.sfrac_false_div 6261773 16384) (BSN.cos_reduce3 qz588 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 1144668687192970756096) (@Nat.cast Real Real.instNatCast 2361183241434822606848)) 226375608064910080 72057594037927936 Bool.false 488656 1048576 60 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q3 6261773 16384 226375608064910080 72057594037927936 60 1144668687192970756096 2361183241434822606848 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 488656 1048576 1144668687192970756096 2361183241434822606848 1041070106 2147483648 378978 378608 (ep405 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep407 := BSN.cos_dyadic_bound_f 1041070106 2147483648 2 1 1048576 378978 ep404 ep110 ep404 ep404 ep111 ep404 927753 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1041070106) qz274 0 1 ep404 ep110 ep404 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1041070106) qz275 0 1 ep404 ep111 ep404 rfl rfl rfl rfl) rfl rfl

noncomputable def ep408 := @Enclosure.Real.IsNear.sin_image qz340 qz588 Bool.false 6261773 16384 169 262144 Bool.true 927753 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz340 Bool.false 430305764652715751877 1125899906842624000 3809093752884306733 5915750000000000000000 6261773 16384 169 262144 (ep403 rfl) rfl) (Enclosure.sfrac_false_div 6261773 16384) (BSN.sin_reduce3 qz588 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 1144668687192970756096) (@Nat.cast Real Real.instNatCast 2361183241434822606848)) 226375608064910080 72057594037927936 Bool.false 927753 1048576 60 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q3 6261773 16384 226375608064910080 72057594037927936 60 1144668687192970756096 2361183241434822606848 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 927753 1048576 1144668687192970756096 2361183241434822606848 1041070106 2147483648 378978 378608 (ep407 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz589 := (@Enclosure.Real.IsNear.recentre' qz339 Bool.false 218643 1048576 1 1048576 218643 1048576 1 1048576 (ep401 rfl rfl) rfl)

noncomputable def ep409 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz339 (Real.cos qz340)) (@HMul.hMul Real Real Real qz0 qz339 (@Neg.neg Real Real.instNeg (Real.sin qz340))) Bool.false 6677575863 68719476736 110552865699 813054489001984 Bool.false 202846699179 1099511627776 3548082054679 26017743648063488 (@Enclosure.Real.IsNear.mulLit_ff qz339 (Real.cos qz340) 218643 1048576 1 1048576 30541 65536 4031815 6203113472 6677575863 68719476736 110552865699 813054489001984 qz589 (@Enclosure.Real.IsNear.recentre' (Real.cos qz340) Bool.false 488656 1048576 32254520 49624907776 30541 65536 4031815 6203113472 (ep406 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz339 (@Neg.neg Real Real.instNeg (Real.sin qz340)) 218643 1048576 1 1048576 927753 1048576 4031815 6203113472 202846699179 1099511627776 3548082054679 26017743648063488 qz589 (@Enclosure.Real.IsNear.neg (Real.sin qz340) Bool.true 927753 1048576 4031815 6203113472 (@Enclosure.Real.IsNear.recentre' (Real.sin qz340) Bool.true 927753 1048576 32254520 49624907776 927753 1048576 4031815 6203113472 (ep408 rfl rfl) rfl)) rfl)

noncomputable def ep410 := @ep307 6677575863 68719476736 110552865699 813054489001984 Bool.false 202846699179 1099511627776 3548082054679 26017743648063488 Bool.false 75634455571970939420672 1100626185827 1099511627776 122745568121085 26017743648063488 Bool.true 13123765935340255182848 23871991171 1099511627776 122790480258455 26017743648063488 (ep308 (BSN.head_sum_c_succ qz14 22 23 rfl rfl) (ep399 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep400 ep409) rfl rfl

noncomputable abbrev qz900 := (@Nat.cast Real Real.instNatCast 24)

noncomputable abbrev qz342 := (@Inv.inv Real Real.instInv (Real.sqrt qz900))

noncomputable abbrev qz343 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 24 1)))

noncomputable def ep411 := @Enclosure.Complex.IsNear.of_eq qz873 (Complex.mk (@HMul.hMul Real Real Real qz0 qz342 (Real.cos qz343)) (@HMul.hMul Real Real Real qz0 qz342 (@Neg.neg Real Real.instNeg (Real.sin qz343)))) Bool.true 128691162789 1099511627776 3466106132813 26017743648063488 Bool.false 91937669943 549755813888 1736103499231 13008871824031744 (BSN.cpow_neg_s_mk qz11 121891 1000 24 (@Eq.refl Real qz11) rfl)

noncomputable abbrev qz901 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 24) qz267)

noncomputable def ep412 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz900) 5136953 1048576 1 1048576 107019 107020 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz900) (Real.sqrt qz901) Bool.false 5136953 1048576 1 1048576 (BSN.sqrt_natCast_div_one 24) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz901) Bool.false 5136953 1048576 1 1048576 5136953 1048576 1 1048576 (BSN.sqrt_enclosure 24 1 2568476 2568477 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep413 := BSN.log_dyadic_bound 8 40 4 3 430080000000 524288 189304 5875957760 3932160 212580 48 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 8) (BSN.artanhQ 40) 0 3 5875957760 430080000000 3932160 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz344 := (Real.log (Enclosure.sfrac Bool.false 24 1))

noncomputable def ep414 := @Enclosure.Real.IsNear.mulLit_ff qz11 qz344 121891 1000 0 1 3578169457974519 1125899906842624 31250000023663 5915750000000000000 436146653401972095429 1125899906842624000 3809093752884306733 5915750000000000000000 qz272 (BSN.isNear_log_sfrac 24 1 3578169457974519 1125899906842624 31250000023663 5915750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz901) Bool.false 60031721881041427759104 18889465931478580854784 1000000000757216 189304000000000000000 3578169457974519 1125899906842624 31250000023663 5915750000000000000 (BSN.log_rat_reduce_isNear 24 1 4 48 32 212580 524288 24973259072661432 36028797018963968 189304 1000000000000000 rfl rfl rfl rfl (ep413 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep415 := nat_lit 646133246133695066591860717059678969173891862612562589795409792444079784969761

noncomputable def ep416 := nat_lit 326698694770605121416067685776362902683432111568866293094238394948418651681

noncomputable def ep417 := nat_lit 1937746341011543989532750015807484181716308723614550036800040900542342517605921

noncomputable def ep418 := BSN.cos_dyadic_bound_f 2061903923 2147483648 3 2 1048576 378978 ep415 ep95 ep416 ep417 ep97 ep416 601251 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2061903923) qz274 0 2 ep415 ep95 ep416 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2061903923) qz275 0 2 ep417 ep97 ep416 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz590 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 50774153) (@Nat.cast Real Real.instNatCast 131072))

noncomputable def ep419 := @Enclosure.Real.IsNear.cos_image qz343 qz590 Bool.false 50774153 131072 169 262144 Bool.true 601251 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz343 Bool.false 436146653401972095429 1125899906842624000 3809093752884306733 5915750000000000000000 50774153 131072 169 262144 (ep414 rfl) rfl) (Enclosure.sfrac_false_div 50774153 131072) (BSN.cos_reduce2 qz590 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 18136698717443725459456) qz565) 226375608064910080 72057594037927936 Bool.false 601251 1048576 61 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q2 50774153 131072 226375608064910080 72057594037927936 61 18136698717443725459456 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 601251 1048576 18136698717443725459456 18889465931478580854784 2061903923 2147483648 378978 378608 (ep418 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep420 := nat_lit 1162778484084834635768216436558801054190858607013357568597262235683384878024225

noncomputable def ep421 := nat_lit 3044843279478271637767797986162745792466951747330539277089724707483710574151201

noncomputable def ep422 := BSN.sin_dyadic_bound_f 2061903923 2147483648 3 2 1048576 378978 ep420 ep88 ep416 ep421 ep91 ep416 859074 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2061903923) qz268 0 2 ep420 ep88 ep416 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2061903923) qz269 0 2 ep421 ep91 ep416 rfl rfl rfl rfl) rfl rfl

noncomputable def ep423 := @Enclosure.Real.IsNear.sin_image qz343 qz590 Bool.false 50774153 131072 169 262144 Bool.true 859074 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz343 Bool.false 436146653401972095429 1125899906842624000 3809093752884306733 5915750000000000000000 50774153 131072 169 262144 (ep414 rfl) rfl) (Enclosure.sfrac_false_div 50774153 131072) (BSN.sin_reduce2 qz590 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 18136698717443725459456) qz565) 226375608064910080 72057594037927936 Bool.false 859074 1048576 61 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q2 50774153 131072 226375608064910080 72057594037927936 61 18136698717443725459456 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 859074 1048576 18136698717443725459456 18889465931478580854784 2061903923 2147483648 378978 378608 (ep422 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz591 := (@Enclosure.Real.IsNear.recentre' qz342 Bool.false 214039 1048576 1 1048576 214039 1048576 1 1048576 (ep412 rfl rfl) rfl)

noncomputable def ep424 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz342 (Real.cos qz343)) (@HMul.hMul Real Real Real qz0 qz342 (@Neg.neg Real Real.instNeg (Real.sin qz343))) Bool.true 128691162789 1099511627776 3466106132813 26017743648063488 Bool.false 91937669943 549755813888 1736103499231 13008871824031744 (@Enclosure.Real.IsNear.mulLit_ft qz342 (Real.cos qz343) 214039 1048576 1 1048576 601251 1048576 4031815 6203113472 128691162789 1099511627776 3466106132813 26017743648063488 qz591 (@Enclosure.Real.IsNear.recentre' (Real.cos qz343) Bool.true 601251 1048576 32254520 49624907776 601251 1048576 4031815 6203113472 (ep419 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz342 (@Neg.neg Real Real.instNeg (Real.sin qz343)) 214039 1048576 1 1048576 429537 524288 4031815 6203113472 91937669943 549755813888 1736103499231 13008871824031744 qz591 (@Enclosure.Real.IsNear.neg (Real.sin qz343) Bool.true 429537 524288 4031815 6203113472 (@Enclosure.Real.IsNear.recentre' (Real.sin qz343) Bool.true 859074 1048576 32254520 49624907776 429537 524288 4031815 6203113472 (ep423 rfl rfl) rfl)) rfl)

noncomputable def ep425 := @ep305 128691162789 1099511627776 3466106132813 26017743648063488 Bool.false 91937669943 549755813888 1736103499231 13008871824031744 Bool.false 1068653859273015440703488 485967511519 549755813888 63105837126949 13008871824031744 Bool.false 87962771197620303953920 160003348715 1099511627776 126262687256917 26017743648063488 (ep306 (BSN.head_sum_c_succ qz14 23 24 rfl rfl) (ep410 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep411 ep424) rfl rfl

theorem EMRow40.d9 : Enclosure.Complex.IsNear (BSN.headSumC qz14 25) Bool.false 485967511519 549755813888 63105837126949 13008871824031744 Bool.false 160003348715 1099511627776 126262687256917 26017743648063488 := ep304 (BSN.head_sum_c_succ qz14 24 25 rfl rfl) (ep425 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

theorem EMRow40.d10 : @Eq Nat (BSN.factNat (Nat.mul 2 1)) 2 := @Eq.refl Nat 2

theorem EMRow40.d11 : @Eq Nat (Nat.pow 31 1) 31 := @Eq.refl Nat 31

theorem EMRow40.d12 : @Eq Nat (BSN.factNat (Nat.mul 2 2)) 24 := @Eq.refl Nat 24

noncomputable abbrev qz20 := (@HAdd.hAdd Complex Complex Complex qz262 qz261 qz555)

noncomputable def ep426 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz3 (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 2)) qz20) Bool.true 133712992929 2000000 0 1 Bool.true 1810284405900971 1000000000 0 1

noncomputable def ep427 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.re qz20)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.im qz20)) 14856665881 400000 0 1 14857415881 500000 0 1

noncomputable def ep428 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.re qz20) 14856665881 1000000 0 1 5 2 0 1 14856665881 400000

noncomputable abbrev qz592 := (@Nat.cast Complex Complex.instNatCast 1)

noncomputable abbrev qz21 := (@HAdd.hAdd Complex Complex Complex qz262 qz261 qz592)

noncomputable def ep429 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz3 (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1)) qz21) Bool.true 14856665881 1000000 0 1 Bool.false 121891 500 0 1

noncomputable def ep430 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.re qz21)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.im qz21)) 3 4 0 1 14857415881 1000000 0 1

noncomputable def ep431 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.re qz21) 1 2 0 1 3 2 0 1 3 4

noncomputable def ep432 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1)) qz14 Bool.false 1 2 0 1 Bool.false 121891 1000 0 1 (BSN.ascPochhammer_one_eval qz14)

noncomputable abbrev qz345 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz346 := (Enclosure.Real.IsNear.const Bool.false 1 2)

noncomputable def ep433 := ep432 (@Enclosure.Complex.IsNear.of_eq qz14 (Complex.mk qz345 qz11) Bool.false 1 2 0 1 Bool.false 121891 1000 0 1 (BSN.s_crit_mk qz11 Bool.false 121891 1000 (@Eq.refl Real qz11)) (@Enclosure.Complex.IsNear.mk qz345 qz11 Bool.false 1 2 0 1 Bool.false 121891 1000 0 1 qz346 qz272))

noncomputable def ep434 := @ep431 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 121891 1000 0 1 ep433)

noncomputable def ep435 := @Enclosure.Complex.IsNear.of_eq qz21 (Complex.mk (Enclosure.sfrac Bool.false 3 2) qz11) Bool.false 3 2 0 1 Bool.false 121891 1000 0 1 (BSN.s_add_nat_mk qz11 Bool.false 121891 1000 1 (@Eq.refl Real qz11))

noncomputable abbrev qz593 := (ep435 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz11 Bool.false 3 2 0 1 Bool.false 121891 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz272))

noncomputable def ep436 := ep434 (@Enclosure.Complex.IsNear.re_isNear qz21 Bool.false 3 2 0 1 Bool.false 121891 1000 0 1 qz593)

noncomputable def ep437 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.im qz21) 121891 1000 0 1 121891 1000 0 1 14857415881 1000000

noncomputable def ep438 := @ep437 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 121891 1000 0 1 ep433)

noncomputable def ep439 := ep438 (@Enclosure.Complex.IsNear.im_isNear qz21 Bool.false 3 2 0 1 Bool.false 121891 1000 0 1 qz593)

noncomputable def ep440 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1)) qz21 Bool.true 14856665881 1000000 0 1 Bool.false 121891 500 0 1 (@ep430 59426663524 14856665881 1000000 0 1 (ep436 rfl) (ep439 rfl) rfl rfl)

noncomputable def ep441 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.im qz21)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.re qz21)) 121891 2000 0 1 365673 2000 0 1

noncomputable def ep442 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.im qz21) 1 2 0 1 121891 1000 0 1 121891 2000

noncomputable def ep443 := @ep442 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 121891 1000 0 1 ep433)

noncomputable def ep444 := ep443 (@Enclosure.Complex.IsNear.im_isNear qz21 Bool.false 3 2 0 1 Bool.false 121891 1000 0 1 qz593)

noncomputable def ep445 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.re qz21) 121891 1000 0 1 3 2 0 1 365673 2000

noncomputable def ep446 := @ep445 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 121891 1000 0 1 ep433)

noncomputable def ep447 := ep446 (@Enclosure.Complex.IsNear.re_isNear qz21 Bool.false 3 2 0 1 Bool.false 121891 1000 0 1 qz593)

noncomputable abbrev qz594 := (ep429 (BSN.ascPochhammer_succ_eval_c 1 2 qz14 rfl) (ep440 (@ep441 975128000 121891 500 0 1 (ep444 rfl) (ep447 rfl) rfl rfl)))

noncomputable def ep448 := @ep428 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 14856665881 1000000 0 1 Bool.false 121891 500 0 1 qz594)

noncomputable def ep449 := @Enclosure.Complex.IsNear.of_eq qz20 (Complex.mk (Enclosure.sfrac Bool.false 5 2) qz11) Bool.false 5 2 0 1 Bool.false 121891 1000 0 1 (BSN.s_add_nat_mk qz11 Bool.false 121891 1000 2 (@Eq.refl Real qz11))

noncomputable abbrev qz595 := (ep449 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz11 Bool.false 5 2 0 1 Bool.false 121891 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz272))

noncomputable def ep450 := ep448 (@Enclosure.Complex.IsNear.re_isNear qz20 Bool.false 5 2 0 1 Bool.false 121891 1000 0 1 qz595)

noncomputable def ep451 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.im qz20) 121891 500 0 1 121891 1000 0 1 14857415881 500000

noncomputable def ep452 := @ep451 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 14856665881 1000000 0 1 Bool.false 121891 500 0 1 qz594)

noncomputable def ep453 := ep452 (@Enclosure.Complex.IsNear.im_isNear qz20 Bool.false 5 2 0 1 Bool.false 121891 1000 0 1 qz595)

noncomputable def ep454 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 2)) qz20 Bool.true 133712992929 2000000 0 1 Bool.true 1810284405900971 1000000000 0 1 (@ep427 13371299292900000 133712992929 2000000 0 1 (ep450 rfl) (ep453 rfl) rfl rfl)

noncomputable def ep455 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.im qz20)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.re qz20)) 1810893860900971 1000000000 0 1 121891 200 0 1

noncomputable def ep456 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.im qz20) 14856665881 1000000 0 1 121891 1000 0 1 1810893860900971 1000000000

noncomputable def ep457 := @ep456 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 14856665881 1000000 0 1 Bool.false 121891 500 0 1 qz594)

noncomputable def ep458 := ep457 (@Enclosure.Complex.IsNear.im_isNear qz20 Bool.false 5 2 0 1 Bool.false 121891 1000 0 1 qz595)

noncomputable def ep459 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.re qz20) 121891 500 0 1 5 2 0 1 121891 200

noncomputable def ep460 := @ep459 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 14856665881 1000000 0 1 Bool.false 121891 500 0 1 qz594)

noncomputable def ep461 := ep460 (@Enclosure.Complex.IsNear.re_isNear qz20 Bool.false 5 2 0 1 Bool.false 121891 1000 0 1 qz595)

noncomputable abbrev qz596 := (ep454 (@ep455 362056881180194200 1810284405900971 1000000000 0 1 (ep458 rfl) (ep461 rfl) rfl rfl))

theorem EMRow40.d13 : Enclosure.Complex.IsNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 133712992929 2000000 0 1 Bool.true 1810284405900971 1000000000 0 1 := ep426 (BSN.ascPochhammer_succ_eval_c 2 3 qz14 rfl) qz596

theorem EMRow40.d14 : @Eq Nat (Nat.pow 31 3) 29791 := @Eq.refl Nat 29791

noncomputable def ep462 := nat_lit 151123303716013965661786359540625059006110389

noncomputable def ep463 := nat_lit 183712162705572296552589864531394560000000000

noncomputable def ep464 := nat_lit 153365145663252472344624377493464117809987704354961

noncomputable def ep465 := nat_lit 25716835445272653621351062349937098526556160000000000

noncomputable abbrev qz597 := (@instHSub Complex Complex.instSub)

noncomputable abbrev qz22 := qz597

noncomputable abbrev qz23 := (Complex.Stirling.logGammaStirling 2 qz257)

noncomputable abbrev qz598 := (@HAdd.hAdd Complex Complex Complex qz820 qz821 (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I (@HDiv.hDiv Complex Complex Complex qz822 (↑(Enclosure.sfrac Bool.false 121891 1000)) (2 : Complex))))

noncomputable abbrev qz347 := qz598

noncomputable abbrev qz24 := qz347

noncomputable abbrev qz348 := (@HMul.hMul Real Real Real qz0 (@HDiv.hDiv Real Real Real qz1 qz11 (2 : Real)) (Real.log Real.pi))

noncomputable abbrev qz599 := (@instHSub Real Real.instSub)

noncomputable def ep466 := Complex.re (@HMul.hMul Complex Complex Complex qz3 (Complex.exp (@HMul.hMul Complex Complex Complex qz3 Complex.I ↑(@HSub.hSub Real Real Real qz599 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz23 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz24 (@Nat.cast Complex Complex.instNatCast j))))) qz348))) (zetaApproximant qz14 2 31))

noncomputable def ep467 := @Enclosure.Real.IsNear.of_eq ep466 (@HSub.hSub Real Real Real qz599 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz599 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz23 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz24 (@Nat.cast Complex Complex.instNatCast j))))) qz348)) (Complex.re (zetaApproximant qz14 2 31))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz599 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz23 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz24 (@Nat.cast Complex Complex.instNatCast j))))) qz348)) (Complex.im (zetaApproximant qz14 2 31))))

noncomputable def ep468 := nat_lit 129998639295779819314028944397346629487901

noncomputable def ep469 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz599 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz23 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz24 (@Nat.cast Complex Complex.instNatCast j))))) qz348)) (Complex.re (zetaApproximant qz14 2 31))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz599 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz23 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz24 (@Nat.cast Complex Complex.instNatCast j))))) qz348)) (Complex.im (zetaApproximant qz14 2 31))) ep468

noncomputable def ep470 := nat_lit 158031967918771868002227840457113600000000

noncomputable def ep471 := nat_lit 245202274786166854213564475714418014934235850916947

noncomputable def ep472 := nat_lit 41146936712436245794161699759899357642489856000000000

noncomputable def ep473 := nat_lit 228930660148581544576642580795547149047

noncomputable def ep474 := nat_lit 367424325411144593105179729062789120000000000

noncomputable def ep475 := nat_lit 909791375185507689172641375622867808722380254953

noncomputable def ep476 := nat_lit 205734683562181228970808498799496788212449280000000000

noncomputable def ep477 := nat_lit 47764626169255872893665452974345412430133745521267919775404583883050603826380800000000

noncomputable def ep478 := @Enclosure.Real.IsNear.mulLit_ff (Real.cos (@HSub.hSub Real Real Real qz599 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz23 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz24 (@Nat.cast Complex Complex.instNatCast j))))) qz348)) (Complex.re (zetaApproximant qz14 2 31)) 1048575 1048576 8436785

noncomputable def ep479 := nat_lit 288245319946296716882547548552875009951

noncomputable def ep480 := nat_lit 350403142367500870804958085120000000000

noncomputable def ep481 := nat_lit 15691987183719563855285777503371611762101

noncomputable def ep482 := nat_lit 2763863185947391035285907722731520000000000

noncomputable def ep483 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz599 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz23 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz24 (@Nat.cast Complex Complex.instNatCast j))))) qz348)) Bool.false 1048575 1048576 67494280

noncomputable abbrev qz902 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 125179671) qz270)

noncomputable def ep484 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz599 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz23 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz24 (@Nat.cast Complex Complex.instNatCast j))))) qz348) qz902 Bool.false 125179671 1048576 351

noncomputable def ep485 := nat_lit 8258190270053739073471670753347

noncomputable def ep486 := nat_lit 69175290276410818560000000000

noncomputable def ep487 := nat_lit 639627838202478268425039336075404741

noncomputable def ep488 := nat_lit 1918236203684424843264000000000000000000

noncomputable def ep489 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz599 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz23 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz24 (@Nat.cast Complex Complex.instNatCast j))))) qz348) Bool.false ep485 ep486 ep487 ep488

noncomputable def ep490 := nat_lit 13084281782982496193184950753347

noncomputable def ep491 := nat_lit 193659726967244525577039336075404741

noncomputable def ep492 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz23 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz24 (@Nat.cast Complex Complex.instNatCast j))))) qz348 ep490 ep486 ep491 ep488 9144384711 131072000

noncomputable def ep493 := nat_lit 1082417515076483687838078828982697984000

noncomputable def ep494 := nat_lit 13259735552045654835949114067

noncomputable def ep495 := nat_lit 138350580552821637120000000

noncomputable def ep496 := nat_lit 83018795156333226355070208172065889

noncomputable def ep497 := nat_lit 479559050921106210816000000000000000000

noncomputable def ep498 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz22 qz23 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz24 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true ep494 ep495 ep496 ep497 Bool.false ep490 ep486

noncomputable def ep499 := nat_lit 10984942339183157596909114067

noncomputable def ep500 := nat_lit 80485520355387023234805871534113889

noncomputable def ep501 := nat_lit 13510982717295976385184950753347

noncomputable def ep502 := nat_lit 173393528640240821169670486388876741

noncomputable def ep503 := @Enclosure.Complex.IsNear.subLitP qz23 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz24 (@Nat.cast Complex Complex.instNatCast j))) Bool.true ep499 ep495 ep500 ep497 Bool.false ep501 ep486 ep502

noncomputable def ep504 := nat_lit 29858270045612064594620941618610727987183616

noncomputable def ep505 := nat_lit 1841448955070329339582017095761786553621282816

noncomputable abbrev qz349 := (@HSub.hSub Complex Complex Complex qz597 qz546 qz552)

noncomputable abbrev qz350 := (Complex.log qz546)

noncomputable abbrev qz25 := (@HSub.hSub Complex Complex Complex qz597 (@HMul.hMul Complex Complex Complex qz255 qz349 qz350) qz257)

noncomputable abbrev qz351 := qz552

noncomputable abbrev qz26 := qz351

noncomputable abbrev qz600 := qz822

noncomputable abbrev qz352 := qz600

noncomputable abbrev qz27 := qz352

noncomputable abbrev qz28 := (@instHMul Nat instMulNat)

noncomputable abbrev qz601 := (@instHPow Complex Int (@ZPow.toPow Complex (@DivInvMonoid.toZPow Complex Complex.instDivInvMonoid)))

noncomputable abbrev qz29 := qz601

noncomputable abbrev qz30 := (@instHSub Int Int.instSub)

noncomputable abbrev qz353 := (@OfNat.ofNat Int 1 (@instOfNat 1))

noncomputable abbrev qz31 := qz353

noncomputable abbrev qz32 := (@instHMul Int Int.instMul)

noncomputable abbrev qz602 := (@OfNat.ofNat Int 2 (@instOfNat 2))

noncomputable abbrev qz33 := qz602

noncomputable abbrev qz903 := (@HMul.hMul Complex Complex Complex qz3 qz26 ↑qz253)

noncomputable def ep506 := @Enclosure.Complex.IsNear.of_eq qz23 (@HAdd.hAdd Complex Complex Complex qz15 (@HAdd.hAdd Complex Complex Complex qz15 qz25 qz903) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz22 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz29 qz5 (@HSub.hSub Int Int Int qz30 qz31 (@HMul.hMul Int Int Int qz32 qz33 (@Nat.cast Int instNatCastInt k)))))) Bool.true ep499

noncomputable def ep507 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz15 qz25 qz903) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz22 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz29 qz5 (@HSub.hSub Int Int Int qz30 qz31 (@HMul.hMul Int Int Int qz32 qz33 (@Nat.cast Int instNatCastInt k))))) Bool.true 357583185792352308541 4503599627370496000

noncomputable def ep508 := nat_lit 415051741658464911360000000

noncomputable def ep509 := nat_lit 94129417157239387209246653

noncomputable def ep510 := nat_lit 207525870829232455680000000000

noncomputable def ep511 := nat_lit 49471782225431653235020105622066092134367232000

noncomputable def ep512 := nat_lit 243392226924093482998988170422369606863524200448000

noncomputable def ep513 := @ep507 15885659367629472983 94652000000000000000000 Bool.false 3518509595498211881399 18014398509481984000 8555687531904846563 94652000000000000000000 Bool.false 13128357905321470405933 ep495 34226277139959931 ep508 Bool.true ep509 ep486 245400780820124900971 ep510 Bool.true ep511 ep499 ep495 ep500 ep497 Bool.false ep512

noncomputable def ep514 := @Enclosure.Complex.IsNear.addLitP qz25 qz903 Bool.true 361721713199562804541 4503599627370496000 15705125004836504233 94652000000000000000000

noncomputable def ep515 := nat_lit 46869143328175201785085952

noncomputable def ep516 := @ep514 Bool.false 3518509595498211881399 18014398509481984000 8555687531904846563 94652000000000000000000 Bool.false 120447 131072 1 524288 Bool.false 0 1 0 1 Bool.true ep515 357583185792352308541 4503599627370496000 15885659367629472983 94652000000000000000000 Bool.false 3518509595498211881399 3518509595498211881399 18014398509481984000

noncomputable abbrev qz34 := (@HMul.hMul Complex Complex Complex qz255 qz349 qz350)

noncomputable def ep517 := @Enclosure.Complex.IsNear.subLitP qz34 qz5 Bool.true 342581414783238196541 4503599627370496000 15705125004836504233 94652000000000000000000 Bool.false 4616406119857846137271

noncomputable def ep518 := nat_lit 1446886852798251218164000

noncomputable def ep519 := nat_lit 14074038381992847525596000

noncomputable def ep520 := @ep517 18014398509481984000 8555687531904846563 94652000000000000000000 Bool.false 17000 4000 0 1 Bool.false 243782 4000 0 1 Bool.true ep518 361721713199562804541 4503599627370496000 15705125004836504233 94652000000000000000000 Bool.false ep519 3518509595498211881399 18014398509481984000 8555687531904846563 94652000000000000000000

noncomputable abbrev qz35 := qz349

noncomputable abbrev qz36 := qz350

noncomputable def ep521 := @Enclosure.Complex.IsNear.mul qz35 qz36 Bool.true 342581414783238196541 4503599627370496000 15705125004836504233 94652000000000000000000 Bool.false 4616406119857846137271 18014398509481984000 8555687531904846563

noncomputable def ep522 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re qz35) (Complex.re qz36)) (@HMul.hMul Real Real Real qz0 (Complex.im qz35) (Complex.im qz36)) 555618840116177715 36028797018963968 187500000780879 37860800000000000000 103008442449440102729 1125899906842624000

noncomputable def ep523 := nat_lit 3085699063923697743291461818145308672

noncomputable def ep524 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz35) (Complex.re qz36) 15000 4000 0 1 37041256007745181 9007199254740992 62500000260293 47326000000000000000

noncomputable def ep525 := @Enclosure.Complex.IsNear.re_isNear qz35 Bool.false 15000 4000 0 1 Bool.false 243782 4000 0 1

noncomputable def ep526 := @Enclosure.Complex.IsNear.of_eq qz35 (Complex.mk (Enclosure.sfrac Bool.false 15000 4000) qz260) Bool.false 15000 4000 0 1 Bool.false 243782 4000 0

noncomputable abbrev qz603 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 17000 4000) qz260))

noncomputable def ep527 := @Enclosure.Complex.IsNear.of_eq qz36 qz603 Bool.false 37041256007745181 9007199254740992 62500000260293 47326000000000000000 Bool.false 845086531814819 562949953421312 125000000023663 47326000000000000000

noncomputable def ep528 := nat_lit 476009497833996478625109852280953034349655709736942319677673264931685241975928454431319576318886393628586299883520

noncomputable def ep529 := nat_lit 14204356500257824717410069524167555687704214846619921385823833946212398218919246134306499524900407520207913877504

noncomputable def ep530 := nat_lit 191040931984023515154598783635329687895007133788681193407976447482774444120981042433170243671165739409080320

noncomputable def ep531 := BSN.log_dyadic_bound 26950663524 92486663524 6 5 ep528 1048576 378608 ep529 ep530 629347 119437327048 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 26950663524) (BSN.artanhQ 92486663524) 0 5 ep529 ep528 ep530 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz904 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable def ep532 := @Enclosure.Real.IsNear.mulLit_ff qz345 (Real.log (Enclosure.sfrac Bool.false 59718663524 16000000)) 1 2 0 1 37041256007745181 4503599627370496 62500000260293 23663000000000000000 37041256007745181 9007199254740992 62500000260293 47326000000000000000 qz346 (BSN.isNear_log_sfrac 59718663524 16000000 37041256007745181 4503599627370496 62500000260293 23663000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 59718663524) qz904)) Bool.false 310724576476619287298048 37778931862957161709568 1000000004164688 378608000000000000000 37041256007745181 4503599627370496 62500000260293 23663000000000000000 (BSN.log_rat_reduce_isNear 59718663524 16000000 11 119437327048 65536000000 629347 1048576 24973259072661432 36028797018963968 378608 1000000000000000 rfl rfl rfl rfl (ep531 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep533 := BSN.arctan_dyadic_bound_f 17000 243782 1 0 1048576 378608 0 1 1 0 1 1 73003 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 17000) (BSN.arctanEvenQ 243782) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 17000) (BSN.arctanOddQ 243782) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz354 := (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz355 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 2) Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable abbrev qz604 := (@Nat.cast Real Real.instNatCast 17000)

noncomputable abbrev qz605 := (@Nat.cast Real Real.instNatCast 243782)

noncomputable def ep534 := @Enclosure.Real.IsNear.subLit_ff_p qz354 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz604 qz605)) 884279719003555 562949953421312 1 2000000000000000 73003 1048576 1 378608 886137455184255647744 845086531814819 562949953421312 125000000023663 47326000000000000000 qz355 (ep533 rfl) rfl rfl

noncomputable abbrev qz606 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 243782) (@Nat.cast Real Real.instNatCast 17000)))

noncomputable def ep535 := @Enclosure.Complex.IsNear.re_isNear qz36 Bool.false 37041256007745181 9007199254740992 62500000260293 47326000000000000000 Bool.false 845086531814819 562949953421312 125000000023663 47326000000000000000 (ep527 (@congrArg Complex Complex qz5 qz548 Complex.log (BSN.w_shift_mk qz11 Bool.false 121891 1000 4 (@Eq.refl Real qz11) rfl)) (@Enclosure.Complex.IsNear.of_parts qz603 Bool.false 37041256007745181 9007199254740992 62500000260293 47326000000000000000 Bool.false 845086531814819 562949953421312 125000000023663 47326000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz603) (@HMul.hMul Real Real Real qz0 qz345 (Real.log (Enclosure.sfrac Bool.false 59718663524 16000000))) Bool.false 37041256007745181 9007199254740992 62500000260293 47326000000000000000 (Enclosure.clog_re_eq 17000 243782 4000 59718663524 16000000 rfl rfl rfl) (ep532 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz603) qz606 Bool.false 845086531814819 562949953421312 125000000023663 47326000000000000000 (Enclosure.clog_im_eq 17000 243782 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz606 (@HSub.hSub Real Real Real qz599 qz354 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz604 qz605))) Bool.false 845086531814819 562949953421312 125000000023663 47326000000000000000 (BSN.arctan_recip 243782 17000 rfl rfl) ep534))))

noncomputable def ep536 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz35) (Complex.im qz36) 243782 4000 0 1 845086531814819 562949953421312 125000000023663 47326000000000000000

noncomputable def ep537 := @Enclosure.Complex.IsNear.im_isNear qz35 Bool.false 15000 4000 0 1 Bool.false 243782 4000 0 1

noncomputable def ep538 := @Enclosure.Complex.IsNear.im_isNear qz36 Bool.false 37041256007745181 9007199254740992 62500000260293 47326000000000000000 Bool.false 845086531814819 562949953421312 125000000023663 47326000000000000000 (ep527 (@congrArg Complex Complex qz5 qz548 Complex.log (BSN.w_shift_mk qz11 Bool.false 121891 1000 4 (@Eq.refl Real qz11) rfl)) (@Enclosure.Complex.IsNear.of_parts qz603 Bool.false 37041256007745181 9007199254740992 62500000260293 47326000000000000000 Bool.false 845086531814819 562949953421312 125000000023663 47326000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz603) (@HMul.hMul Real Real Real qz0 qz345 (Real.log (Enclosure.sfrac Bool.false 59718663524 16000000))) Bool.false 37041256007745181 9007199254740992 62500000260293 47326000000000000000 (Enclosure.clog_re_eq 17000 243782 4000 59718663524 16000000 rfl rfl rfl) (ep532 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz603) qz606 Bool.false 845086531814819 562949953421312 125000000023663 47326000000000000000 (Enclosure.clog_im_eq 17000 243782 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz606 (@HSub.hSub Real Real Real qz599 qz354 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz604 qz605))) Bool.false 845086531814819 562949953421312 125000000023663 47326000000000000000 (BSN.arctan_recip 243782 17000 rfl rfl) ep534))))

noncomputable abbrev qz356 := (@ep526 1 (BSN.w_sub_half_mk qz11 Bool.false 121891 1000 4 (@Eq.refl Real qz11) rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 15000 4000) (Enclosure.sfrac Bool.false 243782 4000) Bool.false 15000 4000 0 1 Bool.false 243782 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 15000 4000) (Enclosure.Real.IsNear.const Bool.false 243782 4000)))

noncomputable def ep539 := @ep522 15236375002884306733 94652000000000000000000 ep523 342581414783238196541 4503599627370496000 15705125004836504233 94652000000000000000000 (@ep524 555618840116177715 36028797018963968 187500000780879 37860800000000000000 (ep525 qz356) ep535 rfl) (@ep536 103008442449440102729 1125899906842624000 15236375002884306733 94652000000000000000000 (ep537 qz356) ep538 rfl) rfl

noncomputable def ep540 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re qz35) (Complex.im qz36)) (@HMul.hMul Real Real Real qz0 (Complex.im qz35) (Complex.re qz36)) 12676297977222285 2251799813685248 375000000070989 37860800000000000000 4514995736040067857271 18014398509481984000

noncomputable def ep541 := nat_lit 10395222440591336579309959480195678208

noncomputable def ep542 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz35) (Complex.im qz36) 15000 4000 0 1 845086531814819 562949953421312 125000000023663 47326000000000000000

noncomputable def ep543 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz35) (Complex.re qz36) 243782 4000 0 1 37041256007745181 9007199254740992 62500000260293 47326000000000000000

noncomputable def ep544 := @ep540 7618187531727374063 94652000000000000000000 ep541 4616406119857846137271 18014398509481984000 8555687531904846563 94652000000000000000000 (@ep542 12676297977222285 2251799813685248 375000000070989 37860800000000000000 (ep525 qz356) ep538 rfl) (@ep543 4514995736040067857271 18014398509481984000 7618187531727374063 94652000000000000000000 (ep537 qz356) ep535 rfl) rfl

noncomputable def ep545 := ep520 (@ep521 94652000000000000000000 (ep539 rfl) (ep544 rfl)) qz13 rfl rfl rfl rfl rfl rfl

noncomputable def ep546 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re qz26) (Complex.re ↑qz253)) (@HMul.hMul Real Real Real qz0 (Complex.im qz26) (Complex.im ↑qz253)) 120447 131072 1 524288 0 1 0 1 120447 120447

noncomputable def ep547 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz26) (Complex.re ↑qz253) 1 2 0 1 120447 65536 1 262144 120447 131072 1 524288

noncomputable abbrev qz357 := (@Enclosure.Complex.IsNear.of_eq qz26 (Complex.mk (Enclosure.sfrac Bool.false 1 2) qz828) Bool.false 1 2 0 1 Bool.false 0 1 0 1 BSN.half_c_mk (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 2) qz828 Bool.false 1 2 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 2) qz830))

noncomputable def ep548 := ep547 (@Enclosure.Complex.IsNear.re_isNear qz26 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz357) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz253) qz253 Bool.false 120447 65536 1 262144 (Complex.ofReal_re qz253) EMRow40.d4)

noncomputable def ep549 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz26) (Complex.im ↑qz253) 0 1 0 1 0 1 0 1 0 1 0 1

noncomputable def ep550 := ep549 (@Enclosure.Complex.IsNear.im_isNear qz26 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz357) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz253) qz264 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz253) (0 : Real) qz264 (Complex.ofReal_im qz253) Enclosure.sfrac_zero_eq) qz276)

noncomputable def ep551 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re qz26) (Complex.im ↑qz253)) (@HMul.hMul Real Real Real qz0 (Complex.im qz26) (Complex.re ↑qz253)) 0 1 0 1 0 1 0 1 0 0

noncomputable def ep552 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz26) (Complex.im ↑qz253) 1 2 0 1 0 1 0 1 0 1 0 1

noncomputable def ep553 := ep552 (@Enclosure.Complex.IsNear.re_isNear qz26 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz357) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz253) qz264 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz253) (0 : Real) qz264 (Complex.ofReal_im qz253) Enclosure.sfrac_zero_eq) qz276)

noncomputable def ep554 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz26) (Complex.re ↑qz253) 0 1 0 1 120447 65536 1 262144 0 1 0 1

noncomputable def ep555 := ep554 (@Enclosure.Complex.IsNear.im_isNear qz26 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz357) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz253) qz253 Bool.false 120447 65536 1 262144 (Complex.ofReal_re qz253) EMRow40.d4)

noncomputable def ep556 := @ep516 8555687531904846563 94652000000000000000000 (ep545 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz26 (↑qz253) Bool.false 120447 131072 1 524288 Bool.false 0 1 0 1 (@ep546 131072 1 524288 (ep548 rfl) (ep550 rfl) rfl rfl) (@ep551 1 0 1 (ep553 rfl) (ep555 rfl) rfl rfl))

noncomputable abbrev qz37 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)

noncomputable abbrev qz38 := (@HMul.hMul Complex Complex Complex qz255 (@HMul.hMul Complex Complex Complex qz255 (2 : Complex) qz555) (@HSub.hSub Complex Complex Complex qz597 (@HMul.hMul Complex Complex Complex qz255 (2 : Complex) qz555) (1 : Complex)))

noncomputable abbrev qz39 := (@HPow.hPow Complex Int Complex qz601 qz257 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) qz353 (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) qz602 (@Nat.cast Int instNatCastInt 2))))

noncomputable def ep557 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz22 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz29 qz5 (@HSub.hSub Int Int Int qz30 qz31 (@HMul.hMul Int Int Int qz32 qz33 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz15 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz22 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz29 qz5 (@HSub.hSub Int Int Int qz30 qz31 (@HMul.hMul Int Int Int qz32 qz33 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz37)) qz38) qz39)) Bool.false 13128357905321470405933 ep495 34226277139959931 ep508

noncomputable def ep558 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz22 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz29 qz5 (@HSub.hSub Int Int Int qz30 qz31 (@HMul.hMul Int Int Int qz32 qz33 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz37)) qz38) qz39) Bool.false 19562257 206158430208 17 206158430208 Bool.true

noncomputable def ep559 := nat_lit 46116860184273879040000000

noncomputable def ep560 := nat_lit 23058430092136939520000000000

noncomputable def ep561 := nat_lit 902173885656620476161825269874688

noncomputable def ep562 := nat_lit 3234262146255075661654360667459682304000

noncomputable def ep563 := @ep558 140262533411 103079215104000 121891 103079215104000 Bool.false 116486620330135311 ep559 756499959931 ep508 Bool.true 274789165612056415551 ep560 1784565404900971 ep510 Bool.false ep561 13128357905321470405933 ep495 34226277139959931 ep508 Bool.true ep562 ep509 ep486 245400780820124900971

noncomputable abbrev qz40 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)

noncomputable abbrev qz41 := (@HMul.hMul Complex Complex Complex qz255 (@HMul.hMul Complex Complex Complex qz255 (2 : Complex) qz592) (@HSub.hSub Complex Complex Complex qz597 (@HMul.hMul Complex Complex Complex qz255 (2 : Complex) qz592) (1 : Complex)))

noncomputable abbrev qz42 := (@HPow.hPow Complex Int Complex qz601 qz257 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) qz353 (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) qz602 (@Nat.cast Int instNatCastInt 1))))

noncomputable def ep564 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz22 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz29 qz5 (@HSub.hSub Int Int Int qz30 qz31 (@HMul.hMul Int Int Int qz32 qz33 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz15 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz22 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz29 qz5 (@HSub.hSub Int Int Int qz30 qz31 (@HMul.hMul Int Int Int qz32 qz33 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz40)) qz41) qz42)) Bool.false 19562257 206158430208 17 206158430208

noncomputable def ep565 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz22 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz29 qz5 (@HSub.hSub Int Int Int qz30 qz31 (@HMul.hMul Int Int Int qz32 qz33 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz40)) qz41) qz42) Bool.false 0 1 0 1 Bool.false

noncomputable def ep566 := @ep565 0 1 0 1 Bool.false 19562257 206158430208 17 206158430208 Bool.true 140262533411 103079215104000 121891 103079215104000 Bool.false 19562257 19562257 206158430208 17 206158430208 Bool.true 140262533411 140262533411 103079215104000 121891

noncomputable def ep567 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz22 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz29 qz5 (@HSub.hSub Int Int Int qz30 qz31 (@HMul.hMul Int Int Int qz32 qz33 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz264 qz264) Bool.false 0 1 0 1 Bool.false

noncomputable def ep568 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz40)) qz41) qz42 Bool.false 19562257 206158430208 17 206158430208 Bool.true 140262533411 103079215104000 121891 103079215104000

noncomputable def ep569 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz40)) qz41)) (Complex.re qz42)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz40)) qz41)) (Complex.im qz42)) 19562257 206158430208 17 206158430208 0 1 0

noncomputable def ep570 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz40)) qz41)) (Complex.re qz42) 1 12 0 1 19562257 17179869184 17 17179869184 19562257

noncomputable def ep571 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz40)) qz41) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz264) Bool.false 1 12 0 1 Bool.false 0 1 0 1

noncomputable abbrev qz905 := (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 12) qz264 Bool.false 1 12 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 12) qz276)

noncomputable def ep572 := @Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz40)) qz41) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep571 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz905)

noncomputable def ep573 := @Enclosure.Complex.IsNear.re_isNear qz42 Bool.false 19562257 17179869184 17 17179869184 Bool.true 140262533411 8589934592000 121891 8589934592000

noncomputable def ep574 := @Enclosure.Complex.IsNear.of_eq qz42 (@Inv.inv Complex Complex.instInv qz8) Bool.false 19562257 17179869184 17 17179869184 Bool.true 140262533411 8589934592000 121891

noncomputable def ep575 := @Enclosure.Complex.IsNear.of_parts (@Inv.inv Complex Complex.instInv qz8) Bool.false 19562257 17179869184 17 17179869184 Bool.true 140262533411 8589934592000 121891

noncomputable abbrev qz358 := (@MonoidWithZeroHom Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz359 := (@MonoidWithZeroHom.funLike Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable def ep576 := @Enclosure.Real.IsNear.mulLit_ff qz9 (@Inv.inv Real Real.instInv (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz8)) 17000 4000 0 1 1150721 4294967296 1 4294967296

noncomputable def ep577 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz8)) Bool.false 1150721 4294967296 1 4294967296 1150721 4294967296 1

noncomputable abbrev qz607 := (@instHAdd Real Real.instAdd)

noncomputable def ep578 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz8) (@HAdd.hAdd Real Real Real qz607 (@HMul.hMul Real Real Real qz0 qz9 qz9) (@HMul.hMul Real Real Real qz0 qz10 qz10)) Bool.false 14929665881 4000000 0 1

noncomputable def ep579 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz9 qz9) (@HMul.hMul Real Real Real qz0 qz10 qz10) 289 16 0 1 14857415881 4000000

noncomputable def ep580 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz9 17000 4000 0 1 17000 4000 0 1

noncomputable def ep581 := @Enclosure.Real.IsNear.mulLit_ff qz10 qz10 243782 4000 0 1 243782 4000 0 1

noncomputable def ep582 := @ep579 0 1 238874654096 14929665881 4000000 0 1 (@ep580 289 16 0 1 (ep32 qz12) (ep32 qz12) rfl) (@ep581 14857415881 4000000 0 1 (ep37 qz12) (ep37 qz12) rfl)

noncomputable def ep583 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz8) 14929665881 4000000 0 1 575360 575361 2147483648 (ep578 (Enclosure.Complex.normSq_eq_mul_add_mul qz8) (ep582 rfl rfl)) rfl

noncomputable def ep584 := @Enclosure.Real.IsNear.of_eq (Complex.re (@Inv.inv Complex Complex.instInv qz8)) (@HMul.hMul Real Real Real qz0 qz9 (@Inv.inv Real Real.instInv (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz8))) Bool.false 19562257 17179869184 17 17179869184 (Enclosure.Complex.inv_re_eq_mul qz8) (@ep576 19562257 17179869184 17 17179869184 (ep32 qz12) (@ep577 4294967296 (ep583 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep585 := @Enclosure.Real.IsNear.of_eq (Complex.im (@Inv.inv Complex Complex.instInv qz8)) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz10) (@Inv.inv Real Real.instInv (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz8))) Bool.true 140262533411 8589934592000 121891 8589934592000 (Enclosure.Complex.inv_im_eq_mul qz8)

noncomputable def ep586 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz10) (@Inv.inv Real Real.instInv (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz8)) 243782 4000 0 1 1150721 4294967296 1

noncomputable def ep587 := @ep586 4294967296 140262533411 8589934592000 121891 8589934592000 (@Enclosure.Real.IsNear.neg qz10 Bool.false 243782 4000 0 1 (ep37 qz12)) (@ep577 4294967296 (ep583 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep588 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz40)) qz41)) (Complex.im qz42) 0 1 0 1 140262533411 8589934592000 121891 8589934592000 0

noncomputable def ep589 := @Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz40)) qz41) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep571 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz905)

noncomputable def ep590 := @Enclosure.Complex.IsNear.im_isNear qz42 Bool.false 19562257 17179869184 17 17179869184 Bool.true 140262533411 8589934592000 121891 8589934592000

noncomputable abbrev qz906 := (@ep574 8589934592000 (BSN.zpow_one_sub_two_mul qz5 1 1 rfl rfl) (@ep575 8589934592000 ep584 (ep585 ep587)))

noncomputable def ep591 := @ep569 1 19562257 19562257 206158430208 17 206158430208 (@ep570 206158430208 17 206158430208 ep572 (ep573 qz906) rfl) (@ep588 1 0 1 ep589 (ep590 qz906) rfl) rfl

noncomputable def ep592 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz40)) qz41)) (Complex.im qz42)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz40)) qz41)) (Complex.re qz42)) 140262533411 103079215104000 121891 103079215104000 0 1 0

noncomputable def ep593 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz40)) qz41)) (Complex.im qz42) 1 12 0 1 140262533411 8589934592000 121891 8589934592000 140262533411

noncomputable def ep594 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz40)) qz41)) (Complex.re qz42) 0 1 0 1 19562257 17179869184 17 17179869184 0

noncomputable def ep595 := @ep592 1 140262533411 140262533411 103079215104000 121891 103079215104000 (@ep593 103079215104000 121891 103079215104000 ep572 (ep590 qz906) rfl) (@ep594 1 0 1 ep589 (ep573 qz906) rfl) rfl

noncomputable abbrev qz360 := (@Enclosure.Complex.IsNear.mk qz828 qz828 Bool.false 0 1 0 1 Bool.false 0 1 0 1 qz830 qz830)

noncomputable def ep596 := @ep566 103079215104000 (@ep567 0 1 0 1 (BSN.stirling_sum_base qz5) qz360) (ep568 (ep591 rfl) (ep595 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep597 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz37)) qz38) qz39 Bool.false 116486620330135311 ep559 756499959931 ep508 Bool.true 274789165612056415551 ep560 1784565404900971 ep510

noncomputable def ep598 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz37)) qz38)) (Complex.re qz39)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz37)) qz38)) (Complex.im qz39)) 116486620330135311 ep559 756499959931 ep508 0 1 0

noncomputable def ep599 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz37)) qz38)) (Complex.re qz39) 1 360 0 1 1048379582971217799 1152921504606846976000000 756499959931 1152921504606846976000000 116486620330135311

noncomputable def ep600 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz37)) qz38) (Complex.mk (Enclosure.sfrac Bool.true 1 360) qz264) Bool.true 1 360 0 1 Bool.false 0 1 0 1

noncomputable def ep601 := @Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz37)) qz38) Bool.true 1 360 0 1 Bool.false 0 1 0 1 (ep600 (BSN.stirling_coeff_mk 2 1 30 Bool.true BSN.bern_real_2 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 1 360) qz264 Bool.true 1 360 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.true 1 360) qz276))

noncomputable def ep602 := nat_lit 576460752303423488000000000

noncomputable def ep603 := @Enclosure.Complex.IsNear.re_isNear qz39 Bool.true 1048379582971217799 1152921504606846976000000 756499959931 1152921504606846976000000 Bool.false 2473102490508507739959 ep602 1784565404900971 ep602

noncomputable def ep604 := @Enclosure.Complex.IsNear.of_eq qz39 (@Inv.inv Complex Complex.instInv qz2) Bool.true 1048379582971217799 1152921504606846976000000 756499959931 1152921504606846976000000 Bool.false 2473102490508507739959 ep602 1784565404900971

noncomputable def ep605 := @Enclosure.Complex.IsNear.of_parts (@Inv.inv Complex Complex.instInv qz2) Bool.true 1048379582971217799 1152921504606846976000000 756499959931 1152921504606846976000000 Bool.false 2473102490508507739959 ep602 1784565404900971

noncomputable abbrev qz43 := (Complex.re qz254)

noncomputable def ep606 := @Enclosure.Real.IsNear.mulLit_tf qz43 (@Inv.inv Real Real.instInv (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz2)) 756499959931 16000000 0 1 1385829 72057594037927936 1 72057594037927936

noncomputable def ep607 := @Enclosure.Complex.IsNear.re_isNear qz2 Bool.true 756499959931 16000000 0 1 Bool.true 1784565404900971 8000000000 0 1

noncomputable def ep608 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz2)) Bool.false 1385829 72057594037927936 1 72057594037927936 1385829 72057594037927936 1

noncomputable def ep609 := nat_lit 3327746731713267721407506992841

noncomputable abbrev qz44 := (Complex.im qz254)

noncomputable def ep610 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz2) (@HAdd.hAdd Real Real Real qz607 (@HMul.hMul Real Real Real qz0 qz43 qz43) (@HMul.hMul Real Real Real qz0 qz44 qz44)) Bool.false ep609 64000000000000000000 0 1

noncomputable def ep611 := nat_lit 3184673684369366570026316742841

noncomputable def ep612 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz43 qz43) (@HMul.hMul Real Real Real qz0 qz44 qz44) 572292189375604605524761 256000000000000 0 1 ep611 64000000000000000000

noncomputable def ep613 := nat_lit 851903163318596536680321790167296000000000000

noncomputable def ep614 := @Enclosure.Real.IsNear.mulLit_tt qz43 qz43 756499959931 16000000 0 1 756499959931 16000000 0 1

noncomputable def ep615 := @Enclosure.Real.IsNear.mulLit_tt qz44 qz44 1784565404900971 8000000000 0 1 1784565404900971 8000000000 0 1

noncomputable def ep616 := @Enclosure.Complex.IsNear.im_isNear qz2 Bool.true 756499959931 16000000 0 1 Bool.true 1784565404900971 8000000000 0 1

noncomputable def ep617 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz2) ep609 64000000000000000000 0 1 692914 692915 36028797018963968 (ep610 (Enclosure.Complex.normSq_eq_mul_add_mul qz2) (@ep612 0 1 ep613 ep609 64000000000000000000 0 1 (@ep614 572292189375604605524761 256000000000000 0 1 (ep607 EMRow40.d5) (ep607 EMRow40.d5) rfl) (@ep615 ep611 64000000000000000000 0 1 (ep616 EMRow40.d5) (ep616 EMRow40.d5) rfl) rfl rfl)) rfl

noncomputable def ep618 := @Enclosure.Real.IsNear.of_eq (Complex.re (@Inv.inv Complex Complex.instInv qz2)) (@HMul.hMul Real Real Real qz0 qz43 (@Inv.inv Real Real.instInv (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz2))) Bool.true 1048379582971217799 1152921504606846976000000 756499959931 1152921504606846976000000 (Enclosure.Complex.inv_re_eq_mul qz2) (@ep606 1048379582971217799 1152921504606846976000000 756499959931 1152921504606846976000000 (ep607 EMRow40.d5) (@ep608 72057594037927936 (ep617 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep619 := @Enclosure.Real.IsNear.of_eq (Complex.im (@Inv.inv Complex Complex.instInv qz2)) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz44) (@Inv.inv Real Real.instInv (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz2))) Bool.false 2473102490508507739959 ep602 1784565404900971 ep602 (Enclosure.Complex.inv_im_eq_mul qz2)

noncomputable def ep620 := @Enclosure.Real.IsNear.mulLit_ff (@Neg.neg Real Real.instNeg qz44) (@Inv.inv Real Real.instInv (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz2)) 1784565404900971 8000000000 0 1 1385829 72057594037927936 1

noncomputable def ep621 := @ep620 72057594037927936 2473102490508507739959 ep602 1784565404900971 ep602 (@Enclosure.Real.IsNear.neg qz44 Bool.true 1784565404900971 8000000000 0 1 (ep616 EMRow40.d5)) (@ep608 72057594037927936 (ep617 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep622 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz37)) qz38)) (Complex.im qz39) 0 1 0 1 2473102490508507739959 ep602 1784565404900971 ep602 0

noncomputable def ep623 := @Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz37)) qz38) Bool.true 1 360 0 1 Bool.false 0 1 0 1 (ep600 (BSN.stirling_coeff_mk 2 1 30 Bool.true BSN.bern_real_2 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 1 360) qz264 Bool.true 1 360 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.true 1 360) qz276))

noncomputable def ep624 := @Enclosure.Complex.IsNear.im_isNear qz39 Bool.true 1048379582971217799 1152921504606846976000000 756499959931 1152921504606846976000000 Bool.false 2473102490508507739959 ep602 1784565404900971 ep602

noncomputable abbrev qz907 := (@ep604 ep602 (BSN.zpow_one_sub_two_mul qz5 2 3 rfl rfl) (@ep605 ep602 ep618 (ep619 ep621)))

noncomputable def ep625 := @ep598 1 116486620330135311 116486620330135311 ep559 756499959931 ep508 (@ep599 ep559 756499959931 ep508 ep601 (ep603 qz907) rfl) (@ep622 1 0 1 ep623 (ep624 qz907) rfl) rfl

noncomputable def ep626 := @Enclosure.Real.IsNear.addLit_tt (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz37)) qz38)) (Complex.im qz39)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz37)) qz38)) (Complex.re qz39)) 274789165612056415551 ep560 1784565404900971 ep510 0 1 0

noncomputable def ep627 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz37)) qz38)) (Complex.im qz39) 1 360 0 1 2473102490508507739959 ep602 1784565404900971 ep602 274789165612056415551

noncomputable def ep628 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz37)) qz38)) (Complex.re qz39) 0 1 0 1 1048379582971217799 1152921504606846976000000 756499959931 1152921504606846976000000 0

noncomputable def ep629 := @ep626 1 274789165612056415551 274789165612056415551 ep560 1784565404900971 ep510 (@ep627 ep560 1784565404900971 ep510 ep601 (ep624 qz907) rfl) (@ep628 1 0 1 ep623 (ep603 qz907) rfl) rfl

noncomputable def ep630 := @ep563 ep510 (@ep564 Bool.true 140262533411 103079215104000 121891 103079215104000 (BSN.stirling_sum_succ qz5 0 1 rfl) (ep596 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep597 (ep625 rfl) (ep629 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep631 := @ep513 ep501 ep486 ep502 ep488 (ep556 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep557 Bool.true ep509 ep486 245400780820124900971 ep510 (BSN.stirling_sum_succ qz5 1 2 rfl) (ep630 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep632 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz24 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz11 4) Bool.false 37024629115600541 2251799813685248 62500000260293 11831500000000000000 Bool.false 868125273261475 140737488355328

noncomputable def ep633 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz11 4) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.logSumC qz11 3) (Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz24 qz554))) Bool.false 37024629115600541 2251799813685248 62500000260293 11831500000000000000 Bool.false 868125273261475 140737488355328 125000000023663 11831500000000000000

noncomputable def ep634 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz11 3) (Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz24 qz554)) Bool.false 111066322835651543 9007199254740992 187500000780879 47326000000000000000 Bool.false 2618212593799401 562949953421312 375000000070989 47326000000000000000 Bool.false

noncomputable def ep635 := nat_lit 1333952847108395306539293960306688

noncomputable def ep636 := nat_lit 1954844328585644412356054220800

noncomputable def ep637 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz11 3) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.logSumC qz11 2) (Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz24 qz555))) Bool.false 111066322835651543 9007199254740992 187500000780879 47326000000000000000 Bool.false 2618212593799401 562949953421312 375000000070989 47326000000000000000

noncomputable def ep638 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz11 2) (Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz24 qz555)) Bool.false 37020391056621213 4503599627370496 62500000260293 23663000000000000000 Bool.false 877353010496931 281474976710656 125000000023663 23663000000000000000 Bool.false

noncomputable def ep639 := nat_lit 500198250136051499702092015075328

noncomputable def ep640 := nat_lit 736961328863232634348483117056

noncomputable def ep641 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz11 2) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.logSumC qz11 1) (Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz24 qz592))) Bool.false 37020391056621213 4503599627370496 62500000260293 23663000000000000000 Bool.false 877353010496931 281474976710656 125000000023663 23663000000000000000

noncomputable def ep642 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz11 1) (Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz24 qz592)) Bool.false 37019480523554461 9007199254740992 62500000260293 47326000000000000000 Bool.false 881970637211043 562949953421312 125000000023663 47326000000000000000 Bool.false

noncomputable def ep643 := nat_lit 666900077470837350208005935726592

noncomputable def ep644 := nat_lit 987811672786590329305451986944

noncomputable abbrev qz908 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz24 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep645 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz11 1) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.logSumC qz11 0) qz908) Bool.false 37019480523554461 9007199254740992 62500000260293 47326000000000000000 Bool.false 881970637211043 562949953421312 125000000023663 47326000000000000000

noncomputable def ep646 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz11 0) qz908 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz909 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz260))

noncomputable def ep647 := @Enclosure.Complex.IsNear.of_eq qz908 qz909 Bool.false 37019480523554461 9007199254740992 62500000260293 47326000000000000000 Bool.false 881970637211043 562949953421312 125000000023663 47326000000000000000

noncomputable def ep648 := nat_lit 461392734040458355133747531962461570213188925568658760772192859758875253351424471275389824334904442020163899883520

noncomputable def ep649 := nat_lit 13548576979567389425210095184143802918913400364898782009818739141581948946904467292104430576940164906427433877504

noncomputable def ep650 := nat_lit 171580183815096838409762786655001594989583689877705293700221015247130697059093147184005944521237701009080320

noncomputable def ep651 := BSN.log_dyadic_bound 26662663524 92198663524 6 5 ep648 1048576 378608 ep649 ep650 624277 118861327048 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 26662663524) (BSN.artanhQ 92198663524) 0 5 ep649 ep648 ep650 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep652 := @Enclosure.Real.IsNear.mulLit_ff qz345 (Real.log (Enclosure.sfrac Bool.false 59430663524 16000000)) 1 2 0 1 37019480523554461 4503599627370496 62500000260293 23663000000000000000 37019480523554461 9007199254740992 62500000260293 47326000000000000000 qz346 (BSN.isNear_log_sfrac 59430663524 16000000 37019480523554461 4503599627370496 62500000260293 23663000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 59430663524) qz904)) Bool.false 310541910475733139980288 37778931862957161709568 1000000004164688 378608000000000000000 37019480523554461 4503599627370496 62500000260293 23663000000000000000 (BSN.log_rat_reduce_isNear 59430663524 16000000 11 118861327048 65536000000 624277 1048576 24973259072661432 36028797018963968 378608 1000000000000000 rfl rfl rfl rfl (ep651 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep653 := BSN.arctan_dyadic_bound_f 1000 243782 1 0 1048576 378608 0 1 1 0 1 1 4301 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 243782) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 243782) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz910 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable def ep654 := @Enclosure.Real.IsNear.subLit_ff_p qz354 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz910 qz605)) 884279719003555 562949953421312 1 2000000000000000 4301 1048576 1 378608 924813242884206624768 881970637211043 562949953421312 125000000023663 47326000000000000000 qz355 (ep653 rfl) rfl rfl

noncomputable abbrev qz911 := (@HAdd.hAdd Complex Complex Complex qz15 qz24 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz912 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz260)

noncomputable def ep655 := @ep646 37019480523554461 9007199254740992 62500000260293 47326000000000000000 Bool.false 881970637211043 562949953421312 125000000023663 47326000000000000000 Bool.false 37019480523554461 37019480523554461 9007199254740992 62500000260293 47326000000000000000 Bool.false 881970637211043 881970637211043 562949953421312 125000000023663 47326000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz11 0) (Complex.mk qz264 qz264) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz11) qz360) (ep647 (@congrArg Complex Complex qz911 qz912 Complex.log (BSN.w_shift_mk qz11 Bool.false 121891 1000 0 (@Eq.refl Real qz11) rfl)) (@Enclosure.Complex.IsNear.of_parts qz909 Bool.false 37019480523554461 9007199254740992 62500000260293 47326000000000000000 Bool.false 881970637211043 562949953421312 125000000023663 47326000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz909) (@HMul.hMul Real Real Real qz0 qz345 (Real.log (Enclosure.sfrac Bool.false 59430663524 16000000))) Bool.false 37019480523554461 9007199254740992 62500000260293 47326000000000000000 (Enclosure.clog_re_eq 1000 243782 4000 59430663524 16000000 rfl rfl rfl) (ep652 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz909) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz605 qz910)) Bool.false 881970637211043 562949953421312 125000000023663 47326000000000000000 (Enclosure.clog_im_eq 1000 243782 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz605 qz910)) (@HSub.hSub Real Real Real qz599 qz354 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz910 qz605))) Bool.false 881970637211043 562949953421312 125000000023663 47326000000000000000 (BSN.arctan_recip 243782 1000 rfl rfl) ep654)))) rfl rfl

noncomputable abbrev qz913 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz260))

noncomputable def ep656 := @Enclosure.Complex.IsNear.of_eq (Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz24 qz592)) qz913 Bool.false 37021301589687965 9007199254740992 62500000260293 47326000000000000000 Bool.false 872735383782819 562949953421312 125000000023663 47326000000000000000

noncomputable def ep657 := nat_lit 462595181606423832493278488718822211157060143804583396299768811813661822155126586919598802596842462254199099883520

noncomputable def ep658 := nat_lit 13602208810877889828875886856738576001277338977723253723190472474241851688796660551967670902195860644242473877504

noncomputable def ep659 := nat_lit 173130908335575075277807226674741302636210795504829414461324505862434162137404085085906491225331704209080320

noncomputable def ep660 := BSN.log_dyadic_bound 26686663524 92222663524 6 5 ep657 1048576 378608 ep658 ep659 624701 118909327048 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 26686663524) (BSN.artanhQ 92222663524) 0 5 ep658 ep657 ep659 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep661 := @Enclosure.Real.IsNear.mulLit_ff qz345 (Real.log (Enclosure.sfrac Bool.false 59454663524 16000000)) 1 2 0 1 37021301589687965 4503599627370496 62500000260293 23663000000000000000 37021301589687965 9007199254740992 62500000260293 47326000000000000000 qz346 (BSN.isNear_log_sfrac 59454663524 16000000 37021301589687965 4503599627370496 62500000260293 23663000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 59454663524) qz904)) Bool.false 310557186685669180702720 37778931862957161709568 1000000004164688 378608000000000000000 37021301589687965 4503599627370496 62500000260293 23663000000000000000 (BSN.log_rat_reduce_isNear 59454663524 16000000 11 118909327048 65536000000 624701 1048576 24973259072661432 36028797018963968 378608 1000000000000000 rfl rfl rfl rfl (ep660 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep662 := BSN.arctan_dyadic_bound_f 5000 243782 1 0 1048576 378608 0 1 1 0 1 1 21503 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 243782) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 243782) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz914 := (@Nat.cast Real Real.instNatCast 5000)

noncomputable def ep663 := @Enclosure.Real.IsNear.subLit_ff_p qz354 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz914 qz605)) 884279719003555 562949953421312 1 2000000000000000 21503 1048576 1 378608 915129377785453215744 872735383782819 562949953421312 125000000023663 47326000000000000000 qz355 (ep662 rfl) rfl rfl

noncomputable abbrev qz915 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz260)

noncomputable def ep664 := @ep642 37021301589687965 9007199254740992 62500000260293 47326000000000000000 Bool.false 872735383782819 562949953421312 125000000023663 47326000000000000000 Bool.false ep643 37020391056621213 4503599627370496 62500000260293 23663000000000000000 Bool.false ep644 877353010496931 281474976710656 125000000023663 23663000000000000000 (ep645 (BSN.log_sum_c_succ qz11 0 1 rfl) (ep655 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep656 (@congrArg Complex Complex (@HAdd.hAdd Complex Complex Complex qz15 qz24 qz592) qz915 Complex.log (BSN.w_shift_mk qz11 Bool.false 121891 1000 1 (@Eq.refl Real qz11) rfl)) (@Enclosure.Complex.IsNear.of_parts qz913 Bool.false 37021301589687965 9007199254740992 62500000260293 47326000000000000000 Bool.false 872735383782819 562949953421312 125000000023663 47326000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz913) (@HMul.hMul Real Real Real qz0 qz345 (Real.log (Enclosure.sfrac Bool.false 59454663524 16000000))) Bool.false 37021301589687965 9007199254740992 62500000260293 47326000000000000000 (Enclosure.clog_re_eq 5000 243782 4000 59454663524 16000000 rfl rfl rfl) (ep661 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz913) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz605 qz914)) Bool.false 872735383782819 562949953421312 125000000023663 47326000000000000000 (Enclosure.clog_im_eq 5000 243782 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz605 qz914)) (@HSub.hSub Real Real Real qz599 qz354 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz914 qz605))) Bool.false 872735383782819 562949953421312 125000000023663 47326000000000000000 (BSN.arctan_recip 243782 5000 rfl rfl) ep663)))) rfl rfl

noncomputable abbrev qz916 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 9000 4000) qz260))

noncomputable def ep665 := @Enclosure.Complex.IsNear.of_eq (Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz24 qz555)) qz916 Bool.false 37025540722409117 9007199254740992 62500000260293 47326000000000000000 Bool.false 863506572805539 562949953421312 125000000023663 47326000000000000000

noncomputable def ep666 := nat_lit 465411867947754566899734167764530467622907982418247077224455617146862423908222157333174646528787741466947899883520

noncomputable def ep667 := nat_lit 13728062400644194431579034004711108030715361212633355742392379291367838993437750938465934401449077099144233877504

noncomputable def ep668 := nat_lit 176798432106634289558297419188003627708024191550252447653011092703230849385212735202450502313551045009080320

noncomputable def ep669 := BSN.log_dyadic_bound 26742663524 92278663524 6 5 ep666 1048576 378608 ep667 ep668 625688 119021327048 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 26742663524) (BSN.artanhQ 92278663524) 0 5 ep667 ep666 ep668 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep670 := @Enclosure.Real.IsNear.mulLit_ff qz345 (Real.log (Enclosure.sfrac Bool.false 59510663524 16000000)) 1 2 0 1 37025540722409117 4503599627370496 62500000260293 23663000000000000000 37025540722409117 9007199254740992 62500000260293 47326000000000000000 qz346 (BSN.isNear_log_sfrac 59510663524 16000000 37025540722409117 4503599627370496 62500000260293 23663000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 59510663524) qz904)) Bool.false 310592747108326898139136 37778931862957161709568 1000000004164688 378608000000000000000 37025540722409117 4503599627370496 62500000260293 23663000000000000000 (BSN.log_rat_reduce_isNear 59510663524 16000000 11 119021327048 65536000000 625688 1048576 24973259072661432 36028797018963968 378608 1000000000000000 rfl rfl rfl rfl (ep669 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep671 := BSN.arctan_dyadic_bound_f 9000 243782 1 0 1048576 378608 0 1 1 0 1 1 38693 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 243782) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 243782) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz917 := (@Nat.cast Real Real.instNatCast 9000)

noncomputable def ep672 := @Enclosure.Real.IsNear.subLit_ff_p qz354 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz917 qz605)) 884279719003555 562949953421312 1 2000000000000000 38693 1048576 1 378608 905452268086140862464 863506572805539 562949953421312 125000000023663 47326000000000000000 qz355 (ep671 rfl) rfl rfl

noncomputable abbrev qz918 := (Complex.mk (Enclosure.sfrac Bool.false 9000 4000) qz260)

noncomputable def ep673 := @ep638 37025540722409117 9007199254740992 62500000260293 47326000000000000000 Bool.false 863506572805539 562949953421312 125000000023663 47326000000000000000 Bool.false ep639 111066322835651543 9007199254740992 187500000780879 47326000000000000000 Bool.false ep640 2618212593799401 562949953421312 375000000070989 47326000000000000000 (ep641 (BSN.log_sum_c_succ qz11 1 2 rfl) (ep664 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep665 (@congrArg Complex Complex (@HAdd.hAdd Complex Complex Complex qz15 qz24 qz555) qz918 Complex.log (BSN.w_shift_mk qz11 Bool.false 121891 1000 2 (@Eq.refl Real qz11) rfl)) (@Enclosure.Complex.IsNear.of_parts qz916 Bool.false 37025540722409117 9007199254740992 62500000260293 47326000000000000000 Bool.false 863506572805539 562949953421312 125000000023663 47326000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz916) (@HMul.hMul Real Real Real qz0 qz345 (Real.log (Enclosure.sfrac Bool.false 59510663524 16000000))) Bool.false 37025540722409117 9007199254740992 62500000260293 47326000000000000000 (Enclosure.clog_re_eq 9000 243782 4000 59510663524 16000000 rfl rfl rfl) (ep670 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz916) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz605 qz917)) Bool.false 863506572805539 562949953421312 125000000023663 47326000000000000000 (Enclosure.clog_im_eq 9000 243782 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz605 qz917)) (@HSub.hSub Real Real Real qz599 qz354 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz917 qz605))) Bool.false 863506572805539 562949953421312 125000000023663 47326000000000000000 (BSN.arctan_recip 243782 9000 rfl rfl) ep672)))) rfl rfl

noncomputable abbrev qz919 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 13000 4000) qz260))

noncomputable def ep674 := @Enclosure.Complex.IsNear.of_eq (Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz24 qz554)) qz919 Bool.false 37032193626750621 9007199254740992 62500000260293 47326000000000000000 Bool.false 854288499246499 562949953421312 125000000023663 47326000000000000000

noncomputable def ep675 := nat_lit 469869285087433583686296707295027745492016600253426008156163755260961667171120218681096499550156036458410299883520

noncomputable def ep676 := nat_lit 13927861911719119499452590052760172854070025798835426232147721348135782470560525112537161685395637631132713877504

noncomputable def ep677 := nat_lit 182703109080335147385727056175039278193396440560364550553460737990855196819516800707814142854695723409080320

noncomputable def ep678 := BSN.log_dyadic_bound 26830663524 92366663524 6 5 ep675 1048576 378608 ep676 ep677 627237 119197327048 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 26830663524) (BSN.artanhQ 92366663524) 0 5 ep676 ep675 ep677 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep679 := @Enclosure.Real.IsNear.mulLit_ff qz345 (Real.log (Enclosure.sfrac Bool.false 59598663524 16000000)) 1 2 0 1 37032193626750621 4503599627370496 62500000260293 23663000000000000000 37032193626750621 9007199254740992 62500000260293 47326000000000000000 qz346 (BSN.isNear_log_sfrac 59598663524 16000000 37032193626750621 4503599627370496 62500000260293 23663000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 59598663524) qz904)) Bool.false 310648555714909273325568 37778931862957161709568 1000000004164688 378608000000000000000 37032193626750621 4503599627370496 62500000260293 23663000000000000000 (BSN.log_rat_reduce_isNear 59598663524 16000000 11 119197327048 65536000000 627237 1048576 24973259072661432 36028797018963968 378608 1000000000000000 rfl rfl rfl rfl (ep678 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep680 := BSN.arctan_dyadic_bound_f 13000 243782 1 0 1048576 378608 0 1 1 0 1 1 55863 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 13000) (BSN.arctanEvenQ 243782) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 13000) (BSN.arctanOddQ 243782) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz920 := (@Nat.cast Real Real.instNatCast 13000)

noncomputable def ep681 := @Enclosure.Real.IsNear.subLit_ff_p qz354 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz920 qz605)) 884279719003555 562949953421312 1 2000000000000000 55863 1048576 1 378608 895786417385896935424 854288499246499 562949953421312 125000000023663 47326000000000000000 qz355 (ep680 rfl) rfl rfl

noncomputable abbrev qz921 := (Complex.mk (Enclosure.sfrac Bool.false 13000 4000) qz260)

noncomputable def ep682 := @ep634 37032193626750621 9007199254740992 62500000260293 47326000000000000000 Bool.false 854288499246499 562949953421312 125000000023663 47326000000000000000 Bool.false ep635 37024629115600541 2251799813685248 62500000260293 11831500000000000000 Bool.false ep636 868125273261475 140737488355328 125000000023663 11831500000000000000 (ep637 (BSN.log_sum_c_succ qz11 2 3 rfl) (ep673 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep674 (@congrArg Complex Complex (@HAdd.hAdd Complex Complex Complex qz15 qz24 qz554) qz921 Complex.log (BSN.w_shift_mk qz11 Bool.false 121891 1000 3 (@Eq.refl Real qz11) rfl)) (@Enclosure.Complex.IsNear.of_parts qz919 Bool.false 37032193626750621 9007199254740992 62500000260293 47326000000000000000 Bool.false 854288499246499 562949953421312 125000000023663 47326000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz919) (@HMul.hMul Real Real Real qz0 qz345 (Real.log (Enclosure.sfrac Bool.false 59598663524 16000000))) Bool.false 37032193626750621 9007199254740992 62500000260293 47326000000000000000 (Enclosure.clog_re_eq 13000 243782 4000 59598663524 16000000 rfl rfl rfl) (ep679 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz919) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz605 qz920)) Bool.false 854288499246499 562949953421312 125000000023663 47326000000000000000 (Enclosure.clog_im_eq 13000 243782 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz605 qz920)) (@HSub.hSub Real Real Real qz599 qz354 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz920 qz605))) Bool.false 854288499246499 562949953421312 125000000023663 47326000000000000000 (BSN.arctan_recip 243782 13000 rfl rfl) ep681)))) rfl rfl

noncomputable def ep683 := @ep503 ep488 Bool.false 37024629115600541 2251799813685248 62500000260293 11831500000000000000 Bool.false 868125273261475 140737488355328 125000000023663 11831500000000000000 Bool.true ep504 ep494 ep495 ep496 ep497 Bool.false ep505 ep490 ep486 ep491 ep488 (@ep506 ep495 ep500 ep497 Bool.false ep501 ep486 ep502 ep488 (BSN.logGammaStirling_unfold 2 qz5) (ep631 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep632 125000000023663 11831500000000000000 (BSN.log_sum_c_eq qz11 4) (ep633 (BSN.log_sum_c_succ qz11 3 4 rfl) (ep682 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable def ep684 := @Enclosure.Real.IsNear.mulLit_ff (@HDiv.hDiv Real Real Real qz1 qz11 (2 : Real)) (Real.log Real.pi) 121891 2000 0 1 75021 65536 1 262144 9144384711 131072000 121891 524288000 (@Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real qz1 qz11 (2 : Real)) (Enclosure.sfrac Bool.false 121891 2000) Bool.false 121891 2000 0 1 (BSN.t_half_eq qz11 Bool.false 121891 1000 (@Eq.refl Real qz11)) (Enclosure.Real.IsNear.const Bool.false 121891 2000)) EMRow40.d6 rfl

noncomputable def ep685 := @ep492 121891 524288000 ep493 ep485 ep486 ep487 ep488 (@ep498 ep491 ep488 (ep683 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep684 rfl rfl

noncomputable def ep686 := BSN.cos_dyadic_bound_f 249822 2147483648 1 0 1048576 378978 0 1 1 0 1 1 1048575 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 249822) qz274 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 249822) qz275 0 0 rfl) rfl rfl

noncomputable def ep687 := @ep484 1048576 Bool.false 1048575 1048576 1 189304 (@ep489 125179671 1048576 351 1048576 ep685 rfl) (Enclosure.sfrac_false_div 125179671 1048576) (BSN.cos_reduce0 qz902 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 17579666153544876032) qz273) 226375608064910080 72057594037927936 Bool.false 1048575 1048576 19 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q0 125179671 1048576 226375608064910080 72057594037927936 19 17579666153544876032 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1048575 1048576 17579666153544876032 151115727451828646838272 249822 2147483648 378978 378608 (ep686 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep688 := nat_lit 1891988926847781360137541990045844207

noncomputable def ep689 := nat_lit 5231809279435009066433970105449131954719

noncomputable def ep690 := nat_lit 921287728649130345095302574243840000000000

noncomputable abbrev qz45 := (@HPow.hPow Complex Complex Complex (@instHPow Complex Complex Complex.instPow) (@Nat.cast Complex Complex.instNatCast 31) (@Neg.neg Complex Complex.instNeg qz261))

noncomputable abbrev qz46 := (@HAdd.hAdd Complex Complex Complex qz262 (@HDiv.hDiv Complex Complex Complex qz352 (@Nat.cast Complex Complex.instNatCast 31) (@HSub.hSub Complex Complex Complex qz597 qz261 (1 : Complex))) qz351)

noncomputable abbrev qz47 := (@instHSub Nat instSubNat)

noncomputable abbrev qz48 := qz256

noncomputable abbrev qz49 := (@Nat.cast Complex Complex.instNatCast 31)

noncomputable def ep691 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz14 2 31) (@HAdd.hAdd Complex Complex Complex qz15 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 31, @HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast n) qz17) (@HMul.hMul Complex Complex Complex qz3 qz45 (@HAdd.hAdd Complex Complex Complex qz15 qz46 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz49 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1))))))) Bool.false ep479 ep480 ep481

noncomputable def ep692 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 31, @HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast n) qz17) (@HMul.hMul Complex Complex Complex qz3 qz45 (@HAdd.hAdd Complex Complex Complex qz15 qz46 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz49 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))))) Bool.false 998876950005 1099511627776 145697227047729 26017743648063488

noncomputable def ep693 := nat_lit 30086576941585408877675587047124990049

noncomputable def ep694 := nat_lit 214580396301668310734390633211611762101

noncomputable def ep695 := nat_lit 14039263290710029111412327910045844207

noncomputable def ep696 := nat_lit 71507411055887474020483268969131954719

noncomputable def ep697 := nat_lit 316929080932966624082614475315089995395896207998976

noncomputable def ep698 := nat_lit 260032978086571433982372509090357069112833736704

noncomputable def ep699 := @ep692 Bool.true 4764536827 137438953472 9108135207321 1626108978003968 Bool.true ep693 ep480 ep694 ep482 Bool.false ep695 ep480 ep696 ep690 Bool.false ep697 ep479 ep480 ep481 ep482 Bool.false ep698 ep688 ep480

noncomputable def ep700 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 31, @HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast n) qz17) (BSN.headSumC qz14 31) Bool.false 998876950005 1099511627776 145697227047729 26017743648063488 Bool.true 4764536827 137438953472 9108135207321

noncomputable abbrev qz922 := (@Nat.cast Complex Complex.instNatCast 30)

noncomputable def ep701 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 31) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz14 30) (@HPow.hPow Complex Complex Complex qz16 qz922 qz17)) Bool.false 998876950005 1099511627776 145697227047729 26017743648063488 Bool.true 4764536827 137438953472 9108135207321 1626108978003968

noncomputable def ep702 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz14 30) (@HPow.hPow Complex Complex Complex qz16 qz922 qz17) Bool.false 799463029257 1099511627776 142585111651621 26017743648063488 Bool.true 7646519749 137438953472 8914990398205 1626108978003968 Bool.false

noncomputable abbrev qz923 := (@Nat.cast Complex Complex.instNatCast 29)

noncomputable def ep703 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 30) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz14 29) (@HPow.hPow Complex Complex Complex qz16 qz923 qz17)) Bool.false 799463029257 1099511627776 142585111651621 26017743648063488 Bool.true 7646519749 137438953472 8914990398205 1626108978003968

noncomputable def ep704 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz14 29) (@HPow.hPow Complex Complex Complex qz16 qz923 qz17) Bool.false 445512029211 549755813888 17428642681575 3252217956007936 Bool.false 60659901299 549755813888 69736412834787 13008871824031744 Bool.true

noncomputable abbrev qz924 := (@Nat.cast Complex Complex.instNatCast 28)

noncomputable def ep705 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 29) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz14 28) (@HPow.hPow Complex Complex Complex qz16 qz924 qz17)) Bool.false 445512029211 549755813888 17428642681575 3252217956007936 Bool.false 60659901299 549755813888 69736412834787 13008871824031744

noncomputable def ep706 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz14 28) (@HPow.hPow Complex Complex Complex qz16 qz924 qz17) Bool.false 255043207603 274877906944 68108938607485 13008871824031744 Bool.true 41458617633 1099511627776 136257545655203 26017743648063488 Bool.true

noncomputable abbrev qz925 := (@Nat.cast Complex Complex.instNatCast 27)

noncomputable def ep707 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 28) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz14 27) (@HPow.hPow Complex Complex Complex qz16 qz925 qz17)) Bool.false 255043207603 274877906944 68108938607485 13008871824031744 Bool.true 41458617633 1099511627776 136257545655203 26017743648063488

noncomputable def ep708 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz14 27) (@HPow.hPow Complex Complex Complex qz16 qz925 qz17) Bool.false 824555539179 1099511627776 132940458015649 26017743648063488 Bool.true 30534313109 274877906944 16624200523849 3252217956007936 Bool.false

noncomputable abbrev qz926 := (@Nat.cast Complex Complex.instNatCast 26)

noncomputable def ep709 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 27) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz14 26) (@HPow.hPow Complex Complex Complex qz16 qz926 qz17)) Bool.false 824555539179 1099511627776 132940458015649 26017743648063488 Bool.true 30534313109 274877906944 16624200523849 3252217956007936

noncomputable def ep710 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz14 26) (@HPow.hPow Complex Complex Complex qz16 qz926 qz17) Bool.false 765163373063 1099511627776 129617149601853 26017743648063488 Bool.false 85154387495 1099511627776 129653277229081 26017743648063488 Bool.false

noncomputable abbrev qz927 := (@Nat.cast Complex Complex.instNatCast 25)

noncomputable def ep711 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 26) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz14 25) (@HPow.hPow Complex Complex Complex qz16 qz927 qz17)) Bool.false 765163373063 1099511627776 129617149601853 26017743648063488 Bool.false 85154387495 1099511627776 129653277229081 26017743648063488

noncomputable def ep712 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz14 25) (@HPow.hPow Complex Complex Complex qz16 qz927 qz17) Bool.false 485967511519 549755813888 63105837126949 13008871824031744 Bool.false 160003348715 1099511627776 126262687256917 26017743648063488 Bool.true

noncomputable abbrev qz928 := (@Nat.cast Real Real.instNatCast 25)

noncomputable abbrev qz361 := (@Inv.inv Real Real.instInv (Real.sqrt qz928))

noncomputable abbrev qz362 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 25 1)))

noncomputable def ep713 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz927 qz17) (Complex.mk (@HMul.hMul Real Real Real qz0 qz361 (Real.cos qz362)) (@HMul.hMul Real Real Real qz0 qz361 (@Neg.neg Real Real.instNeg (Real.sin qz362)))) Bool.true 206771649975 1099511627776 3405475347955 26017743648063488 Bool.true 18712240305 274877906944 847647493041 6504435912015872 (BSN.cpow_neg_s_mk qz11 121891 1000 25 (@Eq.refl Real qz11) rfl)

noncomputable abbrev qz929 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 25) qz267)

noncomputable def ep714 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz928) 5242881 1048576 1 1048576 104857 104858 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz928) (Real.sqrt qz929) Bool.false 5242881 1048576 1 1048576 (BSN.sqrt_natCast_div_one 25) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz929) Bool.false 5242881 1048576 1 1048576 5242881 1048576 1 1048576 (BSN.sqrt_enclosure 25 1 2621440 2621441 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep715 := BSN.log_dyadic_bound 9 41 5 4 7545754341519345 524288 189304 124828057765224 4519905705 233982 50 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 9) (BSN.artanhQ 41) 0 4 124828057765224 7545754341519345 4519905705 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz363 := (Real.log (Enclosure.sfrac Bool.false 25 1))

noncomputable def ep716 := @Enclosure.Real.IsNear.mulLit_ff qz11 qz363 121891 1000 0 1 3624129903009015 1125899906842624 31250000023663 5915750000000000000 88349763601534369473 225179981368524800 3809093752884306733 5915750000000000000000 qz272 (BSN.isNear_log_sfrac 25 1 3624129903009015 1125899906842624 31250000023663 5915750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz929) Bool.false 60802810194841294602240 18889465931478580854784 1000000000757216 189304000000000000000 3624129903009015 1125899906842624 31250000023663 5915750000000000000 (BSN.log_rat_reduce_isNear 25 1 4 50 32 233982 524288 24973259072661432 36028797018963968 189304 1000000000000000 rfl rfl rfl rfl (ep715 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep717 := nat_lit 3067126004355654670464638802059769742702519906881479780438414734716234468874785

noncomputable def ep718 := nat_lit 2271001221509762900144414211424094304802826488626195063745038363255177927201

noncomputable def ep719 := nat_lit 8029272199906174996997629715718996030584538037041337966283118052621058082789921

noncomputable def ep720 := BSN.sin_dyadic_bound_f 2627405901 2147483648 3 2 1048576 378978 ep717 ep88 ep718 ep719 ep91 ep718 985965 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2627405901) qz268 0 2 ep717 ep88 ep718 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2627405901) qz269 0 2 ep719 ep91 ep718 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz930 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 205705323) qz279)

noncomputable def ep721 := @Enclosure.Real.IsNear.cos_image qz362 qz930 Bool.false 205705323 524288 169 262144 Bool.true 985965 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz362 Bool.false 88349763601534369473 225179981368524800 3809093752884306733 5915750000000000000000 205705323 524288 169 262144 (ep716 rfl) rfl) (Enclosure.sfrac_false_div 205705323 524288) (BSN.cos_reduce1 qz930 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 92443626866922221469696) qz281) 226375608064910080 72057594037927936 Bool.false 985965 1048576 62 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q1 205705323 524288 226375608064910080 72057594037927936 62 92443626866922221469696 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 985965 1048576 92443626866922221469696 75557863725914323419136 2627405901 2147483648 378978 378608 (ep720 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep722 := nat_lit 1704968225184923600435974629682727232303534537817989298049672647448243672898081

noncomputable def ep723 := nat_lit 5110362673111751275507635060625333508300997960476715504021527865618220662839841

noncomputable def ep724 := BSN.cos_dyadic_bound_f 2627405901 2147483648 3 2 1048576 378978 ep722 ep95 ep718 ep723 ep97 ep718 356908 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2627405901) qz274 0 2 ep722 ep95 ep718 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2627405901) qz275 0 2 ep723 ep97 ep718 rfl rfl rfl rfl) rfl rfl

noncomputable def ep725 := @Enclosure.Real.IsNear.sin_image qz362 qz930 Bool.false 205705323 524288 169 262144 Bool.false 356908 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz362 Bool.false 88349763601534369473 225179981368524800 3809093752884306733 5915750000000000000000 205705323 524288 169 262144 (ep716 rfl) rfl) (Enclosure.sfrac_false_div 205705323 524288) (BSN.sin_reduce1 qz930 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 92443626866922221469696) qz281) 226375608064910080 72057594037927936 Bool.false 356908 1048576 62 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q1 205705323 524288 226375608064910080 72057594037927936 62 92443626866922221469696 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 356908 1048576 92443626866922221469696 75557863725914323419136 2627405901 2147483648 378978 378608 (ep724 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz608 := (@Enclosure.Real.IsNear.recentre' qz361 Bool.false 209715 1048576 1 1048576 209715 1048576 1 1048576 (ep714 rfl rfl) rfl)

noncomputable def ep726 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz361 (Real.cos qz362)) (@HMul.hMul Real Real Real qz0 qz361 (@Neg.neg Real Real.instNeg (Real.sin qz362))) Bool.true 206771649975 1099511627776 3405475347955 26017743648063488 Bool.true 18712240305 274877906944 847647493041 6504435912015872 (@Enclosure.Real.IsNear.mulLit_ft qz361 (Real.cos qz362) 209715 1048576 1 1048576 985965 1048576 4031815 6203113472 206771649975 1099511627776 3405475347955 26017743648063488 qz608 (@Enclosure.Real.IsNear.recentre' (Real.cos qz362) Bool.true 985965 1048576 32254520 49624907776 985965 1048576 4031815 6203113472 (ep721 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz361 (@Neg.neg Real Real.instNeg (Real.sin qz362)) 209715 1048576 1 1048576 89227 262144 4031815 6203113472 18712240305 274877906944 847647493041 6504435912015872 qz608 (@Enclosure.Real.IsNear.neg (Real.sin qz362) Bool.false 89227 262144 4031815 6203113472 (@Enclosure.Real.IsNear.recentre' (Real.sin qz362) Bool.false 356908 1048576 32254520 49624907776 89227 262144 4031815 6203113472 (ep725 rfl rfl) rfl)) rfl)

noncomputable def ep727 := @ep712 206771649975 1099511627776 3405475347955 26017743648063488 Bool.true 18712240305 274877906944 847647493041 6504435912015872 Bool.false 420653012915536940498944 765163373063 1099511627776 129617149601853 26017743648063488 Bool.false 23407059801723927265280 85154387495 1099511627776 129653277229081 26017743648063488 EMRow40.d9 (ep713 ep726) rfl rfl

noncomputable abbrev qz931 := (@Nat.cast Real Real.instNatCast 26)

noncomputable abbrev qz364 := (@Inv.inv Real Real.instInv (Real.sqrt qz931))

noncomputable abbrev qz365 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 26 1)))

noncomputable def ep728 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz926 qz17) (Complex.mk (@HMul.hMul Real Real Real qz0 qz364 (Real.cos qz365)) (@HMul.hMul Real Real Real qz0 qz364 (@Neg.neg Real Real.instNeg (Real.sin qz365)))) Bool.false 14848041529 274877906944 830827103449 6504435912015872 Bool.true 207291639931 1099511627776 3340326961711 26017743648063488 (BSN.cpow_neg_s_mk qz11 121891 1000 26 (@Eq.refl Real qz11) rfl)

noncomputable abbrev qz932 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26) qz267)

noncomputable def ep729 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz931) 5346709 1048576 1 1048576 102821 102822 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz931) (Real.sqrt qz932) Bool.false 5346709 1048576 1 1048576 (BSN.sqrt_natCast_div_one 26) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz932) Bool.false 5346709 1048576 1 1048576 5346709 1048576 1 1048576 (BSN.sqrt_enclosure 26 1 2673354 2673355 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep730 := BSN.log_dyadic_bound 10 42 5 4 9150106136613120 524288 189304 179034245376000 10500000000 254545 52 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 10) (BSN.artanhQ 42) 0 4 179034245376000 9150106136613120 10500000000 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz366 := (Real.log (Enclosure.sfrac Bool.false 26 1))

noncomputable def ep731 := @Enclosure.Real.IsNear.mulLit_ff qz11 qz366 121891 1000 0 1 3668288609262839 1125899906842624 31250000023663 5915750000000000000 447131366871656708549 1125899906842624000 3809093752884306733 5915750000000000000000 qz272 (BSN.isNear_log_sfrac 26 1 3668288609262839 1125899906842624 31250000023663 5915750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz932) Bool.false 61543670347942250676224 18889465931478580854784 1000000000757216 189304000000000000000 3668288609262839 1125899906842624 31250000023663 5915750000000000000 (BSN.log_rat_reduce_isNear 26 1 4 52 32 254545 524288 24973259072661432 36028797018963968 189304 1000000000000000 rfl rfl rfl rfl (ep730 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep732 := nat_lit 2119283048208653836936133080931933252155534251883138806599552791570724552690625

noncomputable def ep733 := nat_lit 3506566525056941464404967040891528314898238956535751971687715185224187890625

noncomputable def ep734 := nat_lit 6350836011575847627879589308714016699836806277736344915855282944341725282290625

noncomputable def ep735 := BSN.cos_dyadic_bound_f 2774024295 2147483648 3 2 1048576 378978 ep732 ep95 ep733 ep734 ep97 ep733 288812 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2774024295) qz274 0 2 ep732 ep95 ep733 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2774024295) qz275 0 2 ep734 ep97 ep733 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz933 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 416423535) qz270)

noncomputable def ep736 := @Enclosure.Real.IsNear.cos_image qz365 qz933 Bool.false 416423535 1048576 169 262144 Bool.false 288812 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz365 Bool.false 447131366871656708549 1125899906842624000 3809093752884306733 5915750000000000000000 416423535 1048576 169 262144 (ep731 rfl) rfl) (Enclosure.sfrac_false_div 416423535 1048576) (BSN.cos_reduce0 qz933 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 195204605965420053135360) qz273) 226375608064910080 72057594037927936 Bool.false 288812 1048576 63 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q0 416423535 1048576 226375608064910080 72057594037927936 63 195204605965420053135360 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 288812 1048576 195204605965420053135360 151115727451828646838272 2774024295 2147483648 378978 378608 (ep735 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep737 := nat_lit 3811904233555531353313515572044766631228043062224421250301844852679124844530625

noncomputable def ep738 := nat_lit 9977881408747728020116837503955802512135039442753378723788765932431154479090625

noncomputable def ep739 := BSN.sin_dyadic_bound_f 2774024295 2147483648 3 2 1048576 378978 ep737 ep88 ep733 ep738 ep91 ep733 1008017 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2774024295) qz268 0 2 ep737 ep88 ep733 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2774024295) qz269 0 2 ep738 ep91 ep733 rfl rfl rfl rfl) rfl rfl

noncomputable def ep740 := @Enclosure.Real.IsNear.sin_image qz365 qz933 Bool.false 416423535 1048576 169 262144 Bool.false 1008017 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz365 Bool.false 447131366871656708549 1125899906842624000 3809093752884306733 5915750000000000000000 416423535 1048576 169 262144 (ep731 rfl) rfl) (Enclosure.sfrac_false_div 416423535 1048576) (BSN.sin_reduce0 qz933 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 195204605965420053135360) qz273) 226375608064910080 72057594037927936 Bool.false 1008017 1048576 63 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q0 416423535 1048576 226375608064910080 72057594037927936 63 195204605965420053135360 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1008017 1048576 195204605965420053135360 151115727451828646838272 2774024295 2147483648 378978 378608 (ep739 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz609 := (@Enclosure.Real.IsNear.recentre' qz364 Bool.false 205643 1048576 1 1048576 205643 1048576 1 1048576 (ep729 rfl rfl) rfl)

noncomputable def ep741 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz364 (Real.cos qz365)) (@HMul.hMul Real Real Real qz0 qz364 (@Neg.neg Real Real.instNeg (Real.sin qz365))) Bool.false 14848041529 274877906944 830827103449 6504435912015872 Bool.true 207291639931 1099511627776 3340326961711 26017743648063488 (@Enclosure.Real.IsNear.mulLit_ff qz364 (Real.cos qz365) 205643 1048576 1 1048576 72203 262144 4031815 6203113472 14848041529 274877906944 830827103449 6504435912015872 qz609 (@Enclosure.Real.IsNear.recentre' (Real.cos qz365) Bool.false 288812 1048576 32254520 49624907776 72203 262144 4031815 6203113472 (ep736 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz364 (@Neg.neg Real Real.instNeg (Real.sin qz365)) 205643 1048576 1 1048576 1008017 1048576 4031815 6203113472 207291639931 1099511627776 3340326961711 26017743648063488 qz609 (@Enclosure.Real.IsNear.neg (Real.sin qz365) Bool.false 1008017 1048576 4031815 6203113472 (@Enclosure.Real.IsNear.recentre' (Real.sin qz365) Bool.false 1008017 1048576 32254520 49624907776 1008017 1048576 4031815 6203113472 (ep740 rfl rfl) rfl)) rfl)

noncomputable def ep742 := @ep710 14848041529 274877906944 830827103449 6504435912015872 Bool.true 207291639931 1099511627776 3340326961711 26017743648063488 Bool.false 226652100768604908158976 824555539179 1099511627776 132940458015649 26017743648063488 Bool.true 134291329237994581262336 30534313109 274877906944 16624200523849 3252217956007936 (ep711 (BSN.head_sum_c_succ qz14 25 26 rfl rfl) (ep727 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep728 ep741) rfl rfl

noncomputable abbrev qz934 := (@Nat.cast Real Real.instNatCast 27)

noncomputable abbrev qz367 := (@Inv.inv Real Real.instInv (Real.sqrt qz934))

noncomputable abbrev qz368 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 27 1)))

noncomputable def ep743 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz925 qz17) (Complex.mk (@HMul.hMul Real Real Real qz0 qz367 (Real.cos qz368)) (@HMul.hMul Real Real Real qz0 qz367 (@Neg.neg Real Real.instNeg (Real.sin qz368)))) Bool.false 195617291233 1099511627776 3277419199321 26017743648063488 Bool.false 80678634803 1099511627776 3263941464411 26017743648063488 (BSN.cpow_neg_s_mk qz11 121891 1000 27 (@Eq.refl Real qz11) rfl)

noncomputable abbrev qz935 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 27) qz267)

noncomputable def ep744 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz934) 5448561 1048576 1 1048576 100899 100900 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz934) (Real.sqrt qz935) Bool.false 5448561 1048576 1 1048576 (BSN.sqrt_natCast_div_one 27) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz935) Bool.false 5448561 1048576 1 1048576 5448561 1048576 1 1048576 (BSN.sqrt_enclosure 27 1 2724280 2724281 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep745 := BSN.log_dyadic_bound 11 43 5 4 11045349262332945 524288 189304 250863800262504 22507682505 274332 54 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 11) (BSN.artanhQ 43) 0 4 250863800262504 11045349262332945 22507682505 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz369 := (Real.log (Enclosure.sfrac Bool.false 27 1))

noncomputable def ep746 := @Enclosure.Real.IsNear.mulLit_ff qz11 qz369 121891 1000 0 1 3710780868205815 1125899906842624 31250000023663 5915750000000000000 90462158161294999233 225179981368524800 3809093752884306733 5915750000000000000000 qz272 (BSN.isNear_log_sfrac 27 1 3710780868205815 1125899906842624 31250000023663 5915750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz935) Bool.false 62256572154556490711040 18889465931478580854784 1000000000757216 189304000000000000000 3710780868205815 1125899906842624 31250000023663 5915750000000000000 (BSN.log_rat_reduce_isNear 27 1 4 54 32 274332 524288 24973259072661432 36028797018963968 189304 1000000000000000 rfl rfl rfl rfl (ep745 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep747 := nat_lit 2650128846275257251263510087187110431775006494972817138948178060663668604928000

noncomputable def ep748 := nat_lit 1695803381843843955926719071630331128378834974019023050828328977138614009856

noncomputable def ep749 := nat_lit 6938068058578878958332930778421697261393356039732775993258172864346621923557376

noncomputable def ep750 := BSN.sin_dyadic_bound_f 2533214336 2147483648 3 2 1048576 378978 ep747 ep88 ep748 ep749 ep91 ep748 969367 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2533214336) qz268 0 2 ep747 ep88 ep748 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2533214336) qz269 0 2 ep749 ep91 ep748 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz936 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 210623625) qz279)

noncomputable def ep751 := @Enclosure.Real.IsNear.cos_image qz368 qz936 Bool.false 210623625 524288 169 262144 Bool.false 969367 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz368 Bool.false 90462158161294999233 225179981368524800 3809093752884306733 5915750000000000000000 210623625 524288 169 262144 (ep746 rfl) rfl) (Enclosure.sfrac_false_div 210623625 524288) (BSN.cos_reduce3 qz936 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 89129555803966852300800) qz281) 226375608064910080 72057594037927936 Bool.false 969367 1048576 63 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q3 210623625 524288 226375608064910080 72057594037927936 63 89129555803966852300800 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 969367 1048576 89129555803966852300800 75557863725914323419136 2533214336 2147483648 378978 378608 (ep750 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep752 := nat_lit 1473047493878184625793473034691341498154283090528906865216022624358544164519936

noncomputable def ep753 := nat_lit 4415750874870866189468565665930763832206091601638682549546411215121355265540096

noncomputable def ep754 := BSN.cos_dyadic_bound_f 2533214336 2147483648 3 2 1048576 378978 ep752 ep95 ep748 ep753 ep97 ep748 399797 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2533214336) qz274 0 2 ep752 ep95 ep748 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2533214336) qz275 0 2 ep753 ep97 ep748 rfl rfl rfl rfl) rfl rfl

noncomputable def ep755 := @Enclosure.Real.IsNear.sin_image qz368 qz936 Bool.false 210623625 524288 169 262144 Bool.true 399797 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz368 Bool.false 90462158161294999233 225179981368524800 3809093752884306733 5915750000000000000000 210623625 524288 169 262144 (ep746 rfl) rfl) (Enclosure.sfrac_false_div 210623625 524288) (BSN.sin_reduce3 qz936 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 89129555803966852300800) qz281) 226375608064910080 72057594037927936 Bool.false 399797 1048576 63 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q3 210623625 524288 226375608064910080 72057594037927936 63 89129555803966852300800 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 399797 1048576 89129555803966852300800 75557863725914323419136 2533214336 2147483648 378978 378608 (ep754 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz610 := (@Enclosure.Real.IsNear.recentre' qz367 Bool.false 201799 1048576 1 1048576 201799 1048576 1 1048576 (ep744 rfl rfl) rfl)

noncomputable def ep756 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz367 (Real.cos qz368)) (@HMul.hMul Real Real Real qz0 qz367 (@Neg.neg Real Real.instNeg (Real.sin qz368))) Bool.false 195617291233 1099511627776 3277419199321 26017743648063488 Bool.false 80678634803 1099511627776 3263941464411 26017743648063488 (@Enclosure.Real.IsNear.mulLit_ff qz367 (Real.cos qz368) 201799 1048576 1 1048576 969367 1048576 4031815 6203113472 195617291233 1099511627776 3277419199321 26017743648063488 qz610 (@Enclosure.Real.IsNear.recentre' (Real.cos qz368) Bool.false 969367 1048576 32254520 49624907776 969367 1048576 4031815 6203113472 (ep751 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz367 (@Neg.neg Real Real.instNeg (Real.sin qz368)) 201799 1048576 1 1048576 399797 1048576 4031815 6203113472 80678634803 1099511627776 3263941464411 26017743648063488 qz610 (@Enclosure.Real.IsNear.neg (Real.sin qz368) Bool.true 399797 1048576 4031815 6203113472 (@Enclosure.Real.IsNear.recentre' (Real.sin qz368) Bool.true 399797 1048576 32254520 49624907776 399797 1048576 4031815 6203113472 (ep755 rfl rfl) rfl)) rfl)

noncomputable def ep757 := @ep708 195617291233 1099511627776 3277419199321 26017743648063488 Bool.false 80678634803 1099511627776 3263941464411 26017743648063488 Bool.false 1121691889379147316723712 255043207603 274877906944 68108938607485 13008871824031744 Bool.true 11396058039750651543552 41458617633 1099511627776 136257545655203 26017743648063488 (ep709 (BSN.head_sum_c_succ qz14 26 27 rfl rfl) (ep742 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep743 ep756) rfl rfl

noncomputable abbrev qz937 := (@Nat.cast Real Real.instNatCast 28)

noncomputable abbrev qz370 := (@Inv.inv Real Real.instInv (Real.sqrt qz937))

noncomputable abbrev qz371 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 28 1)))

noncomputable def ep758 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz924 qz17) (Complex.mk (@HMul.hMul Real Real Real qz0 qz370 (Real.cos qz371)) (@HMul.hMul Real Real Real qz0 qz370 (@Neg.neg Real Real.instNeg (Real.sin qz371)))) Bool.true 64574385995 549755813888 1605632118815 13008871824031744 Bool.false 162778420231 1099511627776 3215280014371 26017743648063488 (BSN.cpow_neg_s_mk qz11 121891 1000 28 (@Eq.refl Real qz11) rfl)

noncomputable abbrev qz938 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 28) qz267)

noncomputable def ep759 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz937) 5548543 1048576 1 1048576 99081 99082 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz937) (Real.sqrt qz938) Bool.false 5548543 1048576 1 1048576 (BSN.sqrt_natCast_div_one 28) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz938) Bool.false 5548543 1048576 1 1048576 5548543 1048576 1 1048576 (BSN.sqrt_enclosure 28 1 2774271 2774272 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep760 := BSN.log_dyadic_bound 12 44 5 4 13275571325829120 524288 189304 344661139390464 45148078080 293399 56 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 12) (BSN.artanhQ 44) 0 4 344661139390464 13275571325829120 45148078080 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz372 := (Real.log (Enclosure.sfrac Bool.false 28 1))

noncomputable def ep761 := @Enclosure.Real.IsNear.mulLit_ff qz11 qz372 121891 1000 0 1 3751726938922231 1125899906842624 31250000023663 5915750000000000000 457301748312169658821 1125899906842624000 3809093752884306733 5915750000000000000000 qz272 (BSN.isNear_log_sfrac 28 1 3751726938922231 1125899906842624 31250000023663 5915750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz938) Bool.false 62943533227317076688896 18889465931478580854784 1000000000757216 189304000000000000000 3751726938922231 1125899906842624 31250000023663 5915750000000000000 (BSN.log_rat_reduce_isNear 28 1 4 56 32 293399 524288 24973259072661432 36028797018963968 189304 1000000000000000 rfl rfl rfl rfl (ep760 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep762 := nat_lit 498958005888022298610105599971818652012441652287746249583944337400598913229056

noncomputable def ep763 := nat_lit 194863821944649527359369663832602880487348451017198268161029253311122514176

noncomputable def ep764 := nat_lit 1496484290020177596775598060587790750276350259961204352215510953695174494658816

noncomputable def ep765 := BSN.cos_dyadic_bound_f 1932931226 2147483648 3 2 1048576 378978 ep762 ep95 ep763 ep764 ep97 ep763 651730 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1932931226) qz274 0 2 ep762 ep95 ep763 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1932931226) qz275 0 2 ep764 ep97 ep763 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz939 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 425895441) qz270)

noncomputable def ep766 := @Enclosure.Real.IsNear.cos_image qz371 qz939 Bool.false 425895441 1048576 169 262144 Bool.true 651730 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz371 Bool.false 457301748312169658821 1125899906842624000 3809093752884306733 5915750000000000000000 425895441 1048576 169 262144 (ep761 rfl) rfl) (Enclosure.sfrac_false_div 425895441 1048576) (BSN.cos_reduce2 qz939 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 136017942978620829990912) qz273) 226375608064910080 72057594037927936 Bool.false 651730 1048576 64 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q2 425895441 1048576 226375608064910080 72057594037927936 64 136017942978620829990912 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 651730 1048576 136017942978620829990912 151115727451828646838272 1932931226 2147483648 378978 378608 (ep765 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep767 := nat_lit 897968519540884417876302584218207491318005095357129490636570983918429145800960

noncomputable def ep768 := nat_lit 2351506819276310709488877312544338263073986209395597011613996624804810707312896

noncomputable def ep769 := BSN.sin_dyadic_bound_f 1932931226 2147483648 3 2 1048576 378978 ep767 ep88 ep763 ep768 ep91 ep763 821437 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1932931226) qz268 0 2 ep767 ep88 ep763 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1932931226) qz269 0 2 ep768 ep91 ep763 rfl rfl rfl rfl) rfl rfl

noncomputable def ep770 := @Enclosure.Real.IsNear.sin_image qz371 qz939 Bool.false 425895441 1048576 169 262144 Bool.true 821437 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz371 Bool.false 457301748312169658821 1125899906842624000 3809093752884306733 5915750000000000000000 425895441 1048576 169 262144 (ep761 rfl) rfl) (Enclosure.sfrac_false_div 425895441 1048576) (BSN.sin_reduce2 qz939 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 136017942978620829990912) qz273) 226375608064910080 72057594037927936 Bool.false 821437 1048576 64 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q2 425895441 1048576 226375608064910080 72057594037927936 64 136017942978620829990912 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 821437 1048576 136017942978620829990912 151115727451828646838272 1932931226 2147483648 378978 378608 (ep769 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz611 := (@Enclosure.Real.IsNear.recentre' qz370 Bool.false 198163 1048576 1 1048576 198163 1048576 1 1048576 (ep759 rfl rfl) rfl)

noncomputable def ep771 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz370 (Real.cos qz371)) (@HMul.hMul Real Real Real qz0 qz370 (@Neg.neg Real Real.instNeg (Real.sin qz371))) Bool.true 64574385995 549755813888 1605632118815 13008871824031744 Bool.false 162778420231 1099511627776 3215280014371 26017743648063488 (@Enclosure.Real.IsNear.mulLit_ft qz370 (Real.cos qz371) 198163 1048576 1 1048576 325865 524288 4031815 6203113472 64574385995 549755813888 1605632118815 13008871824031744 qz611 (@Enclosure.Real.IsNear.recentre' (Real.cos qz371) Bool.true 651730 1048576 32254520 49624907776 325865 524288 4031815 6203113472 (ep766 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz370 (@Neg.neg Real Real.instNeg (Real.sin qz371)) 198163 1048576 1 1048576 821437 1048576 4031815 6203113472 162778420231 1099511627776 3215280014371 26017743648063488 qz611 (@Enclosure.Real.IsNear.neg (Real.sin qz371) Bool.true 821437 1048576 4031815 6203113472 (@Enclosure.Real.IsNear.recentre' (Real.sin qz371) Bool.true 821437 1048576 32254520 49624907776 821437 1048576 4031815 6203113472 (ep770 rfl rfl) rfl)) rfl)

noncomputable def ep772 := @ep706 64574385995 549755813888 1605632118815 13008871824031744 Bool.false 162778420231 1099511627776 3215280014371 26017743648063488 Bool.false 122461414107893867741184 445512029211 549755813888 17428642681575 3252217956007936 Bool.false 133392533635989973762048 60659901299 549755813888 69736412834787 13008871824031744 (ep707 (BSN.head_sum_c_succ qz14 27 28 rfl rfl) (ep757 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep758 ep771) rfl rfl

noncomputable abbrev qz940 := (@Nat.cast Real Real.instNatCast 29)

noncomputable abbrev qz373 := (@Inv.inv Real Real.instInv (Real.sqrt qz940))

noncomputable abbrev qz374 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 29 1)))

noncomputable def ep773 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz923 qz17) (Complex.mk (@HMul.hMul Real Real Real qz0 qz373 (Real.cos qz374)) (@HMul.hMul Real Real Real qz0 qz373 (@Neg.neg Real Real.instNeg (Real.sin qz374)))) Bool.true 91561029165 1099511627776 3155970199021 26017743648063488 Bool.true 91245980295 549755813888 1583510350853 13008871824031744 (BSN.cpow_neg_s_mk qz11 121891 1000 29 (@Eq.refl Real qz11) rfl)

noncomputable abbrev qz941 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 29) qz267)

noncomputable def ep774 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz940) 5646755 1048576 1 1048576 97357 97358 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz940) (Real.sqrt qz941) Bool.false 5646755 1048576 1 1048576 (BSN.sqrt_natCast_div_one 29) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz941) Bool.false 5646755 1048576 1 1048576 5646755 1048576 1 1048576 (BSN.sqrt_enclosure 29 1 2823377 2823378 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep775 := BSN.log_dyadic_bound 13 45 6 5 353956287581982421875 524288 189304 10371179520995104305 130276274797305 311797 58 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 13) (BSN.artanhQ 45) 0 5 10371179520995104305 353956287581982421875 130276274797305 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz375 := (Real.log (Enclosure.sfrac Bool.false 29 1))

noncomputable def ep776 := @Enclosure.Real.IsNear.mulLit_ff qz11 qz375 121891 1000 0 1 3791236343078135 1125899906842624 31250000023663 5915750000000000000 92423517818827390657 225179981368524800 3809093752884306733 5915750000000000000000 qz272 (BSN.isNear_log_sfrac 29 1 3791236343078135 1125899906842624 31250000023663 5915750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz941) Bool.false 63606391034871975772160 18889465931478580854784 1000000000757216 189304000000000000000 3791236343078135 1125899906842624 31250000023663 5915750000000000000 (BSN.log_rat_reduce_isNear 29 1 4 58 32 311797 524288 24973259072661432 36028797018963968 189304 1000000000000000 rfl rfl rfl rfl (ep775 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep777 := nat_lit 994570270882900531417883008046100625

noncomputable def ep778 := BSN.sin_dyadic_bound_f 998639795 2147483648 2 1 1048576 378978 ep777 ep106 ep777 ep777 ep107 ep777 470231 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 998639795) qz268 0 1 ep777 ep106 ep777 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 998639795) qz269 0 1 ep777 ep107 ep777 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz942 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 215190271) qz279)

noncomputable def ep779 := @Enclosure.Real.IsNear.cos_image qz374 qz942 Bool.false 215190271 524288 677 1048576 Bool.true 470231 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz374 Bool.false 92423517818827390657 225179981368524800 3809093752884306733 5915750000000000000000 215190271 524288 677 1048576 (ep776 rfl) rfl) (Enclosure.sfrac_false_div 215190271 524288) (BSN.cos_reduce1 qz942 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 35136514163008310607872) qz281) 226375608064910080 72057594037927936 Bool.false 470231 1048576 65 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q1 215190271 524288 226375608064910080 72057594037927936 65 35136514163008310607872 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 470231 1048576 35136514163008310607872 75557863725914323419136 998639795 2147483648 378978 378608 (ep778 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep780 := BSN.cos_dyadic_bound_f 998639795 2147483648 2 1 1048576 378978 ep777 ep110 ep777 ep777 ep111 ep777 937226 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 998639795) qz274 0 1 ep777 ep110 ep777 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 998639795) qz275 0 1 ep777 ep111 ep777 rfl rfl rfl rfl) rfl rfl

noncomputable def ep781 := @Enclosure.Real.IsNear.sin_image qz374 qz942 Bool.false 215190271 524288 677 1048576 Bool.false 937226 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz374 Bool.false 92423517818827390657 225179981368524800 3809093752884306733 5915750000000000000000 215190271 524288 677 1048576 (ep776 rfl) rfl) (Enclosure.sfrac_false_div 215190271 524288) (BSN.sin_reduce1 qz942 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 35136514163008310607872) qz281) 226375608064910080 72057594037927936 Bool.false 937226 1048576 65 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q1 215190271 524288 226375608064910080 72057594037927936 65 35136514163008310607872 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 937226 1048576 35136514163008310607872 75557863725914323419136 998639795 2147483648 378978 378608 (ep780 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz612 := (@Enclosure.Real.IsNear.recentre' qz373 Bool.false 194715 1048576 1 1048576 194715 1048576 1 1048576 (ep774 rfl rfl) rfl)

noncomputable def ep782 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz373 (Real.cos qz374)) (@HMul.hMul Real Real Real qz0 qz373 (@Neg.neg Real Real.instNeg (Real.sin qz374))) Bool.true 91561029165 1099511627776 3155970199021 26017743648063488 Bool.true 91245980295 549755813888 1583510350853 13008871824031744 (@Enclosure.Real.IsNear.mulLit_ft qz373 (Real.cos qz374) 194715 1048576 1 1048576 470231 1048576 16150923 24812453888 91561029165 1099511627776 3155970199021 26017743648063488 qz612 (@Enclosure.Real.IsNear.recentre' (Real.cos qz374) Bool.true 470231 1048576 129207384 198499631104 470231 1048576 16150923 24812453888 (ep779 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz373 (@Neg.neg Real Real.instNeg (Real.sin qz374)) 194715 1048576 1 1048576 468613 524288 16150923 24812453888 91245980295 549755813888 1583510350853 13008871824031744 qz612 (@Enclosure.Real.IsNear.neg (Real.sin qz374) Bool.false 468613 524288 16150923 24812453888 (@Enclosure.Real.IsNear.recentre' (Real.sin qz374) Bool.false 937226 1048576 129207384 198499631104 468613 524288 16150923 24812453888 (ep781 rfl rfl) rfl)) rfl)

noncomputable def ep783 := @ep704 91561029165 1099511627776 3155970199021 26017743648063488 Bool.true 91245980295 549755813888 1583510350853 13008871824031744 Bool.false 439509448322547990921216 799463029257 1099511627776 142585111651621 26017743648063488 Bool.true 16814874752088641896448 7646519749 137438953472 8914990398205 1626108978003968 (ep705 (BSN.head_sum_c_succ qz14 28 29 rfl rfl) (ep772 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep773 ep782) rfl rfl

noncomputable abbrev qz943 := (@Nat.cast Real Real.instNatCast 30)

noncomputable abbrev qz376 := (@Inv.inv Real Real.instInv (Real.sqrt qz943))

noncomputable abbrev qz377 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 30 1)))

noncomputable def ep784 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz922 qz17) (Complex.mk (@HMul.hMul Real Real Real qz0 qz376 (Real.cos qz377)) (@HMul.hMul Real Real Real qz0 qz376 (@Neg.neg Real Real.instNeg (Real.sin qz377)))) Bool.false 49853480187 274877906944 778028849027 6504435912015872 Bool.false 1440991461 68719476736 48286202279 406527244500992 (BSN.cpow_neg_s_mk qz11 121891 1000 30 (@Eq.refl Real qz11) rfl)

noncomputable abbrev qz944 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 30) qz267)

noncomputable def ep785 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz943) 5743287 1048576 1 1048576 95721 95722 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz943) (Real.sqrt qz944) Bool.false 5743287 1048576 1 1048576 (BSN.sqrt_natCast_div_one 30) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz944) Bool.false 5743287 1048576 1 1048576 5743287 1048576 1 1048576 (BSN.sqrt_enclosure 30 1 2871643 2871644 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep786 := BSN.log_dyadic_bound 14 46 6 5 440963670083462507520 524288 189304 14425761949190022144 273345648952320 329571 60 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 14) (BSN.artanhQ 46) 0 5 14425761949190022144 440963670083462507520 273345648952320 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz378 := (Real.log (Enclosure.sfrac Bool.false 30 1))

noncomputable def ep787 := @Enclosure.Real.IsNear.mulLit_ff qz11 qz378 121891 1000 0 1 3829405717437687 1125899906842624 31250000023663 5915750000000000000 466770092304197106117 1125899906842624000 3809093752884306733 5915750000000000000000 qz272 (BSN.isNear_log_sfrac 30 1 3829405717437687 1125899906842624 31250000023663 5915750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz944) Bool.false 64246766873087041339392 18889465931478580854784 1000000000757216 189304000000000000000 3829405717437687 1125899906842624 31250000023663 5915750000000000000 (BSN.log_rat_reduce_isNear 30 1 4 60 32 329571 524288 24973259072661432 36028797018963968 189304 1000000000000000 rfl rfl rfl rfl (ep786 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep788 := nat_lit 6150910033235269596939560384671879760175008360148675171993342354015460906254465

noncomputable def ep789 := nat_lit 9119844938666637323699873247203690958486435556197280863178587331252464402561

noncomputable def ep790 := nat_lit 16094760814286912483936667879359450538906520047584115567156464642932750764490881

noncomputable def ep791 := BSN.sin_dyadic_bound_f 3126068079 2147483648 3 2 1048576 378978 ep788 ep88 ep789 ep790 ep91 ep789 1041636 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3126068079) qz268 0 2 ep788 ep88 ep789 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3126068079) qz269 0 2 ep790 ep91 ep789 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz613 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 108678381) (@Nat.cast Real Real.instNatCast 262144))

noncomputable def ep792 := @Enclosure.Real.IsNear.cos_image qz377 qz613 Bool.false 108678381 262144 169 262144 Bool.false 1041636 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz377 Bool.false 466770092304197106117 1125899906842624000 3809093752884306733 5915750000000000000000 108678381 262144 169 262144 (ep787 rfl) rfl) (Enclosure.sfrac_false_div 108678381 262144) (BSN.cos_reduce3 qz613 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 54994371245193111273472) qz578) 226375608064910080 72057594037927936 Bool.false 1041636 1048576 65 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q3 108678381 262144 226375608064910080 72057594037927936 65 54994371245193111273472 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1041636 1048576 54994371245193111273472 37778931862957161709568 3126068079 2147483648 378978 378608 (ep791 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep793 := nat_lit 3421225505103446059332511268483134840523220838107573887046602902155812709875841

noncomputable def ep794 := nat_lit 10245436825433004903350134058954997139652689643210327099413451531804933200822401

noncomputable def ep795 := BSN.cos_dyadic_bound_f 3126068079 2147483648 3 2 1048576 378978 ep793 ep95 ep789 ep794 ep97 ep789 120432 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3126068079) qz274 0 2 ep793 ep95 ep789 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3126068079) qz275 0 2 ep794 ep97 ep789 rfl rfl rfl rfl) rfl rfl

noncomputable def ep796 := @Enclosure.Real.IsNear.sin_image qz377 qz613 Bool.false 108678381 262144 169 262144 Bool.true 120432 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz377 Bool.false 466770092304197106117 1125899906842624000 3809093752884306733 5915750000000000000000 108678381 262144 169 262144 (ep787 rfl) rfl) (Enclosure.sfrac_false_div 108678381 262144) (BSN.sin_reduce3 qz613 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 54994371245193111273472) qz578) 226375608064910080 72057594037927936 Bool.false 120432 1048576 65 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q3 108678381 262144 226375608064910080 72057594037927936 65 54994371245193111273472 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 120432 1048576 54994371245193111273472 37778931862957161709568 3126068079 2147483648 378978 378608 (ep795 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz614 := (@Enclosure.Real.IsNear.recentre' qz376 Bool.false 191443 1048576 1 1048576 191443 1048576 1 1048576 (ep785 rfl rfl) rfl)

noncomputable def ep797 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz376 (Real.cos qz377)) (@HMul.hMul Real Real Real qz0 qz376 (@Neg.neg Real Real.instNeg (Real.sin qz377))) Bool.false 49853480187 274877906944 778028849027 6504435912015872 Bool.false 1440991461 68719476736 48286202279 406527244500992 (@Enclosure.Real.IsNear.mulLit_ff qz376 (Real.cos qz377) 191443 1048576 1 1048576 260409 262144 4031815 6203113472 49853480187 274877906944 778028849027 6504435912015872 qz614 (@Enclosure.Real.IsNear.recentre' (Real.cos qz377) Bool.false 1041636 1048576 32254520 49624907776 260409 262144 4031815 6203113472 (ep792 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz376 (@Neg.neg Real Real.instNeg (Real.sin qz377)) 191443 1048576 1 1048576 7527 65536 4031815 6203113472 1440991461 68719476736 48286202279 406527244500992 qz614 (@Enclosure.Real.IsNear.neg (Real.sin qz377) Bool.true 7527 65536 4031815 6203113472 (@Enclosure.Real.IsNear.recentre' (Real.sin qz377) Bool.true 120432 1048576 32254520 49624907776 7527 65536 4031815 6203113472 (ep796 rfl rfl) rfl)) rfl)

noncomputable def ep798 := @ep702 49853480187 274877906944 778028849027 6504435912015872 Bool.false 1440991461 68719476736 48286202279 406527244500992 Bool.false 274569205311980930334720 998876950005 1099511627776 145697227047729 26017743648063488 Bool.true 327416477640841756672 4764536827 137438953472 9108135207321 1626108978003968 (ep703 (BSN.head_sum_c_succ qz14 29 30 rfl rfl) (ep783 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep784 ep797) rfl rfl

noncomputable def ep799 := @Enclosure.Complex.IsNear.mul qz45 (@HAdd.hAdd Complex Complex Complex qz15 qz46 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz49 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1))))) Bool.true ep693 ep480 ep694 ep482 Bool.false

noncomputable def ep800 := nat_lit 5197997353998516480354336117765823

noncomputable def ep801 := nat_lit 77867364970555749067768463360000000

noncomputable def ep802 := nat_lit 108937114142905666604177599058938881

noncomputable def ep803 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re qz45) (Complex.re (@HAdd.hAdd Complex Complex Complex qz15 qz46 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz49 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 (Complex.im qz45) (Complex.im (@HAdd.hAdd Complex Complex Complex qz15 qz46 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz49 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1))))))) ep800 ep801 ep802

noncomputable def ep804 := nat_lit 1842575457298260690190605148487680000000

noncomputable def ep805 := nat_lit 6695588848592084716081074517178786549

noncomputable def ep806 := nat_lit 1650797583461606800907233374942046471

noncomputable def ep807 := nat_lit 89156876966044872105997023313920000000000

noncomputable def ep808 := nat_lit 2342762467425137990592273258349497161016330592394322182476021104640000000

noncomputable def ep809 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re qz45) (Complex.re (@HAdd.hAdd Complex Complex Complex qz15 qz46 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz49 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))))) 145798096943 1099511627776 3055565989521 26017743648063488 35652024703934797506161

noncomputable abbrev qz945 := (@Nat.cast Real Real.instNatCast 31)

noncomputable abbrev qz379 := (@Inv.inv Real Real.instInv (Real.sqrt qz945))

noncomputable abbrev qz380 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 31 1)))

noncomputable abbrev qz946 := (@Neg.neg Real Real.instNeg (Real.sin qz380))

noncomputable def ep810 := @Enclosure.Complex.IsNear.of_eq qz45 (Complex.mk (@HMul.hMul Real Real Real qz0 qz379 (Real.cos qz380)) (@HMul.hMul Real Real Real qz0 qz379 qz946)) Bool.true 145798096943 1099511627776 3055565989521 26017743648063488 Bool.false 133192106999 1099511627776 3053982082953 26017743648063488 (BSN.cpow_neg_s_mk qz11 121891 1000 31 (@Eq.refl Real qz11) rfl)

noncomputable abbrev qz947 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 31) qz267)

noncomputable def ep811 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz945) 5838225 1048576 1 1048576 94164 94165 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz945) (Real.sqrt qz947) Bool.false 5838225 1048576 1 1048576 (BSN.sqrt_natCast_div_one 31) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz947) Bool.false 5838225 1048576 1 1048576 5838225 1048576 1 1048576 (BSN.sqrt_enclosure 31 1 2919112 2919113 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep812 := BSN.log_dyadic_bound 15 47 6 5 546767979591453359355 524288 189304 19788004106328479625 544934619140625 346763 62 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 15) (BSN.artanhQ 47) 0 5 19788004106328479625 546767979591453359355 544934619140625 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz381 := (Real.log (Enclosure.sfrac Bool.false 31 1))

noncomputable def ep813 := @Enclosure.Real.IsNear.mulLit_ff qz11 qz381 121891 1000 0 1 3866325256314103 1125899906842624 31250000023663 5915750000000000000 471270251817382328773 1125899906842624000 3809093752884306733 5915750000000000000000 qz272 (BSN.isNear_log_sfrac 31 1 3866325256314103 1125899906842624 31250000023663 5915750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz947) Bool.false 64866173951437069877248 18889465931478580854784 1000000000757216 189304000000000000000 3866325256314103 1125899906842624 31250000023663 5915750000000000000 (BSN.log_rat_reduce_isNear 31 1 4 62 32 346763 524288 24973259072661432 36028797018963968 189304 1000000000000000 rfl rfl rfl rfl (ep812 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep814 := nat_lit 228205541079259483850692834232571074102045601213980840977663147152238006735681

noncomputable def ep815 := nat_lit 40779289599725115262156894337569722948699637278969524087749479429258580801

noncomputable def ep816 := nat_lit 684535064658579001321554188909038082860239404367384583884813942497855503045441

noncomputable def ep817 := BSN.cos_dyadic_bound_f 1589662601 2147483648 3 2 1048576 378978 ep814 ep95 ep815 ep816 ep97 ep815 774167 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1589662601) qz274 0 2 ep814 ep95 ep815 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1589662601) qz275 0 2 ep816 ep97 ep815 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz615 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 27431539) (@Nat.cast Real Real.instNatCast 65536))

noncomputable def ep818 := @Enclosure.Real.IsNear.cos_image qz380 qz615 Bool.false 27431539 65536 169 262144 Bool.true 774167 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz380 Bool.false 471270251817382328773 1125899906842624000 3809093752884306733 5915750000000000000000 27431539 65536 169 262144 (ep813 rfl) rfl) (Enclosure.sfrac_false_div 27431539 65536) (BSN.cos_reduce2 qz615 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6991410057417408380928) qz864) 226375608064910080 72057594037927936 Bool.false 774167 1048576 66 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q2 27431539 65536 226375608064910080 72057594037927936 66 6991410057417408380928 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 774167 1048576 6991410057417408380928 9444732965739290427392 1589662601 2147483648 378978 378608 (ep817 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep819 := nat_lit 6385866393820427814146705444495210401

noncomputable def ep820 := BSN.sin_dyadic_bound_f 1589662601 2147483648 2 1 1048576 378978 ep819 ep106 ep819 ep819 ep107 ep819 707231 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1589662601) qz268 0 1 ep819 ep106 ep819 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1589662601) qz269 0 1 ep819 ep107 ep819 rfl rfl rfl rfl) rfl rfl

noncomputable def ep821 := @Enclosure.Real.IsNear.sin_image qz380 qz615 Bool.false 27431539 65536 169 262144 Bool.true 707231 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz380 Bool.false 471270251817382328773 1125899906842624000 3809093752884306733 5915750000000000000000 27431539 65536 169 262144 (ep813 rfl) rfl) (Enclosure.sfrac_false_div 27431539 65536) (BSN.sin_reduce2 qz615 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6991410057417408380928) qz864) 226375608064910080 72057594037927936 Bool.false 707231 1048576 66 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q2 27431539 65536 226375608064910080 72057594037927936 66 6991410057417408380928 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 707231 1048576 6991410057417408380928 9444732965739290427392 1589662601 2147483648 378978 378608 (ep820 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz616 := (@Enclosure.Real.IsNear.recentre' qz379 Bool.false 188329 1048576 1 1048576 188329 1048576 1 1048576 (ep811 rfl rfl) rfl)

noncomputable def ep822 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz379 (Real.cos qz380)) (@HMul.hMul Real Real Real qz0 qz379 qz946) Bool.true 145798096943 1099511627776 3055565989521 26017743648063488 Bool.false 133192106999 1099511627776 3053982082953 26017743648063488 (@Enclosure.Real.IsNear.mulLit_ft qz379 (Real.cos qz380) 188329 1048576 1 1048576 774167 1048576 4031815 6203113472 145798096943 1099511627776 3055565989521 26017743648063488 qz616 (@Enclosure.Real.IsNear.recentre' (Real.cos qz380) Bool.true 774167 1048576 32254520 49624907776 774167 1048576 4031815 6203113472 (ep818 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz379 qz946 188329 1048576 1 1048576 707231 1048576 4031815 6203113472 133192106999 1099511627776 3053982082953 26017743648063488 qz616 (@Enclosure.Real.IsNear.neg (Real.sin qz380) Bool.true 707231 1048576 4031815 6203113472 (@Enclosure.Real.IsNear.recentre' (Real.sin qz380) Bool.true 707231 1048576 32254520 49624907776 707231 1048576 4031815 6203113472 (ep821 rfl rfl) rfl)) rfl)

noncomputable def ep823 := @ep809 70819955881739360000000 0 1 ep800 ep801 ep802 ep804 (@Enclosure.Complex.IsNear.re_isNear qz45 Bool.true 145798096943 1099511627776 3055565989521 26017743648063488 Bool.false 133192106999 1099511627776 3053982082953 26017743648063488 (ep810 ep822))

noncomputable def ep824 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz15 qz46 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz49 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1))))) Bool.false 35652024703934797506161 70819955881739360000000 0 1 Bool.false

noncomputable def ep825 := nat_lit 50270162395151199751470451

noncomputable def ep826 := nat_lit 318689801467827120000000000

noncomputable def ep827 := @Enclosure.Complex.IsNear.addLitP qz46 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz49 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) Bool.false 14826665881 29715331762 0 1 Bool.true 3778621000

noncomputable def ep828 := @ep827 14857665881 0 1 Bool.false 21263665881 4766560000000 0 1 Bool.false 8838519465900971 21449520000000000 0 1 Bool.false 71304049407869595012322 35652024703934797506161 70819955881739360000000 0 1 Bool.false ep825 ep825 ep826 0 1

noncomputable abbrev qz50 := (@HDiv.hDiv Complex Complex Complex qz352 (@Nat.cast Complex Complex.instNatCast 31) (@HSub.hSub Complex Complex Complex qz597 qz261 (1 : Complex)))

noncomputable def ep829 := @Enclosure.Complex.IsNear.addLitP qz50 qz26 Bool.true 62000000 59430663524 0 1 Bool.true 15114484000 59430663524 0 1

noncomputable def ep830 := @Enclosure.Complex.IsNear.of_eq qz50 (Complex.mk (Enclosure.sfrac Bool.true 62000000 59430663524) (Enclosure.sfrac Bool.true 15114484000 59430663524)) Bool.true 62000000 59430663524 0 1 Bool.true 15114484000 59430663524 0 1

noncomputable def ep831 := @ep829 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 59306663524 14826665881 29715331762 0 1 Bool.true 15114484000 3778621000 14857665881 0 1 (ep830 (BSN.N_div_s_sub_one_mk qz11 121891 1000 31 (@Eq.refl Real qz11) rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 62000000 59430663524) (Enclosure.sfrac Bool.true 15114484000 59430663524) Bool.true 62000000 59430663524 0 1 Bool.true 15114484000 59430663524 0 1 (Enclosure.Real.IsNear.const Bool.true 62000000 59430663524) (Enclosure.Real.IsNear.const Bool.true 15114484000 59430663524))) qz357 rfl

noncomputable abbrev qz51 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)))

noncomputable abbrev qz382 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz49 3))

noncomputable def ep832 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz49 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz15 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz49 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3))) qz382)) Bool.false 21263665881 4766560000000 0 1

noncomputable def ep833 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz49 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3))) qz382) Bool.false 1 744 0 1 Bool.false

noncomputable def ep834 := @ep833 121891 372000 0 1 Bool.false 44570997643 14299680000000 0 1 Bool.false 1810284405900971 21449520000000000 0 1 Bool.false 47460502246392 21263665881 4766560000000 0 1 Bool.false 3287929241315161212000 8838519465900971 21449520000000000 0

noncomputable abbrev qz52 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)))

noncomputable abbrev qz383 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz49 1))

noncomputable def ep835 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz49 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz15 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz49 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1))) qz383)) Bool.false 1 744 0 1

noncomputable def ep836 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz49 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1))) qz383) Bool.false 0 1 0 1 Bool.false

noncomputable def ep837 := @ep836 0 1 0 1 Bool.false 1 744 0 1 Bool.false 121891 372000 0 1 Bool.false 1 1 744 0 1 Bool.false 121891 121891 372000 0

noncomputable def ep838 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz49 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (Complex.mk qz264 qz264) Bool.false 0 1 0 1 Bool.false

noncomputable def ep839 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1))) qz383 Bool.false 1 744 0 1 Bool.false 121891 372000 0 1

noncomputable def ep840 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz383)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz383)) 1 744 0 1 0 1 0

noncomputable def ep841 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz383) 1 24 0 1 1 31 0 1 1

noncomputable def ep842 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep843 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep844 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz264) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 1 1 6 2 Bool.false BSN.bern_real_1 EMRow40.d10 rfl) qz905

noncomputable def ep845 := @ep843 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep844) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 121891 1000 0 1 ep433)

noncomputable def ep846 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 121891 1000 0 1 0 1 0

noncomputable def ep847 := @ep846 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep844) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 121891 1000 0 1 ep433)

noncomputable def ep848 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1)))) 121891 12000 0 1 0 1 0 1 121891

noncomputable def ep849 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 121891 1000 0 1 121891 12000 0

noncomputable def ep850 := @ep849 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep844) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 121891 1000 0 1 ep433)

noncomputable def ep851 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep852 := @ep851 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep844) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 121891 1000 0 1 ep433)

noncomputable def ep853 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 121891 12000 0 1 (@ep842 1 24 0 1 (ep845 rfl) (ep847 rfl) rfl rfl) (@ep848 121891 12000 0 1 (ep850 rfl) (ep852 rfl) rfl rfl)

noncomputable def ep854 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 121891 12000 0 1 ep853

noncomputable abbrev qz384 := (@Enclosure.Complex.IsNear.of_eq (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz49 1)) (Complex.mk (Enclosure.sfrac Bool.false 1 31) qz828) Bool.false 1 31 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 31 1 31 EMRow40.d11 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 31) qz828 Bool.false 1 31 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 31) qz830))

noncomputable def ep855 := @ep841 744 0 1 ep854 (@Enclosure.Complex.IsNear.re_isNear qz383 Bool.false 1 31 0 1 Bool.false 0 1 0 1 qz384)

noncomputable def ep856 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz383) 121891 12000 0 1 0 1 0 1 0

noncomputable def ep857 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 121891 12000 0 1 ep853

noncomputable def ep858 := @ep856 1 0 1 ep857 (@Enclosure.Complex.IsNear.im_isNear qz383 Bool.false 1 31 0 1 Bool.false 0 1 0 1 qz384)

noncomputable def ep859 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz383)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz383)) 0 1 0 1 121891 372000 0

noncomputable def ep860 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz383) 1 24 0 1 0 1 0 1 0

noncomputable def ep861 := @ep860 1 0 1 ep854 (@Enclosure.Complex.IsNear.im_isNear qz383 Bool.false 1 31 0 1 Bool.false 0 1 0 1 qz384)

noncomputable def ep862 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz383) 121891 12000 0 1 1 31 0 1 121891

noncomputable def ep863 := @ep862 372000 0 1 ep857 (@Enclosure.Complex.IsNear.re_isNear qz383 Bool.false 1 31 0 1 Bool.false 0 1 0 1 qz384)

noncomputable def ep864 := @ep837 1 (@ep838 0 1 0 1 (BSN.bern_sum_base qz14 31) qz360) (ep839 (@ep840 1 1 1 744 0 1 (ep855 rfl) (ep858 rfl) rfl rfl) (@ep859 1 121891 121891 372000 0 1 (ep861 rfl) (ep863 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep865 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3))) qz382 Bool.false 44570997643 14299680000000 0 1 Bool.false 1810284405900971 21449520000000000 0 1

noncomputable def ep866 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.re qz382)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.im qz382)) 44570997643 14299680000000 0 1 0 1 0

noncomputable def ep867 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.re qz382) 44570997643 480000000 0 1 1 29791 0 1 44570997643

noncomputable def ep868 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3)))) 44570997643 480000000 0 1 0 1 0 1 44570997643

noncomputable def ep869 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 133712992929 2000000 0 1 44570997643 480000000 0

noncomputable def ep870 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (Complex.mk (Enclosure.sfrac Bool.true 1 720) qz264) Bool.true 1 720 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 2 1 30 24 Bool.true BSN.bern_real_2 EMRow40.d12 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 1 720) qz264 Bool.true 1 720 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.true 1 720) qz276)

noncomputable def ep871 := @ep869 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep870) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 133712992929 2000000 0 1 Bool.true 1810284405900971 1000000000 0 1 EMRow40.d13)

noncomputable def ep872 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 1810284405900971 1000000000 0 1 0 1 0

noncomputable def ep873 := @ep872 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep870) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 133712992929 2000000 0 1 Bool.true 1810284405900971 1000000000 0 1 EMRow40.d13)

noncomputable def ep874 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3)))) 1810284405900971 720000000000 0 1 0 1 0 1 1810284405900971

noncomputable def ep875 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 1810284405900971 1000000000 0 1 1810284405900971 720000000000 0

noncomputable def ep876 := @ep875 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep870) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 133712992929 2000000 0 1 Bool.true 1810284405900971 1000000000 0 1 EMRow40.d13)

noncomputable def ep877 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 133712992929 2000000 0 1 0 1 0

noncomputable def ep878 := @ep877 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep870) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 133712992929 2000000 0 1 Bool.true 1810284405900971 1000000000 0 1 EMRow40.d13)

noncomputable def ep879 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 44570997643 480000000 0 1 Bool.false 1810284405900971 720000000000 0 1 (@ep868 44570997643 480000000 0 1 (ep871 rfl) (ep873 rfl) rfl rfl) (@ep874 1810284405900971 720000000000 0 1 (ep876 rfl) (ep878 rfl) rfl rfl)

noncomputable def ep880 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 44570997643 480000000 0 1 Bool.false 1810284405900971 720000000000 0 1 ep879

noncomputable abbrev qz385 := (@Enclosure.Complex.IsNear.of_eq (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz49 3)) (Complex.mk (Enclosure.sfrac Bool.false 1 29791) qz828) Bool.false 1 29791 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 31 3 29791 EMRow40.d14 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 29791) qz828 Bool.false 1 29791 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 29791) qz830))

noncomputable def ep881 := @ep867 14299680000000 0 1 ep880 (@Enclosure.Complex.IsNear.re_isNear qz382 Bool.false 1 29791 0 1 Bool.false 0 1 0 1 qz385)

noncomputable def ep882 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.im qz382) 1810284405900971 720000000000 0 1 0 1 0 1 0

noncomputable def ep883 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 44570997643 480000000 0 1 Bool.false 1810284405900971 720000000000 0 1 ep879

noncomputable def ep884 := @ep882 1 0 1 ep883 (@Enclosure.Complex.IsNear.im_isNear qz382 Bool.false 1 29791 0 1 Bool.false 0 1 0 1 qz385)

noncomputable def ep885 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.im qz382)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.re qz382)) 0 1 0 1 1810284405900971 21449520000000000 0

noncomputable def ep886 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.im qz382) 44570997643 480000000 0 1 0 1 0 1 0

noncomputable def ep887 := @ep886 1 0 1 ep880 (@Enclosure.Complex.IsNear.im_isNear qz382 Bool.false 1 29791 0 1 Bool.false 0 1 0 1 qz385)

noncomputable def ep888 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.re qz382) 1810284405900971 720000000000 0 1 1 29791 0 1 1810284405900971

noncomputable def ep889 := @ep888 21449520000000000 0 1 ep883 (@Enclosure.Complex.IsNear.re_isNear qz382 Bool.false 1 29791 0 1 Bool.false 0 1 0 1 qz385)

noncomputable def ep890 := @ep834 1 (@ep835 Bool.false 121891 372000 0 1 (BSN.bern_sum_succ qz14 31 0 1 1 rfl rfl) (ep864 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep865 (@ep866 1 44570997643 44570997643 14299680000000 0 1 (ep881 rfl) (ep884 rfl) rfl rfl) (@ep885 1 1810284405900971 1810284405900971 21449520000000000 0 1 (ep887 rfl) (ep889 rfl) rfl rfl)) rfl rfl rfl rfl

noncomputable def ep891 := ep828 (ep831 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep832 Bool.false 8838519465900971 21449520000000000 0 1 (BSN.bern_sum_succ qz14 31 1 2 3 rfl rfl) (ep890 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep892 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz45) (Complex.im (@HAdd.hAdd Complex Complex Complex qz15 qz46 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz49 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))))) 133192106999 1099511627776 3053982082953 26017743648063488 ep825

noncomputable def ep893 := @ep892 ep826 0 1 ep805 ep480 ep806 ep807 (@Enclosure.Complex.IsNear.im_isNear qz45 Bool.true 145798096943 1099511627776 3055565989521 26017743648063488 Bool.false 133192106999 1099511627776 3053982082953 26017743648063488 (ep810 ep822))

noncomputable def ep894 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz15 qz46 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz49 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1))))) Bool.false 35652024703934797506161 70819955881739360000000 0 1 Bool.false

noncomputable def ep895 := nat_lit 7329294010228607694507646321697931293

noncomputable def ep896 := nat_lit 17067088722480171009001348653845238219

noncomputable def ep897 := @Enclosure.Real.IsNear.addLit_tf_p (@HMul.hMul Real Real Real qz0 (Complex.re qz45) (Complex.im (@HAdd.hAdd Complex Complex Complex qz15 qz46 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz49 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 (Complex.im qz45) (Complex.re (@HAdd.hAdd Complex Complex Complex qz15 qz46 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz49 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1))))))) ep895 ep480 ep896

noncomputable def ep898 := nat_lit 4748568289097474845759994273720839

noncomputable def ep899 := nat_lit 3512278860219826000740769052599143

noncomputable def ep900 := nat_lit 59437917977363248070664682209280000000

noncomputable def ep901 := nat_lit 1093200438575443354743636637415371006343188998486443212062347755520000000

noncomputable def ep902 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re qz45) (Complex.im (@HAdd.hAdd Complex Complex Complex qz15 qz46 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz49 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))))) 145798096943 1099511627776 3055565989521 26017743648063488 ep825

noncomputable def ep903 := @ep902 ep826 0 1 ep895 ep480 ep896 ep690 (@Enclosure.Complex.IsNear.re_isNear qz45 Bool.true 145798096943 1099511627776 3055565989521 26017743648063488 Bool.false 133192106999 1099511627776 3053982082953 26017743648063488 (ep810 ep822))

noncomputable def ep904 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz45) (Complex.re (@HAdd.hAdd Complex Complex Complex qz15 qz46 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz49 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))))) 133192106999 1099511627776 3053982082953 26017743648063488 35652024703934797506161

noncomputable def ep905 := @ep904 70819955881739360000000 0 1 ep898 ep801 ep899 ep900 (@Enclosure.Complex.IsNear.im_isNear qz45 Bool.true 145798096943 1099511627776 3055565989521 26017743648063488 Bool.false 133192106999 1099511627776 3053982082953 26017743648063488 (ep810 ep822))

noncomputable abbrev qz948 := (ep891 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep906 := @ep799 ep695 ep480 ep696 ep690 (@ep803 ep804 ep805 ep480 ep806 ep807 ep808 ep693 ep480 ep694 ep482 (ep823 (@ep824 ep825 ep826 0 1 qz948) rfl) (ep893 (@ep894 ep825 ep826 0 1 qz948) rfl) rfl rfl) (@ep897 ep690 ep898 ep801 ep899 ep900 ep901 ep695 ep480 ep696 ep690 (ep903 (@ep894 ep825 ep826 0 1 qz948) rfl) (ep905 (@ep824 ep825 ep826 0 1 qz948) rfl) rfl rfl)

noncomputable def ep907 := @ep699 ep689 ep690 (@ep700 1626108978003968 (BSN.head_sum_c_eq qz14 31) (ep701 (BSN.head_sum_c_succ qz14 30 31 rfl rfl) (ep798 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep906 rfl rfl rfl

noncomputable def ep908 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz14 2 31) Bool.false ep479 ep480 ep481 ep482 Bool.false ep688 ep480 ep689 ep690 (@ep691 ep482 Bool.false ep688 ep480 ep689 ep690 (BSN.zetaApproximant_eq_folded' qz14 2 31 rfl) (ep907 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep909 := @Enclosure.Real.IsNear.mulLit_ff (Real.sin (@HSub.hSub Real Real Real qz599 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz23 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz24 (@Nat.cast Complex Complex.instNatCast j))))) qz348)) (Complex.im (zetaApproximant qz14 2 31)) 121 1048576 8436785

noncomputable def ep910 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz599 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz23 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz24 (@Nat.cast Complex Complex.instNatCast j))))) qz348)) Bool.false 121 1048576 67494280

noncomputable def ep911 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz599 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz23 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz24 (@Nat.cast Complex Complex.instNatCast j))))) qz348) qz902 Bool.false 125179671 1048576 351

noncomputable def ep912 := BSN.sin_dyadic_bound_f 249822 2147483648 1 0 1048576 378978 0 1 1 0 1 1 121 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 249822) qz268 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 249822) qz269 0 0 rfl) rfl rfl

noncomputable def ep913 := @ep911 1048576 Bool.false 121 1048576 1 189304 (@ep489 125179671 1048576 351 1048576 ep685 rfl) (Enclosure.sfrac_false_div 125179671 1048576) (BSN.sin_reduce0 qz902 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 17579666153544876032) qz273) 226375608064910080 72057594037927936 Bool.false 121 1048576 19 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q0 125179671 1048576 226375608064910080 72057594037927936 19 17579666153544876032 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 121 1048576 17579666153544876032 151115727451828646838272 249822 2147483648 378978 378608 (ep912 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep914 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz14 2 31) Bool.false ep479 ep480 ep481 ep482 Bool.false ep688 ep480 ep689 ep690 (@ep691 ep482 Bool.false ep688 ep480 ep689 ep690 (BSN.zetaApproximant_eq_folded' qz14 2 31 rfl) (ep907 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow40.d15 : Enclosure.Real.IsNear (hardyZApproximantEM 2 31 qz11) Bool.false ep462 ep463 ep464 ep465 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 2 31 qz11) ep466 Bool.false ep462 ep463 ep464 ep465 (@Eq.refl Real ep466) (@ep467 Bool.false ep462 ep463 ep464 ep465 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz599 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz23 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz24 (@Nat.cast Complex Complex.instNatCast j))))) qz348) (zetaApproximant qz14 2 31)) (@ep469 ep470 ep471 ep472 ep473 ep474 ep475 ep476 ep477 ep462 ep463 ep464 ep465 (@ep478 24812453888 ep479 ep480 ep481 ep482 ep468 ep470 ep471 ep472 (@ep483 198499631104 1048575 1048576 8436785 24812453888 (ep687 rfl rfl) rfl) ep908 rfl) (@ep909 24812453888 ep688 ep480 ep689 ep690 ep473 ep474 ep475 ep476 (@ep910 198499631104 121 1048576 8436785 24812453888 (ep913 rfl rfl) rfl) ep914 rfl) rfl rfl))

noncomputable abbrev qz617 := (@HAdd.hAdd Complex Complex Complex qz820 (@HAdd.hAdd Complex Complex Complex qz820 qz821 (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I (@HDiv.hDiv Complex Complex Complex qz822 (↑(Enclosure.sfrac Bool.false 124004 1000)) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 4))

noncomputable abbrev qz386 := (@HPow.hPow Complex Nat Complex qz545 qz617 3)

noncomputable abbrev qz53 := qz386

noncomputable def ep915 := Enclosure.Complex.IsNear qz53 Bool.true 24468698213 500000 0 1 Bool.true 14686958210563 62500000 0 1

noncomputable abbrev qz387 := qz617

noncomputable abbrev qz54 := (@HPow.hPow Complex Nat Complex qz256 qz387 2)

noncomputable abbrev qz55 := qz387

noncomputable def ep916 := @Enclosure.Complex.IsNear.of_eq qz53 (@HMul.hMul Complex Complex Complex qz3 qz54 qz55) Bool.true 24468698213 500000 0 1 Bool.true 14686958210563 62500000

noncomputable def ep917 := @Enclosure.Complex.IsNear.mul qz54 qz55 Bool.true 24468698213 500000 0 1 Bool.true 14686958210563 62500000 0

noncomputable abbrev qz56 := (Complex.re qz387)

noncomputable abbrev qz57 := (Complex.im qz387)

noncomputable def ep918 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re qz54) qz56) (@HMul.hMul Real Real Real qz0 (Complex.im qz54) qz57) 2032661049 125000 0 1 16338054017 500000

noncomputable def ep919 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re qz54) qz56 119568297 31250 0 1 17000 4000 0 1

noncomputable def ep920 := @Enclosure.Complex.IsNear.re_isNear qz54 Bool.true 119568297 31250 0 1 Bool.false 527017 1000 0 1

noncomputable abbrev qz388 := (@HPow.hPow Complex Nat Complex qz545 qz617 1)

noncomputable abbrev qz58 := qz388

noncomputable def ep921 := @Enclosure.Complex.IsNear.of_eq qz54 (@HMul.hMul Complex Complex Complex qz3 qz58 qz55) Bool.true 119568297 31250 0 1 Bool.false 527017 1000

noncomputable def ep922 := @Enclosure.Complex.IsNear.mul qz58 qz55 Bool.true 119568297 31250 0 1 Bool.false 527017 1000 0

noncomputable abbrev qz59 := (Complex.re qz388)

noncomputable abbrev qz60 := (Complex.im qz388)

noncomputable def ep923 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz59 qz56) (@HMul.hMul Real Real Real qz0 qz60 qz57) 289 16 0 1 961062001 250000

noncomputable def ep924 := @Enclosure.Real.IsNear.mulLit_ff qz59 qz56 17000 4000 0 1 17000 4000 0 1

noncomputable def ep925 := @Enclosure.Complex.IsNear.re_isNear qz58 Bool.false 17000 4000 0 1 Bool.false 248008 4000 0 1

noncomputable def ep926 := @Enclosure.Complex.IsNear.of_eq qz58 qz55 Bool.false 17000 4000 0 1 Bool.false 248008 4000 0

noncomputable abbrev qz389 := (Enclosure.sfrac Bool.false 124004 1000)

noncomputable abbrev qz61 := qz389

noncomputable abbrev qz390 := (Enclosure.sfrac Bool.false 248008 4000)

noncomputable abbrev qz618 := (Complex.mk (Enclosure.sfrac Bool.false 17000 4000) qz390)

noncomputable def ep927 := @Enclosure.Complex.IsNear.of_eq qz55 qz618 Bool.false 17000 4000 0 1 Bool.false 248008 4000 0 1 (BSN.w_shift_mk qz61 Bool.false 124004 1000 4 (@Eq.refl Real qz61) rfl)

noncomputable abbrev qz62 := (@ep926 1 (BSN.pow_one_c qz387) (ep927 (@Enclosure.Complex.IsNear.mk qz549 qz390 Bool.false 17000 4000 0 1 Bool.false 248008 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 17000 4000) (Enclosure.Real.IsNear.const Bool.false 248008 4000))))

noncomputable abbrev qz63 := (ep927 (@Enclosure.Complex.IsNear.mk qz549 qz390 Bool.false 17000 4000 0 1 Bool.false 248008 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 17000 4000) (Enclosure.Real.IsNear.const Bool.false 248008 4000)))

noncomputable abbrev qz949 := (@Enclosure.Complex.IsNear.re_isNear qz55 Bool.false 17000 4000 0 1 Bool.false 248008 4000 0 1 qz63)

noncomputable def ep928 := @ep924 289 16 0 1 (ep925 qz62) qz949

noncomputable def ep929 := @Enclosure.Real.IsNear.mulLit_ff qz60 qz57 248008 4000 0 1 248008 4000 0 1

noncomputable def ep930 := @Enclosure.Complex.IsNear.im_isNear qz58 Bool.false 17000 4000 0 1 Bool.false 248008 4000 0 1

noncomputable abbrev qz950 := (@Enclosure.Complex.IsNear.im_isNear qz55 Bool.false 17000 4000 0 1 Bool.false 248008 4000 0 1 qz63)

noncomputable def ep931 := @ep929 961062001 250000 0 1 (ep930 qz62) qz950

noncomputable def ep932 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz59 qz57) (@HMul.hMul Real Real Real qz0 qz60 qz56) 527017 2000 0 1 527017 2000

noncomputable def ep933 := @Enclosure.Real.IsNear.mulLit_ff qz59 qz57 17000 4000 0 1 248008 4000 0 1

noncomputable def ep934 := @ep933 527017 2000 0 1 (ep925 qz62) qz950

noncomputable def ep935 := @Enclosure.Real.IsNear.mulLit_ff qz60 qz56 248008 4000 0 1 17000 4000 0 1

noncomputable def ep936 := @ep935 527017 2000 0 1 (ep930 qz62) qz949

noncomputable abbrev qz619 := (@ep921 0 1 (BSN.pow_succ_c qz55 1 2 rfl) (@ep922 1 (@ep923 0 1 15304742016 119568297 31250 0 1 (ep928 rfl) (ep931 rfl) rfl rfl) (@ep932 0 1 2108068000 527017 1000 0 1 (ep934 rfl) (ep936 rfl) rfl rfl)))

noncomputable def ep937 := @ep919 2032661049 125000 0 1 (ep920 qz619) qz949

noncomputable def ep938 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz54) qz57 527017 1000 0 1 248008 4000 0 1

noncomputable def ep939 := @Enclosure.Complex.IsNear.im_isNear qz54 Bool.true 119568297 31250 0 1 Bool.false 527017 1000 0 1

noncomputable def ep940 := @ep938 16338054017 500000 0 1 (ep939 qz619) qz950

noncomputable def ep941 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re qz54) qz57) (@HMul.hMul Real Real Real qz0 (Complex.im qz54) qz56) 3706736775297 15625000 0 1 8959289 4000

noncomputable def ep942 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re qz54) qz57 119568297 31250 0 1 248008 4000 0 1

noncomputable def ep943 := @ep942 3706736775297 15625000 0 1 (ep920 qz619) qz950

noncomputable def ep944 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz54) qz56 527017 1000 0 1 17000 4000 0 1

noncomputable def ep945 := @ep944 8959289 4000 0 1 (ep939 qz619) qz949

theorem EMRow40.d16 : ep915 := @ep916 0 1 (BSN.pow_succ_c qz55 2 3 rfl) (@ep917 1 (@ep918 0 1 3058587276625000 24468698213 500000 0 1 (ep937 rfl) (ep940 rfl) rfl rfl) (@ep941 0 1 14686958210563000 14686958210563 62500000 0 1 (ep943 rfl) (ep945 rfl) rfl rfl))

noncomputable abbrev qz391 := (@HAdd.hAdd Complex Complex Complex qz551 qz552 (@HMul.hMul Complex Complex Complex qz547 Complex.I ↑(Enclosure.sfrac Bool.false 124004 1000)))

noncomputable abbrev qz64 := qz391

noncomputable abbrev qz65 := (@Neg.neg Complex Complex.instNeg qz391)

noncomputable def ep946 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 9) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 8) (@HPow.hPow Complex Complex Complex qz16 qz825 qz65)) Bool.true 3670267425 68719476736 14526913298637 6504435912015872 Bool.false 336530433525 549755813888 29068169191171 13008871824031744

noncomputable def ep947 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 8) (@HPow.hPow Complex Complex Complex qz16 qz825 qz65) Bool.true 435521191971 1099511627776 52008278011665 26017743648063488 Bool.false 384329748543 549755813888 26027455851637 13008871824031744 Bool.false

noncomputable def ep948 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 8) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 7) (@HPow.hPow Complex Complex Complex qz16 qz826 qz65)) Bool.true 435521191971 1099511627776 52008278011665 26017743648063488 Bool.false 384329748543 549755813888 26027455851637 13008871824031744

noncomputable def ep949 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 7) (@HPow.hPow Complex Complex Complex qz16 qz826 qz65) Bool.true 11630757337 137438953472 1421363705689 813054489001984 Bool.false 1004062675711 1099511627776 45536665117063 26017743648063488 Bool.true

noncomputable def ep950 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 7) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 6) (@HPow.hPow Complex Complex Complex qz16 qz827 qz65)) Bool.true 11630757337 137438953472 1421363705689 813054489001984 Bool.false 1004062675711 1099511627776 45536665117063 26017743648063488

noncomputable def ep951 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 6) (@HPow.hPow Complex Complex Complex qz16 qz827 qz65) Bool.false 197134568797 1099511627776 38442284869947 26017743648063488 Bool.false 1346527588027 1099511627776 38492421277131 26017743648063488 Bool.true

noncomputable def ep952 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 6) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 5) (@HPow.hPow Complex Complex Complex qz16 qz18 qz65)) Bool.false 197134568797 1099511627776 38442284869947 26017743648063488 Bool.false 1346527588027 1099511627776 38492421277131 26017743648063488

noncomputable def ep953 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 5) (@HPow.hPow Complex Complex Complex qz16 qz18 qz65) Bool.false 155206911627 1099511627776 30744326352509 26017743648063488 Bool.false 428301187359 549755813888 1923241023977 1626108978003968 Bool.false

noncomputable def ep954 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 5) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 4) (@HPow.hPow Complex Complex Complex qz16 qz19 qz65)) Bool.false 155206911627 1099511627776 30744326352509 26017743648063488 Bool.false 428301187359 549755813888 1923241023977 1626108978003968

noncomputable def ep955 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 4) (@HPow.hPow Complex Complex Complex qz16 qz19 qz65) Bool.false 504776317451 1099511627776 22124345385725 26017743648063488 Bool.false 1280903125235 1099511627776 22148502516491 26017743648063488 Bool.true

noncomputable def ep956 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 4) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 3) (@HPow.hPow Complex Complex Complex qz16 qz554 qz65)) Bool.false 504776317451 1099511627776 22124345385725 26017743648063488 Bool.false 1280903125235 1099511627776 22148502516491 26017743648063488

noncomputable def ep957 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 3) (@HPow.hPow Complex Complex Complex qz16 qz554 qz65) Bool.false 767686047261 1099511627776 12178784543875 26017743648063488 Bool.false 703103240125 1099511627776 12190633601821 26017743648063488 Bool.true

noncomputable def ep958 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 3) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 2) (@HPow.hPow Complex Complex Complex qz16 qz555 qz65)) Bool.false 767686047261 1099511627776 12178784543875 26017743648063488 Bool.false 703103240125 1099511627776 12190633601821 26017743648063488

noncomputable def ep959 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 2) (@HPow.hPow Complex Complex Complex qz16 qz555 qz65) Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.true

noncomputable def ep960 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz264) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz64)

noncomputable abbrev qz620 := (@HMul.hMul Real Real Real qz0 qz61 qz271)

noncomputable def ep961 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz555 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz265 (Real.cos qz620)) (@HMul.hMul Real Real Real qz0 qz265 (@Neg.neg Real Real.instNeg (Real.sin qz620)))) Bool.true 331825580515 1099511627776 12178784543875 26017743648063488 Bool.false 703103240125 1099511627776 12190633601821 26017743648063488 (BSN.cpow_neg_s_mk qz61 124004 1000 2 (@Eq.refl Real qz61) rfl)

noncomputable def ep962 := nat_lit 1239490155484820154434528516543141487270795842229092420478363559185399530192896

noncomputable def ep963 := nat_lit 1201120464452813459287239706928232233817495927330963576732077585699312828416

noncomputable def ep964 := nat_lit 3716068225525554836385011070215567997344752534832615334281626522384799964921856

noncomputable def ep965 := BSN.cos_dyadic_bound_f 2426321356 2147483648 3 2 1048576 378978 ep962 ep95 ep963 ep964 ep97 ep963 447533 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2426321356) qz274 0 2 ep962 ep95 ep963 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2426321356) qz275 0 2 ep964 ep97 ep963 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz392 := (Enclosure.Real.IsNear.const Bool.false 124004 1000)

noncomputable abbrev qz951 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 90128091) qz270)

noncomputable def ep966 := @Enclosure.Real.IsNear.cos_image qz620 qz951 Bool.false 90128091 1048576 43 65536 Bool.true 447533 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz620 Bool.false 704125713 8192000 31001 47326000 90128091 1048576 43 65536 (@Enclosure.Real.IsNear.mulLit_ff qz61 qz271 124004 1000 0 1 363408 524288 1 189304 704125713 8192000 31001 47326000 qz392 qz556 rfl) rfl) (Enclosure.sfrac_false_div 90128091 1048576) (BSN.cos_reduce2 qz951 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 170737186860210724012032) qz273) 226375608064910080 72057594037927936 Bool.false 447533 1048576 13 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q2 90128091 1048576 226375608064910080 72057594037927936 13 170737186860210724012032 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 447533 1048576 170737186860210724012032 151115727451828646838272 2426321356 2147483648 378978 378608 (ep965 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep967 := nat_lit 2230121383501114027214721538012112091300378519270501585999668744465159704084480

noncomputable def ep968 := nat_lit 5838849428417613135199710401934790720265286842778492117541566205127143194689536

noncomputable def ep969 := BSN.sin_dyadic_bound_f 2426321356 2147483648 3 2 1048576 378978 ep967 ep88 ep963 ep968 ep91 ep963 948275 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2426321356) qz268 0 2 ep967 ep88 ep963 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2426321356) qz269 0 2 ep968 ep91 ep963 rfl rfl rfl rfl) rfl rfl

noncomputable def ep970 := @Enclosure.Real.IsNear.sin_image qz620 qz951 Bool.false 90128091 1048576 43 65536 Bool.true 948275 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz620 Bool.false 704125713 8192000 31001 47326000 90128091 1048576 43 65536 (@Enclosure.Real.IsNear.mulLit_ff qz61 qz271 124004 1000 0 1 363408 524288 1 189304 704125713 8192000 31001 47326000 qz392 qz556 rfl) rfl) (Enclosure.sfrac_false_div 90128091 1048576) (BSN.sin_reduce2 qz951 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 170737186860210724012032) qz273) 226375608064910080 72057594037927936 Bool.false 948275 1048576 13 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q2 90128091 1048576 226375608064910080 72057594037927936 13 170737186860210724012032 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 948275 1048576 170737186860210724012032 151115727451828646838272 2426321356 2147483648 378978 378608 (ep969 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep971 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz265 (Real.cos qz620)) (@HMul.hMul Real Real Real qz0 qz265 (@Neg.neg Real Real.instNeg (Real.sin qz620))) Bool.true 331825580515 1099511627776 12178784543875 26017743648063488 Bool.false 703103240125 1099511627776 12190633601821 26017743648063488 (@Enclosure.Real.IsNear.mulLit_ft qz265 (Real.cos qz620) 741455 1048576 1 1048576 447533 1048576 1025701 1550778368 331825580515 1099511627776 12178784543875 26017743648063488 qz557 (@Enclosure.Real.IsNear.recentre' (Real.cos qz620) Bool.true 447533 1048576 8205608 12406226944 447533 1048576 1025701 1550778368 (ep966 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz265 (@Neg.neg Real Real.instNeg (Real.sin qz620)) 741455 1048576 1 1048576 948275 1048576 1025701 1550778368 703103240125 1099511627776 12190633601821 26017743648063488 qz557 (@Enclosure.Real.IsNear.neg (Real.sin qz620) Bool.true 948275 1048576 1025701 1550778368 (@Enclosure.Real.IsNear.recentre' (Real.sin qz620) Bool.true 948275 1048576 8205608 12406226944 948275 1048576 1025701 1550778368 (ep970 rfl rfl) rfl)) rfl)

noncomputable def ep972 := @ep959 331825580515 1099511627776 12178784543875 26017743648063488 Bool.false 703103240125 1099511627776 12190633601821 26017743648063488 Bool.false 767686047261 767686047261 1099511627776 12178784543875 26017743648063488 Bool.false 703103240125 703103240125 1099511627776 12190633601821 26017743648063488 (ep960 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz264 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz276)) (ep961 ep971) rfl rfl

noncomputable abbrev qz621 := (@HMul.hMul Real Real Real qz0 qz61 qz280)

noncomputable def ep973 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz554 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz277 (Real.cos qz621)) (@HMul.hMul Real Real Real qz0 qz277 (@Neg.neg Real Real.instNeg (Real.sin qz621)))) Bool.true 131454864905 549755813888 4972780420925 13008871824031744 Bool.false 288899942555 549755813888 4978934457335 13008871824031744 (BSN.cpow_neg_s_mk qz61 124004 1000 3 (@Eq.refl Real qz61) rfl)

noncomputable def ep974 := nat_lit 1301832874753323877649085804331594131346761193952637728820530701693738282909696

noncomputable def ep975 := nat_lit 1324855706672358172585764608937884927567227325601318600340000257601454473216

noncomputable def ep976 := nat_lit 3902848912846626916602085883776906624185149127206710549260912104566011939782656

noncomputable def ep977 := BSN.cos_dyadic_bound_f 2456241544 2147483648 3 2 1048576 378978 ep974 ep95 ep975 ep976 ep97 ep975 434278 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2456241544) qz274 0 2 ep974 ep95 ep975 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2456241544) qz275 0 2 ep976 ep97 ep975 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz952 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 142849879) qz270)

noncomputable def ep978 := @Enclosure.Real.IsNear.cos_image qz621 qz952 Bool.false 142849879 1048576 43 65536 Bool.true 434278 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz621 Bool.false 17856234989 131072000 31001 47326000 142849879 1048576 43 65536 (@Enclosure.Real.IsNear.mulLit_ff qz61 qz280 124004 1000 0 1 575989 524288 1 189304 17856234989 131072000 31001 47326000 qz392 qz558 rfl) rfl) (Enclosure.sfrac_false_div 142849879 1048576) (BSN.cos_reduce2 qz952 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 172842632902935060676608) qz273) 226375608064910080 72057594037927936 Bool.false 434278 1048576 21 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q2 142849879 1048576 226375608064910080 72057594037927936 21 172842632902935060676608 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 434278 1048576 172842632902935060676608 151115727451828646838272 2456241544 2147483648 378978 378608 (ep977 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep979 := nat_lit 2342239289990645093230285836109719128482116367254266856996683262842647745658880

noncomputable def ep980 := nat_lit 6132291231212315235704657380444317332332338784281630109638381878456532217102336

noncomputable def ep981 := BSN.sin_dyadic_bound_f 2456241544 2147483648 3 2 1048576 378978 ep979 ep88 ep975 ep980 ep91 ep975 954418 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2456241544) qz268 0 2 ep979 ep88 ep975 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2456241544) qz269 0 2 ep980 ep91 ep975 rfl rfl rfl rfl) rfl rfl

noncomputable def ep982 := @Enclosure.Real.IsNear.sin_image qz621 qz952 Bool.false 142849879 1048576 43 65536 Bool.true 954418 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz621 Bool.false 17856234989 131072000 31001 47326000 142849879 1048576 43 65536 (@Enclosure.Real.IsNear.mulLit_ff qz61 qz280 124004 1000 0 1 575989 524288 1 189304 17856234989 131072000 31001 47326000 qz392 qz558 rfl) rfl) (Enclosure.sfrac_false_div 142849879 1048576) (BSN.sin_reduce2 qz952 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 172842632902935060676608) qz273) 226375608064910080 72057594037927936 Bool.false 954418 1048576 21 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q2 142849879 1048576 226375608064910080 72057594037927936 21 172842632902935060676608 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 954418 1048576 172842632902935060676608 151115727451828646838272 2456241544 2147483648 378978 378608 (ep981 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep983 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz277 (Real.cos qz621)) (@HMul.hMul Real Real Real qz0 qz277 (@Neg.neg Real Real.instNeg (Real.sin qz621))) Bool.true 131454864905 549755813888 4972780420925 13008871824031744 Bool.false 288899942555 549755813888 4978934457335 13008871824031744 (@Enclosure.Real.IsNear.mulLit_ft qz277 (Real.cos qz621) 605395 1048576 1 1048576 217139 524288 1025701 1550778368 131454864905 549755813888 4972780420925 13008871824031744 qz559 (@Enclosure.Real.IsNear.recentre' (Real.cos qz621) Bool.true 434278 1048576 8205608 12406226944 217139 524288 1025701 1550778368 (ep978 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz277 (@Neg.neg Real Real.instNeg (Real.sin qz621)) 605395 1048576 1 1048576 477209 524288 1025701 1550778368 288899942555 549755813888 4978934457335 13008871824031744 qz559 (@Enclosure.Real.IsNear.neg (Real.sin qz621) Bool.true 477209 524288 1025701 1550778368 (@Enclosure.Real.IsNear.recentre' (Real.sin qz621) Bool.true 954418 1048576 8205608 12406226944 477209 524288 1025701 1550778368 (ep982 rfl rfl) rfl)) rfl)

noncomputable def ep984 := @ep957 131454864905 549755813888 4972780420925 13008871824031744 Bool.false 288899942555 549755813888 4978934457335 13008871824031744 Bool.false 277503715231661962559488 504776317451 1099511627776 22124345385725 26017743648063488 Bool.false 704183940125250216263680 1280903125235 1099511627776 22148502516491 26017743648063488 (ep958 (BSN.head_sum_c_succ qz64 2 3 rfl rfl) (ep972 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep973 ep983) rfl rfl

noncomputable abbrev qz622 := (@HMul.hMul Real Real Real qz0 qz61 qz284)

noncomputable def ep985 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz19 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz282 (Real.cos qz622)) (@HMul.hMul Real Real Real qz0 qz282 (@Neg.neg Real Real.instNeg (Real.sin qz622)))) Bool.true 2731010983 8589934592 67343601303 203263622250496 Bool.true 424300750517 1099511627776 8623353867141 26017743648063488 (BSN.cpow_neg_s_mk qz61 124004 1000 4 (@Eq.refl Real qz61) rfl)

noncomputable def ep986 := nat_lit 4796441371007572396858587148225107361

noncomputable def ep987 := BSN.sin_dyadic_bound_f 1479891191 2147483648 2 1 1048576 378978 ep986 ep106 ep986 ep986 ep107 ep986 666752 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1479891191) qz268 0 1 ep986 ep106 ep986 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1479891191) qz269 0 1 ep986 ep107 ep986 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz953 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 90128215) qz279)

noncomputable def ep988 := @Enclosure.Real.IsNear.cos_image qz622 qz953 Bool.false 90128215 524288 43 65536 Bool.true 666752 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz622 Bool.false 22532053817 131072000 31001 47326000 90128215 524288 43 65536 (@Enclosure.Real.IsNear.mulLit_ff qz61 qz284 124004 1000 0 1 726817 524288 1 189304 22532053817 131072000 31001 47326000 qz392 qz560 rfl) rfl) (Enclosure.sfrac_false_div 90128215 524288) (BSN.cos_reduce1 qz953 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 52069042342396554117120) qz281) 226375608064910080 72057594037927936 Bool.false 666752 1048576 27 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q1 90128215 524288 226375608064910080 72057594037927936 27 52069042342396554117120 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 666752 1048576 52069042342396554117120 75557863725914323419136 1479891191 2147483648 378978 378608 (ep987 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep989 := nat_lit 171398170214842140970612835903460710747647802753205845423836851465097739784001

noncomputable def ep990 := nat_lit 23005849825513000756140373009905812274944978173257336390200266179976384321

noncomputable def ep991 := nat_lit 514148498944875396910326226964362320618393518303271021598730153862933266583361

noncomputable def ep992 := BSN.cos_dyadic_bound_f 1479891191 2147483648 3 2 1048576 378978 ep989 ep95 ep990 ep991 ep97 ep990 809291 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1479891191) qz274 0 2 ep989 ep95 ep990 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1479891191) qz275 0 2 ep991 ep97 ep990 rfl rfl rfl rfl) rfl rfl

noncomputable def ep993 := @Enclosure.Real.IsNear.sin_image qz622 qz953 Bool.false 90128215 524288 43 65536 Bool.false 809291 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz622 Bool.false 22532053817 131072000 31001 47326000 90128215 524288 43 65536 (@Enclosure.Real.IsNear.mulLit_ff qz61 qz284 124004 1000 0 1 726817 524288 1 189304 22532053817 131072000 31001 47326000 qz392 qz560 rfl) rfl) (Enclosure.sfrac_false_div 90128215 524288) (BSN.sin_reduce1 qz953 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 52069042342396554117120) qz281) 226375608064910080 72057594037927936 Bool.false 809291 1048576 27 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q1 90128215 524288 226375608064910080 72057594037927936 27 52069042342396554117120 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 809291 1048576 52069042342396554117120 75557863725914323419136 1479891191 2147483648 378978 378608 (ep992 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep994 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz282 (Real.cos qz622)) (@HMul.hMul Real Real Real qz0 qz282 (@Neg.neg Real Real.instNeg (Real.sin qz622))) Bool.true 2731010983 8589934592 67343601303 203263622250496 Bool.true 424300750517 1099511627776 8623353867141 26017743648063488 (@Enclosure.Real.IsNear.mulLit_ft qz282 (Real.cos qz622) 524287 1048576 1 1048576 5209 8192 1025701 1550778368 2731010983 8589934592 67343601303 203263622250496 qz561 (@Enclosure.Real.IsNear.recentre' (Real.cos qz622) Bool.true 666752 1048576 8205608 12406226944 5209 8192 1025701 1550778368 (ep988 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz282 (@Neg.neg Real Real.instNeg (Real.sin qz622)) 524287 1048576 1 1048576 809291 1048576 1025701 1550778368 424300750517 1099511627776 8623353867141 26017743648063488 qz561 (@Enclosure.Real.IsNear.neg (Real.sin qz622) Bool.false 809291 1048576 1025701 1550778368 (@Enclosure.Real.IsNear.recentre' (Real.sin qz622) Bool.false 809291 1048576 8205608 12406226944 809291 1048576 1025701 1550778368 (ep993 rfl rfl) rfl)) rfl)

noncomputable def ep995 := @ep955 2731010983 8589934592 67343601303 203263622250496 Bool.true 424300750517 1099511627776 8623353867141 26017743648063488 Bool.false 1333217219102254301184 155206911627 1099511627776 30744326352509 26017743648063488 Bool.false 941844271382975288967168 428301187359 549755813888 1923241023977 1626108978003968 (ep956 (BSN.head_sum_c_succ qz64 3 4 rfl rfl) (ep984 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep985 ep994) rfl rfl

noncomputable abbrev qz623 := (@HMul.hMul Real Real Real qz0 qz61 qz287)

noncomputable def ep996 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz18 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz285 (Real.cos qz623)) (@HMul.hMul Real Real Real qz0 qz285 (@Neg.neg Real Real.instNeg (Real.sin qz623)))) Bool.false 20963828585 549755813888 3848979258719 13008871824031744 Bool.false 489925213309 1099511627776 7720564893499 26017743648063488 (BSN.cpow_neg_s_mk qz61 124004 1000 5 (@Eq.refl Real qz61) rfl)

noncomputable def ep997 := BSN.sin_dyadic_bound_f 183335313 2147483648 1 0 1048576 378978 0 1 1 0 1 1 89410 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 183335313) qz268 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 183335313) qz269 0 0 rfl) rfl rfl

noncomputable abbrev qz954 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 104635567) qz279)

noncomputable def ep998 := @Enclosure.Real.IsNear.cos_image qz623 qz954 Bool.false 104635567 524288 43 65536 Bool.false 89410 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz623 Bool.false 817465369 4096000 31001 47326000 104635567 524288 43 65536 (@Enclosure.Real.IsNear.mulLit_ff qz61 qz287 124004 1000 0 1 843808 524288 1 189304 817465369 4096000 31001 47326000 qz392 qz562 rfl) rfl) (Enclosure.sfrac_false_div 104635567 524288) (BSN.cos_reduce3 qz954 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6450537884600022073344) qz281) 226375608064910080 72057594037927936 Bool.false 89410 1048576 31 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q3 104635567 524288 226375608064910080 72057594037927936 31 6450537884600022073344 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 89410 1048576 6450537884600022073344 75557863725914323419136 183335313 2147483648 378978 378608 (ep997 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep999 := nat_lit 1129755586031094252709831309904961

noncomputable def ep1000 := BSN.cos_dyadic_bound_f 183335313 2147483648 2 1 1048576 378978 ep999 ep110 ep999 ep999 ep111 ep999 1044757 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 183335313) qz274 0 1 ep999 ep110 ep999 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 183335313) qz275 0 1 ep999 ep111 ep999 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1001 := @Enclosure.Real.IsNear.sin_image qz623 qz954 Bool.false 104635567 524288 43 65536 Bool.true 1044757 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz623 Bool.false 817465369 4096000 31001 47326000 104635567 524288 43 65536 (@Enclosure.Real.IsNear.mulLit_ff qz61 qz287 124004 1000 0 1 843808 524288 1 189304 817465369 4096000 31001 47326000 qz392 qz562 rfl) rfl) (Enclosure.sfrac_false_div 104635567 524288) (BSN.sin_reduce3 qz954 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6450537884600022073344) qz281) 226375608064910080 72057594037927936 Bool.false 1044757 1048576 31 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q3 104635567 524288 226375608064910080 72057594037927936 31 6450537884600022073344 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1044757 1048576 6450537884600022073344 75557863725914323419136 183335313 2147483648 378978 378608 (ep1000 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1002 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz285 (Real.cos qz623)) (@HMul.hMul Real Real Real qz0 qz285 (@Neg.neg Real Real.instNeg (Real.sin qz623))) Bool.false 20963828585 549755813888 3848979258719 13008871824031744 Bool.false 489925213309 1099511627776 7720564893499 26017743648063488 (@Enclosure.Real.IsNear.mulLit_ff qz285 (Real.cos qz623) 468937 1048576 1 1048576 44705 524288 1025701 1550778368 20963828585 549755813888 3848979258719 13008871824031744 qz563 (@Enclosure.Real.IsNear.recentre' (Real.cos qz623) Bool.false 89410 1048576 8205608 12406226944 44705 524288 1025701 1550778368 (ep998 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz285 (@Neg.neg Real Real.instNeg (Real.sin qz623)) 468937 1048576 1 1048576 1044757 1048576 1025701 1550778368 489925213309 1099511627776 7720564893499 26017743648063488 qz563 (@Enclosure.Real.IsNear.neg (Real.sin qz623) Bool.true 1044757 1048576 1025701 1550778368 (@Enclosure.Real.IsNear.recentre' (Real.sin qz623) Bool.true 1044757 1048576 8205608 12406226944 1044757 1048576 1025701 1550778368 (ep1001 rfl rfl) rfl)) rfl)

noncomputable def ep1003 := @ep953 20963828585 549755813888 3848979258719 13008871824031744 Bool.false 489925213309 1099511627776 7720564893499 26017743648063488 Bool.false 108375875314454664052736 197134568797 1099511627776 38442284869947 26017743648063488 Bool.false 740261370078428949118976 1346527588027 1099511627776 38492421277131 26017743648063488 (ep954 (BSN.head_sum_c_succ qz64 4 5 rfl rfl) (ep995 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep996 ep1002) rfl rfl

noncomputable abbrev qz624 := (@HMul.hMul Real Real Real qz0 qz61 qz290)

noncomputable def ep1004 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz827 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz288 (Real.cos qz624)) (@HMul.hMul Real Real Real qz0 qz288 (@Neg.neg Real Real.instNeg (Real.sin qz624)))) Bool.true 290180627493 1099511627776 7041353712101 26017743648063488 Bool.true 85616228079 274877906944 1761060959983 6504435912015872 (BSN.cpow_neg_s_mk qz61 124004 1000 6 (@Eq.refl Real qz61) rfl)

noncomputable def ep1005 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz290 124004 1000 0 1 4034681531866359 2251799813685248 62500000023663 11831500000000000000 125079162169388995359 562949953421312000 1937562500733576663 2957875000000000000000 qz392 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 62500000023663 11831500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz836) Bool.false 33845361775666394038272 18889465931478580854784 1000000000378608 189304000000000000000 4034681531866359 2251799813685248 62500000023663 11831500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 212580 524288 24973259072661432 36028797018963968 189304 1000000000000000 rfl rfl rfl rfl (ep152 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1006 := nat_lit 5192763660495647770530271459945988241

noncomputable def ep1007 := BSN.sin_dyadic_bound_f 1509557427 2147483648 2 1 1048576 378978 ep1006 ep106 ep1006 ep1006 ep107 ep1006 677867 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1509557427) qz268 0 1 ep1006 ep106 ep1006 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1509557427) qz269 0 1 ep1006 ep107 ep1006 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz955 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 116489047) qz279)

noncomputable def ep1008 := @Enclosure.Real.IsNear.cos_image qz624 qz955 Bool.false 116489047 524288 43 65536 Bool.true 677867 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz624 Bool.false 125079162169388995359 562949953421312000 1937562500733576663 2957875000000000000000 116489047 524288 43 65536 (ep1005 rfl) rfl) (Enclosure.sfrac_false_div 116489047 524288) (BSN.cos_reduce1 qz955 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 53112830222098019385344) qz281) 226375608064910080 72057594037927936 Bool.false 677867 1048576 35 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q1 116489047 524288 226375608064910080 72057594037927936 35 53112830222098019385344 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 677867 1048576 53112830222098019385344 75557863725914323419136 1509557427 2147483648 378978 378608 (ep1007 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1009 := nat_lit 185562585266155796140879701186392678765108357314928619523490343799782746608161

noncomputable def ep1010 := nat_lit 26964794433764159062184891846716975234819178725428994951398720990110274081

noncomputable def ep1011 := nat_lit 556633826209599860104514733775484602344855433587335000580568233957368019276321

noncomputable def ep1012 := BSN.cos_dyadic_bound_f 1509557427 2147483648 3 2 1048576 378978 ep1009 ep95 ep1010 ep1011 ep97 ep1010 800004 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1509557427) qz274 0 2 ep1009 ep95 ep1010 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1509557427) qz275 0 2 ep1011 ep97 ep1010 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1013 := @Enclosure.Real.IsNear.sin_image qz624 qz955 Bool.false 116489047 524288 43 65536 Bool.false 800004 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz624 Bool.false 125079162169388995359 562949953421312000 1937562500733576663 2957875000000000000000 116489047 524288 43 65536 (ep1005 rfl) rfl) (Enclosure.sfrac_false_div 116489047 524288) (BSN.sin_reduce1 qz955 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 53112830222098019385344) qz281) 226375608064910080 72057594037927936 Bool.false 800004 1048576 35 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q1 116489047 524288 226375608064910080 72057594037927936 35 53112830222098019385344 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 800004 1048576 53112830222098019385344 75557863725914323419136 1509557427 2147483648 378978 378608 (ep1012 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1014 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz288 (Real.cos qz624)) (@HMul.hMul Real Real Real qz0 qz288 (@Neg.neg Real Real.instNeg (Real.sin qz624))) Bool.true 290180627493 1099511627776 7041353712101 26017743648063488 Bool.true 85616228079 274877906944 1761060959983 6504435912015872 (@Enclosure.Real.IsNear.mulLit_ft qz288 (Real.cos qz624) 428079 1048576 1 1048576 677867 1048576 1025701 1550778368 290180627493 1099511627776 7041353712101 26017743648063488 qz566 (@Enclosure.Real.IsNear.recentre' (Real.cos qz624) Bool.true 677867 1048576 8205608 12406226944 677867 1048576 1025701 1550778368 (ep1008 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz288 (@Neg.neg Real Real.instNeg (Real.sin qz624)) 428079 1048576 1 1048576 200001 262144 1025701 1550778368 85616228079 274877906944 1761060959983 6504435912015872 qz566 (@Enclosure.Real.IsNear.neg (Real.sin qz624) Bool.false 200001 262144 1025701 1550778368 (@Enclosure.Real.IsNear.recentre' (Real.sin qz624) Bool.false 800004 1048576 8205608 12406226944 200001 262144 1025701 1550778368 (ep1013 rfl rfl) rfl)) rfl)

noncomputable def ep1015 := @ep951 290180627493 1099511627776 7041353712101 26017743648063488 Bool.true 85616228079 274877906944 1761060959983 6504435912015872 Bool.true 102305223454980199940096 11630757337 137438953472 1421363705689 813054489001984 Bool.false 275994646740031907037184 1004062675711 1099511627776 45536665117063 26017743648063488 (ep952 (BSN.head_sum_c_succ qz64 5 6 rfl rfl) (ep1003 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1004 ep1014) rfl rfl

noncomputable abbrev qz625 := (@HMul.hMul Real Real Real qz0 qz61 qz293)

noncomputable def ep1016 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz826 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz291 (Real.cos qz625)) (@HMul.hMul Real Real Real qz0 qz291 (@Neg.neg Real Real.instNeg (Real.sin qz625)))) Bool.true 342475133275 1099511627776 6524639429617 26017743648063488 Bool.true 235403178625 1099511627776 6518246586211 26017743648063488 (BSN.cpow_neg_s_mk qz61 124004 1000 7 (@Eq.refl Real qz61) rfl)

noncomputable def ep1017 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz293 124004 1000 0 1 4381796493761783 2251799813685248 62500000023663 11831500000000000000 135840073103109034783 562949953421312000 1937562500733576663 2957875000000000000000 qz392 (BSN.isNear_log_sfrac 7 1 4381796493761783 2251799813685248 62500000023663 11831500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz838) Bool.false 36757173121942042968064 18889465931478580854784 1000000000378608 189304000000000000000 4381796493761783 2251799813685248 62500000023663 11831500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 293399 524288 24973259072661432 36028797018963968 189304 1000000000000000 rfl rfl rfl rfl (ep162 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1018 := nat_lit 1204296394916314345007359904352204921954210801431072958826320874871014894608640

noncomputable def ep1019 := nat_lit 350438236953733153712809409089322381585317367835083579302182810639683297536

noncomputable def ep1020 := nat_lit 3153542229540041049913264724736296845071794918485839042559589233444955712921856

noncomputable def ep1021 := BSN.sin_dyadic_bound_f 2080062746 2147483648 3 2 1048576 378978 ep1018 ep88 ep1019 ep1020 ep91 ep1019 864127 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2080062746) qz268 0 2 ep1018 ep88 ep1019 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2080062746) qz269 0 2 ep1020 ep91 ep1019 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz956 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 253021853) qz270)

noncomputable def ep1022 := @Enclosure.Real.IsNear.cos_image qz625 qz956 Bool.false 253021853 1048576 43 65536 Bool.true 864127 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz625 Bool.false 135840073103109034783 562949953421312000 1937562500733576663 2957875000000000000000 253021853 1048576 43 65536 (ep1017 rfl) rfl) (Enclosure.sfrac_false_div 253021853 1048576) (BSN.cos_reduce1 qz956 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 146371403249071031320576) qz273) 226375608064910080 72057594037927936 Bool.false 864127 1048576 38 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q1 253021853 1048576 226375608064910080 72057594037927936 38 146371403249071031320576 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 864127 1048576 146371403249071031320576 151115727451828646838272 2080062746 2147483648 378978 378608 (ep1021 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1023 := nat_lit 669209303058820739739072306599709099921932808514078347605423678399737022914816

noncomputable def ep1024 := nat_lit 2006927032702554752909791300980948655002627790806564875657666669577931702149376

noncomputable def ep1025 := BSN.cos_dyadic_bound_f 2080062746 2147483648 3 2 1048576 378978 ep1023 ep95 ep1019 ep1024 ep97 ep1019 593965 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2080062746) qz274 0 2 ep1023 ep95 ep1019 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2080062746) qz275 0 2 ep1024 ep97 ep1019 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1026 := @Enclosure.Real.IsNear.sin_image qz625 qz956 Bool.false 253021853 1048576 43 65536 Bool.false 593965 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz625 Bool.false 135840073103109034783 562949953421312000 1937562500733576663 2957875000000000000000 253021853 1048576 43 65536 (ep1017 rfl) rfl) (Enclosure.sfrac_false_div 253021853 1048576) (BSN.sin_reduce1 qz956 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 146371403249071031320576) qz273) 226375608064910080 72057594037927936 Bool.false 593965 1048576 38 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q1 253021853 1048576 226375608064910080 72057594037927936 38 146371403249071031320576 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 593965 1048576 146371403249071031320576 151115727451828646838272 2080062746 2147483648 378978 378608 (ep1025 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1027 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz291 (Real.cos qz625)) (@HMul.hMul Real Real Real qz0 qz291 (@Neg.neg Real Real.instNeg (Real.sin qz625))) Bool.true 342475133275 1099511627776 6524639429617 26017743648063488 Bool.true 235403178625 1099511627776 6518246586211 26017743648063488 (@Enclosure.Real.IsNear.mulLit_ft qz291 (Real.cos qz625) 396325 1048576 1 1048576 864127 1048576 1025701 1550778368 342475133275 1099511627776 6524639429617 26017743648063488 qz567 (@Enclosure.Real.IsNear.recentre' (Real.cos qz625) Bool.true 864127 1048576 8205608 12406226944 864127 1048576 1025701 1550778368 (ep1022 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz291 (@Neg.neg Real Real.instNeg (Real.sin qz625)) 396325 1048576 1 1048576 593965 1048576 1025701 1550778368 235403178625 1099511627776 6518246586211 26017743648063488 qz567 (@Enclosure.Real.IsNear.neg (Real.sin qz625) Bool.false 593965 1048576 1025701 1550778368 (@Enclosure.Real.IsNear.recentre' (Real.sin qz625) Bool.false 593965 1048576 8205608 12406226944 593965 1048576 1025701 1550778368 (ep1026 rfl rfl) rfl)) rfl)

noncomputable def ep1028 := @ep949 342475133275 1099511627776 6524639429617 26017743648063488 Bool.true 235403178625 1099511627776 6518246586211 26017743648063488 Bool.true 59857576839372248973312 435521191971 1099511627776 52008278011665 26017743648063488 Bool.false 845150054846509388660736 384329748543 549755813888 26027455851637 13008871824031744 (ep950 (BSN.head_sum_c_succ qz64 6 7 rfl rfl) (ep1015 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1016 ep1027) rfl rfl

noncomputable abbrev qz626 := (@HMul.hMul Real Real Real qz0 qz61 qz296)

noncomputable def ep1029 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz825 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz294 (Real.cos qz626)) (@HMul.hMul Real Real Real qz0 qz294 (@Neg.neg Real Real.instNeg (Real.sin qz626)))) Bool.false 376796913171 1099511627776 6099375182883 26017743648063488 Bool.true 23899657509 274877906944 1520356669767 6504435912015872 (BSN.cpow_neg_s_mk qz61 124004 1000 8 (@Eq.refl Real qz61) rfl)

noncomputable def ep1030 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz296 124004 1000 0 1 9364972152248037 4503599627370496 125000000070989 23663000000000000000 290323501691841395037 1125899906842624000 3875125002200729989 5915750000000000000000 qz392 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 125000000070989 23663000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz841) Bool.false 39279540158062550581248 18889465931478580854784 1000000000567912 189304000000000000000 9364972152248037 4503599627370496 125000000070989 23663000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 524288 24973259072661432 36028797018963968 189304 1000000000000000 rfl rfl rfl rfl (ep177 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1031 := nat_lit 81063289418146036402351482930816016

noncomputable def ep1032 := BSN.cos_dyadic_bound_f 533588002 2147483648 2 1 1048576 378978 ep1031 ep110 ep1031 ep1031 ep111 ep1031 1016373 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 533588002) qz274 0 1 ep1031 ep110 ep1031 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 533588002) qz275 0 1 ep1031 ep111 ep1031 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz957 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 270384831) qz270)

noncomputable def ep1033 := @Enclosure.Real.IsNear.cos_image qz626 qz957 Bool.false 270384831 1048576 687 1048576 Bool.false 1016373 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz626 Bool.false 290323501691841395037 1125899906842624000 3875125002200729989 5915750000000000000000 270384831 1048576 687 1048576 (ep1030 rfl) rfl) (Enclosure.sfrac_false_div 270384831 1048576) (BSN.cos_reduce0 qz957 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 37547917651036195520512) qz273) 226375608064910080 72057594037927936 Bool.false 1016373 1048576 41 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q0 270384831 1048576 226375608064910080 72057594037927936 41 37547917651036195520512 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1016373 1048576 37547917651036195520512 151115727451828646838272 533588002 2147483648 378978 378608 (ep1032 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1034 := BSN.sin_dyadic_bound_f 533588002 2147483648 2 1 1048576 378978 ep1031 ep106 ep1031 ep1031 ep107 ep1031 257868 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 533588002) qz268 0 1 ep1031 ep106 ep1031 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 533588002) qz269 0 1 ep1031 ep107 ep1031 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1035 := @Enclosure.Real.IsNear.sin_image qz626 qz957 Bool.false 270384831 1048576 687 1048576 Bool.false 257868 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz626 Bool.false 290323501691841395037 1125899906842624000 3875125002200729989 5915750000000000000000 270384831 1048576 687 1048576 (ep1030 rfl) rfl) (Enclosure.sfrac_false_div 270384831 1048576) (BSN.sin_reduce0 qz957 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 37547917651036195520512) qz273) 226375608064910080 72057594037927936 Bool.false 257868 1048576 41 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q0 270384831 1048576 226375608064910080 72057594037927936 41 37547917651036195520512 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 257868 1048576 37547917651036195520512 151115727451828646838272 533588002 2147483648 378978 378608 (ep1034 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1036 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz294 (Real.cos qz626)) (@HMul.hMul Real Real Real qz0 qz294 (@Neg.neg Real Real.instNeg (Real.sin qz626))) Bool.false 376796913171 1099511627776 6099375182883 26017743648063488 Bool.true 23899657509 274877906944 1520356669767 6504435912015872 (@Enclosure.Real.IsNear.mulLit_ff qz294 (Real.cos qz626) 370727 1048576 1 1048576 1016373 1048576 16387553 24812453888 376796913171 1099511627776 6099375182883 26017743648063488 qz568 (@Enclosure.Real.IsNear.recentre' (Real.cos qz626) Bool.false 1016373 1048576 131100424 198499631104 1016373 1048576 16387553 24812453888 (ep1033 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz294 (@Neg.neg Real Real.instNeg (Real.sin qz626)) 370727 1048576 1 1048576 64467 262144 16387553 24812453888 23899657509 274877906944 1520356669767 6504435912015872 qz568 (@Enclosure.Real.IsNear.neg (Real.sin qz626) Bool.false 64467 262144 16387553 24812453888 (@Enclosure.Real.IsNear.recentre' (Real.sin qz626) Bool.false 257868 1048576 131100424 198499631104 64467 262144 16387553 24812453888 (ep1035 rfl rfl) rfl)) rfl)

noncomputable def ep1037 := @ep947 376796913171 1099511627776 6099375182883 26017743648063488 Bool.true 23899657509 274877906944 1520356669767 6504435912015872 Bool.true 64568027373359647948800 3670267425 68719476736 14526913298637 6504435912015872 Bool.false 92504781190308927897600 336530433525 549755813888 29068169191171 13008871824031744 (ep948 (BSN.head_sum_c_succ qz64 7 8 rfl rfl) (ep1028 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1029 ep1036) rfl rfl

theorem EMRow40.d17 : Enclosure.Complex.IsNear (BSN.headSumC qz64 9) Bool.true 3670267425 68719476736 14526913298637 6504435912015872 Bool.false 336530433525 549755813888 29068169191171 13008871824031744 := ep946 (BSN.head_sum_c_succ qz64 8 9 rfl rfl) (ep1037 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz958 := (@Nat.cast Complex Complex.instNatCast 16)

noncomputable def ep1038 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 17) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 16) (@HPow.hPow Complex Complex Complex qz16 qz958 qz65)) Bool.true 755071943339 1099511627776 97686741457215 26017743648063488 Bool.false 135108165307 1099511627776 97691435723155 26017743648063488

noncomputable def ep1039 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 16) (@HPow.hPow Complex Complex Complex qz16 qz958 qz65) Bool.true 702537437567 1099511627776 93386100603731 26017743648063488 Bool.true 67350865507 549755813888 46685590978881 13008871824031744 Bool.true

noncomputable abbrev qz959 := (@Nat.cast Complex Complex.instNatCast 15)

noncomputable def ep1040 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 16) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 15) (@HPow.hPow Complex Complex Complex qz16 qz959 qz65)) Bool.true 702537437567 1099511627776 93386100603731 26017743648063488 Bool.true 67350865507 549755813888 46685590978881 13008871824031744

noncomputable def ep1041 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 15) (@HPow.hPow Complex Complex Complex qz16 qz959 qz65) Bool.true 217523612377 549755813888 22229879070775 6504435912015872 Bool.true 19801165159 549755813888 44459832372381 13008871824031744 Bool.true

noncomputable abbrev qz960 := (@Nat.cast Complex Complex.instNatCast 14)

noncomputable def ep1042 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 15) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 14) (@HPow.hPow Complex Complex Complex qz16 qz960 qz65)) Bool.true 217523612377 549755813888 22229879070775 6504435912015872 Bool.true 19801165159 549755813888 44459832372381 13008871824031744

noncomputable def ep1043 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 14) (@HPow.hPow Complex Complex Complex qz16 qz960 qz65) Bool.true 43056864387 68719476736 42149467979619 13008871824031744 Bool.false 108401004057 1099511627776 84308022906183 26017743648063488 Bool.false

noncomputable abbrev qz961 := (@Nat.cast Complex Complex.instNatCast 13)

noncomputable def ep1044 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 14) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 13) (@HPow.hPow Complex Complex Complex qz16 qz961 qz65)) Bool.true 43056864387 68719476736 42149467979619 13008871824031744 Bool.false 108401004057 1099511627776 84308022906183 26017743648063488

noncomputable def ep1045 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 13) (@HPow.hPow Complex Complex Complex qz16 qz961 qz65) Bool.true 58560285285 137438953472 39754112624191 13008871824031744 Bool.true 102326433513 1099511627776 79518101451029 26017743648063488 Bool.true

noncomputable abbrev qz962 := (@Nat.cast Complex Complex.instNatCast 12)

noncomputable def ep1046 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 13) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 12) (@HPow.hPow Complex Complex Complex qz16 qz962 qz65)) Bool.true 58560285285 137438953472 39754112624191 13008871824031744 Bool.true 102326433513 1099511627776 79518101451029 26017743648063488

noncomputable def ep1047 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 12) (@HPow.hPow Complex Complex Complex qz16 qz962 qz65) Bool.true 387518729121 549755813888 9314577297377 3252217956007936 Bool.true 20064286005 1099511627776 74544028438729 26017743648063488 Bool.false

noncomputable abbrev qz963 := (@Nat.cast Complex Complex.instNatCast 11)

noncomputable def ep1048 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 12) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 11) (@HPow.hPow Complex Complex Complex qz16 qz963 qz65)) Bool.true 387518729121 549755813888 9314577297377 3252217956007936 Bool.true 20064286005 1099511627776 74544028438729 26017743648063488

noncomputable def ep1049 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 11) (@HPow.hPow Complex Complex Complex qz16 qz963 qz65) Bool.true 625494248771 1099511627776 69316888480899 26017743648063488 Bool.false 275804919305 1099511627776 69333346665311 26017743648063488 Bool.true

noncomputable abbrev qz964 := (@Nat.cast Complex Complex.instNatCast 10)

noncomputable def ep1050 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 11) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 10) (@HPow.hPow Complex Complex Complex qz16 qz964 qz65)) Bool.true 625494248771 1099511627776 69316888480899 26017743648063488 Bool.false 275804919305 1099511627776 69333346665311 26017743648063488

noncomputable def ep1051 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 10) (@HPow.hPow Complex Complex Complex qz16 qz964 qz65) Bool.true 149756375175 549755813888 15962957633113 6504435912015872 Bool.false 49594208125 137438953472 31941460177153 13008871824031744 Bool.true

noncomputable def ep1052 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 10) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 9) (@HPow.hPow Complex Complex Complex qz16 qz850 qz65)) Bool.true 149756375175 549755813888 15962957633113 6504435912015872 Bool.false 49594208125 137438953472 31941460177153 13008871824031744

noncomputable def ep1053 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 9) (@HPow.hPow Complex Complex Complex qz16 qz850 qz65) Bool.true 3670267425 68719476736 14526913298637 6504435912015872 Bool.false 336530433525 549755813888 29068169191171 13008871824031744 Bool.true

noncomputable abbrev qz627 := (@HMul.hMul Real Real Real qz0 qz61 qz299)

noncomputable def ep1054 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz850 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz297 (Real.cos qz627)) (@HMul.hMul Real Real Real qz0 qz297 (@Neg.neg Real Real.instNeg (Real.sin qz627)))) Bool.true 120394235775 549755813888 359011083619 1626108978003968 Bool.true 138153601025 549755813888 1436645492991 6504435912015872 (BSN.cpow_neg_s_mk qz61 124004 1000 9 (@Eq.refl Real qz61) rfl)

noncomputable def ep1055 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz299 124004 1000 0 1 9895417793173221 4503599627370496 125000000070989 23663000000000000000 306767847006163024221 1125899906842624000 3875125002200729989 5915750000000000000000 qz392 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 125000000070989 23663000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz852) Bool.false 41504390431577613533184 18889465931478580854784 1000000000567912 189304000000000000000 9895417793173221 4503599627370496 125000000070989 23663000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 61752 524288 24973259072661432 36028797018963968 189304 1000000000000000 rfl rfl rfl rfl (ep204 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1056 := nat_lit 5615035888866172035551854686004560961

noncomputable def ep1057 := BSN.sin_dyadic_bound_f 1539352687 2147483648 2 1 1048576 378978 ep1056 ep106 ep1056 ep1056 ep107 ep1056 688902 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1539352687) qz268 0 1 ep1056 ep106 ep1056 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1539352687) qz269 0 1 ep1056 ep107 ep1056 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz965 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 285699821) qz270)

noncomputable def ep1058 := @Enclosure.Real.IsNear.cos_image qz627 qz965 Bool.false 285699821 1048576 687 1048576 Bool.true 688902 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz627 Bool.false 306767847006163024221 1125899906842624000 3875125002200729989 5915750000000000000000 285699821 1048576 687 1048576 (ep1055 rfl) rfl) (Enclosure.sfrac_false_div 285699821 1048576) (BSN.cos_reduce1 qz965 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 108322315460447748227072) qz273) 226375608064910080 72057594037927936 Bool.false 688902 1048576 43 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q1 285699821 1048576 226375608064910080 72057594037927936 43 108322315460447748227072 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 688902 1048576 108322315460447748227072 151115727451828646838272 1539352687 2147483648 378978 378608 (ep1057 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1059 := nat_lit 200654787402019898270171806043782578192536225738773608878066905265190875011201

noncomputable def ep1060 := nat_lit 31528628033255122674361605888925205673503793504207043841401047294365243521

noncomputable def ep1061 := nat_lit 601901304949993184565166694919569884166261669629312412546517913700983894546561

noncomputable def ep1062 := BSN.cos_dyadic_bound_f 1539352687 2147483648 3 2 1048576 378978 ep1059 ep95 ep1060 ep1061 ep97 ep1060 790522 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1539352687) qz274 0 2 ep1059 ep95 ep1060 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1539352687) qz275 0 2 ep1061 ep97 ep1060 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1063 := @Enclosure.Real.IsNear.sin_image qz627 qz965 Bool.false 285699821 1048576 687 1048576 Bool.false 790522 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz627 Bool.false 306767847006163024221 1125899906842624000 3875125002200729989 5915750000000000000000 285699821 1048576 687 1048576 (ep1055 rfl) rfl) (Enclosure.sfrac_false_div 285699821 1048576) (BSN.sin_reduce1 qz965 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 108322315460447748227072) qz273) 226375608064910080 72057594037927936 Bool.false 790522 1048576 43 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q1 285699821 1048576 226375608064910080 72057594037927936 43 108322315460447748227072 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 790522 1048576 108322315460447748227072 151115727451828646838272 1539352687 2147483648 378978 378608 (ep1062 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1064 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz297 (Real.cos qz627)) (@HMul.hMul Real Real Real qz0 qz297 (@Neg.neg Real Real.instNeg (Real.sin qz627))) Bool.true 120394235775 549755813888 359011083619 1626108978003968 Bool.true 138153601025 549755813888 1436645492991 6504435912015872 (@Enclosure.Real.IsNear.mulLit_ft qz297 (Real.cos qz627) 349525 1048576 1 1048576 344451 524288 16387553 24812453888 120394235775 549755813888 359011083619 1626108978003968 qz569 (@Enclosure.Real.IsNear.recentre' (Real.cos qz627) Bool.true 688902 1048576 131100424 198499631104 344451 524288 16387553 24812453888 (ep1058 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz297 (@Neg.neg Real Real.instNeg (Real.sin qz627)) 349525 1048576 1 1048576 395261 524288 16387553 24812453888 138153601025 549755813888 1436645492991 6504435912015872 qz569 (@Enclosure.Real.IsNear.neg (Real.sin qz627) Bool.false 395261 524288 16387553 24812453888 (@Enclosure.Real.IsNear.recentre' (Real.sin qz627) Bool.false 790522 1048576 131100424 198499631104 395261 524288 16387553 24812453888 (ep1063 rfl rfl) rfl)) rfl)

noncomputable def ep1065 := @ep1053 120394235775 549755813888 359011083619 1626108978003968 Bool.true 138153601025 549755813888 1436645492991 6504435912015872 Bool.true 10291179739906100428800 149756375175 549755813888 15962957633113 6504435912015872 Bool.false 109058817007560949760000 49594208125 137438953472 31941460177153 13008871824031744 EMRow40.d17 (ep1054 ep1064) rfl rfl

noncomputable abbrev qz393 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 10 1)))

noncomputable def ep1066 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz964 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz300 (Real.cos qz393)) (@HMul.hMul Real Real Real qz0 qz300 (@Neg.neg Real Real.instNeg (Real.sin qz393)))) Bool.true 325981498421 1099511627776 5465057948447 26017743648063488 Bool.true 120948745695 1099511627776 5450426311005 26017743648063488 (BSN.cpow_neg_s_mk qz61 124004 1000 10 (@Eq.refl Real qz61) rfl)

noncomputable def ep1067 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz302 124004 1000 0 1 10369917190100709 4503599627370496 125000000070989 23663000000000000000 321477802810312079709 1125899906842624000 3875125002200729989 5915750000000000000000 qz392 (BSN.isNear_log_sfrac 10 1 10369917190100709 4503599627370496 125000000070989 23663000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz855) Bool.false 43494585150108164161536 18889465931478580854784 1000000000567912 189304000000000000000 10369917190100709 4503599627370496 125000000070989 23663000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 116991 524288 24973259072661432 36028797018963968 189304 1000000000000000 rfl rfl rfl rfl (ep218 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1068 := nat_lit 2987922600013329927659209709388300386092699795626363042192962777142989184467200

noncomputable def ep1069 := nat_lit 2155308362436974912069601155635217529764173413930986949661411932076904448256

noncomputable def ep1070 := nat_lit 7822022024590966136868865122717377325670786041113157798301164987484466209259776

noncomputable def ep1071 := BSN.sin_dyadic_bound_f 2610289502 2147483648 3 2 1048576 378978 ep1068 ep88 ep1069 ep1070 ep91 ep1069 983089 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2610289502) qz268 0 2 ep1068 ep88 ep1069 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2610289502) qz269 0 2 ep1070 ep91 ep1069 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz966 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 149699767) qz279)

noncomputable def ep1072 := @Enclosure.Real.IsNear.cos_image qz393 qz966 Bool.false 149699767 524288 43 65536 Bool.true 983089 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz393 Bool.false 321477802810312079709 1125899906842624000 3875125002200729989 5915750000000000000000 149699767 524288 43 65536 (ep1067 rfl) rfl) (Enclosure.sfrac_false_div 149699767 524288) (BSN.cos_reduce1 qz966 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 91841397111263103811584) qz281) 226375608064910080 72057594037927936 Bool.false 983089 1048576 45 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q1 149699767 524288 226375608064910080 72057594037927936 45 91841397111263103811584 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 983089 1048576 91841397111263103811584 75557863725914323419136 2610289502 2147483648 378978 378608 (ep1071 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1073 := nat_lit 1660914914835155281993814105729338088953617296865282128751495503715917060014336

noncomputable def ep1074 := nat_lit 4978434127780591896157303114876743831801323543767984412355163687283597371146496

noncomputable def ep1075 := BSN.cos_dyadic_bound_f 2610289502 2147483648 3 2 1048576 378978 ep1073 ep95 ep1069 ep1074 ep97 ep1069 364755 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2610289502) qz274 0 2 ep1073 ep95 ep1069 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2610289502) qz275 0 2 ep1074 ep97 ep1069 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1076 := @Enclosure.Real.IsNear.sin_image qz393 qz966 Bool.false 149699767 524288 43 65536 Bool.false 364755 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz393 Bool.false 321477802810312079709 1125899906842624000 3875125002200729989 5915750000000000000000 149699767 524288 43 65536 (ep1067 rfl) rfl) (Enclosure.sfrac_false_div 149699767 524288) (BSN.sin_reduce1 qz966 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 91841397111263103811584) qz281) 226375608064910080 72057594037927936 Bool.false 364755 1048576 45 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q1 149699767 524288 226375608064910080 72057594037927936 45 91841397111263103811584 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 364755 1048576 91841397111263103811584 75557863725914323419136 2610289502 2147483648 378978 378608 (ep1075 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1077 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz300 (Real.cos qz393)) (@HMul.hMul Real Real Real qz0 qz300 (@Neg.neg Real Real.instNeg (Real.sin qz393))) Bool.true 325981498421 1099511627776 5465057948447 26017743648063488 Bool.true 120948745695 1099511627776 5450426311005 26017743648063488 (@Enclosure.Real.IsNear.mulLit_ft qz300 (Real.cos qz393) 331589 1048576 1 1048576 983089 1048576 1025701 1550778368 325981498421 1099511627776 5465057948447 26017743648063488 qz570 (@Enclosure.Real.IsNear.recentre' (Real.cos qz393) Bool.true 983089 1048576 8205608 12406226944 983089 1048576 1025701 1550778368 (ep1072 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz300 (@Neg.neg Real Real.instNeg (Real.sin qz393)) 331589 1048576 1 1048576 364755 1048576 1025701 1550778368 120948745695 1099511627776 5450426311005 26017743648063488 qz570 (@Enclosure.Real.IsNear.neg (Real.sin qz393) Bool.false 364755 1048576 1025701 1550778368 (@Enclosure.Real.IsNear.recentre' (Real.sin qz393) Bool.false 364755 1048576 8205608 12406226944 364755 1048576 1025701 1550778368 (ep1076 rfl rfl) rfl)) rfl)

noncomputable def ep1078 := @ep1051 325981498421 1099511627776 5465057948447 26017743648063488 Bool.true 120948745695 1099511627776 5450426311005 26017743648063488 Bool.true 343869099815364248731648 625494248771 1099511627776 69316888480899 26017743648063488 Bool.false 37906339471708609576960 275804919305 1099511627776 69333346665311 26017743648063488 (ep1052 (BSN.head_sum_c_succ qz64 9 10 rfl rfl) (ep1065 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1066 ep1077) rfl rfl

noncomputable abbrev qz394 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 11 1)))

noncomputable def ep1079 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz963 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz303 (Real.cos qz394)) (@HMul.hMul Real Real Real qz0 qz303 (@Neg.neg Real Real.instNeg (Real.sin qz394)))) Bool.true 149543209471 1099511627776 5199729898117 26017743648063488 Bool.true 147934602655 549755813888 2605340886709 13008871824031744 (BSN.cpow_neg_s_mk qz61 124004 1000 11 (@Eq.refl Real qz61) rfl)

noncomputable def ep1080 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz305 124004 1000 0 1 10799156221662949 4503599627370496 125000000070989 23663000000000000000 334784642027773081949 1125899906842624000 3875125002200729989 5915750000000000000000 qz392 (BSN.isNear_log_sfrac 11 1 10799156221662949 4503599627370496 125000000070989 23663000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz858) Bool.false 45294944137145793642496 18889465931478580854784 1000000000567912 189304000000000000000 10799156221662949 4503599627370496 125000000070989 23663000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 166961 524288 24973259072661432 36028797018963968 189304 1000000000000000 rfl rfl rfl rfl (ep233 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1081 := nat_lit 1020134961943742801308683965576273041

noncomputable def ep1082 := BSN.sin_dyadic_bound_f 1004996173 2147483648 2 1 1048576 378978 ep1081 ep106 ep1081 ep1081 ep107 ep1081 473003 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1004996173) qz268 0 1 ep1081 ep106 ep1081 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1004996173) qz269 0 1 ep1081 ep107 ep1081 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz967 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 155896247) qz279)

noncomputable def ep1083 := @Enclosure.Real.IsNear.cos_image qz394 qz967 Bool.false 155896247 524288 43 65536 Bool.true 473003 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz394 Bool.false 334784642027773081949 1125899906842624000 3875125002200729989 5915750000000000000000 155896247 524288 43 65536 (ep1080 rfl) rfl) (Enclosure.sfrac_false_div 155896247 524288) (BSN.cos_reduce1 qz967 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 35360159310457889357824) qz281) 226375608064910080 72057594037927936 Bool.false 473003 1048576 47 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q1 155896247 524288 226375608064910080 72057594037927936 47 35360159310457889357824 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 473003 1048576 35360159310457889357824 75557863725914323419136 1004996173 2147483648 378978 378608 (ep1082 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1084 := BSN.cos_dyadic_bound_f 1004996173 2147483648 2 1 1048576 378978 ep1081 ep110 ep1081 ep1081 ep111 ep1081 935830 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1004996173) qz274 0 1 ep1081 ep110 ep1081 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1004996173) qz275 0 1 ep1081 ep111 ep1081 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1085 := @Enclosure.Real.IsNear.sin_image qz394 qz967 Bool.false 155896247 524288 43 65536 Bool.false 935830 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz394 Bool.false 334784642027773081949 1125899906842624000 3875125002200729989 5915750000000000000000 155896247 524288 43 65536 (ep1080 rfl) rfl) (Enclosure.sfrac_false_div 155896247 524288) (BSN.sin_reduce1 qz967 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 35360159310457889357824) qz281) 226375608064910080 72057594037927936 Bool.false 935830 1048576 47 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q1 155896247 524288 226375608064910080 72057594037927936 47 35360159310457889357824 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 935830 1048576 35360159310457889357824 75557863725914323419136 1004996173 2147483648 378978 378608 (ep1084 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1086 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz303 (Real.cos qz394)) (@HMul.hMul Real Real Real qz0 qz303 (@Neg.neg Real Real.instNeg (Real.sin qz394))) Bool.true 149543209471 1099511627776 5199729898117 26017743648063488 Bool.true 147934602655 549755813888 2605340886709 13008871824031744 (@Enclosure.Real.IsNear.mulLit_ft qz303 (Real.cos qz394) 316157 1048576 1 1048576 473003 1048576 1025701 1550778368 149543209471 1099511627776 5199729898117 26017743648063488 qz571 (@Enclosure.Real.IsNear.recentre' (Real.cos qz394) Bool.true 473003 1048576 8205608 12406226944 473003 1048576 1025701 1550778368 (ep1083 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz303 (@Neg.neg Real Real.instNeg (Real.sin qz394)) 316157 1048576 1 1048576 467915 524288 1025701 1550778368 147934602655 549755813888 2605340886709 13008871824031744 qz571 (@Enclosure.Real.IsNear.neg (Real.sin qz394) Bool.false 467915 524288 1025701 1550778368 (@Enclosure.Real.IsNear.recentre' (Real.sin qz394) Bool.false 935830 1048576 8205608 12406226944 467915 524288 1025701 1550778368 (ep1085 rfl rfl) rfl)) rfl)

noncomputable def ep1087 := @ep1049 149543209471 1099511627776 5199729898117 26017743648063488 Bool.true 147934602655 549755813888 2605340886709 13008871824031744 Bool.true 852162697299035047329792 387518729121 549755813888 9314577297377 3252217956007936 Bool.true 11030457882760383037440 20064286005 1099511627776 74544028438729 26017743648063488 (ep1050 (BSN.head_sum_c_succ qz64 10 11 rfl rfl) (ep1078 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1079 ep1086) rfl rfl

noncomputable abbrev qz395 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 12 1)))

noncomputable def ep1088 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz962 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz306 (Real.cos qz395)) (@HMul.hMul Real Real Real qz0 qz306 (@Neg.neg Real Real.instNeg (Real.sin qz395)))) Bool.false 153277587981 549755813888 2495803434683 13008871824031744 Bool.true 20565536877 274877906944 1243518253075 6504435912015872 (BSN.cpow_neg_s_mk qz61 124004 1000 12 (@Eq.refl Real qz61) rfl)

noncomputable def ep1089 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz308 124004 1000 0 1 11191020447815397 4503599627370496 125000000070989 23663000000000000000 346932824902725122397 1125899906842624000 3875125002200729989 5915750000000000000000 qz392 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 125000000070989 23663000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz861) Bool.false 46938541828353910898688 18889465931478580854784 1000000000567912 189304000000000000000 11191020447815397 4503599627370496 125000000070989 23663000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 212580 524288 24973259072661432 36028797018963968 189304 1000000000000000 rfl rfl rfl rfl (ep244 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1090 := nat_lit 100469551112013328830626520002585616

noncomputable def ep1091 := BSN.cos_dyadic_bound_f 563000286 2147483648 2 1 1048576 378978 ep1090 ep110 ep1090 ep1090 ep111 ep1090 1012746 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 563000286) qz274 0 1 ep1090 ep110 ep1090 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 563000286) qz275 0 1 ep1090 ep111 ep1090 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz968 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 323106371) qz270)

noncomputable def ep1092 := @Enclosure.Real.IsNear.cos_image qz395 qz968 Bool.false 323106371 1048576 43 65536 Bool.false 1012746 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz395 Bool.false 346932824902725122397 1125899906842624000 3875125002200729989 5915750000000000000000 323106371 1048576 43 65536 (ep1089 rfl) rfl) (Enclosure.sfrac_false_div 323106371 1048576) (BSN.cos_reduce0 qz968 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 39617623127117719928832) qz273) 226375608064910080 72057594037927936 Bool.false 1012746 1048576 49 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q0 323106371 1048576 226375608064910080 72057594037927936 49 39617623127117719928832 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1012746 1048576 39617623127117719928832 151115727451828646838272 563000286 2147483648 378978 378608 (ep1091 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1093 := BSN.sin_dyadic_bound_f 563000286 2147483648 2 1 1048576 378978 ep1090 ep106 ep1090 ep1090 ep107 ep1090 271764 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 563000286) qz268 0 1 ep1090 ep106 ep1090 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 563000286) qz269 0 1 ep1090 ep107 ep1090 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1094 := @Enclosure.Real.IsNear.sin_image qz395 qz968 Bool.false 323106371 1048576 43 65536 Bool.false 271764 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz395 Bool.false 346932824902725122397 1125899906842624000 3875125002200729989 5915750000000000000000 323106371 1048576 43 65536 (ep1089 rfl) rfl) (Enclosure.sfrac_false_div 323106371 1048576) (BSN.sin_reduce0 qz968 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 39617623127117719928832) qz273) 226375608064910080 72057594037927936 Bool.false 271764 1048576 49 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q0 323106371 1048576 226375608064910080 72057594037927936 49 39617623127117719928832 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 271764 1048576 39617623127117719928832 151115727451828646838272 563000286 2147483648 378978 378608 (ep1093 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1095 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz306 (Real.cos qz395)) (@HMul.hMul Real Real Real qz0 qz306 (@Neg.neg Real Real.instNeg (Real.sin qz395))) Bool.false 153277587981 549755813888 2495803434683 13008871824031744 Bool.true 20565536877 274877906944 1243518253075 6504435912015872 (@Enclosure.Real.IsNear.mulLit_ff qz306 (Real.cos qz395) 302697 1048576 1 1048576 506373 524288 1025701 1550778368 153277587981 549755813888 2495803434683 13008871824031744 qz573 (@Enclosure.Real.IsNear.recentre' (Real.cos qz395) Bool.false 1012746 1048576 8205608 12406226944 506373 524288 1025701 1550778368 (ep1092 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz306 (@Neg.neg Real Real.instNeg (Real.sin qz395)) 302697 1048576 1 1048576 67941 262144 1025701 1550778368 20565536877 274877906944 1243518253075 6504435912015872 qz573 (@Enclosure.Real.IsNear.neg (Real.sin qz395) Bool.false 67941 262144 1025701 1550778368 (@Enclosure.Real.IsNear.recentre' (Real.sin qz395) Bool.false 271764 1048576 8205608 12406226944 67941 262144 1025701 1550778368 (ep1094 rfl rfl) rfl)) rfl)

noncomputable def ep1096 := @ep1047 153277587981 549755813888 2495803434683 13008871824031744 Bool.true 20565536877 274877906944 1243518253075 6504435912015872 Bool.true 128775429193474580152320 58560285285 137438953472 39754112624191 13008871824031744 Bool.true 28127275869097817014272 102326433513 1099511627776 79518101451029 26017743648063488 (ep1048 (BSN.head_sum_c_succ qz64 11 12 rfl rfl) (ep1087 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1088 ep1095) rfl rfl

noncomputable abbrev qz396 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 13 1)))

noncomputable def ep1097 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz961 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz309 (Real.cos qz396)) (@HMul.hMul Real Real Real qz0 qz309 (@Neg.neg Real Real.instNeg (Real.sin qz396)))) Bool.true 27553443489 137438953472 598838838857 3252217956007936 Bool.false 105363718785 549755813888 2394960727577 13008871824031744 (BSN.cpow_neg_s_mk qz61 124004 1000 13 (@Eq.refl Real qz61) rfl)

noncomputable def ep1098 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz311 124004 1000 0 1 11551497052968677 4503599627370496 125000000070989 23663000000000000000 358107960139081955677 1125899906842624000 3875125002200729989 5915750000000000000000 qz392 (BSN.isNear_log_sfrac 13 1 11551497052968677 4503599627370496 125000000070989 23663000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz863) Bool.false 48450490295254733815808 18889465931478580854784 1000000000567912 189304000000000000000 11551497052968677 4503599627370496 125000000070989 23663000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 254545 524288 24973259072661432 36028797018963968 189304 1000000000000000 rfl rfl rfl rfl (ep259 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1099 := nat_lit 257462894839101251909151059829600188225870478962293661646304710097539239918721

noncomputable def ep1100 := nat_lit 51903504974906991762335746016463418828386091701983353845636856392016346241

noncomputable def ep1101 := nat_lit 772284877507353941743928507996767637839954664703477018231222856579833687063681

noncomputable def ep1102 := BSN.cos_dyadic_bound_f 1638323217 2147483648 3 2 1048576 378978 ep1099 ep95 ep1100 ep1101 ep97 ep1100 757944 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1638323217) qz274 0 2 ep1099 ep95 ep1100 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1638323217) qz275 0 2 ep1101 ep97 ep1100 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz969 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 333514027) qz270)

noncomputable def ep1103 := @Enclosure.Real.IsNear.cos_image qz396 qz969 Bool.false 333514027 1048576 43 65536 Bool.true 757944 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz396 Bool.false 358107960139081955677 1125899906842624000 3875125002200729989 5915750000000000000000 333514027 1048576 43 65536 (ep1098 rfl) rfl) (Enclosure.sfrac_false_div 333514027 1048576) (BSN.cos_reduce2 qz969 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 115286747382300629008384) qz273) 226375608064910080 72057594037927936 Bool.false 757944 1048576 50 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q2 333514027 1048576 226375608064910080 72057594037927936 50 115286747382300629008384 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 757944 1048576 115286747382300629008384 151115727451828646838272 1638323217 2147483648 378978 378608 (ep1102 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1104 := nat_lit 7204408717924531505343867868739769921

noncomputable def ep1105 := BSN.sin_dyadic_bound_f 1638323217 2147483648 2 1 1048576 378978 ep1104 ep106 ep1104 ep1104 ep107 ep1104 724590 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1638323217) qz268 0 1 ep1104 ep106 ep1104 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1638323217) qz269 0 1 ep1104 ep107 ep1104 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1106 := @Enclosure.Real.IsNear.sin_image qz396 qz969 Bool.false 333514027 1048576 43 65536 Bool.true 724590 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz396 Bool.false 358107960139081955677 1125899906842624000 3875125002200729989 5915750000000000000000 333514027 1048576 43 65536 (ep1098 rfl) rfl) (Enclosure.sfrac_false_div 333514027 1048576) (BSN.sin_reduce2 qz969 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 115286747382300629008384) qz273) 226375608064910080 72057594037927936 Bool.false 724590 1048576 50 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q2 333514027 1048576 226375608064910080 72057594037927936 50 115286747382300629008384 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 724590 1048576 115286747382300629008384 151115727451828646838272 1638323217 2147483648 378978 378608 (ep1105 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1107 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz309 (Real.cos qz396)) (@HMul.hMul Real Real Real qz0 qz309 (@Neg.neg Real Real.instNeg (Real.sin qz396))) Bool.true 27553443489 137438953472 598838838857 3252217956007936 Bool.false 105363718785 549755813888 2394960727577 13008871824031744 (@Enclosure.Real.IsNear.mulLit_ft qz309 (Real.cos qz396) 290823 1048576 1 1048576 94743 131072 1025701 1550778368 27553443489 137438953472 598838838857 3252217956007936 qz575 (@Enclosure.Real.IsNear.recentre' (Real.cos qz396) Bool.true 757944 1048576 8205608 12406226944 94743 131072 1025701 1550778368 (ep1103 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz309 (@Neg.neg Real Real.instNeg (Real.sin qz396)) 290823 1048576 1 1048576 362295 524288 1025701 1550778368 105363718785 549755813888 2394960727577 13008871824031744 qz575 (@Enclosure.Real.IsNear.neg (Real.sin qz396) Bool.true 362295 524288 1025701 1550778368 (@Enclosure.Real.IsNear.recentre' (Real.sin qz396) Bool.true 724590 1048576 8205608 12406226944 362295 524288 1025701 1550778368 (ep1106 rfl rfl) rfl)) rfl)

noncomputable def ep1108 := @ep1045 27553443489 137438953472 598838838857 3252217956007936 Bool.false 105363718785 549755813888 2394960727577 13008871824031744 Bool.true 11835380762270213603328 43056864387 68719476736 42149467979619 13008871824031744 Bool.false 59594082211632424943616 108401004057 1099511627776 84308022906183 26017743648063488 (ep1046 (BSN.head_sum_c_succ qz64 12 13 rfl rfl) (ep1096 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1097 ep1107) rfl rfl

noncomputable abbrev qz397 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 14 1)))

noncomputable def ep1109 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz960 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz312 (Real.cos qz397)) (@HMul.hMul Real Real Real qz0 qz312 (@Neg.neg Real Real.instNeg (Real.sin qz397)))) Bool.false 126931302719 549755813888 2310290161931 13008871824031744 Bool.true 148003334375 1099511627776 4611641838579 26017743648063488 (BSN.cpow_neg_s_mk qz61 124004 1000 14 (@Eq.refl Real qz61) rfl)

noncomputable def ep1110 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz314 124004 1000 0 1 11885250371606245 4503599627370496 125000000070989 23663000000000000000 73690929354033040249 225179981368524800 3875125002200729989 5915750000000000000000 qz392 (BSN.isNear_log_sfrac 14 1 11885250371606245 4503599627370496 125000000070989 23663000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz866) Bool.false 49850353174629559828480 18889465931478580854784 1000000000567912 189304000000000000000 11885250371606245 4503599627370496 125000000070989 23663000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 293399 524288 24973259072661432 36028797018963968 189304 1000000000000000 rfl rfl rfl rfl (ep269 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1111 := nat_lit 1650800859789553662075120171843993856

noncomputable def ep1112 := BSN.cos_dyadic_bound_f 1133505604 2147483648 2 1 1048576 378978 ep1111 ep110 ep1111 ep1111 ep111 ep1111 905866 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1133505604) qz274 0 1 ep1111 ep110 ep1111 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1133505604) qz275 0 1 ep1111 ep111 ep1111 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz970 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 171575065) qz279)

noncomputable def ep1113 := @Enclosure.Real.IsNear.cos_image qz397 qz970 Bool.false 171575065 524288 43 65536 Bool.false 905866 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz397 Bool.false 73690929354033040249 225179981368524800 3875125002200729989 5915750000000000000000 171575065 524288 43 65536 (ep1110 rfl) rfl) (Enclosure.sfrac_false_div 171575065 524288) (BSN.cos_reduce0 qz970 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 39881682965996356239360) qz281) 226375608064910080 72057594037927936 Bool.false 905866 1048576 52 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q0 171575065 524288 226375608064910080 72057594037927936 52 39881682965996356239360 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 905866 1048576 39881682965996356239360 75557863725914323419136 1133505604 2147483648 378978 378608 (ep1112 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1114 := BSN.sin_dyadic_bound_f 1133505604 2147483648 2 1 1048576 378978 ep1111 ep106 ep1111 ep1111 ep107 ep1111 528125 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1133505604) qz268 0 1 ep1111 ep106 ep1111 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1133505604) qz269 0 1 ep1111 ep107 ep1111 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1115 := @Enclosure.Real.IsNear.sin_image qz397 qz970 Bool.false 171575065 524288 43 65536 Bool.false 528125 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz397 Bool.false 73690929354033040249 225179981368524800 3875125002200729989 5915750000000000000000 171575065 524288 43 65536 (ep1110 rfl) rfl) (Enclosure.sfrac_false_div 171575065 524288) (BSN.sin_reduce0 qz970 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 39881682965996356239360) qz281) 226375608064910080 72057594037927936 Bool.false 528125 1048576 52 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q0 171575065 524288 226375608064910080 72057594037927936 52 39881682965996356239360 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 528125 1048576 39881682965996356239360 75557863725914323419136 1133505604 2147483648 378978 378608 (ep1114 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1116 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz312 (Real.cos qz397)) (@HMul.hMul Real Real Real qz0 qz312 (@Neg.neg Real Real.instNeg (Real.sin qz397))) Bool.false 126931302719 549755813888 2310290161931 13008871824031744 Bool.true 148003334375 1099511627776 4611641838579 26017743648063488 (@Enclosure.Real.IsNear.mulLit_ff qz312 (Real.cos qz397) 280243 1048576 1 1048576 452933 524288 1025701 1550778368 126931302719 549755813888 2310290161931 13008871824031744 qz576 (@Enclosure.Real.IsNear.recentre' (Real.cos qz397) Bool.false 905866 1048576 8205608 12406226944 452933 524288 1025701 1550778368 (ep1113 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz312 (@Neg.neg Real Real.instNeg (Real.sin qz397)) 280243 1048576 1 1048576 528125 1048576 1025701 1550778368 148003334375 1099511627776 4611641838579 26017743648063488 qz576 (@Enclosure.Real.IsNear.neg (Real.sin qz397) Bool.false 528125 1048576 1025701 1550778368 (@Enclosure.Real.IsNear.recentre' (Real.sin qz397) Bool.false 528125 1048576 8205608 12406226944 528125 1048576 1025701 1550778368 (ep1115 rfl rfl) rfl)) rfl)

noncomputable def ep1117 := @ep1043 126931302719 549755813888 2310290161931 13008871824031744 Bool.true 148003334375 1099511627776 4611641838579 26017743648063488 Bool.true 14948108820271933161472 217523612377 549755813888 22229879070775 6504435912015872 Bool.true 43543222671667015712768 19801165159 549755813888 44459832372381 13008871824031744 (ep1044 (BSN.head_sum_c_succ qz64 13 14 rfl rfl) (ep1108 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1109 ep1116) rfl rfl

noncomputable abbrev qz398 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 15 1)))

noncomputable def ep1118 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz959 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz315 (Real.cos qz398)) (@HMul.hMul Real Real Real qz0 qz315 (@Neg.neg Real Real.instNeg (Real.sin qz398)))) Bool.true 267490212813 1099511627776 4466584320631 26017743648063488 Bool.true 11887425087 137438953472 556439651625 3252217956007936 (BSN.cpow_neg_s_mk qz61 124004 1000 15 (@Eq.refl Real qz61) rfl)

noncomputable def ep1119 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz317 124004 1000 0 1 12195965485668069 4503599627370496 125000000070989 23663000000000000000 378087126021195807069 1125899906842624000 3875125002200729989 5915750000000000000000 qz392 (BSN.isNear_log_sfrac 15 1 12195965485668069 4503599627370496 125000000070989 23663000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz869) Bool.false 51153586820399524478976 18889465931478580854784 1000000000567912 189304000000000000000 12195965485668069 4503599627370496 125000000070989 23663000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 329571 524288 24973259072661432 36028797018963968 189304 1000000000000000 rfl rfl rfl rfl (ep284 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1120 := nat_lit 3124998476396702051596339673783912061938454200349627639423599315780217880715520

noncomputable def ep1121 := nat_lit 2357445305894365074330006494258827771377927523341889261061295407861377802496

noncomputable def ep1122 := nat_lit 8180703002924676401203402944633826822018482451592185520639137063049747456860416

noncomputable def ep1123 := BSN.sin_dyadic_bound_f 2639703834 2147483648 3 2 1048576 378978 ep1120 ep88 ep1121 ep1122 ep91 ep1121 987993 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2639703834) qz268 0 2 ep1120 ep88 ep1121 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2639703834) qz269 0 2 ep1122 ep91 ep1121 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz971 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 352121075) qz270)

noncomputable def ep1124 := @Enclosure.Real.IsNear.cos_image qz398 qz971 Bool.false 352121075 1048576 43 65536 Bool.true 987993 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz398 Bool.false 378087126021195807069 1125899906842624000 3875125002200729989 5915750000000000000000 352121075 1048576 43 65536 (ep1119 rfl) rfl) (Enclosure.sfrac_false_div 352121075 1048576) (BSN.cos_reduce1 qz971 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 185752643813795807887360) qz273) 226375608064910080 72057594037927936 Bool.false 987993 1048576 53 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q1 352121075 1048576 226375608064910080 72057594037927936 53 185752643813795807887360 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 987993 1048576 185752643813795807887360 151115727451828646838272 2639703834 2147483648 378978 378608 (ep1123 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1125 := nat_lit 1737158018134120857586557599432955068975309190204611750462471306725837212754176

noncomputable def ep1126 := nat_lit 5206759163790573842611012785310347551383171715567151472865291329361788882657536

noncomputable def ep1127 := BSN.cos_dyadic_bound_f 2639703834 2147483648 3 2 1048576 378978 ep1125 ep95 ep1121 ep1126 ep97 ep1121 351256 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2639703834) qz274 0 2 ep1125 ep95 ep1121 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2639703834) qz275 0 2 ep1126 ep97 ep1121 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1128 := @Enclosure.Real.IsNear.sin_image qz398 qz971 Bool.false 352121075 1048576 43 65536 Bool.false 351256 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz398 Bool.false 378087126021195807069 1125899906842624000 3875125002200729989 5915750000000000000000 352121075 1048576 43 65536 (ep1119 rfl) rfl) (Enclosure.sfrac_false_div 352121075 1048576) (BSN.sin_reduce1 qz971 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 185752643813795807887360) qz273) 226375608064910080 72057594037927936 Bool.false 351256 1048576 53 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q1 352121075 1048576 226375608064910080 72057594037927936 53 185752643813795807887360 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 351256 1048576 185752643813795807887360 151115727451828646838272 2639703834 2147483648 378978 378608 (ep1127 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1129 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz315 (Real.cos qz398)) (@HMul.hMul Real Real Real qz0 qz315 (@Neg.neg Real Real.instNeg (Real.sin qz398))) Bool.true 267490212813 1099511627776 4466584320631 26017743648063488 Bool.true 11887425087 137438953472 556439651625 3252217956007936 (@Enclosure.Real.IsNear.mulLit_ft qz315 (Real.cos qz398) 270741 1048576 1 1048576 987993 1048576 1025701 1550778368 267490212813 1099511627776 4466584320631 26017743648063488 qz579 (@Enclosure.Real.IsNear.recentre' (Real.cos qz398) Bool.true 987993 1048576 8205608 12406226944 987993 1048576 1025701 1550778368 (ep1124 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz315 (@Neg.neg Real Real.instNeg (Real.sin qz398)) 270741 1048576 1 1048576 43907 131072 1025701 1550778368 11887425087 137438953472 556439651625 3252217956007936 qz579 (@Enclosure.Real.IsNear.neg (Real.sin qz398) Bool.false 43907 131072 1025701 1550778368 (@Enclosure.Real.IsNear.recentre' (Real.sin qz398) Bool.false 351256 1048576 8205608 12406226944 43907 131072 1025701 1550778368 (ep1128 rfl rfl) rfl)) rfl)

noncomputable def ep1130 := @ep1041 267490212813 1099511627776 4466584320631 26017743648063488 Bool.true 11887425087 137438953472 556439651625 3252217956007936 Bool.true 386224040776436071530496 702537437567 1099511627776 93386100603731 26017743648063488 Bool.true 9256632470715502690304 67350865507 549755813888 46685590978881 13008871824031744 (ep1042 (BSN.head_sum_c_succ qz64 14 15 rfl rfl) (ep1117 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1118 ep1129) rfl rfl

noncomputable abbrev qz399 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 16 1)))

noncomputable def ep1131 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz958 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz318 (Real.cos qz399)) (@HMul.hMul Real Real Real qz0 qz318 (@Neg.neg Real Real.instNeg (Real.sin qz399)))) Bool.true 13133626443 274877906944 1075160213371 6504435912015872 Bool.false 269809896321 1099511627776 4320253765393 26017743648063488 (BSN.cpow_neg_s_mk qz61 124004 1000 16 (@Eq.refl Real qz61) rfl)

noncomputable def ep1132 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz320 124004 1000 0 1 3121657384082679 1125899906842624 31250000023663 5915750000000000000 96774500563947131679 281474976710656000 968781250733576663 1478937500000000000000 qz392 (BSN.isNear_log_sfrac 16 1 3121657384082679 1125899906842624 31250000023663 5915750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz871) Bool.false 52372720210750067441664 18889465931478580854784 1000000000757216 189304000000000000000 3121657384082679 1125899906842624 31250000023663 5915750000000000000 (BSN.log_rat_reduce_isNear 16 1 4 32 32 0 524288 24973259072661432 36028797018963968 189304 1000000000000000 rfl rfl rfl rfl (ep295 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1133 := nat_lit 2749782836090496817484098208168439788213337602936825472733763023936288245353601

noncomputable def ep1134 := nat_lit 5897587616252430792163514061340152746407674343685411911092037795818890529921

noncomputable def ep1135 := nat_lit 8237553333038985590867967596382639059147197460123105594379104996217226955000961

noncomputable def ep1136 := BSN.cos_dyadic_bound_f 2960290287 2147483648 3 2 1048576 378978 ep1133 ep95 ep1134 ep1135 ep97 ep1134 200404 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2960290287) qz274 0 2 ep1133 ep95 ep1134 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2960290287) qz275 0 2 ep1135 ep97 ep1134 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz628 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 90128277) (@Nat.cast Real Real.instNatCast 262144))

noncomputable def ep1137 := @Enclosure.Real.IsNear.cos_image qz399 qz628 Bool.false 90128277 262144 687 1048576 Bool.true 200404 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz399 Bool.false 96774500563947131679 281474976710656000 968781250733576663 1478937500000000000000 90128277 262144 687 1048576 (ep1132 rfl) rfl) (Enclosure.sfrac_false_div 90128277 262144) (BSN.cos_reduce2 qz628 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 52077977484057257181184) qz578) 226375608064910080 72057594037927936 Bool.false 200404 1048576 54 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q2 90128277 262144 226375608064910080 72057594037927936 54 52077977484057257181184 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 200404 1048576 52077977484057257181184 37778931862957161709568 2960290287 2147483648 378978 378608 (ep1136 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1138 := nat_lit 4944891034869892326837645963454119496586881545811337521391899812848663729212545

noncomputable def ep1139 := nat_lit 12941356616137690253768427071994809862804791623425631412932255258172317277555841

noncomputable def ep1140 := BSN.sin_dyadic_bound_f 2960290287 2147483648 3 2 1048576 378978 ep1138 ep88 ep1134 ep1139 ep91 ep1134 1029247 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2960290287) qz268 0 2 ep1138 ep88 ep1134 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2960290287) qz269 0 2 ep1139 ep91 ep1134 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1141 := @Enclosure.Real.IsNear.sin_image qz399 qz628 Bool.false 90128277 262144 687 1048576 Bool.true 1029247 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz399 Bool.false 96774500563947131679 281474976710656000 968781250733576663 1478937500000000000000 90128277 262144 687 1048576 (ep1132 rfl) rfl) (Enclosure.sfrac_false_div 90128277 262144) (BSN.sin_reduce2 qz628 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 52077977484057257181184) qz578) 226375608064910080 72057594037927936 Bool.false 1029247 1048576 54 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q2 90128277 262144 226375608064910080 72057594037927936 54 52077977484057257181184 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1029247 1048576 52077977484057257181184 37778931862957161709568 2960290287 2147483648 378978 378608 (ep1140 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1142 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz318 (Real.cos qz399)) (@HMul.hMul Real Real Real qz0 qz318 (@Neg.neg Real Real.instNeg (Real.sin qz399))) Bool.true 13133626443 274877906944 1075160213371 6504435912015872 Bool.false 269809896321 1099511627776 4320253765393 26017743648063488 (@Enclosure.Real.IsNear.mulLit_ft qz318 (Real.cos qz399) 262143 1048576 1 1048576 50101 262144 16387553 24812453888 13133626443 274877906944 1075160213371 6504435912015872 qz580 (@Enclosure.Real.IsNear.recentre' (Real.cos qz399) Bool.true 200404 1048576 131100424 198499631104 50101 262144 16387553 24812453888 (ep1137 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz318 (@Neg.neg Real Real.instNeg (Real.sin qz399)) 262143 1048576 1 1048576 1029247 1048576 16387553 24812453888 269809896321 1099511627776 4320253765393 26017743648063488 qz580 (@Enclosure.Real.IsNear.neg (Real.sin qz399) Bool.true 1029247 1048576 16387553 24812453888 (@Enclosure.Real.IsNear.recentre' (Real.sin qz399) Bool.true 1029247 1048576 131100424 198499631104 1029247 1048576 16387553 24812453888 (ep1141 rfl rfl) rfl)) rfl)

noncomputable def ep1143 := @ep1039 13133626443 274877906944 1075160213371 6504435912015872 Bool.false 269809896321 1099511627776 4320253765393 26017743648063488 Bool.true 207552595377162882646016 755071943339 1099511627776 97686741457215 26017743648063488 Bool.false 74276499381264230383616 135108165307 1099511627776 97691435723155 26017743648063488 (ep1040 (BSN.head_sum_c_succ qz64 15 16 rfl rfl) (ep1130 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1131 ep1142) rfl rfl

theorem EMRow40.d18 : Enclosure.Complex.IsNear (BSN.headSumC qz64 17) Bool.true 755071943339 1099511627776 97686741457215 26017743648063488 Bool.false 135108165307 1099511627776 97691435723155 26017743648063488 := ep1038 (BSN.head_sum_c_succ qz64 16 17 rfl rfl) (ep1143 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz972 := (@Nat.cast Complex Complex.instNatCast 24)

noncomputable def ep1144 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 25) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 24) (@HPow.hPow Complex Complex Complex qz16 qz972 qz65)) Bool.false 662294107461 1099511627776 128397876462363 26017743648063488 Bool.false 111037628441 1099511627776 128350589506313 26017743648063488

noncomputable def ep1145 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 24) (@HPow.hPow Complex Complex Complex qz16 qz972 qz65) Bool.false 175541804683 274877906944 31220202908279 6504435912015872 Bool.true 13728518183 137438953472 7800844693893 1626108978003968 Bool.true

noncomputable def ep1146 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 24) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 23) (@HPow.hPow Complex Complex Complex qz16 qz874 qz65)) Bool.false 175541804683 274877906944 31220202908279 6504435912015872 Bool.true 13728518183 137438953472 7800844693893 1626108978003968

noncomputable def ep1147 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 23) (@HPow.hPow Complex Complex Complex qz16 qz874 qz65) Bool.false 133366881841 274877906944 30318584979781 6504435912015872 Bool.true 16567307467 68719476736 15151062392007 3252217956007936 Bool.false

noncomputable def ep1148 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 23) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 22) (@HPow.hPow Complex Complex Complex qz16 qz875 qz65)) Bool.false 133366881841 274877906944 30318584979781 6504435912015872 Bool.true 16567307467 68719476736 15151062392007 3252217956007936

noncomputable def ep1149 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 22) (@HPow.hPow Complex Complex Complex qz16 qz875 qz65) Bool.false 299137986205 1099511627776 117580678043615 26017743648063488 Bool.true 258698614705 1099511627776 117538965380475 26017743648063488 Bool.false

noncomputable def ep1150 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 22) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 21) (@HPow.hPow Complex Complex Complex qz16 qz876 qz65)) Bool.false 299137986205 1099511627776 117580678043615 26017743648063488 Bool.true 258698614705 1099511627776 117538965380475 26017743648063488

noncomputable def ep1151 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 21) (@HPow.hPow Complex Complex Complex qz16 qz876 qz65) Bool.false 93555767651 1099511627776 113782943411817 26017743648063488 Bool.true 134990222367 1099511627776 113758164559389 26017743648063488 Bool.false

noncomputable def ep1152 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 21) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 20) (@HPow.hPow Complex Complex Complex qz16 qz877 qz65)) Bool.false 93555767651 1099511627776 113782943411817 26017743648063488 Bool.true 134990222367 1099511627776 113758164559389 26017743648063488

noncomputable def ep1153 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 20) (@HPow.hPow Complex Complex Complex qz16 qz877 qz65) Bool.true 41067920011 549755813888 13740352846467 3252217956007936 Bool.false 2312151901 68719476736 54949209015669 13008871824031744 Bool.false

noncomputable def ep1154 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 20) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 19) (@HPow.hPow Complex Complex Complex qz16 qz878 qz65)) Bool.true 41067920011 549755813888 13740352846467 3252217956007936 Bool.false 2312151901 68719476736 54949209015669 13008871824031744

noncomputable def ep1155 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 19) (@HPow.hPow Complex Complex Complex qz16 qz878 qz65) Bool.true 275475754471 1099511627776 105955922437383 26017743648063488 Bool.false 49750804757 274877906944 52967299818547 13008871824031744 Bool.false

noncomputable def ep1156 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 19) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 18) (@HPow.hPow Complex Complex Complex qz16 qz879 qz65)) Bool.true 275475754471 1099511627776 105955922437383 26017743648063488 Bool.false 49750804757 274877906944 52967299818547 13008871824031744

noncomputable def ep1157 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 18) (@HPow.hPow Complex Complex Complex qz16 qz879 qz65) Bool.true 524820961049 1099511627776 101881832858213 26017743648063488 Bool.false 33704501127 137438953472 50938810268297 13008871824031744 Bool.false

noncomputable def ep1158 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 18) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 17) (@HPow.hPow Complex Complex Complex qz16 qz880 qz65)) Bool.true 524820961049 1099511627776 101881832858213 26017743648063488 Bool.false 33704501127 137438953472 50938810268297 13008871824031744

noncomputable def ep1159 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 17) (@HPow.hPow Complex Complex Complex qz16 qz880 qz65) Bool.true 755071943339 1099511627776 97686741457215 26017743648063488 Bool.false 135108165307 1099511627776 97691435723155 26017743648063488 Bool.false

noncomputable abbrev qz400 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 17 1)))

noncomputable def ep1160 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz880 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz321 (Real.cos qz400)) (@HMul.hMul Real Real Real qz0 qz321 (@Neg.neg Real Real.instNeg (Real.sin qz400)))) Bool.false 115125491145 549755813888 2097545700499 13008871824031744 Bool.false 134527843709 1099511627776 4186184813439 26017743648063488 (BSN.cpow_neg_s_mk qz61 124004 1000 17 (@Eq.refl Real qz61) rfl)

noncomputable def ep1161 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz323 124004 1000 0 1 3189913004350711 1125899906842624 31250000023663 5915750000000000000 98890493047876391711 281474976710656000 968781250733576663 1478937500000000000000 qz392 (BSN.isNear_log_sfrac 17 1 3189913004350711 1125899906842624 31250000023663 5915750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz882) Bool.false 53517859495200818200576 18889465931478580854784 1000000000757216 189304000000000000000 3189913004350711 1125899906842624 31250000023663 5915750000000000000 (BSN.log_rat_reduce_isNear 17 1 4 34 32 31784 524288 24973259072661432 36028797018963968 189304 1000000000000000 rfl rfl rfl rfl (ep322 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1162 := nat_lit 1613260301700041452392179989070492582486353494001147926180104862952237232619520

noncomputable def ep1163 := nat_lit 628735257572187418871620176376474955543337662422371497203049877867551850496

noncomputable def ep1164 := nat_lit 4224187599749753595682298300613347232774331842359084538523850655548835763388416

noncomputable def ep1165 := BSN.sin_dyadic_bound_f 2237734084 2147483648 3 2 1048576 378978 ep1162 ep88 ep1163 ep1164 ep91 ep1163 905370 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2237734084) qz268 0 2 ep1162 ep88 ep1163 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2237734084) qz269 0 2 ep1164 ep91 ep1163 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz973 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 184197897) qz279)

noncomputable def ep1166 := @Enclosure.Real.IsNear.cos_image qz400 qz973 Bool.false 184197897 524288 43 65536 Bool.false 905370 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz400 Bool.false 98890493047876391711 281474976710656000 968781250733576663 1478937500000000000000 184197897 524288 43 65536 (ep1161 rfl) rfl) (Enclosure.sfrac_false_div 184197897 524288) (BSN.cos_reduce3 qz973 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 78733268678894644363264) qz281) 226375608064910080 72057594037927936 Bool.false 905370 1048576 55 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q3 184197897 524288 226375608064910080 72057594037927936 55 78733268678894644363264 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 905370 1048576 78733268678894644363264 75557863725914323419136 2237734084 2147483648 378978 378608 (ep1165 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1167 := nat_lit 896535161058944001292931825117552090250437868961714346321037390474739596722176

noncomputable def ep1168 := nat_lit 2688348012661687629041052234999903320840226931560298295968706071668483686465536

noncomputable def ep1169 := BSN.cos_dyadic_bound_f 2237734084 2147483648 3 2 1048576 378978 ep1167 ep95 ep1163 ep1168 ep97 ep1163 528977 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2237734084) qz274 0 2 ep1167 ep95 ep1163 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2237734084) qz275 0 2 ep1168 ep97 ep1163 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1170 := @Enclosure.Real.IsNear.sin_image qz400 qz973 Bool.false 184197897 524288 43 65536 Bool.true 528977 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz400 Bool.false 98890493047876391711 281474976710656000 968781250733576663 1478937500000000000000 184197897 524288 43 65536 (ep1161 rfl) rfl) (Enclosure.sfrac_false_div 184197897 524288) (BSN.sin_reduce3 qz973 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 78733268678894644363264) qz281) 226375608064910080 72057594037927936 Bool.false 528977 1048576 55 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q3 184197897 524288 226375608064910080 72057594037927936 55 78733268678894644363264 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 528977 1048576 78733268678894644363264 75557863725914323419136 2237734084 2147483648 378978 378608 (ep1169 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1171 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz321 (Real.cos qz400)) (@HMul.hMul Real Real Real qz0 qz321 (@Neg.neg Real Real.instNeg (Real.sin qz400))) Bool.false 115125491145 549755813888 2097545700499 13008871824031744 Bool.false 134527843709 1099511627776 4186184813439 26017743648063488 (@Enclosure.Real.IsNear.mulLit_ff qz321 (Real.cos qz400) 254317 1048576 1 1048576 452685 524288 1025701 1550778368 115125491145 549755813888 2097545700499 13008871824031744 qz581 (@Enclosure.Real.IsNear.recentre' (Real.cos qz400) Bool.false 905370 1048576 8205608 12406226944 452685 524288 1025701 1550778368 (ep1166 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz321 (@Neg.neg Real Real.instNeg (Real.sin qz400)) 254317 1048576 1 1048576 528977 1048576 1025701 1550778368 134527843709 1099511627776 4186184813439 26017743648063488 qz581 (@Enclosure.Real.IsNear.neg (Real.sin qz400) Bool.true 528977 1048576 1025701 1550778368 (@Enclosure.Real.IsNear.recentre' (Real.sin qz400) Bool.true 528977 1048576 8205608 12406226944 528977 1048576 1025701 1550778368 (ep1170 rfl rfl) rfl)) rfl)

noncomputable def ep1172 := @ep1159 115125491145 549755813888 2097545700499 13008871824031744 Bool.false 134527843709 1099511627776 4186184813439 26017743648063488 Bool.true 288523374586975341248512 524820961049 1099511627776 101881832858213 26017743648063488 Bool.false 296467927180206372028416 33704501127 137438953472 50938810268297 13008871824031744 EMRow40.d18 (ep1160 ep1171) rfl rfl

noncomputable abbrev qz401 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 18 1)))

noncomputable def ep1173 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz879 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz324 (Real.cos qz401)) (@HMul.hMul Real Real Real qz0 qz324 (@Neg.neg Real Real.instNeg (Real.sin qz401)))) Bool.false 124672603289 549755813888 2037044789585 13008871824031744 Bool.true 17658197497 274877906944 1014244775125 6504435912015872 (BSN.cpow_neg_s_mk qz61 124004 1000 18 (@Eq.refl Real qz61) rfl)

noncomputable def ep1174 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz326 124004 1000 0 1 3254268794313975 1125899906842624 31250000023663 5915750000000000000 4035423475701101559 11258999068426240 968781250733576663 1478937500000000000000 qz392 (BSN.isNear_log_sfrac 18 1 3254268794313975 1125899906842624 31250000023663 5915750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz885) Bool.false 54597570484265130393600 18889465931478580854784 1000000000757216 189304000000000000000 3254268794313975 1125899906842624 31250000023663 5915750000000000000 (BSN.log_rat_reduce_isNear 18 1 4 36 32 61752 524288 24973259072661432 36028797018963968 189304 1000000000000000 rfl rfl rfl rfl (ep337 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1175 := nat_lit 123486569959432677925767694769629456

noncomputable def ep1176 := BSN.cos_dyadic_bound_f 592795546 2147483648 2 1 1048576 378978 ep1175 ep110 ep1175 ep1175 ep111 ep1175 1008878 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 592795546) qz274 0 1 ep1175 ep110 ep1175 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 592795546) qz275 0 1 ep1175 ep111 ep1175 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz974 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 187914049) qz279)

noncomputable def ep1177 := @Enclosure.Real.IsNear.cos_image qz401 qz974 Bool.false 187914049 524288 687 1048576 Bool.false 1008878 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz401 Bool.false 4035423475701101559 11258999068426240 968781250733576663 1478937500000000000000 187914049 524288 687 1048576 (ep1174 rfl) rfl) (Enclosure.sfrac_false_div 187914049 524288) (BSN.cos_reduce0 qz974 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 20857139071684714692608) qz281) 226375608064910080 72057594037927936 Bool.false 1008878 1048576 57 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q0 187914049 524288 226375608064910080 72057594037927936 57 20857139071684714692608 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1008878 1048576 20857139071684714692608 75557863725914323419136 592795546 2147483648 378978 378608 (ep1176 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1178 := BSN.sin_dyadic_bound_f 592795546 2147483648 2 1 1048576 378978 ep1175 ep106 ep1175 ep1175 ep107 ep1175 285788 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 592795546) qz268 0 1 ep1175 ep106 ep1175 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 592795546) qz269 0 1 ep1175 ep107 ep1175 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1179 := @Enclosure.Real.IsNear.sin_image qz401 qz974 Bool.false 187914049 524288 687 1048576 Bool.false 285788 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz401 Bool.false 4035423475701101559 11258999068426240 968781250733576663 1478937500000000000000 187914049 524288 687 1048576 (ep1174 rfl) rfl) (Enclosure.sfrac_false_div 187914049 524288) (BSN.sin_reduce0 qz974 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 20857139071684714692608) qz281) 226375608064910080 72057594037927936 Bool.false 285788 1048576 57 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q0 187914049 524288 226375608064910080 72057594037927936 57 20857139071684714692608 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 285788 1048576 20857139071684714692608 75557863725914323419136 592795546 2147483648 378978 378608 (ep1178 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1180 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz324 (Real.cos qz401)) (@HMul.hMul Real Real Real qz0 qz324 (@Neg.neg Real Real.instNeg (Real.sin qz401))) Bool.false 124672603289 549755813888 2037044789585 13008871824031744 Bool.true 17658197497 274877906944 1014244775125 6504435912015872 (@Enclosure.Real.IsNear.mulLit_ff qz324 (Real.cos qz401) 247151 1048576 1 1048576 504439 524288 16387553 24812453888 124672603289 549755813888 2037044789585 13008871824031744 qz583 (@Enclosure.Real.IsNear.recentre' (Real.cos qz401) Bool.false 1008878 1048576 131100424 198499631104 504439 524288 16387553 24812453888 (ep1177 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz324 (@Neg.neg Real Real.instNeg (Real.sin qz401)) 247151 1048576 1 1048576 71447 262144 16387553 24812453888 17658197497 274877906944 1014244775125 6504435912015872 qz583 (@Enclosure.Real.IsNear.neg (Real.sin qz401) Bool.false 71447 262144 16387553 24812453888 (@Enclosure.Real.IsNear.recentre' (Real.sin qz401) Bool.false 285788 1048576 131100424 198499631104 71447 262144 16387553 24812453888 (ep1179 rfl rfl) rfl)) rfl)

noncomputable def ep1181 := @ep1157 124672603289 549755813888 2037044789585 13008871824031744 Bool.true 17658197497 274877906944 1014244775125 6504435912015872 Bool.true 151444397605615459893248 275475754471 1099511627776 105955922437383 26017743648063488 Bool.false 6837698540191879266304 49750804757 274877906944 52967299818547 13008871824031744 (ep1158 (BSN.head_sum_c_succ qz64 17 18 rfl rfl) (ep1172 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1173 ep1180) rfl rfl

noncomputable abbrev qz402 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 19 1)))

noncomputable def ep1182 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz878 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz327 (Real.cos qz402)) (@HMul.hMul Real Real Real qz0 qz327 (@Neg.neg Real Real.instNeg (Real.sin qz402)))) Bool.false 193339914449 1099511627776 3966900334353 26017743648063488 Bool.true 40502197153 274877906944 990954598561 6504435912015872 (BSN.cpow_neg_s_mk qz61 124004 1000 19 (@Eq.refl Real qz61) rfl)

noncomputable def ep1183 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz329 124004 1000 0 1 3315143513283831 1125899906842624 31250000023663 5915750000000000000 102772764055312044831 281474976710656000 968781250733576663 1478937500000000000000 qz392 (BSN.isNear_log_sfrac 19 1 3315143513283831 1125899906842624 31250000023663 5915750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz887) Bool.false 55618878793361701994496 18889465931478580854784 1000000000757216 189304000000000000000 3315143513283831 1125899906842624 31250000023663 5915750000000000000 (BSN.log_rat_reduce_isNear 19 1 4 38 32 90099 524288 24973259072661432 36028797018963968 189304 1000000000000000 rfl rfl rfl rfl (ep348 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1184 := nat_lit 179836009363420274765729307346611272446431953835835136798837128116287730680961

noncomputable def ep1185 := nat_lit 25326401825489449305379861219964528736707734388268869589458811945036874881

noncomputable def ep1186 := nat_lit 539457375286609845398577162317393888281822446038728872657332466724973118293121

noncomputable def ep1187 := BSN.cos_dyadic_bound_f 1497775377 2147483648 3 2 1048576 378978 ep1184 ep95 ep1185 ep1186 ep97 ep1185 803711 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1497775377) qz274 0 2 ep1184 ep95 ep1185 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1497775377) qz275 0 2 ep1186 ep97 ep1185 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz629 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 95714595) (@Nat.cast Real Real.instNatCast 262144))

noncomputable def ep1188 := @Enclosure.Real.IsNear.cos_image qz402 qz629 Bool.false 95714595 262144 43 65536 Bool.false 803711 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz402 Bool.false 102772764055312044831 281474976710656000 968781250733576663 1478937500000000000000 95714595 262144 43 65536 (ep1183 rfl) rfl) (Enclosure.sfrac_false_div 95714595 262144) (BSN.cos_reduce0 qz629 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26349143097647248179200) qz578) 226375608064910080 72057594037927936 Bool.false 803711 1048576 58 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q0 95714595 262144 226375608064910080 72057594037927936 58 26349143097647248179200 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 803711 1048576 26349143097647248179200 37778931862957161709568 1497775377 2147483648 378978 378608 (ep1187 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1189 := nat_lit 5032534334258381322084895716516952641

noncomputable def ep1190 := BSN.sin_dyadic_bound_f 1497775377 2147483648 2 1 1048576 378978 ep1189 ep106 ep1189 ep1189 ep107 ep1189 673468 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1497775377) qz268 0 1 ep1189 ep106 ep1189 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1497775377) qz269 0 1 ep1189 ep107 ep1189 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1191 := @Enclosure.Real.IsNear.sin_image qz402 qz629 Bool.false 95714595 262144 43 65536 Bool.false 673468 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz402 Bool.false 102772764055312044831 281474976710656000 968781250733576663 1478937500000000000000 95714595 262144 43 65536 (ep1183 rfl) rfl) (Enclosure.sfrac_false_div 95714595 262144) (BSN.sin_reduce0 qz629 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26349143097647248179200) qz578) 226375608064910080 72057594037927936 Bool.false 673468 1048576 58 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q0 95714595 262144 226375608064910080 72057594037927936 58 26349143097647248179200 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 673468 1048576 26349143097647248179200 37778931862957161709568 1497775377 2147483648 378978 378608 (ep1190 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1192 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz327 (Real.cos qz402)) (@HMul.hMul Real Real Real qz0 qz327 (@Neg.neg Real Real.instNeg (Real.sin qz402))) Bool.false 193339914449 1099511627776 3966900334353 26017743648063488 Bool.true 40502197153 274877906944 990954598561 6504435912015872 (@Enclosure.Real.IsNear.mulLit_ff qz327 (Real.cos qz402) 240559 1048576 1 1048576 803711 1048576 1025701 1550778368 193339914449 1099511627776 3966900334353 26017743648063488 qz584 (@Enclosure.Real.IsNear.recentre' (Real.cos qz402) Bool.false 803711 1048576 8205608 12406226944 803711 1048576 1025701 1550778368 (ep1188 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz327 (@Neg.neg Real Real.instNeg (Real.sin qz402)) 240559 1048576 1 1048576 168367 262144 1025701 1550778368 40502197153 274877906944 990954598561 6504435912015872 qz584 (@Enclosure.Real.IsNear.neg (Real.sin qz402) Bool.false 168367 262144 1025701 1550778368 (@Enclosure.Real.IsNear.recentre' (Real.sin qz402) Bool.false 673468 1048576 8205608 12406226944 168367 262144 1025701 1550778368 (ep1191 rfl rfl) rfl)) rfl)

noncomputable def ep1193 := @ep1155 193339914449 1099511627776 3966900334353 26017743648063488 Bool.true 40502197153 274877906944 990954598561 6504435912015872 Bool.true 90309311161338347651072 41067920011 549755813888 13740352846467 3252217956007936 Bool.false 2542237900333882802176 2312151901 68719476736 54949209015669 13008871824031744 (ep1156 (BSN.head_sum_c_succ qz64 18 19 rfl rfl) (ep1181 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1182 ep1192) rfl rfl

noncomputable abbrev qz403 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 20 1)))

noncomputable def ep1194 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz877 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz330 (Real.cos qz403)) (@HMul.hMul Real Real Real qz0 qz330 (@Neg.neg Real Real.instNeg (Real.sin qz403)))) Bool.false 175691607673 1099511627776 3860120640081 26017743648063488 Bool.true 171984652783 1099511627776 3859746528051 26017743648063488 (BSN.cpow_neg_s_mk qz61 124004 1000 20 (@Eq.refl Real qz61) rfl)

noncomputable def ep1195 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz332 124004 1000 0 1 3372893643545847 1125899906842624 31250000023663 5915750000000000000 104563075843564802847 281474976710656000 968781250733576663 1478937500000000000000 qz392 (BSN.isNear_log_sfrac 20 1 3372893643545847 1125899906842624 31250000023663 5915750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz890) Bool.false 56587765202795681021952 18889465931478580854784 1000000000757216 189304000000000000000 3372893643545847 1125899906842624 31250000023663 5915750000000000000 (BSN.log_rat_reduce_isNear 20 1 4 40 32 116991 524288 24973259072661432 36028797018963968 189304 1000000000000000 rfl rfl rfl rfl (ep362 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1196 := nat_lit 273815393105189681277069772737296838028134810407896527354689232522638931643201

noncomputable def ep1197 := nat_lit 58704580577170919427892972589326416360175127889712872488592426342503795521

noncomputable def ep1198 := nat_lit 821328770154414701992353532266711861251684080967910156319090512715231787338561

noncomputable def ep1199 := BSN.cos_dyadic_bound_f 1663734409 2147483648 3 2 1048576 378978 ep1196 ep95 ep1197 ep1198 ep97 ep1197 749317 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1663734409) qz274 0 2 ep1196 ep95 ep1197 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1663734409) qz275 0 2 ep1198 ep97 ep1197 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz630 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 97381953) (@Nat.cast Real Real.instNatCast 262144))

noncomputable def ep1200 := @Enclosure.Real.IsNear.cos_image qz403 qz630 Bool.false 97381953 262144 687 1048576 Bool.false 749317 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz403 Bool.false 104563075843564802847 281474976710656000 968781250733576663 1478937500000000000000 97381953 262144 687 1048576 (ep1195 rfl) rfl) (Enclosure.sfrac_false_div 97381953 262144) (BSN.cos_reduce0 qz630 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 29268725255158991159296) qz578) 226375608064910080 72057594037927936 Bool.false 749317 1048576 59 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q0 97381953 262144 226375608064910080 72057594037927936 59 29268725255158991159296 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 749317 1048576 29268725255158991159296 37778931862957161709568 1663734409 2147483648 378978 378608 (ep1199 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1201 := nat_lit 7661891449059489215747660589346476961

noncomputable def ep1202 := BSN.sin_dyadic_bound_f 1663734409 2147483648 2 1 1048576 378978 ep1201 ep106 ep1201 ep1201 ep107 ep1201 733507 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1663734409) qz268 0 1 ep1201 ep106 ep1201 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1663734409) qz269 0 1 ep1201 ep107 ep1201 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1203 := @Enclosure.Real.IsNear.sin_image qz403 qz630 Bool.false 97381953 262144 687 1048576 Bool.false 733507 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz403 Bool.false 104563075843564802847 281474976710656000 968781250733576663 1478937500000000000000 97381953 262144 687 1048576 (ep1195 rfl) rfl) (Enclosure.sfrac_false_div 97381953 262144) (BSN.sin_reduce0 qz630 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 29268725255158991159296) qz578) 226375608064910080 72057594037927936 Bool.false 733507 1048576 59 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q0 97381953 262144 226375608064910080 72057594037927936 59 29268725255158991159296 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 733507 1048576 29268725255158991159296 37778931862957161709568 1663734409 2147483648 378978 378608 (ep1202 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1204 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz330 (Real.cos qz403)) (@HMul.hMul Real Real Real qz0 qz330 (@Neg.neg Real Real.instNeg (Real.sin qz403))) Bool.false 175691607673 1099511627776 3860120640081 26017743648063488 Bool.true 171984652783 1099511627776 3859746528051 26017743648063488 (@Enclosure.Real.IsNear.mulLit_ff qz330 (Real.cos qz403) 234469 1048576 1 1048576 749317 1048576 16387553 24812453888 175691607673 1099511627776 3860120640081 26017743648063488 qz585 (@Enclosure.Real.IsNear.recentre' (Real.cos qz403) Bool.false 749317 1048576 131100424 198499631104 749317 1048576 16387553 24812453888 (ep1200 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz330 (@Neg.neg Real Real.instNeg (Real.sin qz403)) 234469 1048576 1 1048576 733507 1048576 16387553 24812453888 171984652783 1099511627776 3859746528051 26017743648063488 qz585 (@Enclosure.Real.IsNear.neg (Real.sin qz403) Bool.false 733507 1048576 16387553 24812453888 (@Enclosure.Real.IsNear.recentre' (Real.sin qz403) Bool.false 733507 1048576 131100424 198499631104 733507 1048576 16387553 24812453888 (ep1203 rfl rfl) rfl)) rfl)

noncomputable def ep1205 := @ep1153 175691607673 1099511627776 3860120640081 26017743648063488 Bool.true 171984652783 1099511627776 3859746528051 26017743648063488 Bool.false 51432827188892126937088 93555767651 1099511627776 113782943411817 26017743648063488 Bool.true 9276457445536523354112 134990222367 1099511627776 113758164559389 26017743648063488 (ep1154 (BSN.head_sum_c_succ qz64 19 20 rfl rfl) (ep1193 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1194 ep1204) rfl rfl

noncomputable abbrev qz404 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 21 1)))

noncomputable def ep1206 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz876 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz333 (Real.cos qz404)) (@HMul.hMul Real Real Real qz0 qz333 (@Neg.neg Real Real.instNeg (Real.sin qz404)))) Bool.false 102791109277 549755813888 1898867315899 13008871824031744 Bool.true 61854196169 549755813888 1890400410543 13008871824031744 (BSN.cpow_neg_s_mk qz61 124004 1000 21 (@Eq.refl Real qz61) rfl)

noncomputable def ep1207 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz335 124004 1000 0 1 3427826275261687 1125899906842624 31250000023663 5915750000000000000 106266042359387558687 281474976710656000 968781250733576663 1478937500000000000000 qz392 (BSN.isNear_log_sfrac 21 1 3427826275261687 1125899906842624 31250000023663 5915750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz893) Bool.false 57509381830540779323392 18889465931478580854784 1000000000757216 189304000000000000000 3427826275261687 1125899906842624 31250000023663 5915750000000000000 (BSN.log_rat_reduce_isNear 21 1 4 42 32 142571 524288 24973259072661432 36028797018963968 189304 1000000000000000 rfl rfl rfl rfl (ep376 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1208 := nat_lit 1831323819908207427300719259587444736

noncomputable def ep1209 := BSN.cos_dyadic_bound_f 1163298816 2147483648 2 1 1048576 378978 ep1208 ep110 ep1208 ep1208 ep111 ep1208 898453 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1163298816) qz274 0 1 ep1208 ep110 ep1208 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1163298816) qz275 0 1 ep1208 ep111 ep1208 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz631 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 24741991) (@Nat.cast Real Real.instNatCast 65536))

noncomputable def ep1210 := @Enclosure.Real.IsNear.cos_image qz404 qz631 Bool.false 24741991 65536 43 65536 Bool.false 898453 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz404 Bool.false 106266042359387558687 281474976710656000 968781250733576663 1478937500000000000000 24741991 65536 43 65536 (ep1207 rfl) rfl) (Enclosure.sfrac_false_div 24741991 65536) (BSN.cos_reduce0 qz631 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 5116242302066021629952) qz864) 226375608064910080 72057594037927936 Bool.false 898453 1048576 60 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q0 24741991 65536 226375608064910080 72057594037927936 60 5116242302066021629952 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 898453 1048576 5116242302066021629952 9444732965739290427392 1163298816 2147483648 378978 378608 (ep1209 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1211 := BSN.sin_dyadic_bound_f 1163298816 2147483648 2 1 1048576 378978 ep1208 ep106 ep1208 ep1208 ep107 ep1208 540641 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1163298816) qz268 0 1 ep1208 ep106 ep1208 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1163298816) qz269 0 1 ep1208 ep107 ep1208 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1212 := @Enclosure.Real.IsNear.sin_image qz404 qz631 Bool.false 24741991 65536 43 65536 Bool.false 540641 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz404 Bool.false 106266042359387558687 281474976710656000 968781250733576663 1478937500000000000000 24741991 65536 43 65536 (ep1207 rfl) rfl) (Enclosure.sfrac_false_div 24741991 65536) (BSN.sin_reduce0 qz631 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 5116242302066021629952) qz864) 226375608064910080 72057594037927936 Bool.false 540641 1048576 60 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q0 24741991 65536 226375608064910080 72057594037927936 60 5116242302066021629952 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 540641 1048576 5116242302066021629952 9444732965739290427392 1163298816 2147483648 378978 378608 (ep1211 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1213 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz333 (Real.cos qz404)) (@HMul.hMul Real Real Real qz0 qz333 (@Neg.neg Real Real.instNeg (Real.sin qz404))) Bool.false 102791109277 549755813888 1898867315899 13008871824031744 Bool.true 61854196169 549755813888 1890400410543 13008871824031744 (@Enclosure.Real.IsNear.mulLit_ff qz333 (Real.cos qz404) 114409 524288 1 524288 898453 1048576 1025701 1550778368 102791109277 549755813888 1898867315899 13008871824031744 qz586 (@Enclosure.Real.IsNear.recentre' (Real.cos qz404) Bool.false 898453 1048576 8205608 12406226944 898453 1048576 1025701 1550778368 (ep1210 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz333 (@Neg.neg Real Real.instNeg (Real.sin qz404)) 114409 524288 1 524288 540641 1048576 1025701 1550778368 61854196169 549755813888 1890400410543 13008871824031744 qz586 (@Enclosure.Real.IsNear.neg (Real.sin qz404) Bool.false 540641 1048576 1025701 1550778368 (@Enclosure.Real.IsNear.recentre' (Real.sin qz404) Bool.false 540641 1048576 8205608 12406226944 540641 1048576 1025701 1550778368 (ep1212 rfl rfl) rfl)) rfl)

noncomputable def ep1214 := @ep1151 102791109277 549755813888 1898867315899 13008871824031744 Bool.true 61854196169 549755813888 1890400410543 13008871824031744 Bool.false 164452847070947091415040 299137986205 1099511627776 117580678043615 26017743648063488 Bool.true 142221067478845400023040 258698614705 1099511627776 117538965380475 26017743648063488 (ep1152 (BSN.head_sum_c_succ qz64 20 21 rfl rfl) (ep1205 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1206 ep1213) rfl rfl

noncomputable abbrev qz405 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 22 1)))

noncomputable def ep1215 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz875 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz336 (Real.cos qz405)) (@HMul.hMul Real Real Real qz0 qz336 (@Neg.neg Real Real.instNeg (Real.sin qz405)))) Bool.false 234329541159 1099511627776 3693661875509 26017743648063488 Bool.true 6378304767 1099511627776 3669533755581 26017743648063488 (BSN.cpow_neg_s_mk qz61 124004 1000 22 (@Eq.refl Real qz61) rfl)

noncomputable def ep1216 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz338 124004 1000 0 1 3480203401436407 1125899906842624 31250000023663 5915750000000000000 107889785647930053407 281474976710656000 968781250733576663 1478937500000000000000 qz392 (BSN.isNear_log_sfrac 22 1 3480203401436407 1125899906842624 31250000023663 5915750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz896) Bool.false 58388124189833310502912 18889465931478580854784 1000000000757216 189304000000000000000 3480203401436407 1125899906842624 31250000023663 5915750000000000000 (BSN.log_rat_reduce_isNear 22 1 4 44 32 166961 524288 24973259072661432 36028797018963968 189304 1000000000000000 rfl rfl rfl rfl (ep387 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1217 := BSN.cos_dyadic_bound_f 58439032 2147483648 1 0 1048576 378978 0 1 1 0 1 1 1048187 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 58439032) qz274 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 58439032) qz275 0 0 rfl) rfl rfl

noncomputable abbrev qz975 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 401920771) qz270)

noncomputable def ep1218 := @Enclosure.Real.IsNear.cos_image qz405 qz975 Bool.false 401920771 1048576 43 65536 Bool.false 1048187 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz405 Bool.false 107889785647930053407 281474976710656000 968781250733576663 1478937500000000000000 401920771 1048576 43 65536 (ep1216 rfl) rfl) (Enclosure.sfrac_false_div 401920771 1048576) (BSN.cos_reduce0 qz975 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4112281303837459873792) qz273) 226375608064910080 72057594037927936 Bool.false 1048187 1048576 61 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q0 401920771 1048576 226375608064910080 72057594037927936 61 4112281303837459873792 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1048187 1048576 4112281303837459873792 151115727451828646838272 58439032 2147483648 378978 378608 (ep1217 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1219 := BSN.sin_dyadic_bound_f 58439032 2147483648 1 0 1048576 378978 0 1 1 0 1 1 28531 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 58439032) qz268 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 58439032) qz269 0 0 rfl) rfl rfl

noncomputable def ep1220 := @Enclosure.Real.IsNear.sin_image qz405 qz975 Bool.false 401920771 1048576 43 65536 Bool.false 28531 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz405 Bool.false 107889785647930053407 281474976710656000 968781250733576663 1478937500000000000000 401920771 1048576 43 65536 (ep1216 rfl) rfl) (Enclosure.sfrac_false_div 401920771 1048576) (BSN.sin_reduce0 qz975 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4112281303837459873792) qz273) 226375608064910080 72057594037927936 Bool.false 28531 1048576 61 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q0 401920771 1048576 226375608064910080 72057594037927936 61 4112281303837459873792 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 28531 1048576 4112281303837459873792 151115727451828646838272 58439032 2147483648 378978 378608 (ep1219 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1221 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz336 (Real.cos qz405)) (@HMul.hMul Real Real Real qz0 qz336 (@Neg.neg Real Real.instNeg (Real.sin qz405))) Bool.false 234329541159 1099511627776 3693661875509 26017743648063488 Bool.true 6378304767 1099511627776 3669533755581 26017743648063488 (@Enclosure.Real.IsNear.mulLit_ff qz336 (Real.cos qz405) 223557 1048576 1 1048576 1048187 1048576 1025701 1550778368 234329541159 1099511627776 3693661875509 26017743648063488 qz587 (@Enclosure.Real.IsNear.recentre' (Real.cos qz405) Bool.false 1048187 1048576 8205608 12406226944 1048187 1048576 1025701 1550778368 (ep1218 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz336 (@Neg.neg Real Real.instNeg (Real.sin qz405)) 223557 1048576 1 1048576 28531 1048576 1025701 1550778368 6378304767 1099511627776 3669533755581 26017743648063488 qz587 (@Enclosure.Real.IsNear.neg (Real.sin qz405) Bool.false 28531 1048576 1025701 1550778368 (@Enclosure.Real.IsNear.recentre' (Real.sin qz405) Bool.false 28531 1048576 8205608 12406226944 28531 1048576 1025701 1550778368 (ep1220 rfl rfl) rfl)) rfl)

noncomputable def ep1222 := @ep1149 234329541159 1099511627776 3693661875509 26017743648063488 Bool.true 6378304767 1099511627776 3669533755581 26017743648063488 Bool.false 586553749377629462462464 133366881841 274877906944 30318584979781 6504435912015872 Bool.true 291455155214506390454272 16567307467 68719476736 15151062392007 3252217956007936 (ep1150 (BSN.head_sum_c_succ qz64 21 22 rfl rfl) (ep1214 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1215 ep1221) rfl rfl

noncomputable abbrev qz406 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 23 1)))

noncomputable def ep1223 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz874 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz339 (Real.cos qz406)) (@HMul.hMul Real Real Real qz0 qz339 (@Neg.neg Real Real.instNeg (Real.sin qz406)))) Bool.false 21087461421 137438953472 450808964249 3252217956007936 Bool.false 19406096751 137438953472 450626995779 3252217956007936 (BSN.cpow_neg_s_mk qz61 124004 1000 23 (@Eq.refl Real qz61) rfl)

noncomputable def ep1224 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz341 124004 1000 0 1 3530250507853047 1125899906842624 31250000023663 5915750000000000000 109441295993952310047 281474976710656000 968781250733576663 1478937500000000000000 qz392 (BSN.isNear_log_sfrac 23 1 3530250507853047 1125899906842624 31250000023663 5915750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz899) Bool.false 59227775304360265777152 18889465931478580854784 1000000000757216 189304000000000000000 3530250507853047 1125899906842624 31250000023663 5915750000000000000 (BSN.log_rat_reduce_isNear 23 1 4 46 32 190266 524288 24973259072661432 36028797018963968 189304 1000000000000000 rfl rfl rfl rfl (ep402 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1225 := nat_lit 9943146070737635527975935925484379201

noncomputable def ep1226 := BSN.sin_dyadic_bound_f 1775746449 2147483648 2 1 1048576 378978 ep1225 ep106 ep1225 ep1225 ep107 ep1225 771576 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1775746449) qz268 0 1 ep1225 ep106 ep1225 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1775746449) qz269 0 1 ep1225 ep107 ep1225 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz976 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 203850299) qz279)

noncomputable def ep1227 := @Enclosure.Real.IsNear.cos_image qz406 qz976 Bool.false 203850299 524288 43 65536 Bool.false 771576 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz406 Bool.false 109441295993952310047 281474976710656000 968781250733576663 1478937500000000000000 203850299 524288 43 65536 (ep1224 rfl) rfl) (Enclosure.sfrac_false_div 203850299 524288) (BSN.cos_reduce3 qz976 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 62478523823966910414848) qz281) 226375608064910080 72057594037927936 Bool.false 771576 1048576 61 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q3 203850299 524288 226375608064910080 72057594037927936 61 62478523823966910414848 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 771576 1048576 62478523823966910414848 75557863725914323419136 1775746449 2147483648 378978 378608 (ep1226 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1228 := nat_lit 355363980510863348224146255216718683263089438588089540956527920048697275697281

noncomputable def ep1229 := nat_lit 98866153784025280502716710876235973549004036635045999606392015060361398401

noncomputable def ep1230 := nat_lit 1065894209225021994111433332228403577842170307690998530870370976115971104295041

noncomputable def ep1231 := BSN.cos_dyadic_bound_f 1775746449 2147483648 3 2 1048576 378978 ep1228 ep95 ep1229 ep1230 ep97 ep1229 710056 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1775746449) qz274 0 2 ep1228 ep95 ep1229 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1775746449) qz275 0 2 ep1230 ep97 ep1229 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1232 := @Enclosure.Real.IsNear.sin_image qz406 qz976 Bool.false 203850299 524288 43 65536 Bool.true 710056 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz406 Bool.false 109441295993952310047 281474976710656000 968781250733576663 1478937500000000000000 203850299 524288 43 65536 (ep1224 rfl) rfl) (Enclosure.sfrac_false_div 203850299 524288) (BSN.sin_reduce3 qz976 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 62478523823966910414848) qz281) 226375608064910080 72057594037927936 Bool.false 710056 1048576 61 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q3 203850299 524288 226375608064910080 72057594037927936 61 62478523823966910414848 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 710056 1048576 62478523823966910414848 75557863725914323419136 1775746449 2147483648 378978 378608 (ep1231 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1233 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz339 (Real.cos qz406)) (@HMul.hMul Real Real Real qz0 qz339 (@Neg.neg Real Real.instNeg (Real.sin qz406))) Bool.false 21087461421 137438953472 450808964249 3252217956007936 Bool.false 19406096751 137438953472 450626995779 3252217956007936 (@Enclosure.Real.IsNear.mulLit_ff qz339 (Real.cos qz406) 218643 1048576 1 1048576 96447 131072 1025701 1550778368 21087461421 137438953472 450808964249 3252217956007936 qz589 (@Enclosure.Real.IsNear.recentre' (Real.cos qz406) Bool.false 771576 1048576 8205608 12406226944 96447 131072 1025701 1550778368 (ep1227 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz339 (@Neg.neg Real Real.instNeg (Real.sin qz406)) 218643 1048576 1 1048576 88757 131072 1025701 1550778368 19406096751 137438953472 450626995779 3252217956007936 qz589 (@Enclosure.Real.IsNear.neg (Real.sin qz406) Bool.true 88757 131072 1025701 1550778368 (@Enclosure.Real.IsNear.recentre' (Real.sin qz406) Bool.true 710056 1048576 8205608 12406226944 88757 131072 1025701 1550778368 (ep1232 rfl rfl) rfl)) rfl)

noncomputable def ep1234 := @ep1147 21087461421 137438953472 450808964249 3252217956007936 Bool.false 19406096751 137438953472 450626995779 3252217956007936 Bool.false 24126281926217748709376 175541804683 274877906944 31220202908279 6504435912015872 Bool.true 943416585896421490688 13728518183 137438953472 7800844693893 1626108978003968 (ep1148 (BSN.head_sum_c_succ qz64 22 23 rfl rfl) (ep1222 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1223 ep1233) rfl rfl

noncomputable abbrev qz407 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 24 1)))

noncomputable def ep1235 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz972 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz342 (Real.cos qz407)) (@HMul.hMul Real Real Real qz0 qz342 (@Neg.neg Real Real.instNeg (Real.sin qz407)))) Bool.true 39873111271 1099511627776 3517064829247 26017743648063488 Bool.false 220865773905 1099511627776 3537074404025 26017743648063488 (BSN.cpow_neg_s_mk qz61 124004 1000 24 (@Eq.refl Real qz61) rfl)

noncomputable def ep1236 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz344 124004 1000 0 1 3578169457974519 1125899906842624 31250000023663 5915750000000000000 110926831366668063519 281474976710656000 968781250733576663 1478937500000000000000 qz392 (BSN.isNear_log_sfrac 24 1 3578169457974519 1125899906842624 31250000023663 5915750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz901) Bool.false 60031721881041427759104 18889465931478580854784 1000000000757216 189304000000000000000 3578169457974519 1125899906842624 31250000023663 5915750000000000000 (BSN.log_rat_reduce_isNear 24 1 4 48 32 212580 524288 24973259072661432 36028797018963968 189304 1000000000000000 rfl rfl rfl rfl (ep413 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1237 := nat_lit 2860952896657156950842209977219323785102033763626035875710493725266527020307041

noncomputable def ep1238 := nat_lit 6382985815239478171925660414085142206992127883190982214322144914513455665761

noncomputable def ep1239 := nat_lit 8570092718340991896182778610829801070892117035111725662702836885970554149589601

noncomputable def ep1240 := BSN.cos_dyadic_bound_f 2989702571 2147483648 3 2 1048576 378978 ep1237 ep95 ep1238 ep1239 ep97 ep1238 186289 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2989702571) qz274 0 2 ep1237 ep95 ep1238 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2989702571) qz275 0 2 ep1239 ep97 ep1238 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz632 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 51654331) (@Nat.cast Real Real.instNatCast 131072))

noncomputable def ep1241 := @Enclosure.Real.IsNear.cos_image qz407 qz632 Bool.false 51654331 131072 43 65536 Bool.true 186289 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz407 Bool.false 110926831366668063519 281474976710656000 968781250733576663 1478937500000000000000 51654331 131072 43 65536 (ep1236 rfl) rfl) (Enclosure.sfrac_false_div 51654331 131072) (BSN.cos_reduce2 qz632 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26297701926538819141632) qz565) 226375608064910080 72057594037927936 Bool.false 186289 1048576 62 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q2 51654331 131072 226375608064910080 72057594037927936 62 26297701926538819141632 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 186289 1048576 26297701926538819141632 18889465931478580854784 2989702571 2147483648 378978 378608 (ep1240 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1242 := nat_lit 5144608825330690928978437430663514699418067072220311790507430989548137872020065

noncomputable def ep1243 := nat_lit 13463641136927136135046123153924495887283616982099459765839131023716863117546081

noncomputable def ep1244 := BSN.sin_dyadic_bound_f 2989702571 2147483648 3 2 1048576 378978 ep1242 ep88 ep1238 ep1243 ep91 ep1238 1031895 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2989702571) qz268 0 2 ep1242 ep88 ep1238 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2989702571) qz269 0 2 ep1243 ep91 ep1238 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1245 := @Enclosure.Real.IsNear.sin_image qz407 qz632 Bool.false 51654331 131072 43 65536 Bool.true 1031895 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz407 Bool.false 110926831366668063519 281474976710656000 968781250733576663 1478937500000000000000 51654331 131072 43 65536 (ep1236 rfl) rfl) (Enclosure.sfrac_false_div 51654331 131072) (BSN.sin_reduce2 qz632 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26297701926538819141632) qz565) 226375608064910080 72057594037927936 Bool.false 1031895 1048576 62 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q2 51654331 131072 226375608064910080 72057594037927936 62 26297701926538819141632 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1031895 1048576 26297701926538819141632 18889465931478580854784 2989702571 2147483648 378978 378608 (ep1244 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1246 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz342 (Real.cos qz407)) (@HMul.hMul Real Real Real qz0 qz342 (@Neg.neg Real Real.instNeg (Real.sin qz407))) Bool.true 39873111271 1099511627776 3517064829247 26017743648063488 Bool.false 220865773905 1099511627776 3537074404025 26017743648063488 (@Enclosure.Real.IsNear.mulLit_ft qz342 (Real.cos qz407) 214039 1048576 1 1048576 186289 1048576 1025701 1550778368 39873111271 1099511627776 3517064829247 26017743648063488 qz591 (@Enclosure.Real.IsNear.recentre' (Real.cos qz407) Bool.true 186289 1048576 8205608 12406226944 186289 1048576 1025701 1550778368 (ep1241 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz342 (@Neg.neg Real Real.instNeg (Real.sin qz407)) 214039 1048576 1 1048576 1031895 1048576 1025701 1550778368 220865773905 1099511627776 3537074404025 26017743648063488 qz591 (@Enclosure.Real.IsNear.neg (Real.sin qz407) Bool.true 1031895 1048576 1025701 1550778368 (@Enclosure.Real.IsNear.recentre' (Real.sin qz407) Bool.true 1031895 1048576 8205608 12406226944 1031895 1048576 1025701 1550778368 (ep1245 rfl rfl) rfl)) rfl)

noncomputable def ep1247 := @ep1145 39873111271 1099511627776 3517064829247 26017743648063488 Bool.false 220865773905 1099511627776 3537074404025 26017743648063488 Bool.false 182050018040224294109184 662294107461 1099511627776 128397876462363 26017743648063488 Bool.false 15260895448943822897152 111037628441 1099511627776 128350589506313 26017743648063488 (ep1146 (BSN.head_sum_c_succ qz64 23 24 rfl rfl) (ep1234 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1235 ep1246) rfl rfl

theorem EMRow40.d19 : Enclosure.Complex.IsNear (BSN.headSumC qz64 25) Bool.false 662294107461 1099511627776 128397876462363 26017743648063488 Bool.false 111037628441 1099511627776 128350589506313 26017743648063488 := ep1144 (BSN.head_sum_c_succ qz64 24 25 rfl rfl) (ep1247 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

theorem EMRow40.d20 : @Eq Nat (Nat.pow 32 1) 32 := @Eq.refl Nat 32

noncomputable abbrev qz66 := (@HAdd.hAdd Complex Complex Complex qz262 qz391 qz555)

noncomputable def ep1248 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz3 (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2)) qz66) Bool.true 4324661817 62500 0 1 Bool.true 14891371054313 7812500 0 1

noncomputable def ep1249 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.re qz66)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.im qz66)) 480507563 12500 0 1 961062001 31250 0 1

noncomputable def ep1250 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.re qz66) 480507563 31250 0 1 5 2 0 1 480507563 12500

noncomputable abbrev qz67 := (@HAdd.hAdd Complex Complex Complex qz262 qz391 qz592)

noncomputable def ep1251 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz3 (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)) qz67) Bool.true 480507563 31250 0 1 Bool.false 31001 125 0 1

noncomputable def ep1252 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.re qz67)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.im qz67)) 3 4 0 1 961062001 62500 0 1

noncomputable def ep1253 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.re qz67) 1 2 0 1 3 2 0 1 3 4

noncomputable def ep1254 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)) qz64 Bool.false 1 2 0 1 Bool.false 124004 1000 0 1 (BSN.ascPochhammer_one_eval qz64)

noncomputable def ep1255 := ep1254 (@Enclosure.Complex.IsNear.of_eq qz64 (Complex.mk qz345 qz61) Bool.false 1 2 0 1 Bool.false 124004 1000 0 1 (BSN.s_crit_mk qz61 Bool.false 124004 1000 (@Eq.refl Real qz61)) (@Enclosure.Complex.IsNear.mk qz345 qz61 Bool.false 1 2 0 1 Bool.false 124004 1000 0 1 qz346 qz392))

noncomputable def ep1256 := @ep1253 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 124004 1000 0 1 ep1255)

noncomputable def ep1257 := @Enclosure.Complex.IsNear.of_eq qz67 (Complex.mk (Enclosure.sfrac Bool.false 3 2) qz61) Bool.false 3 2 0 1 Bool.false 124004 1000 0 1 (BSN.s_add_nat_mk qz61 Bool.false 124004 1000 1 (@Eq.refl Real qz61))

noncomputable abbrev qz633 := (ep1257 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz61 Bool.false 3 2 0 1 Bool.false 124004 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz392))

noncomputable def ep1258 := ep1256 (@Enclosure.Complex.IsNear.re_isNear qz67 Bool.false 3 2 0 1 Bool.false 124004 1000 0 1 qz633)

noncomputable def ep1259 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.im qz67) 124004 1000 0 1 124004 1000 0 1 961062001 62500

noncomputable def ep1260 := @ep1259 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 124004 1000 0 1 ep1255)

noncomputable def ep1261 := ep1260 (@Enclosure.Complex.IsNear.im_isNear qz67 Bool.false 3 2 0 1 Bool.false 124004 1000 0 1 qz633)

noncomputable def ep1262 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)) qz67 Bool.true 480507563 31250 0 1 Bool.false 31001 125 0 1 (@ep1252 3844060504 480507563 31250 0 1 (ep1258 rfl) (ep1261 rfl) rfl rfl)

noncomputable def ep1263 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.im qz67)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.re qz67)) 31001 500 0 1 93003 500 0 1

noncomputable def ep1264 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.im qz67) 1 2 0 1 124004 1000 0 1 31001 500

noncomputable def ep1265 := @ep1264 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 124004 1000 0 1 ep1255)

noncomputable def ep1266 := ep1265 (@Enclosure.Complex.IsNear.im_isNear qz67 Bool.false 3 2 0 1 Bool.false 124004 1000 0 1 qz633)

noncomputable def ep1267 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.re qz67) 124004 1000 0 1 3 2 0 1 93003 500

noncomputable def ep1268 := @ep1267 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 124004 1000 0 1 ep1255)

noncomputable def ep1269 := ep1268 (@Enclosure.Complex.IsNear.re_isNear qz67 Bool.false 3 2 0 1 Bool.false 124004 1000 0 1 qz633)

noncomputable abbrev qz634 := (ep1251 (BSN.ascPochhammer_succ_eval_c 1 2 qz64 rfl) (ep1262 (@ep1263 62002000 31001 125 0 1 (ep1266 rfl) (ep1269 rfl) rfl rfl)))

noncomputable def ep1270 := @ep1250 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 480507563 31250 0 1 Bool.false 31001 125 0 1 qz634)

noncomputable def ep1271 := @Enclosure.Complex.IsNear.of_eq qz66 (Complex.mk (Enclosure.sfrac Bool.false 5 2) qz61) Bool.false 5 2 0 1 Bool.false 124004 1000 0 1 (BSN.s_add_nat_mk qz61 Bool.false 124004 1000 2 (@Eq.refl Real qz61))

noncomputable abbrev qz635 := (ep1271 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz61 Bool.false 5 2 0 1 Bool.false 124004 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz392))

noncomputable def ep1272 := ep1270 (@Enclosure.Complex.IsNear.re_isNear qz66 Bool.false 5 2 0 1 Bool.false 124004 1000 0 1 qz635)

noncomputable def ep1273 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.im qz66) 31001 125 0 1 124004 1000 0 1 961062001 31250

noncomputable def ep1274 := @ep1273 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 480507563 31250 0 1 Bool.false 31001 125 0 1 qz634)

noncomputable def ep1275 := ep1274 (@Enclosure.Complex.IsNear.im_isNear qz66 Bool.false 5 2 0 1 Bool.false 124004 1000 0 1 qz635)

noncomputable def ep1276 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2)) qz66 Bool.true 4324661817 62500 0 1 Bool.true 14891371054313 7812500 0 1 (@ep1249 27029136356250 4324661817 62500 0 1 (ep1272 rfl) (ep1275 rfl) rfl rfl)

noncomputable def ep1277 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.im qz66)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.re qz66)) 14896214960563 7812500 0 1 31001 50 0 1

noncomputable def ep1278 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.im qz66) 480507563 31250 0 1 124004 1000 0 1 14896214960563 7812500

noncomputable def ep1279 := @ep1278 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 480507563 31250 0 1 Bool.false 31001 125 0 1 qz634)

noncomputable def ep1280 := ep1279 (@Enclosure.Complex.IsNear.im_isNear qz66 Bool.false 5 2 0 1 Bool.false 124004 1000 0 1 qz635)

noncomputable def ep1281 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.re qz66) 31001 125 0 1 5 2 0 1 31001 50

noncomputable def ep1282 := @ep1281 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 480507563 31250 0 1 Bool.false 31001 125 0 1 qz634)

noncomputable def ep1283 := ep1282 (@Enclosure.Complex.IsNear.re_isNear qz66 Bool.false 5 2 0 1 Bool.false 124004 1000 0 1 qz635)

noncomputable abbrev qz636 := (ep1276 (@ep1277 744568552715650 14891371054313 7812500 0 1 (ep1280 rfl) (ep1283 rfl) rfl rfl))

theorem EMRow40.d21 : Enclosure.Complex.IsNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 4324661817 62500 0 1 Bool.true 14891371054313 7812500 0 1 := ep1248 (BSN.ascPochhammer_succ_eval_c 2 3 qz64 rfl) qz636

theorem EMRow40.d22 : @Eq Nat (Nat.pow 32 3) 32768 := @Eq.refl Nat 32768

noncomputable def ep1284 := nat_lit 11819055016201341858655114268754921741803

noncomputable def ep1285 := nat_lit 25529404322578096628106830807040000000000

noncomputable def ep1286 := nat_lit 500757297609279588383878401876578525431525889

noncomputable def ep1287 := nat_lit 82629321354927579413810612221897605120000000000

noncomputable abbrev qz68 := (Complex.Stirling.logGammaStirling 2 qz387)

noncomputable abbrev qz637 := (@HAdd.hAdd Complex Complex Complex qz820 qz821 (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I (@HDiv.hDiv Complex Complex Complex qz822 (↑(Enclosure.sfrac Bool.false 124004 1000)) (2 : Complex))))

noncomputable abbrev qz408 := qz637

noncomputable abbrev qz69 := qz408

noncomputable abbrev qz409 := (@HMul.hMul Real Real Real qz0 (@HDiv.hDiv Real Real Real qz1 qz61 (2 : Real)) (Real.log Real.pi))

noncomputable def ep1288 := Complex.re (@HMul.hMul Complex Complex Complex qz3 (Complex.exp (@HMul.hMul Complex Complex Complex qz3 Complex.I ↑(@HSub.hSub Real Real Real qz599 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz409))) (zetaApproximant qz64 2 32))

noncomputable def ep1289 := @Enclosure.Real.IsNear.of_eq ep1288 (@HSub.hSub Real Real Real qz599 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz599 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz409)) (Complex.re (zetaApproximant qz64 2 32))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz599 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz409)) (Complex.im (zetaApproximant qz64 2 32))))

noncomputable def ep1290 := nat_lit 157588345139390640550381877331838245619

noncomputable def ep1291 := @Enclosure.Real.IsNear.subLit_tt_n (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz599 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz409)) (Complex.re (zetaApproximant qz64 2 32))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz599 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz409)) (Complex.im (zetaApproximant qz64 2 32))) ep1290

noncomputable def ep1292 := nat_lit 340392057634374621708091077427200000000

noncomputable def ep1293 := nat_lit 1153787923569393683062953429631490541597286097

noncomputable def ep1294 := nat_lit 190598301258699616514523145525177142476800000000

noncomputable def ep1295 := nat_lit 35434626478091311763265566473339811

noncomputable def ep1296 := nat_lit 12764702161289048314053415403520000000000

noncomputable def ep1297 := nat_lit 48459109350421280344728151143147139928760761

noncomputable def ep1298 := nat_lit 7147436297201235619294617957194142842880000000000

noncomputable def ep1299 := nat_lit 2011556228129325818138830050690336616490468278375071391239552379964620800000000

noncomputable def ep1300 := @Enclosure.Real.IsNear.mulLit_tf (Real.cos (@HSub.hSub Real Real Real qz599 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz409)) (Complex.re (zetaApproximant qz64 2 32)) 1048575 1048576 2138775

noncomputable def ep1301 := nat_lit 11271607548772665800041619149691599

noncomputable def ep1302 := nat_lit 24346737215593430164439040000000000

noncomputable def ep1303 := nat_lit 3394396977786173185670770800857759611

noncomputable def ep1304 := nat_lit 576116842732587337981121003520000000000

noncomputable def ep1305 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz599 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz409)) Bool.true 1048575 1048576 17110200

noncomputable abbrev qz977 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 64237083) qz279)

noncomputable def ep1306 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz599 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz409) qz977 Bool.false 64237083 524288 89

noncomputable def ep1307 := nat_lit 198645243458809726812971910109

noncomputable def ep1308 := nat_lit 1621295865853378560000000000

noncomputable def ep1309 := nat_lit 5078400085631024149490110624562093

noncomputable def ep1310 := nat_lit 14986220341284569088000000000000000000

noncomputable def ep1311 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz599 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz409) Bool.false ep1307 ep1308 ep1309 ep1310

noncomputable def ep1312 := nat_lit 313717569598791656981291910109

noncomputable def ep1313 := nat_lit 1533876336850484245490110624562093

noncomputable def ep1314 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz409 ep1312 ep1308 ep1313 ep1310 2325726021 32768000

noncomputable def ep1315 := nat_lit 6509207337658277128207463550451712000

noncomputable def ep1316 := nat_lit 1264680851530986353788944059

noncomputable def ep1317 := nat_lit 12970366926827028480000000

noncomputable def ep1318 := nat_lit 2636156173895118952225065095782463

noncomputable def ep1319 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz22 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz69 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true ep1316 ep1317 ep1318 ep1310 Bool.false ep1312 ep1308

noncomputable def ep1320 := nat_lit 1050528327743852521468944059

noncomputable def ep1321 := nat_lit 2556991336365550104716804575846463

noncomputable def ep1322 := nat_lit 323721539340251843861291910109

noncomputable def ep1323 := nat_lit 1375546662420767804807541486386093

noncomputable def ep1324 := @Enclosure.Complex.IsNear.subLitP qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz69 (@Nat.cast Complex Complex.instNatCast j))) Bool.true ep1320 ep1317 ep1321 ep1310 Bool.false ep1322 ep1308 ep1323

noncomputable def ep1325 := nat_lit 2847808105848775859317401410484827305541632

noncomputable def ep1326 := nat_lit 44151822798271742209304128315310958027210752

noncomputable abbrev qz410 := (@HSub.hSub Complex Complex Complex qz597 qz617 qz552)

noncomputable abbrev qz411 := (Complex.log qz617)

noncomputable abbrev qz70 := (@HSub.hSub Complex Complex Complex qz597 (@HMul.hMul Complex Complex Complex qz255 qz410 qz411) qz387)

noncomputable def ep1327 := @Enclosure.Complex.IsNear.of_eq qz68 (@HAdd.hAdd Complex Complex Complex qz15 (@HAdd.hAdd Complex Complex Complex qz15 qz70 qz903) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz22 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz29 qz55 (@HSub.hSub Int Int Int qz30 qz31 (@HMul.hMul Int Int Int qz32 qz33 (@Nat.cast Int instNatCastInt k)))))) Bool.true ep1320

noncomputable def ep1328 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz15 qz70 qz903) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz22 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz29 qz55 (@HSub.hSub Int Int Int qz30 qz31 (@HMul.hMul Int Int Int qz32 qz33 (@Nat.cast Int instNatCastInt k))))) Bool.true 364767193449221252809 4503599627370496000

noncomputable def ep1329 := nat_lit 2168920000357580508089891

noncomputable def ep1330 := nat_lit 4731158985369364510546332339990423891083264000

noncomputable def ep1331 := nat_lit 291582440788912313107836486649648627374148812800

noncomputable def ep1332 := @ep1328 8074892183839736451 47326000000000000000000 Bool.false 179846504589029000801 900719925474099200 1085968754056855709 11831500000000000000000 Bool.false 1189389904686620975941 ep1317 1069571988698213 ep1317 Bool.true ep1329 ep1308 1950428961518210563 ep1308 Bool.true ep1330 ep1320 ep1317 ep1321 ep1310 Bool.false ep1331

noncomputable def ep1333 := @Enclosure.Complex.IsNear.addLitP qz70 qz903 Bool.true 368905720856431748809 4503599627370496000 1996156250610813019 11831500000000000000000

noncomputable def ep1334 := nat_lit 47810765579776328048181248

noncomputable def ep1335 := @ep1333 Bool.false 179846504589029000801 900719925474099200 1085968754056855709 11831500000000000000000 Bool.false 120447 131072 1 524288 Bool.false 0 1 0 1 Bool.true ep1334 364767193449221252809 4503599627370496000 8074892183839736451 47326000000000000000000 Bool.false 179846504589029000801 179846504589029000801 900719925474099200

noncomputable abbrev qz71 := (@HMul.hMul Complex Complex Complex qz255 qz410 qz411)

noncomputable def ep1336 := @Enclosure.Complex.IsNear.subLitP qz71 qz55 Bool.true 349765422440107140809 4503599627370496000 1996156250610813019 11831500000000000000000 Bool.false 1178464707041370496997

noncomputable def ep1337 := nat_lit 1475622883425726995236000

noncomputable def ep1338 := nat_lit 3596930091780580016020000

noncomputable def ep1339 := @ep1336 4503599627370496000 1085968754056855709 11831500000000000000000 Bool.false 17000 4000 0 1 Bool.false 248008 4000 0 1 Bool.true ep1337 368905720856431748809 4503599627370496000 1996156250610813019 11831500000000000000000 Bool.false ep1338 179846504589029000801 900719925474099200 1085968754056855709 11831500000000000000000

noncomputable abbrev qz72 := qz410

noncomputable abbrev qz73 := qz411

noncomputable def ep1340 := @Enclosure.Complex.IsNear.mul qz72 qz73 Bool.true 349765422440107140809 4503599627370496000 1996156250610813019 11831500000000000000000 Bool.false 1178464707041370496997 4503599627370496000 1085968754056855709

noncomputable def ep1341 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re qz72) (Complex.re qz73)) (@HMul.hMul Real Real Real qz0 (Complex.im qz72) (Complex.im qz73)) 557929811694299955 36028797018963968 187500000780879 37860800000000000000 26219165556368414699 281474976710656000

noncomputable def ep1342 := nat_lit 787601713084175319569909406742085632

noncomputable def ep1343 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz72) (Complex.re qz73) 15000 4000 0 1 37195320779619997 9007199254740992 62500000260293 47326000000000000000

noncomputable def ep1344 := @Enclosure.Complex.IsNear.re_isNear qz72 Bool.false 15000 4000 0 1 Bool.false 248008 4000 0 1

noncomputable def ep1345 := @Enclosure.Complex.IsNear.of_eq qz72 (Complex.mk (Enclosure.sfrac Bool.false 15000 4000) qz390) Bool.false 15000 4000 0 1 Bool.false 248008 4000 0

noncomputable abbrev qz638 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 17000 4000) qz390))

noncomputable def ep1346 := @Enclosure.Complex.IsNear.of_eq qz73 qz638 Bool.false 37195320779619997 9007199254740992 62500000260293 47326000000000000000 Bool.false 845752251745699 562949953421312 125000000023663 47326000000000000000

noncomputable def ep1347 := nat_lit 594466376947520792577211899471573072768612410430727673164307351417816194682356575456570707233066808836758196715520

noncomputable def ep1348 := nat_lit 19805192289581212440922463225896012698237464059879685681981648216263395824581351821148512501282331930601302523904

noncomputable def ep1349 := nat_lit 401557539463445952375200608431116089945069136501818884197561077104749616939724224315946383458746130308792320

noncomputable def ep1350 := BSN.log_dyadic_bound 29028968064 94564968064 6 5 ep1347 1048576 378608 ep1348 ep1349 665218 123593936128 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 29028968064) (BSN.artanhQ 94564968064) 0 5 ep1348 ep1347 ep1349 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1351 := @Enclosure.Real.IsNear.mulLit_ff qz345 (Real.log (Enclosure.sfrac Bool.false 61796968064 16000000)) 1 2 0 1 37195320779619997 4503599627370496 62500000260293 23663000000000000000 37195320779619997 9007199254740992 62500000260293 47326000000000000000 qz346 (BSN.isNear_log_sfrac 61796968064 16000000 37195320779619997 4503599627370496 62500000260293 23663000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 61796968064) qz904)) Bool.false 312016965454486543794176 37778931862957161709568 1000000004164688 378608000000000000000 37195320779619997 4503599627370496 62500000260293 23663000000000000000 (BSN.log_rat_reduce_isNear 61796968064 16000000 11 123593936128 65536000000 665218 1048576 24973259072661432 36028797018963968 378608 1000000000000000 rfl rfl rfl rfl (ep1350 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1352 := BSN.arctan_dyadic_bound_f 17000 248008 1 0 1048576 378608 0 1 1 0 1 1 71763 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 17000) (BSN.arctanEvenQ 248008) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 17000) (BSN.arctanOddQ 248008) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz639 := (@Nat.cast Real Real.instNatCast 248008)

noncomputable def ep1353 := @Enclosure.Real.IsNear.subLit_ff_p qz354 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz604 qz639)) 884279719003555 562949953421312 1 2000000000000000 71763 1048576 1 378608 886835513126498074624 845752251745699 562949953421312 125000000023663 47326000000000000000 qz355 (ep1352 rfl) rfl rfl

noncomputable abbrev qz640 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 248008) (@Nat.cast Real Real.instNatCast 17000)))

noncomputable def ep1354 := @Enclosure.Complex.IsNear.re_isNear qz73 Bool.false 37195320779619997 9007199254740992 62500000260293 47326000000000000000 Bool.false 845752251745699 562949953421312 125000000023663 47326000000000000000 (ep1346 (@congrArg Complex Complex qz55 qz618 Complex.log (BSN.w_shift_mk qz61 Bool.false 124004 1000 4 (@Eq.refl Real qz61) rfl)) (@Enclosure.Complex.IsNear.of_parts qz638 Bool.false 37195320779619997 9007199254740992 62500000260293 47326000000000000000 Bool.false 845752251745699 562949953421312 125000000023663 47326000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz638) (@HMul.hMul Real Real Real qz0 qz345 (Real.log (Enclosure.sfrac Bool.false 61796968064 16000000))) Bool.false 37195320779619997 9007199254740992 62500000260293 47326000000000000000 (Enclosure.clog_re_eq 17000 248008 4000 61796968064 16000000 rfl rfl rfl) (ep1351 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz638) qz640 Bool.false 845752251745699 562949953421312 125000000023663 47326000000000000000 (Enclosure.clog_im_eq 17000 248008 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz640 (@HSub.hSub Real Real Real qz599 qz354 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz604 qz639))) Bool.false 845752251745699 562949953421312 125000000023663 47326000000000000000 (BSN.arctan_recip 248008 17000 rfl rfl) ep1353))))

noncomputable def ep1355 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz72) (Complex.im qz73) 248008 4000 0 1 845752251745699 562949953421312 125000000023663 47326000000000000000

noncomputable def ep1356 := @Enclosure.Complex.IsNear.im_isNear qz72 Bool.false 15000 4000 0 1 Bool.false 248008 4000 0 1

noncomputable def ep1357 := @Enclosure.Complex.IsNear.im_isNear qz73 Bool.false 37195320779619997 9007199254740992 62500000260293 47326000000000000000 Bool.false 845752251745699 562949953421312 125000000023663 47326000000000000000 (ep1346 (@congrArg Complex Complex qz55 qz618 Complex.log (BSN.w_shift_mk qz61 Bool.false 124004 1000 4 (@Eq.refl Real qz61) rfl)) (@Enclosure.Complex.IsNear.of_parts qz638 Bool.false 37195320779619997 9007199254740992 62500000260293 47326000000000000000 Bool.false 845752251745699 562949953421312 125000000023663 47326000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz638) (@HMul.hMul Real Real Real qz0 qz345 (Real.log (Enclosure.sfrac Bool.false 61796968064 16000000))) Bool.false 37195320779619997 9007199254740992 62500000260293 47326000000000000000 (Enclosure.clog_re_eq 17000 248008 4000 61796968064 16000000 rfl rfl rfl) (ep1351 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz638) qz640 Bool.false 845752251745699 562949953421312 125000000023663 47326000000000000000 (Enclosure.clog_im_eq 17000 248008 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz640 (@HSub.hSub Real Real Real qz599 qz354 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz604 qz639))) Bool.false 845752251745699 562949953421312 125000000023663 47326000000000000000 (BSN.arctan_recip 248008 17000 rfl rfl) ep1353))))

noncomputable abbrev qz412 := (@ep1345 1 (BSN.w_sub_half_mk qz61 Bool.false 124004 1000 4 (@Eq.refl Real qz61) rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 15000 4000) (Enclosure.sfrac Bool.false 248008 4000) Bool.false 15000 4000 0 1 Bool.false 248008 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 15000 4000) (Enclosure.Real.IsNear.const Bool.false 248008 4000)))

noncomputable def ep1358 := @ep1341 3875125000733576663 23663000000000000000000 ep1342 349765422440107140809 4503599627370496000 1996156250610813019 11831500000000000000000 (@ep1343 557929811694299955 36028797018963968 187500000780879 37860800000000000000 (ep1344 qz412) ep1354 rfl) (@ep1355 26219165556368414699 281474976710656000 3875125000733576663 23663000000000000000000 (ep1356 qz412) ep1357 rfl) rfl

noncomputable def ep1359 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re qz72) (Complex.im qz73)) (@HMul.hMul Real Real Real qz0 (Complex.im qz72) (Complex.re qz73)) 12686283776185485 2251799813685248 375000000070989 37860800000000000000 1153092139488999526997 4503599627370496000

noncomputable def ep1360 := nat_lit 2653666607750398451972246711887200256

noncomputable def ep1361 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz72) (Complex.im qz73) 15000 4000 0 1 845752251745699 562949953421312 125000000023663 47326000000000000000

noncomputable def ep1362 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz72) (Complex.re qz73) 248008 4000 0 1 37195320779619997 9007199254740992 62500000260293 47326000000000000000

noncomputable def ep1363 := @ep1359 1937562508069343293 23663000000000000000000 ep1360 1178464707041370496997 4503599627370496000 1085968754056855709 11831500000000000000000 (@ep1361 12686283776185485 2251799813685248 375000000070989 37860800000000000000 (ep1344 qz412) ep1357 rfl) (@ep1362 1153092139488999526997 4503599627370496000 1937562508069343293 23663000000000000000000 (ep1356 qz412) ep1354 rfl) rfl

noncomputable def ep1364 := ep1339 (@ep1340 11831500000000000000000 (ep1358 rfl) (ep1363 rfl)) qz63 rfl rfl rfl rfl rfl rfl

noncomputable def ep1365 := @ep1335 1085968754056855709 11831500000000000000000 (ep1364 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz26 (↑qz253) Bool.false 120447 131072 1 524288 Bool.false 0 1 0 1 (@ep546 131072 1 524288 (ep548 rfl) (ep550 rfl) rfl rfl) (@ep551 1 0 1 (ep553 rfl) (ep555 rfl) rfl rfl))

noncomputable abbrev qz74 := (@HPow.hPow Complex Int Complex qz601 qz387 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) qz353 (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) qz602 (@Nat.cast Int instNatCastInt 2))))

noncomputable def ep1366 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz22 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz29 qz55 (@HSub.hSub Int Int Int qz30 qz31 (@HMul.hMul Int Int Int qz32 qz33 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz15 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz22 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz29 qz55 (@HSub.hSub Int Int Int qz30 qz31 (@HMul.hMul Int Int Int qz32 qz33 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz37)) qz38) qz74)) Bool.false 1189389904686620975941 ep1317 1069571988698213 ep1317

noncomputable def ep1367 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz22 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz29 qz55 (@HSub.hSub Int Int Int qz30 qz31 (@HMul.hMul Int Int Int qz32 qz33 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz37)) qz38) qz74) Bool.false 18904357 206158430208 17 206158430208 Bool.true

noncomputable def ep1368 := nat_lit 245202755655436522579881495625728

noncomputable def ep1369 := nat_lit 55892642815056699527598871639228416000

noncomputable def ep1370 := @ep1367 34473763021 25769803776000 31001 25769803776000 Bool.false 30601948700975941 ep1317 24468698213 ep1317 Bool.true 18368347094748089891 ep1308 14686958210563 ep1308 Bool.false ep1368 1189389904686620975941 ep1317 1069571988698213 ep1317 Bool.true ep1369 ep1329 ep1308 1950428961518210563

noncomputable abbrev qz75 := (@HPow.hPow Complex Int Complex qz601 qz387 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) qz353 (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) qz602 (@Nat.cast Int instNatCastInt 1))))

noncomputable def ep1371 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz22 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz29 qz55 (@HSub.hSub Int Int Int qz30 qz31 (@HMul.hMul Int Int Int qz32 qz33 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz15 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz22 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz29 qz55 (@HSub.hSub Int Int Int qz30 qz31 (@HMul.hMul Int Int Int qz32 qz33 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz40)) qz41) qz75)) Bool.false 18904357 206158430208 17 206158430208

noncomputable def ep1372 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz22 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz29 qz55 (@HSub.hSub Int Int Int qz30 qz31 (@HMul.hMul Int Int Int qz32 qz33 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz40)) qz41) qz75) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1373 := @ep1372 0 1 0 1 Bool.false 18904357 206158430208 17 206158430208 Bool.true 34473763021 25769803776000 31001 25769803776000 Bool.false 18904357 18904357 206158430208 17 206158430208 Bool.true 34473763021 34473763021 25769803776000 31001

noncomputable def ep1374 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz22 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz29 qz55 (@HSub.hSub Int Int Int qz30 qz31 (@HMul.hMul Int Int Int qz32 qz33 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz264 qz264) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1375 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz40)) qz41) qz75 Bool.false 18904357 206158430208 17 206158430208 Bool.true 34473763021 25769803776000 31001 25769803776000

noncomputable def ep1376 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz40)) qz41)) (Complex.re qz75)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz40)) qz41)) (Complex.im qz75)) 18904357 206158430208 17 206158430208 0 1 0

noncomputable def ep1377 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz40)) qz41)) (Complex.re qz75) 1 12 0 1 18904357 17179869184 17 17179869184 18904357

noncomputable def ep1378 := @Enclosure.Complex.IsNear.re_isNear qz75 Bool.false 18904357 17179869184 17 17179869184 Bool.true 34473763021 2147483648000 31001 2147483648000

noncomputable def ep1379 := @Enclosure.Complex.IsNear.of_eq qz75 (@Inv.inv Complex Complex.instInv qz58) Bool.false 18904357 17179869184 17 17179869184 Bool.true 34473763021 2147483648000 31001

noncomputable def ep1380 := @Enclosure.Complex.IsNear.of_parts (@Inv.inv Complex Complex.instInv qz58) Bool.false 18904357 17179869184 17 17179869184 Bool.true 34473763021 2147483648000 31001

noncomputable def ep1381 := @Enclosure.Real.IsNear.mulLit_ff qz59 (@Inv.inv Real Real.instInv (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz58)) 17000 4000 0 1 1112021 4294967296 1 4294967296

noncomputable def ep1382 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz58)) Bool.false 1112021 4294967296 1 4294967296 1112021 4294967296 1

noncomputable def ep1383 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz58) (@HAdd.hAdd Real Real Real qz607 (@HMul.hMul Real Real Real qz0 qz59 qz59) (@HMul.hMul Real Real Real qz0 qz60 qz60)) Bool.false 482788813 125000 0 1

noncomputable def ep1384 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz59 qz59) (@HMul.hMul Real Real Real qz0 qz60 qz60) 289 16 0 1 961062001 250000

noncomputable def ep1385 := @Enclosure.Real.IsNear.mulLit_ff qz59 qz59 17000 4000 0 1 17000 4000 0 1

noncomputable def ep1386 := @Enclosure.Real.IsNear.mulLit_ff qz60 qz60 248008 4000 0 1 248008 4000 0 1

noncomputable def ep1387 := @ep1384 0 1 15449242016 482788813 125000 0 1 (@ep1385 289 16 0 1 (ep925 qz62) (ep925 qz62) rfl) (@ep1386 961062001 250000 0 1 (ep930 qz62) (ep930 qz62) rfl)

noncomputable def ep1388 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz58) 482788813 125000 0 1 556010 556011 2147483648 (ep1383 (Enclosure.Complex.normSq_eq_mul_add_mul qz58) (ep1387 rfl rfl)) rfl

noncomputable def ep1389 := @Enclosure.Real.IsNear.of_eq (Complex.re (@Inv.inv Complex Complex.instInv qz58)) (@HMul.hMul Real Real Real qz0 qz59 (@Inv.inv Real Real.instInv (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz58))) Bool.false 18904357 17179869184 17 17179869184 (Enclosure.Complex.inv_re_eq_mul qz58) (@ep1381 18904357 17179869184 17 17179869184 (ep925 qz62) (@ep1382 4294967296 (ep1388 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep1390 := @Enclosure.Real.IsNear.of_eq (Complex.im (@Inv.inv Complex Complex.instInv qz58)) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz60) (@Inv.inv Real Real.instInv (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz58))) Bool.true 34473763021 2147483648000 31001 2147483648000 (Enclosure.Complex.inv_im_eq_mul qz58)

noncomputable def ep1391 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz60) (@Inv.inv Real Real.instInv (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz58)) 248008 4000 0 1 1112021 4294967296 1

noncomputable def ep1392 := @ep1391 4294967296 34473763021 2147483648000 31001 2147483648000 (@Enclosure.Real.IsNear.neg qz60 Bool.false 248008 4000 0 1 (ep930 qz62)) (@ep1382 4294967296 (ep1388 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep1393 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz40)) qz41)) (Complex.im qz75) 0 1 0 1 34473763021 2147483648000 31001 2147483648000 0

noncomputable def ep1394 := @Enclosure.Complex.IsNear.im_isNear qz75 Bool.false 18904357 17179869184 17 17179869184 Bool.true 34473763021 2147483648000 31001 2147483648000

noncomputable abbrev qz641 := (@ep1379 2147483648000 (BSN.zpow_one_sub_two_mul qz55 1 1 rfl rfl) (@ep1380 2147483648000 ep1389 (ep1390 ep1392)))

noncomputable def ep1395 := @ep1376 1 18904357 18904357 206158430208 17 206158430208 (@ep1377 206158430208 17 206158430208 ep572 (ep1378 qz641) rfl) (@ep1393 1 0 1 ep589 (ep1394 qz641) rfl) rfl

noncomputable def ep1396 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz40)) qz41)) (Complex.im qz75)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz40)) qz41)) (Complex.re qz75)) 34473763021 25769803776000 31001 25769803776000 0 1 0

noncomputable def ep1397 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz40)) qz41)) (Complex.im qz75) 1 12 0 1 34473763021 2147483648000 31001 2147483648000 34473763021

noncomputable def ep1398 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz40)) qz41)) (Complex.re qz75) 0 1 0 1 18904357 17179869184 17 17179869184 0

noncomputable def ep1399 := @ep1396 1 34473763021 34473763021 25769803776000 31001 25769803776000 (@ep1397 25769803776000 31001 25769803776000 ep572 (ep1394 qz641) rfl) (@ep1398 1 0 1 ep589 (ep1378 qz641) rfl) rfl

noncomputable def ep1400 := @ep1373 25769803776000 (@ep1374 0 1 0 1 (BSN.stirling_sum_base qz55) qz360) (ep1375 (ep1395 rfl) (ep1399 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep1401 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz37)) qz38) qz74 Bool.false 30601948700975941 ep1317 24468698213 ep1317 Bool.true 18368347094748089891 ep1308 14686958210563 ep1308

noncomputable def ep1402 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz37)) qz38)) (Complex.re qz74)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz37)) qz38)) (Complex.im qz74)) 30601948700975941 ep1317 24468698213 ep1317 0 1 0

noncomputable def ep1403 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz37)) qz38)) (Complex.re qz74) 1 360 0 1 30601948700975941 36028797018963968000000 24468698213 36028797018963968000000 30601948700975941

noncomputable def ep1404 := nat_lit 4503599627370496000000000

noncomputable def ep1405 := @Enclosure.Complex.IsNear.re_isNear qz74 Bool.true 30601948700975941 36028797018963968000000 24468698213 36028797018963968000000 Bool.false 18368347094748089891 ep1404 14686958210563 ep1404

noncomputable def ep1406 := @Enclosure.Complex.IsNear.of_eq qz74 (@Inv.inv Complex Complex.instInv qz53) Bool.true 30601948700975941 36028797018963968000000 24468698213 36028797018963968000000 Bool.false 18368347094748089891 ep1404 14686958210563

noncomputable def ep1407 := @Enclosure.Complex.IsNear.of_parts (@Inv.inv Complex Complex.instInv qz53) Bool.true 30601948700975941 36028797018963968000000 24468698213 36028797018963968000000 Bool.false 18368347094748089891 ep1404 14686958210563

noncomputable abbrev qz76 := (Complex.re qz386)

noncomputable def ep1408 := @Enclosure.Real.IsNear.mulLit_tf qz76 (@Inv.inv Real Real.instInv (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz53)) 24468698213 500000 0 1 1250657 72057594037927936 1 72057594037927936

noncomputable def ep1409 := @Enclosure.Complex.IsNear.re_isNear qz53 Bool.true 24468698213 500000 0 1 Bool.true 14686958210563 62500000 0 1

noncomputable def ep1410 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz53)) Bool.false 1250657 72057594037927936 1 72057594037927936 1250657 72057594037927936 1

noncomputable def ep1411 := nat_lit 112530848803778126658083797

noncomputable abbrev qz77 := (Complex.im qz386)

noncomputable def ep1412 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz53) (@HAdd.hAdd Real Real Real qz607 (@HMul.hMul Real Real Real qz0 qz76 qz76) (@HMul.hMul Real Real Real qz0 qz77 qz77)) Bool.false ep1411 1953125000000000 0 1

noncomputable def ep1413 := nat_lit 215706741478823919044776969

noncomputable def ep1414 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz76 qz76) (@HMul.hMul Real Real Real qz0 qz77 qz77) 598717192238869393369 250000000000 0 1 ep1413 3906250000000000

noncomputable def ep1415 := nat_lit 56265424401889063329041898500000000000

noncomputable def ep1416 := @Enclosure.Real.IsNear.mulLit_tt qz76 qz76 24468698213 500000 0 1 24468698213 500000 0 1

noncomputable def ep1417 := @Enclosure.Real.IsNear.mulLit_tt qz77 qz77 14686958210563 62500000 0 1 14686958210563 62500000 0 1

noncomputable def ep1418 := @Enclosure.Complex.IsNear.im_isNear qz53 Bool.true 24468698213 500000 0 1 Bool.true 14686958210563 62500000 0 1

noncomputable def ep1419 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz53) ep1411 1953125000000000 0 1 625328 625329 36028797018963968 (ep1412 (Enclosure.Complex.normSq_eq_mul_add_mul qz53) (@ep1414 0 1 ep1415 ep1411 1953125000000000 0 1 (@ep1416 598717192238869393369 250000000000 0 1 (ep1409 EMRow40.d16) (ep1409 EMRow40.d16) rfl) (@ep1417 ep1413 3906250000000000 0 1 (ep1418 EMRow40.d16) (ep1418 EMRow40.d16) rfl) rfl rfl)) rfl

noncomputable def ep1420 := @Enclosure.Real.IsNear.of_eq (Complex.re (@Inv.inv Complex Complex.instInv qz53)) (@HMul.hMul Real Real Real qz0 qz76 (@Inv.inv Real Real.instInv (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz53))) Bool.true 30601948700975941 36028797018963968000000 24468698213 36028797018963968000000 (Enclosure.Complex.inv_re_eq_mul qz53) (@ep1408 30601948700975941 36028797018963968000000 24468698213 36028797018963968000000 (ep1409 EMRow40.d16) (@ep1410 72057594037927936 (ep1419 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep1421 := @Enclosure.Real.IsNear.of_eq (Complex.im (@Inv.inv Complex Complex.instInv qz53)) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz77) (@Inv.inv Real Real.instInv (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz53))) Bool.false 18368347094748089891 ep1404 14686958210563 ep1404 (Enclosure.Complex.inv_im_eq_mul qz53)

noncomputable def ep1422 := @Enclosure.Real.IsNear.mulLit_ff (@Neg.neg Real Real.instNeg qz77) (@Inv.inv Real Real.instInv (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz53)) 14686958210563 62500000 0 1 1250657 72057594037927936 1

noncomputable def ep1423 := @ep1422 72057594037927936 18368347094748089891 ep1404 14686958210563 ep1404 (@Enclosure.Real.IsNear.neg qz77 Bool.true 14686958210563 62500000 0 1 (ep1418 EMRow40.d16)) (@ep1410 72057594037927936 (ep1419 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep1424 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz37)) qz38)) (Complex.im qz74) 0 1 0 1 18368347094748089891 ep1404 14686958210563 ep1404 0

noncomputable def ep1425 := @Enclosure.Complex.IsNear.im_isNear qz74 Bool.true 30601948700975941 36028797018963968000000 24468698213 36028797018963968000000 Bool.false 18368347094748089891 ep1404 14686958210563 ep1404

noncomputable abbrev qz978 := (@ep1406 ep1404 (BSN.zpow_one_sub_two_mul qz55 2 3 rfl rfl) (@ep1407 ep1404 ep1420 (ep1421 ep1423)))

noncomputable def ep1426 := @ep1402 1 30601948700975941 30601948700975941 ep1317 24468698213 ep1317 (@ep1403 ep1317 24468698213 ep1317 ep601 (ep1405 qz978) rfl) (@ep1424 1 0 1 ep623 (ep1425 qz978) rfl) rfl

noncomputable def ep1427 := @Enclosure.Real.IsNear.addLit_tt (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz37)) qz38)) (Complex.im qz74)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz37)) qz38)) (Complex.re qz74)) 18368347094748089891 ep1308 14686958210563 ep1308 0 1 0

noncomputable def ep1428 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz37)) qz38)) (Complex.im qz74) 1 360 0 1 18368347094748089891 ep1404 14686958210563 ep1404 18368347094748089891

noncomputable def ep1429 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz37)) qz38)) (Complex.re qz74) 0 1 0 1 30601948700975941 36028797018963968000000 24468698213 36028797018963968000000 0

noncomputable def ep1430 := @ep1427 1 18368347094748089891 18368347094748089891 ep1308 14686958210563 ep1308 (@ep1428 ep1308 14686958210563 ep1308 ep601 (ep1425 qz978) rfl) (@ep1429 1 0 1 ep623 (ep1405 qz978) rfl) rfl

noncomputable def ep1431 := @ep1370 ep1308 (@ep1371 Bool.true 34473763021 25769803776000 31001 25769803776000 (BSN.stirling_sum_succ qz55 0 1 rfl) (ep1400 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1401 (ep1426 rfl) (ep1430 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep1432 := @ep1332 ep1322 ep1308 ep1323 ep1310 (ep1365 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep1366 Bool.true ep1329 ep1308 1950428961518210563 ep1308 (BSN.stirling_sum_succ qz55 1 2 rfl) (ep1431 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep1433 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz69 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz61 4) Bool.false 37179257601932957 2251799813685248 62500000260293 11831500000000000000 Bool.false 868400151168419 140737488355328

noncomputable def ep1434 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz61 4) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.logSumC qz61 3) (Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz69 qz554))) Bool.false 37179257601932957 2251799813685248 62500000260293 11831500000000000000 Bool.false 868400151168419 140737488355328 125000000023663 11831500000000000000

noncomputable def ep1435 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz61 3) (Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz69 qz554)) Bool.false 111530462771461079 9007199254740992 187500000780879 47326000000000000000 Bool.false 2618802078060777 562949953421312 375000000070989 47326000000000000000 Bool.false

noncomputable def ep1436 := nat_lit 1339523925455815566789542334693376

noncomputable def ep1437 := nat_lit 1955463298605287102493503782912

noncomputable def ep1438 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz61 3) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.logSumC qz61 2) (Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz69 qz555))) Bool.false 111530462771461079 9007199254740992 187500000780879 47326000000000000000 Bool.false 2618802078060777 562949953421312 375000000070989 47326000000000000000

noncomputable def ep1439 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz61 2) (Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz69 qz555)) Bool.false 37175162350616221 4503599627370496 62500000260293 23663000000000000000 Bool.false 877471122097571 281474976710656 125000000023663 23663000000000000000 Bool.false

noncomputable def ep1440 := nat_lit 502288550578011091964392776925184

noncomputable def ep1441 := nat_lit 737127253931974742202711539712

noncomputable def ep1442 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz61 2) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.logSumC qz61 1) (Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz69 qz592))) Bool.false 37175162350616221 4503599627370496 62500000260293 23663000000000000000 Bool.false 877471122097571 281474976710656 125000000023663 23663000000000000000

noncomputable def ep1443 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz61 1) (Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz69 qz592)) Bool.false 37174284029804189 9007199254740992 62500000260293 47326000000000000000 Bool.false 882010365658531 562949953421312 125000000023663 47326000000000000000 Bool.false

noncomputable def ep1444 := nat_lit 669688189238691620264013897662464

noncomputable def ep1445 := nat_lit 987944654626747938514669666304

noncomputable abbrev qz979 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz69 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep1446 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz61 1) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.logSumC qz61 0) qz979) Bool.false 37174284029804189 9007199254740992 62500000260293 47326000000000000000 Bool.false 882010365658531 562949953421312 125000000023663 47326000000000000000

noncomputable def ep1447 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz61 0) qz979 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz980 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz390))

noncomputable def ep1448 := @Enclosure.Complex.IsNear.of_eq qz979 qz980 Bool.false 37174284029804189 9007199254740992 62500000260293 47326000000000000000 Bool.false 882010365658531 562949953421312 125000000023663 47326000000000000000

noncomputable def ep1449 := nat_lit 576607870217708384564499406410570821877928028605511928485866016502903380578367799990467131482112495885359796715520

noncomputable def ep1450 := nat_lit 18930201044607261456099054490917137151997975385996439697112161894727842256026875771144208634422493761185622523904

noncomputable def ep1451 := nat_lit 363450884115554215168524430762512454370427611139935464406417005020318361694537130830104798053423275908792320

noncomputable def ep1452 := BSN.log_dyadic_bound 28740968064 94276968064 6 5 ep1449 1048576 378608 ep1450 ep1451 660320 123017936128 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 28740968064) (BSN.artanhQ 94276968064) 0 5 ep1450 ep1449 ep1451 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1453 := @Enclosure.Real.IsNear.mulLit_ff qz345 (Real.log (Enclosure.sfrac Bool.false 61508968064 16000000)) 1 2 0 1 37174284029804189 4503599627370496 62500000260293 23663000000000000000 37174284029804189 9007199254740992 62500000260293 47326000000000000000 qz346 (BSN.isNear_log_sfrac 61508968064 16000000 37174284029804189 4503599627370496 62500000260293 23663000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 61508968064) qz904)) Bool.false 311840496406687658278912 37778931862957161709568 1000000004164688 378608000000000000000 37174284029804189 4503599627370496 62500000260293 23663000000000000000 (BSN.log_rat_reduce_isNear 61508968064 16000000 11 123017936128 65536000000 660320 1048576 24973259072661432 36028797018963968 378608 1000000000000000 rfl rfl rfl rfl (ep1452 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1454 := BSN.arctan_dyadic_bound_f 1000 248008 1 0 1048576 378608 0 1 1 0 1 1 4227 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 248008) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 248008) 0 0 rfl) rfl rfl rfl

noncomputable def ep1455 := @Enclosure.Real.IsNear.subLit_ff_p qz354 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz910 qz639)) 884279719003555 562949953421312 1 2000000000000000 4227 1048576 1 378608 924854901180759801856 882010365658531 562949953421312 125000000023663 47326000000000000000 qz355 (ep1454 rfl) rfl rfl

noncomputable abbrev qz981 := (@HAdd.hAdd Complex Complex Complex qz15 qz69 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz982 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz390)

noncomputable def ep1456 := @ep1447 37174284029804189 9007199254740992 62500000260293 47326000000000000000 Bool.false 882010365658531 562949953421312 125000000023663 47326000000000000000 Bool.false 37174284029804189 37174284029804189 9007199254740992 62500000260293 47326000000000000000 Bool.false 882010365658531 882010365658531 562949953421312 125000000023663 47326000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz61 0) (Complex.mk qz264 qz264) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz61) qz360) (ep1448 (@congrArg Complex Complex qz981 qz982 Complex.log (BSN.w_shift_mk qz61 Bool.false 124004 1000 0 (@Eq.refl Real qz61) rfl)) (@Enclosure.Complex.IsNear.of_parts qz980 Bool.false 37174284029804189 9007199254740992 62500000260293 47326000000000000000 Bool.false 882010365658531 562949953421312 125000000023663 47326000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz980) (@HMul.hMul Real Real Real qz0 qz345 (Real.log (Enclosure.sfrac Bool.false 61508968064 16000000))) Bool.false 37174284029804189 9007199254740992 62500000260293 47326000000000000000 (Enclosure.clog_re_eq 1000 248008 4000 61508968064 16000000 rfl rfl rfl) (ep1453 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz980) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz639 qz910)) Bool.false 882010365658531 562949953421312 125000000023663 47326000000000000000 (Enclosure.clog_im_eq 1000 248008 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz639 qz910)) (@HSub.hSub Real Real Real qz599 qz354 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz910 qz639))) Bool.false 882010365658531 562949953421312 125000000023663 47326000000000000000 (BSN.arctan_recip 248008 1000 rfl rfl) ep1455)))) rfl rfl

noncomputable abbrev qz983 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz390))

noncomputable def ep1457 := @Enclosure.Complex.IsNear.of_eq (Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz69 qz592)) qz983 Bool.false 37176040671428253 9007199254740992 62500000260293 47326000000000000000 Bool.false 872931878536611 562949953421312 125000000023663 47326000000000000000

noncomputable def ep1458 := nat_lit 578077418176389904662242583195718412269794233463162844537206198227013506578855729832806587078498127564642996715520

noncomputable def ep1459 := nat_lit 19001813926457098554027867251449942446788010643655415975813025914310391359937635103318560048580392061970262523904

noncomputable def ep1460 := nat_lit 366497292315841454509924979414504843991873710322976364061709191474658329570654021784495409513466847108792320

noncomputable def ep1461 := BSN.log_dyadic_bound 28764968064 94300968064 6 5 ep1458 1048576 378608 ep1459 ep1460 660729 123065936128 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 28764968064) (BSN.artanhQ 94300968064) 0 5 ep1459 ep1458 ep1460 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1462 := @Enclosure.Real.IsNear.mulLit_ff qz345 (Real.log (Enclosure.sfrac Bool.false 61532968064 16000000)) 1 2 0 1 37176040671428253 4503599627370496 62500000260293 23663000000000000000 37176040671428253 9007199254740992 62500000260293 47326000000000000000 qz346 (BSN.isNear_log_sfrac 61532968064 16000000 37176040671428253 4503599627370496 62500000260293 23663000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 61532968064) qz904)) Bool.false 311855232184668414541824 37778931862957161709568 1000000004164688 378608000000000000000 37176040671428253 4503599627370496 62500000260293 23663000000000000000 (BSN.log_rat_reduce_isNear 61532968064 16000000 11 123065936128 65536000000 660729 1048576 24973259072661432 36028797018963968 378608 1000000000000000 rfl rfl rfl rfl (ep1461 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1463 := BSN.arctan_dyadic_bound_f 5000 248008 1 0 1048576 378608 0 1 1 0 1 1 21137 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 248008) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 248008) 0 0 rfl) rfl rfl rfl

noncomputable def ep1464 := @Enclosure.Real.IsNear.subLit_ff_p qz354 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz914 qz639)) 884279719003555 562949953421312 1 2000000000000000 21137 1048576 1 378608 915335417468405415936 872931878536611 562949953421312 125000000023663 47326000000000000000 qz355 (ep1463 rfl) rfl rfl

noncomputable abbrev qz984 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz390)

noncomputable def ep1465 := @ep1443 37176040671428253 9007199254740992 62500000260293 47326000000000000000 Bool.false 872931878536611 562949953421312 125000000023663 47326000000000000000 Bool.false ep1444 37175162350616221 4503599627370496 62500000260293 23663000000000000000 Bool.false ep1445 877471122097571 281474976710656 125000000023663 23663000000000000000 (ep1446 (BSN.log_sum_c_succ qz61 0 1 rfl) (ep1456 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1457 (@congrArg Complex Complex (@HAdd.hAdd Complex Complex Complex qz15 qz69 qz592) qz984 Complex.log (BSN.w_shift_mk qz61 Bool.false 124004 1000 1 (@Eq.refl Real qz61) rfl)) (@Enclosure.Complex.IsNear.of_parts qz983 Bool.false 37176040671428253 9007199254740992 62500000260293 47326000000000000000 Bool.false 872931878536611 562949953421312 125000000023663 47326000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz983) (@HMul.hMul Real Real Real qz0 qz345 (Real.log (Enclosure.sfrac Bool.false 61532968064 16000000))) Bool.false 37176040671428253 9007199254740992 62500000260293 47326000000000000000 (Enclosure.clog_re_eq 5000 248008 4000 61532968064 16000000 rfl rfl rfl) (ep1462 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz983) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz639 qz914)) Bool.false 872931878536611 562949953421312 125000000023663 47326000000000000000 (Enclosure.clog_im_eq 5000 248008 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz639 qz914)) (@HSub.hSub Real Real Real qz599 qz354 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz914 qz639))) Bool.false 872931878536611 562949953421312 125000000023663 47326000000000000000 (BSN.arctan_recip 248008 5000 rfl rfl) ep1464)))) rfl rfl

noncomputable abbrev qz985 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 9000 4000) qz390))

noncomputable def ep1466 := @Enclosure.Complex.IsNear.of_eq (Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz69 qz555)) qz985 Bool.false 37180138070228637 9007199254740992 62500000260293 47326000000000000000 Bool.false 863859833865635 562949953421312 125000000023663 47326000000000000000

noncomputable def ep1467 := nat_lit 581519480505986217920364827714629735125493995407906505932442356447001166573364509599172771714484526816303796715520

noncomputable def ep1468 := nat_lit 19169824508557229540890379026303438494131738095299727085256924288355747469368680805843670203552486497134422523904

noncomputable def ep1469 := nat_lit 373695140524039564594815951957244544993756235948409711532773047142300223003868962974550510792235179908792320

noncomputable def ep1470 := BSN.log_dyadic_bound 28820968064 94356968064 6 5 ep1467 1048576 378608 ep1468 ep1469 661683 123177936128 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 28820968064) (BSN.artanhQ 94356968064) 0 5 ep1468 ep1467 ep1469 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1471 := @Enclosure.Real.IsNear.mulLit_ff qz345 (Real.log (Enclosure.sfrac Bool.false 61588968064 16000000)) 1 2 0 1 37180138070228637 4503599627370496 62500000260293 23663000000000000000 37180138070228637 9007199254740992 62500000260293 47326000000000000000 qz346 (BSN.isNear_log_sfrac 61588968064 16000000 37180138070228637 4503599627370496 62500000260293 23663000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 61588968064) qz904)) Bool.false 311889603657024506167296 37778931862957161709568 1000000004164688 378608000000000000000 37180138070228637 4503599627370496 62500000260293 23663000000000000000 (BSN.log_rat_reduce_isNear 61588968064 16000000 11 123177936128 65536000000 661683 1048576 24973259072661432 36028797018963968 378608 1000000000000000 rfl rfl rfl rfl (ep1470 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1472 := BSN.arctan_dyadic_bound_f 9000 248008 1 0 1048576 378608 0 1 1 0 1 1 38035 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 248008) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 248008) 0 0 rfl) rfl rfl rfl

noncomputable def ep1473 := @Enclosure.Real.IsNear.subLit_ff_p qz354 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz917 qz639)) 884279719003555 562949953421312 1 2000000000000000 38035 1048576 1 378608 905822689155492085760 863859833865635 562949953421312 125000000023663 47326000000000000000 qz355 (ep1472 rfl) rfl rfl

noncomputable abbrev qz986 := (Complex.mk (Enclosure.sfrac Bool.false 9000 4000) qz390)

noncomputable def ep1474 := @ep1439 37180138070228637 9007199254740992 62500000260293 47326000000000000000 Bool.false 863859833865635 562949953421312 125000000023663 47326000000000000000 Bool.false ep1440 111530462771461079 9007199254740992 187500000780879 47326000000000000000 Bool.false ep1441 2618802078060777 562949953421312 375000000070989 47326000000000000000 (ep1442 (BSN.log_sum_c_succ qz61 1 2 rfl) (ep1465 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1466 (@congrArg Complex Complex (@HAdd.hAdd Complex Complex Complex qz15 qz69 qz555) qz986 Complex.log (BSN.w_shift_mk qz61 Bool.false 124004 1000 2 (@Eq.refl Real qz61) rfl)) (@Enclosure.Complex.IsNear.of_parts qz985 Bool.false 37180138070228637 9007199254740992 62500000260293 47326000000000000000 Bool.false 863859833865635 562949953421312 125000000023663 47326000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz985) (@HMul.hMul Real Real Real qz0 qz345 (Real.log (Enclosure.sfrac Bool.false 61588968064 16000000))) Bool.false 37180138070228637 9007199254740992 62500000260293 47326000000000000000 (Enclosure.clog_re_eq 9000 248008 4000 61588968064 16000000 rfl rfl rfl) (ep1471 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz985) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz639 qz917)) Bool.false 863859833865635 562949953421312 125000000023663 47326000000000000000 (Enclosure.clog_im_eq 9000 248008 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz639 qz917)) (@HSub.hSub Real Real Real qz599 qz354 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz917 qz639))) Bool.false 863859833865635 562949953421312 125000000023663 47326000000000000000 (BSN.arctan_recip 248008 9000 rfl rfl) ep1473)))) rfl rfl

noncomputable abbrev qz987 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 13000 4000) qz390))

noncomputable def ep1475 := @Enclosure.Complex.IsNear.of_eq (Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz69 qz554)) qz987 Bool.false 37186567636270749 9007199254740992 62500000260293 47326000000000000000 Bool.false 854798526612899 562949953421312 125000000023663 47326000000000000000

noncomputable def ep1476 := nat_lit 586965714910882487656515569294239026121814986707423342463043992332644223354889386806842752498279514440342196715520

noncomputable def ep1477 := nat_lit 19436443119717839503272606884258989900781135852708270398772285533165695865602866771325784280307573226678102523904

noncomputable def ep1478 := nat_lit 385263354739994037636434881440855500895704571045431360008591531679426894612395539400480520782528274308792320

noncomputable def ep1479 := BSN.log_dyadic_bound 28908968064 94444968064 6 5 ep1476 1048576 378608 ep1477 ep1478 663180 123353936128 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 28908968064) (BSN.artanhQ 94444968064) 0 5 ep1477 ep1476 ep1478 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1480 := @Enclosure.Real.IsNear.mulLit_ff qz345 (Real.log (Enclosure.sfrac Bool.false 61676968064 16000000)) 1 2 0 1 37186567636270749 4503599627370496 62500000260293 23663000000000000000 37186567636270749 9007199254740992 62500000260293 47326000000000000000 qz346 (BSN.isNear_log_sfrac 61676968064 16000000 37186567636270749 4503599627370496 62500000260293 23663000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 61676968064) qz904)) Bool.false 311943538766161895227392 37778931862957161709568 1000000004164688 378608000000000000000 37186567636270749 4503599627370496 62500000260293 23663000000000000000 (BSN.log_rat_reduce_isNear 61676968064 16000000 11 123353936128 65536000000 663180 1048576 24973259072661432 36028797018963968 378608 1000000000000000 rfl rfl rfl rfl (ep1479 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1481 := BSN.arctan_dyadic_bound_f 13000 248008 1 0 1048576 378608 0 1 1 0 1 1 54913 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 13000) (BSN.arctanEvenQ 248008) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 13000) (BSN.arctanOddQ 248008) 0 0 rfl) rfl rfl rfl

noncomputable def ep1482 := @Enclosure.Real.IsNear.subLit_ff_p qz354 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz920 qz639)) 884279719003555 562949953421312 1 2000000000000000 54913 1048576 1 378608 896321219841647181824 854798526612899 562949953421312 125000000023663 47326000000000000000 qz355 (ep1481 rfl) rfl rfl

noncomputable abbrev qz988 := (Complex.mk (Enclosure.sfrac Bool.false 13000 4000) qz390)

noncomputable def ep1483 := @ep1435 37186567636270749 9007199254740992 62500000260293 47326000000000000000 Bool.false 854798526612899 562949953421312 125000000023663 47326000000000000000 Bool.false ep1436 37179257601932957 2251799813685248 62500000260293 11831500000000000000 Bool.false ep1437 868400151168419 140737488355328 125000000023663 11831500000000000000 (ep1438 (BSN.log_sum_c_succ qz61 2 3 rfl) (ep1474 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1475 (@congrArg Complex Complex (@HAdd.hAdd Complex Complex Complex qz15 qz69 qz554) qz988 Complex.log (BSN.w_shift_mk qz61 Bool.false 124004 1000 3 (@Eq.refl Real qz61) rfl)) (@Enclosure.Complex.IsNear.of_parts qz987 Bool.false 37186567636270749 9007199254740992 62500000260293 47326000000000000000 Bool.false 854798526612899 562949953421312 125000000023663 47326000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz987) (@HMul.hMul Real Real Real qz0 qz345 (Real.log (Enclosure.sfrac Bool.false 61676968064 16000000))) Bool.false 37186567636270749 9007199254740992 62500000260293 47326000000000000000 (Enclosure.clog_re_eq 13000 248008 4000 61676968064 16000000 rfl rfl rfl) (ep1480 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz987) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz639 qz920)) Bool.false 854798526612899 562949953421312 125000000023663 47326000000000000000 (Enclosure.clog_im_eq 13000 248008 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz639 qz920)) (@HSub.hSub Real Real Real qz599 qz354 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz920 qz639))) Bool.false 854798526612899 562949953421312 125000000023663 47326000000000000000 (BSN.arctan_recip 248008 13000 rfl rfl) ep1482)))) rfl rfl

noncomputable def ep1484 := @ep1324 ep1310 Bool.false 37179257601932957 2251799813685248 62500000260293 11831500000000000000 Bool.false 868400151168419 140737488355328 125000000023663 11831500000000000000 Bool.true ep1325 ep1316 ep1317 ep1318 ep1310 Bool.false ep1326 ep1312 ep1308 ep1313 ep1310 (@ep1327 ep1317 ep1321 ep1310 Bool.false ep1322 ep1308 ep1323 ep1310 (BSN.logGammaStirling_unfold 2 qz55) (ep1432 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep1433 125000000023663 11831500000000000000 (BSN.log_sum_c_eq qz61 4) (ep1434 (BSN.log_sum_c_succ qz61 3 4 rfl) (ep1483 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable def ep1485 := @Enclosure.Real.IsNear.mulLit_ff (@HDiv.hDiv Real Real Real qz1 qz61 (2 : Real)) (Real.log Real.pi) 124004 2000 0 1 75021 65536 1 262144 2325726021 32768000 31001 131072000 (@Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real qz1 qz61 (2 : Real)) (Enclosure.sfrac Bool.false 124004 2000) Bool.false 124004 2000 0 1 (BSN.t_half_eq qz61 Bool.false 124004 1000 (@Eq.refl Real qz61)) (Enclosure.Real.IsNear.const Bool.false 124004 2000)) EMRow40.d6 rfl

noncomputable def ep1486 := @ep1314 31001 131072000 ep1315 ep1307 ep1308 ep1309 ep1310 (@ep1319 ep1313 ep1310 (ep1484 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep1485 rfl rfl

noncomputable def ep1487 := BSN.cos_dyadic_bound_f 856729 2147483648 1 0 1048576 378978 0 1 1 0 1 1 1048575 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 856729) qz274 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 856729) qz275 0 0 rfl) rfl rfl

noncomputable def ep1488 := @ep1306 262144 Bool.true 1048575 1048576 1 189304 (@ep1311 64237083 524288 89 262144 ep1486 rfl) (Enclosure.sfrac_false_div 64237083 524288) (BSN.cos_reduce2 qz977 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 30143500789015904256) qz281) 226375608064910080 72057594037927936 Bool.false 1048575 1048576 19 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q2 64237083 524288 226375608064910080 72057594037927936 19 30143500789015904256 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1048575 1048576 30143500789015904256 75557863725914323419136 856729 2147483648 378978 378608 (ep1487 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1489 := nat_lit 169543667359288573029978786953779

noncomputable def ep1490 := nat_lit 3393425024017289660400935052769367183

noncomputable abbrev qz78 := (@HPow.hPow Complex Complex Complex (@instHPow Complex Complex Complex.instPow) (@Nat.cast Complex Complex.instNatCast 32) (@Neg.neg Complex Complex.instNeg qz391))

noncomputable abbrev qz79 := (@HAdd.hAdd Complex Complex Complex qz262 (@HDiv.hDiv Complex Complex Complex qz352 (@Nat.cast Complex Complex.instNatCast 32) (@HSub.hSub Complex Complex Complex qz597 qz391 (1 : Complex))) qz351)

noncomputable abbrev qz80 := (@Nat.cast Complex Complex.instNatCast 32)

noncomputable def ep1491 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz64 2 32) (@HAdd.hAdd Complex Complex Complex qz15 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 32, @HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast n) qz65) (@HMul.hMul Complex Complex Complex qz3 qz78 (@HAdd.hAdd Complex Complex Complex qz15 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz80 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1))))))) Bool.false ep1301 ep1302 ep1303

noncomputable def ep1492 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 32, @HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast n) qz65) (@HMul.hMul Complex Complex Complex qz3 qz78 (@HAdd.hAdd Complex Complex Complex qz15 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz80 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))))) Bool.false 571132114927 1099511627776 151309553471723 26017743648063488

noncomputable def ep1493 := nat_lit 1375101377480397648836460850308401

noncomputable def ep1494 := nat_lit 43914960568861465411232880857759611

noncomputable def ep1495 := nat_lit 1786735543846744488156581213046221

noncomputable def ep1496 := nat_lit 43872809204493061550605452769367183

noncomputable def ep1497 := nat_lit 12393263563603283084778605999824063024882253824

noncomputable def ep1498 := nat_lit 186415233677324058365508228490299460764565504

noncomputable def ep1499 := @ep1492 Bool.false 88346611739 1099511627776 151267563099615 26017743648063488 Bool.true ep1493 ep1302 ep1494 ep1304 Bool.true ep1495 ep1302 ep1496 ep1304 Bool.false ep1497 ep1301 ep1302 ep1303 ep1304 Bool.false ep1498 ep1489 ep1302

noncomputable def ep1500 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 32, @HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast n) qz65) (BSN.headSumC qz64 32) Bool.false 571132114927 1099511627776 151309553471723 26017743648063488 Bool.false 88346611739 1099511627776 151267563099615

noncomputable def ep1501 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 32) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 31) (@HPow.hPow Complex Complex Complex qz16 qz49 qz65)) Bool.false 571132114927 1099511627776 151309553471723 26017743648063488 Bool.false 88346611739 1099511627776 151267563099615 26017743648063488

noncomputable def ep1502 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 31) (@HPow.hPow Complex Complex Complex qz16 qz49 qz65) Bool.false 543130605891 1099511627776 148215310852951 26017743648063488 Bool.true 107135123681 1099511627776 148152277069595 26017743648063488 Bool.false

noncomputable def ep1503 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 31) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 30) (@HPow.hPow Complex Complex Complex qz16 qz922 qz65)) Bool.false 543130605891 1099511627776 148215310852951 26017743648063488 Bool.true 107135123681 1099511627776 148152277069595 26017743648063488

noncomputable def ep1504 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 30) (@HPow.hPow Complex Complex Complex qz16 qz922 qz65) Bool.false 25100984303 68719476736 18131998787973 3252217956007936 Bool.false 17620613431 549755813888 2265513281827 406527244500992 Bool.false

noncomputable def ep1505 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 30) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 29) (@HPow.hPow Complex Complex Complex qz16 qz923 qz65)) Bool.false 25100984303 68719476736 18131998787973 3252217956007936 Bool.false 17620613431 549755813888 2265513281827 406527244500992

noncomputable def ep1506 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 29) (@HPow.hPow Complex Complex Complex qz16 qz923 qz65) Bool.false 598180346633 1099511627776 141836576194291 26017743648063488 Bool.false 90459869567 1099511627776 141790613183091 26017743648063488 Bool.true

noncomputable def ep1507 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 29) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 28) (@HPow.hPow Complex Complex Complex qz16 qz924 qz65)) Bool.false 598180346633 1099511627776 141836576194291 26017743648063488 Bool.false 90459869567 1099511627776 141790613183091 26017743648063488

noncomputable def ep1508 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 28) (@HPow.hPow Complex Complex Complex qz16 qz924 qz65) Bool.false 580114222249 1099511627776 138582306678483 26017743648063488 Bool.true 14567773881 137438953472 270534731421 50815905562624 Bool.false

noncomputable def ep1509 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 28) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 27) (@HPow.hPow Complex Complex Complex qz16 qz925 qz65)) Bool.false 580114222249 1099511627776 138582306678483 26017743648063488 Bool.true 14567773881 137438953472 270534731421 50815905562624

noncomputable def ep1510 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 27) (@HPow.hPow Complex Complex Complex qz16 qz925 qz65) Bool.false 377332461119 1099511627776 135246745050873 26017743648063488 Bool.true 56087448427 1099511627776 135194910160875 26017743648063488 Bool.false

noncomputable def ep1511 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 27) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 26) (@HPow.hPow Complex Complex Complex qz16 qz926 qz65)) Bool.false 377332461119 1099511627776 135246745050873 26017743648063488 Bool.true 56087448427 1099511627776 135194910160875 26017743648063488

noncomputable def ep1512 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 26) (@HPow.hPow Complex Complex Complex qz16 qz926 qz65) Bool.false 445598533971 1099511627776 131864021683637 26017743648063488 Bool.false 9278344421 68719476736 32949126466947 6504435912015872 Bool.true

noncomputable def ep1513 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 26) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 25) (@HPow.hPow Complex Complex Complex qz16 qz927 qz65)) Bool.false 445598533971 1099511627776 131864021683637 26017743648063488 Bool.false 9278344421 68719476736 32949126466947 6504435912015872

noncomputable def ep1514 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 25) (@HPow.hPow Complex Complex Complex qz16 qz927 qz65) Bool.false 662294107461 1099511627776 128397876462363 26017743648063488 Bool.false 111037628441 1099511627776 128350589506313 26017743648063488 Bool.true

noncomputable abbrev qz413 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 25 1)))

noncomputable def ep1515 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz927 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz361 (Real.cos qz413)) (@HMul.hMul Real Real Real qz0 qz361 (@Neg.neg Real Real.instNeg (Real.sin qz413)))) Bool.true 108347786745 549755813888 1733072610637 13008871824031744 Bool.false 37415882295 1099511627776 3445916361475 26017743648063488 (BSN.cpow_neg_s_mk qz61 124004 1000 25 (@Eq.refl Real qz61) rfl)

noncomputable def ep1516 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz363 124004 1000 0 1 3624129903009015 1125899906842624 31250000023663 5915750000000000000 22470330224636494803 56294995342131200 968781250733576663 1478937500000000000000 qz392 (BSN.isNear_log_sfrac 25 1 3624129903009015 1125899906842624 31250000023663 5915750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz929) Bool.false 60802810194841294602240 18889465931478580854784 1000000000757216 189304000000000000000 3624129903009015 1125899906842624 31250000023663 5915750000000000000 (BSN.log_rat_reduce_isNear 25 1 4 50 32 233982 524288 24973259072661432 36028797018963968 189304 1000000000000000 rfl rfl rfl rfl (ep715 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1517 := nat_lit 18176046529383754996450407980712976

noncomputable def ep1518 := BSN.cos_dyadic_bound_f 367176482 2147483648 2 1 1048576 378978 ep1517 ep110 ep1517 ep1517 ep111 ep1517 1033286 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 367176482) qz274 0 1 ep1517 ep110 ep1517 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 367176482) qz275 0 1 ep1517 ep111 ep1517 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz989 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 418542515) qz270)

noncomputable def ep1519 := @Enclosure.Real.IsNear.cos_image qz413 qz989 Bool.false 418542515 1048576 43 65536 Bool.true 1033286 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz413 Bool.false 22470330224636494803 56294995342131200 968781250733576663 1478937500000000000000 418542515 1048576 43 65536 (ep1516 rfl) rfl) (Enclosure.sfrac_false_div 418542515 1048576) (BSN.cos_reduce2 qz989 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 25837747989854824693760) qz273) 226375608064910080 72057594037927936 Bool.false 1033286 1048576 63 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q2 418542515 1048576 226375608064910080 72057594037927936 63 25837747989854824693760 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1033286 1048576 25837747989854824693760 151115727451828646838272 367176482 2147483648 378978 378608 (ep1518 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1520 := BSN.sin_dyadic_bound_f 367176482 2147483648 2 1 1048576 378978 ep1517 ep106 ep1517 ep1517 ep107 ep1517 178413 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 367176482) qz268 0 1 ep1517 ep106 ep1517 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 367176482) qz269 0 1 ep1517 ep107 ep1517 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1521 := @Enclosure.Real.IsNear.sin_image qz413 qz989 Bool.false 418542515 1048576 43 65536 Bool.true 178413 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz413 Bool.false 22470330224636494803 56294995342131200 968781250733576663 1478937500000000000000 418542515 1048576 43 65536 (ep1516 rfl) rfl) (Enclosure.sfrac_false_div 418542515 1048576) (BSN.sin_reduce2 qz989 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 25837747989854824693760) qz273) 226375608064910080 72057594037927936 Bool.false 178413 1048576 63 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q2 418542515 1048576 226375608064910080 72057594037927936 63 25837747989854824693760 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 178413 1048576 25837747989854824693760 151115727451828646838272 367176482 2147483648 378978 378608 (ep1520 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1522 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz361 (Real.cos qz413)) (@HMul.hMul Real Real Real qz0 qz361 (@Neg.neg Real Real.instNeg (Real.sin qz413))) Bool.true 108347786745 549755813888 1733072610637 13008871824031744 Bool.false 37415882295 1099511627776 3445916361475 26017743648063488 (@Enclosure.Real.IsNear.mulLit_ft qz361 (Real.cos qz413) 209715 1048576 1 1048576 516643 524288 1025701 1550778368 108347786745 549755813888 1733072610637 13008871824031744 qz608 (@Enclosure.Real.IsNear.recentre' (Real.cos qz413) Bool.true 1033286 1048576 8205608 12406226944 516643 524288 1025701 1550778368 (ep1519 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz361 (@Neg.neg Real Real.instNeg (Real.sin qz413)) 209715 1048576 1 1048576 178413 1048576 1025701 1550778368 37415882295 1099511627776 3445916361475 26017743648063488 qz608 (@Enclosure.Real.IsNear.neg (Real.sin qz413) Bool.true 178413 1048576 1025701 1550778368 (@Enclosure.Real.IsNear.recentre' (Real.sin qz413) Bool.true 178413 1048576 8205608 12406226944 178413 1048576 1025701 1550778368 (ep1521 rfl rfl) rfl)) rfl)

noncomputable def ep1523 := @ep1514 108347786745 549755813888 1733072610637 13008871824031744 Bool.false 37415882295 1099511627776 3445916361475 26017743648063488 Bool.false 244970384710526721589248 445598533971 1099511627776 131864021683637 26017743648063488 Bool.false 163226361238401251803136 9278344421 68719476736 32949126466947 6504435912015872 EMRow40.d19 (ep1515 ep1522) rfl rfl

noncomputable abbrev qz414 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 26 1)))

noncomputable def ep1524 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz926 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz364 (Real.cos qz414)) (@HMul.hMul Real Real Real qz0 qz364 (@Neg.neg Real Real.instNeg (Real.sin qz414)))) Bool.true 17066518213 274877906944 845680841809 6504435912015872 Bool.true 204540959163 1099511627776 3398404293087 26017743648063488 (BSN.cpow_neg_s_mk qz61 124004 1000 26 (@Eq.refl Real qz61) rfl)

noncomputable def ep1525 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz366 124004 1000 0 1 3668288609262839 1125899906842624 31250000023663 5915750000000000000 113720615175757271839 281474976710656000 968781250733576663 1478937500000000000000 qz392 (BSN.isNear_log_sfrac 26 1 3668288609262839 1125899906842624 31250000023663 5915750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz932) Bool.false 61543670347942250676224 18889465931478580854784 1000000000757216 189304000000000000000 3668288609262839 1125899906842624 31250000023663 5915750000000000000 (BSN.log_rat_reduce_isNear 26 1 4 52 32 254545 524288 24973259072661432 36028797018963968 189304 1000000000000000 rfl rfl rfl rfl (ep730 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1526 := nat_lit 229000822460951664561379946655826176

noncomputable def ep1527 := BSN.sin_dyadic_bound_f 691766076 2147483648 2 1 1048576 378978 ep1526 ep106 ep1526 ep1526 ep107 ep1526 331964 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 691766076) qz268 0 1 ep1526 ep106 ep1526 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 691766076) qz269 0 1 ep1526 ep107 ep1526 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz642 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6619411) (@Nat.cast Real Real.instNatCast 16384))

noncomputable def ep1528 := @Enclosure.Real.IsNear.cos_image qz414 qz642 Bool.false 6619411 16384 43 65536 Bool.true 331964 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz414 Bool.false 113720615175757271839 281474976710656000 968781250733576663 1478937500000000000000 6619411 16384 43 65536 (ep1525 rfl) rfl) (Enclosure.sfrac_false_div 6619411 16384) (BSN.cos_reduce1 qz642 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 760604844769098596352) (@Nat.cast Real Real.instNatCast 2361183241434822606848)) 226375608064910080 72057594037927936 Bool.false 331964 1048576 64 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q1 6619411 16384 226375608064910080 72057594037927936 64 760604844769098596352 2361183241434822606848 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 331964 1048576 760604844769098596352 2361183241434822606848 691766076 2147483648 378978 378608 (ep1527 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1529 := BSN.cos_dyadic_bound_f 691766076 2147483648 2 1 1048576 378978 ep1526 ep110 ep1526 ep1526 ep111 ep1526 994641 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 691766076) qz274 0 1 ep1526 ep110 ep1526 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 691766076) qz275 0 1 ep1526 ep111 ep1526 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1530 := @Enclosure.Real.IsNear.sin_image qz414 qz642 Bool.false 6619411 16384 43 65536 Bool.false 994641 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz414 Bool.false 113720615175757271839 281474976710656000 968781250733576663 1478937500000000000000 6619411 16384 43 65536 (ep1525 rfl) rfl) (Enclosure.sfrac_false_div 6619411 16384) (BSN.sin_reduce1 qz642 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 760604844769098596352) (@Nat.cast Real Real.instNatCast 2361183241434822606848)) 226375608064910080 72057594037927936 Bool.false 994641 1048576 64 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q1 6619411 16384 226375608064910080 72057594037927936 64 760604844769098596352 2361183241434822606848 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 994641 1048576 760604844769098596352 2361183241434822606848 691766076 2147483648 378978 378608 (ep1529 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1531 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz364 (Real.cos qz414)) (@HMul.hMul Real Real Real qz0 qz364 (@Neg.neg Real Real.instNeg (Real.sin qz414))) Bool.true 17066518213 274877906944 845680841809 6504435912015872 Bool.true 204540959163 1099511627776 3398404293087 26017743648063488 (@Enclosure.Real.IsNear.mulLit_ft qz364 (Real.cos qz414) 205643 1048576 1 1048576 82991 262144 1025701 1550778368 17066518213 274877906944 845680841809 6504435912015872 qz609 (@Enclosure.Real.IsNear.recentre' (Real.cos qz414) Bool.true 331964 1048576 8205608 12406226944 82991 262144 1025701 1550778368 (ep1528 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz364 (@Neg.neg Real Real.instNeg (Real.sin qz414)) 205643 1048576 1 1048576 994641 1048576 1025701 1550778368 204540959163 1099511627776 3398404293087 26017743648063488 qz609 (@Enclosure.Real.IsNear.neg (Real.sin qz414) Bool.false 994641 1048576 1025701 1550778368 (@Enclosure.Real.IsNear.recentre' (Real.sin qz414) Bool.false 994641 1048576 8205608 12406226944 994641 1048576 1025701 1550778368 (ep1530 rfl rfl) rfl)) rfl)

noncomputable def ep1532 := @ep1512 17066518213 274877906944 845680841809 6504435912015872 Bool.true 204540959163 1099511627776 3398404293087 26017743648063488 Bool.false 103720357134418980110336 377332461119 1099511627776 135246745050873 26017743648063488 Bool.true 3854300107360826294272 56087448427 1099511627776 135194910160875 26017743648063488 (ep1513 (BSN.head_sum_c_succ qz64 25 26 rfl rfl) (ep1523 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1524 ep1531) rfl rfl

noncomputable abbrev qz415 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 27 1)))

noncomputable def ep1533 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz925 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz367 (Real.cos qz415)) (@HMul.hMul Real Real Real qz0 qz367 (@Neg.neg Real Real.instNeg (Real.sin qz415)))) Bool.false 101390880565 549755813888 1667780813805 13008871824031744 Bool.true 60454742621 1099511627776 3318872326677 26017743648063488 (BSN.cpow_neg_s_mk qz61 124004 1000 27 (@Eq.refl Real qz61) rfl)

noncomputable def ep1534 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz369 124004 1000 0 1 3710780868205815 1125899906842624 31250000023663 5915750000000000000 23007583539049694163 56294995342131200 968781250733576663 1478937500000000000000 qz392 (BSN.isNear_log_sfrac 27 1 3710780868205815 1125899906842624 31250000023663 5915750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz935) Bool.false 62256572154556490711040 18889465931478580854784 1000000000757216 189304000000000000000 3710780868205815 1125899906842624 31250000023663 5915750000000000000 (BSN.log_rat_reduce_isNear 27 1 4 54 32 274332 524288 24973259072661432 36028797018963968 189304 1000000000000000 rfl rfl rfl rfl (ep745 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1535 := nat_lit 149879380124216389554586986819210000

noncomputable def ep1536 := BSN.cos_dyadic_bound_f 622207830 2147483648 2 1 1048576 378978 ep1535 ep110 ep1535 ep1535 ep111 ep1535 1004870 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 622207830) qz274 0 1 ep1535 ep110 ep1535 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 622207830) qz275 0 1 ep1535 ep111 ep1535 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz990 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 214274819) qz279)

noncomputable def ep1537 := @Enclosure.Real.IsNear.cos_image qz415 qz990 Bool.false 214274819 524288 43 65536 Bool.false 1004870 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz415 Bool.false 23007583539049694163 56294995342131200 968781250733576663 1478937500000000000000 214274819 524288 43 65536 (ep1534 rfl) rfl) (Enclosure.sfrac_false_div 214274819 524288) (BSN.cos_reduce0 qz990 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 21891991809725476896768) qz281) 226375608064910080 72057594037927936 Bool.false 1004870 1048576 65 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q0 214274819 524288 226375608064910080 72057594037927936 65 21891991809725476896768 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1004870 1048576 21891991809725476896768 75557863725914323419136 622207830 2147483648 378978 378608 (ep1536 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1538 := BSN.sin_dyadic_bound_f 622207830 2147483648 2 1 1048576 378978 ep1535 ep106 ep1535 ep1535 ep107 ep1535 299579 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 622207830) qz268 0 1 ep1535 ep106 ep1535 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 622207830) qz269 0 1 ep1535 ep107 ep1535 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1539 := @Enclosure.Real.IsNear.sin_image qz415 qz990 Bool.false 214274819 524288 43 65536 Bool.false 299579 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz415 Bool.false 23007583539049694163 56294995342131200 968781250733576663 1478937500000000000000 214274819 524288 43 65536 (ep1534 rfl) rfl) (Enclosure.sfrac_false_div 214274819 524288) (BSN.sin_reduce0 qz990 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 21891991809725476896768) qz281) 226375608064910080 72057594037927936 Bool.false 299579 1048576 65 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q0 214274819 524288 226375608064910080 72057594037927936 65 21891991809725476896768 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 299579 1048576 21891991809725476896768 75557863725914323419136 622207830 2147483648 378978 378608 (ep1538 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1540 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz367 (Real.cos qz415)) (@HMul.hMul Real Real Real qz0 qz367 (@Neg.neg Real Real.instNeg (Real.sin qz415))) Bool.false 101390880565 549755813888 1667780813805 13008871824031744 Bool.true 60454742621 1099511627776 3318872326677 26017743648063488 (@Enclosure.Real.IsNear.mulLit_ff qz367 (Real.cos qz415) 201799 1048576 1 1048576 502435 524288 1025701 1550778368 101390880565 549755813888 1667780813805 13008871824031744 qz610 (@Enclosure.Real.IsNear.recentre' (Real.cos qz415) Bool.false 1004870 1048576 8205608 12406226944 502435 524288 1025701 1550778368 (ep1537 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz367 (@Neg.neg Real Real.instNeg (Real.sin qz415)) 201799 1048576 1 1048576 299579 1048576 1025701 1550778368 60454742621 1099511627776 3318872326677 26017743648063488 qz610 (@Enclosure.Real.IsNear.neg (Real.sin qz415) Bool.false 299579 1048576 1025701 1550778368 (@Enclosure.Real.IsNear.recentre' (Real.sin qz415) Bool.false 299579 1048576 8205608 12406226944 299579 1048576 1025701 1550778368 (ep1539 rfl rfl) rfl)) rfl)

noncomputable def ep1541 := @ep1510 101390880565 549755813888 1667780813805 13008871824031744 Bool.true 60454742621 1099511627776 3318872326677 26017743648063488 Bool.false 318921166400503112794112 580114222249 1099511627776 138582306678483 26017743648063488 Bool.true 128139494183768055349248 14567773881 137438953472 270534731421 50815905562624 (ep1511 (BSN.head_sum_c_succ qz64 26 27 rfl rfl) (ep1532 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1533 ep1540) rfl rfl

noncomputable abbrev qz416 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 28 1)))

noncomputable def ep1542 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz924 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz370 (Real.cos qz416)) (@HMul.hMul Real Real Real qz0 qz370 (@Neg.neg Real Real.instNeg (Real.sin qz416)))) Bool.false 564566387 34359738368 101695922369 813054489001984 Bool.false 207002060615 1099511627776 3276830695539 26017743648063488 (BSN.cpow_neg_s_mk qz61 124004 1000 28 (@Eq.refl Real qz61) rfl)

noncomputable def ep1543 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz372 124004 1000 0 1 3751726938922231 1125899906842624 31250000023663 5915750000000000000 116307286833528083231 281474976710656000 968781250733576663 1478937500000000000000 qz392 (BSN.isNear_log_sfrac 28 1 3751726938922231 1125899906842624 31250000023663 5915750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz938) Bool.false 62943533227317076688896 18889465931478580854784 1000000000757216 189304000000000000000 3751726938922231 1125899906842624 31250000023663 5915750000000000000 (BSN.log_rat_reduce_isNear 28 1 4 56 32 293399 524288 24973259072661432 36028797018963968 189304 1000000000000000 rfl rfl rfl rfl (ep760 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1544 := BSN.sin_dyadic_bound_f 186948463 2147483648 1 0 1048576 378978 0 1 1 0 1 1 91168 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 186948463) qz268 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 186948463) qz269 0 0 rfl) rfl rfl

noncomputable abbrev qz991 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 433278407) qz270)

noncomputable def ep1545 := @Enclosure.Real.IsNear.cos_image qz416 qz991 Bool.false 433278407 1048576 43 65536 Bool.false 91168 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz416 Bool.false 116307286833528083231 281474976710656000 968781250733576663 1478937500000000000000 433278407 1048576 43 65536 (ep1543 rfl) rfl) (Enclosure.sfrac_false_div 433278407 1048576) (BSN.cos_reduce3 qz991 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13155328614914393636864) qz273) 226375608064910080 72057594037927936 Bool.false 91168 1048576 65 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q3 433278407 1048576 226375608064910080 72057594037927936 65 13155328614914393636864 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 91168 1048576 13155328614914393636864 151115727451828646838272 186948463 2147483648 378978 378608 (ep1544 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1546 := nat_lit 1221483474556642600272565573892161

noncomputable def ep1547 := BSN.cos_dyadic_bound_f 186948463 2147483648 2 1 1048576 378978 ep1546 ep110 ep1546 ep1546 ep111 ep1546 1044605 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 186948463) qz274 0 1 ep1546 ep110 ep1546 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 186948463) qz275 0 1 ep1546 ep111 ep1546 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1548 := @Enclosure.Real.IsNear.sin_image qz416 qz991 Bool.false 433278407 1048576 43 65536 Bool.true 1044605 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz416 Bool.false 116307286833528083231 281474976710656000 968781250733576663 1478937500000000000000 433278407 1048576 43 65536 (ep1543 rfl) rfl) (Enclosure.sfrac_false_div 433278407 1048576) (BSN.sin_reduce3 qz991 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13155328614914393636864) qz273) 226375608064910080 72057594037927936 Bool.false 1044605 1048576 65 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q3 433278407 1048576 226375608064910080 72057594037927936 65 13155328614914393636864 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1044605 1048576 13155328614914393636864 151115727451828646838272 186948463 2147483648 378978 378608 (ep1547 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1549 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz370 (Real.cos qz416)) (@HMul.hMul Real Real Real qz0 qz370 (@Neg.neg Real Real.instNeg (Real.sin qz416))) Bool.false 564566387 34359738368 101695922369 813054489001984 Bool.false 207002060615 1099511627776 3276830695539 26017743648063488 (@Enclosure.Real.IsNear.mulLit_ff qz370 (Real.cos qz416) 198163 1048576 1 1048576 2849 32768 1025701 1550778368 564566387 34359738368 101695922369 813054489001984 qz611 (@Enclosure.Real.IsNear.recentre' (Real.cos qz416) Bool.false 91168 1048576 8205608 12406226944 2849 32768 1025701 1550778368 (ep1545 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz370 (@Neg.neg Real Real.instNeg (Real.sin qz416)) 198163 1048576 1 1048576 1044605 1048576 1025701 1550778368 207002060615 1099511627776 3276830695539 26017743648063488 qz611 (@Enclosure.Real.IsNear.neg (Real.sin qz416) Bool.true 1044605 1048576 1025701 1550778368 (@Enclosure.Real.IsNear.recentre' (Real.sin qz416) Bool.true 1044605 1048576 8205608 12406226944 1044605 1048576 1025701 1550778368 (ep1548 rfl rfl) rfl)) rfl)

noncomputable def ep1550 := @ep1508 564566387 34359738368 101695922369 813054489001984 Bool.false 207002060615 1099511627776 3276830695539 26017743648063488 Bool.false 20553320207189429714944 598180346633 1099511627776 141836576194291 26017743648063488 Bool.false 12432709804502101786624 90459869567 1099511627776 141790613183091 26017743648063488 (ep1509 (BSN.head_sum_c_succ qz64 27 28 rfl rfl) (ep1541 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1542 ep1549) rfl rfl

noncomputable abbrev qz417 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 29 1)))

noncomputable def ep1551 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz923 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz373 (Real.cos qz417)) (@HMul.hMul Real Real Real qz0 qz373 (@Neg.neg Real Real.instNeg (Real.sin qz417)))) Bool.true 196564597785 1099511627776 3219414109493 26017743648063488 Bool.true 55218642705 1099511627776 3202236853837 26017743648063488 (BSN.cpow_neg_s_mk qz61 124004 1000 29 (@Eq.refl Real qz61) rfl)

noncomputable def ep1552 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz375 124004 1000 0 1 3791236343078135 1125899906842624 31250000023663 5915750000000000000 23506423574353052627 56294995342131200 968781250733576663 1478937500000000000000 qz392 (BSN.isNear_log_sfrac 29 1 3791236343078135 1125899906842624 31250000023663 5915750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz941) Bool.false 63606391034871975772160 18889465931478580854784 1000000000757216 189304000000000000000 3791236343078135 1125899906842624 31250000023663 5915750000000000000 (BSN.log_rat_reduce_isNear 29 1 4 58 32 311797 524288 24973259072661432 36028797018963968 189304 1000000000000000 rfl rfl rfl rfl (ep775 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1553 := nat_lit 3873475252537841611493114757297915947087393610360583118347404294801479332290145

noncomputable def ep1554 := nat_lit 3620652107572162215896476512099268234459254929481353722793691866923457601121

noncomputable def ep1555 := nat_lit 10138954129424944529370515783332095331896906376296652642025345270981236462739041

noncomputable def ep1556 := BSN.sin_dyadic_bound_f 2785148459 2147483648 3 2 1048576 378978 ep1553 ep88 ep1554 ep1555 ep91 ep1554 1009499 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2785148459) qz268 0 2 ep1553 ep88 ep1554 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2785148459) qz269 0 2 ep1555 ep91 ep1554 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz992 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 218920629) qz279)

noncomputable def ep1557 := @Enclosure.Real.IsNear.cos_image qz417 qz992 Bool.false 218920629 524288 43 65536 Bool.true 1009499 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz417 Bool.false 23506423574353052627 56294995342131200 968781250733576663 1478937500000000000000 218920629 524288 43 65536 (ep1552 rfl) rfl) (Enclosure.sfrac_false_div 218920629 524288) (BSN.cos_reduce1 qz992 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 97993699718739565477888) qz281) 226375608064910080 72057594037927936 Bool.false 1009499 1048576 66 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q1 218920629 524288 226375608064910080 72057594037927936 66 97993699718739565477888 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1009499 1048576 97993699718739565477888 75557863725914323419136 2785148459 2147483648 378978 378608 (ep1556 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1558 := nat_lit 2153539874568832967369906632504219645374978341280093445180910693497232276872801

noncomputable def ep1559 := nat_lit 6453378319491354577677926944488460399656016513981317628097144696757849915416161

noncomputable def ep1560 := BSN.cos_dyadic_bound_f 2785148459 2147483648 3 2 1048576 378978 ep1558 ep95 ep1554 ep1559 ep97 ep1554 283587 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2785148459) qz274 0 2 ep1558 ep95 ep1554 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2785148459) qz275 0 2 ep1559 ep97 ep1554 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1561 := @Enclosure.Real.IsNear.sin_image qz417 qz992 Bool.false 218920629 524288 43 65536 Bool.false 283587 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz417 Bool.false 23506423574353052627 56294995342131200 968781250733576663 1478937500000000000000 218920629 524288 43 65536 (ep1552 rfl) rfl) (Enclosure.sfrac_false_div 218920629 524288) (BSN.sin_reduce1 qz992 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 97993699718739565477888) qz281) 226375608064910080 72057594037927936 Bool.false 283587 1048576 66 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q1 218920629 524288 226375608064910080 72057594037927936 66 97993699718739565477888 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 283587 1048576 97993699718739565477888 75557863725914323419136 2785148459 2147483648 378978 378608 (ep1560 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1562 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz373 (Real.cos qz417)) (@HMul.hMul Real Real Real qz0 qz373 (@Neg.neg Real Real.instNeg (Real.sin qz417))) Bool.true 196564597785 1099511627776 3219414109493 26017743648063488 Bool.true 55218642705 1099511627776 3202236853837 26017743648063488 (@Enclosure.Real.IsNear.mulLit_ft qz373 (Real.cos qz417) 194715 1048576 1 1048576 1009499 1048576 1025701 1550778368 196564597785 1099511627776 3219414109493 26017743648063488 qz612 (@Enclosure.Real.IsNear.recentre' (Real.cos qz417) Bool.true 1009499 1048576 8205608 12406226944 1009499 1048576 1025701 1550778368 (ep1557 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz373 (@Neg.neg Real Real.instNeg (Real.sin qz417)) 194715 1048576 1 1048576 283587 1048576 1025701 1550778368 55218642705 1099511627776 3202236853837 26017743648063488 qz612 (@Enclosure.Real.IsNear.neg (Real.sin qz417) Bool.false 283587 1048576 1025701 1550778368 (@Enclosure.Real.IsNear.recentre' (Real.sin qz417) Bool.false 283587 1048576 8205608 12406226944 283587 1048576 1025701 1550778368 (ep1561 rfl rfl) rfl)) rfl)

noncomputable def ep1563 := @ep1506 196564597785 1099511627776 3219414109493 26017743648063488 Bool.true 55218642705 1099511627776 3202236853837 26017743648063488 Bool.false 441581185756341676802048 25100984303 68719476736 18131998787973 3252217956007936 Bool.false 38748138711860916518912 17620613431 549755813888 2265513281827 406527244500992 (ep1507 (BSN.head_sum_c_succ qz64 28 29 rfl rfl) (ep1550 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1551 ep1562) rfl rfl

noncomputable abbrev qz418 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 30 1)))

noncomputable def ep1564 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz922 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz376 (Real.cos qz418)) (@HMul.hMul Real Real Real qz0 qz376 (@Neg.neg Real Real.instNeg (Real.sin qz418)))) Bool.false 141514857043 1099511627776 3159320549167 26017743648063488 Bool.true 142376350543 1099511627776 3159427032667 26017743648063488 (BSN.cpow_neg_s_mk qz61 124004 1000 30 (@Eq.refl Real qz61) rfl)

noncomputable def ep1565 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz378 124004 1000 0 1 3829405717437687 1125899906842624 31250000023663 5915750000000000000 118715406646285734687 281474976710656000 968781250733576663 1478937500000000000000 qz392 (BSN.isNear_log_sfrac 30 1 3829405717437687 1125899906842624 31250000023663 5915750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz944) Bool.false 64246766873087041339392 18889465931478580854784 1000000000757216 189304000000000000000 3829405717437687 1125899906842624 31250000023663 5915750000000000000 (BSN.log_rat_reduce_isNear 30 1 4 60 32 329571 524288 24973259072661432 36028797018963968 189304 1000000000000000 rfl rfl rfl rfl (ep786 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1566 := nat_lit 293702046112341991968563059837388692734549961009989634379991422059655846182881

noncomputable def ep1567 := nat_lit 67539321528212969968692861249387730411332196170149428760523562574660780001

noncomputable def ep1568 := nat_lit 880971059693969549965751793789667302742827218637628604282453219053818216988641

noncomputable def ep1569 := BSN.cos_dyadic_bound_f 1693146693 2147483648 3 2 1048576 378978 ep1566 ep95 ep1567 ep1568 ep97 ep1567 739201 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1693146693) qz274 0 2 ep1566 ep95 ep1567 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1693146693) qz275 0 2 ep1568 ep97 ep1567 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz643 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 55281169) (@Nat.cast Real Real.instNatCast 131072))

noncomputable def ep1570 := @Enclosure.Real.IsNear.cos_image qz418 qz643 Bool.false 55281169 131072 43 65536 Bool.false 739201 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz418 Bool.false 118715406646285734687 281474976710656000 968781250733576663 1478937500000000000000 55281169 131072 43 65536 (ep1565 rfl) rfl) (Enclosure.sfrac_false_div 55281169 131072) (BSN.cos_reduce0 qz643 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14893075812089686130688) qz565) 226375608064910080 72057594037927936 Bool.false 739201 1048576 67 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q0 55281169 131072 226375608064910080 72057594037927936 67 14893075812089686130688 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 739201 1048576 14893075812089686130688 18889465931478580854784 1693146693 2147483648 378978 378608 (ep1569 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1571 := nat_lit 8218231046168814665658182011280390001

noncomputable def ep1572 := BSN.sin_dyadic_bound_f 1693146693 2147483648 2 1 1048576 378978 ep1571 ep106 ep1571 ep1571 ep107 ep1571 743701 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1693146693) qz268 0 1 ep1571 ep106 ep1571 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1693146693) qz269 0 1 ep1571 ep107 ep1571 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1573 := @Enclosure.Real.IsNear.sin_image qz418 qz643 Bool.false 55281169 131072 43 65536 Bool.false 743701 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz418 Bool.false 118715406646285734687 281474976710656000 968781250733576663 1478937500000000000000 55281169 131072 43 65536 (ep1565 rfl) rfl) (Enclosure.sfrac_false_div 55281169 131072) (BSN.sin_reduce0 qz643 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14893075812089686130688) qz565) 226375608064910080 72057594037927936 Bool.false 743701 1048576 67 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q0 55281169 131072 226375608064910080 72057594037927936 67 14893075812089686130688 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 743701 1048576 14893075812089686130688 18889465931478580854784 1693146693 2147483648 378978 378608 (ep1572 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1574 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz376 (Real.cos qz418)) (@HMul.hMul Real Real Real qz0 qz376 (@Neg.neg Real Real.instNeg (Real.sin qz418))) Bool.false 141514857043 1099511627776 3159320549167 26017743648063488 Bool.true 142376350543 1099511627776 3159427032667 26017743648063488 (@Enclosure.Real.IsNear.mulLit_ff qz376 (Real.cos qz418) 191443 1048576 1 1048576 739201 1048576 1025701 1550778368 141514857043 1099511627776 3159320549167 26017743648063488 qz614 (@Enclosure.Real.IsNear.recentre' (Real.cos qz418) Bool.false 739201 1048576 8205608 12406226944 739201 1048576 1025701 1550778368 (ep1570 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz376 (@Neg.neg Real Real.instNeg (Real.sin qz418)) 191443 1048576 1 1048576 743701 1048576 1025701 1550778368 142376350543 1099511627776 3159427032667 26017743648063488 qz614 (@Enclosure.Real.IsNear.neg (Real.sin qz418) Bool.false 743701 1048576 1025701 1550778368 (@Enclosure.Real.IsNear.recentre' (Real.sin qz418) Bool.false 743701 1048576 8205608 12406226944 743701 1048576 1025701 1550778368 (ep1573 rfl rfl) rfl)) rfl)

noncomputable def ep1575 := @ep1504 141514857043 1099511627776 3159320549167 26017743648063488 Bool.true 142376350543 1099511627776 3159427032667 26017743648063488 Bool.false 37323651036136159051776 543130605891 1099511627776 148215310852951 26017743648063488 Bool.true 58898157115239697481728 107135123681 1099511627776 148152277069595 26017743648063488 (ep1505 (BSN.head_sum_c_succ qz64 29 30 rfl rfl) (ep1563 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1564 ep1574) rfl rfl

noncomputable abbrev qz419 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 31 1)))

noncomputable def ep1576 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz49 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz379 (Real.cos qz419)) (@HMul.hMul Real Real Real qz0 qz379 (@Neg.neg Real Real.instNeg (Real.sin qz419)))) Bool.false 7000377259 274877906944 773560654693 6504435912015872 Bool.false 48870433855 274877906944 778821507505 6504435912015872 (BSN.cpow_neg_s_mk qz61 124004 1000 31 (@Eq.refl Real qz61) rfl)

noncomputable def ep1577 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz381 124004 1000 0 1 3866325256314103 1125899906842624 31250000023663 5915750000000000000 119859949270993507103 281474976710656000 968781250733576663 1478937500000000000000 qz392 (BSN.isNear_log_sfrac 31 1 3866325256314103 1125899906842624 31250000023663 5915750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz947) Bool.false 64866173951437069877248 18889465931478580854784 1000000000757216 189304000000000000000 3866325256314103 1125899906842624 31250000023663 5915750000000000000 (BSN.log_rat_reduce_isNear 31 1 4 62 32 346763 524288 24973259072661432 36028797018963968 189304 1000000000000000 rfl rfl rfl rfl (ep812 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1578 := BSN.sin_dyadic_bound_f 305536606 2147483648 1 0 1048576 378978 0 1 1 0 1 1 148684 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 305536606) qz268 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 305536606) qz269 0 0 rfl) rfl rfl

noncomputable abbrev qz993 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 223256553) qz279)

noncomputable def ep1579 := @Enclosure.Real.IsNear.cos_image qz419 qz993 Bool.false 223256553 524288 43 65536 Bool.false 148684 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz419 Bool.false 119859949270993507103 281474976710656000 968781250733576663 1478937500000000000000 223256553 524288 43 65536 (ep1577 rfl) rfl) (Enclosure.sfrac_false_div 223256553 524288) (BSN.cos_reduce3 qz993 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 10750113654543405285376) qz281) 226375608064910080 72057594037927936 Bool.false 148684 1048576 67 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q3 223256553 524288 226375608064910080 72057594037927936 67 10750113654543405285376 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 148684 1048576 10750113654543405285376 75557863725914323419136 305536606 2147483648 378978 378608 (ep1578 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1580 := nat_lit 8714711213891918528436298032583696

noncomputable def ep1581 := BSN.cos_dyadic_bound_f 305536606 2147483648 2 1 1048576 378978 ep1580 ep110 ep1580 ep1580 ep111 ep1580 1037980 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 305536606) qz274 0 1 ep1580 ep110 ep1580 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 305536606) qz275 0 1 ep1580 ep111 ep1580 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1582 := @Enclosure.Real.IsNear.sin_image qz419 qz993 Bool.false 223256553 524288 43 65536 Bool.true 1037980 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz419 Bool.false 119859949270993507103 281474976710656000 968781250733576663 1478937500000000000000 223256553 524288 43 65536 (ep1577 rfl) rfl) (Enclosure.sfrac_false_div 223256553 524288) (BSN.sin_reduce3 qz993 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 10750113654543405285376) qz281) 226375608064910080 72057594037927936 Bool.false 1037980 1048576 67 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q3 223256553 524288 226375608064910080 72057594037927936 67 10750113654543405285376 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1037980 1048576 10750113654543405285376 75557863725914323419136 305536606 2147483648 378978 378608 (ep1581 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1583 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz379 (Real.cos qz419)) (@HMul.hMul Real Real Real qz0 qz379 (@Neg.neg Real Real.instNeg (Real.sin qz419))) Bool.false 7000377259 274877906944 773560654693 6504435912015872 Bool.false 48870433855 274877906944 778821507505 6504435912015872 (@Enclosure.Real.IsNear.mulLit_ff qz379 (Real.cos qz419) 188329 1048576 1 1048576 37171 262144 1025701 1550778368 7000377259 274877906944 773560654693 6504435912015872 qz616 (@Enclosure.Real.IsNear.recentre' (Real.cos qz419) Bool.false 148684 1048576 8205608 12406226944 37171 262144 1025701 1550778368 (ep1579 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz379 (@Neg.neg Real Real.instNeg (Real.sin qz419)) 188329 1048576 1 1048576 259495 262144 1025701 1550778368 48870433855 274877906944 778821507505 6504435912015872 qz616 (@Enclosure.Real.IsNear.neg (Real.sin qz419) Bool.true 259495 262144 1025701 1550778368 (@Enclosure.Real.IsNear.recentre' (Real.sin qz419) Bool.true 1037980 1048576 8205608 12406226944 259495 262144 1025701 1550778368 (ep1582 rfl rfl) rfl)) rfl)

noncomputable def ep1584 := @ep1502 7000377259 274877906944 773560654693 6504435912015872 Bool.false 48870433855 274877906944 778821507505 6504435912015872 Bool.false 156991600339633819353088 571132114927 1099511627776 151309553471723 26017743648063488 Bool.false 24284531720410540015616 88346611739 1099511627776 151267563099615 26017743648063488 (ep1503 (BSN.head_sum_c_succ qz64 30 31 rfl rfl) (ep1575 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1576 ep1583) rfl rfl

noncomputable def ep1585 := @Enclosure.Complex.IsNear.mul qz78 (@HAdd.hAdd Complex Complex Complex qz15 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz80 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1))))) Bool.true ep1493 ep1302 ep1494 ep1304 Bool.true

noncomputable def ep1586 := nat_lit 1552012291534080100769571005721

noncomputable def ep1587 := nat_lit 21641544191638604590612480000000

noncomputable def ep1588 := nat_lit 15142038792659231428332492300279

noncomputable def ep1589 := @Enclosure.Real.IsNear.subLit_tt_n (@HMul.hMul Real Real Real qz0 (Complex.re qz78) (Complex.re (@HAdd.hAdd Complex Complex Complex qz15 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz80 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 (Complex.im qz78) (Complex.im (@HAdd.hAdd Complex Complex Complex qz15 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz80 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1))))))) ep1586 ep1587 ep1588

noncomputable def ep1590 := nat_lit 256051930103372150213831557120000000

noncomputable def ep1591 := nat_lit 92728112623860616132326632781931

noncomputable def ep1592 := nat_lit 6086684303898357541109760000000000

noncomputable def ep1593 := nat_lit 9845373285378194697484773182131861

noncomputable def ep1594 := nat_lit 7439829307181286001440823472310515557592548583939369861120000000

noncomputable def ep1595 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re qz78) (Complex.re (@HAdd.hAdd Complex Complex Complex qz15 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz80 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))))) 39175172509 274877906944 382208301491 3252217956007936 39617242047307511469

noncomputable abbrev qz420 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 32 1)))

noncomputable abbrev qz644 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 32)))

noncomputable abbrev qz994 := (@Neg.neg Real Real.instNeg (Real.sin qz420))

noncomputable def ep1596 := @Enclosure.Complex.IsNear.of_eq qz78 (Complex.mk (@HMul.hMul Real Real Real qz0 qz644 (Real.cos qz420)) (@HMul.hMul Real Real Real qz0 qz644 qz994)) Bool.true 39175172509 274877906944 382208301491 3252217956007936 Bool.true 7187079599 68719476736 763085535569 6504435912015872 (BSN.cpow_neg_s_mk qz61 124004 1000 32 (@Eq.refl Real qz61) rfl)

noncomputable abbrev qz645 := (Real.sqrt (@Nat.cast Real Real.instNatCast 32))

noncomputable abbrev qz646 := (@Nat.cast Real Real.instNatCast 32)

noncomputable def ep1597 := @Enclosure.Real.IsNear.inv_image qz645 5931641 1048576 1 1048576 92681 92682 524288 (@Enclosure.Real.IsNear.of_eq qz645 (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz646 qz267)) Bool.false 5931641 1048576 1 1048576 (BSN.sqrt_natCast_div_one 32) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz646 qz267)) Bool.false 5931641 1048576 1 1048576 5931641 1048576 1 1048576 (BSN.sqrt_enclosure 32 1 2965820 2965821 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep1598 := BSN.log_dyadic_bound 0 64 1 0 1 524288 189304 0 1 0 64 64 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 64) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz421 := (Real.log (Enclosure.sfrac Bool.false 32 1))

noncomputable def ep1599 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz421 124004 1000 0 1 15608286920413395 4503599627370496 25000000023663 4732600000000000000 96774500563947131679 225179981368524800 775025000733576663 1183150000000000000000 qz392 (BSN.isNear_log_sfrac 32 1 15608286920413395 4503599627370496 25000000023663 4732600000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 qz646 qz267)) Bool.false 65465900263437584302080 18889465931478580854784 1000000000946520 189304000000000000000 15608286920413395 4503599627370496 25000000023663 4732600000000000000 (BSN.log_rat_reduce_isNear 32 1 5 64 64 0 524288 24973259072661432 36028797018963968 189304 1000000000000000 rfl rfl rfl rfl (ep1598 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1600 := nat_lit 1057839920431547125576152918822798452869619631973509794730557614604542068138240

noncomputable def ep1601 := nat_lit 270405392896146696344820133939008107065088072694418784189764842694476308736

noncomputable def ep1602 := nat_lit 2770095325732220139000604126223808982485184131622448974834200799933247693005056

noncomputable def ep1603 := BSN.sin_dyadic_bound_f 2013733146 2147483648 3 2 1048576 378978 ep1600 ep88 ep1601 ep1602 ep91 ep1601 845372 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2013733146) qz268 0 2 ep1600 ep88 ep1601 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2013733146) qz269 0 2 ep1602 ep91 ep1601 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz995 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 450641385) qz270)

noncomputable def ep1604 := @Enclosure.Real.IsNear.cos_image qz420 qz995 Bool.false 450641385 1048576 687 1048576 Bool.true 845372 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz420 Bool.false 96774500563947131679 225179981368524800 775025000733576663 1183150000000000000000 450641385 1048576 687 1048576 (ep1599 rfl) rfl) (Enclosure.sfrac_false_div 450641385 1048576) (BSN.cos_reduce1 qz995 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 141703872619150709882880) qz273) 226375608064910080 72057594037927936 Bool.false 845372 1048576 68 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q1 450641385 1048576 226375608064910080 72057594037927936 68 141703872619150709882880 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 845372 1048576 141703872619150709882880 151115727451828646838272 2013733146 2147483648 378978 378608 (ep1603 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1605 := nat_lit 587809024858813357185127097183305366308484279128702960976616348043720916214016

noncomputable def ep1606 := nat_lit 1762886263790647778162691651282038082711322661240720045361469514445773796024576

noncomputable def ep1607 := BSN.cos_dyadic_bound_f 2013733146 2147483648 3 2 1048576 378978 ep1605 ep95 ep1601 ep1606 ep97 ep1601 620368 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2013733146) qz274 0 2 ep1605 ep95 ep1601 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2013733146) qz275 0 2 ep1606 ep97 ep1601 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1608 := @Enclosure.Real.IsNear.sin_image qz420 qz995 Bool.false 450641385 1048576 687 1048576 Bool.false 620368 1048576 1 189304 (@Enclosure.Real.IsNear.recentre' qz420 Bool.false 96774500563947131679 225179981368524800 775025000733576663 1183150000000000000000 450641385 1048576 687 1048576 (ep1599 rfl) rfl) (Enclosure.sfrac_false_div 450641385 1048576) (BSN.sin_reduce1 qz995 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 141703872619150709882880) qz273) 226375608064910080 72057594037927936 Bool.false 620368 1048576 68 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q1 450641385 1048576 226375608064910080 72057594037927936 68 141703872619150709882880 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 620368 1048576 141703872619150709882880 151115727451828646838272 2013733146 2147483648 378978 378608 (ep1607 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1609 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz644 (Real.cos qz420)) (@HMul.hMul Real Real Real qz0 qz644 qz994) Bool.true 39175172509 274877906944 382208301491 3252217956007936 Bool.true 7187079599 68719476736 763085535569 6504435912015872 (@Enclosure.Real.IsNear.mulLit_ft qz644 (Real.cos qz420) 185363 1048576 1 1048576 211343 262144 16387553 24812453888 39175172509 274877906944 382208301491 3252217956007936 (@Enclosure.Real.IsNear.recentre' qz644 Bool.false 185363 1048576 1 1048576 185363 1048576 1 1048576 (ep1597 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' (Real.cos qz420) Bool.true 845372 1048576 131100424 198499631104 211343 262144 16387553 24812453888 (ep1604 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz644 qz994 185363 1048576 1 1048576 38773 65536 16387553 24812453888 7187079599 68719476736 763085535569 6504435912015872 (@Enclosure.Real.IsNear.recentre' qz644 Bool.false 185363 1048576 1 1048576 185363 1048576 1 1048576 (ep1597 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg (Real.sin qz420) Bool.false 38773 65536 16387553 24812453888 (@Enclosure.Real.IsNear.recentre' (Real.sin qz420) Bool.false 620368 1048576 131100424 198499631104 38773 65536 16387553 24812453888 (ep1608 rfl rfl) rfl)) rfl)

noncomputable def ep1610 := @ep1595 78731479121920000000 0 1 ep1586 ep1587 ep1588 ep1590 (@Enclosure.Complex.IsNear.re_isNear qz78 Bool.true 39175172509 274877906944 382208301491 3252217956007936 Bool.true 7187079599 68719476736 763085535569 6504435912015872 (ep1596 ep1609))

noncomputable def ep1611 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz15 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz80 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1))))) Bool.false 39617242047307511469 78731479121920000000 0 1 Bool.false

noncomputable def ep1612 := @Enclosure.Complex.IsNear.addLitP qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz80 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) Bool.false 479538813 961077626 0 1 Bool.true 124004000

noncomputable def ep1613 := @ep1612 480538813 0 1 Bool.false 693851313 163840000000 0 1 Bool.false 74413291054313 184320000000000 0 1 Bool.false 79234484094615022938 39617242047307511469 78731479121920000000 0 1 Bool.false 12902057274663087550469 12902057274663087550469 88572914012160000000000 0 1

noncomputable abbrev qz81 := (@HDiv.hDiv Complex Complex Complex qz352 (@Nat.cast Complex Complex.instNatCast 32) (@HSub.hSub Complex Complex Complex qz597 qz391 (1 : Complex)))

noncomputable def ep1614 := @Enclosure.Complex.IsNear.addLitP qz81 qz26 Bool.true 64000000 61508968064 0 1 Bool.true 15872512000 61508968064 0 1

noncomputable def ep1615 := @Enclosure.Complex.IsNear.of_eq qz81 (Complex.mk (Enclosure.sfrac Bool.true 64000000 61508968064) (Enclosure.sfrac Bool.true 15872512000 61508968064)) Bool.true 64000000 61508968064 0 1 Bool.true 15872512000 61508968064 0 1

noncomputable def ep1616 := @ep1614 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 61380968064 479538813 961077626 0 1 Bool.true 15872512000 124004000 480538813 0 1 (ep1615 (BSN.N_div_s_sub_one_mk qz61 124004 1000 32 (@Eq.refl Real qz61) rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 64000000 61508968064) (Enclosure.sfrac Bool.true 15872512000 61508968064) Bool.true 64000000 61508968064 0 1 Bool.true 15872512000 61508968064 0 1 (Enclosure.Real.IsNear.const Bool.true 64000000 61508968064) (Enclosure.Real.IsNear.const Bool.true 15872512000 61508968064))) qz357 rfl

noncomputable abbrev qz422 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz80 3))

noncomputable def ep1617 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz80 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz15 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz80 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) qz422)) Bool.false 693851313 163840000000 0 1

noncomputable def ep1618 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz80 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) qz422) Bool.false 1 768 0 1 Bool.false

noncomputable def ep1619 := @ep1618 31001 96000 0 1 Bool.false 1441553939 491520000000 0 1 Bool.false 14891371054313 184320000000000 0 1 Bool.false 1598633425152 693851313 163840000000 0 1 Bool.false 7143675941214048000 74413291054313 184320000000000 0

noncomputable abbrev qz423 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz80 1))

noncomputable def ep1620 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz80 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz15 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz80 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) qz423)) Bool.false 1 768 0 1

noncomputable def ep1621 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz80 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) qz423) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1622 := @ep1621 0 1 0 1 Bool.false 1 768 0 1 Bool.false 31001 96000 0 1 Bool.false 1 1 768 0 1 Bool.false 31001 31001 96000 0

noncomputable def ep1623 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz80 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (Complex.mk qz264 qz264) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1624 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) qz423 Bool.false 1 768 0 1 Bool.false 31001 96000 0 1

noncomputable def ep1625 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz423)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz423)) 1 768 0 1 0 1 0

noncomputable def ep1626 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz423) 1 24 0 1 1 32 0 1 1

noncomputable def ep1627 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep1628 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep1629 := @ep1628 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep844) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 124004 1000 0 1 ep1255)

noncomputable def ep1630 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 124004 1000 0 1 0 1 0

noncomputable def ep1631 := @ep1630 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep844) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 124004 1000 0 1 ep1255)

noncomputable def ep1632 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)))) 31001 3000 0 1 0 1 0 1 31001

noncomputable def ep1633 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 124004 1000 0 1 31001 3000 0

noncomputable def ep1634 := @ep1633 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep844) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 124004 1000 0 1 ep1255)

noncomputable def ep1635 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep1636 := @ep1635 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep844) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 124004 1000 0 1 ep1255)

noncomputable def ep1637 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 31001 3000 0 1 (@ep1627 1 24 0 1 (ep1629 rfl) (ep1631 rfl) rfl rfl) (@ep1632 31001 3000 0 1 (ep1634 rfl) (ep1636 rfl) rfl rfl)

noncomputable def ep1638 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 31001 3000 0 1 ep1637

noncomputable abbrev qz424 := (@Enclosure.Complex.IsNear.of_eq (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz80 1)) (Complex.mk (Enclosure.sfrac Bool.false 1 32) qz828) Bool.false 1 32 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 32 1 32 EMRow40.d20 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 32) qz828 Bool.false 1 32 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 32) qz830))

noncomputable def ep1639 := @ep1626 768 0 1 ep1638 (@Enclosure.Complex.IsNear.re_isNear qz423 Bool.false 1 32 0 1 Bool.false 0 1 0 1 qz424)

noncomputable def ep1640 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz423) 31001 3000 0 1 0 1 0 1 0

noncomputable def ep1641 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 31001 3000 0 1 ep1637

noncomputable def ep1642 := @ep1640 1 0 1 ep1641 (@Enclosure.Complex.IsNear.im_isNear qz423 Bool.false 1 32 0 1 Bool.false 0 1 0 1 qz424)

noncomputable def ep1643 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz423)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz423)) 0 1 0 1 31001 96000 0

noncomputable def ep1644 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz423) 1 24 0 1 0 1 0 1 0

noncomputable def ep1645 := @ep1644 1 0 1 ep1638 (@Enclosure.Complex.IsNear.im_isNear qz423 Bool.false 1 32 0 1 Bool.false 0 1 0 1 qz424)

noncomputable def ep1646 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz423) 31001 3000 0 1 1 32 0 1 31001

noncomputable def ep1647 := @ep1646 96000 0 1 ep1641 (@Enclosure.Complex.IsNear.re_isNear qz423 Bool.false 1 32 0 1 Bool.false 0 1 0 1 qz424)

noncomputable def ep1648 := @ep1622 1 (@ep1623 0 1 0 1 (BSN.bern_sum_base qz64 32) qz360) (ep1624 (@ep1625 1 1 1 768 0 1 (ep1639 rfl) (ep1642 rfl) rfl rfl) (@ep1643 1 31001 31001 96000 0 1 (ep1645 rfl) (ep1647 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep1649 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) qz422 Bool.false 1441553939 491520000000 0 1 Bool.false 14891371054313 184320000000000 0 1

noncomputable def ep1650 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.re qz422)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.im qz422)) 1441553939 491520000000 0 1 0 1 0

noncomputable def ep1651 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.re qz422) 1441553939 15000000 0 1 1 32768 0 1 1441553939

noncomputable def ep1652 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)))) 1441553939 15000000 0 1 0 1 0 1 1441553939

noncomputable def ep1653 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 4324661817 62500 0 1 1441553939 15000000 0

noncomputable def ep1654 := @ep1653 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep870) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 4324661817 62500 0 1 Bool.true 14891371054313 7812500 0 1 EMRow40.d21)

noncomputable def ep1655 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 14891371054313 7812500 0 1 0 1 0

noncomputable def ep1656 := @ep1655 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep870) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 4324661817 62500 0 1 Bool.true 14891371054313 7812500 0 1 EMRow40.d21)

noncomputable def ep1657 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)))) 14891371054313 5625000000 0 1 0 1 0 1 14891371054313

noncomputable def ep1658 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 14891371054313 7812500 0 1 14891371054313 5625000000 0

noncomputable def ep1659 := @ep1658 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep870) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 4324661817 62500 0 1 Bool.true 14891371054313 7812500 0 1 EMRow40.d21)

noncomputable def ep1660 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 4324661817 62500 0 1 0 1 0

noncomputable def ep1661 := @ep1660 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep870) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 4324661817 62500 0 1 Bool.true 14891371054313 7812500 0 1 EMRow40.d21)

noncomputable def ep1662 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 1441553939 15000000 0 1 Bool.false 14891371054313 5625000000 0 1 (@ep1652 1441553939 15000000 0 1 (ep1654 rfl) (ep1656 rfl) rfl rfl) (@ep1657 14891371054313 5625000000 0 1 (ep1659 rfl) (ep1661 rfl) rfl rfl)

noncomputable def ep1663 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 1441553939 15000000 0 1 Bool.false 14891371054313 5625000000 0 1 ep1662

noncomputable abbrev qz425 := (@Enclosure.Complex.IsNear.of_eq (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz80 3)) (Complex.mk (Enclosure.sfrac Bool.false 1 32768) qz828) Bool.false 1 32768 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 32 3 32768 EMRow40.d22 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 32768) qz828 Bool.false 1 32768 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 32768) qz830))

noncomputable def ep1664 := @ep1651 491520000000 0 1 ep1663 (@Enclosure.Complex.IsNear.re_isNear qz422 Bool.false 1 32768 0 1 Bool.false 0 1 0 1 qz425)

noncomputable def ep1665 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.im qz422) 14891371054313 5625000000 0 1 0 1 0 1 0

noncomputable def ep1666 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 1441553939 15000000 0 1 Bool.false 14891371054313 5625000000 0 1 ep1662

noncomputable def ep1667 := @ep1665 1 0 1 ep1666 (@Enclosure.Complex.IsNear.im_isNear qz422 Bool.false 1 32768 0 1 Bool.false 0 1 0 1 qz425)

noncomputable def ep1668 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.im qz422)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.re qz422)) 0 1 0 1 14891371054313 184320000000000 0

noncomputable def ep1669 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.im qz422) 1441553939 15000000 0 1 0 1 0 1 0

noncomputable def ep1670 := @ep1669 1 0 1 ep1663 (@Enclosure.Complex.IsNear.im_isNear qz422 Bool.false 1 32768 0 1 Bool.false 0 1 0 1 qz425)

noncomputable def ep1671 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.re qz422) 14891371054313 5625000000 0 1 1 32768 0 1 14891371054313

noncomputable def ep1672 := @ep1671 184320000000000 0 1 ep1666 (@Enclosure.Complex.IsNear.re_isNear qz422 Bool.false 1 32768 0 1 Bool.false 0 1 0 1 qz425)

noncomputable def ep1673 := @ep1619 1 (@ep1620 Bool.false 31001 96000 0 1 (BSN.bern_sum_succ qz64 32 0 1 1 rfl rfl) (ep1648 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1649 (@ep1650 1 1441553939 1441553939 491520000000 0 1 (ep1664 rfl) (ep1667 rfl) rfl rfl) (@ep1668 1 14891371054313 14891371054313 184320000000000 0 1 (ep1670 rfl) (ep1672 rfl) rfl rfl)) rfl rfl rfl rfl

noncomputable def ep1674 := ep1613 (ep1616 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep1617 Bool.false 74413291054313 184320000000000 0 1 (BSN.bern_sum_succ qz64 32 1 2 3 rfl rfl) (ep1673 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep1675 := @Enclosure.Real.IsNear.mulLit_tf (Complex.im qz78) (Complex.im (@HAdd.hAdd Complex Complex Complex qz15 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz80 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))))) 7187079599 68719476736 763085535569 6504435912015872 12902057274663087550469

noncomputable def ep1676 := @ep1675 88572914012160000000000 0 1 ep1591 ep1592 ep1593 ep1304 (@Enclosure.Complex.IsNear.im_isNear qz78 Bool.true 39175172509 274877906944 382208301491 3252217956007936 Bool.true 7187079599 68719476736 763085535569 6504435912015872 (ep1596 ep1609))

noncomputable def ep1677 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz15 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz80 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1))))) Bool.false 39617242047307511469 78731479121920000000 0 1 Bool.false

noncomputable def ep1678 := nat_lit 505440319455924849644193318856721

noncomputable def ep1679 := nat_lit 4931273396688579161938584230449279

noncomputable def ep1680 := @Enclosure.Real.IsNear.addLit_tt (@HMul.hMul Real Real Real qz0 (Complex.re qz78) (Complex.im (@HAdd.hAdd Complex Complex Complex qz15 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz80 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 (Complex.im qz78) (Complex.re (@HAdd.hAdd Complex Complex Complex qz15 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz80 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1))))))) ep1678 ep1302 ep1679

noncomputable def ep1681 := nat_lit 288058421366293668990560501760000000000

noncomputable def ep1682 := nat_lit 284732272086848808558308420931

noncomputable def ep1683 := nat_lit 5410386047909651147653120000000

noncomputable def ep1684 := nat_lit 30231344365436358423758474940861

noncomputable def ep1685 := nat_lit 512103860206744300427663114240000000

noncomputable def ep1686 := nat_lit 9666929057732689123109336380552356240629359618530234859520000000

noncomputable def ep1687 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re qz78) (Complex.im (@HAdd.hAdd Complex Complex Complex qz15 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz80 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))))) 39175172509 274877906944 382208301491 3252217956007936 12902057274663087550469

noncomputable def ep1688 := @ep1687 88572914012160000000000 0 1 ep1678 ep1302 ep1679 ep1681 (@Enclosure.Complex.IsNear.re_isNear qz78 Bool.true 39175172509 274877906944 382208301491 3252217956007936 Bool.true 7187079599 68719476736 763085535569 6504435912015872 (ep1596 ep1609))

noncomputable def ep1689 := @Enclosure.Real.IsNear.mulLit_tf (Complex.im qz78) (Complex.re (@HAdd.hAdd Complex Complex Complex qz15 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz80 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))))) 7187079599 68719476736 763085535569 6504435912015872 39617242047307511469

noncomputable def ep1690 := @ep1689 78731479121920000000 0 1 ep1682 ep1683 ep1684 ep1685 (@Enclosure.Complex.IsNear.im_isNear qz78 Bool.true 39175172509 274877906944 382208301491 3252217956007936 Bool.true 7187079599 68719476736 763085535569 6504435912015872 (ep1596 ep1609))

noncomputable abbrev qz996 := (ep1674 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep1691 := @ep1585 ep1495 ep1302 ep1496 ep1304 (@ep1589 ep1590 ep1591 ep1592 ep1593 ep1304 ep1594 ep1493 ep1302 ep1494 ep1304 (ep1610 (@ep1611 12902057274663087550469 88572914012160000000000 0 1 qz996) rfl) (ep1676 (@ep1677 12902057274663087550469 88572914012160000000000 0 1 qz996) rfl) rfl rfl) (@ep1680 ep1681 ep1682 ep1683 ep1684 ep1685 ep1686 ep1495 ep1302 ep1496 ep1304 (ep1688 (@ep1677 12902057274663087550469 88572914012160000000000 0 1 qz996) rfl) (ep1690 (@ep1611 12902057274663087550469 88572914012160000000000 0 1 qz996) rfl) rfl rfl)

noncomputable def ep1692 := @ep1499 ep1490 ep1304 (@ep1500 26017743648063488 (BSN.head_sum_c_eq qz64 32) (ep1501 (BSN.head_sum_c_succ qz64 31 32 rfl rfl) (ep1584 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep1691 rfl rfl rfl

noncomputable def ep1693 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz64 2 32) Bool.false ep1301 ep1302 ep1303 ep1304 Bool.false ep1489 ep1302 ep1490 ep1304 (@ep1491 ep1304 Bool.false ep1489 ep1302 ep1490 ep1304 (BSN.zetaApproximant_eq_folded' qz64 2 32 rfl) (ep1692 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep1694 := @Enclosure.Real.IsNear.mulLit_tf (Real.sin (@HSub.hSub Real Real Real qz599 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz409)) (Complex.im (zetaApproximant qz64 2 32)) 209 524288 2138775

noncomputable def ep1695 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz599 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz409)) Bool.true 418 1048576 17110200

noncomputable def ep1696 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz599 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz409) qz977 Bool.false 64237083 524288 89

noncomputable def ep1697 := BSN.sin_dyadic_bound_f 856729 2147483648 1 0 1048576 378978 0 1 1 0 1 1 418 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 856729) qz268 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 856729) qz269 0 0 rfl) rfl rfl

noncomputable def ep1698 := @ep1696 262144 Bool.true 418 1048576 1 189304 (@ep1311 64237083 524288 89 262144 ep1486 rfl) (Enclosure.sfrac_false_div 64237083 524288) (BSN.sin_reduce2 qz977 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 30143500789015904256) qz281) 226375608064910080 72057594037927936 Bool.false 418 1048576 19 1000000000000000 378608 189304 (BSN.sin_reduce_arg_pos_rat_q2 64237083 524288 226375608064910080 72057594037927936 19 30143500789015904256 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 418 1048576 30143500789015904256 75557863725914323419136 856729 2147483648 378978 378608 (ep1697 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1699 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz64 2 32) Bool.false ep1301 ep1302 ep1303 ep1304 Bool.false ep1489 ep1302 ep1490 ep1304 (@ep1491 ep1304 Bool.false ep1489 ep1302 ep1490 ep1304 (BSN.zetaApproximant_eq_folded' qz64 2 32 rfl) (ep1692 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow40.d23 : Enclosure.Real.IsNear (hardyZApproximantEM 2 32 qz61) Bool.true ep1284 ep1285 ep1286 ep1287 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 2 32 qz61) ep1288 Bool.true ep1284 ep1285 ep1286 ep1287 (@Eq.refl Real ep1288) (@ep1289 Bool.true ep1284 ep1285 ep1286 ep1287 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz599 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz409) (zetaApproximant qz64 2 32)) (@ep1291 ep1292 ep1293 ep1294 ep1295 ep1296 ep1297 ep1298 ep1299 ep1284 ep1285 ep1286 ep1287 (@ep1300 6203113472 ep1301 ep1302 ep1303 ep1304 ep1290 ep1292 ep1293 ep1294 (@ep1305 49624907776 1048575 1048576 2138775 6203113472 (ep1488 rfl rfl) rfl) ep1693 rfl) (@ep1694 6203113472 ep1489 ep1302 ep1490 ep1304 ep1295 ep1296 ep1297 ep1298 (@ep1695 49624907776 209 524288 2138775 6203113472 (ep1698 rfl rfl) rfl) ep1699 rfl) rfl rfl))

theorem EMRow40.d24 : @Eq Nat (Nat.mul (BSN.factNat (Nat.succ (Nat.mul 2 2))) (Nat.pow 4 (Nat.mul 2 2))) 30720 := @Eq.refl Nat 30720

theorem EMRow40.d25 : @Eq Nat (Nat.mul (Nat.mul 2 2) (Nat.pow (Nat.succ (Nat.mul 4 4)) (Nat.mul 2 2))) 334084 := @Eq.refl Nat 334084

theorem EMRow40.d179 : @Eq Nat (TangentNumbers.tangentNumber 3) 16 := Height20.tangent_three

noncomputable abbrev qz233 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 3)

theorem EMRow40.d180 : @Eq Real (@Rat.cast Real Real.instRatCast (bernoulli qz233)) (Enclosure.sfrac Bool.false 1 42) := BSN.bern_real_tangent_pos 2 16 1 42 EMRow40.d179 rfl rfl rfl

theorem EMRow40.d181 : @Eq Nat (BSN.factNat (Nat.mul 2 3)) 720 := @Eq.refl Nat 720

theorem EMRow40.d182 : @Eq Nat (Nat.pow 31 (Nat.succ (Nat.mul 2 5))) 25408476896404831 := @Eq.refl Nat 25408476896404831

noncomputable def ep1833 := nat_lit 1181671153346359170692730265957638242378174781758650

noncomputable def ep1834 := nat_lit 5986310706507378352962293074805895248510699696029696

noncomputable def ep1835 := nat_lit 2000000000000000000000000000000000000000000000000000

noncomputable def ep1836 := nat_lit 1499028120395240233173640088155429295548437777754679499662777369540625

noncomputable def ep1837 := nat_lit 4680297997409431328241185462095581837349556053595733828842639923095703125

noncomputable def ep1838 := nat_lit 13442882392639581675476766202062253719655739830178303899086159055189875

noncomputable def ep1839 := nat_lit 19584239746202378791298717228947477708711488730841665528714656829833984375

noncomputable def ep1840 := nat_lit 2442358029135994033939875

noncomputable def ep1841 := nat_lit 37260822860694382775919147000

noncomputable def ep1842 := nat_lit 116336546489037573337554931640625

noncomputable def ep1843 := nat_lit 57493278893883548332405996866302358825

noncomputable def ep1844 := nat_lit 40230676762013536063022911548614501953125

noncomputable def ep1845 := nat_lit 236310350532676991248348623960

noncomputable def ep1846 := nat_lit 344268321641720831394195556640625

noncomputable def ep1847 := nat_lit 81801971833623620377505564448994707675

noncomputable def ep1848 := nat_lit 56886557708273976459167897701263427734375

noncomputable def ep1849 := BSN.arctan_dyadic_bound_f 1 5 18 17 ep1834 ep1835 ep1836 ep1837 200200021673987500790625 ep1838 ep1839 ep1840 ep1833 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 17 8 ep1841 ep1842 151412625 ep1843 ep1844 1322214852783825 ep1836 ep1837 200200021673987500790625 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 8 ep1841 ep1842 151412625 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 8 17 ep1843 ep1844 1322214852783825 rfl rfl rfl rfl)) (@BSN.binarySplit_rec (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 17 8 ep1845 ep1846 1267389585 ep1847 ep1848 1927077560082675 ep1838 ep1839 ep1840 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 8 ep1845 ep1846 1267389585 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 8 17 ep1847 ep1848 1927077560082675 rfl rfl rfl rfl)) rfl

theorem EMRow40.d183 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz267 qz833)) Bool.false ep1833 ep1834 1 ep1835 := ep1849 rfl rfl rfl

noncomputable def ep1850 := nat_lit 25047178968060507272880539293402373975644382030403

noncomputable def ep1851 := nat_lit 4733915408010924740926662591654183582145509

noncomputable def ep1852 := nat_lit 77229300481955664312677298336960122659119574530232845

noncomputable def ep1853 := nat_lit 24516194103503660983641551147684725335332607

noncomputable def ep1854 := nat_lit 186647183216068817672719845704257068688983305564016735

noncomputable def ep1855 := BSN.arctan_dyadic_bound_f 1 239 6 5 ep1834 ep1835 ep1851 ep1852 9945 ep1853 ep1854 65835 ep1850 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 239) 0 5 ep1851 ep1852 9945 rfl rfl rfl rfl) (@BSN.binarySplit_of_base5 (BSN.arctanOddP 1) (BSN.arctanOddQ 239) 0 5 ep1853 ep1854 65835 rfl rfl rfl rfl) rfl rfl rfl

theorem EMRow40.d184 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz267 (@Nat.cast Real Real.instNatCast 239))) Bool.false ep1850 ep1834 1 ep1835 := ep1855 rfl

noncomputable def ep1856 := nat_lit 18806549737669504701992162098148602382148218980016788

noncomputable def ep1857 := nat_lit 100000000000000000000000000000000000000000000000000

theorem EMRow40.d185 : Enclosure.Real.IsNear Real.pi Bool.false ep1856 ep1834 1 ep1857 := BSN.pi_combine ep1833 ep1850 ep1834 ep1835 ep1857 ep1856 rfl rfl rfl rfl EMRow40.d183 EMRow40.d184

noncomputable def ep1858 := nat_lit 2118449453697906258214912

noncomputable abbrev qz540 := (@HAdd.hAdd Complex Complex Complex qz551 (@HAdd.hAdd Complex Complex Complex qz551 qz552 (@HMul.hMul Complex Complex Complex qz547 Complex.I ↑(Enclosure.sfrac Bool.false 121891 1000))) (@Nat.cast Complex Complex.instNatCast 5))

noncomputable abbrev qz234 := (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Norm.norm Complex Complex.instNorm qz540) (@HAdd.hAdd Real Real Real qz607 (Complex.re qz261) qz833))

noncomputable abbrev qz235 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 3)))

noncomputable abbrev qz236 := (@HPow.hPow Complex Complex Complex (@instHPow Complex Complex Complex.instPow) (@Nat.cast Complex Complex.instNatCast 31) (@HSub.hSub Complex Complex Complex qz597 (@Neg.neg Complex Complex.instNeg qz261) (@Nat.cast Complex Complex.instNatCast 5)))

noncomputable def ep1859 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 2 4) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz14 2 31))) (@HMul.hMul Real Real Real qz0 qz234 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236))) 8707613865 179359981764608 73952355 179359981764608 571873519111373175 4611686018427387904 510795509325

noncomputable def ep1860 := nat_lit 102611380740593182221027099279360

noncomputable def ep1861 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 2 4) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz14 2 31)) 10095 171051008 15 171051008 862567 1048576 6035 1048576 8707613865 179359981764608

noncomputable abbrev qz541 := (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid)))

noncomputable abbrev qz542 := (@HMul.hMul Real Real Real qz0 (2 : Real) Real.pi)

noncomputable abbrev qz1127 := (@Inv.inv Real Real.instInv (@HPow.hPow Real Nat Real qz541 qz542 4))

noncomputable def ep1862 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 30720 334084) qz1127 30720 334084 0 1 673 1048576 1 1048576 10095 171051008 15 171051008

noncomputable def ep1863 := nat_lit 611446774371975769155682509262542103857872115376664175900625

noncomputable def ep1864 := nat_lit 392318858461667547739736838950479151006397215279002157056

noncomputable def ep1865 := nat_lit 19652562622312316682495810535216024035134795670488584765154486969712234385047

noncomputable def ep1866 := nat_lit 9903520314283042199192993792000000000000000000000000000000000000000000000000000000000000

noncomputable def ep1867 := nat_lit 691463075802508163054686763366652189853178875

noncomputable def ep1868 := nat_lit 2787593149816327892691964784081045188247552

noncomputable def ep1869 := nat_lit 2184744797947834540264818678394244808492865883128339

noncomputable def ep1870 := nat_lit 9223372036854775808000000000000000000000000000000000000000000000

noncomputable def ep1871 := @Enclosure.Real.IsNear.mulLit_ff (@HPow.hPow Real Nat Real qz541 qz542 3) qz542 ep1867 ep1868 ep1869 ep1870 884279719003555 140737488355328 1 500000000000000 ep1863 ep1864 ep1865 ep1866

noncomputable def ep1872 := nat_lit 781950621441006189802102638025

noncomputable def ep1873 := nat_lit 19807040628566084398385987584

noncomputable def ep1874 := nat_lit 26986075409044041160201671

noncomputable def ep1875 := nat_lit 1073741824000000000000000000000000000000

noncomputable def ep1876 := @Enclosure.Real.IsNear.mulLit_ff (@HPow.hPow Real Nat Real qz541 qz542 2) qz542 ep1872 ep1873 ep1874 ep1875 884279719003555 140737488355328 1 500000000000000 ep1867 ep1868 ep1869 ep1870

noncomputable def ep1877 := @Enclosure.Real.IsNear.mulLit_ff (@HPow.hPow Real Nat Real qz541 qz542 1) qz542 884279719003555 140737488355328 1 500000000000000 884279719003555 140737488355328 1 500000000000000 ep1872 ep1873 ep1874 ep1875

noncomputable abbrev qz543 := (@Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 (2 : Real) Real.pi) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 2 1) Real.pi) Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 2 1) Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) BSN.pi_near_15 rfl))

noncomputable def ep1878 := ep1877 (@Enclosure.Real.IsNear.of_eq (@HPow.hPow Real Nat Real qz541 qz542 1) qz542 Bool.false 884279719003555 140737488355328 1 500000000000000 (BSN.pow_one_r qz542) qz543) qz543 rfl

noncomputable def ep1879 := @Enclosure.Real.IsNear.of_eq (@HPow.hPow Real Nat Real qz541 qz542 3) (@HMul.hMul Real Real Real qz0 (@HPow.hPow Real Nat Real qz541 qz542 2) qz542) Bool.false ep1867 ep1868 ep1869 ep1870 (BSN.pow_succ_r qz542 2 3 rfl) (ep1876 (@Enclosure.Real.IsNear.of_eq (@HPow.hPow Real Nat Real qz541 qz542 2) (@HMul.hMul Real Real Real qz0 (@HPow.hPow Real Nat Real qz541 qz542 1) qz542) Bool.false ep1872 ep1873 ep1874 ep1875 (BSN.pow_succ_r qz542 1 2 rfl) ep1878) qz543 rfl)

noncomputable def ep1880 := @Enclosure.Real.IsNear.inv_image (@HPow.hPow Real Nat Real qz541 qz542 4) ep1863 ep1864 ep1865 ep1866 336 337 524288 (@Enclosure.Real.IsNear.of_eq (@HPow.hPow Real Nat Real qz541 qz542 4) (@HMul.hMul Real Real Real qz0 (@HPow.hPow Real Nat Real qz541 qz542 3) qz542) Bool.false ep1863 ep1864 ep1865 ep1866 (BSN.pow_succ_r qz542 3 4 rfl) (ep1871 ep1879 qz543 rfl))

noncomputable def ep1881 := ep1862 (Enclosure.Real.IsNear.const Bool.false 30720 334084) (@Enclosure.Real.IsNear.recentre' qz1127 Bool.false 673 1048576 1 1048576 673 1048576 1 1048576 (ep1880 rfl rfl rfl rfl rfl rfl) rfl)

noncomputable def ep1882 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz14 2 31)) (Real.sqrt (@HAdd.hAdd Real Real Real qz607 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz14 2 31)) (Complex.re (zetaApproximant qz14 2 31))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz14 2 31)) (Complex.im (zetaApproximant qz14 2 31))))) Bool.false 862567 1048576 6035 1048576

noncomputable def ep1883 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz607 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz14 2 31)) (Complex.re (zetaApproximant qz14 2 31))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz14 2 31)) (Complex.im (zetaApproximant qz14 2 31))))) Bool.false 862567 1048576 6035 1048576

noncomputable def ep1884 := nat_lit 894772514159673068155133876682388340034693432051910149827163157

noncomputable def ep1885 := nat_lit 1322225045731128553119129379631582661978970128384000000000000000

noncomputable def ep1886 := nat_lit 4338906790644612570634771242776187779858947758555082073861074295984870799551654477

noncomputable def ep1887 := nat_lit 458336382638115758060943742924186535158221524745835423087800090624000000000000000000

noncomputable def ep1888 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz607 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz14 2 31)) (Complex.re (zetaApproximant qz14 2 31))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz14 2 31)) (Complex.im (zetaApproximant qz14 2 31)))) ep1884 ep1885 ep1886 ep1887 428266 434301

noncomputable def ep1889 := nat_lit 83085364470942959948402683713271241818670862744886514903132076924318349022401

noncomputable def ep1890 := nat_lit 122782362181019083770643654451105387918225627600057165414400000000000000000000

noncomputable def ep1891 := nat_lit 214800927352885224820813435478146030714079110818956029906629728440764250035422658229

noncomputable def ep1892 := nat_lit 22916819131905787903047187146209326757911076237291771154390004531200000000000000000000

noncomputable def ep1893 := nat_lit 3579622099314619366817627798650139614705765691342934146923605551315458849

noncomputable def ep1894 := nat_lit 238268019927267078991680740073706475429808567644230420713776262053254438017785069

noncomputable def ep1895 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz14 2 31)) (Complex.re (zetaApproximant qz14 2 31))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz14 2 31)) (Complex.im (zetaApproximant qz14 2 31))) ep1889 ep1890 ep1891 ep1892 ep1893 ep1890 ep1894

noncomputable def ep1896 := nat_lit 2546313236878420878116354127356591861990119581921307906043333836800000000000000000000

noncomputable def ep1897 := nat_lit 10201856826870362768476015189056270236035605909393224843701371957040242426210167807298276007671110254741473050080917501448059617280000000000000000000000000

noncomputable def ep1898 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz14 2 31)) (Complex.re (zetaApproximant qz14 2 31)) ep479 ep480 ep481 ep482 ep479 ep480 ep481 ep482 ep1889

noncomputable def ep1899 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (zetaApproximant qz14 2 31)) (Complex.im (zetaApproximant qz14 2 31)) ep688 ep480 ep689 ep690 ep688 ep480 ep689 ep690 ep1893

noncomputable def ep1900 := @ep1859 25364273101350633472 ep1860 47782147648089184528695 385172627945073865129984 916125253749084045 ep1858 (@ep1861 73952355 179359981764608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 2 4) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 30720 334084) qz1127) Bool.false 10095 171051008 15 171051008 (BSN.theta_err_eq 2 4 30720 334084 EMRow40.d24 EMRow40.d25 rfl) (ep1881 rfl)) (ep1882 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz14 2 31)) (@ep1883 862567 1048576 6035 1048576 (@ep1888 524288 (@ep1895 ep1896 ep1897 ep1884 ep1885 ep1886 ep1887 (@ep1898 ep1890 ep1891 ep1892 ep908 ep908 rfl) (@ep1899 ep1890 ep1894 ep1896 ep914 ep914 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz237 := (@Norm.norm Complex Complex.instNorm qz540)

noncomputable def ep1901 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz234 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz237 (Enclosure.sfrac Bool.false 2 11)) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236))) Bool.false 571873519111373175 4611686018427387904 510795509325 25364273101350633472 (BSN.zrb_shape_eq qz237 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236)) qz11 5)

noncomputable def ep1902 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz237 (Enclosure.sfrac Bool.false 2 11)) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236)) 127942025 5767168 1 5767168 49167650037 8796093022208 15201 17592186044416

noncomputable def ep1903 := @Enclosure.Real.IsNear.mulLit_ff qz237 (Enclosure.sfrac Bool.false 2 11) 127942025 1048576 1 1048576 2 11 0 1 127942025 5767168

noncomputable abbrev qz238 := (Complex.re qz540)

noncomputable abbrev qz239 := (Complex.im qz540)

noncomputable abbrev qz240 := qz540

noncomputable abbrev qz1128 := (@HAdd.hAdd Real Real Real qz607 (@HMul.hMul Real Real Real qz0 qz238 qz238) (@HMul.hMul Real Real Real qz0 qz239 qz239))

noncomputable def ep1904 := @Enclosure.Real.IsNear.of_eq qz237 (Real.sqrt qz1128) Bool.false 127942025 1048576 1 1048576 (BSN.norm_eq_sqrt_mul_add qz240)

noncomputable def ep1905 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz1128) Bool.false 127942025 1048576 1 1048576 127942025

noncomputable def ep1906 := @Enclosure.Real.IsNear.sqrt_image qz1128 14887665881 1000000 0 1 63971012 63971013 524288

noncomputable def ep1907 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz238 qz238) (@HMul.hMul Real Real Real qz0 qz239 qz239) 121 4 0 1 14857415881 1000000 0 1

noncomputable def ep1908 := @Enclosure.Real.IsNear.mulLit_ff qz238 qz238 11 2 0 1 11 2 0 1 121 4

noncomputable def ep1909 := @Enclosure.Complex.IsNear.of_eq qz240 (Complex.mk (Enclosure.sfrac Bool.false 11 2) qz11) Bool.false 11 2 0 1 Bool.false 121891 1000 0 1 (BSN.s_add_nat_mk qz11 Bool.false 121891 1000 5 (@Eq.refl Real qz11))

noncomputable abbrev qz793 := (ep1909 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 11 2) qz11 Bool.false 11 2 0 1 Bool.false 121891 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 11 2) qz272))

noncomputable def ep1910 := @ep1908 0 1 (@Enclosure.Complex.IsNear.re_isNear qz240 Bool.false 11 2 0 1 Bool.false 121891 1000 0 1 qz793)

noncomputable def ep1911 := ep1910 (@Enclosure.Complex.IsNear.re_isNear qz240 Bool.false 11 2 0 1 Bool.false 121891 1000 0 1 qz793)

noncomputable def ep1912 := @Enclosure.Real.IsNear.mulLit_ff qz239 qz239 121891 1000 0 1 121891 1000 0 1 14857415881 1000000

noncomputable def ep1913 := @ep1912 0 1 (@Enclosure.Complex.IsNear.im_isNear qz240 Bool.false 11 2 0 1 Bool.false 121891 1000 0 1 qz793)

noncomputable def ep1914 := ep1913 (@Enclosure.Complex.IsNear.im_isNear qz240 Bool.false 11 2 0 1 Bool.false 121891 1000 0 1 qz793)

noncomputable def ep1915 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236)) (Real.sqrt (@HAdd.hAdd Real Real Real qz607 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236)) (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236)) (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236))))) Bool.false 49167650037 8796093022208

noncomputable def ep1916 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz607 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236)) (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236)) (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236))))) Bool.false 6293459204736 1125899906842624

noncomputable def ep1917 := nat_lit 4164504969463757552605685779870848995458403494071131656208492865342289788011218975174118441

noncomputable def ep1918 := nat_lit 133285869143017689414552503787145390903601605116319968931237330944000000000000000000000000000000

noncomputable def ep1919 := nat_lit 14196315051853768172125297133891970846421019416684580842935975737110023277552133037715266046736347135482267957587

noncomputable def ep1920 := nat_lit 1469616605304055453949207258120769788725807497297165157167541009355128536799018153392105062400000000000000000000000000000000

noncomputable def ep1921 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz607 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236)) (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236)) (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236)))) ep1917 ep1918 ep1919 ep1920

noncomputable def ep1922 := nat_lit 2320918152106009699332917768628820642347370082883447762967802733513980364898694955048344041

noncomputable def ep1923 := nat_lit 805123237011794035323105597066263462093260482797556954402273511986719168661353560670175181108791414605793042859

noncomputable def ep1924 := nat_lit 163290733922672828216578584235641087636200833033018350796393445483903170755446461488011673600000000000000000000000000000000

noncomputable def ep1925 := nat_lit 1152241760848592408295480007026267720694395881992302433275431332392693389445327512578609

noncomputable def ep1926 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236)) (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236)) (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236))) ep1922 ep1918 ep1923 ep1924 ep1925

noncomputable def ep1927 := nat_lit 83303668214386055884095314866965869314751003197699980582023331840000000000000000000000000000

noncomputable def ep1928 := nat_lit 434387869921726365888584172518474980473854691969160515832219633076846922474996936980230588547326525251883160741

noncomputable def ep1929 := nat_lit 91851037831503465871825453632548111795362968581072822322971313084695533549938634587006566400000000000000000000000000000000

noncomputable def ep1930 := nat_lit 346918540253370792307806362541375048719452513418060883566452751123597563520010756342753247395698285802026240237470865634586303586186990534001839165606461440000000000000000000000000000

noncomputable def ep1931 := nat_lit 1523455989553360776484731656950096342569520429

noncomputable def ep1932 := nat_lit 365083372865730067631050523148288000000000000000

noncomputable def ep1933 := nat_lit 22648266179897668160695005536352183899618357595112699

noncomputable def ep1934 := nat_lit 38335578843993675295881587055642785056366264320000000000000000

noncomputable def ep1935 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236)) (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236)) ep1931 ep1932 ep1933 ep1934 ep1931 ep1932 ep1933

noncomputable def ep1936 := nat_lit 33944686783775047941114468284225469213359353

noncomputable def ep1937 := nat_lit 9127084321643251690776263078707200000000000000

noncomputable def ep1938 := nat_lit 6093486871028433816965892196542930913061721337244879

noncomputable def ep1939 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236) Bool.true ep1931 ep1932 ep1933 ep1934 Bool.true ep1936 ep1937 ep1938

noncomputable def ep1940 := nat_lit 9583894710998418823970396763910696264091566080000000000000000

noncomputable def ep1941 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236 Bool.true ep1931 ep1932 ep1933 ep1934 Bool.true ep1936 ep1937 ep1938 ep1940

noncomputable def ep1942 := nat_lit 68527621915972863166064389410233642899

noncomputable def ep1943 := nat_lit 162259276829213363391578010288128000000000

noncomputable def ep1944 := nat_lit 68766045688795864232063698623526822788521973641

noncomputable def ep1945 := nat_lit 1150067365319810258876447611669283551690987929600000000000

noncomputable def ep1946 := nat_lit 1369268840242421834361086780777070646046770429

noncomputable def ep1947 := nat_lit 61068193970813418058878646746703869420002875421238097

noncomputable def ep1948 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.re qz236)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.im qz236)) ep1942 ep1943 ep1944 ep1945 ep1946 ep1932 ep1947

noncomputable def ep1949 := nat_lit 115006736531981025887644761166928355169098792960000000000000000

noncomputable def ep1950 := nat_lit 247194867146061948035797406283034785113706827292335658213661182234037072166912000000000

noncomputable def ep1951 := nat_lit 316912650057057350374175801344

noncomputable def ep1952 := nat_lit 2182043018288970423508190767

noncomputable def ep1953 := nat_lit 3327741219096673202767498876357880647254016

noncomputable def ep1954 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.re qz236) 31514523367517358023 345600000000000 0 1 1467772311002450543775 ep1951 ep1952 ep1953 ep1942

noncomputable def ep1955 := nat_lit 3828920380040337342781493

noncomputable def ep1956 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5)))) 31514523367517358023 345600000000000 0 1 0 1 0 1 31514523367517358023

noncomputable def ep1957 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) 1 30240 0 1 220601663572621506161 80000000000 0 1 31514523367517358023 345600000000000 0

noncomputable def ep1958 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (Complex.mk (Enclosure.sfrac Bool.false 1 30240) qz264) Bool.false 1 30240 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 3 1 42 720 Bool.false EMRow40.d180 EMRow40.d181 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 30240) qz264 Bool.false 1 30240 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 30240) qz276)

noncomputable def ep1959 := nat_lit 26802442660282361399470451

noncomputable abbrev qz241 := (@HAdd.hAdd Complex Complex Complex qz262 qz261 qz263)

noncomputable def ep1960 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5)) (@HMul.hMul Complex Complex Complex qz3 (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 4)) qz241) Bool.false 220601663572621506161 80000000000 0 1 Bool.false ep1959 1000000000000000 0 1

noncomputable def ep1961 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.re qz241)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.im qz241)) 1983810409038445555449 2000000000000 0 1 220701948767318256161 125000000000 0 1

noncomputable def ep1962 := nat_lit 689380198664442206753125000000000

noncomputable def ep1963 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.re qz241) 220423378782049506161 1000000000000 0 1 9 2 0 1 1983810409038445555449 2000000000000

noncomputable abbrev qz242 := (@HAdd.hAdd Complex Complex Complex qz262 qz261 qz554)

noncomputable def ep1964 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 4)) (@HMul.hMul Complex Complex Complex qz3 (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3)) qz242) Bool.false 220423378782049506161 1000000000000 0 1 Bool.true 1810650078900971 125000000 0 1

noncomputable def ep1965 := @Enclosure.Real.IsNear.subLit_tt_p (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.re qz242)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.im qz242)) 935990950503 4000000 0 1 220657376519675256161 1000000000000 0 1

noncomputable def ep1966 := nat_lit 881693515128198024644000000

noncomputable def ep1967 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.re qz242) 133712992929 2000000 0 1 7 2 0 1 935990950503 4000000

noncomputable abbrev qz794 := (ep426 (BSN.ascPochhammer_succ_eval_c 2 3 qz14 rfl) (ep454 (@ep455 362056881180194200 1810284405900971 1000000000 0 1 (ep458 rfl) (ep461 rfl) rfl rfl)))

noncomputable def ep1968 := @ep1967 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 133712992929 2000000 0 1 Bool.true 1810284405900971 1000000000 0 1 qz794)

noncomputable def ep1969 := @Enclosure.Complex.IsNear.of_eq qz242 (Complex.mk (Enclosure.sfrac Bool.false 7 2) qz11) Bool.false 7 2 0 1 Bool.false 121891 1000 0 1 (BSN.s_add_nat_mk qz11 Bool.false 121891 1000 3 (@Eq.refl Real qz11))

noncomputable abbrev qz795 := (ep1969 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz11 Bool.false 7 2 0 1 Bool.false 121891 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz272))

noncomputable def ep1970 := ep1968 (@Enclosure.Complex.IsNear.re_isNear qz242 Bool.false 7 2 0 1 Bool.false 121891 1000 0 1 qz795)

noncomputable def ep1971 := @Enclosure.Real.IsNear.mulLit_tf (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.im qz242) 1810284405900971 1000000000 0 1 121891 1000 0 1 220657376519675256161 1000000000000

noncomputable def ep1972 := @ep1971 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 133712992929 2000000 0 1 Bool.true 1810284405900971 1000000000 0 1 qz794)

noncomputable def ep1973 := ep1972 (@Enclosure.Complex.IsNear.im_isNear qz242 Bool.false 7 2 0 1 Bool.false 121891 1000 0 1 qz795)

noncomputable def ep1974 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3)) qz242 Bool.false 220423378782049506161 1000000000000 0 1 Bool.true 1810650078900971 125000000 0 1 (@ep1965 ep1966 220423378782049506161 1000000000000 0 1 (ep1970 rfl) (ep1973 rfl) rfl rfl)

noncomputable def ep1975 := @Enclosure.Real.IsNear.addLit_tt (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.im qz242)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.re qz242)) 16298410421108739 2000000000 0 1 12671990841306797 2000000000 0 1

noncomputable def ep1976 := nat_lit 57940802524831072000000000

noncomputable def ep1977 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.im qz242) 133712992929 2000000 0 1 121891 1000 0 1 16298410421108739 2000000000

noncomputable def ep1978 := @ep1977 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 133712992929 2000000 0 1 Bool.true 1810284405900971 1000000000 0 1 qz794)

noncomputable def ep1979 := ep1978 (@Enclosure.Complex.IsNear.im_isNear qz242 Bool.false 7 2 0 1 Bool.false 121891 1000 0 1 qz795)

noncomputable def ep1980 := @Enclosure.Real.IsNear.mulLit_tf (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.re qz242) 1810284405900971 1000000000 0 1 7 2 0 1 12671990841306797 2000000000

noncomputable def ep1981 := @ep1980 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 133712992929 2000000 0 1 Bool.true 1810284405900971 1000000000 0 1 qz794)

noncomputable def ep1982 := ep1981 (@Enclosure.Complex.IsNear.re_isNear qz242 Bool.false 7 2 0 1 Bool.false 121891 1000 0 1 qz795)

noncomputable abbrev qz796 := (ep1964 (BSN.ascPochhammer_succ_eval_c 3 4 qz14 rfl) (ep1974 (@ep1975 ep1976 1810650078900971 125000000 0 1 (ep1979 rfl) (ep1982 rfl) rfl rfl)))

noncomputable def ep1983 := @ep1963 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 4)) Bool.false 220423378782049506161 1000000000000 0 1 Bool.true 1810650078900971 125000000 0 1 qz796)

noncomputable def ep1984 := @Enclosure.Complex.IsNear.of_eq qz241 (Complex.mk (Enclosure.sfrac Bool.false 9 2) qz11) Bool.false 9 2 0 1 Bool.false 121891 1000 0 1 (BSN.s_add_nat_mk qz11 Bool.false 121891 1000 4 (@Eq.refl Real qz11))

noncomputable abbrev qz797 := (ep1984 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9 2) qz11 Bool.false 9 2 0 1 Bool.false 121891 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 9 2) qz272))

noncomputable def ep1985 := ep1983 (@Enclosure.Complex.IsNear.re_isNear qz241 Bool.false 9 2 0 1 Bool.false 121891 1000 0 1 qz797)

noncomputable def ep1986 := @Enclosure.Real.IsNear.mulLit_tf (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.im qz241) 1810650078900971 125000000 0 1 121891 1000 0 1 220701948767318256161 125000000000

noncomputable def ep1987 := @ep1986 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 4)) Bool.false 220423378782049506161 1000000000000 0 1 Bool.true 1810650078900971 125000000 0 1 qz796)

noncomputable def ep1988 := ep1987 (@Enclosure.Complex.IsNear.im_isNear qz241 Bool.false 9 2 0 1 Bool.false 121891 1000 0 1 qz797)

noncomputable def ep1989 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 4)) qz241 Bool.false 220601663572621506161 80000000000 0 1 Bool.false ep1959 1000000000000000 0 1 (@ep1961 ep1962 220601663572621506161 80000000000 0 1 (ep1985 rfl) (ep1988 rfl) rfl rfl)

noncomputable def ep1990 := nat_lit 26867626063122796355470451

noncomputable def ep1991 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.im qz241)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.re qz241)) ep1990 1000000000000000 0 1 16295850710108739 250000000 0 1

noncomputable def ep1992 := nat_lit 6700610665070590349867612750000000

noncomputable def ep1993 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.im qz241) 220423378782049506161 1000000000000 0 1 121891 1000 0 1 ep1990 1000000000000000

noncomputable def ep1994 := @ep1993 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 4)) Bool.false 220423378782049506161 1000000000000 0 1 Bool.true 1810650078900971 125000000 0 1 qz796)

noncomputable def ep1995 := ep1994 (@Enclosure.Complex.IsNear.im_isNear qz241 Bool.false 9 2 0 1 Bool.false 121891 1000 0 1 qz797)

noncomputable def ep1996 := @Enclosure.Real.IsNear.mulLit_tf (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.re qz241) 1810650078900971 125000000 0 1 9 2 0 1 16295850710108739 250000000

noncomputable def ep1997 := @ep1996 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 4)) Bool.false 220423378782049506161 1000000000000 0 1 Bool.true 1810650078900971 125000000 0 1 qz796)

noncomputable def ep1998 := ep1997 (@Enclosure.Complex.IsNear.re_isNear qz241 Bool.false 9 2 0 1 Bool.false 121891 1000 0 1 qz797)

noncomputable abbrev qz798 := (ep1960 (BSN.ascPochhammer_succ_eval_c 4 5 qz14 rfl) (ep1989 (@ep1991 ep1992 ep1959 1000000000000000 0 1 (ep1995 rfl) (ep1998 rfl) rfl rfl)))

noncomputable def ep1999 := @ep1957 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) Bool.false 1 30240 0 1 Bool.false 0 1 0 1 ep1958) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5)) Bool.false 220601663572621506161 80000000000 0 1 Bool.false ep1959 1000000000000000 0 1 qz798)

noncomputable def ep2000 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) 0 1 0 1 ep1959 1000000000000000 0 1 0 1 0

noncomputable def ep2001 := @ep2000 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) Bool.false 1 30240 0 1 Bool.false 0 1 0 1 ep1958) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5)) Bool.false 220601663572621506161 80000000000 0 1 Bool.false ep1959 1000000000000000 0 1 qz798)

noncomputable def ep2002 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5)))) ep1955 4320000000000000000 0 1 0 1 0 1 ep1955

noncomputable def ep2003 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) 1 30240 0 1 ep1959 1000000000000000 0 1 ep1955 4320000000000000000 0

noncomputable def ep2004 := @ep2003 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) Bool.false 1 30240 0 1 Bool.false 0 1 0 1 ep1958) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5)) Bool.false 220601663572621506161 80000000000 0 1 Bool.false ep1959 1000000000000000 0 1 qz798)

noncomputable def ep2005 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) 0 1 0 1 220601663572621506161 80000000000 0 1 0 1 0

noncomputable def ep2006 := @ep2005 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) Bool.false 1 30240 0 1 Bool.false 0 1 0 1 ep1958) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5)) Bool.false 220601663572621506161 80000000000 0 1 Bool.false ep1959 1000000000000000 0 1 qz798)

noncomputable def ep2007 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5)) Bool.false 31514523367517358023 345600000000000 0 1 Bool.false ep1955 4320000000000000000 0 1 (@ep1956 31514523367517358023 345600000000000 0 1 (ep1999 rfl) (ep2001 rfl) rfl rfl) (@ep2002 ep1955 4320000000000000000 0 1 (ep2004 rfl) (ep2006 rfl) rfl rfl)

noncomputable def ep2008 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) Bool.false 31514523367517358023 345600000000000 0 1 Bool.false ep1955 4320000000000000000 0 1 ep2007

noncomputable def ep2009 := nat_lit 1267650600228229401496703205376

noncomputable def ep2010 := nat_lit 15949194004961281005590403629

noncomputable def ep2011 := nat_lit 26621929752773385622139991010863045178032128

noncomputable def ep2012 := @Enclosure.Complex.IsNear.re_isNear qz236 Bool.true 1467772311002450543775 ep1951 ep1952 ep1953 Bool.false 5364183781596406712295 ep2009 ep2010 ep2011

noncomputable abbrev qz799 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 25408476896404831)))

noncomputable def ep2013 := @Enclosure.Complex.IsNear.of_eq qz236 (Complex.mk (@HMul.hMul Real Real Real qz0 qz799 (Real.cos qz380)) (@HMul.hMul Real Real Real qz0 qz799 qz946)) Bool.true 1467772311002450543775 ep1951 ep1952 ep1953 Bool.false 5364183781596406712295 ep2009 ep2010

noncomputable def ep2014 := nat_lit 11822511748593005630310055936

noncomputable abbrev qz800 := (Real.sqrt (@Nat.cast Real Real.instNatCast 25408476896404831))

noncomputable abbrev qz801 := (@Nat.cast Real Real.instNatCast 25408476896404831)

noncomputable def ep2015 := @Enclosure.Real.IsNear.inv_image qz800 179468857991052819133049 1125899906842624 1 1125899906842624 3531672 3531673 562949953421312 (@Enclosure.Real.IsNear.of_eq qz800 (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz801 qz267)) Bool.false 179468857991052819133049 1125899906842624 1 1125899906842624 (BSN.sqrt_natCast_div_one 25408476896404831) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz801 qz267)) Bool.false 179468857991052819133049 1125899906842624 1 1125899906842624 179468857991052819133049 1125899906842624 1 1125899906842624 (BSN.sqrt_enclosure 25408476896404831 1 89734428995526409566524 89734428995526409566525 562949953421312 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep2016 := nat_lit 94580093988744045042480447488

noncomputable def ep2017 := nat_lit 5250249900875750000000000000000

noncomputable def ep2018 := nat_lit 5250249900875750000000000000

noncomputable def ep2019 := nat_lit 69649535055066447282451783876608

noncomputable def ep2020 := nat_lit 20282409603651670423947251286016

noncomputable def ep2021 := nat_lit 168007996828024000000000000000

noncomputable def ep2022 := nat_lit 407803126487611369510712240836643677231310855520504641681829375

noncomputable def ep2023 := nat_lit 14758784810707816243361475489559229339408485454012280808500000

noncomputable def ep2024 := nat_lit 181914695786991974680041032843291759490966796875

noncomputable def ep2025 := BSN.log_dyadic_bound 15 47 15 14 ep2022 562949953421312 168007996828024 ep2023 ep2024 372334244772954 62 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base14 (BSN.artanhP 15) (BSN.artanhQ 47) 0 14 ep2023 ep2022 ep2024 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep2026 := @Enclosure.Real.IsNear.mulLit_ff qz11 qz381 121891 1000 0 1 3866325873628587 1125899906842624 52250999603503 ep2018 471270327062462098017 1125899906842624000 6368926592670584173 ep2017 qz272 (BSN.isNear_log_sfrac 31 1 3866325873628587 1125899906842624 52250999603503 ep2018 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz947) Bool.false ep2019 ep2020 1672031987312096 ep2021 3866325873628587 1125899906842624 52250999603503 ep2018 (BSN.log_rat_reduce_isNear 31 1 4 62 32 372334244772954 562949953421312 24973259072661432 36028797018963968 168007996828024 1000000000000000 rfl rfl rfl rfl (ep2025 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep2027 := nat_lit 4989689062705817818830627915274589316268508480889192553103084224512

noncomputable def ep2028 := nat_lit 6739986666787659948666753771754907668409286105635143120275902562304

noncomputable def ep2029 := nat_lit 135462153100943729474004525419692688049227172705446065884215870188552309870715783121681984185933545546784958010464484363122476703607402266294261452323313539798886535315832399832439018428125030982034295190416312216911285791297536

noncomputable def ep2030 := nat_lit 10821657637148560913492946031921314191599039087545316774779112146610557800425141274980107660439910087336441848082102652922524673568245877354709081054961510112752972936751739152800669431482567824842593065617095249443484864190873600

noncomputable def ep2031 := nat_lit 612251944381161136379293148479931983533806523841245692749892218798937088752799287502464523237558560363469393676479018796587078030155518201973005275643537299372819005114038800828046863132311423670355921501590169445011456

noncomputable def ep2032 := nat_lit 821705788505340597221321642852546382058617554502741582363029166196795845927860163623069544576376656310077277467576932460145872156781706481139545500903442546528496827372124194410363892631346198819175994592396434592505265643130880

noncomputable def ep2033 := nat_lit 984770844980519043127858088904839591435512556966623826504899205341560759838687856023189797100031817947616208175471341415949745294710374839278526376001497420260520537244408262904860918264913672060675968971155667699357122641369497600

noncomputable def ep2034 := BSN.cos_dyadic_bound_f 1707041899665038666 2305843009213693952 4 3 1125899906842624 336344134274853 ep2029 ep2030 ep2031 ep2032 ep2033 ep2031 831205221323580 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 1707041899665038666) (BSN.cosEvenQ 2305843009213693952) 0 3 ep2029 ep2030 ep2031 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 1707041899665038666) (BSN.cosOddQ 2305843009213693952) 0 3 ep2032 ep2033 ep2031 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz802 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 235635163531231049) (@Nat.cast Real Real.instNatCast 562949953421312))

noncomputable def ep2035 := @Enclosure.Real.IsNear.cos_image qz380 qz802 Bool.false 235635163531231049 562949953421312 683 562949953421312 Bool.true 831205221323580 1125899906842624 1 168007996828024 (@Enclosure.Real.IsNear.recentre' qz380 Bool.false 471270327062462098017 1125899906842624000 6368926592670584173 ep2017 235635163531231049 562949953421312 683 562949953421312 (ep2026 rfl) rfl) (Enclosure.sfrac_false_div 235635163531231049 562949953421312) (BSN.cos_reduce2 qz802 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep2027) (@Nat.cast Real Real.instNatCast ep2028)) ep1856 ep1834 Bool.false 831205221323580 1125899906842624 66 ep1857 336015993656048 168007996828024 (BSN.sin_reduce_arg_pos_rat_q2 235635163531231049 562949953421312 ep1856 ep1834 66 ep2027 ep2028 rfl rfl rfl rfl) EMRow40.d185 (@BSN.cos_arg_round Bool.false 831205221323580 1125899906842624 ep2027 ep2028 1707041899665038666 2305843009213693952 336344134274853 336015993656048 (ep2034 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep2036 := nat_lit 352173615024286344654052218254283197129136072521304143665662743705370095955123311930670079030207809164369643211086340495474830895107919544614055866256730705783399835666089239383221396596676323560223027822610311480844212049350656

noncomputable def ep2037 := nat_lit 140681549282931291875408298414977084490787508138089118072128457905937251405526836574741399585718831135373744025067334487992820756387196405611218053714499631465788648177772608986408702609273381722953709853022238242765303234481356800

noncomputable def ep2038 := nat_lit 1760759960173425742003678044910873204924502917426065481762378225585087942371356273487423304814432106209791618331623465856296253422044916172553363029605202207413583364544716071010591441067386394434766342022913180495616151050326016

noncomputable def ep2039 := nat_lit 4923854224902595215639290444524197957177562784833119132524496026707803799193439280115948985500159089738081040877356707079748726473551874196392631880007487101302602686222041314524304591324568360303379844855778338496785613206847488000

noncomputable def ep2040 := BSN.sin_dyadic_bound_f 1707041899665038666 2305843009213693952 4 3 1125899906842624 336344134274853 ep2036 ep2037 ep2031 ep2038 ep2039 ep2031 759439583029911 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 1707041899665038666) (BSN.sinEvenQ 2305843009213693952) 0 3 ep2036 ep2037 ep2031 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 1707041899665038666) (BSN.sinOddQ 2305843009213693952) 0 3 ep2038 ep2039 ep2031 rfl rfl rfl rfl) rfl rfl

noncomputable def ep2041 := @Enclosure.Real.IsNear.sin_image qz380 qz802 Bool.false 235635163531231049 562949953421312 683 562949953421312 Bool.true 759439583029911 1125899906842624 1 168007996828024 (@Enclosure.Real.IsNear.recentre' qz380 Bool.false 471270327062462098017 1125899906842624000 6368926592670584173 ep2017 235635163531231049 562949953421312 683 562949953421312 (ep2026 rfl) rfl) (Enclosure.sfrac_false_div 235635163531231049 562949953421312) (BSN.sin_reduce2 qz802 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep2027) (@Nat.cast Real Real.instNatCast ep2028)) ep1856 ep1834 Bool.false 759439583029911 1125899906842624 66 ep1857 336015993656048 168007996828024 (BSN.sin_reduce_arg_pos_rat_q2 235635163531231049 562949953421312 ep1856 ep1834 66 ep2027 ep2028 rfl rfl rfl rfl) EMRow40.d185 (@BSN.sin_arg_round Bool.false 759439583029911 1125899906842624 ep2027 ep2028 1707041899665038666 2305843009213693952 336344134274853 336015993656048 (ep2040 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep2042 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz799 (Real.cos qz380)) (@HMul.hMul Real Real Real qz0 qz799 qz946) Bool.true 1467772311002450543775 ep1951 ep1952 ep1953 Bool.false 5364183781596406712295 ep2009 ep2010 ep2011 (@Enclosure.Real.IsNear.mulLit_ft qz799 (Real.cos qz380) 7063345 1125899906842624 1 1125899906842624 207801305330895 281474976710656 14414051473370213 ep2014 1467772311002450543775 ep1951 ep1952 ep1953 (@Enclosure.Real.IsNear.recentre' qz799 Bool.false 7063345 1125899906842624 1 1125899906842624 7063345 1125899906842624 1 1125899906842624 (ep2015 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' (Real.cos qz380) Bool.true 831205221323580 1125899906842624 115312411786961704 ep2016 207801305330895 281474976710656 14414051473370213 ep2014 (ep2035 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz799 qz946 7063345 1125899906842624 1 1125899906842624 759439583029911 1125899906842624 14414051473370213 ep2014 5364183781596406712295 ep2009 ep2010 ep2011 (@Enclosure.Real.IsNear.recentre' qz799 Bool.false 7063345 1125899906842624 1 1125899906842624 7063345 1125899906842624 1 1125899906842624 (ep2015 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg (Real.sin qz380) Bool.true 759439583029911 1125899906842624 14414051473370213 ep2014 (@Enclosure.Real.IsNear.recentre' (Real.sin qz380) Bool.true 759439583029911 1125899906842624 115312411786961704 ep2016 759439583029911 1125899906842624 14414051473370213 ep2014 (ep2041 rfl rfl) rfl)) rfl)

noncomputable def ep2043 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.im qz236) ep1955 4320000000000000000 0 1 5364183781596406712295 ep2009 ep2010 ep2011 ep1946

noncomputable def ep2044 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) Bool.false 31514523367517358023 345600000000000 0 1 Bool.false ep1955 4320000000000000000 0 1 ep2007

noncomputable def ep2045 := @Enclosure.Complex.IsNear.im_isNear qz236 Bool.true 1467772311002450543775 ep1951 ep1952 ep1953 Bool.false 5364183781596406712295 ep2009 ep2010 ep2011

noncomputable def ep2046 := nat_lit 11269979675518505827607453630522791399519

noncomputable def ep2047 := nat_lit 29206669829258405410484041851863040000000000

noncomputable def ep2048 := nat_lit 502631247162420047659782253329681802012271465467

noncomputable def ep2049 := nat_lit 9200538922558482071011580893354268413527903436800000000000

noncomputable def ep2050 := nat_lit 8325901207194351336053732787503075894602009

noncomputable def ep2051 := nat_lit 2028240960365167042394725128601600000000000000

noncomputable def ep2052 := nat_lit 8354868982851369400980428523986768553948407841075131

noncomputable def ep2053 := @Enclosure.Real.IsNear.addLit_ft_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.im qz236)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.re qz236)) ep2046 ep2047 ep2048 ep2049 ep2050 ep2051 ep2052

noncomputable def ep2054 := nat_lit 14375842066497628235955595145866044396137349120000000000000000

noncomputable def ep2055 := nat_lit 220313613189179828921531140252219573732446280335746190892599034245373346447360000000000

noncomputable def ep2056 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.im qz236) 31514523367517358023 345600000000000 0 1 5364183781596406712295 ep2009 ep2010 ep2011 ep2046

noncomputable def ep2057 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.re qz236) ep1955 4320000000000000000 0 1 1467772311002450543775 ep1951 ep1952 ep1953 ep2050

noncomputable abbrev qz803 := (@ep2013 ep2011 (BSN.cpow_neg_s_sub_mk qz11 121891 1000 31 5 25408476896404831 (@Eq.refl Real qz11) rfl EMRow40.d182) ep2042)

noncomputable def ep2058 := ep1941 (@ep1948 ep1949 ep1950 ep1931 ep1932 ep1933 ep1934 (@ep1954 ep1943 ep1944 ep1945 ep2008 (ep2012 qz803) rfl) (@ep2043 ep1932 ep1947 ep1949 ep2044 (ep2045 qz803) rfl) rfl rfl) (@ep2053 ep2054 ep2055 ep1936 ep1937 ep1938 ep1940 (@ep2056 ep2047 ep2048 ep2049 ep2008 (ep2045 qz803) rfl) (@ep2057 ep2051 ep2052 ep2054 ep2044 (ep2012 qz803) rfl) rfl rfl)

noncomputable def ep2059 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236)) (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236)) ep1936 ep1937 ep1938 ep1940 ep1936 ep1937 ep1938

noncomputable def ep2060 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236) Bool.true ep1931 ep1932 ep1933 ep1934 Bool.true ep1936 ep1937 ep1938

noncomputable def ep2061 := @ep1902 571873519111373175 4611686018427387904 510795509325 25364273101350633472 (@ep1903 1 5767168 (ep1904 (@ep1905 1048576 1 1048576 (ep1906 (@ep1907 59550663524 14887665881 1000000 0 1 (ep1911 rfl) (ep1914 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 11) rfl) (@ep1915 15201 17592186044416 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236)) (@ep1916 972864 1125899906842624 49167650037 8796093022208 15201 17592186044416 (@ep1921 3146729115936 3146730088800 562949953421312 (@ep1926 ep1927 ep1928 ep1929 ep1930 ep1917 ep1918 ep1919 ep1920 (@ep1935 ep1934 ep1922 ep1918 ep1923 ep1924 (@ep1939 ep1940 ep2058) (@ep1939 ep1940 ep2058) rfl) (@ep2059 ep1940 ep1925 ep1927 ep1928 ep1929 (@ep2060 ep1940 ep2058) (@ep2060 ep1940 ep2058) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow40.d186 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz607 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 2 4) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz14 2 31))) (@HMul.hMul Real Real Real qz0 qz234 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236)))) Bool.false 47782147648089184528695 385172627945073865129984 916125253749084045 ep1858 := ep1900 (ep1901 ep2061) rfl rfl

theorem EMRow40.d187 : @Eq Nat (Nat.pow 32 (Nat.succ (Nat.mul 2 5))) 36028797018963968 := @Eq.refl Nat 36028797018963968

noncomputable def ep2062 := nat_lit 3913763998985653921324077

noncomputable def ep2063 := nat_lit 33895191259166500131438592

noncomputable def ep2064 := nat_lit 8473797814791625032859648

noncomputable abbrev qz544 := (@HAdd.hAdd Complex Complex Complex qz551 (@HAdd.hAdd Complex Complex Complex qz551 qz552 (@HMul.hMul Complex Complex Complex qz547 Complex.I ↑(Enclosure.sfrac Bool.false 124004 1000))) (@Nat.cast Complex Complex.instNatCast 5))

noncomputable abbrev qz243 := (@Norm.norm Complex Complex.instNorm qz544)

noncomputable abbrev qz244 := (@HPow.hPow Complex Complex Complex (@instHPow Complex Complex Complex.instPow) (@Nat.cast Complex Complex.instNatCast 32) (@HSub.hSub Complex Complex Complex qz597 (@Neg.neg Complex Complex.instNeg qz391) (@Nat.cast Complex Complex.instNatCast 5)))

noncomputable abbrev qz804 := (@HDiv.hDiv Real Real Real qz1 qz243 (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (Complex.re qz64) qz833))

noncomputable def ep2065 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 2 4) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz64 2 32))) (@HMul.hMul Real Real Real qz0 qz804 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244))) 612594885 22419997720576 17870115 44839995441152 46848551389312750317 405828369621610135552 2227089510157

noncomputable def ep2066 := nat_lit 1050593023744097547828816733274112

noncomputable def ep2067 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 2 4) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz64 2 32)) 10095 171051008 15 171051008 60683 131072 3175 524288 612594885 22419997720576

noncomputable def ep2068 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz64 2 32)) (Real.sqrt (@HAdd.hAdd Real Real Real qz607 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz64 2 32)) (Complex.re (zetaApproximant qz64 2 32))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz64 2 32)) (Complex.im (zetaApproximant qz64 2 32))))) Bool.false 60683 131072 3175 524288

noncomputable def ep2069 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz607 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz64 2 32)) (Complex.re (zetaApproximant qz64 2 32))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz64 2 32)) (Complex.im (zetaApproximant qz64 2 32))))) Bool.false 485464 1048576 6350 1048576

noncomputable def ep2070 := nat_lit 132224368095622049915198677999209736062328921200223014863017

noncomputable def ep2071 := nat_lit 616769756166566021758012758996236736921600000000000000000000

noncomputable def ep2072 := nat_lit 930486483705594035023248237434560348583462294739412160065235060360438679403

noncomputable def ep2073 := nat_lit 165955308240082385915212192052945892064783638014045926195200000000000000000000

noncomputable def ep2074 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz607 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz64 2 32)) (Complex.re (zetaApproximant qz64 2 32))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz64 2 32)) (Complex.im (zetaApproximant qz64 2 32)))) ep2070 ep2071 ep2072 ep2073 239557 245907

noncomputable def ep2075 := nat_lit 127049136733548943632258158682164293708363794342849451725136811176801

noncomputable def ep2076 := nat_lit 592763613045162132763455248893813346054597876121600000000000000000000

noncomputable def ep2077 := nat_lit 364445878044022997502385402003277381363605485985239520222769645925886831747

noncomputable def ep2078 := nat_lit 66382123296032954366084876821178356825913455205618370478080000000000000000000

noncomputable def ep2079 := nat_lit 28745055141637093494488087654629302505873275401954069974282380841

noncomputable def ep2080 := nat_lit 12914525730357694178189821617577930116299053184208906338873963697147733357

noncomputable def ep2081 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz64 2 32)) (Complex.re (zetaApproximant qz64 2 32))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz64 2 32)) (Complex.im (zetaApproximant qz64 2 32))) ep2075 ep2076 ep2077 ep2078 ep2079 ep2076 ep2080

noncomputable def ep2082 := nat_lit 110636872160054923943474794701963928043189092009363950796800000000000000000000

noncomputable def ep2083 := nat_lit 75327144347190239338704817027367098626783560557789384719592544960206672112103884218181069552497567727102045745001267200000000000000000000

noncomputable def ep2084 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz64 2 32)) (Complex.re (zetaApproximant qz64 2 32)) ep1301 ep1302 ep1303 ep1304 ep1301 ep1302 ep1303 ep1304 ep2075

noncomputable def ep2085 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (zetaApproximant qz64 2 32)) (Complex.im (zetaApproximant qz64 2 32)) ep1489 ep1302 ep1490 ep1304 ep1489 ep1302 ep1490 ep1304 ep2079

noncomputable def ep2086 := @ep2065 101457092405402533888 ep2066 ep2062 ep2063 3563077361011220557 ep2064 (@ep2067 17870115 44839995441152 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 2 4) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 30720 334084) qz1127) Bool.false 10095 171051008 15 171051008 (BSN.theta_err_eq 2 4 30720 334084 EMRow40.d24 EMRow40.d25 rfl) (ep1881 rfl)) (ep2068 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz64 2 32)) (@ep2069 60683 131072 3175 524288 (@ep2074 524288 (@ep2081 ep2082 ep2083 ep2070 ep2071 ep2072 ep2073 (@ep2084 ep2076 ep2077 ep2078 ep1693 ep1693 rfl) (@ep2085 ep2076 ep2080 ep2082 ep1699 ep1699 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable def ep2087 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz804 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz243 (Enclosure.sfrac Bool.false 2 11)) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244))) Bool.false 46848551389312750317 405828369621610135552 2227089510157 101457092405402533888 (BSN.zrb_shape_eq qz243 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244)) qz61 5)

noncomputable def ep2088 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz243 (Enclosure.sfrac Bool.false 2 11)) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244)) 130155453 5767168 1 5767168 359943055089 70368744177664 131357 140737488355328

noncomputable def ep2089 := @Enclosure.Real.IsNear.mulLit_ff qz243 (Enclosure.sfrac Bool.false 2 11) 130155453 1048576 1 1048576 2 11 0 1 130155453 5767168

noncomputable abbrev qz245 := (Complex.re qz544)

noncomputable abbrev qz246 := (Complex.im qz544)

noncomputable abbrev qz247 := qz544

noncomputable abbrev qz1129 := (@HAdd.hAdd Real Real Real qz607 (@HMul.hMul Real Real Real qz0 qz245 qz245) (@HMul.hMul Real Real Real qz0 qz246 qz246))

noncomputable def ep2090 := @Enclosure.Real.IsNear.of_eq qz243 (Real.sqrt qz1129) Bool.false 130155453 1048576 1 1048576 (BSN.norm_eq_sqrt_mul_add qz247)

noncomputable def ep2091 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz1129) Bool.false 130155453 1048576 1 1048576 130155453

noncomputable def ep2092 := @Enclosure.Real.IsNear.sqrt_image qz1129 481476313 31250 0 1 65077726 65077727 524288

noncomputable def ep2093 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz245 qz245) (@HMul.hMul Real Real Real qz0 qz246 qz246) 121 4 0 1 961062001 62500 0 1

noncomputable def ep2094 := @Enclosure.Real.IsNear.mulLit_ff qz245 qz245 11 2 0 1 11 2 0 1 121 4

noncomputable def ep2095 := @Enclosure.Complex.IsNear.of_eq qz247 (Complex.mk (Enclosure.sfrac Bool.false 11 2) qz61) Bool.false 11 2 0 1 Bool.false 124004 1000 0 1 (BSN.s_add_nat_mk qz61 Bool.false 124004 1000 5 (@Eq.refl Real qz61))

noncomputable abbrev qz805 := (ep2095 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 11 2) qz61 Bool.false 11 2 0 1 Bool.false 124004 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 11 2) qz392))

noncomputable def ep2096 := @ep2094 0 1 (@Enclosure.Complex.IsNear.re_isNear qz247 Bool.false 11 2 0 1 Bool.false 124004 1000 0 1 qz805)

noncomputable def ep2097 := ep2096 (@Enclosure.Complex.IsNear.re_isNear qz247 Bool.false 11 2 0 1 Bool.false 124004 1000 0 1 qz805)

noncomputable def ep2098 := @Enclosure.Real.IsNear.mulLit_ff qz246 qz246 124004 1000 0 1 124004 1000 0 1 961062001 62500

noncomputable def ep2099 := @ep2098 0 1 (@Enclosure.Complex.IsNear.im_isNear qz247 Bool.false 11 2 0 1 Bool.false 124004 1000 0 1 qz805)

noncomputable def ep2100 := ep2099 (@Enclosure.Complex.IsNear.im_isNear qz247 Bool.false 11 2 0 1 Bool.false 124004 1000 0 1 qz805)

noncomputable def ep2101 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244)) (Real.sqrt (@HAdd.hAdd Real Real Real qz607 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244))))) Bool.false 359943055089 70368744177664

noncomputable def ep2102 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz607 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244))))) Bool.false 5759088881424 1125899906842624

noncomputable def ep2103 := nat_lit 5846079802052660841218023970015132795374119830906183769688149237750767094900257050021

noncomputable def ep2104 := nat_lit 223437849858246595548646996558515078971612164014369197260800000000000000000000000000000000

noncomputable def ep2105 := nat_lit 58535504785629261463942218428387543749615550550811765512683987724800878206062320337886533

noncomputable def ep2106 := nat_lit 6130451077138466072387745404114188678891169221322723299751996738764800000000000000000000000000000000

noncomputable def ep2107 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz607 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244)))) ep2103 ep2104 ep2105 ep2106

noncomputable def ep2108 := nat_lit 3011606629349433448304268198962101055693421386780557657557021383797988087432487875761

noncomputable def ep2109 := nat_lit 446875699716493191097293993117030157943224328028738394521600000000000000000000000000000000

noncomputable def ep2110 := nat_lit 36766062303953511722855011885544962344831062592851711197467356604568241478347784175887503

noncomputable def ep2111 := nat_lit 12260902154276932144775490808228377357782338442645446599503993477529600000000000000000000000000000000

noncomputable def ep2112 := nat_lit 8680552974755888234131779741068164535054818275031809881819277091703546102368026224281

noncomputable def ep2113 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244))) ep2108 ep2109 ep2110 ep2111 ep2112

noncomputable def ep2114 := nat_lit 80304947267305011205029424971230125154400038508771819827900618845033514933776856499885563

noncomputable def ep2115 := nat_lit 5224942004281481642022760474373668883202043259627597557635930050799341177462218174164933344715197952944206149047483054633198410785510567129907200000000000000000000000000000000

noncomputable def ep2116 := nat_lit 1735398118400914208016772782040202978495431

noncomputable def ep2117 := nat_lit 668487621214105348445527080960000000000000000

noncomputable def ep2118 := nat_lit 63951407737045048400280424835938249685941

noncomputable def ep2119 := nat_lit 110728958065525624021865551217295360000000000000000

noncomputable def ep2120 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244)) ep2116 ep2117 ep2118 ep2119 ep2116 ep2117 ep2118

noncomputable def ep2121 := nat_lit 2946277816967688509588153293395876943094341

noncomputable def ep2122 := nat_lit 82275537718530035811632673198834875118601

noncomputable def ep2123 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244) Bool.false ep2116 ep2117 ep2118 ep2119 Bool.true ep2121 ep2117 ep2122

noncomputable def ep2124 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244 Bool.false ep2116 ep2117 ep2118 ep2119 Bool.true ep2121 ep2117 ep2122 ep2119

noncomputable def ep2125 := nat_lit 29583388480804782993880074764074011947

noncomputable def ep2126 := nat_lit 71305346262837903834189555302400000000000

noncomputable def ep2127 := nat_lit 826123261780666933931351529424927117

noncomputable def ep2128 := nat_lit 11811088860322733228998992129844838400000000000

noncomputable def ep2129 := nat_lit 503185596352114762146099620738349210124639

noncomputable def ep2130 := nat_lit 167121905303526337111381770240000000000000000

noncomputable def ep2131 := nat_lit 28103251078925647947337002123789778982033

noncomputable def ep2132 := @Enclosure.Real.IsNear.subLit_tt_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.re qz244)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.im qz244)) ep2125 ep2126 ep2127 ep2128 ep2129 ep2130 ep2131

noncomputable def ep2133 := nat_lit 55364479032762812010932775608647680000000000000000

noncomputable def ep2134 := nat_lit 30935790934113639519311236351568482983473963881680045787732134030055833600000000000

noncomputable def ep2135 := nat_lit 633825300114114700748351602688

noncomputable def ep2136 := nat_lit 14998208076600296163808243974406144

noncomputable def ep2137 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.re qz244) 230767387107886469 2362500000000 0 1 2692109859555060160923 ep2135 10739688204656638779 ep2136 ep2125

noncomputable def ep2138 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)))) 230767387107886469 2362500000000 0 1 0 1 0 1 230767387107886469

noncomputable def ep2139 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) 1 30240 0 1 230767387107886469 78125000 0 1 230767387107886469 2362500000000 0

noncomputable abbrev qz248 := (@HAdd.hAdd Complex Complex Complex qz262 qz391 qz263)

noncomputable def ep2140 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)) (@HMul.hMul Complex Complex Complex qz3 (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4)) qz248) Bool.false 230767387107886469 78125000 0 1 Bool.false 7131677479731368925469 244140625000 0 1

noncomputable def ep2141 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.re qz248)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.im qz248)) 2075284728758353221 1953125000 0 1 461737493617351063 244140625 0 1

noncomputable def ep2142 := nat_lit 1408492352953408624267578125

noncomputable def ep2143 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.re qz248) 230587192084261469 976562500 0 1 9 2 0 1 2075284728758353221 1953125000

noncomputable abbrev qz249 := (@HAdd.hAdd Complex Complex Complex qz262 qz391 qz554)

noncomputable def ep2144 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4)) (@HMul.hMul Complex Complex Complex qz3 (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) qz249) Bool.false 230587192084261469 976562500 0 1 Bool.true 29788554796126 1953125 0 1

noncomputable def ep2145 := @Enclosure.Real.IsNear.subLit_tt_p (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.re qz249)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.im qz249)) 30272632719 125000 0 1 461647394054757313 1953125000 0 1

noncomputable def ep2146 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.re qz249) 4324661817 62500 0 1 7 2 0 1 30272632719 125000

noncomputable abbrev qz806 := (ep1248 (BSN.ascPochhammer_succ_eval_c 2 3 qz64 rfl) (ep1276 (@ep1277 744568552715650 14891371054313 7812500 0 1 (ep1280 rfl) (ep1283 rfl) rfl rfl)))

noncomputable def ep2147 := @ep2146 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 4324661817 62500 0 1 Bool.true 14891371054313 7812500 0 1 qz806)

noncomputable def ep2148 := @Enclosure.Complex.IsNear.of_eq qz249 (Complex.mk (Enclosure.sfrac Bool.false 7 2) qz61) Bool.false 7 2 0 1 Bool.false 124004 1000 0 1 (BSN.s_add_nat_mk qz61 Bool.false 124004 1000 3 (@Eq.refl Real qz61))

noncomputable abbrev qz807 := (ep2148 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz61 Bool.false 7 2 0 1 Bool.false 124004 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz392))

noncomputable def ep2149 := ep2147 (@Enclosure.Complex.IsNear.re_isNear qz249 Bool.false 7 2 0 1 Bool.false 124004 1000 0 1 qz807)

noncomputable def ep2150 := @Enclosure.Real.IsNear.mulLit_tf (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.im qz249) 14891371054313 7812500 0 1 124004 1000 0 1 461647394054757313 1953125000

noncomputable def ep2151 := @ep2150 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 4324661817 62500 0 1 Bool.true 14891371054313 7812500 0 1 qz806)

noncomputable def ep2152 := ep2151 (@Enclosure.Complex.IsNear.im_isNear qz249 Bool.false 7 2 0 1 Bool.false 124004 1000 0 1 qz807)

noncomputable def ep2153 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) qz249 Bool.false 230587192084261469 976562500 0 1 Bool.true 29788554796126 1953125 0 1 (@ep2145 57646798021065367250000 230587192084261469 976562500 0 1 (ep2149 rfl) (ep2152 rfl) rfl rfl)

noncomputable def ep2154 := @Enclosure.Real.IsNear.addLit_tt (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.im qz249)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.re qz249)) 134068840988817 15625000 0 1 104239597380191 15625000 0 1

noncomputable def ep2155 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.im qz249) 4324661817 62500 0 1 124004 1000 0 1 134068840988817 15625000

noncomputable def ep2156 := @ep2155 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 4324661817 62500 0 1 Bool.true 14891371054313 7812500 0 1 qz806)

noncomputable def ep2157 := ep2156 (@Enclosure.Complex.IsNear.im_isNear qz249 Bool.false 7 2 0 1 Bool.false 124004 1000 0 1 qz807)

noncomputable def ep2158 := @Enclosure.Real.IsNear.mulLit_tf (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.re qz249) 14891371054313 7812500 0 1 7 2 0 1 104239597380191 15625000

noncomputable def ep2159 := @ep2158 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 4324661817 62500 0 1 Bool.true 14891371054313 7812500 0 1 qz806)

noncomputable def ep2160 := ep2159 (@Enclosure.Complex.IsNear.re_isNear qz249 Bool.false 7 2 0 1 Bool.false 124004 1000 0 1 qz807)

noncomputable abbrev qz808 := (ep2144 (BSN.ascPochhammer_succ_eval_c 3 4 qz64 rfl) (ep2153 (@ep2154 3723569349515750000000 29788554796126 1953125 0 1 (ep2157 rfl) (ep2160 rfl) rfl rfl)))

noncomputable def ep2161 := @ep2143 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4)) Bool.false 230587192084261469 976562500 0 1 Bool.true 29788554796126 1953125 0 1 qz808)

noncomputable def ep2162 := @Enclosure.Complex.IsNear.of_eq qz248 (Complex.mk (Enclosure.sfrac Bool.false 9 2) qz61) Bool.false 9 2 0 1 Bool.false 124004 1000 0 1 (BSN.s_add_nat_mk qz61 Bool.false 124004 1000 4 (@Eq.refl Real qz61))

noncomputable abbrev qz809 := (ep2162 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9 2) qz61 Bool.false 9 2 0 1 Bool.false 124004 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 9 2) qz392))

noncomputable def ep2163 := ep2161 (@Enclosure.Complex.IsNear.re_isNear qz248 Bool.false 9 2 0 1 Bool.false 124004 1000 0 1 qz809)

noncomputable def ep2164 := @Enclosure.Real.IsNear.mulLit_tf (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.im qz248) 29788554796126 1953125 0 1 124004 1000 0 1 461737493617351063 244140625

noncomputable def ep2165 := @ep2164 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4)) Bool.false 230587192084261469 976562500 0 1 Bool.true 29788554796126 1953125 0 1 qz808)

noncomputable def ep2166 := ep2165 (@Enclosure.Complex.IsNear.im_isNear qz248 Bool.false 9 2 0 1 Bool.false 124004 1000 0 1 qz809)

noncomputable def ep2167 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4)) qz248 Bool.false 230767387107886469 78125000 0 1 Bool.false 7131677479731368925469 244140625000 0 1 (@ep2141 ep2142 230767387107886469 78125000 0 1 (ep2163 rfl) (ep2166 rfl) rfl rfl)

noncomputable def ep2168 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.im qz248)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.re qz248)) 7148433541804189800469 244140625000 0 1 134048496582567 1953125 0 1

noncomputable def ep2169 := nat_lit 13929057577600329932556640625

noncomputable def ep2170 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.im qz248) 230587192084261469 976562500 0 1 124004 1000 0 1 7148433541804189800469 244140625000

noncomputable def ep2171 := @ep2170 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4)) Bool.false 230587192084261469 976562500 0 1 Bool.true 29788554796126 1953125 0 1 qz808)

noncomputable def ep2172 := ep2171 (@Enclosure.Complex.IsNear.im_isNear qz248 Bool.false 9 2 0 1 Bool.false 124004 1000 0 1 qz809)

noncomputable def ep2173 := @Enclosure.Real.IsNear.mulLit_tf (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.re qz248) 29788554796126 1953125 0 1 9 2 0 1 134048496582567 1953125

noncomputable def ep2174 := @ep2173 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4)) Bool.false 230587192084261469 976562500 0 1 Bool.true 29788554796126 1953125 0 1 qz808)

noncomputable def ep2175 := ep2174 (@Enclosure.Complex.IsNear.re_isNear qz248 Bool.false 9 2 0 1 Bool.false 124004 1000 0 1 qz809)

noncomputable abbrev qz810 := (ep2140 (BSN.ascPochhammer_succ_eval_c 4 5 qz64 rfl) (ep2167 (@ep2168 ep2169 7131677479731368925469 244140625000 0 1 (ep2172 rfl) (ep2175 rfl) rfl rfl)))

noncomputable def ep2176 := @ep2139 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) Bool.false 1 30240 0 1 Bool.false 0 1 0 1 ep1958) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)) Bool.false 230767387107886469 78125000 0 1 Bool.false 7131677479731368925469 244140625000 0 1 qz810)

noncomputable def ep2177 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) 0 1 0 1 7131677479731368925469 244140625000 0 1 0 1 0

noncomputable def ep2178 := @ep2177 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) Bool.false 1 30240 0 1 Bool.false 0 1 0 1 ep1958) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)) Bool.false 230767387107886469 78125000 0 1 Bool.false 7131677479731368925469 244140625000 0 1 qz810)

noncomputable def ep2179 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)))) 7131677479731368925469 7382812500000000 0 1 0 1 0 1 7131677479731368925469

noncomputable def ep2180 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) 1 30240 0 1 7131677479731368925469 244140625000 0 1 7131677479731368925469 7382812500000000 0

noncomputable def ep2181 := @ep2180 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) Bool.false 1 30240 0 1 Bool.false 0 1 0 1 ep1958) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)) Bool.false 230767387107886469 78125000 0 1 Bool.false 7131677479731368925469 244140625000 0 1 qz810)

noncomputable def ep2182 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) 0 1 0 1 230767387107886469 78125000 0 1 0 1 0

noncomputable def ep2183 := @ep2182 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) Bool.false 1 30240 0 1 Bool.false 0 1 0 1 ep1958) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)) Bool.false 230767387107886469 78125000 0 1 Bool.false 7131677479731368925469 244140625000 0 1 qz810)

noncomputable def ep2184 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)) Bool.false 230767387107886469 2362500000000 0 1 Bool.false 7131677479731368925469 7382812500000000 0 1 (@ep2138 230767387107886469 2362500000000 0 1 (ep2176 rfl) (ep2178 rfl) rfl rfl) (@ep2179 7131677479731368925469 7382812500000000 0 1 (ep2181 rfl) (ep2183 rfl) rfl rfl)

noncomputable def ep2185 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) Bool.false 230767387107886469 2362500000000 0 1 Bool.false 7131677479731368925469 7382812500000000 0 1 ep2184

noncomputable def ep2186 := nat_lit 158456325028528675187087900672

noncomputable def ep2187 := nat_lit 7499104038300148081904121987203072

noncomputable def ep2188 := @Enclosure.Complex.IsNear.re_isNear qz244 Bool.true 2692109859555060160923 ep2135 10739688204656638779 ep2136 Bool.true 493894905437798745517 ep2186 3940622828050858757 ep2187

noncomputable abbrev qz811 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 36028797018963968)))

noncomputable def ep2189 := @Enclosure.Complex.IsNear.of_eq qz244 (Complex.mk (@HMul.hMul Real Real Real qz0 qz811 (Real.cos qz420)) (@HMul.hMul Real Real Real qz0 qz811 qz994)) Bool.true 2692109859555060160923 ep2135 10739688204656638779 ep2136 Bool.true 493894905437798745517 ep2186 3940622828050858757

noncomputable abbrev qz812 := (Real.sqrt (@Nat.cast Real Real.instNatCast 36028797018963968))

noncomputable abbrev qz813 := (@Nat.cast Real Real.instNatCast 36028797018963968)

noncomputable def ep2190 := @Enclosure.Real.IsNear.inv_image qz812 213709911250252303767135 1125899906842624 1 1125899906842624 2965820 2965821 562949953421312 (@Enclosure.Real.IsNear.of_eq qz812 (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz813 qz267)) Bool.false 213709911250252303767135 1125899906842624 1 1125899906842624 (BSN.sqrt_natCast_div_one 36028797018963968) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz813 qz267)) Bool.false 213709911250252303767135 1125899906842624 1 1125899906842624 213709911250252303767135 1125899906842624 1 1125899906842624 (BSN.sqrt_enclosure 36028797018963968 1 106854955625126151883567 106854955625126151883568 562949953421312 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep2191 := nat_lit 114427246678163880644288970752

noncomputable def ep2192 := nat_lit 310155673600000000000000000

noncomputable def ep2193 := nat_lit 1240622694400000000000000

noncomputable def ep2194 := nat_lit 70293475158665552278669146193920

noncomputable def ep2195 := nat_lit 203263622250496000000000000000

noncomputable def ep2196 := BSN.log_dyadic_bound 0 64 1 0 1 562949953421312 203263622250496 0 1 0 64 64 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 64) 0 0 rfl) rfl rfl rfl

noncomputable def ep2197 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz421 124004 1000 0 1 15608286920413395 4503599627370496 12306629097 ep2193 96774500563947131679 225179981368524800 381517808636097 ep2192 qz392 (BSN.isNear_log_sfrac 32 1 15608286920413395 4503599627370496 12306629097 ep2193 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 qz646 qz267)) Bool.false ep2194 ep2020 2016318111252480 ep2195 15608286920413395 4503599627370496 12306629097 ep2193 (BSN.log_rat_reduce_isNear 32 1 5 64 64 0 562949953421312 24973259072661432 36028797018963968 203263622250496 1000000000000000 rfl rfl rfl rfl (ep2196 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep2198 := nat_lit 6320204631903813004853318088270782519686956084851959394190260961280

noncomputable def ep2199 := nat_lit 1464072154119698882026295591372973396092038878105186174758693934793222242108953435629351913954296924071753269194875627243793044116582535838309994664231251164746706817010536971428932209384355452210540510382769817825640848713397476237205438236671525840927899439148456124091949742195444565215326434700579373056

noncomputable def ep2200 := nat_lit 227166498108393291591690474249109426965528421018278839661455426590473243066834650624926416047854179247596172938820614485527445924608820872880385787908168637421617142754592441181269508473347051925777211342581761153821293384735107078859788885002196634811247029175151612501537270086431278076342027182518829056000

noncomputable def ep2201 := nat_lit 228259786692632971012076749163304803568562605576346574609085515818746481508970847393408768133408166189268333177810212837264043651900596239207916831722687177341465043266103318052452652558148313949458605722053571973799955298618709689865655012447301549449473883172145175386585098662544272470900736

noncomputable def ep2202 := nat_lit 11919846417187979768266919085876388482207177559806296901100003593481542504845872812868338424397393077049960121767495152976700799915938324338086601254092235617992888001949710203374656506273623828481961291166113763702912557288974495463022890952206446863342363131569940488914147472885263643186861685607397130240

noncomputable def ep2203 := nat_lit 12948490392178417620726357032199237337035119998041893860702959315656974854809575085620805714727688217112981857512775025675064417702702789754181989910765612333032177137011769147332361982980781959769301046527160385767813722929901103495007966445125208184241080662983641912587624394926582850351495549403573256192000

noncomputable def ep2204 := BSN.sin_dyadic_bound_f 2162229747291359598 2305843009213693952 5 4 1125899906842624 406924243763201 ep2199 ep2200 ep2201 ep2202 ep2203 ep2201 907711663452006 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.sinEvenP 2162229747291359598) (BSN.sinEvenQ 2305843009213693952) 0 4 ep2199 ep2200 ep2201 rfl rfl rfl rfl) (@BSN.binarySplit_of_base4 (BSN.sinOddP 2162229747291359598) (BSN.sinOddQ 2305843009213693952) 0 4 ep2202 ep2203 ep2201 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz814 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 241936251409867829) (@Nat.cast Real Real.instNatCast 562949953421312))

noncomputable def ep2205 := @Enclosure.Real.IsNear.cos_image qz420 qz814 Bool.false 241936251409867829 562949953421312 693 562949953421312 Bool.true 907711663452006 1125899906842624 1 203263622250496 (@Enclosure.Real.IsNear.recentre' qz420 Bool.false 96774500563947131679 225179981368524800 381517808636097 ep2192 241936251409867829 562949953421312 693 562949953421312 (ep2197 rfl) rfl) (Enclosure.sfrac_false_div 241936251409867829 562949953421312) (BSN.cos_reduce1 qz814 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep2198) (@Nat.cast Real Real.instNatCast ep2028)) ep1856 ep1834 Bool.false 907711663452006 1125899906842624 68 ep1857 406527244500992 203263622250496 (BSN.sin_reduce_arg_pos_rat_q1 241936251409867829 562949953421312 ep1856 ep1834 68 ep2198 ep2028 rfl rfl rfl rfl) EMRow40.d185 (@BSN.sin_arg_round Bool.false 907711663452006 1125899906842624 ep2198 ep2028 2162229747291359598 2305843009213693952 406924243763201 406527244500992 (ep2204 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep2206 := nat_lit 430697523094984268294462265029492837485872262111891676981611709701388415304991176621034644148555090762777153754753347088911956868584114359542286625915241416573573854299242233436262343556219841682978642518426197191293576624843728305038168122454240403506910080288176772417633025955954369947907894526691311616

noncomputable def ep2207 := nat_lit 13362735182846664211275910249947613350913436530486990568320907446498426062754979448525083296932598779270363114048271440325143877918165933698846222818127566907153949573799555363604088733726297172104541843681280067871840787337359239932928757941305684400661589951479506617737486475672428122137766304854048768000

noncomputable def ep2208 := nat_lit 4391767337317640146672041883684767422085618437437178812341546325535575512011645955922186389486345065370270566313544119678264363981090568223547877207915423781652066952006738410883334611740650366558154624757645181220109528077363433796301085293002549032684424765183954877362450188295266581251599730179938779136

noncomputable def ep2209 := nat_lit 2044498482975539624325214268241984842689755789164509556953098839314259187601511855624337744430687613228365556449385530369747013321479387855923472091173517736794554284791331970631425576260123467331994902083235850384391640462615963709738099965019769713301223262576364512513835430777881502687078244642669461504000

noncomputable def ep2210 := BSN.cos_dyadic_bound_f 2162229747291359598 2305843009213693952 5 4 1125899906842624 406924243763201 ep2206 ep2207 ep2201 ep2208 ep2209 ep2201 666115707862696 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.cosEvenP 2162229747291359598) (BSN.cosEvenQ 2305843009213693952) 0 4 ep2206 ep2207 ep2201 rfl rfl rfl rfl) (@BSN.binarySplit_of_base4 (BSN.cosOddP 2162229747291359598) (BSN.cosOddQ 2305843009213693952) 0 4 ep2208 ep2209 ep2201 rfl rfl rfl rfl) rfl rfl

noncomputable def ep2211 := @Enclosure.Real.IsNear.sin_image qz420 qz814 Bool.false 241936251409867829 562949953421312 693 562949953421312 Bool.false 666115707862696 1125899906842624 1 203263622250496 (@Enclosure.Real.IsNear.recentre' qz420 Bool.false 96774500563947131679 225179981368524800 381517808636097 ep2192 241936251409867829 562949953421312 693 562949953421312 (ep2197 rfl) rfl) (Enclosure.sfrac_false_div 241936251409867829 562949953421312) (BSN.sin_reduce1 qz814 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep2198) (@Nat.cast Real Real.instNatCast ep2028)) ep1856 ep1834 Bool.false 666115707862696 1125899906842624 68 ep1857 406527244500992 203263622250496 (BSN.sin_reduce_arg_pos_rat_q1 241936251409867829 562949953421312 ep1856 ep1834 68 ep2198 ep2028 rfl rfl rfl rfl) EMRow40.d185 (@BSN.cos_arg_round Bool.false 666115707862696 1125899906842624 ep2198 ep2028 2162229747291359598 2305843009213693952 406924243763201 406527244500992 (ep2210 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep2212 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz811 (Real.cos qz420)) (@HMul.hMul Real Real Real qz0 qz811 qz994) Bool.true 2692109859555060160923 ep2135 10739688204656638779 ep2136 Bool.true 493894905437798745517 ep2186 3940622828050858757 ep2187 (@Enclosure.Real.IsNear.mulLit_ft qz811 (Real.cos qz420) 5931641 1125899906842624 1 1125899906842624 453855831726003 562949953421312 16463995 13321084747808505856 2692109859555060160923 ep2135 10739688204656638779 ep2136 (@Enclosure.Real.IsNear.recentre' qz811 Bool.false 5931641 1125899906842624 1 1125899906842624 5931641 1125899906842624 1 1125899906842624 (ep2190 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' (Real.cos qz420) Bool.true 907711663452006 1125899906842624 141424640173015040 ep2191 453855831726003 562949953421312 16463995 13321084747808505856 (ep2205 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz811 qz994 5931641 1125899906842624 1 1125899906842624 83264463482837 140737488355328 16463995 13321084747808505856 493894905437798745517 ep2186 3940622828050858757 ep2187 (@Enclosure.Real.IsNear.recentre' qz811 Bool.false 5931641 1125899906842624 1 1125899906842624 5931641 1125899906842624 1 1125899906842624 (ep2190 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg (Real.sin qz420) Bool.false 83264463482837 140737488355328 16463995 13321084747808505856 (@Enclosure.Real.IsNear.recentre' (Real.sin qz420) Bool.false 666115707862696 1125899906842624 141424640173015040 ep2191 83264463482837 140737488355328 16463995 13321084747808505856 (ep2211 rfl rfl) rfl)) rfl)

noncomputable def ep2213 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.im qz244) 7131677479731368925469 7382812500000000 0 1 493894905437798745517 ep2186 3940622828050858757 ep2187 ep2129

noncomputable def ep2214 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) Bool.false 230767387107886469 2362500000000 0 1 Bool.false 7131677479731368925469 7382812500000000 0 1 ep2184

noncomputable def ep2215 := @Enclosure.Complex.IsNear.im_isNear qz244 Bool.true 2692109859555060160923 ep2135 10739688204656638779 ep2136 Bool.true 493894905437798745517 ep2186 3940622828050858757 ep2187

noncomputable def ep2216 := nat_lit 16282119547682497848515579980779815639

noncomputable def ep2217 := nat_lit 53479009697128427875642166476800000000000

noncomputable def ep2218 := nat_lit 909367233606986861038159262710459033

noncomputable def ep2219 := nat_lit 17716633290484099843498488194767257600000000000

noncomputable def ep2220 := nat_lit 914250440873885762160569514545376415868947

noncomputable def ep2221 := nat_lit 222829207071368449481842360320000000000000000

noncomputable def ep2222 := nat_lit 25530664169495455976714725935631502054117

noncomputable def ep2223 := @Enclosure.Real.IsNear.addLit_tt (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.im qz244)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.re qz244)) ep2216 ep2217 ep2218 ep2219 ep2220 ep2221 ep2222

noncomputable def ep2224 := nat_lit 36909652688508541340621850405765120000000000000000

noncomputable def ep2225 := nat_lit 52521339981349796380341709159395016180616043651275375381116207349995929600000000000

noncomputable def ep2226 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.im qz244) 230767387107886469 2362500000000 0 1 493894905437798745517 ep2186 3940622828050858757 ep2187 ep2216

noncomputable def ep2227 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.re qz244) 7131677479731368925469 7382812500000000 0 1 2692109859555060160923 ep2135 10739688204656638779 ep2136 ep2220

noncomputable abbrev qz815 := (@ep2189 ep2187 (BSN.cpow_neg_s_sub_mk qz61 124004 1000 32 5 36028797018963968 (@Eq.refl Real qz61) rfl EMRow40.d187) ep2212)

noncomputable def ep2228 := ep2124 (@ep2132 ep2133 ep2134 ep2116 ep2117 ep2118 ep2119 (@ep2137 ep2126 ep2127 ep2128 ep2185 (ep2188 qz815) rfl) (@ep2213 ep2130 ep2131 ep2133 ep2214 (ep2215 qz815) rfl) rfl rfl) (@ep2223 ep2224 ep2225 ep2121 ep2117 ep2122 ep2119 (@ep2226 ep2217 ep2218 ep2219 ep2185 (ep2215 qz815) rfl) (@ep2227 ep2221 ep2222 ep2224 ep2214 (ep2188 qz815) rfl) rfl rfl)

noncomputable def ep2229 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244)) ep2121 ep2117 ep2122 ep2119 ep2121 ep2117 ep2122

noncomputable def ep2230 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244) Bool.false ep2116 ep2117 ep2118 ep2119 Bool.true ep2121 ep2117 ep2122

noncomputable def ep2231 := @ep2088 46848551389312750317 405828369621610135552 2227089510157 101457092405402533888 (@ep2089 1 5767168 (ep2090 (@ep2091 1048576 1 1048576 (ep2092 (@ep2093 3851810504 481476313 31250 0 1 (ep2097 rfl) (ep2100 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 11) rfl) (@ep2101 131357 140737488355328 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244)) (@ep2102 1050856 1125899906842624 359943055089 70368744177664 131357 140737488355328 (@ep2107 2879543915284 2879544966140 562949953421312 (@ep2113 ep2109 ep2114 ep2111 ep2115 ep2103 ep2104 ep2105 ep2106 (@ep2120 ep2119 ep2108 ep2109 ep2110 ep2111 (@ep2123 ep2119 ep2228) (@ep2123 ep2119 ep2228) rfl) (@ep2229 ep2119 ep2112 ep2109 ep2114 ep2111 (@ep2230 ep2119 ep2228) (@ep2230 ep2119 ep2228) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow40.d188 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz607 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 2 4) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz64 2 32))) (@HMul.hMul Real Real Real qz0 qz804 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244)))) Bool.false ep2062 ep2063 3563077361011220557 ep2064 := ep2086 (ep2087 ep2231) rfl rfl

noncomputable def EMRow40.d189 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J))

noncomputable abbrev qz250 := (@Enclosure.dec_le_dec qz259 qz389 121891 1000 124004 1000 (@Eq.refl Real qz259) (@Eq.refl Real qz389) rfl rfl rfl)

noncomputable abbrev qz816 := (EMRow40.d3 qz11 qz61 qz250 31 32 2 2)

noncomputable def ep2232 := @Zeta.Certificates.ZIntervalEM.Certificate.mk qz816 (@Enclosure.dec_nonneg qz11 121891 1000 (@Eq.refl Real qz11)) (@Enclosure.pos_of_ble 2 rfl) (@Enclosure.pos_of_ble 31 rfl)

noncomputable def ep2233 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalEM.fstVal qz816) ep462 ep463

noncomputable def ep2234 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalEM.fstVal qz816) (hardyZApproximantEM 2 31 qz11) Bool.false

noncomputable def ep2235 := BSN.mul_neg_of_pos_neg_r (Zeta.Certificates.ZIntervalEM.fstVal qz816) (Zeta.Certificates.ZIntervalEM.sndVal qz816) (@ep2233 ep464 ep465 (@ep2234 ep462 ep463 ep464 ep465 (@Eq.refl Real (hardyZApproximantEM 2 31 qz11)) EMRow40.d15) rfl rfl rfl)

noncomputable def ep2236 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalEM.sndVal qz816) ep1284 ep1285

noncomputable def ep2237 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalEM.sndVal qz816) (hardyZApproximantEM 2 32 qz61) Bool.true

noncomputable def ep2238 := BSN.gt_trans_le (@Norm.norm Real Real.norm (Zeta.Certificates.ZIntervalEM.fstVal qz816)) (BSN.hardyZErrorBoundStrong 2 31 qz11)

noncomputable def ep2239 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalEM.fstVal qz816) (BSN.hardyZErrorBoundStrong 2 31 qz11) Bool.false

noncomputable def ep2240 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 2 31 qz11) (@HAdd.hAdd Real Real Real qz607 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 2 4) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz14 2 31))) (@HMul.hMul Real Real Real qz0 qz234 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236)))) Bool.false 47782147648089184528695 385172627945073865129984 916125253749084045 ep1858 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz607 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 2 4) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz14 2 31))) (@HMul.hMul Real Real Real qz0 qz234 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236)))))

noncomputable def ep2241 := BSN.gt_trans_le (@Norm.norm Real Real.norm (Zeta.Certificates.ZIntervalEM.sndVal qz816)) (BSN.hardyZErrorBoundStrong 2 32 qz61)

noncomputable def ep2242 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalEM.sndVal qz816) (BSN.hardyZErrorBoundStrong 2 32 qz61) Bool.true

noncomputable def ep2243 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 2 32 qz61) (@HAdd.hAdd Real Real Real qz607 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 2 4) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz64 2 32))) (@HMul.hMul Real Real Real qz0 qz804 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244)))) Bool.false ep2062 ep2063 3563077361011220557 ep2064 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz607 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 2 4) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz64 2 32))) (@HMul.hMul Real Real Real qz0 qz804 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244)))))

noncomputable def ep2244 := @List.cons EMRow40.d0 (@PSigma.mk Zeta.Certificates.ZIntervalEM Zeta.Certificates.ZIntervalEM.Certificate qz816 (ep2232 (@Enclosure.pos_of_ble 2 rfl) (@Enclosure.pos_of_ble 32 rfl) (ep2235 (@ep2236 ep1286 ep1287 (@ep2237 ep1284 ep1285 ep1286 ep1287 (@Eq.refl Real (hardyZApproximantEM 2 32 qz61)) EMRow40.d23) rfl rfl rfl)) (ep2238 (hardyZErrorBoundEM 2 31 qz11) (BSN.hardyZErrorBoundEM_le_strong 2 31 qz11 rfl) (@ep2239 Bool.false ep462 ep463 ep464 ep465 47782147648089184528695 385172627945073865129984 916125253749084045 ep1858 (@ep2234 ep462 ep463 ep464 ep465 (@Eq.refl Real (hardyZApproximantEM 2 31 qz11)) EMRow40.d15) (ep2240 EMRow40.d186) rfl rfl rfl rfl rfl)) (ep2241 (hardyZErrorBoundEM 2 32 qz61) (BSN.hardyZErrorBoundEM_le_strong 2 32 qz61 rfl) (@ep2242 Bool.false ep1284 ep1285 ep1286 ep1287 ep2062 ep2063 3563077361011220557 ep2064 (@ep2237 ep1284 ep1285 ep1286 ep1287 (@Eq.refl Real (hardyZApproximantEM 2 32 qz61)) EMRow40.d23) (ep2243 EMRow40.d188) rfl rfl rfl rfl rfl)))) (@List.nil EMRow40.d0)

noncomputable abbrev qz817 := (@NonemptyInterval Real Real.instLE)

noncomputable abbrev qz818 := (Zeta.Certificates.CertifiedZeroIntervals.intervals (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep2244 (@List.IsChain.singleton EMRow40.d1 EMRow40.d189 (EMRow40.d2 qz11 qz61 qz250))))

noncomputable def ep2245 := And (@Eq (Option Real) (@Option.map qz817 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz817 qz818)) (@Option.some Real qz11))

noncomputable def ep2246 := ep2245 (@Eq (Option Real) (@Option.map qz817 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz817 qz818)) (@Option.some Real qz61))

noncomputable def ep2247 := @And.intro (@Eq Nat (@List.length qz817 qz818) 1) ep2246

noncomputable def ep2248 := @And.intro (@Eq (Option Real) (@Option.map qz817 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz817 qz818)) (@Option.some Real qz11))

noncomputable def ep2249 := @ep2248 (@Eq (Option Real) (@Option.map qz817 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz817 qz818)) (@Option.some Real qz61))

noncomputable abbrev qz819 := (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep2244 (@List.IsChain.singleton EMRow40.d1 EMRow40.d189 (EMRow40.d2 qz11 qz61 qz250)))

theorem EMRow40.d190 : Zeta.Certificates.BatchSpec 1 121891 1000 124004 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz817 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 1) (And (@Eq (Option Real) (@Option.map qz817 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz817 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz11)) (@Eq (Option Real) (@Option.map qz817 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz817 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz61)))) qz819 (ep2247 (@Eq.refl Nat 1) (ep2249 (@Eq.refl (Option Real) (@Option.some Real qz11)) (@Eq.refl (Option Real) (@Option.some Real qz61))))

theorem solution : Zeta.Certificates.BatchSpec 1 121891 1000 124004 1000 := EMRow40.d190
#print axioms solution
#check solution
