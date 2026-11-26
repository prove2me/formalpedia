-- Prove2me | solution 1 for RHHeight1000.em_main_0041_0041
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T09:02:58.867757+00:00
-- url     : https://prove2.me/submissions/bd0e1766-2c61-45cc-b7d2-fdf700cf0f79

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

noncomputable def EMRow41.d0 := @PSigma Zeta.Certificates.ZIntervalEM fun (I : Zeta.Certificates.ZIntervalEM) => Zeta.Certificates.ZIntervalEM.Certificate I

noncomputable def EMRow41.d1 := @NonemptyInterval Real Real.instLE

noncomputable def EMRow41.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h

noncomputable def EMRow41.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) (fc sc fb sb : Nat) => Zeta.Certificates.ZIntervalEM.mk (EMRow41.d2 a b h) fc sc fb sb

noncomputable def ep0 := nat_lit 26986075409044028275299783

noncomputable def ep1 := nat_lit 4294967296000000000000000

noncomputable def ep2 := nat_lit 26986075409044045455168967

noncomputable abbrev qz0 := (@instHMul Real Real.instMul)

noncomputable abbrev qz249 := (Enclosure.sfrac Bool.false 2 1)

noncomputable def ep3 := @BSN.isNear_log_image_fff (@HMul.hMul Real Real Real qz0 qz249 Real.pi) 884279719003555 140737488355328 1 500000000000000 ep0 ep1 ep2 ep1 4138529546116343 2251799813685248 50000000038077 19038500000000000000 4138529546116343 2251799813685248 50000000038077 19038500000000000000 963576 524288

noncomputable abbrev qz250 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 2 1) Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) BSN.pi_near_15 rfl)

noncomputable def ep4 := @ep3 2 524288 qz250 rfl rfl rfl rfl

noncomputable def ep5 := nat_lit 53972150818088056550599566

noncomputable def ep6 := nat_lit 34359738368000000000000000

noncomputable def ep7 := nat_lit 9806206225044028275299783

noncomputable def ep8 := nat_lit 44165944593044028275299783

noncomputable def ep9 := nat_lit 13681445815609410487519367394620474863599256634174726093703677122907123617368241606644861540940610176751640793056574796245399519365549113997355475306157239709119582688278313060810592403844863400465080549957745

noncomputable def ep10 := nat_lit 231714499556395493334623298703961145503103241611736774613091488581016477543539392410113701224645713379230392133956226737605624599560350113120270717249177907454870984269546186598262646369758174842349131395304

noncomputable def ep11 := nat_lit 8978369550011295664474073352761810093897501552430546263638635096022803738134167562509900960712119243631997923545019968443113540909076206607473711060286601587364321108377403290080403445693385008949995305

noncomputable def ep12 := BSN.log_dyadic_bound ep7 ep8 5 4 ep9 1048576 380770 ep10 ep11 473518 ep5 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep7) (BSN.artanhQ ep8) 0 4 ep10 ep9 ep11 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz1 := (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))

noncomputable def ep13 := ep4 rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep1 4138529546116343 2251799813685248 50000000038077 19038500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep0) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 69433004117575847641088 37778931862957161709568 1000000000761540 380770000000000000000 4138529546116343 2251799813685248 50000000038077 19038500000000000000 (BSN.log_rat_reduce_isNear ep0 ep1 2 ep5 ep6 473518 1048576 24973259072661432 36028797018963968 380770 1000000000000000 rfl rfl rfl rfl (ep12 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep14 := nat_lit 53972150818088090910337934

noncomputable def ep15 := nat_lit 9806206225044045455168967

noncomputable def ep16 := nat_lit 44165944593044045455168967

noncomputable def ep17 := nat_lit 13681445815609453062485491347592146866046743284321690683909457683007658987562290830600045658905080811372395010565947827677605470036294121079488508864180301737865471494204890974265645509835068840465080549957745

noncomputable def ep18 := nat_lit 231714499556396865510889920206523150079811393376960301632499817942333196803513131357563499488546302200815366867712007119763002650772307103678175657719139104636874731038771518520299266622696414842349131395304

noncomputable def ep19 := nat_lit 8978369550011421500876706511871067098718760264493934208903156435737864998391937547068187824077011975074541700434630537294838404525415248443919841847024664017658842168336182958576672102333385008949995305

noncomputable def ep20 := BSN.log_dyadic_bound ep15 ep16 5 4 ep17 1048576 380770 ep18 ep19 473518 ep14 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep15) (BSN.artanhQ ep16) 0 4 ep18 ep17 ep19 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep21 := ep13 (BSN.isNear_log_sfrac ep2 ep1 4138529546116343 2251799813685248 50000000038077 19038500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep2) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 69433004117575847641088 37778931862957161709568 1000000000761540 380770000000000000000 4138529546116343 2251799813685248 50000000038077 19038500000000000000 (BSN.log_rat_reduce_isNear ep2 ep1 2 ep14 ep6 473518 1048576 24973259072661432 36028797018963968 380770 1000000000000000 rfl rfl rfl rfl (ep20 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable abbrev qz251 := (Real.log (@HMul.hMul Real Real Real qz0 (2 : Real) Real.pi))

theorem EMRow41.d4 : Enclosure.Real.IsNear qz251 Bool.false 120447 65536 1 262144 := @Enclosure.Real.IsNear.of_eq qz251 (Real.log (@HMul.hMul Real Real Real qz0 qz249 Real.pi)) Bool.false 120447 65536 1 262144 BSN.log_two_pi_eq (@Enclosure.Real.IsNear.recentre' (Real.log (@HMul.hMul Real Real Real qz0 qz249 Real.pi)) Bool.false 963576 524288 2 524288 120447 65536 1 262144 (ep21 rfl rfl rfl rfl rfl rfl rfl rfl) rfl)

noncomputable abbrev qz543 := (@instHPow Complex Nat (@NPow.toPow Complex (@Monoid.toNPow Complex (@Semiring.toMonoid Complex Complex.instSemiring))))

noncomputable abbrev qz813 := (@instHAdd Complex Complex.instAdd)

noncomputable abbrev qz814 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (4 : Complex))

noncomputable abbrev qz815 := (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid))

noncomputable abbrev qz544 := (@HAdd.hAdd Complex Complex Complex qz813 (@HAdd.hAdd Complex Complex Complex qz813 qz814 (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I (@HDiv.hDiv Complex Complex Complex qz815 (↑(Enclosure.sfrac Bool.false 124004 1000)) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 4))

noncomputable abbrev qz252 := (@HPow.hPow Complex Nat Complex qz543 qz544 3)

noncomputable abbrev qz2 := qz252

noncomputable def ep22 := Enclosure.Complex.IsNear qz2 Bool.true 24468698213 500000 0 1 Bool.true 14686958210563 62500000 0 1

noncomputable abbrev qz545 := (@instHMul Complex Complex.instMul)

noncomputable abbrev qz253 := qz545

noncomputable abbrev qz3 := qz253

noncomputable abbrev qz254 := qz543

noncomputable abbrev qz255 := qz544

noncomputable abbrev qz4 := (@HPow.hPow Complex Nat Complex qz254 qz255 2)

noncomputable abbrev qz5 := qz255

noncomputable def ep23 := @Enclosure.Complex.IsNear.of_eq qz2 (@HMul.hMul Complex Complex Complex qz3 qz4 qz5) Bool.true 24468698213 500000 0 1 Bool.true 14686958210563 62500000

noncomputable def ep24 := @Enclosure.Complex.IsNear.mul qz4 qz5 Bool.true 24468698213 500000 0 1 Bool.true 14686958210563 62500000 0

noncomputable def ep25 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re qz4) (Complex.re qz5)) (@HMul.hMul Real Real Real qz0 (Complex.im qz4) (Complex.im qz5)) 2032661049 125000 0 1 16338054017 500000

noncomputable def ep26 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re qz4) (Complex.re qz5) 119568297 31250 0 1 17000 4000 0 1

noncomputable def ep27 := @Enclosure.Complex.IsNear.re_isNear qz4 Bool.true 119568297 31250 0 1 Bool.false 527017 1000 0 1

noncomputable abbrev qz256 := (@HPow.hPow Complex Nat Complex qz543 qz544 1)

noncomputable abbrev qz6 := qz256

noncomputable def ep28 := @Enclosure.Complex.IsNear.of_eq qz4 (@HMul.hMul Complex Complex Complex qz3 qz6 qz5) Bool.true 119568297 31250 0 1 Bool.false 527017 1000

noncomputable def ep29 := @Enclosure.Complex.IsNear.mul qz6 qz5 Bool.true 119568297 31250 0 1 Bool.false 527017 1000 0

noncomputable abbrev qz7 := (Complex.re qz256)

noncomputable abbrev qz8 := (Complex.im qz256)

noncomputable def ep30 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz7 (Complex.re qz5)) (@HMul.hMul Real Real Real qz0 qz8 (Complex.im qz5)) 289 16 0 1 961062001 250000

noncomputable def ep31 := @Enclosure.Real.IsNear.mulLit_ff qz7 (Complex.re qz5) 17000 4000 0 1 17000 4000 0 1

noncomputable def ep32 := @Enclosure.Complex.IsNear.re_isNear qz6 Bool.false 17000 4000 0 1 Bool.false 248008 4000 0 1

noncomputable def ep33 := @Enclosure.Complex.IsNear.of_eq qz6 qz5 Bool.false 17000 4000 0 1 Bool.false 248008 4000 0

noncomputable abbrev qz257 := (Enclosure.sfrac Bool.false 124004 1000)

noncomputable abbrev qz9 := qz257

noncomputable abbrev qz258 := (Enclosure.sfrac Bool.false 248008 4000)

noncomputable abbrev qz546 := (Complex.mk (Enclosure.sfrac Bool.false 17000 4000) qz258)

noncomputable def ep34 := @Enclosure.Complex.IsNear.of_eq qz5 qz546 Bool.false 17000 4000 0 1 Bool.false 248008 4000 0 1 (BSN.w_shift_mk qz9 Bool.false 124004 1000 4 (@Eq.refl Real qz9) rfl)

noncomputable abbrev qz547 := (Enclosure.sfrac Bool.false 17000 4000)

noncomputable abbrev qz10 := (@ep33 1 (BSN.pow_one_c qz255) (ep34 (@Enclosure.Complex.IsNear.mk qz547 qz258 Bool.false 17000 4000 0 1 Bool.false 248008 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 17000 4000) (Enclosure.Real.IsNear.const Bool.false 248008 4000))))

noncomputable abbrev qz11 := (ep34 (@Enclosure.Complex.IsNear.mk qz547 qz258 Bool.false 17000 4000 0 1 Bool.false 248008 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 17000 4000) (Enclosure.Real.IsNear.const Bool.false 248008 4000)))

noncomputable abbrev qz816 := (@Enclosure.Complex.IsNear.re_isNear qz5 Bool.false 17000 4000 0 1 Bool.false 248008 4000 0 1 qz11)

noncomputable def ep35 := @ep31 289 16 0 1 (ep32 qz10) qz816

noncomputable def ep36 := @Enclosure.Real.IsNear.mulLit_ff qz8 (Complex.im qz5) 248008 4000 0 1 248008 4000 0 1

noncomputable def ep37 := @Enclosure.Complex.IsNear.im_isNear qz6 Bool.false 17000 4000 0 1 Bool.false 248008 4000 0 1

noncomputable abbrev qz817 := (@Enclosure.Complex.IsNear.im_isNear qz5 Bool.false 17000 4000 0 1 Bool.false 248008 4000 0 1 qz11)

noncomputable def ep38 := @ep36 961062001 250000 0 1 (ep37 qz10) qz817

noncomputable def ep39 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz7 (Complex.im qz5)) (@HMul.hMul Real Real Real qz0 qz8 (Complex.re qz5)) 527017 2000 0 1 527017 2000

noncomputable def ep40 := @Enclosure.Real.IsNear.mulLit_ff qz7 (Complex.im qz5) 17000 4000 0 1 248008 4000 0 1

noncomputable def ep41 := @ep40 527017 2000 0 1 (ep32 qz10) qz817

noncomputable def ep42 := @Enclosure.Real.IsNear.mulLit_ff qz8 (Complex.re qz5) 248008 4000 0 1 17000 4000 0 1

noncomputable def ep43 := @ep42 527017 2000 0 1 (ep37 qz10) qz816

noncomputable abbrev qz548 := (@ep28 0 1 (BSN.pow_succ_c qz5 1 2 rfl) (@ep29 1 (@ep30 0 1 15304742016 119568297 31250 0 1 (ep35 rfl) (ep38 rfl) rfl rfl) (@ep39 0 1 2108068000 527017 1000 0 1 (ep41 rfl) (ep43 rfl) rfl rfl)))

noncomputable def ep44 := @ep26 2032661049 125000 0 1 (ep27 qz548) qz816

noncomputable def ep45 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz4) (Complex.im qz5) 527017 1000 0 1 248008 4000 0 1

noncomputable def ep46 := @Enclosure.Complex.IsNear.im_isNear qz4 Bool.true 119568297 31250 0 1 Bool.false 527017 1000 0 1

noncomputable def ep47 := @ep45 16338054017 500000 0 1 (ep46 qz548) qz817

noncomputable def ep48 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re qz4) (Complex.im qz5)) (@HMul.hMul Real Real Real qz0 (Complex.im qz4) (Complex.re qz5)) 3706736775297 15625000 0 1 8959289 4000

noncomputable def ep49 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re qz4) (Complex.im qz5) 119568297 31250 0 1 248008 4000 0 1

noncomputable def ep50 := @ep49 3706736775297 15625000 0 1 (ep27 qz548) qz817

noncomputable def ep51 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz4) (Complex.re qz5) 527017 1000 0 1 17000 4000 0 1

noncomputable def ep52 := @ep51 8959289 4000 0 1 (ep46 qz548) qz816

theorem EMRow41.d5 : ep22 := @ep23 0 1 (BSN.pow_succ_c qz5 2 3 rfl) (@ep24 1 (@ep25 0 1 3058587276625000 24468698213 500000 0 1 (ep44 rfl) (ep47 rfl) rfl rfl) (@ep48 0 1 14686958210563000 14686958210563 62500000 0 1 (ep50 rfl) (ep52 rfl) rfl rfl))

noncomputable def ep53 := nat_lit 8589934592000000000000000

noncomputable def ep54 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 ep0 ep53 ep2 ep53 1200336 1048576 1 380770 1200336 1048576 1 380770 600168 524288 2 524288 BSN.pi_near_15 rfl rfl rfl

noncomputable def ep55 := nat_lit 17179869184000000000000000

noncomputable def ep56 := nat_lit 18396140817044028275299783

noncomputable def ep57 := nat_lit 35576010001044028275299783

noncomputable def ep58 := nat_lit 145019262663961446558303139663424756232419223153299357158415217874016130572233056993847515999529612750616182853355499335896178729185698845314776375864537073527142908641610750276034469165612529925303649396973267518946591078603565291376312767403717761600170009932259137778521478520425507632472584532570900560707662248426541531715360699177249902784721815296292248142738824858695953661559845440650653128788875447728828657762006237171740033404723254477174341920697506370253193455781322964835857351124092897592956162654178130575

noncomputable def ep59 := nat_lit 15500762873619990602332184736899274490522931101512051618692838888825382235673431503644115344741331161500627469184702974962114537943617674254904297224139410345221262767191485292268260077615645253784097850065864022184521411511133693085443040736512010941548648374196772723338837137976260321103066698629790037694560548409922339907589559883712609967105556007429010014773911317423638534096849366294542840133852248768895750397896505791271178551667935288585787166713880920071720072716082683081155281219708172458141800988558163320

noncomputable def ep60 := nat_lit 12900190794487083783367107939442176642390171280542213571554777169279725287102813254708993369099729304728646904879886535518616983985412662170766446331701281703998252143668221340329975389245922410714088123244705567402747658401492589451585970559635763980329972215329212888079422466283203384882259392047898400615815810081169907384366653346471604103896809335921621947903075223769953790093549808584241881353287841076643853121427928248525828402335494512605306631304432120211393210317325496757155861061354331245840675149075

noncomputable def ep61 := BSN.log_dyadic_bound ep56 ep57 11 10 ep58 1048576 380770 ep59 ep60 1200336 ep5 ep55 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep56) (BSN.artanhQ ep57) 0 10 ep59 ep58 ep60 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep62 := nat_lit 18396140817044045455168967

noncomputable def ep63 := nat_lit 35576010001044045455168967

noncomputable def ep64 := nat_lit 145019262663962847171784895425483977818796535899227200426399035286881207006285364467913811844950531107314785650583974625982406238691319033447632878979985852280879486690814033867010958364699188952871572448188560932645032521756218245629809291975913196623825614492380080480004685076434733043183791438169545293975334857826316990371107134320667652578346815517853870648072772035977941843998949310557583393428557296298890786965786350523173236912472938174255438182435383147950274229549088258679583524155427309880956162654178130575

noncomputable def ep65 := nat_lit 15500762873620157189619721156942591192100275120160672416764593300158228469749443299607348495591439275767946573253526107895503597951484257520435868240203420954375895980141891044871083424251900562230440202302413072793440172565998181227591194192658878334739610458454844032013325963992941389843551995646587189684848765634635122388286241104146031552341815777883628509454807838726994150833304950745987647656768534710890974432620160470644835720379148964170536679305861738540146791997074363921127776563807649880221800988558163320

noncomputable def ep66 := nat_lit 12900190794487324729109480814509220959173684627296055849229843377126536688487849343376525559792931631054411655715865486295286288812423905434305314401904993536755333953308594664509631000767632482919425633906965368325056855874260596615770736441041599390097968820060635361729170158825410327022636428624381203910573184452046894301676992229743752846881064485858738985580654099214803581683226335297196686880535448467637789069028262446657986458573827723305156755787640135484017403116612632808333639900906331245840675149075

noncomputable def ep67 := BSN.log_dyadic_bound ep62 ep63 11 10 ep64 1048576 380770 ep65 ep66 1200336 ep14 ep55 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep62) (BSN.artanhQ ep63) 0 10 ep65 ep64 ep66 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep68 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 600168 524288 2 524288 75021 65536 1 262144 (ep54 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep53 1200336 1048576 1 380770 Bool.false (BSN.logfrac_isNear ep5 ep55 1 ep0 ep53 1200336 1048576 380770 rfl rfl rfl (ep61 rfl))) (BSN.isNear_log_sfrac ep2 ep53 1200336 1048576 1 380770 Bool.false (BSN.logfrac_isNear ep14 ep55 1 ep2 ep53 1200336 1048576 380770 rfl rfl rfl (ep67 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl

theorem EMRow41.d6 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 75021 65536 1 262144 := ep68

noncomputable abbrev qz549 := qz813

noncomputable abbrev qz550 := (@HDiv.hDiv Complex Complex Complex qz815 (1 : Complex) (2 : Complex))

noncomputable abbrev qz259 := (@HAdd.hAdd Complex Complex Complex qz549 qz550 (@HMul.hMul Complex Complex Complex qz545 Complex.I ↑(Enclosure.sfrac Bool.false 124004 1000)))

noncomputable abbrev qz12 := qz259

noncomputable abbrev qz260 := qz549

noncomputable abbrev qz13 := qz260

noncomputable abbrev qz14 := (@instHPow Complex Complex Complex.instPow)

noncomputable abbrev qz15 := (@Neg.neg Complex Complex.instNeg qz259)

noncomputable abbrev qz818 := (@Nat.cast Complex Complex.instNatCast 8)

noncomputable def ep69 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 9) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 8) (@HPow.hPow Complex Complex Complex qz14 qz818 qz15)) Bool.true 3670267425 68719476736 116218243224273 52332630313533440 Bool.false 336530433525 549755813888 232551882414361 104665260627066880

noncomputable def ep70 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 8) (@HPow.hPow Complex Complex Complex qz14 qz818 qz15) Bool.true 435521191971 1099511627776 416013295848639 209330521254133760 Bool.false 384329748543 549755813888 208194247877347 104665260627066880 Bool.false

noncomputable abbrev qz819 := (@Nat.cast Complex Complex.instNatCast 7)

noncomputable def ep71 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 8) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 7) (@HPow.hPow Complex Complex Complex qz14 qz819 qz15)) Bool.true 435521191971 1099511627776 416013295848639 209330521254133760 Bool.false 384329748543 549755813888 208194247877347 104665260627066880

noncomputable def ep72 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 7) (@HPow.hPow Complex Complex Complex qz14 qz819 qz15) Bool.true 11630757337 137438953472 45477788206141 26166315156766720 Bool.false 1004062675711 1099511627776 364248940347553 209330521254133760 Bool.true

noncomputable abbrev qz820 := (@Nat.cast Complex Complex.instNatCast 6)

noncomputable def ep73 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 7) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 6) (@HPow.hPow Complex Complex Complex qz14 qz820 qz15)) Bool.true 11630757337 137438953472 45477788206141 26166315156766720 Bool.false 1004062675711 1099511627776 364248940347553 209330521254133760

noncomputable def ep74 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 6) (@HPow.hPow Complex Complex Complex qz14 qz820 qz15) Bool.false 197134568797 1099511627776 23653720626081 16102347788779520 Bool.false 1346527588027 1099511627776 23684749983441 16102347788779520 Bool.true

noncomputable abbrev qz16 := (@Nat.cast Complex Complex.instNatCast 5)

noncomputable def ep75 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 6) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 5) (@HPow.hPow Complex Complex Complex qz14 qz16 qz15)) Bool.false 197134568797 1099511627776 23653720626081 16102347788779520 Bool.false 1346527588027 1099511627776 23684749983441 16102347788779520

noncomputable def ep76 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 5) (@HPow.hPow Complex Complex Complex qz14 qz16 qz15) Bool.false 155206911627 1099511627776 49184591214199 41866104250826752 Bool.false 428301187359 549755813888 1538402837363 1308315757838336 Bool.false

noncomputable abbrev qz551 := (@Nat.cast Complex Complex.instNatCast 4)

noncomputable abbrev qz261 := qz551

noncomputable abbrev qz17 := qz261

noncomputable def ep77 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 5) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 4) (@HPow.hPow Complex Complex Complex qz14 qz17 qz15)) Bool.false 155206911627 1099511627776 49184591214199 41866104250826752 Bool.false 428301187359 549755813888 1538402837363 1308315757838336

noncomputable def ep78 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 4) (@HPow.hPow Complex Complex Complex qz14 qz17 qz15) Bool.false 504776317451 1099511627776 13613209707359 16102347788779520 Bool.false 1280903125235 1099511627776 13628160524249 16102347788779520 Bool.true

noncomputable abbrev qz552 := (@Nat.cast Complex Complex.instNatCast 3)

noncomputable def ep79 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 4) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 3) (@HPow.hPow Complex Complex Complex qz14 qz552 qz15)) Bool.false 504776317451 1099511627776 13613209707359 16102347788779520 Bool.false 1280903125235 1099511627776 13628160524249 16102347788779520

noncomputable def ep80 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 3) (@HPow.hPow Complex Complex Complex qz14 qz552 qz15) Bool.false 767686047261 1099511627776 97417553319901 209330521254133760 Bool.false 703103240125 1099511627776 97512887085571 209330521254133760 Bool.true

noncomputable abbrev qz553 := (@Nat.cast Complex Complex.instNatCast 2)

noncomputable def ep81 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 3) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 2) (@HPow.hPow Complex Complex Complex qz14 qz553 qz15)) Bool.false 767686047261 1099511627776 97417553319901 209330521254133760 Bool.false 703103240125 1099511627776 97512887085571 209330521254133760

noncomputable def ep82 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 2) (@HPow.hPow Complex Complex Complex qz14 qz553 qz15) Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.true

noncomputable abbrev qz262 := (Enclosure.sfrac Bool.false 0 1)

noncomputable def ep83 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz262) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz12)

noncomputable abbrev qz263 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2)))

noncomputable abbrev qz264 := (@HMul.hMul Real Real Real qz0 qz9 (Real.log (Enclosure.sfrac Bool.false 2 1)))

noncomputable def ep84 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz14 qz553 qz15) (Complex.mk (@HMul.hMul Real Real Real qz0 qz263 (Real.cos qz264)) (@HMul.hMul Real Real Real qz0 qz263 (@Neg.neg Real Real.instNeg (Real.sin qz264)))) Bool.true 331825580515 1099511627776 97417553319901 209330521254133760 Bool.false 703103240125 1099511627776 97512887085571 209330521254133760 (BSN.cpow_neg_s_mk qz9 124004 1000 2 (@Eq.refl Real qz9) rfl)

noncomputable abbrev qz265 := (@Nat.cast Real Real.instNatCast 1)

noncomputable def ep85 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 2)) 1482911 1048576 1 1048576 370727 370728 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 2)) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2) qz265)) Bool.false 1482911 1048576 1 1048576 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2) qz265)) Bool.false 1482911 1048576 1 1048576 1482911 1048576 1 1048576 (BSN.sqrt_enclosure 2 1 741455 741456 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep86 := BSN.log_dyadic_bound 1 3 6 5 613814355 524288 190385 24381081 945 363408 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 1) (BSN.artanhQ 3) 0 5 24381081 613814355 945 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep87 := nat_lit 1239490155484820154434528516543141487270795842229092420478363559185399530192896

noncomputable def ep88 := nat_lit 18237254054877300779212430138868345486890022584838388836214569481246317918289920

noncomputable def ep89 := nat_lit 1201120464452813459287239706928232233817495927330963576732077585699312828416

noncomputable def ep90 := nat_lit 3716068225525554836385011070215567997344752534832615334281626522384799964921856

noncomputable def ep91 := nat_lit 820676432469478535064559356249075546910051016317727497629655626656084306323046400

noncomputable abbrev qz266 := (BSN.cosEvenQ 2147483648)

noncomputable abbrev qz267 := (BSN.cosOddQ 2147483648)

noncomputable def ep92 := BSN.cos_dyadic_bound_f 2426321356 2147483648 3 2 1048576 381142 ep87 ep88 ep89 ep90 ep91 ep89 447533 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2426321356) qz266 0 2 ep87 ep88 ep89 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2426321356) qz267 0 2 ep90 ep91 ep89 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz268 := (@Nat.cast Real Real.instNatCast 1048576)

noncomputable abbrev qz269 := (Real.log (Enclosure.sfrac Bool.false 2 1))

noncomputable abbrev qz270 := (Enclosure.Real.IsNear.const Bool.false 124004 1000)

noncomputable abbrev qz271 := (@Nat.cast Real Real.instNatCast 151115727451828646838272)

noncomputable abbrev qz554 := (BSN.isNear_log_sfrac 2 1 363408 524288 1 190385 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 363408 524288 190385 rfl rfl rfl (ep86 rfl)))

noncomputable abbrev qz821 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 90128091) qz268)

noncomputable def ep93 := @Enclosure.Real.IsNear.cos_image qz264 qz821 Bool.false 90128091 1048576 171 262144 Bool.true 447533 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz264 Bool.false 704125713 8192000 1069 1641250 90128091 1048576 171 262144 (@Enclosure.Real.IsNear.mulLit_ff qz9 qz269 124004 1000 0 1 363408 524288 1 190385 704125713 8192000 1069 1641250 qz270 qz554 rfl) rfl) (Enclosure.sfrac_false_div 90128091 1048576) (BSN.cos_reduce2 qz821 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 170737186860210724012032) qz271) 226375608064910080 72057594037927936 Bool.false 447533 1048576 13 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q2 90128091 1048576 226375608064910080 72057594037927936 13 170737186860210724012032 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 447533 1048576 170737186860210724012032 151115727451828646838272 2426321356 2147483648 381142 380770 (ep92 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep94 := nat_lit 2230121383501114027214721538012112091300378519270501585999668744465159704084480

noncomputable def ep95 := nat_lit 164135286493895707012911871249815109382010203263545499525931125331216861264609280

noncomputable def ep96 := nat_lit 5838849428417613135199710401934790720265286842778492117541566205127143194689536

noncomputable def ep97 := nat_lit 3009146919054754628570050972913277005336853726498334157975403964405642456517836800

noncomputable abbrev qz272 := (BSN.sinEvenQ 2147483648)

noncomputable abbrev qz273 := (BSN.sinOddQ 2147483648)

noncomputable def ep98 := BSN.sin_dyadic_bound_f 2426321356 2147483648 3 2 1048576 381142 ep94 ep95 ep89 ep96 ep97 ep89 948275 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2426321356) qz272 0 2 ep94 ep95 ep89 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2426321356) qz273 0 2 ep96 ep97 ep89 rfl rfl rfl rfl) rfl rfl

noncomputable def ep99 := @Enclosure.Real.IsNear.sin_image qz264 qz821 Bool.false 90128091 1048576 171 262144 Bool.true 948275 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz264 Bool.false 704125713 8192000 1069 1641250 90128091 1048576 171 262144 (@Enclosure.Real.IsNear.mulLit_ff qz9 qz269 124004 1000 0 1 363408 524288 1 190385 704125713 8192000 1069 1641250 qz270 qz554 rfl) rfl) (Enclosure.sfrac_false_div 90128091 1048576) (BSN.sin_reduce2 qz821 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 170737186860210724012032) qz271) 226375608064910080 72057594037927936 Bool.false 948275 1048576 13 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q2 90128091 1048576 226375608064910080 72057594037927936 13 170737186860210724012032 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 948275 1048576 170737186860210724012032 151115727451828646838272 2426321356 2147483648 381142 380770 (ep98 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz555 := (@Enclosure.Real.IsNear.recentre' qz263 Bool.false 741455 1048576 1 1048576 741455 1048576 1 1048576 (ep85 rfl rfl) rfl)

noncomputable def ep100 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz263 (Real.cos qz264)) (@HMul.hMul Real Real Real qz0 qz263 (@Neg.neg Real Real.instNeg (Real.sin qz264))) Bool.true 331825580515 1099511627776 97417553319901 209330521254133760 Bool.false 703103240125 1099511627776 97512887085571 209330521254133760 (@Enclosure.Real.IsNear.mulLit_ft qz263 (Real.cos qz264) 741455 1048576 1 1048576 447533 1048576 32817979 49908285440 331825580515 1099511627776 97417553319901 209330521254133760 qz555 (@Enclosure.Real.IsNear.recentre' (Real.cos qz264) Bool.true 447533 1048576 32817979 49908285440 447533 1048576 32817979 49908285440 (ep93 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz263 (@Neg.neg Real Real.instNeg (Real.sin qz264)) 741455 1048576 1 1048576 948275 1048576 32817979 49908285440 703103240125 1099511627776 97512887085571 209330521254133760 qz555 (@Enclosure.Real.IsNear.neg (Real.sin qz264) Bool.true 948275 1048576 32817979 49908285440 (@Enclosure.Real.IsNear.recentre' (Real.sin qz264) Bool.true 948275 1048576 32817979 49908285440 948275 1048576 32817979 49908285440 (ep99 rfl rfl) rfl)) rfl)

noncomputable abbrev qz274 := (Enclosure.Real.IsNear.const Bool.false 0 1)

noncomputable def ep101 := @ep82 331825580515 1099511627776 97417553319901 209330521254133760 Bool.false 703103240125 1099511627776 97512887085571 209330521254133760 Bool.false 767686047261 767686047261 1099511627776 97417553319901 209330521254133760 Bool.false 703103240125 703103240125 1099511627776 97512887085571 209330521254133760 (ep83 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz262 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz274)) (ep84 ep100) rfl rfl

noncomputable abbrev qz275 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 3)))

noncomputable abbrev qz276 := (@HMul.hMul Real Real Real qz0 qz9 (Real.log (Enclosure.sfrac Bool.false 3 1)))

noncomputable def ep102 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz14 qz552 qz15) (Complex.mk (@HMul.hMul Real Real Real qz0 qz275 (Real.cos qz276)) (@HMul.hMul Real Real Real qz0 qz275 (@Neg.neg Real Real.instNeg (Real.sin qz276)))) Bool.true 131454864905 549755813888 39777086437883 104665260627066880 Bool.false 288899942555 549755813888 39826599864833 104665260627066880 (BSN.cpow_neg_s_mk qz9 124004 1000 3 (@Eq.refl Real qz9) rfl)

noncomputable def ep103 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 3)) 1816187 1048576 1 1048576 302697 302698 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 3)) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3) qz265)) Bool.false 1816187 1048576 1 1048576 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3) qz265)) Bool.false 1816187 1048576 1 1048576 1816187 1048576 1 1048576 (BSN.sqrt_enclosure 3 1 908093 908094 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep104 := BSN.log_dyadic_bound 1 2 10 9 171633298636800 524288 190385 16925142283965 34459425 575989 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP 1) (BSN.artanhQ 2) 0 9 16925142283965 171633298636800 34459425 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep105 := nat_lit 1301832874753323877649085804331594131346761193952637728820530701693738282909696

noncomputable def ep106 := nat_lit 1324855706672358172585764608937884927567227325601318600340000257601454473216

noncomputable def ep107 := nat_lit 3902848912846626916602085883776906624185149127206710549260912104566011939782656

noncomputable def ep108 := BSN.cos_dyadic_bound_f 2456241544 2147483648 3 2 1048576 381142 ep105 ep88 ep106 ep107 ep91 ep106 434278 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2456241544) qz266 0 2 ep105 ep88 ep106 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2456241544) qz267 0 2 ep107 ep91 ep106 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz277 := (Real.log (Enclosure.sfrac Bool.false 3 1))

noncomputable abbrev qz556 := (BSN.isNear_log_sfrac 3 1 575989 524288 1 190385 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 575989 524288 190385 rfl rfl rfl (ep104 rfl)))

noncomputable abbrev qz822 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 142849879) qz268)

noncomputable def ep109 := @Enclosure.Real.IsNear.cos_image qz276 qz822 Bool.false 142849879 1048576 171 262144 Bool.true 434278 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz276 Bool.false 17856234989 131072000 1069 1641250 142849879 1048576 171 262144 (@Enclosure.Real.IsNear.mulLit_ff qz9 qz277 124004 1000 0 1 575989 524288 1 190385 17856234989 131072000 1069 1641250 qz270 qz556 rfl) rfl) (Enclosure.sfrac_false_div 142849879 1048576) (BSN.cos_reduce2 qz822 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 172842632902935060676608) qz271) 226375608064910080 72057594037927936 Bool.false 434278 1048576 21 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q2 142849879 1048576 226375608064910080 72057594037927936 21 172842632902935060676608 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 434278 1048576 172842632902935060676608 151115727451828646838272 2456241544 2147483648 381142 380770 (ep108 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep110 := nat_lit 2342239289990645093230285836109719128482116367254266856996683262842647745658880

noncomputable def ep111 := nat_lit 6132291231212315235704657380444317332332338784281630109638381878456532217102336

noncomputable def ep112 := BSN.sin_dyadic_bound_f 2456241544 2147483648 3 2 1048576 381142 ep110 ep95 ep106 ep111 ep97 ep106 954418 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2456241544) qz272 0 2 ep110 ep95 ep106 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2456241544) qz273 0 2 ep111 ep97 ep106 rfl rfl rfl rfl) rfl rfl

noncomputable def ep113 := @Enclosure.Real.IsNear.sin_image qz276 qz822 Bool.false 142849879 1048576 171 262144 Bool.true 954418 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz276 Bool.false 17856234989 131072000 1069 1641250 142849879 1048576 171 262144 (@Enclosure.Real.IsNear.mulLit_ff qz9 qz277 124004 1000 0 1 575989 524288 1 190385 17856234989 131072000 1069 1641250 qz270 qz556 rfl) rfl) (Enclosure.sfrac_false_div 142849879 1048576) (BSN.sin_reduce2 qz822 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 172842632902935060676608) qz271) 226375608064910080 72057594037927936 Bool.false 954418 1048576 21 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q2 142849879 1048576 226375608064910080 72057594037927936 21 172842632902935060676608 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 954418 1048576 172842632902935060676608 151115727451828646838272 2456241544 2147483648 381142 380770 (ep112 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz557 := (@Enclosure.Real.IsNear.recentre' qz275 Bool.false 605395 1048576 1 1048576 605395 1048576 1 1048576 (ep103 rfl rfl) rfl)

noncomputable def ep114 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz275 (Real.cos qz276)) (@HMul.hMul Real Real Real qz0 qz275 (@Neg.neg Real Real.instNeg (Real.sin qz276))) Bool.true 131454864905 549755813888 39777086437883 104665260627066880 Bool.false 288899942555 549755813888 39826599864833 104665260627066880 (@Enclosure.Real.IsNear.mulLit_ft qz275 (Real.cos qz276) 605395 1048576 1 1048576 217139 524288 32817979 49908285440 131454864905 549755813888 39777086437883 104665260627066880 qz557 (@Enclosure.Real.IsNear.recentre' (Real.cos qz276) Bool.true 434278 1048576 32817979 49908285440 217139 524288 32817979 49908285440 (ep109 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz275 (@Neg.neg Real Real.instNeg (Real.sin qz276)) 605395 1048576 1 1048576 477209 524288 32817979 49908285440 288899942555 549755813888 39826599864833 104665260627066880 qz557 (@Enclosure.Real.IsNear.neg (Real.sin qz276) Bool.true 477209 524288 32817979 49908285440 (@Enclosure.Real.IsNear.recentre' (Real.sin qz276) Bool.true 954418 1048576 32817979 49908285440 477209 524288 32817979 49908285440 (ep113 rfl rfl) rfl)) rfl)

noncomputable def ep115 := @ep80 131454864905 549755813888 39777086437883 104665260627066880 Bool.false 288899942555 549755813888 39826599864833 104665260627066880 Bool.false 277503715231661962559488 504776317451 1099511627776 13613209707359 16102347788779520 Bool.false 704183940125250216263680 1280903125235 1099511627776 13628160524249 16102347788779520 (ep81 (BSN.head_sum_c_succ qz12 2 3 rfl rfl) (ep101 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep102 ep114) rfl rfl

noncomputable abbrev qz278 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 4)))

noncomputable abbrev qz279 := (Real.log (Enclosure.sfrac Bool.false 4 1))

noncomputable abbrev qz558 := (@HMul.hMul Real Real Real qz0 qz9 qz279)

noncomputable def ep116 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz14 qz17 qz15) (Complex.mk (@HMul.hMul Real Real Real qz0 qz278 (Real.cos qz558)) (@HMul.hMul Real Real Real qz0 qz278 (@Neg.neg Real Real.instNeg (Real.sin qz558)))) Bool.true 2731010983 8589934592 538681483401 1635394697297920 Bool.true 424300750517 1099511627776 68978367162843 209330521254133760 (BSN.cpow_neg_s_mk qz9 124004 1000 4 (@Eq.refl Real qz9) rfl)

noncomputable def ep117 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 4)) 2097153 1048576 1 1048576 262143 262144 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 4)) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4) qz265)) Bool.false 2097153 1048576 1 1048576 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4) qz265)) Bool.false 2097153 1048576 1 1048576 2097153 1048576 1 1048576 (BSN.sqrt_enclosure 4 1 1048576 1048577 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep118 := nat_lit 318077276165597140789031982421875

noncomputable def ep119 := nat_lit 49379992292270016474244603430625

noncomputable def ep120 := nat_lit 20095619060363156210525625

noncomputable def ep121 := BSN.log_dyadic_bound 3 5 14 13 ep118 524288 190385 ep119 ep120 726817 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base13 (BSN.artanhP 3) (BSN.artanhQ 5) 0 13 ep119 ep118 ep120 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep122 := nat_lit 4796441371007572396858587148225107361

noncomputable def ep123 := nat_lit 2552117751907038475975309555738261585920

noncomputable def ep124 := nat_lit 17864824263349269331827166890167831101440

noncomputable def ep125 := BSN.sin_dyadic_bound_f 1479891191 2147483648 2 1 1048576 381142 ep122 ep123 ep122 ep122 ep124 ep122 666752 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1479891191) qz272 0 1 ep122 ep123 ep122 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1479891191) qz273 0 1 ep122 ep124 ep122 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz280 := (@Nat.cast Real Real.instNatCast 524288)

noncomputable abbrev qz281 := (@Nat.cast Real Real.instNatCast 75557863725914323419136)

noncomputable abbrev qz559 := (BSN.isNear_log_sfrac 4 1 726817 524288 1 190385 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 726817 524288 190385 rfl rfl rfl (ep121 rfl)))

noncomputable abbrev qz823 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 90128215) qz280)

noncomputable def ep126 := @Enclosure.Real.IsNear.cos_image qz558 qz823 Bool.false 90128215 524288 171 262144 Bool.true 666752 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz558 Bool.false 22532053817 131072000 1069 1641250 90128215 524288 171 262144 (@Enclosure.Real.IsNear.mulLit_ff qz9 qz279 124004 1000 0 1 726817 524288 1 190385 22532053817 131072000 1069 1641250 qz270 qz559 rfl) rfl) (Enclosure.sfrac_false_div 90128215 524288) (BSN.cos_reduce1 qz823 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 52069042342396554117120) qz281) 226375608064910080 72057594037927936 Bool.false 666752 1048576 27 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q1 90128215 524288 226375608064910080 72057594037927936 27 52069042342396554117120 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 666752 1048576 52069042342396554117120 75557863725914323419136 1479891191 2147483648 381142 380770 (ep125 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep127 := nat_lit 171398170214842140970612835903460710747647802753205845423836851465097739784001

noncomputable def ep128 := nat_lit 23005849825513000756140373009905812274944978173257336390200266179976384321

noncomputable def ep129 := nat_lit 514148498944875396910326226964362320618393518303271021598730153862933266583361

noncomputable def ep130 := BSN.cos_dyadic_bound_f 1479891191 2147483648 3 2 1048576 381142 ep127 ep88 ep128 ep129 ep91 ep128 809291 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1479891191) qz266 0 2 ep127 ep88 ep128 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1479891191) qz267 0 2 ep129 ep91 ep128 rfl rfl rfl rfl) rfl rfl

noncomputable def ep131 := @Enclosure.Real.IsNear.sin_image qz558 qz823 Bool.false 90128215 524288 171 262144 Bool.false 809291 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz558 Bool.false 22532053817 131072000 1069 1641250 90128215 524288 171 262144 (@Enclosure.Real.IsNear.mulLit_ff qz9 qz279 124004 1000 0 1 726817 524288 1 190385 22532053817 131072000 1069 1641250 qz270 qz559 rfl) rfl) (Enclosure.sfrac_false_div 90128215 524288) (BSN.sin_reduce1 qz823 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 52069042342396554117120) qz281) 226375608064910080 72057594037927936 Bool.false 809291 1048576 27 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q1 90128215 524288 226375608064910080 72057594037927936 27 52069042342396554117120 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 809291 1048576 52069042342396554117120 75557863725914323419136 1479891191 2147483648 381142 380770 (ep130 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz560 := (@Enclosure.Real.IsNear.recentre' qz278 Bool.false 524287 1048576 1 1048576 524287 1048576 1 1048576 (ep117 rfl rfl) rfl)

noncomputable def ep132 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz278 (Real.cos qz558)) (@HMul.hMul Real Real Real qz0 qz278 (@Neg.neg Real Real.instNeg (Real.sin qz558))) Bool.true 2731010983 8589934592 538681483401 1635394697297920 Bool.true 424300750517 1099511627776 68978367162843 209330521254133760 (@Enclosure.Real.IsNear.mulLit_ft qz278 (Real.cos qz558) 524287 1048576 1 1048576 5209 8192 32817979 49908285440 2731010983 8589934592 538681483401 1635394697297920 qz560 (@Enclosure.Real.IsNear.recentre' (Real.cos qz558) Bool.true 666752 1048576 32817979 49908285440 5209 8192 32817979 49908285440 (ep126 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz278 (@Neg.neg Real Real.instNeg (Real.sin qz558)) 524287 1048576 1 1048576 809291 1048576 32817979 49908285440 424300750517 1099511627776 68978367162843 209330521254133760 qz560 (@Enclosure.Real.IsNear.neg (Real.sin qz558) Bool.false 809291 1048576 32817979 49908285440 (@Enclosure.Real.IsNear.recentre' (Real.sin qz558) Bool.false 809291 1048576 32817979 49908285440 809291 1048576 32817979 49908285440 (ep131 rfl rfl) rfl)) rfl)

noncomputable def ep133 := @ep78 2731010983 8589934592 538681483401 1635394697297920 Bool.true 424300750517 1099511627776 68978367162843 209330521254133760 Bool.false 1333217219102254301184 155206911627 1099511627776 49184591214199 41866104250826752 Bool.false 941844271382975288967168 428301187359 549755813888 1538402837363 1308315757838336 (ep79 (BSN.head_sum_c_succ qz12 3 4 rfl rfl) (ep115 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep116 ep132) rfl rfl

noncomputable abbrev qz561 := (@Nat.cast Real Real.instNatCast 5)

noncomputable abbrev qz282 := (@Inv.inv Real Real.instInv (Real.sqrt qz561))

noncomputable abbrev qz283 := (Real.log (Enclosure.sfrac Bool.false 5 1))

noncomputable abbrev qz562 := (@HMul.hMul Real Real Real qz0 qz9 qz283)

noncomputable def ep134 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz14 qz16 qz15) (Complex.mk (@HMul.hMul Real Real Real qz0 qz282 (Real.cos qz562)) (@HMul.hMul Real Real Real qz0 qz282 (@Neg.neg Real Real.instNeg (Real.sin qz562)))) Bool.false 20963828585 549755813888 30787706034029 104665260627066880 Bool.false 489925213309 1099511627776 61757295806653 209330521254133760 (BSN.cpow_neg_s_mk qz9 124004 1000 5 (@Eq.refl Real qz9) rfl)

noncomputable def ep135 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz561) 2344687 1048576 1 1048576 234468 234469 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz561) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz561 qz265)) Bool.false 2344687 1048576 1 1048576 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz561 qz265)) Bool.false 2344687 1048576 1 1048576 2344687 1048576 1 1048576 (BSN.sqrt_enclosure 5 1 1172343 1172344 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep136 := nat_lit 3696382175741467532940033205863946875

noncomputable def ep137 := nat_lit 765440954430599474856563326857688500

noncomputable def ep138 := nat_lit 108794268166472120024432640000

noncomputable def ep139 := BSN.log_dyadic_bound 2 3 18 17 ep136 524288 190385 ep137 ep138 843808 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.artanhP 2) (BSN.artanhQ 3) 0 17 8 307084260767580 1483365253795425 132843110400 1663129201793174588340 2491889415829100854875 818968088287641600 ep137 ep136 ep138 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.artanhP 2) (BSN.artanhQ 3) 0 8 307084260767580 1483365253795425 132843110400 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.artanhP 2) (BSN.artanhQ 3) 8 17 1663129201793174588340 2491889415829100854875 818968088287641600 rfl rfl rfl rfl)) rfl rfl

noncomputable def ep140 := BSN.sin_dyadic_bound_f 183335313 2147483648 1 0 1048576 381142 0 1 1 0 1 1 89410 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 183335313) qz272 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 183335313) qz273 0 0 rfl) rfl rfl

noncomputable abbrev qz563 := (BSN.isNear_log_sfrac 5 1 843808 524288 1 190385 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 843808 524288 190385 rfl rfl rfl (ep139 rfl rfl)))

noncomputable abbrev qz824 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 104635567) qz280)

noncomputable def ep141 := @Enclosure.Real.IsNear.cos_image qz562 qz824 Bool.false 104635567 524288 171 262144 Bool.false 89410 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz562 Bool.false 817465369 4096000 1069 1641250 104635567 524288 171 262144 (@Enclosure.Real.IsNear.mulLit_ff qz9 qz283 124004 1000 0 1 843808 524288 1 190385 817465369 4096000 1069 1641250 qz270 qz563 rfl) rfl) (Enclosure.sfrac_false_div 104635567 524288) (BSN.cos_reduce3 qz824 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6450537884600022073344) qz281) 226375608064910080 72057594037927936 Bool.false 89410 1048576 31 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q3 104635567 524288 226375608064910080 72057594037927936 31 6450537884600022073344 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 89410 1048576 6450537884600022073344 75557863725914323419136 183335313 2147483648 381142 380770 (ep140 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep142 := nat_lit 1129755586031094252709831309904961

noncomputable def ep143 := nat_lit 510423550381407695195061911147652317184

noncomputable def ep144 := nat_lit 7656353255721115427925928667214784757760

noncomputable def ep145 := BSN.cos_dyadic_bound_f 183335313 2147483648 2 1 1048576 381142 ep142 ep143 ep142 ep142 ep144 ep142 1044757 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 183335313) qz266 0 1 ep142 ep143 ep142 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 183335313) qz267 0 1 ep142 ep144 ep142 rfl rfl rfl rfl) rfl rfl

noncomputable def ep146 := @Enclosure.Real.IsNear.sin_image qz562 qz824 Bool.false 104635567 524288 171 262144 Bool.true 1044757 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz562 Bool.false 817465369 4096000 1069 1641250 104635567 524288 171 262144 (@Enclosure.Real.IsNear.mulLit_ff qz9 qz283 124004 1000 0 1 843808 524288 1 190385 817465369 4096000 1069 1641250 qz270 qz563 rfl) rfl) (Enclosure.sfrac_false_div 104635567 524288) (BSN.sin_reduce3 qz824 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6450537884600022073344) qz281) 226375608064910080 72057594037927936 Bool.false 1044757 1048576 31 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q3 104635567 524288 226375608064910080 72057594037927936 31 6450537884600022073344 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1044757 1048576 6450537884600022073344 75557863725914323419136 183335313 2147483648 381142 380770 (ep145 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz564 := (@Enclosure.Real.IsNear.recentre' qz282 Bool.false 468937 1048576 1 1048576 468937 1048576 1 1048576 (ep135 rfl rfl) rfl)

noncomputable def ep147 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz282 (Real.cos qz562)) (@HMul.hMul Real Real Real qz0 qz282 (@Neg.neg Real Real.instNeg (Real.sin qz562))) Bool.false 20963828585 549755813888 30787706034029 104665260627066880 Bool.false 489925213309 1099511627776 61757295806653 209330521254133760 (@Enclosure.Real.IsNear.mulLit_ff qz282 (Real.cos qz562) 468937 1048576 1 1048576 44705 524288 32817979 49908285440 20963828585 549755813888 30787706034029 104665260627066880 qz564 (@Enclosure.Real.IsNear.recentre' (Real.cos qz562) Bool.false 89410 1048576 32817979 49908285440 44705 524288 32817979 49908285440 (ep141 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz282 (@Neg.neg Real Real.instNeg (Real.sin qz562)) 468937 1048576 1 1048576 1044757 1048576 32817979 49908285440 489925213309 1099511627776 61757295806653 209330521254133760 qz564 (@Enclosure.Real.IsNear.neg (Real.sin qz562) Bool.true 1044757 1048576 32817979 49908285440 (@Enclosure.Real.IsNear.recentre' (Real.sin qz562) Bool.true 1044757 1048576 32817979 49908285440 1044757 1048576 32817979 49908285440 (ep146 rfl rfl) rfl)) rfl)

noncomputable def ep148 := @ep76 20963828585 549755813888 30787706034029 104665260627066880 Bool.false 489925213309 1099511627776 61757295806653 209330521254133760 Bool.false 108375875314454664052736 197134568797 1099511627776 23653720626081 16102347788779520 Bool.false 740261370078428949118976 1346527588027 1099511627776 23684749983441 16102347788779520 (ep77 (BSN.head_sum_c_succ qz12 4 5 rfl rfl) (ep133 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep134 ep147) rfl rfl

noncomputable abbrev qz825 := (@Nat.cast Real Real.instNatCast 6)

noncomputable abbrev qz284 := (@Inv.inv Real Real.instInv (Real.sqrt qz825))

noncomputable abbrev qz285 := (Real.log (Enclosure.sfrac Bool.false 6 1))

noncomputable abbrev qz565 := (@HMul.hMul Real Real Real qz0 qz9 qz285)

noncomputable def ep149 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz14 qz820 qz15) (Complex.mk (@HMul.hMul Real Real Real qz0 qz284 (Real.cos qz565)) (@HMul.hMul Real Real Real qz0 qz284 (@Neg.neg Real Real.instNeg (Real.sin qz565)))) Bool.true 290180627493 1099511627776 11264787502015 41866104250826752 Bool.true 85616228079 274877906944 2817359528141 10466526062706688 (BSN.cpow_neg_s_mk qz9 124004 1000 6 (@Eq.refl Real qz9) rfl)

noncomputable abbrev qz826 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6) qz265)

noncomputable def ep150 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz825) 2568477 1048576 1 1048576 214039 214040 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz825) (Real.sqrt qz826) Bool.false 2568477 1048576 1 1048576 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz826) Bool.false 2568477 1048576 1 1048576 2568477 1048576 1 1048576 (BSN.sqrt_enclosure 6 1 1284238 1284239 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep151 := BSN.log_dyadic_bound 2 10 4 3 105000000 524288 190385 1434560 960 212580 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 2) (BSN.artanhQ 10) 0 3 1434560 105000000 960 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep152 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz285 124004 1000 0 1 4034681531866359 2251799813685248 100000000038077 19038500000000000000 125079162169388995359 562949953421312000 106900000040704313 164125000000000000000 qz270 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 100000000038077 19038500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz826) Bool.false 33845361775666394038272 18889465931478580854784 1000000000380770 190385000000000000000 4034681531866359 2251799813685248 100000000038077 19038500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 212580 524288 24973259072661432 36028797018963968 190385 1000000000000000 rfl rfl rfl rfl (ep151 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep153 := nat_lit 5192763660495647770530271459945988241

noncomputable def ep154 := BSN.sin_dyadic_bound_f 1509557427 2147483648 2 1 1048576 381142 ep153 ep123 ep153 ep153 ep124 ep153 677867 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1509557427) qz272 0 1 ep153 ep123 ep153 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1509557427) qz273 0 1 ep153 ep124 ep153 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz827 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 116489047) qz280)

noncomputable def ep155 := @Enclosure.Real.IsNear.cos_image qz565 qz827 Bool.false 116489047 524288 171 262144 Bool.true 677867 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz565 Bool.false 125079162169388995359 562949953421312000 106900000040704313 164125000000000000000 116489047 524288 171 262144 (ep152 rfl) rfl) (Enclosure.sfrac_false_div 116489047 524288) (BSN.cos_reduce1 qz827 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 53112830222098019385344) qz281) 226375608064910080 72057594037927936 Bool.false 677867 1048576 35 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q1 116489047 524288 226375608064910080 72057594037927936 35 53112830222098019385344 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 677867 1048576 53112830222098019385344 75557863725914323419136 1509557427 2147483648 381142 380770 (ep154 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep156 := nat_lit 185562585266155796140879701186392678765108357314928619523490343799782746608161

noncomputable def ep157 := nat_lit 26964794433764159062184891846716975234819178725428994951398720990110274081

noncomputable def ep158 := nat_lit 556633826209599860104514733775484602344855433587335000580568233957368019276321

noncomputable def ep159 := BSN.cos_dyadic_bound_f 1509557427 2147483648 3 2 1048576 381142 ep156 ep88 ep157 ep158 ep91 ep157 800004 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1509557427) qz266 0 2 ep156 ep88 ep157 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1509557427) qz267 0 2 ep158 ep91 ep157 rfl rfl rfl rfl) rfl rfl

noncomputable def ep160 := @Enclosure.Real.IsNear.sin_image qz565 qz827 Bool.false 116489047 524288 171 262144 Bool.false 800004 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz565 Bool.false 125079162169388995359 562949953421312000 106900000040704313 164125000000000000000 116489047 524288 171 262144 (ep152 rfl) rfl) (Enclosure.sfrac_false_div 116489047 524288) (BSN.sin_reduce1 qz827 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 53112830222098019385344) qz281) 226375608064910080 72057594037927936 Bool.false 800004 1048576 35 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q1 116489047 524288 226375608064910080 72057594037927936 35 53112830222098019385344 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 800004 1048576 53112830222098019385344 75557863725914323419136 1509557427 2147483648 381142 380770 (ep159 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz566 := (@Enclosure.Real.IsNear.recentre' qz284 Bool.false 428079 1048576 1 1048576 428079 1048576 1 1048576 (ep150 rfl rfl) rfl)

noncomputable def ep161 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz284 (Real.cos qz565)) (@HMul.hMul Real Real Real qz0 qz284 (@Neg.neg Real Real.instNeg (Real.sin qz565))) Bool.true 290180627493 1099511627776 11264787502015 41866104250826752 Bool.true 85616228079 274877906944 2817359528141 10466526062706688 (@Enclosure.Real.IsNear.mulLit_ft qz284 (Real.cos qz565) 428079 1048576 1 1048576 677867 1048576 32817979 49908285440 290180627493 1099511627776 11264787502015 41866104250826752 qz566 (@Enclosure.Real.IsNear.recentre' (Real.cos qz565) Bool.true 677867 1048576 32817979 49908285440 677867 1048576 32817979 49908285440 (ep155 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz284 (@Neg.neg Real Real.instNeg (Real.sin qz565)) 428079 1048576 1 1048576 200001 262144 32817979 49908285440 85616228079 274877906944 2817359528141 10466526062706688 qz566 (@Enclosure.Real.IsNear.neg (Real.sin qz565) Bool.false 200001 262144 32817979 49908285440 (@Enclosure.Real.IsNear.recentre' (Real.sin qz565) Bool.false 800004 1048576 32817979 49908285440 200001 262144 32817979 49908285440 (ep160 rfl rfl) rfl)) rfl)

noncomputable def ep162 := @ep74 290180627493 1099511627776 11264787502015 41866104250826752 Bool.true 85616228079 274877906944 2817359528141 10466526062706688 Bool.true 102305223454980199940096 11630757337 137438953472 45477788206141 26166315156766720 Bool.false 275994646740031907037184 1004062675711 1099511627776 364248940347553 209330521254133760 (ep75 (BSN.head_sum_c_succ qz12 5 6 rfl rfl) (ep148 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep149 ep161) rfl rfl

noncomputable abbrev qz828 := (@Nat.cast Real Real.instNatCast 7)

noncomputable abbrev qz286 := (@Inv.inv Real Real.instInv (Real.sqrt qz828))

noncomputable abbrev qz287 := (Real.log (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz567 := (@HMul.hMul Real Real Real qz0 qz9 qz287)

noncomputable def ep163 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz14 qz819 qz15) (Complex.mk (@HMul.hMul Real Real Real qz0 qz286 (Real.cos qz567)) (@HMul.hMul Real Real Real qz0 qz286 (@Neg.neg Real Real.instNeg (Real.sin qz567)))) Bool.true 342475133275 1099511627776 52190990199511 209330521254133760 Bool.true 235403178625 1099511627776 52139555407141 209330521254133760 (BSN.cpow_neg_s_mk qz9 124004 1000 7 (@Eq.refl Real qz9) rfl)

noncomputable abbrev qz829 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 7) qz265)

noncomputable def ep164 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz828) 2774271 1048576 1 1048576 198162 198163 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz828) (Real.sqrt qz829) Bool.false 2774271 1048576 1 1048576 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz829) Bool.false 2774271 1048576 1 1048576 2774271 1048576 1 1048576 (BSN.sqrt_enclosure 7 1 1387135 1387136 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep165 := BSN.log_dyadic_bound 3 11 5 4 202569142545 524288 190385 5259111624 688905 293399 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 3) (BSN.artanhQ 11) 0 4 5259111624 202569142545 688905 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep166 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz287 124004 1000 0 1 4381796493761783 2251799813685248 100000000038077 19038500000000000000 135840073103109034783 562949953421312000 106900000040704313 164125000000000000000 qz270 (BSN.isNear_log_sfrac 7 1 4381796493761783 2251799813685248 100000000038077 19038500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz829) Bool.false 36757173121942042968064 18889465931478580854784 1000000000380770 190385000000000000000 4381796493761783 2251799813685248 100000000038077 19038500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 293399 524288 24973259072661432 36028797018963968 190385 1000000000000000 rfl rfl rfl rfl (ep165 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep167 := nat_lit 1204296394916314345007359904352204921954210801431072958826320874871014894608640

noncomputable def ep168 := nat_lit 350438236953733153712809409089322381585317367835083579302182810639683297536

noncomputable def ep169 := nat_lit 3153542229540041049913264724736296845071794918485839042559589233444955712921856

noncomputable def ep170 := BSN.sin_dyadic_bound_f 2080062746 2147483648 3 2 1048576 381142 ep167 ep95 ep168 ep169 ep97 ep168 864127 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2080062746) qz272 0 2 ep167 ep95 ep168 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2080062746) qz273 0 2 ep169 ep97 ep168 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz830 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 253021853) qz268)

noncomputable def ep171 := @Enclosure.Real.IsNear.cos_image qz567 qz830 Bool.false 253021853 1048576 171 262144 Bool.true 864127 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz567 Bool.false 135840073103109034783 562949953421312000 106900000040704313 164125000000000000000 253021853 1048576 171 262144 (ep166 rfl) rfl) (Enclosure.sfrac_false_div 253021853 1048576) (BSN.cos_reduce1 qz830 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 146371403249071031320576) qz271) 226375608064910080 72057594037927936 Bool.false 864127 1048576 38 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q1 253021853 1048576 226375608064910080 72057594037927936 38 146371403249071031320576 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 864127 1048576 146371403249071031320576 151115727451828646838272 2080062746 2147483648 381142 380770 (ep170 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep172 := nat_lit 669209303058820739739072306599709099921932808514078347605423678399737022914816

noncomputable def ep173 := nat_lit 2006927032702554752909791300980948655002627790806564875657666669577931702149376

noncomputable def ep174 := BSN.cos_dyadic_bound_f 2080062746 2147483648 3 2 1048576 381142 ep172 ep88 ep168 ep173 ep91 ep168 593965 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2080062746) qz266 0 2 ep172 ep88 ep168 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2080062746) qz267 0 2 ep173 ep91 ep168 rfl rfl rfl rfl) rfl rfl

noncomputable def ep175 := @Enclosure.Real.IsNear.sin_image qz567 qz830 Bool.false 253021853 1048576 171 262144 Bool.false 593965 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz567 Bool.false 135840073103109034783 562949953421312000 106900000040704313 164125000000000000000 253021853 1048576 171 262144 (ep166 rfl) rfl) (Enclosure.sfrac_false_div 253021853 1048576) (BSN.sin_reduce1 qz830 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 146371403249071031320576) qz271) 226375608064910080 72057594037927936 Bool.false 593965 1048576 38 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q1 253021853 1048576 226375608064910080 72057594037927936 38 146371403249071031320576 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 593965 1048576 146371403249071031320576 151115727451828646838272 2080062746 2147483648 381142 380770 (ep174 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz568 := (@Enclosure.Real.IsNear.recentre' qz286 Bool.false 396325 1048576 1 1048576 396325 1048576 1 1048576 (ep164 rfl rfl) rfl)

noncomputable def ep176 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz286 (Real.cos qz567)) (@HMul.hMul Real Real Real qz0 qz286 (@Neg.neg Real Real.instNeg (Real.sin qz567))) Bool.true 342475133275 1099511627776 52190990199511 209330521254133760 Bool.true 235403178625 1099511627776 52139555407141 209330521254133760 (@Enclosure.Real.IsNear.mulLit_ft qz286 (Real.cos qz567) 396325 1048576 1 1048576 864127 1048576 32817979 49908285440 342475133275 1099511627776 52190990199511 209330521254133760 qz568 (@Enclosure.Real.IsNear.recentre' (Real.cos qz567) Bool.true 864127 1048576 32817979 49908285440 864127 1048576 32817979 49908285440 (ep171 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz286 (@Neg.neg Real Real.instNeg (Real.sin qz567)) 396325 1048576 1 1048576 593965 1048576 32817979 49908285440 235403178625 1099511627776 52139555407141 209330521254133760 qz568 (@Enclosure.Real.IsNear.neg (Real.sin qz567) Bool.false 593965 1048576 32817979 49908285440 (@Enclosure.Real.IsNear.recentre' (Real.sin qz567) Bool.false 593965 1048576 32817979 49908285440 593965 1048576 32817979 49908285440 (ep175 rfl rfl) rfl)) rfl)

noncomputable def ep177 := @ep72 342475133275 1099511627776 52190990199511 209330521254133760 Bool.true 235403178625 1099511627776 52139555407141 209330521254133760 Bool.true 59857576839372248973312 435521191971 1099511627776 416013295848639 209330521254133760 Bool.false 845150054846509388660736 384329748543 549755813888 208194247877347 104665260627066880 (ep73 (BSN.head_sum_c_succ qz12 6 7 rfl rfl) (ep162 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep163 ep176) rfl rfl

noncomputable abbrev qz831 := (@Nat.cast Real Real.instNatCast 8)

noncomputable abbrev qz288 := (@Inv.inv Real Real.instInv (Real.sqrt qz831))

noncomputable abbrev qz289 := (Real.log (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz569 := (@HMul.hMul Real Real Real qz0 qz9 qz289)

noncomputable def ep178 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz14 qz818 qz15) (Complex.mk (@HMul.hMul Real Real Real qz0 qz288 (Real.cos qz569)) (@HMul.hMul Real Real Real qz0 qz288 (@Neg.neg Real Real.instNeg (Real.sin qz569)))) Bool.false 376796913171 1099511627776 48859677048453 209330521254133760 Bool.true 23899657509 274877906944 12178817268507 52332630313533440 (BSN.cpow_neg_s_mk qz9 124004 1000 8 (@Eq.refl Real qz9) rfl)

noncomputable abbrev qz832 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8) qz265)

noncomputable def ep179 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz831) 2965821 1048576 1 1048576 185363 185364 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz831) (Real.sqrt qz832) Bool.false 2965821 1048576 1 1048576 (BSN.sqrt_natCast_div_one 8) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz832) Bool.false 2965821 1048576 1 1048576 2965821 1048576 1 1048576 (BSN.sqrt_enclosure 8 1 1482910 1482911 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep180 := BSN.log_dyadic_bound 0 16 1 0 1 524288 190385 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl

noncomputable def ep181 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz289 124004 1000 0 1 9364972152248037 4503599627370496 200000000114231 38077000000000000000 290323501691841395037 1125899906842624000 213800000122112939 328250000000000000000 qz270 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 200000000114231 38077000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz832) Bool.false 39279540158062550581248 18889465931478580854784 1000000000571155 190385000000000000000 9364972152248037 4503599627370496 200000000114231 38077000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 524288 24973259072661432 36028797018963968 190385 1000000000000000 rfl rfl rfl rfl (ep180 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep182 := nat_lit 81063289418146036402351482930816016

noncomputable def ep183 := BSN.cos_dyadic_bound_f 533588002 2147483648 2 1 1048576 381142 ep182 ep143 ep182 ep182 ep144 ep182 1016373 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 533588002) qz266 0 1 ep182 ep143 ep182 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 533588002) qz267 0 1 ep182 ep144 ep182 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz833 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 270384831) qz268)

noncomputable def ep184 := @Enclosure.Real.IsNear.cos_image qz569 qz833 Bool.false 270384831 1048576 171 262144 Bool.false 1016373 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz569 Bool.false 290323501691841395037 1125899906842624000 213800000122112939 328250000000000000000 270384831 1048576 171 262144 (ep181 rfl) rfl) (Enclosure.sfrac_false_div 270384831 1048576) (BSN.cos_reduce0 qz833 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 37547917651036195520512) qz271) 226375608064910080 72057594037927936 Bool.false 1016373 1048576 41 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q0 270384831 1048576 226375608064910080 72057594037927936 41 37547917651036195520512 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1016373 1048576 37547917651036195520512 151115727451828646838272 533588002 2147483648 381142 380770 (ep183 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep185 := BSN.sin_dyadic_bound_f 533588002 2147483648 2 1 1048576 381142 ep182 ep123 ep182 ep182 ep124 ep182 257868 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 533588002) qz272 0 1 ep182 ep123 ep182 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 533588002) qz273 0 1 ep182 ep124 ep182 rfl rfl rfl rfl) rfl rfl

noncomputable def ep186 := @Enclosure.Real.IsNear.sin_image qz569 qz833 Bool.false 270384831 1048576 171 262144 Bool.false 257868 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz569 Bool.false 290323501691841395037 1125899906842624000 213800000122112939 328250000000000000000 270384831 1048576 171 262144 (ep181 rfl) rfl) (Enclosure.sfrac_false_div 270384831 1048576) (BSN.sin_reduce0 qz833 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 37547917651036195520512) qz271) 226375608064910080 72057594037927936 Bool.false 257868 1048576 41 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q0 270384831 1048576 226375608064910080 72057594037927936 41 37547917651036195520512 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 257868 1048576 37547917651036195520512 151115727451828646838272 533588002 2147483648 381142 380770 (ep185 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz570 := (@Enclosure.Real.IsNear.recentre' qz288 Bool.false 370727 1048576 1 1048576 370727 1048576 1 1048576 (ep179 rfl rfl) rfl)

noncomputable def ep187 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz288 (Real.cos qz569)) (@HMul.hMul Real Real Real qz0 qz288 (@Neg.neg Real Real.instNeg (Real.sin qz569))) Bool.false 376796913171 1099511627776 48859677048453 209330521254133760 Bool.true 23899657509 274877906944 12178817268507 52332630313533440 (@Enclosure.Real.IsNear.mulLit_ff qz288 (Real.cos qz569) 370727 1048576 1 1048576 1016373 1048576 32817979 49908285440 376796913171 1099511627776 48859677048453 209330521254133760 qz570 (@Enclosure.Real.IsNear.recentre' (Real.cos qz569) Bool.false 1016373 1048576 32817979 49908285440 1016373 1048576 32817979 49908285440 (ep184 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz288 (@Neg.neg Real Real.instNeg (Real.sin qz569)) 370727 1048576 1 1048576 64467 262144 32817979 49908285440 23899657509 274877906944 12178817268507 52332630313533440 qz570 (@Enclosure.Real.IsNear.neg (Real.sin qz569) Bool.false 64467 262144 32817979 49908285440 (@Enclosure.Real.IsNear.recentre' (Real.sin qz569) Bool.false 257868 1048576 32817979 49908285440 64467 262144 32817979 49908285440 (ep186 rfl rfl) rfl)) rfl)

noncomputable def ep188 := @ep70 376796913171 1099511627776 48859677048453 209330521254133760 Bool.true 23899657509 274877906944 12178817268507 52332630313533440 Bool.true 64568027373359647948800 3670267425 68719476736 116218243224273 52332630313533440 Bool.false 92504781190308927897600 336530433525 549755813888 232551882414361 104665260627066880 (ep71 (BSN.head_sum_c_succ qz12 7 8 rfl rfl) (ep177 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep178 ep187) rfl rfl

theorem EMRow41.d7 : Enclosure.Complex.IsNear (BSN.headSumC qz12 9) Bool.true 3670267425 68719476736 116218243224273 52332630313533440 Bool.false 336530433525 549755813888 232551882414361 104665260627066880 := ep69 (BSN.head_sum_c_succ qz12 8 9 rfl rfl) (ep188 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz834 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 16) qz15)

noncomputable def ep189 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 17) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 16) qz834) Bool.true 755071943339 1099511627776 781585148598903 209330521254133760 Bool.false 135108165307 1099511627776 781622917175203 209330521254133760

noncomputable def ep190 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 16) qz834 Bool.true 702537437567 1099511627776 747134849535459 209330521254133760 Bool.true 67350865507 549755813888 186753704709301 52332630313533440 Bool.true

noncomputable abbrev qz835 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 15) qz15)

noncomputable def ep191 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 16) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 15) qz835) Bool.true 702537437567 1099511627776 747134849535459 209330521254133760 Bool.true 67350865507 549755813888 186753704709301 52332630313533440

noncomputable def ep192 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 15) qz835 Bool.true 217523612377 549755813888 355702964703241 104665260627066880 Bool.true 19801165159 549755813888 177851780970493 52332630313533440 Bool.true

noncomputable abbrev qz836 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 14) qz15)

noncomputable def ep193 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 15) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 14) qz836) Bool.true 217523612377 549755813888 355702964703241 104665260627066880 Bool.true 19801165159 549755813888 177851780970493 52332630313533440

noncomputable def ep194 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 14) qz836 Bool.true 43056864387 68719476736 84305662410071 26166315156766720 Bool.false 108401004057 1099511627776 674518409976343 209330521254133760 Bool.false

noncomputable abbrev qz837 := (@HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast 13) qz15)

noncomputable def ep195 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 14) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 13) qz837) Bool.true 43056864387 68719476736 84305662410071 26166315156766720 Bool.false 108401004057 1099511627776 674518409976343 209330521254133760

noncomputable def ep196 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 13) qz837 Bool.true 58560285285 137438953472 19878874200417 6541578789191680 Bool.true 102326433513 1099511627776 636203435210409 209330521254133760 Bool.true

noncomputable abbrev qz838 := (@Nat.cast Complex Complex.instNatCast 12)

noncomputable def ep197 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 13) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 12) (@HPow.hPow Complex Complex Complex qz14 qz838 qz15)) Bool.true 58560285285 137438953472 19878874200417 6541578789191680 Bool.true 102326433513 1099511627776 636203435210409 209330521254133760

noncomputable def ep198 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 12) (@HPow.hPow Complex Complex Complex qz14 qz838 qz15) Bool.true 387518729121 549755813888 298097708168383 104665260627066880 Bool.true 20064286005 1099511627776 596415948991901 209330521254133760 Bool.false

noncomputable abbrev qz839 := (@Nat.cast Complex Complex.instNatCast 11)

noncomputable def ep199 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 12) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 11) (@HPow.hPow Complex Complex Complex qz14 qz839 qz15)) Bool.true 387518729121 549755813888 298097708168383 104665260627066880 Bool.true 20064286005 1099511627776 596415948991901 209330521254133760

noncomputable def ep200 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 11) (@HPow.hPow Complex Complex Complex qz14 qz839 qz15) Bool.true 625494248771 1099511627776 554602697241883 209330521254133760 Bool.false 275804919305 1099511627776 554735114578623 209330521254133760 Bool.true

noncomputable abbrev qz840 := (@Nat.cast Complex Complex.instNatCast 10)

noncomputable def ep201 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 11) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 10) (@HPow.hPow Complex Complex Complex qz14 qz840 qz15)) Bool.true 625494248771 1099511627776 554602697241883 209330521254133760 Bool.false 275804919305 1099511627776 554735114578623 209330521254133760

noncomputable def ep202 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 10) (@HPow.hPow Complex Complex Complex qz14 qz840 qz15) Bool.true 149756375175 549755813888 19649502969853 8051173894389760 Bool.false 49594208125 137438953472 9829561847529 4025586947194880 Bool.true

noncomputable abbrev qz841 := (@Nat.cast Complex Complex.instNatCast 9)

noncomputable def ep203 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 10) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 9) (@HPow.hPow Complex Complex Complex qz14 qz841 qz15)) Bool.true 149756375175 549755813888 19649502969853 8051173894389760 Bool.false 49594208125 137438953472 9829561847529 4025586947194880

noncomputable def ep204 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 9) (@HPow.hPow Complex Complex Complex qz14 qz841 qz15) Bool.true 3670267425 68719476736 116218243224273 52332630313533440 Bool.false 336530433525 549755813888 232551882414361 104665260627066880 Bool.true

noncomputable abbrev qz290 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 9)))

noncomputable abbrev qz291 := (Real.log (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz571 := (@HMul.hMul Real Real Real qz0 qz9 qz291)

noncomputable def ep205 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz14 qz841 qz15) (Complex.mk (@HMul.hMul Real Real Real qz0 qz290 (Real.cos qz571)) (@HMul.hMul Real Real Real qz0 qz290 (@Neg.neg Real Real.instNeg (Real.sin qz571)))) Bool.true 120394235775 549755813888 23007052159543 104665260627066880 Bool.true 138153601025 549755813888 23016725621393 104665260627066880 (BSN.cpow_neg_s_mk qz9 124004 1000 9 (@Eq.refl Real qz9) rfl)

noncomputable abbrev qz842 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9) qz265)

noncomputable def ep206 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 9)) 3145729 1048576 1 1048576 174762 174763 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 9)) (Real.sqrt qz842) Bool.false 3145729 1048576 1 1048576 (BSN.sqrt_natCast_div_one 9) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz842) Bool.false 3145729 1048576 1 1048576 3145729 1048576 1 1048576 (BSN.sqrt_enclosure 9 1 1572864 1572865 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep207 := BSN.log_dyadic_bound 1 17 3 2 1252815 524288 190385 1448 3 61752 18 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 1) (BSN.artanhQ 17) 0 2 1448 1252815 3 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep208 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz291 124004 1000 0 1 9895417793173221 4503599627370496 200000000114231 38077000000000000000 306767847006163024221 1125899906842624000 213800000122112939 328250000000000000000 qz270 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 200000000114231 38077000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz842) Bool.false 41504390431577613533184 18889465931478580854784 1000000000571155 190385000000000000000 9895417793173221 4503599627370496 200000000114231 38077000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 61752 524288 24973259072661432 36028797018963968 190385 1000000000000000 rfl rfl rfl rfl (ep207 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep209 := nat_lit 5615035888866172035551854686004560961

noncomputable def ep210 := BSN.sin_dyadic_bound_f 1539352687 2147483648 2 1 1048576 381142 ep209 ep123 ep209 ep209 ep124 ep209 688902 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1539352687) qz272 0 1 ep209 ep123 ep209 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1539352687) qz273 0 1 ep209 ep124 ep209 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz843 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 285699821) qz268)

noncomputable def ep211 := @Enclosure.Real.IsNear.cos_image qz571 qz843 Bool.false 285699821 1048576 171 262144 Bool.true 688902 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz571 Bool.false 306767847006163024221 1125899906842624000 213800000122112939 328250000000000000000 285699821 1048576 171 262144 (ep208 rfl) rfl) (Enclosure.sfrac_false_div 285699821 1048576) (BSN.cos_reduce1 qz843 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 108322315460447748227072) qz271) 226375608064910080 72057594037927936 Bool.false 688902 1048576 43 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q1 285699821 1048576 226375608064910080 72057594037927936 43 108322315460447748227072 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 688902 1048576 108322315460447748227072 151115727451828646838272 1539352687 2147483648 381142 380770 (ep210 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep212 := nat_lit 200654787402019898270171806043782578192536225738773608878066905265190875011201

noncomputable def ep213 := nat_lit 31528628033255122674361605888925205673503793504207043841401047294365243521

noncomputable def ep214 := nat_lit 601901304949993184565166694919569884166261669629312412546517913700983894546561

noncomputable def ep215 := BSN.cos_dyadic_bound_f 1539352687 2147483648 3 2 1048576 381142 ep212 ep88 ep213 ep214 ep91 ep213 790522 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1539352687) qz266 0 2 ep212 ep88 ep213 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1539352687) qz267 0 2 ep214 ep91 ep213 rfl rfl rfl rfl) rfl rfl

noncomputable def ep216 := @Enclosure.Real.IsNear.sin_image qz571 qz843 Bool.false 285699821 1048576 171 262144 Bool.false 790522 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz571 Bool.false 306767847006163024221 1125899906842624000 213800000122112939 328250000000000000000 285699821 1048576 171 262144 (ep208 rfl) rfl) (Enclosure.sfrac_false_div 285699821 1048576) (BSN.sin_reduce1 qz843 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 108322315460447748227072) qz271) 226375608064910080 72057594037927936 Bool.false 790522 1048576 43 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q1 285699821 1048576 226375608064910080 72057594037927936 43 108322315460447748227072 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 790522 1048576 108322315460447748227072 151115727451828646838272 1539352687 2147483648 381142 380770 (ep215 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz572 := (@Enclosure.Real.IsNear.recentre' qz290 Bool.false 349525 1048576 1 1048576 349525 1048576 1 1048576 (ep206 rfl rfl) rfl)

noncomputable def ep217 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz290 (Real.cos qz571)) (@HMul.hMul Real Real Real qz0 qz290 (@Neg.neg Real Real.instNeg (Real.sin qz571))) Bool.true 120394235775 549755813888 23007052159543 104665260627066880 Bool.true 138153601025 549755813888 23016725621393 104665260627066880 (@Enclosure.Real.IsNear.mulLit_ft qz290 (Real.cos qz571) 349525 1048576 1 1048576 344451 524288 32817979 49908285440 120394235775 549755813888 23007052159543 104665260627066880 qz572 (@Enclosure.Real.IsNear.recentre' (Real.cos qz571) Bool.true 688902 1048576 32817979 49908285440 344451 524288 32817979 49908285440 (ep211 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz290 (@Neg.neg Real Real.instNeg (Real.sin qz571)) 349525 1048576 1 1048576 395261 524288 32817979 49908285440 138153601025 549755813888 23016725621393 104665260627066880 qz572 (@Enclosure.Real.IsNear.neg (Real.sin qz571) Bool.false 395261 524288 32817979 49908285440 (@Enclosure.Real.IsNear.recentre' (Real.sin qz571) Bool.false 790522 1048576 32817979 49908285440 395261 524288 32817979 49908285440 (ep216 rfl rfl) rfl)) rfl)

noncomputable def ep218 := @ep204 120394235775 549755813888 23007052159543 104665260627066880 Bool.true 138153601025 549755813888 23016725621393 104665260627066880 Bool.true 10291179739906100428800 149756375175 549755813888 19649502969853 8051173894389760 Bool.false 109058817007560949760000 49594208125 137438953472 9829561847529 4025586947194880 EMRow41.d7 (ep205 ep217) rfl rfl

noncomputable abbrev qz844 := (@Nat.cast Real Real.instNatCast 10)

noncomputable abbrev qz292 := (@Inv.inv Real Real.instInv (Real.sqrt qz844))

noncomputable abbrev qz293 := (@HMul.hMul Real Real Real qz0 qz9 (Real.log (Enclosure.sfrac Bool.false 10 1)))

noncomputable def ep219 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz14 qz840 qz15) (Complex.mk (@HMul.hMul Real Real Real qz0 qz292 (Real.cos qz293)) (@HMul.hMul Real Real Real qz0 qz292 (@Neg.neg Real Real.instNeg (Real.sin qz293)))) Bool.true 325981498421 1099511627776 8743124005141 41866104250826752 Bool.true 120948745695 1099511627776 8719579701423 41866104250826752 (BSN.cpow_neg_s_mk qz9 124004 1000 10 (@Eq.refl Real qz9) rfl)

noncomputable abbrev qz845 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 10) qz265)

noncomputable def ep220 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz844) 3315889 1048576 1 1048576 165794 165795 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz844) (Real.sqrt qz845) Bool.false 3315889 1048576 1 1048576 (BSN.sqrt_natCast_div_one 10) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz845) Bool.false 3315889 1048576 1 1048576 3315889 1048576 1 1048576 (BSN.sqrt_enclosure 10 1 1657944 1657945 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep221 := BSN.log_dyadic_bound 2 18 3 2 1574640 524288 190385 6528 48 116991 20 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 2) (BSN.artanhQ 18) 0 2 6528 1574640 48 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz294 := (Real.log (Enclosure.sfrac Bool.false 10 1))

noncomputable def ep222 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz294 124004 1000 0 1 10369917190100709 4503599627370496 200000000114231 38077000000000000000 321477802810312079709 1125899906842624000 213800000122112939 328250000000000000000 qz270 (BSN.isNear_log_sfrac 10 1 10369917190100709 4503599627370496 200000000114231 38077000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz845) Bool.false 43494585150108164161536 18889465931478580854784 1000000000571155 190385000000000000000 10369917190100709 4503599627370496 200000000114231 38077000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 116991 524288 24973259072661432 36028797018963968 190385 1000000000000000 rfl rfl rfl rfl (ep221 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep223 := nat_lit 2987922600013329927659209709388300386092699795626363042192962777142989184467200

noncomputable def ep224 := nat_lit 2155308362436974912069601155635217529764173413930986949661411932076904448256

noncomputable def ep225 := nat_lit 7822022024590966136868865122717377325670786041113157798301164987484466209259776

noncomputable def ep226 := BSN.sin_dyadic_bound_f 2610289502 2147483648 3 2 1048576 381142 ep223 ep95 ep224 ep225 ep97 ep224 983089 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2610289502) qz272 0 2 ep223 ep95 ep224 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2610289502) qz273 0 2 ep225 ep97 ep224 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz846 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 149699767) qz280)

noncomputable def ep227 := @Enclosure.Real.IsNear.cos_image qz293 qz846 Bool.false 149699767 524288 171 262144 Bool.true 983089 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz293 Bool.false 321477802810312079709 1125899906842624000 213800000122112939 328250000000000000000 149699767 524288 171 262144 (ep222 rfl) rfl) (Enclosure.sfrac_false_div 149699767 524288) (BSN.cos_reduce1 qz846 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 91841397111263103811584) qz281) 226375608064910080 72057594037927936 Bool.false 983089 1048576 45 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q1 149699767 524288 226375608064910080 72057594037927936 45 91841397111263103811584 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 983089 1048576 91841397111263103811584 75557863725914323419136 2610289502 2147483648 381142 380770 (ep226 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep228 := nat_lit 1660914914835155281993814105729338088953617296865282128751495503715917060014336

noncomputable def ep229 := nat_lit 4978434127780591896157303114876743831801323543767984412355163687283597371146496

noncomputable def ep230 := BSN.cos_dyadic_bound_f 2610289502 2147483648 3 2 1048576 381142 ep228 ep88 ep224 ep229 ep91 ep224 364755 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2610289502) qz266 0 2 ep228 ep88 ep224 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2610289502) qz267 0 2 ep229 ep91 ep224 rfl rfl rfl rfl) rfl rfl

noncomputable def ep231 := @Enclosure.Real.IsNear.sin_image qz293 qz846 Bool.false 149699767 524288 171 262144 Bool.false 364755 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz293 Bool.false 321477802810312079709 1125899906842624000 213800000122112939 328250000000000000000 149699767 524288 171 262144 (ep222 rfl) rfl) (Enclosure.sfrac_false_div 149699767 524288) (BSN.sin_reduce1 qz846 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 91841397111263103811584) qz281) 226375608064910080 72057594037927936 Bool.false 364755 1048576 45 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q1 149699767 524288 226375608064910080 72057594037927936 45 91841397111263103811584 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 364755 1048576 91841397111263103811584 75557863725914323419136 2610289502 2147483648 381142 380770 (ep230 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz573 := (@Enclosure.Real.IsNear.recentre' qz292 Bool.false 331589 1048576 1 1048576 331589 1048576 1 1048576 (ep220 rfl rfl) rfl)

noncomputable def ep232 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz292 (Real.cos qz293)) (@HMul.hMul Real Real Real qz0 qz292 (@Neg.neg Real Real.instNeg (Real.sin qz293))) Bool.true 325981498421 1099511627776 8743124005141 41866104250826752 Bool.true 120948745695 1099511627776 8719579701423 41866104250826752 (@Enclosure.Real.IsNear.mulLit_ft qz292 (Real.cos qz293) 331589 1048576 1 1048576 983089 1048576 32817979 49908285440 325981498421 1099511627776 8743124005141 41866104250826752 qz573 (@Enclosure.Real.IsNear.recentre' (Real.cos qz293) Bool.true 983089 1048576 32817979 49908285440 983089 1048576 32817979 49908285440 (ep227 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz292 (@Neg.neg Real Real.instNeg (Real.sin qz293)) 331589 1048576 1 1048576 364755 1048576 32817979 49908285440 120948745695 1099511627776 8719579701423 41866104250826752 qz573 (@Enclosure.Real.IsNear.neg (Real.sin qz293) Bool.false 364755 1048576 32817979 49908285440 (@Enclosure.Real.IsNear.recentre' (Real.sin qz293) Bool.false 364755 1048576 32817979 49908285440 364755 1048576 32817979 49908285440 (ep231 rfl rfl) rfl)) rfl)

noncomputable def ep233 := @ep202 325981498421 1099511627776 8743124005141 41866104250826752 Bool.true 120948745695 1099511627776 8719579701423 41866104250826752 Bool.true 343869099815364248731648 625494248771 1099511627776 554602697241883 209330521254133760 Bool.false 37906339471708609576960 275804919305 1099511627776 554735114578623 209330521254133760 (ep203 (BSN.head_sum_c_succ qz12 9 10 rfl rfl) (ep218 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep219 ep232) rfl rfl

noncomputable abbrev qz847 := (@Nat.cast Real Real.instNatCast 11)

noncomputable abbrev qz295 := (@Inv.inv Real Real.instInv (Real.sqrt qz847))

noncomputable abbrev qz296 := (@HMul.hMul Real Real Real qz0 qz9 (Real.log (Enclosure.sfrac Bool.false 11 1)))

noncomputable def ep234 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz14 qz839 qz15) (Complex.mk (@HMul.hMul Real Real Real qz0 qz295 (Real.cos qz296)) (@HMul.hMul Real Real Real qz0 qz295 (@Neg.neg Real Real.instNeg (Real.sin qz296)))) Bool.true 149543209471 1099511627776 1434231692927 7218293836349440 Bool.true 147934602655 549755813888 718635076091 3609146918174720 (BSN.cpow_neg_s_mk qz9 124004 1000 11 (@Eq.refl Real qz9) rfl)

noncomputable abbrev qz848 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11) qz265)

noncomputable def ep235 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz847) 3477733 1048576 1 1048576 158078 158079 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz847) (Real.sqrt qz848) Bool.false 3477733 1048576 1 1048576 (BSN.sqrt_natCast_div_one 11) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz848) Bool.false 3477733 1048576 1 1048576 3477733 1048576 1 1048576 (BSN.sqrt_enclosure 11 1 1738866 1738867 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep236 := BSN.log_dyadic_bound 3 19 4 3 4939817505 524288 190385 41676111 10935 166961 22 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 3) (BSN.artanhQ 19) 0 3 41676111 4939817505 10935 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz297 := (Real.log (Enclosure.sfrac Bool.false 11 1))

noncomputable def ep237 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz297 124004 1000 0 1 10799156221662949 4503599627370496 200000000114231 38077000000000000000 334784642027773081949 1125899906842624000 213800000122112939 328250000000000000000 qz270 (BSN.isNear_log_sfrac 11 1 10799156221662949 4503599627370496 200000000114231 38077000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz848) Bool.false 45294944137145793642496 18889465931478580854784 1000000000571155 190385000000000000000 10799156221662949 4503599627370496 200000000114231 38077000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 166961 524288 24973259072661432 36028797018963968 190385 1000000000000000 rfl rfl rfl rfl (ep236 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep238 := nat_lit 1020134961943742801308683965576273041

noncomputable def ep239 := BSN.sin_dyadic_bound_f 1004996173 2147483648 2 1 1048576 381142 ep238 ep123 ep238 ep238 ep124 ep238 473003 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1004996173) qz272 0 1 ep238 ep123 ep238 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1004996173) qz273 0 1 ep238 ep124 ep238 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz849 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 155896247) qz280)

noncomputable def ep240 := @Enclosure.Real.IsNear.cos_image qz296 qz849 Bool.false 155896247 524288 171 262144 Bool.true 473003 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz296 Bool.false 334784642027773081949 1125899906842624000 213800000122112939 328250000000000000000 155896247 524288 171 262144 (ep237 rfl) rfl) (Enclosure.sfrac_false_div 155896247 524288) (BSN.cos_reduce1 qz849 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 35360159310457889357824) qz281) 226375608064910080 72057594037927936 Bool.false 473003 1048576 47 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q1 155896247 524288 226375608064910080 72057594037927936 47 35360159310457889357824 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 473003 1048576 35360159310457889357824 75557863725914323419136 1004996173 2147483648 381142 380770 (ep239 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep241 := BSN.cos_dyadic_bound_f 1004996173 2147483648 2 1 1048576 381142 ep238 ep143 ep238 ep238 ep144 ep238 935830 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1004996173) qz266 0 1 ep238 ep143 ep238 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1004996173) qz267 0 1 ep238 ep144 ep238 rfl rfl rfl rfl) rfl rfl

noncomputable def ep242 := @Enclosure.Real.IsNear.sin_image qz296 qz849 Bool.false 155896247 524288 171 262144 Bool.false 935830 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz296 Bool.false 334784642027773081949 1125899906842624000 213800000122112939 328250000000000000000 155896247 524288 171 262144 (ep237 rfl) rfl) (Enclosure.sfrac_false_div 155896247 524288) (BSN.sin_reduce1 qz849 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 35360159310457889357824) qz281) 226375608064910080 72057594037927936 Bool.false 935830 1048576 47 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q1 155896247 524288 226375608064910080 72057594037927936 47 35360159310457889357824 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 935830 1048576 35360159310457889357824 75557863725914323419136 1004996173 2147483648 381142 380770 (ep241 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz574 := (@Enclosure.Real.IsNear.recentre' qz295 Bool.false 316157 1048576 1 1048576 316157 1048576 1 1048576 (ep235 rfl rfl) rfl)

noncomputable def ep243 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz295 (Real.cos qz296)) (@HMul.hMul Real Real Real qz0 qz295 (@Neg.neg Real Real.instNeg (Real.sin qz296))) Bool.true 149543209471 1099511627776 1434231692927 7218293836349440 Bool.true 147934602655 549755813888 718635076091 3609146918174720 (@Enclosure.Real.IsNear.mulLit_ft qz295 (Real.cos qz296) 316157 1048576 1 1048576 473003 1048576 32817979 49908285440 149543209471 1099511627776 1434231692927 7218293836349440 qz574 (@Enclosure.Real.IsNear.recentre' (Real.cos qz296) Bool.true 473003 1048576 32817979 49908285440 473003 1048576 32817979 49908285440 (ep240 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz295 (@Neg.neg Real Real.instNeg (Real.sin qz296)) 316157 1048576 1 1048576 467915 524288 32817979 49908285440 147934602655 549755813888 718635076091 3609146918174720 qz574 (@Enclosure.Real.IsNear.neg (Real.sin qz296) Bool.false 467915 524288 32817979 49908285440 (@Enclosure.Real.IsNear.recentre' (Real.sin qz296) Bool.false 935830 1048576 32817979 49908285440 467915 524288 32817979 49908285440 (ep242 rfl rfl) rfl)) rfl)

noncomputable def ep244 := @ep200 149543209471 1099511627776 1434231692927 7218293836349440 Bool.true 147934602655 549755813888 718635076091 3609146918174720 Bool.true 852162697299035047329792 387518729121 549755813888 298097708168383 104665260627066880 Bool.true 11030457882760383037440 20064286005 1099511627776 596415948991901 209330521254133760 (ep201 (BSN.head_sum_c_succ qz12 10 11 rfl rfl) (ep233 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep234 ep243) rfl rfl

noncomputable abbrev qz850 := (@Nat.cast Real Real.instNatCast 12)

noncomputable abbrev qz298 := (@Inv.inv Real Real.instInv (Real.sqrt qz850))

noncomputable abbrev qz299 := (@HMul.hMul Real Real Real qz0 qz9 (Real.log (Enclosure.sfrac Bool.false 12 1)))

noncomputable def ep245 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz14 qz838 qz15) (Complex.mk (@HMul.hMul Real Real Real qz0 qz298 (Real.cos qz299)) (@HMul.hMul Real Real Real qz0 qz298 (@Neg.neg Real Real.instNeg (Real.sin qz299)))) Bool.false 153277587981 549755813888 19964279038289 104665260627066880 Bool.true 20565536877 274877906944 9946871554627 52332630313533440 (BSN.cpow_neg_s_mk qz9 124004 1000 12 (@Eq.refl Real qz9) rfl)

noncomputable abbrev qz851 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 12) qz265)

noncomputable def ep246 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz850) 3632373 1048576 1 1048576 151348 151349 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz850) (Real.sqrt qz851) Bool.false 3632373 1048576 1 1048576 (BSN.sqrt_natCast_div_one 12) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz851) Bool.false 3632373 1048576 1 1048576 3632373 1048576 1 1048576 (BSN.sqrt_enclosure 12 1 1816186 1816187 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep247 := BSN.log_dyadic_bound 4 20 4 3 6720000000 524288 190385 91811840 61440 212580 24 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 4) (BSN.artanhQ 20) 0 3 91811840 6720000000 61440 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz300 := (Real.log (Enclosure.sfrac Bool.false 12 1))

noncomputable def ep248 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz300 124004 1000 0 1 11191020447815397 4503599627370496 200000000114231 38077000000000000000 346932824902725122397 1125899906842624000 213800000122112939 328250000000000000000 qz270 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 200000000114231 38077000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz851) Bool.false 46938541828353910898688 18889465931478580854784 1000000000571155 190385000000000000000 11191020447815397 4503599627370496 200000000114231 38077000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 212580 524288 24973259072661432 36028797018963968 190385 1000000000000000 rfl rfl rfl rfl (ep247 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep249 := nat_lit 100469551112013328830626520002585616

noncomputable def ep250 := BSN.cos_dyadic_bound_f 563000286 2147483648 2 1 1048576 381142 ep249 ep143 ep249 ep249 ep144 ep249 1012746 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 563000286) qz266 0 1 ep249 ep143 ep249 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 563000286) qz267 0 1 ep249 ep144 ep249 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz852 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 323106371) qz268)

noncomputable def ep251 := @Enclosure.Real.IsNear.cos_image qz299 qz852 Bool.false 323106371 1048576 171 262144 Bool.false 1012746 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz299 Bool.false 346932824902725122397 1125899906842624000 213800000122112939 328250000000000000000 323106371 1048576 171 262144 (ep248 rfl) rfl) (Enclosure.sfrac_false_div 323106371 1048576) (BSN.cos_reduce0 qz852 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 39617623127117719928832) qz271) 226375608064910080 72057594037927936 Bool.false 1012746 1048576 49 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q0 323106371 1048576 226375608064910080 72057594037927936 49 39617623127117719928832 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1012746 1048576 39617623127117719928832 151115727451828646838272 563000286 2147483648 381142 380770 (ep250 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep252 := BSN.sin_dyadic_bound_f 563000286 2147483648 2 1 1048576 381142 ep249 ep123 ep249 ep249 ep124 ep249 271764 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 563000286) qz272 0 1 ep249 ep123 ep249 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 563000286) qz273 0 1 ep249 ep124 ep249 rfl rfl rfl rfl) rfl rfl

noncomputable def ep253 := @Enclosure.Real.IsNear.sin_image qz299 qz852 Bool.false 323106371 1048576 171 262144 Bool.false 271764 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz299 Bool.false 346932824902725122397 1125899906842624000 213800000122112939 328250000000000000000 323106371 1048576 171 262144 (ep248 rfl) rfl) (Enclosure.sfrac_false_div 323106371 1048576) (BSN.sin_reduce0 qz852 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 39617623127117719928832) qz271) 226375608064910080 72057594037927936 Bool.false 271764 1048576 49 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q0 323106371 1048576 226375608064910080 72057594037927936 49 39617623127117719928832 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 271764 1048576 39617623127117719928832 151115727451828646838272 563000286 2147483648 381142 380770 (ep252 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz575 := (@Enclosure.Real.IsNear.recentre' qz298 Bool.false 302697 1048576 1 1048576 302697 1048576 1 1048576 (ep246 rfl rfl) rfl)

noncomputable def ep254 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz298 (Real.cos qz299)) (@HMul.hMul Real Real Real qz0 qz298 (@Neg.neg Real Real.instNeg (Real.sin qz299))) Bool.false 153277587981 549755813888 19964279038289 104665260627066880 Bool.true 20565536877 274877906944 9946871554627 52332630313533440 (@Enclosure.Real.IsNear.mulLit_ff qz298 (Real.cos qz299) 302697 1048576 1 1048576 506373 524288 32817979 49908285440 153277587981 549755813888 19964279038289 104665260627066880 qz575 (@Enclosure.Real.IsNear.recentre' (Real.cos qz299) Bool.false 1012746 1048576 32817979 49908285440 506373 524288 32817979 49908285440 (ep251 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz298 (@Neg.neg Real Real.instNeg (Real.sin qz299)) 302697 1048576 1 1048576 67941 262144 32817979 49908285440 20565536877 274877906944 9946871554627 52332630313533440 qz575 (@Enclosure.Real.IsNear.neg (Real.sin qz299) Bool.false 67941 262144 32817979 49908285440 (@Enclosure.Real.IsNear.recentre' (Real.sin qz299) Bool.false 271764 1048576 32817979 49908285440 67941 262144 32817979 49908285440 (ep253 rfl rfl) rfl)) rfl)

noncomputable def ep255 := @ep198 153277587981 549755813888 19964279038289 104665260627066880 Bool.true 20565536877 274877906944 9946871554627 52332630313533440 Bool.true 128775429193474580152320 58560285285 137438953472 19878874200417 6541578789191680 Bool.true 28127275869097817014272 102326433513 1099511627776 636203435210409 209330521254133760 (ep199 (BSN.head_sum_c_succ qz12 11 12 rfl rfl) (ep244 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep245 ep254) rfl rfl

noncomputable abbrev qz853 := (@Nat.cast Real Real.instNatCast 13)

noncomputable abbrev qz301 := (@Inv.inv Real Real.instInv (Real.sqrt qz853))

noncomputable abbrev qz302 := (@HMul.hMul Real Real Real qz0 qz9 (Real.log (Enclosure.sfrac Bool.false 13 1)))

noncomputable def ep256 := @Enclosure.Complex.IsNear.of_eq qz837 (Complex.mk (@HMul.hMul Real Real Real qz0 qz301 (Real.cos qz302)) (@HMul.hMul Real Real Real qz0 qz301 (@Neg.neg Real Real.instNeg (Real.sin qz302)))) Bool.true 27553443489 137438953472 4790165608403 26166315156766720 Bool.false 105363718785 549755813888 19157487382967 104665260627066880 (BSN.cpow_neg_s_mk qz9 124004 1000 13 (@Eq.refl Real qz9) rfl)

noncomputable abbrev qz854 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13) qz265)

noncomputable def ep257 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz853) 3780695 1048576 1 1048576 145411 145412 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz853) (Real.sqrt qz854) Bool.false 3780695 1048576 1 1048576 (BSN.sqrt_natCast_div_one 13) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz854) Bool.false 3780695 1048576 1 1048576 3780695 1048576 1 1048576 (BSN.sqrt_enclosure 13 1 1890347 1890348 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep258 := BSN.log_dyadic_bound 5 21 5 4 35742602096145 524288 190385 699352521000 41015625 254545 26 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 5) (BSN.artanhQ 21) 0 4 699352521000 35742602096145 41015625 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz303 := (Real.log (Enclosure.sfrac Bool.false 13 1))

noncomputable def ep259 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz303 124004 1000 0 1 11551497052968677 4503599627370496 200000000114231 38077000000000000000 358107960139081955677 1125899906842624000 213800000122112939 328250000000000000000 qz270 (BSN.isNear_log_sfrac 13 1 11551497052968677 4503599627370496 200000000114231 38077000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz854) Bool.false 48450490295254733815808 18889465931478580854784 1000000000571155 190385000000000000000 11551497052968677 4503599627370496 200000000114231 38077000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 254545 524288 24973259072661432 36028797018963968 190385 1000000000000000 rfl rfl rfl rfl (ep258 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep260 := nat_lit 257462894839101251909151059829600188225870478962293661646304710097539239918721

noncomputable def ep261 := nat_lit 51903504974906991762335746016463418828386091701983353845636856392016346241

noncomputable def ep262 := nat_lit 772284877507353941743928507996767637839954664703477018231222856579833687063681

noncomputable def ep263 := BSN.cos_dyadic_bound_f 1638323217 2147483648 3 2 1048576 381142 ep260 ep88 ep261 ep262 ep91 ep261 757944 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1638323217) qz266 0 2 ep260 ep88 ep261 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1638323217) qz267 0 2 ep262 ep91 ep261 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz855 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 333514027) qz268)

noncomputable def ep264 := @Enclosure.Real.IsNear.cos_image qz302 qz855 Bool.false 333514027 1048576 171 262144 Bool.true 757944 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz302 Bool.false 358107960139081955677 1125899906842624000 213800000122112939 328250000000000000000 333514027 1048576 171 262144 (ep259 rfl) rfl) (Enclosure.sfrac_false_div 333514027 1048576) (BSN.cos_reduce2 qz855 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 115286747382300629008384) qz271) 226375608064910080 72057594037927936 Bool.false 757944 1048576 50 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q2 333514027 1048576 226375608064910080 72057594037927936 50 115286747382300629008384 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 757944 1048576 115286747382300629008384 151115727451828646838272 1638323217 2147483648 381142 380770 (ep263 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep265 := nat_lit 7204408717924531505343867868739769921

noncomputable def ep266 := BSN.sin_dyadic_bound_f 1638323217 2147483648 2 1 1048576 381142 ep265 ep123 ep265 ep265 ep124 ep265 724590 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1638323217) qz272 0 1 ep265 ep123 ep265 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1638323217) qz273 0 1 ep265 ep124 ep265 rfl rfl rfl rfl) rfl rfl

noncomputable def ep267 := @Enclosure.Real.IsNear.sin_image qz302 qz855 Bool.false 333514027 1048576 171 262144 Bool.true 724590 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz302 Bool.false 358107960139081955677 1125899906842624000 213800000122112939 328250000000000000000 333514027 1048576 171 262144 (ep259 rfl) rfl) (Enclosure.sfrac_false_div 333514027 1048576) (BSN.sin_reduce2 qz855 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 115286747382300629008384) qz271) 226375608064910080 72057594037927936 Bool.false 724590 1048576 50 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q2 333514027 1048576 226375608064910080 72057594037927936 50 115286747382300629008384 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 724590 1048576 115286747382300629008384 151115727451828646838272 1638323217 2147483648 381142 380770 (ep266 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz576 := (@Enclosure.Real.IsNear.recentre' qz301 Bool.false 290823 1048576 1 1048576 290823 1048576 1 1048576 (ep257 rfl rfl) rfl)

noncomputable def ep268 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz301 (Real.cos qz302)) (@HMul.hMul Real Real Real qz0 qz301 (@Neg.neg Real Real.instNeg (Real.sin qz302))) Bool.true 27553443489 137438953472 4790165608403 26166315156766720 Bool.false 105363718785 549755813888 19157487382967 104665260627066880 (@Enclosure.Real.IsNear.mulLit_ft qz301 (Real.cos qz302) 290823 1048576 1 1048576 94743 131072 32817979 49908285440 27553443489 137438953472 4790165608403 26166315156766720 qz576 (@Enclosure.Real.IsNear.recentre' (Real.cos qz302) Bool.true 757944 1048576 32817979 49908285440 94743 131072 32817979 49908285440 (ep264 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz301 (@Neg.neg Real Real.instNeg (Real.sin qz302)) 290823 1048576 1 1048576 362295 524288 32817979 49908285440 105363718785 549755813888 19157487382967 104665260627066880 qz576 (@Enclosure.Real.IsNear.neg (Real.sin qz302) Bool.true 362295 524288 32817979 49908285440 (@Enclosure.Real.IsNear.recentre' (Real.sin qz302) Bool.true 724590 1048576 32817979 49908285440 362295 524288 32817979 49908285440 (ep267 rfl rfl) rfl)) rfl)

noncomputable def ep269 := @ep196 27553443489 137438953472 4790165608403 26166315156766720 Bool.false 105363718785 549755813888 19157487382967 104665260627066880 Bool.true 11835380762270213603328 43056864387 68719476736 84305662410071 26166315156766720 Bool.false 59594082211632424943616 108401004057 1099511627776 674518409976343 209330521254133760 (ep197 (BSN.head_sum_c_succ qz12 12 13 rfl rfl) (ep255 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep256 ep268) rfl rfl

noncomputable abbrev qz856 := (@Nat.cast Real Real.instNatCast 14)

noncomputable abbrev qz304 := (@Inv.inv Real Real.instInv (Real.sqrt qz856))

noncomputable abbrev qz305 := (@HMul.hMul Real Real Real qz0 qz9 (Real.log (Enclosure.sfrac Bool.false 14 1)))

noncomputable def ep270 := @Enclosure.Complex.IsNear.of_eq qz836 (Complex.mk (@HMul.hMul Real Real Real qz0 qz304 (Real.cos qz305)) (@HMul.hMul Real Real Real qz0 qz304 (@Neg.neg Real Real.instNeg (Real.sin qz305)))) Bool.false 126931302719 549755813888 18480315062957 104665260627066880 Bool.true 148003334375 1099511627776 36888713905629 209330521254133760 (BSN.cpow_neg_s_mk qz9 124004 1000 14 (@Eq.refl Real qz9) rfl)

noncomputable abbrev qz857 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14) qz265)

noncomputable def ep271 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz856) 3923413 1048576 1 1048576 140121 140122 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz856) (Real.sqrt qz857) Bool.false 3923413 1048576 1 1048576 (BSN.sqrt_natCast_div_one 14) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz857) Bool.false 3923413 1048576 1 1048576 3923413 1048576 1 1048576 (BSN.sqrt_enclosure 14 1 1961706 1961707 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep272 := BSN.log_dyadic_bound 6 22 5 4 51857700491520 524288 190385 1346332575744 176359680 293399 28 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 6) (BSN.artanhQ 22) 0 4 1346332575744 51857700491520 176359680 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz306 := (Real.log (Enclosure.sfrac Bool.false 14 1))

noncomputable def ep273 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz306 124004 1000 0 1 11885250371606245 4503599627370496 200000000114231 38077000000000000000 73690929354033040249 225179981368524800 213800000122112939 328250000000000000000 qz270 (BSN.isNear_log_sfrac 14 1 11885250371606245 4503599627370496 200000000114231 38077000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz857) Bool.false 49850353174629559828480 18889465931478580854784 1000000000571155 190385000000000000000 11885250371606245 4503599627370496 200000000114231 38077000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 293399 524288 24973259072661432 36028797018963968 190385 1000000000000000 rfl rfl rfl rfl (ep272 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep274 := nat_lit 1650800859789553662075120171843993856

noncomputable def ep275 := BSN.cos_dyadic_bound_f 1133505604 2147483648 2 1 1048576 381142 ep274 ep143 ep274 ep274 ep144 ep274 905866 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1133505604) qz266 0 1 ep274 ep143 ep274 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1133505604) qz267 0 1 ep274 ep144 ep274 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz858 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 171575065) qz280)

noncomputable def ep276 := @Enclosure.Real.IsNear.cos_image qz305 qz858 Bool.false 171575065 524288 171 262144 Bool.false 905866 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz305 Bool.false 73690929354033040249 225179981368524800 213800000122112939 328250000000000000000 171575065 524288 171 262144 (ep273 rfl) rfl) (Enclosure.sfrac_false_div 171575065 524288) (BSN.cos_reduce0 qz858 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 39881682965996356239360) qz281) 226375608064910080 72057594037927936 Bool.false 905866 1048576 52 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q0 171575065 524288 226375608064910080 72057594037927936 52 39881682965996356239360 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 905866 1048576 39881682965996356239360 75557863725914323419136 1133505604 2147483648 381142 380770 (ep275 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep277 := BSN.sin_dyadic_bound_f 1133505604 2147483648 2 1 1048576 381142 ep274 ep123 ep274 ep274 ep124 ep274 528125 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1133505604) qz272 0 1 ep274 ep123 ep274 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1133505604) qz273 0 1 ep274 ep124 ep274 rfl rfl rfl rfl) rfl rfl

noncomputable def ep278 := @Enclosure.Real.IsNear.sin_image qz305 qz858 Bool.false 171575065 524288 171 262144 Bool.false 528125 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz305 Bool.false 73690929354033040249 225179981368524800 213800000122112939 328250000000000000000 171575065 524288 171 262144 (ep273 rfl) rfl) (Enclosure.sfrac_false_div 171575065 524288) (BSN.sin_reduce0 qz858 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 39881682965996356239360) qz281) 226375608064910080 72057594037927936 Bool.false 528125 1048576 52 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q0 171575065 524288 226375608064910080 72057594037927936 52 39881682965996356239360 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 528125 1048576 39881682965996356239360 75557863725914323419136 1133505604 2147483648 381142 380770 (ep277 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz577 := (@Enclosure.Real.IsNear.recentre' qz304 Bool.false 280243 1048576 1 1048576 280243 1048576 1 1048576 (ep271 rfl rfl) rfl)

noncomputable def ep279 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz304 (Real.cos qz305)) (@HMul.hMul Real Real Real qz0 qz304 (@Neg.neg Real Real.instNeg (Real.sin qz305))) Bool.false 126931302719 549755813888 18480315062957 104665260627066880 Bool.true 148003334375 1099511627776 36888713905629 209330521254133760 (@Enclosure.Real.IsNear.mulLit_ff qz304 (Real.cos qz305) 280243 1048576 1 1048576 452933 524288 32817979 49908285440 126931302719 549755813888 18480315062957 104665260627066880 qz577 (@Enclosure.Real.IsNear.recentre' (Real.cos qz305) Bool.false 905866 1048576 32817979 49908285440 452933 524288 32817979 49908285440 (ep276 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz304 (@Neg.neg Real Real.instNeg (Real.sin qz305)) 280243 1048576 1 1048576 528125 1048576 32817979 49908285440 148003334375 1099511627776 36888713905629 209330521254133760 qz577 (@Enclosure.Real.IsNear.neg (Real.sin qz305) Bool.false 528125 1048576 32817979 49908285440 (@Enclosure.Real.IsNear.recentre' (Real.sin qz305) Bool.false 528125 1048576 32817979 49908285440 528125 1048576 32817979 49908285440 (ep278 rfl rfl) rfl)) rfl)

noncomputable def ep280 := @ep194 126931302719 549755813888 18480315062957 104665260627066880 Bool.true 148003334375 1099511627776 36888713905629 209330521254133760 Bool.true 14948108820271933161472 217523612377 549755813888 355702964703241 104665260627066880 Bool.true 43543222671667015712768 19801165159 549755813888 177851780970493 52332630313533440 (ep195 (BSN.head_sum_c_succ qz12 13 14 rfl rfl) (ep269 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep270 ep279) rfl rfl

noncomputable abbrev qz859 := (@Nat.cast Real Real.instNatCast 15)

noncomputable abbrev qz307 := (@Inv.inv Real Real.instInv (Real.sqrt qz859))

noncomputable abbrev qz308 := (@HMul.hMul Real Real Real qz0 qz9 (Real.log (Enclosure.sfrac Bool.false 15 1)))

noncomputable def ep281 := @Enclosure.Complex.IsNear.of_eq qz835 (Complex.mk (@HMul.hMul Real Real Real qz0 qz307 (Real.cos qz308)) (@HMul.hMul Real Real Real qz0 qz307 (@Neg.neg Real Real.instNeg (Real.sin qz308)))) Bool.true 267490212813 1099511627776 35728920128977 209330521254133760 Bool.true 11887425087 137438953472 1112740467351 6541578789191680 (BSN.cpow_neg_s_mk qz9 124004 1000 15 (@Eq.refl Real qz9) rfl)

noncomputable abbrev qz860 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 15) qz265)

noncomputable def ep282 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz859) 4061117 1048576 1 1048576 135370 135371 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz859) (Real.sqrt qz860) Bool.false 4061117 1048576 1 1048576 (BSN.sqrt_natCast_div_one 15) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz860) Bool.false 4061117 1048576 1 1048576 4061117 1048576 1 1048576 (BSN.sqrt_enclosure 15 1 2030558 2030559 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep283 := BSN.log_dyadic_bound 7 23 6 5 430628584065881355 524288 190385 14087658153505881 266939110305 329571 30 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 7) (BSN.artanhQ 23) 0 5 14087658153505881 430628584065881355 266939110305 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz309 := (Real.log (Enclosure.sfrac Bool.false 15 1))

noncomputable def ep284 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz309 124004 1000 0 1 12195965485668069 4503599627370496 200000000114231 38077000000000000000 378087126021195807069 1125899906842624000 213800000122112939 328250000000000000000 qz270 (BSN.isNear_log_sfrac 15 1 12195965485668069 4503599627370496 200000000114231 38077000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz860) Bool.false 51153586820399524478976 18889465931478580854784 1000000000571155 190385000000000000000 12195965485668069 4503599627370496 200000000114231 38077000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 329571 524288 24973259072661432 36028797018963968 190385 1000000000000000 rfl rfl rfl rfl (ep283 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep285 := nat_lit 3124998476396702051596339673783912061938454200349627639423599315780217880715520

noncomputable def ep286 := nat_lit 2357445305894365074330006494258827771377927523341889261061295407861377802496

noncomputable def ep287 := nat_lit 8180703002924676401203402944633826822018482451592185520639137063049747456860416

noncomputable def ep288 := BSN.sin_dyadic_bound_f 2639703834 2147483648 3 2 1048576 381142 ep285 ep95 ep286 ep287 ep97 ep286 987993 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2639703834) qz272 0 2 ep285 ep95 ep286 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2639703834) qz273 0 2 ep287 ep97 ep286 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz861 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 352121075) qz268)

noncomputable def ep289 := @Enclosure.Real.IsNear.cos_image qz308 qz861 Bool.false 352121075 1048576 171 262144 Bool.true 987993 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz308 Bool.false 378087126021195807069 1125899906842624000 213800000122112939 328250000000000000000 352121075 1048576 171 262144 (ep284 rfl) rfl) (Enclosure.sfrac_false_div 352121075 1048576) (BSN.cos_reduce1 qz861 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 185752643813795807887360) qz271) 226375608064910080 72057594037927936 Bool.false 987993 1048576 53 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q1 352121075 1048576 226375608064910080 72057594037927936 53 185752643813795807887360 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 987993 1048576 185752643813795807887360 151115727451828646838272 2639703834 2147483648 381142 380770 (ep288 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep290 := nat_lit 1737158018134120857586557599432955068975309190204611750462471306725837212754176

noncomputable def ep291 := nat_lit 5206759163790573842611012785310347551383171715567151472865291329361788882657536

noncomputable def ep292 := BSN.cos_dyadic_bound_f 2639703834 2147483648 3 2 1048576 381142 ep290 ep88 ep286 ep291 ep91 ep286 351256 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2639703834) qz266 0 2 ep290 ep88 ep286 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2639703834) qz267 0 2 ep291 ep91 ep286 rfl rfl rfl rfl) rfl rfl

noncomputable def ep293 := @Enclosure.Real.IsNear.sin_image qz308 qz861 Bool.false 352121075 1048576 171 262144 Bool.false 351256 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz308 Bool.false 378087126021195807069 1125899906842624000 213800000122112939 328250000000000000000 352121075 1048576 171 262144 (ep284 rfl) rfl) (Enclosure.sfrac_false_div 352121075 1048576) (BSN.sin_reduce1 qz861 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 185752643813795807887360) qz271) 226375608064910080 72057594037927936 Bool.false 351256 1048576 53 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q1 352121075 1048576 226375608064910080 72057594037927936 53 185752643813795807887360 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 351256 1048576 185752643813795807887360 151115727451828646838272 2639703834 2147483648 381142 380770 (ep292 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz578 := (@Enclosure.Real.IsNear.recentre' qz307 Bool.false 270741 1048576 1 1048576 270741 1048576 1 1048576 (ep282 rfl rfl) rfl)

noncomputable def ep294 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz307 (Real.cos qz308)) (@HMul.hMul Real Real Real qz0 qz307 (@Neg.neg Real Real.instNeg (Real.sin qz308))) Bool.true 267490212813 1099511627776 35728920128977 209330521254133760 Bool.true 11887425087 137438953472 1112740467351 6541578789191680 (@Enclosure.Real.IsNear.mulLit_ft qz307 (Real.cos qz308) 270741 1048576 1 1048576 987993 1048576 32817979 49908285440 267490212813 1099511627776 35728920128977 209330521254133760 qz578 (@Enclosure.Real.IsNear.recentre' (Real.cos qz308) Bool.true 987993 1048576 32817979 49908285440 987993 1048576 32817979 49908285440 (ep289 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz307 (@Neg.neg Real Real.instNeg (Real.sin qz308)) 270741 1048576 1 1048576 43907 131072 32817979 49908285440 11887425087 137438953472 1112740467351 6541578789191680 qz578 (@Enclosure.Real.IsNear.neg (Real.sin qz308) Bool.false 43907 131072 32817979 49908285440 (@Enclosure.Real.IsNear.recentre' (Real.sin qz308) Bool.false 351256 1048576 32817979 49908285440 43907 131072 32817979 49908285440 (ep293 rfl rfl) rfl)) rfl)

noncomputable def ep295 := @ep192 267490212813 1099511627776 35728920128977 209330521254133760 Bool.true 11887425087 137438953472 1112740467351 6541578789191680 Bool.true 386224040776436071530496 702537437567 1099511627776 747134849535459 209330521254133760 Bool.true 9256632470715502690304 67350865507 549755813888 186753704709301 52332630313533440 (ep193 (BSN.head_sum_c_succ qz12 14 15 rfl rfl) (ep280 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep281 ep294) rfl rfl

noncomputable abbrev qz862 := (@Nat.cast Real Real.instNatCast 16)

noncomputable abbrev qz310 := (@Inv.inv Real Real.instInv (Real.sqrt qz862))

noncomputable abbrev qz311 := (@HMul.hMul Real Real Real qz0 qz9 (Real.log (Enclosure.sfrac Bool.false 16 1)))

noncomputable def ep296 := @Enclosure.Complex.IsNear.of_eq qz834 (Complex.mk (@HMul.hMul Real Real Real qz0 qz310 (Real.cos qz311)) (@HMul.hMul Real Real Real qz0 qz310 (@Neg.neg Real Real.instNeg (Real.sin qz311)))) Bool.true 13133626443 274877906944 8612574765861 52332630313533440 Bool.false 269809896321 1099511627776 34608098337999 209330521254133760 (BSN.cpow_neg_s_mk qz9 124004 1000 16 (@Eq.refl Real qz9) rfl)

noncomputable abbrev qz863 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16) qz265)

noncomputable def ep297 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz862) 4194305 1048576 1 1048576 131071 131072 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz862) (Real.sqrt qz863) Bool.false 4194305 1048576 1 1048576 (BSN.sqrt_natCast_div_one 16) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz863) Bool.false 4194305 1048576 1 1048576 4194305 1048576 1 1048576 (BSN.sqrt_enclosure 16 1 2097152 2097153 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep298 := BSN.log_dyadic_bound 0 32 1 0 1 524288 190385 0 1 0 32 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 32) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz312 := (Real.log (Enclosure.sfrac Bool.false 16 1))

noncomputable def ep299 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz312 124004 1000 0 1 3121657384082679 1125899906842624 50000000038077 9519250000000000000 96774500563947131679 281474976710656000 53450000040704313 82062500000000000000 qz270 (BSN.isNear_log_sfrac 16 1 3121657384082679 1125899906842624 50000000038077 9519250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz863) Bool.false 52372720210750067441664 18889465931478580854784 1000000000761540 190385000000000000000 3121657384082679 1125899906842624 50000000038077 9519250000000000000 (BSN.log_rat_reduce_isNear 16 1 4 32 32 0 524288 24973259072661432 36028797018963968 190385 1000000000000000 rfl rfl rfl rfl (ep298 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep300 := nat_lit 2749782836090496817484098208168439788213337602936825472733763023936288245353601

noncomputable def ep301 := nat_lit 5897587616252430792163514061340152746407674343685411911092037795818890529921

noncomputable def ep302 := nat_lit 8237553333038985590867967596382639059147197460123105594379104996217226955000961

noncomputable def ep303 := BSN.cos_dyadic_bound_f 2960290287 2147483648 3 2 1048576 381142 ep300 ep88 ep301 ep302 ep91 ep301 200404 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2960290287) qz266 0 2 ep300 ep88 ep301 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2960290287) qz267 0 2 ep302 ep91 ep301 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz313 := (@Nat.cast Real Real.instNatCast 262144)

noncomputable abbrev qz314 := (@Nat.cast Real Real.instNatCast 37778931862957161709568)

noncomputable abbrev qz864 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 90128277) qz313)

noncomputable def ep304 := @Enclosure.Real.IsNear.cos_image qz311 qz864 Bool.false 90128277 262144 171 262144 Bool.true 200404 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz311 Bool.false 96774500563947131679 281474976710656000 53450000040704313 82062500000000000000 90128277 262144 171 262144 (ep299 rfl) rfl) (Enclosure.sfrac_false_div 90128277 262144) (BSN.cos_reduce2 qz864 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 52077977484057257181184) qz314) 226375608064910080 72057594037927936 Bool.false 200404 1048576 54 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q2 90128277 262144 226375608064910080 72057594037927936 54 52077977484057257181184 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 200404 1048576 52077977484057257181184 37778931862957161709568 2960290287 2147483648 381142 380770 (ep303 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep305 := nat_lit 4944891034869892326837645963454119496586881545811337521391899812848663729212545

noncomputable def ep306 := nat_lit 12941356616137690253768427071994809862804791623425631412932255258172317277555841

noncomputable def ep307 := BSN.sin_dyadic_bound_f 2960290287 2147483648 3 2 1048576 381142 ep305 ep95 ep301 ep306 ep97 ep301 1029247 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2960290287) qz272 0 2 ep305 ep95 ep301 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2960290287) qz273 0 2 ep306 ep97 ep301 rfl rfl rfl rfl) rfl rfl

noncomputable def ep308 := @Enclosure.Real.IsNear.sin_image qz311 qz864 Bool.false 90128277 262144 171 262144 Bool.true 1029247 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz311 Bool.false 96774500563947131679 281474976710656000 53450000040704313 82062500000000000000 90128277 262144 171 262144 (ep299 rfl) rfl) (Enclosure.sfrac_false_div 90128277 262144) (BSN.sin_reduce2 qz864 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 52077977484057257181184) qz314) 226375608064910080 72057594037927936 Bool.false 1029247 1048576 54 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q2 90128277 262144 226375608064910080 72057594037927936 54 52077977484057257181184 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1029247 1048576 52077977484057257181184 37778931862957161709568 2960290287 2147483648 381142 380770 (ep307 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz579 := (@Enclosure.Real.IsNear.recentre' qz310 Bool.false 262143 1048576 1 1048576 262143 1048576 1 1048576 (ep297 rfl rfl) rfl)

noncomputable def ep309 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz310 (Real.cos qz311)) (@HMul.hMul Real Real Real qz0 qz310 (@Neg.neg Real Real.instNeg (Real.sin qz311))) Bool.true 13133626443 274877906944 8612574765861 52332630313533440 Bool.false 269809896321 1099511627776 34608098337999 209330521254133760 (@Enclosure.Real.IsNear.mulLit_ft qz310 (Real.cos qz311) 262143 1048576 1 1048576 50101 262144 32817979 49908285440 13133626443 274877906944 8612574765861 52332630313533440 qz579 (@Enclosure.Real.IsNear.recentre' (Real.cos qz311) Bool.true 200404 1048576 32817979 49908285440 50101 262144 32817979 49908285440 (ep304 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz310 (@Neg.neg Real Real.instNeg (Real.sin qz311)) 262143 1048576 1 1048576 1029247 1048576 32817979 49908285440 269809896321 1099511627776 34608098337999 209330521254133760 qz579 (@Enclosure.Real.IsNear.neg (Real.sin qz311) Bool.true 1029247 1048576 32817979 49908285440 (@Enclosure.Real.IsNear.recentre' (Real.sin qz311) Bool.true 1029247 1048576 32817979 49908285440 1029247 1048576 32817979 49908285440 (ep308 rfl rfl) rfl)) rfl)

noncomputable def ep310 := @ep190 13133626443 274877906944 8612574765861 52332630313533440 Bool.false 269809896321 1099511627776 34608098337999 209330521254133760 Bool.true 207552595377162882646016 755071943339 1099511627776 781585148598903 209330521254133760 Bool.false 74276499381264230383616 135108165307 1099511627776 781622917175203 209330521254133760 (ep191 (BSN.head_sum_c_succ qz12 15 16 rfl rfl) (ep295 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep296 ep309) rfl rfl

theorem EMRow41.d8 : Enclosure.Complex.IsNear (BSN.headSumC qz12 17) Bool.true 755071943339 1099511627776 781585148598903 209330521254133760 Bool.false 135108165307 1099511627776 781622917175203 209330521254133760 := ep189 (BSN.head_sum_c_succ qz12 16 17 rfl rfl) (ep310 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz865 := (@Nat.cast Complex Complex.instNatCast 24)

noncomputable def ep311 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 25) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 24) (@HPow.hPow Complex Complex Complex qz14 qz865 qz15)) Bool.false 662294107461 1099511627776 205459092604167 41866104250826752 Bool.false 111037628441 1099511627776 205383001431217 41866104250826752

noncomputable def ep312 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 24) (@HPow.hPow Complex Complex Complex qz14 qz865 qz15) Bool.false 175541804683 274877906944 99916255548893 20933052125413376 Bool.true 13728518183 137438953472 99862110892587 20933052125413376 Bool.true

noncomputable abbrev qz866 := (@Nat.cast Complex Complex.instNatCast 23)

noncomputable def ep313 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 24) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 23) (@HPow.hPow Complex Complex Complex qz14 qz866 qz15)) Bool.false 175541804683 274877906944 99916255548893 20933052125413376 Bool.true 13728518183 137438953472 99862110892587 20933052125413376

noncomputable def ep314 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 23) (@HPow.hPow Complex Complex Complex qz14 qz866 qz15) Bool.false 133366881841 274877906944 485156921095133 104665260627066880 Bool.true 16567307467 68719476736 484892054056203 104665260627066880 Bool.false

noncomputable abbrev qz867 := (@Nat.cast Complex Complex.instNatCast 22)

noncomputable def ep315 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 23) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 22) (@HPow.hPow Complex Complex Complex qz14 qz867 qz15)) Bool.false 133366881841 274877906944 485156921095133 104665260627066880 Bool.true 16567307467 68719476736 484892054056203 104665260627066880

noncomputable def ep316 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 22) (@HPow.hPow Complex Complex Complex qz14 qz867 qz15) Bool.false 299137986205 1099511627776 940767396111143 209330521254133760 Bool.true 258698614705 1099511627776 940431789240843 209330521254133760 Bool.false

noncomputable abbrev qz868 := (@Nat.cast Complex Complex.instNatCast 21)

noncomputable def ep317 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 22) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 21) (@HPow.hPow Complex Complex Complex qz14 qz868 qz15)) Bool.false 299137986205 1099511627776 940767396111143 209330521254133760 Bool.true 258698614705 1099511627776 940431789240843 209330521254133760

noncomputable def ep318 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 21) (@HPow.hPow Complex Complex Complex qz14 qz868 qz15) Bool.false 93555767651 1099511627776 910387652343213 209330521254133760 Bool.true 134990222367 1099511627776 910188289548153 209330521254133760 Bool.false

noncomputable abbrev qz869 := (@Nat.cast Complex Complex.instNatCast 20)

noncomputable def ep319 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 21) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 20) (@HPow.hPow Complex Complex Complex qz14 qz869 qz15)) Bool.false 93555767651 1099511627776 910387652343213 209330521254133760 Bool.true 134990222367 1099511627776 910188289548153 209330521254133760

noncomputable def ep320 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 20) (@HPow.hPow Complex Complex Complex qz14 qz869 qz15) Bool.true 41067920011 549755813888 33827319502023 8051173894389760 Bool.false 2312151901 68719476736 16909883735469 4025586947194880 Bool.false

noncomputable abbrev qz870 := (@Nat.cast Complex Complex.instNatCast 19)

noncomputable def ep321 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 20) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 19) (@HPow.hPow Complex Complex Complex qz14 qz870 qz15)) Bool.true 41067920011 549755813888 33827319502023 8051173894389760 Bool.false 2312151901 68719476736 16909883735469 4025586947194880

noncomputable def ep322 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 19) (@HPow.hPow Complex Complex Complex qz14 qz870 qz15) Bool.true 275475754471 1099511627776 847778520420903 209330521254133760 Bool.false 49750804757 274877906944 105950870490781 26166315156766720 Bool.false

noncomputable abbrev qz871 := (@Nat.cast Complex Complex.instNatCast 18)

noncomputable def ep323 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 19) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 18) (@HPow.hPow Complex Complex Complex qz14 qz871 qz15)) Bool.true 275475754471 1099511627776 847778520420903 209330521254133760 Bool.false 49750804757 274877906944 105950870490781 26166315156766720

noncomputable def ep324 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 18) (@HPow.hPow Complex Complex Complex qz14 qz871 qz15) Bool.true 524820961049 1099511627776 815142328599641 209330521254133760 Bool.false 33704501127 137438953472 203777109398659 52332630313533440 Bool.false

noncomputable abbrev qz872 := (@Nat.cast Complex Complex.instNatCast 17)

noncomputable def ep325 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 18) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 17) (@HPow.hPow Complex Complex Complex qz14 qz872 qz15)) Bool.true 524820961049 1099511627776 815142328599641 209330521254133760 Bool.false 33704501127 137438953472 203777109398659 52332630313533440

noncomputable def ep326 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 17) (@HPow.hPow Complex Complex Complex qz14 qz872 qz15) Bool.true 755071943339 1099511627776 781585148598903 209330521254133760 Bool.false 135108165307 1099511627776 781622917175203 209330521254133760 Bool.false

noncomputable abbrev qz873 := (@Nat.cast Real Real.instNatCast 17)

noncomputable abbrev qz315 := (@Inv.inv Real Real.instInv (Real.sqrt qz873))

noncomputable abbrev qz316 := (@HMul.hMul Real Real Real qz0 qz9 (Real.log (Enclosure.sfrac Bool.false 17 1)))

noncomputable def ep327 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz14 qz872 qz15) (Complex.mk (@HMul.hMul Real Real Real qz0 qz315 (Real.cos qz316)) (@HMul.hMul Real Real Real qz0 qz315 (@Neg.neg Real Real.instNeg (Real.sin qz316)))) Bool.false 115125491145 549755813888 166124653469 1036289709178880 Bool.false 134527843709 1099511627776 331539806133 2072579418357760 (BSN.cpow_neg_s_mk qz9 124004 1000 17 (@Eq.refl Real qz9) rfl)

noncomputable abbrev qz874 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 17) qz265)

noncomputable def ep328 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz873) 4323389 1048576 1 1048576 127158 127159 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz873) (Real.sqrt qz874) Bool.false 4323389 1048576 1 1048576 (BSN.sqrt_natCast_div_one 17) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz874) Bool.false 4323389 1048576 1 1048576 4323389 1048576 1 1048576 (BSN.sqrt_enclosure 17 1 2161694 2161695 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep329 := BSN.log_dyadic_bound 1 33 2 1 3267 524288 190385 1 1 31784 34 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1) (BSN.artanhQ 33) 0 1 1 3267 1 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz317 := (Real.log (Enclosure.sfrac Bool.false 17 1))

noncomputable def ep330 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz317 124004 1000 0 1 3189913004350711 1125899906842624 50000000038077 9519250000000000000 98890493047876391711 281474976710656000 53450000040704313 82062500000000000000 qz270 (BSN.isNear_log_sfrac 17 1 3189913004350711 1125899906842624 50000000038077 9519250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz874) Bool.false 53517859495200818200576 18889465931478580854784 1000000000761540 190385000000000000000 3189913004350711 1125899906842624 50000000038077 9519250000000000000 (BSN.log_rat_reduce_isNear 17 1 4 34 32 31784 524288 24973259072661432 36028797018963968 190385 1000000000000000 rfl rfl rfl rfl (ep329 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep331 := nat_lit 1613260301700041452392179989070492582486353494001147926180104862952237232619520

noncomputable def ep332 := nat_lit 628735257572187418871620176376474955543337662422371497203049877867551850496

noncomputable def ep333 := nat_lit 4224187599749753595682298300613347232774331842359084538523850655548835763388416

noncomputable def ep334 := BSN.sin_dyadic_bound_f 2237734084 2147483648 3 2 1048576 381142 ep331 ep95 ep332 ep333 ep97 ep332 905370 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2237734084) qz272 0 2 ep331 ep95 ep332 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2237734084) qz273 0 2 ep333 ep97 ep332 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz875 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 184197897) qz280)

noncomputable def ep335 := @Enclosure.Real.IsNear.cos_image qz316 qz875 Bool.false 184197897 524288 171 262144 Bool.false 905370 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz316 Bool.false 98890493047876391711 281474976710656000 53450000040704313 82062500000000000000 184197897 524288 171 262144 (ep330 rfl) rfl) (Enclosure.sfrac_false_div 184197897 524288) (BSN.cos_reduce3 qz875 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 78733268678894644363264) qz281) 226375608064910080 72057594037927936 Bool.false 905370 1048576 55 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q3 184197897 524288 226375608064910080 72057594037927936 55 78733268678894644363264 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 905370 1048576 78733268678894644363264 75557863725914323419136 2237734084 2147483648 381142 380770 (ep334 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep336 := nat_lit 896535161058944001292931825117552090250437868961714346321037390474739596722176

noncomputable def ep337 := nat_lit 2688348012661687629041052234999903320840226931560298295968706071668483686465536

noncomputable def ep338 := BSN.cos_dyadic_bound_f 2237734084 2147483648 3 2 1048576 381142 ep336 ep88 ep332 ep337 ep91 ep332 528977 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2237734084) qz266 0 2 ep336 ep88 ep332 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2237734084) qz267 0 2 ep337 ep91 ep332 rfl rfl rfl rfl) rfl rfl

noncomputable def ep339 := @Enclosure.Real.IsNear.sin_image qz316 qz875 Bool.false 184197897 524288 171 262144 Bool.true 528977 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz316 Bool.false 98890493047876391711 281474976710656000 53450000040704313 82062500000000000000 184197897 524288 171 262144 (ep330 rfl) rfl) (Enclosure.sfrac_false_div 184197897 524288) (BSN.sin_reduce3 qz875 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 78733268678894644363264) qz281) 226375608064910080 72057594037927936 Bool.false 528977 1048576 55 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q3 184197897 524288 226375608064910080 72057594037927936 55 78733268678894644363264 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 528977 1048576 78733268678894644363264 75557863725914323419136 2237734084 2147483648 381142 380770 (ep338 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz580 := (@Enclosure.Real.IsNear.recentre' qz315 Bool.false 254317 1048576 1 1048576 254317 1048576 1 1048576 (ep328 rfl rfl) rfl)

noncomputable def ep340 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz315 (Real.cos qz316)) (@HMul.hMul Real Real Real qz0 qz315 (@Neg.neg Real Real.instNeg (Real.sin qz316))) Bool.false 115125491145 549755813888 166124653469 1036289709178880 Bool.false 134527843709 1099511627776 331539806133 2072579418357760 (@Enclosure.Real.IsNear.mulLit_ff qz315 (Real.cos qz316) 254317 1048576 1 1048576 452685 524288 32817979 49908285440 115125491145 549755813888 166124653469 1036289709178880 qz580 (@Enclosure.Real.IsNear.recentre' (Real.cos qz316) Bool.false 905370 1048576 32817979 49908285440 452685 524288 32817979 49908285440 (ep335 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz315 (@Neg.neg Real Real.instNeg (Real.sin qz316)) 254317 1048576 1 1048576 528977 1048576 32817979 49908285440 134527843709 1099511627776 331539806133 2072579418357760 qz580 (@Enclosure.Real.IsNear.neg (Real.sin qz316) Bool.true 528977 1048576 32817979 49908285440 (@Enclosure.Real.IsNear.recentre' (Real.sin qz316) Bool.true 528977 1048576 32817979 49908285440 528977 1048576 32817979 49908285440 (ep339 rfl rfl) rfl)) rfl)

noncomputable def ep341 := @ep326 115125491145 549755813888 166124653469 1036289709178880 Bool.false 134527843709 1099511627776 331539806133 2072579418357760 Bool.true 288523374586975341248512 524820961049 1099511627776 815142328599641 209330521254133760 Bool.false 296467927180206372028416 33704501127 137438953472 203777109398659 52332630313533440 EMRow41.d8 (ep327 ep340) rfl rfl

noncomputable abbrev qz876 := (@Nat.cast Real Real.instNatCast 18)

noncomputable abbrev qz318 := (@Inv.inv Real Real.instInv (Real.sqrt qz876))

noncomputable abbrev qz319 := (@HMul.hMul Real Real Real qz0 qz9 (Real.log (Enclosure.sfrac Bool.false 18 1)))

noncomputable def ep342 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz14 qz871 qz15) (Complex.mk (@HMul.hMul Real Real Real qz0 qz318 (Real.cos qz319)) (@HMul.hMul Real Real Real qz0 qz318 (@Neg.neg Real Real.instNeg (Real.sin qz319)))) Bool.false 124672603289 549755813888 16318095910631 104665260627066880 Bool.true 17658197497 274877906944 8124631582903 52332630313533440 (BSN.cpow_neg_s_mk qz9 124004 1000 18 (@Eq.refl Real qz9) rfl)

noncomputable abbrev qz877 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 18) qz265)

noncomputable def ep343 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz876) 4448731 1048576 1 1048576 123575 123576 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz876) (Real.sqrt qz877) Bool.false 4448731 1048576 1 1048576 (BSN.sqrt_natCast_div_one 18) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz877) Bool.false 4448731 1048576 1 1048576 4448731 1048576 1 1048576 (BSN.sqrt_enclosure 18 1 2224365 2224366 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep344 := BSN.log_dyadic_bound 2 34 3 2 20045040 524288 190385 23168 48 61752 36 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 2) (BSN.artanhQ 34) 0 2 23168 20045040 48 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz320 := (Real.log (Enclosure.sfrac Bool.false 18 1))

noncomputable def ep345 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz320 124004 1000 0 1 3254268794313975 1125899906842624 50000000038077 9519250000000000000 4035423475701101559 11258999068426240 53450000040704313 82062500000000000000 qz270 (BSN.isNear_log_sfrac 18 1 3254268794313975 1125899906842624 50000000038077 9519250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz877) Bool.false 54597570484265130393600 18889465931478580854784 1000000000761540 190385000000000000000 3254268794313975 1125899906842624 50000000038077 9519250000000000000 (BSN.log_rat_reduce_isNear 18 1 4 36 32 61752 524288 24973259072661432 36028797018963968 190385 1000000000000000 rfl rfl rfl rfl (ep344 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep346 := nat_lit 123486569959432677925767694769629456

noncomputable def ep347 := BSN.cos_dyadic_bound_f 592795546 2147483648 2 1 1048576 381142 ep346 ep143 ep346 ep346 ep144 ep346 1008878 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 592795546) qz266 0 1 ep346 ep143 ep346 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 592795546) qz267 0 1 ep346 ep144 ep346 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz878 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 187914049) qz280)

noncomputable def ep348 := @Enclosure.Real.IsNear.cos_image qz319 qz878 Bool.false 187914049 524288 171 262144 Bool.false 1008878 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz319 Bool.false 4035423475701101559 11258999068426240 53450000040704313 82062500000000000000 187914049 524288 171 262144 (ep345 rfl) rfl) (Enclosure.sfrac_false_div 187914049 524288) (BSN.cos_reduce0 qz878 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 20857139071684714692608) qz281) 226375608064910080 72057594037927936 Bool.false 1008878 1048576 57 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q0 187914049 524288 226375608064910080 72057594037927936 57 20857139071684714692608 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1008878 1048576 20857139071684714692608 75557863725914323419136 592795546 2147483648 381142 380770 (ep347 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep349 := BSN.sin_dyadic_bound_f 592795546 2147483648 2 1 1048576 381142 ep346 ep123 ep346 ep346 ep124 ep346 285788 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 592795546) qz272 0 1 ep346 ep123 ep346 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 592795546) qz273 0 1 ep346 ep124 ep346 rfl rfl rfl rfl) rfl rfl

noncomputable def ep350 := @Enclosure.Real.IsNear.sin_image qz319 qz878 Bool.false 187914049 524288 171 262144 Bool.false 285788 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz319 Bool.false 4035423475701101559 11258999068426240 53450000040704313 82062500000000000000 187914049 524288 171 262144 (ep345 rfl) rfl) (Enclosure.sfrac_false_div 187914049 524288) (BSN.sin_reduce0 qz878 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 20857139071684714692608) qz281) 226375608064910080 72057594037927936 Bool.false 285788 1048576 57 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q0 187914049 524288 226375608064910080 72057594037927936 57 20857139071684714692608 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 285788 1048576 20857139071684714692608 75557863725914323419136 592795546 2147483648 381142 380770 (ep349 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz581 := (@Enclosure.Real.IsNear.recentre' qz318 Bool.false 247151 1048576 1 1048576 247151 1048576 1 1048576 (ep343 rfl rfl) rfl)

noncomputable def ep351 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz318 (Real.cos qz319)) (@HMul.hMul Real Real Real qz0 qz318 (@Neg.neg Real Real.instNeg (Real.sin qz319))) Bool.false 124672603289 549755813888 16318095910631 104665260627066880 Bool.true 17658197497 274877906944 8124631582903 52332630313533440 (@Enclosure.Real.IsNear.mulLit_ff qz318 (Real.cos qz319) 247151 1048576 1 1048576 504439 524288 32817979 49908285440 124672603289 549755813888 16318095910631 104665260627066880 qz581 (@Enclosure.Real.IsNear.recentre' (Real.cos qz319) Bool.false 1008878 1048576 32817979 49908285440 504439 524288 32817979 49908285440 (ep348 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz318 (@Neg.neg Real Real.instNeg (Real.sin qz319)) 247151 1048576 1 1048576 71447 262144 32817979 49908285440 17658197497 274877906944 8124631582903 52332630313533440 qz581 (@Enclosure.Real.IsNear.neg (Real.sin qz319) Bool.false 71447 262144 32817979 49908285440 (@Enclosure.Real.IsNear.recentre' (Real.sin qz319) Bool.false 285788 1048576 32817979 49908285440 71447 262144 32817979 49908285440 (ep350 rfl rfl) rfl)) rfl)

noncomputable def ep352 := @ep324 124672603289 549755813888 16318095910631 104665260627066880 Bool.true 17658197497 274877906944 8124631582903 52332630313533440 Bool.true 151444397605615459893248 275475754471 1099511627776 847778520420903 209330521254133760 Bool.false 6837698540191879266304 49750804757 274877906944 105950870490781 26166315156766720 (ep325 (BSN.head_sum_c_succ qz12 17 18 rfl rfl) (ep341 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep342 ep351) rfl rfl

noncomputable abbrev qz879 := (@Nat.cast Real Real.instNatCast 19)

noncomputable abbrev qz321 := (@Inv.inv Real Real.instInv (Real.sqrt qz879))

noncomputable abbrev qz322 := (@HMul.hMul Real Real Real qz0 qz9 (Real.log (Enclosure.sfrac Bool.false 19 1)))

noncomputable def ep353 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz14 qz870 qz15) (Complex.mk (@HMul.hMul Real Real Real qz0 qz321 (Real.cos qz322)) (@HMul.hMul Real Real Real qz0 qz321 (@Neg.neg Real Real.instNeg (Real.sin qz322)))) Bool.false 193339914449 1099511627776 6346357326339 41866104250826752 Bool.true 40502197153 274877906944 1585349515907 10466526062706688 (BSN.cpow_neg_s_mk qz9 124004 1000 19 (@Eq.refl Real qz9) rfl)

noncomputable abbrev qz880 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 19) qz265)

noncomputable def ep354 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz879) 4570637 1048576 1 1048576 120279 120280 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz879) (Real.sqrt qz880) Bool.false 4570637 1048576 1 1048576 (BSN.sqrt_natCast_div_one 19) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz880) Bool.false 4570637 1048576 1 1048576 4570637 1048576 1 1048576 (BSN.sqrt_enclosure 19 1 2285318 2285319 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep355 := BSN.log_dyadic_bound 3 35 3 2 22509375 524288 190385 55368 243 90099 38 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 3) (BSN.artanhQ 35) 0 2 55368 22509375 243 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz323 := (Real.log (Enclosure.sfrac Bool.false 19 1))

noncomputable def ep356 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz323 124004 1000 0 1 3315143513283831 1125899906842624 50000000038077 9519250000000000000 102772764055312044831 281474976710656000 53450000040704313 82062500000000000000 qz270 (BSN.isNear_log_sfrac 19 1 3315143513283831 1125899906842624 50000000038077 9519250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz880) Bool.false 55618878793361701994496 18889465931478580854784 1000000000761540 190385000000000000000 3315143513283831 1125899906842624 50000000038077 9519250000000000000 (BSN.log_rat_reduce_isNear 19 1 4 38 32 90099 524288 24973259072661432 36028797018963968 190385 1000000000000000 rfl rfl rfl rfl (ep355 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep357 := nat_lit 179836009363420274765729307346611272446431953835835136798837128116287730680961

noncomputable def ep358 := nat_lit 25326401825489449305379861219964528736707734388268869589458811945036874881

noncomputable def ep359 := nat_lit 539457375286609845398577162317393888281822446038728872657332466724973118293121

noncomputable def ep360 := BSN.cos_dyadic_bound_f 1497775377 2147483648 3 2 1048576 381142 ep357 ep88 ep358 ep359 ep91 ep358 803711 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1497775377) qz266 0 2 ep357 ep88 ep358 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1497775377) qz267 0 2 ep359 ep91 ep358 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz881 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 95714595) qz313)

noncomputable def ep361 := @Enclosure.Real.IsNear.cos_image qz322 qz881 Bool.false 95714595 262144 171 262144 Bool.false 803711 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz322 Bool.false 102772764055312044831 281474976710656000 53450000040704313 82062500000000000000 95714595 262144 171 262144 (ep356 rfl) rfl) (Enclosure.sfrac_false_div 95714595 262144) (BSN.cos_reduce0 qz881 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26349143097647248179200) qz314) 226375608064910080 72057594037927936 Bool.false 803711 1048576 58 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q0 95714595 262144 226375608064910080 72057594037927936 58 26349143097647248179200 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 803711 1048576 26349143097647248179200 37778931862957161709568 1497775377 2147483648 381142 380770 (ep360 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep362 := nat_lit 5032534334258381322084895716516952641

noncomputable def ep363 := BSN.sin_dyadic_bound_f 1497775377 2147483648 2 1 1048576 381142 ep362 ep123 ep362 ep362 ep124 ep362 673468 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1497775377) qz272 0 1 ep362 ep123 ep362 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1497775377) qz273 0 1 ep362 ep124 ep362 rfl rfl rfl rfl) rfl rfl

noncomputable def ep364 := @Enclosure.Real.IsNear.sin_image qz322 qz881 Bool.false 95714595 262144 171 262144 Bool.false 673468 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz322 Bool.false 102772764055312044831 281474976710656000 53450000040704313 82062500000000000000 95714595 262144 171 262144 (ep356 rfl) rfl) (Enclosure.sfrac_false_div 95714595 262144) (BSN.sin_reduce0 qz881 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26349143097647248179200) qz314) 226375608064910080 72057594037927936 Bool.false 673468 1048576 58 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q0 95714595 262144 226375608064910080 72057594037927936 58 26349143097647248179200 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 673468 1048576 26349143097647248179200 37778931862957161709568 1497775377 2147483648 381142 380770 (ep363 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz582 := (@Enclosure.Real.IsNear.recentre' qz321 Bool.false 240559 1048576 1 1048576 240559 1048576 1 1048576 (ep354 rfl rfl) rfl)

noncomputable def ep365 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz321 (Real.cos qz322)) (@HMul.hMul Real Real Real qz0 qz321 (@Neg.neg Real Real.instNeg (Real.sin qz322))) Bool.false 193339914449 1099511627776 6346357326339 41866104250826752 Bool.true 40502197153 274877906944 1585349515907 10466526062706688 (@Enclosure.Real.IsNear.mulLit_ff qz321 (Real.cos qz322) 240559 1048576 1 1048576 803711 1048576 32817979 49908285440 193339914449 1099511627776 6346357326339 41866104250826752 qz582 (@Enclosure.Real.IsNear.recentre' (Real.cos qz322) Bool.false 803711 1048576 32817979 49908285440 803711 1048576 32817979 49908285440 (ep361 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz321 (@Neg.neg Real Real.instNeg (Real.sin qz322)) 240559 1048576 1 1048576 168367 262144 32817979 49908285440 40502197153 274877906944 1585349515907 10466526062706688 qz582 (@Enclosure.Real.IsNear.neg (Real.sin qz322) Bool.false 168367 262144 32817979 49908285440 (@Enclosure.Real.IsNear.recentre' (Real.sin qz322) Bool.false 673468 1048576 32817979 49908285440 168367 262144 32817979 49908285440 (ep364 rfl rfl) rfl)) rfl)

noncomputable def ep366 := @ep322 193339914449 1099511627776 6346357326339 41866104250826752 Bool.true 40502197153 274877906944 1585349515907 10466526062706688 Bool.true 90309311161338347651072 41067920011 549755813888 33827319502023 8051173894389760 Bool.false 2542237900333882802176 2312151901 68719476736 16909883735469 4025586947194880 (ep323 (BSN.head_sum_c_succ qz12 18 19 rfl rfl) (ep352 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep353 ep365) rfl rfl

noncomputable abbrev qz882 := (@Nat.cast Real Real.instNatCast 20)

noncomputable abbrev qz324 := (@Inv.inv Real Real.instInv (Real.sqrt qz882))

noncomputable abbrev qz325 := (@HMul.hMul Real Real Real qz0 qz9 (Real.log (Enclosure.sfrac Bool.false 20 1)))

noncomputable def ep367 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz14 qz869 qz15) (Complex.mk (@HMul.hMul Real Real Real qz0 qz324 (Real.cos qz325)) (@HMul.hMul Real Real Real qz0 qz324 (@Neg.neg Real Real.instNeg (Real.sin qz325)))) Bool.false 175691607673 1099511627776 6175469058123 41866104250826752 Bool.true 171984652783 1099511627776 6174867060753 41866104250826752 (BSN.cpow_neg_s_mk qz9 124004 1000 20 (@Eq.refl Real qz9) rfl)

noncomputable abbrev qz883 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 20) qz265)

noncomputable def ep368 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz882) 4689375 1048576 1 1048576 117234 117235 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz882) (Real.sqrt qz883) Bool.false 4689375 1048576 1 1048576 (BSN.sqrt_natCast_div_one 20) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz883) Bool.false 4689375 1048576 1 1048576 4689375 1048576 1 1048576 (BSN.sqrt_enclosure 20 1 2344687 2344688 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep369 := BSN.log_dyadic_bound 4 36 3 2 25194240 524288 190385 104448 768 116991 40 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 4) (BSN.artanhQ 36) 0 2 104448 25194240 768 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz326 := (Real.log (Enclosure.sfrac Bool.false 20 1))

noncomputable def ep370 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz326 124004 1000 0 1 3372893643545847 1125899906842624 50000000038077 9519250000000000000 104563075843564802847 281474976710656000 53450000040704313 82062500000000000000 qz270 (BSN.isNear_log_sfrac 20 1 3372893643545847 1125899906842624 50000000038077 9519250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz883) Bool.false 56587765202795681021952 18889465931478580854784 1000000000761540 190385000000000000000 3372893643545847 1125899906842624 50000000038077 9519250000000000000 (BSN.log_rat_reduce_isNear 20 1 4 40 32 116991 524288 24973259072661432 36028797018963968 190385 1000000000000000 rfl rfl rfl rfl (ep369 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep371 := nat_lit 273815393105189681277069772737296838028134810407896527354689232522638931643201

noncomputable def ep372 := nat_lit 58704580577170919427892972589326416360175127889712872488592426342503795521

noncomputable def ep373 := nat_lit 821328770154414701992353532266711861251684080967910156319090512715231787338561

noncomputable def ep374 := BSN.cos_dyadic_bound_f 1663734409 2147483648 3 2 1048576 381142 ep371 ep88 ep372 ep373 ep91 ep372 749317 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1663734409) qz266 0 2 ep371 ep88 ep372 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1663734409) qz267 0 2 ep373 ep91 ep372 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz884 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 97381953) qz313)

noncomputable def ep375 := @Enclosure.Real.IsNear.cos_image qz325 qz884 Bool.false 97381953 262144 683 1048576 Bool.false 749317 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz325 Bool.false 104563075843564802847 281474976710656000 53450000040704313 82062500000000000000 97381953 262144 683 1048576 (ep370 rfl) rfl) (Enclosure.sfrac_false_div 97381953 262144) (BSN.cos_reduce0 qz884 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 29268725255158991159296) qz314) 226375608064910080 72057594037927936 Bool.false 749317 1048576 59 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q0 97381953 262144 226375608064910080 72057594037927936 59 29268725255158991159296 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 749317 1048576 29268725255158991159296 37778931862957161709568 1663734409 2147483648 381142 380770 (ep374 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep376 := nat_lit 7661891449059489215747660589346476961

noncomputable def ep377 := BSN.sin_dyadic_bound_f 1663734409 2147483648 2 1 1048576 381142 ep376 ep123 ep376 ep376 ep124 ep376 733507 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1663734409) qz272 0 1 ep376 ep123 ep376 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1663734409) qz273 0 1 ep376 ep124 ep376 rfl rfl rfl rfl) rfl rfl

noncomputable def ep378 := @Enclosure.Real.IsNear.sin_image qz325 qz884 Bool.false 97381953 262144 683 1048576 Bool.false 733507 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz325 Bool.false 104563075843564802847 281474976710656000 53450000040704313 82062500000000000000 97381953 262144 683 1048576 (ep370 rfl) rfl) (Enclosure.sfrac_false_div 97381953 262144) (BSN.sin_reduce0 qz884 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 29268725255158991159296) qz314) 226375608064910080 72057594037927936 Bool.false 733507 1048576 59 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q0 97381953 262144 226375608064910080 72057594037927936 59 29268725255158991159296 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 733507 1048576 29268725255158991159296 37778931862957161709568 1663734409 2147483648 381142 380770 (ep377 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz583 := (@Enclosure.Real.IsNear.recentre' qz324 Bool.false 234469 1048576 1 1048576 234469 1048576 1 1048576 (ep368 rfl rfl) rfl)

noncomputable def ep379 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz324 (Real.cos qz325)) (@HMul.hMul Real Real Real qz0 qz324 (@Neg.neg Real Real.instNeg (Real.sin qz325))) Bool.false 175691607673 1099511627776 6175469058123 41866104250826752 Bool.true 171984652783 1099511627776 6174867060753 41866104250826752 (@Enclosure.Real.IsNear.mulLit_ff qz324 (Real.cos qz325) 234469 1048576 1 1048576 749317 1048576 131081531 199633141760 175691607673 1099511627776 6175469058123 41866104250826752 qz583 (@Enclosure.Real.IsNear.recentre' (Real.cos qz325) Bool.false 749317 1048576 131081531 199633141760 749317 1048576 131081531 199633141760 (ep375 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz324 (@Neg.neg Real Real.instNeg (Real.sin qz325)) 234469 1048576 1 1048576 733507 1048576 131081531 199633141760 171984652783 1099511627776 6174867060753 41866104250826752 qz583 (@Enclosure.Real.IsNear.neg (Real.sin qz325) Bool.false 733507 1048576 131081531 199633141760 (@Enclosure.Real.IsNear.recentre' (Real.sin qz325) Bool.false 733507 1048576 131081531 199633141760 733507 1048576 131081531 199633141760 (ep378 rfl rfl) rfl)) rfl)

noncomputable def ep380 := @ep320 175691607673 1099511627776 6175469058123 41866104250826752 Bool.true 171984652783 1099511627776 6174867060753 41866104250826752 Bool.false 51432827188892126937088 93555767651 1099511627776 910387652343213 209330521254133760 Bool.true 9276457445536523354112 134990222367 1099511627776 910188289548153 209330521254133760 (ep321 (BSN.head_sum_c_succ qz12 19 20 rfl rfl) (ep366 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep367 ep379) rfl rfl

noncomputable abbrev qz885 := (@Nat.cast Real Real.instNatCast 21)

noncomputable abbrev qz327 := (@Inv.inv Real Real.instInv (Real.sqrt qz885))

noncomputable abbrev qz328 := (@HMul.hMul Real Real Real qz0 qz9 (Real.log (Enclosure.sfrac Bool.false 21 1)))

noncomputable def ep381 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz14 qz868 qz15) (Complex.mk (@HMul.hMul Real Real Real qz0 qz327 (Real.cos qz328)) (@HMul.hMul Real Real Real qz0 qz327 (@Neg.neg Real Real.instNeg (Real.sin qz328)))) Bool.false 102791109277 549755813888 3037974376793 20933052125413376 Bool.true 61854196169 549755813888 3024349969269 20933052125413376 (BSN.cpow_neg_s_mk qz9 124004 1000 21 (@Eq.refl Real qz9) rfl)

noncomputable abbrev qz886 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 21) qz265)

noncomputable def ep382 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz885) 4805179 1048576 1 1048576 114408 114410 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz885) (Real.sqrt qz886) Bool.false 4805179 1048576 1 1048576 (BSN.sqrt_natCast_div_one 21) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz886) Bool.false 4805179 1048576 1 1048576 4805179 1048576 1 1048576 (BSN.sqrt_enclosure 21 1 2402589 2402590 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep383 := BSN.log_dyadic_bound 5 37 4 3 269401272945 524288 190385 1658093375 234375 142571 42 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 5) (BSN.artanhQ 37) 0 3 1658093375 269401272945 234375 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz329 := (Real.log (Enclosure.sfrac Bool.false 21 1))

noncomputable def ep384 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz329 124004 1000 0 1 3427826275261687 1125899906842624 50000000038077 9519250000000000000 106266042359387558687 281474976710656000 53450000040704313 82062500000000000000 qz270 (BSN.isNear_log_sfrac 21 1 3427826275261687 1125899906842624 50000000038077 9519250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz886) Bool.false 57509381830540779323392 18889465931478580854784 1000000000761540 190385000000000000000 3427826275261687 1125899906842624 50000000038077 9519250000000000000 (BSN.log_rat_reduce_isNear 21 1 4 42 32 142571 524288 24973259072661432 36028797018963968 190385 1000000000000000 rfl rfl rfl rfl (ep383 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep385 := nat_lit 1831323819908207427300719259587444736

noncomputable def ep386 := BSN.cos_dyadic_bound_f 1163298816 2147483648 2 1 1048576 381142 ep385 ep143 ep385 ep385 ep144 ep385 898453 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1163298816) qz266 0 1 ep385 ep143 ep385 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1163298816) qz267 0 1 ep385 ep144 ep385 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz584 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 24741991) (@Nat.cast Real Real.instNatCast 65536))

noncomputable def ep387 := @Enclosure.Real.IsNear.cos_image qz328 qz584 Bool.false 24741991 65536 171 262144 Bool.false 898453 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz328 Bool.false 106266042359387558687 281474976710656000 53450000040704313 82062500000000000000 24741991 65536 171 262144 (ep384 rfl) rfl) (Enclosure.sfrac_false_div 24741991 65536) (BSN.cos_reduce0 qz584 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 5116242302066021629952) (@Nat.cast Real Real.instNatCast 9444732965739290427392)) 226375608064910080 72057594037927936 Bool.false 898453 1048576 60 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q0 24741991 65536 226375608064910080 72057594037927936 60 5116242302066021629952 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 898453 1048576 5116242302066021629952 9444732965739290427392 1163298816 2147483648 381142 380770 (ep386 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep388 := BSN.sin_dyadic_bound_f 1163298816 2147483648 2 1 1048576 381142 ep385 ep123 ep385 ep385 ep124 ep385 540641 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1163298816) qz272 0 1 ep385 ep123 ep385 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1163298816) qz273 0 1 ep385 ep124 ep385 rfl rfl rfl rfl) rfl rfl

noncomputable def ep389 := @Enclosure.Real.IsNear.sin_image qz328 qz584 Bool.false 24741991 65536 171 262144 Bool.false 540641 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz328 Bool.false 106266042359387558687 281474976710656000 53450000040704313 82062500000000000000 24741991 65536 171 262144 (ep384 rfl) rfl) (Enclosure.sfrac_false_div 24741991 65536) (BSN.sin_reduce0 qz584 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 5116242302066021629952) (@Nat.cast Real Real.instNatCast 9444732965739290427392)) 226375608064910080 72057594037927936 Bool.false 540641 1048576 60 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q0 24741991 65536 226375608064910080 72057594037927936 60 5116242302066021629952 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 540641 1048576 5116242302066021629952 9444732965739290427392 1163298816 2147483648 381142 380770 (ep388 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz585 := (@Enclosure.Real.IsNear.recentre' qz327 Bool.false 228818 1048576 2 1048576 114409 524288 1 524288 (ep382 rfl rfl) rfl)

noncomputable def ep390 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz327 (Real.cos qz328)) (@HMul.hMul Real Real Real qz0 qz327 (@Neg.neg Real Real.instNeg (Real.sin qz328))) Bool.false 102791109277 549755813888 3037974376793 20933052125413376 Bool.true 61854196169 549755813888 3024349969269 20933052125413376 (@Enclosure.Real.IsNear.mulLit_ff qz327 (Real.cos qz328) 114409 524288 1 524288 898453 1048576 32817979 49908285440 102791109277 549755813888 3037974376793 20933052125413376 qz585 (@Enclosure.Real.IsNear.recentre' (Real.cos qz328) Bool.false 898453 1048576 32817979 49908285440 898453 1048576 32817979 49908285440 (ep387 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz327 (@Neg.neg Real Real.instNeg (Real.sin qz328)) 114409 524288 1 524288 540641 1048576 32817979 49908285440 61854196169 549755813888 3024349969269 20933052125413376 qz585 (@Enclosure.Real.IsNear.neg (Real.sin qz328) Bool.false 540641 1048576 32817979 49908285440 (@Enclosure.Real.IsNear.recentre' (Real.sin qz328) Bool.false 540641 1048576 32817979 49908285440 540641 1048576 32817979 49908285440 (ep389 rfl rfl) rfl)) rfl)

noncomputable def ep391 := @ep318 102791109277 549755813888 3037974376793 20933052125413376 Bool.true 61854196169 549755813888 3024349969269 20933052125413376 Bool.false 164452847070947091415040 299137986205 1099511627776 940767396111143 209330521254133760 Bool.true 142221067478845400023040 258698614705 1099511627776 940431789240843 209330521254133760 (ep319 (BSN.head_sum_c_succ qz12 20 21 rfl rfl) (ep380 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep381 ep390) rfl rfl

noncomputable abbrev qz887 := (@Nat.cast Real Real.instNatCast 22)

noncomputable abbrev qz330 := (@Inv.inv Real Real.instInv (Real.sqrt qz887))

noncomputable abbrev qz331 := (@HMul.hMul Real Real Real qz0 qz9 (Real.log (Enclosure.sfrac Bool.false 22 1)))

noncomputable def ep392 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz14 qz867 qz15) (Complex.mk (@HMul.hMul Real Real Real qz0 qz330 (Real.cos qz331)) (@HMul.hMul Real Real Real qz0 qz330 (@Neg.neg Real Real.instNeg (Real.sin qz331)))) Bool.false 234329541159 1099511627776 29546446079123 209330521254133760 Bool.true 6378304767 1099511627776 29352318871563 209330521254133760 (BSN.cpow_neg_s_mk qz9 124004 1000 22 (@Eq.refl Real qz9) rfl)

noncomputable abbrev qz888 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 22) qz265)

noncomputable def ep393 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz887) 4918257 1048576 1 1048576 111778 111779 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz887) (Real.sqrt qz888) Bool.false 4918257 1048576 1 1048576 (BSN.sqrt_natCast_div_one 22) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz888) Bool.false 4918257 1048576 1 1048576 4918257 1048576 1 1048576 (BSN.sqrt_enclosure 22 1 2459128 2459129 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep394 := BSN.log_dyadic_bound 6 38 4 3 316148320320 524288 190385 2667271104 699840 166961 44 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 6) (BSN.artanhQ 38) 0 3 2667271104 316148320320 699840 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz332 := (Real.log (Enclosure.sfrac Bool.false 22 1))

noncomputable def ep395 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz332 124004 1000 0 1 3480203401436407 1125899906842624 50000000038077 9519250000000000000 107889785647930053407 281474976710656000 53450000040704313 82062500000000000000 qz270 (BSN.isNear_log_sfrac 22 1 3480203401436407 1125899906842624 50000000038077 9519250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz888) Bool.false 58388124189833310502912 18889465931478580854784 1000000000761540 190385000000000000000 3480203401436407 1125899906842624 50000000038077 9519250000000000000 (BSN.log_rat_reduce_isNear 22 1 4 44 32 166961 524288 24973259072661432 36028797018963968 190385 1000000000000000 rfl rfl rfl rfl (ep394 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep396 := BSN.cos_dyadic_bound_f 58439032 2147483648 1 0 1048576 381142 0 1 1 0 1 1 1048187 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 58439032) qz266 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 58439032) qz267 0 0 rfl) rfl rfl

noncomputable abbrev qz889 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 401920771) qz268)

noncomputable def ep397 := @Enclosure.Real.IsNear.cos_image qz331 qz889 Bool.false 401920771 1048576 171 262144 Bool.false 1048187 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz331 Bool.false 107889785647930053407 281474976710656000 53450000040704313 82062500000000000000 401920771 1048576 171 262144 (ep395 rfl) rfl) (Enclosure.sfrac_false_div 401920771 1048576) (BSN.cos_reduce0 qz889 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4112281303837459873792) qz271) 226375608064910080 72057594037927936 Bool.false 1048187 1048576 61 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q0 401920771 1048576 226375608064910080 72057594037927936 61 4112281303837459873792 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1048187 1048576 4112281303837459873792 151115727451828646838272 58439032 2147483648 381142 380770 (ep396 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep398 := BSN.sin_dyadic_bound_f 58439032 2147483648 1 0 1048576 381142 0 1 1 0 1 1 28531 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 58439032) qz272 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 58439032) qz273 0 0 rfl) rfl rfl

noncomputable def ep399 := @Enclosure.Real.IsNear.sin_image qz331 qz889 Bool.false 401920771 1048576 171 262144 Bool.false 28531 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz331 Bool.false 107889785647930053407 281474976710656000 53450000040704313 82062500000000000000 401920771 1048576 171 262144 (ep395 rfl) rfl) (Enclosure.sfrac_false_div 401920771 1048576) (BSN.sin_reduce0 qz889 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4112281303837459873792) qz271) 226375608064910080 72057594037927936 Bool.false 28531 1048576 61 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q0 401920771 1048576 226375608064910080 72057594037927936 61 4112281303837459873792 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 28531 1048576 4112281303837459873792 151115727451828646838272 58439032 2147483648 381142 380770 (ep398 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz586 := (@Enclosure.Real.IsNear.recentre' qz330 Bool.false 223557 1048576 1 1048576 223557 1048576 1 1048576 (ep393 rfl rfl) rfl)

noncomputable def ep400 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz330 (Real.cos qz331)) (@HMul.hMul Real Real Real qz0 qz330 (@Neg.neg Real Real.instNeg (Real.sin qz331))) Bool.false 234329541159 1099511627776 29546446079123 209330521254133760 Bool.true 6378304767 1099511627776 29352318871563 209330521254133760 (@Enclosure.Real.IsNear.mulLit_ff qz330 (Real.cos qz331) 223557 1048576 1 1048576 1048187 1048576 32817979 49908285440 234329541159 1099511627776 29546446079123 209330521254133760 qz586 (@Enclosure.Real.IsNear.recentre' (Real.cos qz331) Bool.false 1048187 1048576 32817979 49908285440 1048187 1048576 32817979 49908285440 (ep397 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz330 (@Neg.neg Real Real.instNeg (Real.sin qz331)) 223557 1048576 1 1048576 28531 1048576 32817979 49908285440 6378304767 1099511627776 29352318871563 209330521254133760 qz586 (@Enclosure.Real.IsNear.neg (Real.sin qz331) Bool.false 28531 1048576 32817979 49908285440 (@Enclosure.Real.IsNear.recentre' (Real.sin qz331) Bool.false 28531 1048576 32817979 49908285440 28531 1048576 32817979 49908285440 (ep399 rfl rfl) rfl)) rfl)

noncomputable def ep401 := @ep316 234329541159 1099511627776 29546446079123 209330521254133760 Bool.true 6378304767 1099511627776 29352318871563 209330521254133760 Bool.false 586553749377629462462464 133366881841 274877906944 485156921095133 104665260627066880 Bool.true 291455155214506390454272 16567307467 68719476736 484892054056203 104665260627066880 (ep317 (BSN.head_sum_c_succ qz12 21 22 rfl rfl) (ep391 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep392 ep400) rfl rfl

noncomputable abbrev qz890 := (@Nat.cast Real Real.instNatCast 23)

noncomputable abbrev qz333 := (@Inv.inv Real Real.instInv (Real.sqrt qz890))

noncomputable abbrev qz334 := (@HMul.hMul Real Real Real qz0 qz9 (Real.log (Enclosure.sfrac Bool.false 23 1)))

noncomputable def ep402 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz14 qz866 qz15) (Complex.mk (@HMul.hMul Real Real Real qz0 qz333 (Real.cos qz334)) (@HMul.hMul Real Real Real qz0 qz333 (@Neg.neg Real Real.instNeg (Real.sin qz334)))) Bool.false 21087461421 137438953472 3606089162333 26166315156766720 Bool.false 19406096751 137438953472 3604625101683 26166315156766720 (BSN.cpow_neg_s_mk qz9 124004 1000 23 (@Eq.refl Real qz9) rfl)

noncomputable abbrev qz891 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 23) qz265)

noncomputable def ep403 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz890) 5028793 1048576 1 1048576 109321 109322 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz890) (Real.sqrt qz891) Bool.false 5028793 1048576 1 1048576 (BSN.sqrt_natCast_div_one 23) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz891) Bool.false 5028793 1048576 1 1048576 5028793 1048576 1 1048576 (BSN.sqrt_enclosure 23 1 2514396 2514397 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep404 := BSN.log_dyadic_bound 7 39 4 3 369468094905 524288 190385 4046006391 1764735 190266 46 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 7) (BSN.artanhQ 39) 0 3 4046006391 369468094905 1764735 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz335 := (Real.log (Enclosure.sfrac Bool.false 23 1))

noncomputable def ep405 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz335 124004 1000 0 1 3530250507853047 1125899906842624 50000000038077 9519250000000000000 109441295993952310047 281474976710656000 53450000040704313 82062500000000000000 qz270 (BSN.isNear_log_sfrac 23 1 3530250507853047 1125899906842624 50000000038077 9519250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz891) Bool.false 59227775304360265777152 18889465931478580854784 1000000000761540 190385000000000000000 3530250507853047 1125899906842624 50000000038077 9519250000000000000 (BSN.log_rat_reduce_isNear 23 1 4 46 32 190266 524288 24973259072661432 36028797018963968 190385 1000000000000000 rfl rfl rfl rfl (ep404 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep406 := nat_lit 9943146070737635527975935925484379201

noncomputable def ep407 := BSN.sin_dyadic_bound_f 1775746449 2147483648 2 1 1048576 381142 ep406 ep123 ep406 ep406 ep124 ep406 771576 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1775746449) qz272 0 1 ep406 ep123 ep406 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1775746449) qz273 0 1 ep406 ep124 ep406 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz892 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 203850299) qz280)

noncomputable def ep408 := @Enclosure.Real.IsNear.cos_image qz334 qz892 Bool.false 203850299 524288 171 262144 Bool.false 771576 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz334 Bool.false 109441295993952310047 281474976710656000 53450000040704313 82062500000000000000 203850299 524288 171 262144 (ep405 rfl) rfl) (Enclosure.sfrac_false_div 203850299 524288) (BSN.cos_reduce3 qz892 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 62478523823966910414848) qz281) 226375608064910080 72057594037927936 Bool.false 771576 1048576 61 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q3 203850299 524288 226375608064910080 72057594037927936 61 62478523823966910414848 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 771576 1048576 62478523823966910414848 75557863725914323419136 1775746449 2147483648 381142 380770 (ep407 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep409 := nat_lit 355363980510863348224146255216718683263089438588089540956527920048697275697281

noncomputable def ep410 := nat_lit 98866153784025280502716710876235973549004036635045999606392015060361398401

noncomputable def ep411 := nat_lit 1065894209225021994111433332228403577842170307690998530870370976115971104295041

noncomputable def ep412 := BSN.cos_dyadic_bound_f 1775746449 2147483648 3 2 1048576 381142 ep409 ep88 ep410 ep411 ep91 ep410 710056 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1775746449) qz266 0 2 ep409 ep88 ep410 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1775746449) qz267 0 2 ep411 ep91 ep410 rfl rfl rfl rfl) rfl rfl

noncomputable def ep413 := @Enclosure.Real.IsNear.sin_image qz334 qz892 Bool.false 203850299 524288 171 262144 Bool.true 710056 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz334 Bool.false 109441295993952310047 281474976710656000 53450000040704313 82062500000000000000 203850299 524288 171 262144 (ep405 rfl) rfl) (Enclosure.sfrac_false_div 203850299 524288) (BSN.sin_reduce3 qz892 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 62478523823966910414848) qz281) 226375608064910080 72057594037927936 Bool.false 710056 1048576 61 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q3 203850299 524288 226375608064910080 72057594037927936 61 62478523823966910414848 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 710056 1048576 62478523823966910414848 75557863725914323419136 1775746449 2147483648 381142 380770 (ep412 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz587 := (@Enclosure.Real.IsNear.recentre' qz333 Bool.false 218643 1048576 1 1048576 218643 1048576 1 1048576 (ep403 rfl rfl) rfl)

noncomputable def ep414 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz333 (Real.cos qz334)) (@HMul.hMul Real Real Real qz0 qz333 (@Neg.neg Real Real.instNeg (Real.sin qz334))) Bool.false 21087461421 137438953472 3606089162333 26166315156766720 Bool.false 19406096751 137438953472 3604625101683 26166315156766720 (@Enclosure.Real.IsNear.mulLit_ff qz333 (Real.cos qz334) 218643 1048576 1 1048576 96447 131072 32817979 49908285440 21087461421 137438953472 3606089162333 26166315156766720 qz587 (@Enclosure.Real.IsNear.recentre' (Real.cos qz334) Bool.false 771576 1048576 32817979 49908285440 96447 131072 32817979 49908285440 (ep408 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz333 (@Neg.neg Real Real.instNeg (Real.sin qz334)) 218643 1048576 1 1048576 88757 131072 32817979 49908285440 19406096751 137438953472 3604625101683 26166315156766720 qz587 (@Enclosure.Real.IsNear.neg (Real.sin qz334) Bool.true 88757 131072 32817979 49908285440 (@Enclosure.Real.IsNear.recentre' (Real.sin qz334) Bool.true 710056 1048576 32817979 49908285440 88757 131072 32817979 49908285440 (ep413 rfl rfl) rfl)) rfl)

noncomputable def ep415 := @ep314 21087461421 137438953472 3606089162333 26166315156766720 Bool.false 19406096751 137438953472 3604625101683 26166315156766720 Bool.false 24126281926217748709376 175541804683 274877906944 99916255548893 20933052125413376 Bool.true 943416585896421490688 13728518183 137438953472 99862110892587 20933052125413376 (ep315 (BSN.head_sum_c_succ qz12 22 23 rfl rfl) (ep401 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep402 ep414) rfl rfl

noncomputable abbrev qz893 := (@Nat.cast Real Real.instNatCast 24)

noncomputable abbrev qz336 := (@Inv.inv Real Real.instInv (Real.sqrt qz893))

noncomputable abbrev qz337 := (@HMul.hMul Real Real Real qz0 qz9 (Real.log (Enclosure.sfrac Bool.false 24 1)))

noncomputable def ep416 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz14 qz865 qz15) (Complex.mk (@HMul.hMul Real Real Real qz0 qz336 (Real.cos qz337)) (@HMul.hMul Real Real Real qz0 qz336 (@Neg.neg Real Real.instNeg (Real.sin qz337)))) Bool.true 39873111271 1099511627776 5626581506381 41866104250826752 Bool.false 220865773905 1099511627776 5658779646043 41866104250826752 (BSN.cpow_neg_s_mk qz9 124004 1000 24 (@Eq.refl Real qz9) rfl)

noncomputable abbrev qz894 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 24) qz265)

noncomputable def ep417 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz893) 5136953 1048576 1 1048576 107019 107020 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz893) (Real.sqrt qz894) Bool.false 5136953 1048576 1 1048576 (BSN.sqrt_natCast_div_one 24) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz894) Bool.false 5136953 1048576 1 1048576 5136953 1048576 1 1048576 (BSN.sqrt_enclosure 24 1 2568476 2568477 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep418 := BSN.log_dyadic_bound 8 40 4 3 430080000000 524288 190385 5875957760 3932160 212580 48 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 8) (BSN.artanhQ 40) 0 3 5875957760 430080000000 3932160 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz338 := (Real.log (Enclosure.sfrac Bool.false 24 1))

noncomputable def ep419 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz338 124004 1000 0 1 3578169457974519 1125899906842624 50000000038077 9519250000000000000 110926831366668063519 281474976710656000 53450000040704313 82062500000000000000 qz270 (BSN.isNear_log_sfrac 24 1 3578169457974519 1125899906842624 50000000038077 9519250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz894) Bool.false 60031721881041427759104 18889465931478580854784 1000000000761540 190385000000000000000 3578169457974519 1125899906842624 50000000038077 9519250000000000000 (BSN.log_rat_reduce_isNear 24 1 4 48 32 212580 524288 24973259072661432 36028797018963968 190385 1000000000000000 rfl rfl rfl rfl (ep418 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep420 := nat_lit 2860952896657156950842209977219323785102033763626035875710493725266527020307041

noncomputable def ep421 := nat_lit 6382985815239478171925660414085142206992127883190982214322144914513455665761

noncomputable def ep422 := nat_lit 8570092718340991896182778610829801070892117035111725662702836885970554149589601

noncomputable def ep423 := BSN.cos_dyadic_bound_f 2989702571 2147483648 3 2 1048576 381142 ep420 ep88 ep421 ep422 ep91 ep421 186289 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2989702571) qz266 0 2 ep420 ep88 ep421 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2989702571) qz267 0 2 ep422 ep91 ep421 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz588 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 51654331) (@Nat.cast Real Real.instNatCast 131072))

noncomputable def ep424 := @Enclosure.Real.IsNear.cos_image qz337 qz588 Bool.false 51654331 131072 171 262144 Bool.true 186289 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz337 Bool.false 110926831366668063519 281474976710656000 53450000040704313 82062500000000000000 51654331 131072 171 262144 (ep419 rfl) rfl) (Enclosure.sfrac_false_div 51654331 131072) (BSN.cos_reduce2 qz588 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26297701926538819141632) (@Nat.cast Real Real.instNatCast 18889465931478580854784)) 226375608064910080 72057594037927936 Bool.false 186289 1048576 62 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q2 51654331 131072 226375608064910080 72057594037927936 62 26297701926538819141632 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 186289 1048576 26297701926538819141632 18889465931478580854784 2989702571 2147483648 381142 380770 (ep423 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep425 := nat_lit 5144608825330690928978437430663514699418067072220311790507430989548137872020065

noncomputable def ep426 := nat_lit 13463641136927136135046123153924495887283616982099459765839131023716863117546081

noncomputable def ep427 := BSN.sin_dyadic_bound_f 2989702571 2147483648 3 2 1048576 381142 ep425 ep95 ep421 ep426 ep97 ep421 1031895 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2989702571) qz272 0 2 ep425 ep95 ep421 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2989702571) qz273 0 2 ep426 ep97 ep421 rfl rfl rfl rfl) rfl rfl

noncomputable def ep428 := @Enclosure.Real.IsNear.sin_image qz337 qz588 Bool.false 51654331 131072 171 262144 Bool.true 1031895 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz337 Bool.false 110926831366668063519 281474976710656000 53450000040704313 82062500000000000000 51654331 131072 171 262144 (ep419 rfl) rfl) (Enclosure.sfrac_false_div 51654331 131072) (BSN.sin_reduce2 qz588 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26297701926538819141632) (@Nat.cast Real Real.instNatCast 18889465931478580854784)) 226375608064910080 72057594037927936 Bool.false 1031895 1048576 62 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q2 51654331 131072 226375608064910080 72057594037927936 62 26297701926538819141632 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1031895 1048576 26297701926538819141632 18889465931478580854784 2989702571 2147483648 381142 380770 (ep427 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz589 := (@Enclosure.Real.IsNear.recentre' qz336 Bool.false 214039 1048576 1 1048576 214039 1048576 1 1048576 (ep417 rfl rfl) rfl)

noncomputable def ep429 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz336 (Real.cos qz337)) (@HMul.hMul Real Real Real qz0 qz336 (@Neg.neg Real Real.instNeg (Real.sin qz337))) Bool.true 39873111271 1099511627776 5626581506381 41866104250826752 Bool.false 220865773905 1099511627776 5658779646043 41866104250826752 (@Enclosure.Real.IsNear.mulLit_ft qz336 (Real.cos qz337) 214039 1048576 1 1048576 186289 1048576 32817979 49908285440 39873111271 1099511627776 5626581506381 41866104250826752 qz589 (@Enclosure.Real.IsNear.recentre' (Real.cos qz337) Bool.true 186289 1048576 32817979 49908285440 186289 1048576 32817979 49908285440 (ep424 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz336 (@Neg.neg Real Real.instNeg (Real.sin qz337)) 214039 1048576 1 1048576 1031895 1048576 32817979 49908285440 220865773905 1099511627776 5658779646043 41866104250826752 qz589 (@Enclosure.Real.IsNear.neg (Real.sin qz337) Bool.true 1031895 1048576 32817979 49908285440 (@Enclosure.Real.IsNear.recentre' (Real.sin qz337) Bool.true 1031895 1048576 32817979 49908285440 1031895 1048576 32817979 49908285440 (ep428 rfl rfl) rfl)) rfl)

noncomputable def ep430 := @ep312 39873111271 1099511627776 5626581506381 41866104250826752 Bool.false 220865773905 1099511627776 5658779646043 41866104250826752 Bool.false 182050018040224294109184 662294107461 1099511627776 205459092604167 41866104250826752 Bool.false 15260895448943822897152 111037628441 1099511627776 205383001431217 41866104250826752 (ep313 (BSN.head_sum_c_succ qz12 23 24 rfl rfl) (ep415 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep416 ep429) rfl rfl

theorem EMRow41.d9 : Enclosure.Complex.IsNear (BSN.headSumC qz12 25) Bool.false 662294107461 1099511627776 205459092604167 41866104250826752 Bool.false 111037628441 1099511627776 205383001431217 41866104250826752 := ep311 (BSN.head_sum_c_succ qz12 24 25 rfl rfl) (ep430 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

theorem EMRow41.d10 : @Eq Nat (BSN.factNat (Nat.mul 2 1)) 2 := @Eq.refl Nat 2

theorem EMRow41.d11 : @Eq Nat (Nat.pow 32 1) 32 := @Eq.refl Nat 32

theorem EMRow41.d12 : @Eq Nat (BSN.factNat (Nat.mul 2 2)) 24 := @Eq.refl Nat 24

noncomputable abbrev qz18 := (@HAdd.hAdd Complex Complex Complex qz260 qz259 qz553)

noncomputable def ep431 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz3 (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 2)) qz18) Bool.true 4324661817 62500 0 1 Bool.true 14891371054313 7812500 0 1

noncomputable def ep432 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.re qz18)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.im qz18)) 480507563 12500 0 1 961062001 31250 0 1

noncomputable def ep433 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.re qz18) 480507563 31250 0 1 5 2 0 1 480507563 12500

noncomputable abbrev qz590 := (@Nat.cast Complex Complex.instNatCast 1)

noncomputable abbrev qz19 := (@HAdd.hAdd Complex Complex Complex qz260 qz259 qz590)

noncomputable def ep434 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz3 (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)) qz19) Bool.true 480507563 31250 0 1 Bool.false 31001 125 0 1

noncomputable def ep435 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.re qz19)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.im qz19)) 3 4 0 1 961062001 62500 0 1

noncomputable def ep436 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.re qz19) 1 2 0 1 3 2 0 1 3 4

noncomputable def ep437 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)) qz12 Bool.false 1 2 0 1 Bool.false 124004 1000 0 1 (BSN.ascPochhammer_one_eval qz12)

noncomputable abbrev qz339 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz340 := (Enclosure.Real.IsNear.const Bool.false 1 2)

noncomputable def ep438 := ep437 (@Enclosure.Complex.IsNear.of_eq qz12 (Complex.mk qz339 qz9) Bool.false 1 2 0 1 Bool.false 124004 1000 0 1 (BSN.s_crit_mk qz9 Bool.false 124004 1000 (@Eq.refl Real qz9)) (@Enclosure.Complex.IsNear.mk qz339 qz9 Bool.false 1 2 0 1 Bool.false 124004 1000 0 1 qz340 qz270))

noncomputable def ep439 := @ep436 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 124004 1000 0 1 ep438)

noncomputable def ep440 := @Enclosure.Complex.IsNear.of_eq qz19 (Complex.mk (Enclosure.sfrac Bool.false 3 2) qz9) Bool.false 3 2 0 1 Bool.false 124004 1000 0 1 (BSN.s_add_nat_mk qz9 Bool.false 124004 1000 1 (@Eq.refl Real qz9))

noncomputable abbrev qz591 := (ep440 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz9 Bool.false 3 2 0 1 Bool.false 124004 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz270))

noncomputable def ep441 := ep439 (@Enclosure.Complex.IsNear.re_isNear qz19 Bool.false 3 2 0 1 Bool.false 124004 1000 0 1 qz591)

noncomputable def ep442 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.im qz19) 124004 1000 0 1 124004 1000 0 1 961062001 62500

noncomputable def ep443 := @ep442 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 124004 1000 0 1 ep438)

noncomputable def ep444 := ep443 (@Enclosure.Complex.IsNear.im_isNear qz19 Bool.false 3 2 0 1 Bool.false 124004 1000 0 1 qz591)

noncomputable def ep445 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)) qz19 Bool.true 480507563 31250 0 1 Bool.false 31001 125 0 1 (@ep435 3844060504 480507563 31250 0 1 (ep441 rfl) (ep444 rfl) rfl rfl)

noncomputable def ep446 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.im qz19)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.re qz19)) 31001 500 0 1 93003 500 0 1

noncomputable def ep447 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.im qz19) 1 2 0 1 124004 1000 0 1 31001 500

noncomputable def ep448 := @ep447 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 124004 1000 0 1 ep438)

noncomputable def ep449 := ep448 (@Enclosure.Complex.IsNear.im_isNear qz19 Bool.false 3 2 0 1 Bool.false 124004 1000 0 1 qz591)

noncomputable def ep450 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.re qz19) 124004 1000 0 1 3 2 0 1 93003 500

noncomputable def ep451 := @ep450 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 124004 1000 0 1 ep438)

noncomputable def ep452 := ep451 (@Enclosure.Complex.IsNear.re_isNear qz19 Bool.false 3 2 0 1 Bool.false 124004 1000 0 1 qz591)

noncomputable abbrev qz592 := (ep434 (BSN.ascPochhammer_succ_eval_c 1 2 qz12 rfl) (ep445 (@ep446 62002000 31001 125 0 1 (ep449 rfl) (ep452 rfl) rfl rfl)))

noncomputable def ep453 := @ep433 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 480507563 31250 0 1 Bool.false 31001 125 0 1 qz592)

noncomputable def ep454 := @Enclosure.Complex.IsNear.of_eq qz18 (Complex.mk (Enclosure.sfrac Bool.false 5 2) qz9) Bool.false 5 2 0 1 Bool.false 124004 1000 0 1 (BSN.s_add_nat_mk qz9 Bool.false 124004 1000 2 (@Eq.refl Real qz9))

noncomputable abbrev qz593 := (ep454 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz9 Bool.false 5 2 0 1 Bool.false 124004 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz270))

noncomputable def ep455 := ep453 (@Enclosure.Complex.IsNear.re_isNear qz18 Bool.false 5 2 0 1 Bool.false 124004 1000 0 1 qz593)

noncomputable def ep456 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.im qz18) 31001 125 0 1 124004 1000 0 1 961062001 31250

noncomputable def ep457 := @ep456 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 480507563 31250 0 1 Bool.false 31001 125 0 1 qz592)

noncomputable def ep458 := ep457 (@Enclosure.Complex.IsNear.im_isNear qz18 Bool.false 5 2 0 1 Bool.false 124004 1000 0 1 qz593)

noncomputable def ep459 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 2)) qz18 Bool.true 4324661817 62500 0 1 Bool.true 14891371054313 7812500 0 1 (@ep432 27029136356250 4324661817 62500 0 1 (ep455 rfl) (ep458 rfl) rfl rfl)

noncomputable def ep460 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.im qz18)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.re qz18)) 14896214960563 7812500 0 1 31001 50 0 1

noncomputable def ep461 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.im qz18) 480507563 31250 0 1 124004 1000 0 1 14896214960563 7812500

noncomputable def ep462 := @ep461 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 480507563 31250 0 1 Bool.false 31001 125 0 1 qz592)

noncomputable def ep463 := ep462 (@Enclosure.Complex.IsNear.im_isNear qz18 Bool.false 5 2 0 1 Bool.false 124004 1000 0 1 qz593)

noncomputable def ep464 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.re qz18) 31001 125 0 1 5 2 0 1 31001 50

noncomputable def ep465 := @ep464 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 480507563 31250 0 1 Bool.false 31001 125 0 1 qz592)

noncomputable def ep466 := ep465 (@Enclosure.Complex.IsNear.re_isNear qz18 Bool.false 5 2 0 1 Bool.false 124004 1000 0 1 qz593)

noncomputable abbrev qz594 := (ep459 (@ep460 744568552715650 14891371054313 7812500 0 1 (ep463 rfl) (ep466 rfl) rfl rfl))

theorem EMRow41.d13 : Enclosure.Complex.IsNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 4324661817 62500 0 1 Bool.true 14891371054313 7812500 0 1 := ep431 (BSN.ascPochhammer_succ_eval_c 2 3 qz12 rfl) qz594

theorem EMRow41.d14 : @Eq Nat (Nat.pow 32 3) 32768 := @Eq.refl Nat 32768

noncomputable def ep467 := nat_lit 11819055016201341858655114268754921741803

noncomputable def ep468 := nat_lit 25529404322578096628106830807040000000000

noncomputable def ep469 := nat_lit 1859128671666440880133288433767194713953821394561

noncomputable def ep470 := nat_lit 308450077331139392649907107538736775168000000000000

noncomputable abbrev qz595 := (@instHSub Complex Complex.instSub)

noncomputable abbrev qz20 := qz595

noncomputable abbrev qz21 := (Complex.Stirling.logGammaStirling 2 qz255)

noncomputable abbrev qz596 := (@HAdd.hAdd Complex Complex Complex qz813 qz814 (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I (@HDiv.hDiv Complex Complex Complex qz815 (↑(Enclosure.sfrac Bool.false 124004 1000)) (2 : Complex))))

noncomputable abbrev qz341 := qz596

noncomputable abbrev qz22 := qz341

noncomputable abbrev qz342 := (@HMul.hMul Real Real Real qz0 (@HDiv.hDiv Real Real Real qz1 qz9 (2 : Real)) (Real.log Real.pi))

noncomputable abbrev qz597 := (@instHSub Real Real.instSub)

noncomputable def ep471 := Complex.re (@HMul.hMul Complex Complex Complex qz3 (Complex.exp (@HMul.hMul Complex Complex Complex qz3 Complex.I ↑(@HSub.hSub Real Real Real qz597 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz21 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz22 (@Nat.cast Complex Complex.instNatCast j))))) qz342))) (zetaApproximant qz12 2 32))

noncomputable def ep472 := @Enclosure.Real.IsNear.of_eq ep471 (@HSub.hSub Real Real Real qz597 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz597 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz21 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz22 (@Nat.cast Complex Complex.instNatCast j))))) qz342)) (Complex.re (zetaApproximant qz12 2 32))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz597 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz21 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz22 (@Nat.cast Complex Complex.instNatCast j))))) qz342)) (Complex.im (zetaApproximant qz12 2 32))))

noncomputable def ep473 := nat_lit 157588345139390640550381877331838245619

noncomputable def ep474 := @Enclosure.Real.IsNear.subLit_tt_n (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz597 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz21 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz22 (@Nat.cast Complex Complex.instNatCast j))))) qz342)) (Complex.re (zetaApproximant qz12 2 32))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz597 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz21 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz22 (@Nat.cast Complex Complex.instNatCast j))))) qz342)) (Complex.im (zetaApproximant qz12 2 32))) ep473

noncomputable def ep475 := nat_lit 340392057634374621708091077427200000000

noncomputable def ep476 := nat_lit 1857045067560112411693379540806219375278338730383

noncomputable def ep477 := nat_lit 35434626478091311763265566473339811

noncomputable def ep478 := nat_lit 12764702161289048314053415403520000000000

noncomputable def ep479 := nat_lit 1041802053164234219954446480487669337741332089

noncomputable def ep480 := nat_lit 154225038665569696324953553769368387584000000000000

noncomputable def ep481 := nat_lit 2011556228129325818138830050690336616490468278375071391239552379964620800000000

noncomputable def ep482 := @Enclosure.Real.IsNear.mulLit_tf (Real.cos (@HSub.hSub Real Real Real qz597 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz21 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz22 (@Nat.cast Complex Complex.instNatCast j))))) qz342)) (Complex.re (zetaApproximant qz12 2 32)) 1048575 1048576 17206409

noncomputable def ep483 := nat_lit 11271607548772665800041619149691599

noncomputable def ep484 := nat_lit 24346737215593430164439040000000000

noncomputable def ep485 := nat_lit 27157691104156740227923410937198123819

noncomputable def ep486 := nat_lit 4635253564790755201856726630400000000000

noncomputable def ep487 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz597 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz21 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz22 (@Nat.cast Complex Complex.instNatCast j))))) qz342)) Bool.true 1048575 1048576 17206409

noncomputable abbrev qz895 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 64237083) qz280)

noncomputable def ep488 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz597 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz21 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz22 (@Nat.cast Complex Complex.instNatCast j))))) qz342) qz895 Bool.false 64237083 524288 89

noncomputable def ep489 := nat_lit 198645243458809726812971910109

noncomputable def ep490 := nat_lit 1621295865853378560000000000

noncomputable def ep491 := nat_lit 8157825292457760698557737491081047

noncomputable def ep492 := nat_lit 24114876048476209152000000000000000000

noncomputable def ep493 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz597 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz21 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz22 (@Nat.cast Complex Complex.instNatCast j))))) qz342) Bool.false ep489 ep490 ep491 ep492

noncomputable def ep494 := nat_lit 313717569598791656981291910109

noncomputable def ep495 := nat_lit 2454202303727818682557737491081047

noncomputable def ep496 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz21 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz22 (@Nat.cast Complex Complex.instNatCast j))))) qz342 ep494 ep490 ep495 ep492 2325726021 32768000

noncomputable def ep497 := nat_lit 6509207337658277128207463550451712000

noncomputable def ep498 := nat_lit 1264680851530986353788944059

noncomputable def ep499 := nat_lit 12970366926827028480000000

noncomputable def ep500 := nat_lit 4218111050388500960602941455103277

noncomputable def ep501 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz20 qz21 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz22 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true ep498 ep499 ep500 ep492 Bool.false ep494 ep490

noncomputable def ep502 := nat_lit 1050528327743852521468944059

noncomputable def ep503 := nat_lit 4091447310338178487536464853759277

noncomputable def ep504 := nat_lit 323721539340251843861291910109

noncomputable def ep505 := nat_lit 2200874824639998530460785072777047

noncomputable def ep506 := @Enclosure.Complex.IsNear.subLitP qz21 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz22 (@Nat.cast Complex Complex.instNatCast j))) Bool.true ep502 ep499 ep503 ep492 Bool.false ep504 ep490 ep505

noncomputable def ep507 := nat_lit 2847808105848775859317401410484827305541632

noncomputable def ep508 := nat_lit 44151822798271742209304128315310958027210752

noncomputable abbrev qz343 := (@HSub.hSub Complex Complex Complex qz595 qz544 qz550)

noncomputable abbrev qz344 := (Complex.log qz544)

noncomputable abbrev qz23 := (@HSub.hSub Complex Complex Complex qz595 (@HMul.hMul Complex Complex Complex qz253 qz343 qz344) qz255)

noncomputable abbrev qz345 := qz550

noncomputable abbrev qz24 := qz345

noncomputable abbrev qz598 := qz815

noncomputable abbrev qz346 := qz598

noncomputable abbrev qz25 := qz346

noncomputable abbrev qz26 := (@instHMul Nat instMulNat)

noncomputable abbrev qz599 := (@instHPow Complex Int (@ZPow.toPow Complex (@DivInvMonoid.toZPow Complex Complex.instDivInvMonoid)))

noncomputable abbrev qz27 := qz599

noncomputable abbrev qz28 := (@instHSub Int Int.instSub)

noncomputable abbrev qz347 := (@OfNat.ofNat Int 1 (@instOfNat 1))

noncomputable abbrev qz29 := qz347

noncomputable abbrev qz30 := (@instHMul Int Int.instMul)

noncomputable abbrev qz600 := (@OfNat.ofNat Int 2 (@instOfNat 2))

noncomputable abbrev qz31 := qz600

noncomputable abbrev qz896 := (@HMul.hMul Complex Complex Complex qz3 qz24 ↑qz251)

noncomputable def ep509 := @Enclosure.Complex.IsNear.of_eq qz21 (@HAdd.hAdd Complex Complex Complex qz13 (@HAdd.hAdd Complex Complex Complex qz13 qz23 qz896) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz20 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz27 qz5 (@HSub.hSub Int Int Int qz28 qz29 (@HMul.hMul Int Int Int qz30 qz31 (@Nat.cast Int instNatCastInt k)))))) Bool.true ep502

noncomputable def ep510 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz13 qz23 qz896) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz20 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz27 qz5 (@HSub.hSub Int Int Int qz28 qz29 (@HMul.hMul Int Int Int qz30 qz31 (@Nat.cast Int instNatCastInt k))))) Bool.true 364767193449221252809 4503599627370496000

noncomputable def ep511 := nat_lit 2168920000357580508089891

noncomputable def ep512 := nat_lit 4731158985369364510546332339990423891083264000

noncomputable def ep513 := nat_lit 291582440788912313107836486649648627374148812800

noncomputable def ep514 := @ep510 12920652231714729529 76154000000000000000000 Bool.false 179846504589029000801 900719925474099200 1737550006528035111 19038500000000000000000 Bool.false 1189389904686620975941 ep499 1069571988698213 ep499 Bool.true ep511 ep490 1950428961518210563 ep490 Bool.true ep512 ep502 ep499 ep503 ep492 Bool.false ep513

noncomputable def ep515 := @Enclosure.Complex.IsNear.addLitP qz23 qz896 Bool.true 368905720856431748809 4503599627370496000 3193850000982881601 19038500000000000000000

noncomputable def ep516 := nat_lit 47810765579776328048181248

noncomputable def ep517 := @ep515 Bool.false 179846504589029000801 900719925474099200 1737550006528035111 19038500000000000000000 Bool.false 120447 131072 1 524288 Bool.false 0 1 0 1 Bool.true ep516 364767193449221252809 4503599627370496000 12920652231714729529 76154000000000000000000 Bool.false 179846504589029000801 179846504589029000801 900719925474099200

noncomputable abbrev qz32 := (@HMul.hMul Complex Complex Complex qz253 qz343 qz344)

noncomputable def ep518 := @Enclosure.Complex.IsNear.subLitP qz32 qz5 Bool.true 349765422440107140809 4503599627370496000 3193850000982881601 19038500000000000000000 Bool.false 1178464707041370496997

noncomputable def ep519 := nat_lit 1475622883425726995236000

noncomputable def ep520 := nat_lit 3596930091780580016020000

noncomputable def ep521 := @ep518 4503599627370496000 1737550006528035111 19038500000000000000000 Bool.false 17000 4000 0 1 Bool.false 248008 4000 0 1 Bool.true ep519 368905720856431748809 4503599627370496000 3193850000982881601 19038500000000000000000 Bool.false ep520 179846504589029000801 900719925474099200 1737550006528035111 19038500000000000000000

noncomputable abbrev qz33 := qz343

noncomputable abbrev qz34 := qz344

noncomputable def ep522 := @Enclosure.Complex.IsNear.mul qz33 qz34 Bool.true 349765422440107140809 4503599627370496000 3193850000982881601 19038500000000000000000 Bool.false 1178464707041370496997 4503599627370496000 1737550006528035111

noncomputable def ep523 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re qz33) (Complex.re qz34)) (@HMul.hMul Real Real Real qz0 (Complex.im qz33) (Complex.im qz34)) 557929811694299955 36028797018963968 300000001256541 60923200000000000000 26219165556368414699 281474976710656000

noncomputable def ep524 := nat_lit 787601713084175319569909406742085632

noncomputable def ep525 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz33) (Complex.re qz34) 15000 4000 0 1 37195320779619997 9007199254740992 100000000418847 76154000000000000000

noncomputable def ep526 := @Enclosure.Complex.IsNear.re_isNear qz33 Bool.false 15000 4000 0 1 Bool.false 248008 4000 0 1

noncomputable def ep527 := @Enclosure.Complex.IsNear.of_eq qz33 (Complex.mk (Enclosure.sfrac Bool.false 15000 4000) qz258) Bool.false 15000 4000 0 1 Bool.false 248008 4000 0

noncomputable abbrev qz601 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 17000 4000) qz258))

noncomputable def ep528 := @Enclosure.Complex.IsNear.of_eq qz34 qz601 Bool.false 37195320779619997 9007199254740992 100000000418847 76154000000000000000 Bool.false 845752251745699 562949953421312 200000000038077 76154000000000000000

noncomputable def ep529 := nat_lit 594466376947520792577211899471573072768612410430727673164307351417816194682356575456570707233066808836758196715520

noncomputable def ep530 := nat_lit 19805192289581212440922463225896012698237464059879685681981648216263395824581351821148512501282331930601302523904

noncomputable def ep531 := nat_lit 401557539463445952375200608431116089945069136501818884197561077104749616939724224315946383458746130308792320

noncomputable def ep532 := BSN.log_dyadic_bound 29028968064 94564968064 6 5 ep529 1048576 380770 ep530 ep531 665218 123593936128 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 29028968064) (BSN.artanhQ 94564968064) 0 5 ep530 ep529 ep531 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz602 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable def ep533 := @Enclosure.Real.IsNear.mulLit_ff qz339 (Real.log (Enclosure.sfrac Bool.false 61796968064 16000000)) 1 2 0 1 37195320779619997 4503599627370496 100000000418847 38077000000000000000 37195320779619997 9007199254740992 100000000418847 76154000000000000000 qz340 (BSN.isNear_log_sfrac 61796968064 16000000 37195320779619997 4503599627370496 100000000418847 38077000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 61796968064) qz602)) Bool.false 312016965454486543794176 37778931862957161709568 1000000004188470 380770000000000000000 37195320779619997 4503599627370496 100000000418847 38077000000000000000 (BSN.log_rat_reduce_isNear 61796968064 16000000 11 123593936128 65536000000 665218 1048576 24973259072661432 36028797018963968 380770 1000000000000000 rfl rfl rfl rfl (ep532 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep534 := BSN.arctan_dyadic_bound_f 17000 248008 1 0 1048576 380770 0 1 1 0 1 1 71763 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 17000) (BSN.arctanEvenQ 248008) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 17000) (BSN.arctanOddQ 248008) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz348 := (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz349 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 2) Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable abbrev qz603 := (@Nat.cast Real Real.instNatCast 17000)

noncomputable abbrev qz604 := (@Nat.cast Real Real.instNatCast 248008)

noncomputable def ep535 := @Enclosure.Real.IsNear.subLit_ff_p qz348 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz603 qz604)) 884279719003555 562949953421312 1 2000000000000000 71763 1048576 1 380770 886835513126498074624 845752251745699 562949953421312 200000000038077 76154000000000000000 qz349 (ep534 rfl) rfl rfl

noncomputable abbrev qz605 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 248008) (@Nat.cast Real Real.instNatCast 17000)))

noncomputable def ep536 := @Enclosure.Complex.IsNear.re_isNear qz34 Bool.false 37195320779619997 9007199254740992 100000000418847 76154000000000000000 Bool.false 845752251745699 562949953421312 200000000038077 76154000000000000000 (ep528 (@congrArg Complex Complex qz5 qz546 Complex.log (BSN.w_shift_mk qz9 Bool.false 124004 1000 4 (@Eq.refl Real qz9) rfl)) (@Enclosure.Complex.IsNear.of_parts qz601 Bool.false 37195320779619997 9007199254740992 100000000418847 76154000000000000000 Bool.false 845752251745699 562949953421312 200000000038077 76154000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz601) (@HMul.hMul Real Real Real qz0 qz339 (Real.log (Enclosure.sfrac Bool.false 61796968064 16000000))) Bool.false 37195320779619997 9007199254740992 100000000418847 76154000000000000000 (Enclosure.clog_re_eq 17000 248008 4000 61796968064 16000000 rfl rfl rfl) (ep533 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz601) qz605 Bool.false 845752251745699 562949953421312 200000000038077 76154000000000000000 (Enclosure.clog_im_eq 17000 248008 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz605 (@HSub.hSub Real Real Real qz597 qz348 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz603 qz604))) Bool.false 845752251745699 562949953421312 200000000038077 76154000000000000000 (BSN.arctan_recip 248008 17000 rfl rfl) ep535))))

noncomputable def ep537 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz33) (Complex.im qz34) 248008 4000 0 1 845752251745699 562949953421312 200000000038077 76154000000000000000

noncomputable def ep538 := @Enclosure.Complex.IsNear.im_isNear qz33 Bool.false 15000 4000 0 1 Bool.false 248008 4000 0 1

noncomputable def ep539 := @Enclosure.Complex.IsNear.im_isNear qz34 Bool.false 37195320779619997 9007199254740992 100000000418847 76154000000000000000 Bool.false 845752251745699 562949953421312 200000000038077 76154000000000000000 (ep528 (@congrArg Complex Complex qz5 qz546 Complex.log (BSN.w_shift_mk qz9 Bool.false 124004 1000 4 (@Eq.refl Real qz9) rfl)) (@Enclosure.Complex.IsNear.of_parts qz601 Bool.false 37195320779619997 9007199254740992 100000000418847 76154000000000000000 Bool.false 845752251745699 562949953421312 200000000038077 76154000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz601) (@HMul.hMul Real Real Real qz0 qz339 (Real.log (Enclosure.sfrac Bool.false 61796968064 16000000))) Bool.false 37195320779619997 9007199254740992 100000000418847 76154000000000000000 (Enclosure.clog_re_eq 17000 248008 4000 61796968064 16000000 rfl rfl rfl) (ep533 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz601) qz605 Bool.false 845752251745699 562949953421312 200000000038077 76154000000000000000 (Enclosure.clog_im_eq 17000 248008 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz605 (@HSub.hSub Real Real Real qz597 qz348 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz603 qz604))) Bool.false 845752251745699 562949953421312 200000000038077 76154000000000000000 (BSN.arctan_recip 248008 17000 rfl rfl) ep535))))

noncomputable abbrev qz350 := (@ep527 1 (BSN.w_sub_half_mk qz9 Bool.false 124004 1000 4 (@Eq.refl Real qz9) rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 15000 4000) (Enclosure.sfrac Bool.false 248008 4000) Bool.false 15000 4000 0 1 Bool.false 248008 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 15000 4000) (Enclosure.Real.IsNear.const Bool.false 248008 4000)))

noncomputable def ep540 := @ep523 213800000040704313 1313000000000000000000 ep524 349765422440107140809 4503599627370496000 3193850000982881601 19038500000000000000000 (@ep525 557929811694299955 36028797018963968 300000001256541 60923200000000000000 (ep526 qz350) ep536 rfl) (@ep537 26219165556368414699 281474976710656000 213800000040704313 1313000000000000000000 (ep538 qz350) ep539 rfl) rfl

noncomputable def ep541 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re qz33) (Complex.im qz34)) (@HMul.hMul Real Real Real qz0 (Complex.im qz33) (Complex.re qz34)) 12686283776185485 2251799813685248 600000000114231 60923200000000000000 1153092139488999526997 4503599627370496000

noncomputable def ep542 := nat_lit 2653666607750398451972246711887200256

noncomputable def ep543 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz33) (Complex.im qz34) 15000 4000 0 1 845752251745699 562949953421312 200000000038077 76154000000000000000

noncomputable def ep544 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz33) (Complex.re qz34) 248008 4000 0 1 37195320779619997 9007199254740992 100000000418847 76154000000000000000

noncomputable def ep545 := @ep541 106900000447747443 1313000000000000000000 ep542 1178464707041370496997 4503599627370496000 1737550006528035111 19038500000000000000000 (@ep543 12686283776185485 2251799813685248 600000000114231 60923200000000000000 (ep526 qz350) ep539 rfl) (@ep544 1153092139488999526997 4503599627370496000 106900000447747443 1313000000000000000000 (ep538 qz350) ep536 rfl) rfl

noncomputable def ep546 := ep521 (@ep522 19038500000000000000000 (ep540 rfl) (ep545 rfl)) qz11 rfl rfl rfl rfl rfl rfl

noncomputable def ep547 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re qz24) (Complex.re ↑qz251)) (@HMul.hMul Real Real Real qz0 (Complex.im qz24) (Complex.im ↑qz251)) 120447 131072 1 524288 0 1 0 1 120447 120447

noncomputable def ep548 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz24) (Complex.re ↑qz251) 1 2 0 1 120447 65536 1 262144 120447 131072 1 524288

noncomputable abbrev qz351 := (@Enclosure.Complex.IsNear.of_eq qz24 (Complex.mk (Enclosure.sfrac Bool.false 1 2) (Enclosure.sfrac Bool.false 0 1)) Bool.false 1 2 0 1 Bool.false 0 1 0 1 BSN.half_c_mk (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 2) (Enclosure.sfrac Bool.false 0 1) Bool.false 1 2 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 2) (Enclosure.Real.IsNear.const Bool.false 0 1)))

noncomputable def ep549 := ep548 (@Enclosure.Complex.IsNear.re_isNear qz24 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz351) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz251) qz251 Bool.false 120447 65536 1 262144 (Complex.ofReal_re qz251) EMRow41.d4)

noncomputable def ep550 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz24) (Complex.im ↑qz251) 0 1 0 1 0 1 0 1 0 1 0 1

noncomputable def ep551 := ep550 (@Enclosure.Complex.IsNear.im_isNear qz24 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz351) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz251) qz262 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz251) (0 : Real) qz262 (Complex.ofReal_im qz251) Enclosure.sfrac_zero_eq) qz274)

noncomputable def ep552 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re qz24) (Complex.im ↑qz251)) (@HMul.hMul Real Real Real qz0 (Complex.im qz24) (Complex.re ↑qz251)) 0 1 0 1 0 1 0 1 0 0

noncomputable def ep553 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz24) (Complex.im ↑qz251) 1 2 0 1 0 1 0 1 0 1 0 1

noncomputable def ep554 := ep553 (@Enclosure.Complex.IsNear.re_isNear qz24 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz351) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz251) qz262 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz251) (0 : Real) qz262 (Complex.ofReal_im qz251) Enclosure.sfrac_zero_eq) qz274)

noncomputable def ep555 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz24) (Complex.re ↑qz251) 0 1 0 1 120447 65536 1 262144 0 1 0 1

noncomputable def ep556 := ep555 (@Enclosure.Complex.IsNear.im_isNear qz24 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz351) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz251) qz251 Bool.false 120447 65536 1 262144 (Complex.ofReal_re qz251) EMRow41.d4)

noncomputable def ep557 := @ep517 1737550006528035111 19038500000000000000000 (ep546 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz24 (↑qz251) Bool.false 120447 131072 1 524288 Bool.false 0 1 0 1 (@ep547 131072 1 524288 (ep549 rfl) (ep551 rfl) rfl rfl) (@ep552 1 0 1 (ep554 rfl) (ep556 rfl) rfl rfl))

noncomputable abbrev qz35 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)

noncomputable abbrev qz36 := (@HMul.hMul Complex Complex Complex qz253 (@HMul.hMul Complex Complex Complex qz253 (2 : Complex) qz553) (@HSub.hSub Complex Complex Complex qz595 (@HMul.hMul Complex Complex Complex qz253 (2 : Complex) qz553) (1 : Complex)))

noncomputable abbrev qz37 := (@HPow.hPow Complex Int Complex qz599 qz255 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) qz347 (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) qz600 (@Nat.cast Int instNatCastInt 2))))

noncomputable def ep558 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz20 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz27 qz5 (@HSub.hSub Int Int Int qz28 qz29 (@HMul.hMul Int Int Int qz30 qz31 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz13 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz20 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz27 qz5 (@HSub.hSub Int Int Int qz28 qz29 (@HMul.hMul Int Int Int qz30 qz31 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz35)) qz36) qz37)) Bool.false 1189389904686620975941 ep499 1069571988698213 ep499

noncomputable def ep559 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz20 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz27 qz5 (@HSub.hSub Int Int Int qz28 qz29 (@HMul.hMul Int Int Int qz30 qz31 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz35)) qz36) qz37) Bool.false 18904357 206158430208 17 206158430208 Bool.true

noncomputable def ep560 := nat_lit 245202755655436522579881495625728

noncomputable def ep561 := nat_lit 55892642815056699527598871639228416000

noncomputable def ep562 := @ep559 34473763021 25769803776000 31001 25769803776000 Bool.false 30601948700975941 ep499 24468698213 ep499 Bool.true 18368347094748089891 ep490 14686958210563 ep490 Bool.false ep560 1189389904686620975941 ep499 1069571988698213 ep499 Bool.true ep561 ep511 ep490 1950428961518210563

noncomputable abbrev qz38 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)

noncomputable abbrev qz39 := (@HMul.hMul Complex Complex Complex qz253 (@HMul.hMul Complex Complex Complex qz253 (2 : Complex) qz590) (@HSub.hSub Complex Complex Complex qz595 (@HMul.hMul Complex Complex Complex qz253 (2 : Complex) qz590) (1 : Complex)))

noncomputable abbrev qz40 := (@HPow.hPow Complex Int Complex qz599 qz255 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) qz347 (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) qz600 (@Nat.cast Int instNatCastInt 1))))

noncomputable def ep563 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz20 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz27 qz5 (@HSub.hSub Int Int Int qz28 qz29 (@HMul.hMul Int Int Int qz30 qz31 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz13 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz20 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz27 qz5 (@HSub.hSub Int Int Int qz28 qz29 (@HMul.hMul Int Int Int qz30 qz31 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz38)) qz39) qz40)) Bool.false 18904357 206158430208 17 206158430208

noncomputable def ep564 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz20 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz27 qz5 (@HSub.hSub Int Int Int qz28 qz29 (@HMul.hMul Int Int Int qz30 qz31 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz38)) qz39) qz40) Bool.false 0 1 0 1 Bool.false

noncomputable def ep565 := @ep564 0 1 0 1 Bool.false 18904357 206158430208 17 206158430208 Bool.true 34473763021 25769803776000 31001 25769803776000 Bool.false 18904357 18904357 206158430208 17 206158430208 Bool.true 34473763021 34473763021 25769803776000 31001

noncomputable def ep566 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz20 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz27 qz5 (@HSub.hSub Int Int Int qz28 qz29 (@HMul.hMul Int Int Int qz30 qz31 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz262 qz262) Bool.false 0 1 0 1 Bool.false

noncomputable def ep567 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz38)) qz39) qz40 Bool.false 18904357 206158430208 17 206158430208 Bool.true 34473763021 25769803776000 31001 25769803776000

noncomputable def ep568 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz38)) qz39)) (Complex.re qz40)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz38)) qz39)) (Complex.im qz40)) 18904357 206158430208 17 206158430208 0 1 0

noncomputable def ep569 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz38)) qz39)) (Complex.re qz40) 1 12 0 1 18904357 17179869184 17 17179869184 18904357

noncomputable def ep570 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz38)) qz39) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz262) Bool.false 1 12 0 1 Bool.false 0 1 0 1

noncomputable abbrev qz606 := (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 12) qz262 Bool.false 1 12 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 12) qz274)

noncomputable def ep571 := @Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz38)) qz39) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep570 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz606)

noncomputable def ep572 := @Enclosure.Complex.IsNear.re_isNear qz40 Bool.false 18904357 17179869184 17 17179869184 Bool.true 34473763021 2147483648000 31001 2147483648000

noncomputable def ep573 := @Enclosure.Complex.IsNear.of_eq qz40 (@Inv.inv Complex Complex.instInv qz6) Bool.false 18904357 17179869184 17 17179869184 Bool.true 34473763021 2147483648000 31001

noncomputable def ep574 := @Enclosure.Complex.IsNear.of_parts (@Inv.inv Complex Complex.instInv qz6) Bool.false 18904357 17179869184 17 17179869184 Bool.true 34473763021 2147483648000 31001

noncomputable abbrev qz352 := (@MonoidWithZeroHom Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz353 := (@MonoidWithZeroHom.funLike Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable def ep575 := @Enclosure.Real.IsNear.mulLit_ff qz7 (@Inv.inv Real Real.instInv (@DFunLike.coe qz352 Complex (fun (x : Complex) => Real) qz353 Complex.normSq qz6)) 17000 4000 0 1 1112021 4294967296 1 4294967296

noncomputable def ep576 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz352 Complex (fun (x : Complex) => Real) qz353 Complex.normSq qz6)) Bool.false 1112021 4294967296 1 4294967296 1112021 4294967296 1

noncomputable abbrev qz607 := (@instHAdd Real Real.instAdd)

noncomputable def ep577 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz352 Complex (fun (x : Complex) => Real) qz353 Complex.normSq qz6) (@HAdd.hAdd Real Real Real qz607 (@HMul.hMul Real Real Real qz0 qz7 qz7) (@HMul.hMul Real Real Real qz0 qz8 qz8)) Bool.false 482788813 125000 0 1

noncomputable def ep578 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz7 qz7) (@HMul.hMul Real Real Real qz0 qz8 qz8) 289 16 0 1 961062001 250000

noncomputable def ep579 := @Enclosure.Real.IsNear.mulLit_ff qz7 qz7 17000 4000 0 1 17000 4000 0 1

noncomputable def ep580 := @Enclosure.Real.IsNear.mulLit_ff qz8 qz8 248008 4000 0 1 248008 4000 0 1

noncomputable def ep581 := @ep578 0 1 15449242016 482788813 125000 0 1 (@ep579 289 16 0 1 (ep32 qz10) (ep32 qz10) rfl) (@ep580 961062001 250000 0 1 (ep37 qz10) (ep37 qz10) rfl)

noncomputable def ep582 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz352 Complex (fun (x : Complex) => Real) qz353 Complex.normSq qz6) 482788813 125000 0 1 556010 556011 2147483648 (ep577 (Enclosure.Complex.normSq_eq_mul_add_mul qz6) (ep581 rfl rfl)) rfl

noncomputable def ep583 := @Enclosure.Real.IsNear.of_eq (Complex.re (@Inv.inv Complex Complex.instInv qz6)) (@HMul.hMul Real Real Real qz0 qz7 (@Inv.inv Real Real.instInv (@DFunLike.coe qz352 Complex (fun (x : Complex) => Real) qz353 Complex.normSq qz6))) Bool.false 18904357 17179869184 17 17179869184 (Enclosure.Complex.inv_re_eq_mul qz6) (@ep575 18904357 17179869184 17 17179869184 (ep32 qz10) (@ep576 4294967296 (ep582 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep584 := @Enclosure.Real.IsNear.of_eq (Complex.im (@Inv.inv Complex Complex.instInv qz6)) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz8) (@Inv.inv Real Real.instInv (@DFunLike.coe qz352 Complex (fun (x : Complex) => Real) qz353 Complex.normSq qz6))) Bool.true 34473763021 2147483648000 31001 2147483648000 (Enclosure.Complex.inv_im_eq_mul qz6)

noncomputable def ep585 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz8) (@Inv.inv Real Real.instInv (@DFunLike.coe qz352 Complex (fun (x : Complex) => Real) qz353 Complex.normSq qz6)) 248008 4000 0 1 1112021 4294967296 1

noncomputable def ep586 := @ep585 4294967296 34473763021 2147483648000 31001 2147483648000 (@Enclosure.Real.IsNear.neg qz8 Bool.false 248008 4000 0 1 (ep37 qz10)) (@ep576 4294967296 (ep582 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep587 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz38)) qz39)) (Complex.im qz40) 0 1 0 1 34473763021 2147483648000 31001 2147483648000 0

noncomputable def ep588 := @Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz38)) qz39) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep570 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz606)

noncomputable def ep589 := @Enclosure.Complex.IsNear.im_isNear qz40 Bool.false 18904357 17179869184 17 17179869184 Bool.true 34473763021 2147483648000 31001 2147483648000

noncomputable abbrev qz608 := (@ep573 2147483648000 (BSN.zpow_one_sub_two_mul qz5 1 1 rfl rfl) (@ep574 2147483648000 ep583 (ep584 ep586)))

noncomputable def ep590 := @ep568 1 18904357 18904357 206158430208 17 206158430208 (@ep569 206158430208 17 206158430208 ep571 (ep572 qz608) rfl) (@ep587 1 0 1 ep588 (ep589 qz608) rfl) rfl

noncomputable def ep591 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz38)) qz39)) (Complex.im qz40)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz38)) qz39)) (Complex.re qz40)) 34473763021 25769803776000 31001 25769803776000 0 1 0

noncomputable def ep592 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz38)) qz39)) (Complex.im qz40) 1 12 0 1 34473763021 2147483648000 31001 2147483648000 34473763021

noncomputable def ep593 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz38)) qz39)) (Complex.re qz40) 0 1 0 1 18904357 17179869184 17 17179869184 0

noncomputable def ep594 := @ep591 1 34473763021 34473763021 25769803776000 31001 25769803776000 (@ep592 25769803776000 31001 25769803776000 ep571 (ep589 qz608) rfl) (@ep593 1 0 1 ep588 (ep572 qz608) rfl) rfl

noncomputable abbrev qz354 := (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 0 1) (Enclosure.sfrac Bool.false 0 1) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 0 1) (Enclosure.Real.IsNear.const Bool.false 0 1))

noncomputable def ep595 := @ep565 25769803776000 (@ep566 0 1 0 1 (BSN.stirling_sum_base qz5) qz354) (ep567 (ep590 rfl) (ep594 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep596 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz35)) qz36) qz37 Bool.false 30601948700975941 ep499 24468698213 ep499 Bool.true 18368347094748089891 ep490 14686958210563 ep490

noncomputable def ep597 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz35)) qz36)) (Complex.re qz37)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz35)) qz36)) (Complex.im qz37)) 30601948700975941 ep499 24468698213 ep499 0 1 0

noncomputable def ep598 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz35)) qz36)) (Complex.re qz37) 1 360 0 1 30601948700975941 36028797018963968000000 24468698213 36028797018963968000000 30601948700975941

noncomputable def ep599 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz35)) qz36) (Complex.mk (Enclosure.sfrac Bool.true 1 360) qz262) Bool.true 1 360 0 1 Bool.false 0 1 0 1

noncomputable def ep600 := @Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz35)) qz36) Bool.true 1 360 0 1 Bool.false 0 1 0 1 (ep599 (BSN.stirling_coeff_mk 2 1 30 Bool.true BSN.bern_real_2 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 1 360) qz262 Bool.true 1 360 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.true 1 360) qz274))

noncomputable def ep601 := nat_lit 4503599627370496000000000

noncomputable def ep602 := @Enclosure.Complex.IsNear.re_isNear qz37 Bool.true 30601948700975941 36028797018963968000000 24468698213 36028797018963968000000 Bool.false 18368347094748089891 ep601 14686958210563 ep601

noncomputable def ep603 := @Enclosure.Complex.IsNear.of_eq qz37 (@Inv.inv Complex Complex.instInv qz2) Bool.true 30601948700975941 36028797018963968000000 24468698213 36028797018963968000000 Bool.false 18368347094748089891 ep601 14686958210563

noncomputable def ep604 := @Enclosure.Complex.IsNear.of_parts (@Inv.inv Complex Complex.instInv qz2) Bool.true 30601948700975941 36028797018963968000000 24468698213 36028797018963968000000 Bool.false 18368347094748089891 ep601 14686958210563

noncomputable abbrev qz41 := (Complex.re qz252)

noncomputable def ep605 := @Enclosure.Real.IsNear.mulLit_tf qz41 (@Inv.inv Real Real.instInv (@DFunLike.coe qz352 Complex (fun (x : Complex) => Real) qz353 Complex.normSq qz2)) 24468698213 500000 0 1 1250657 72057594037927936 1 72057594037927936

noncomputable def ep606 := @Enclosure.Complex.IsNear.re_isNear qz2 Bool.true 24468698213 500000 0 1 Bool.true 14686958210563 62500000 0 1

noncomputable def ep607 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz352 Complex (fun (x : Complex) => Real) qz353 Complex.normSq qz2)) Bool.false 1250657 72057594037927936 1 72057594037927936 1250657 72057594037927936 1

noncomputable def ep608 := nat_lit 112530848803778126658083797

noncomputable abbrev qz42 := (Complex.im qz252)

noncomputable def ep609 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz352 Complex (fun (x : Complex) => Real) qz353 Complex.normSq qz2) (@HAdd.hAdd Real Real Real qz607 (@HMul.hMul Real Real Real qz0 qz41 qz41) (@HMul.hMul Real Real Real qz0 qz42 qz42)) Bool.false ep608 1953125000000000 0 1

noncomputable def ep610 := nat_lit 215706741478823919044776969

noncomputable def ep611 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz41 qz41) (@HMul.hMul Real Real Real qz0 qz42 qz42) 598717192238869393369 250000000000 0 1 ep610 3906250000000000

noncomputable def ep612 := nat_lit 56265424401889063329041898500000000000

noncomputable def ep613 := @Enclosure.Real.IsNear.mulLit_tt qz41 qz41 24468698213 500000 0 1 24468698213 500000 0 1

noncomputable def ep614 := @Enclosure.Real.IsNear.mulLit_tt qz42 qz42 14686958210563 62500000 0 1 14686958210563 62500000 0 1

noncomputable def ep615 := @Enclosure.Complex.IsNear.im_isNear qz2 Bool.true 24468698213 500000 0 1 Bool.true 14686958210563 62500000 0 1

noncomputable def ep616 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz352 Complex (fun (x : Complex) => Real) qz353 Complex.normSq qz2) ep608 1953125000000000 0 1 625328 625329 36028797018963968 (ep609 (Enclosure.Complex.normSq_eq_mul_add_mul qz2) (@ep611 0 1 ep612 ep608 1953125000000000 0 1 (@ep613 598717192238869393369 250000000000 0 1 (ep606 EMRow41.d5) (ep606 EMRow41.d5) rfl) (@ep614 ep610 3906250000000000 0 1 (ep615 EMRow41.d5) (ep615 EMRow41.d5) rfl) rfl rfl)) rfl

noncomputable def ep617 := @Enclosure.Real.IsNear.of_eq (Complex.re (@Inv.inv Complex Complex.instInv qz2)) (@HMul.hMul Real Real Real qz0 qz41 (@Inv.inv Real Real.instInv (@DFunLike.coe qz352 Complex (fun (x : Complex) => Real) qz353 Complex.normSq qz2))) Bool.true 30601948700975941 36028797018963968000000 24468698213 36028797018963968000000 (Enclosure.Complex.inv_re_eq_mul qz2) (@ep605 30601948700975941 36028797018963968000000 24468698213 36028797018963968000000 (ep606 EMRow41.d5) (@ep607 72057594037927936 (ep616 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep618 := @Enclosure.Real.IsNear.of_eq (Complex.im (@Inv.inv Complex Complex.instInv qz2)) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz42) (@Inv.inv Real Real.instInv (@DFunLike.coe qz352 Complex (fun (x : Complex) => Real) qz353 Complex.normSq qz2))) Bool.false 18368347094748089891 ep601 14686958210563 ep601 (Enclosure.Complex.inv_im_eq_mul qz2)

noncomputable def ep619 := @Enclosure.Real.IsNear.mulLit_ff (@Neg.neg Real Real.instNeg qz42) (@Inv.inv Real Real.instInv (@DFunLike.coe qz352 Complex (fun (x : Complex) => Real) qz353 Complex.normSq qz2)) 14686958210563 62500000 0 1 1250657 72057594037927936 1

noncomputable def ep620 := @ep619 72057594037927936 18368347094748089891 ep601 14686958210563 ep601 (@Enclosure.Real.IsNear.neg qz42 Bool.true 14686958210563 62500000 0 1 (ep615 EMRow41.d5)) (@ep607 72057594037927936 (ep616 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep621 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz35)) qz36)) (Complex.im qz37) 0 1 0 1 18368347094748089891 ep601 14686958210563 ep601 0

noncomputable def ep622 := @Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz35)) qz36) Bool.true 1 360 0 1 Bool.false 0 1 0 1 (ep599 (BSN.stirling_coeff_mk 2 1 30 Bool.true BSN.bern_real_2 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 1 360) qz262 Bool.true 1 360 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.true 1 360) qz274))

noncomputable def ep623 := @Enclosure.Complex.IsNear.im_isNear qz37 Bool.true 30601948700975941 36028797018963968000000 24468698213 36028797018963968000000 Bool.false 18368347094748089891 ep601 14686958210563 ep601

noncomputable abbrev qz897 := (@ep603 ep601 (BSN.zpow_one_sub_two_mul qz5 2 3 rfl rfl) (@ep604 ep601 ep617 (ep618 ep620)))

noncomputable def ep624 := @ep597 1 30601948700975941 30601948700975941 ep499 24468698213 ep499 (@ep598 ep499 24468698213 ep499 ep600 (ep602 qz897) rfl) (@ep621 1 0 1 ep622 (ep623 qz897) rfl) rfl

noncomputable def ep625 := @Enclosure.Real.IsNear.addLit_tt (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz35)) qz36)) (Complex.im qz37)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz35)) qz36)) (Complex.re qz37)) 18368347094748089891 ep490 14686958210563 ep490 0 1 0

noncomputable def ep626 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz35)) qz36)) (Complex.im qz37) 1 360 0 1 18368347094748089891 ep601 14686958210563 ep601 18368347094748089891

noncomputable def ep627 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz35)) qz36)) (Complex.re qz37) 0 1 0 1 30601948700975941 36028797018963968000000 24468698213 36028797018963968000000 0

noncomputable def ep628 := @ep625 1 18368347094748089891 18368347094748089891 ep490 14686958210563 ep490 (@ep626 ep490 14686958210563 ep490 ep600 (ep623 qz897) rfl) (@ep627 1 0 1 ep622 (ep602 qz897) rfl) rfl

noncomputable def ep629 := @ep562 ep490 (@ep563 Bool.true 34473763021 25769803776000 31001 25769803776000 (BSN.stirling_sum_succ qz5 0 1 rfl) (ep595 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep596 (ep624 rfl) (ep628 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep630 := @ep514 ep504 ep490 ep505 ep492 (ep557 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep558 Bool.true ep511 ep490 1950428961518210563 ep490 (BSN.stirling_sum_succ qz5 1 2 rfl) (ep629 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep631 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz22 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz9 4) Bool.false 37179257601932957 2251799813685248 100000000418847 19038500000000000000 Bool.false 868400151168419 140737488355328

noncomputable def ep632 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz9 4) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.logSumC qz9 3) (Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz22 qz552))) Bool.false 37179257601932957 2251799813685248 100000000418847 19038500000000000000 Bool.false 868400151168419 140737488355328 200000000038077 19038500000000000000

noncomputable def ep633 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz9 3) (Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz22 qz552)) Bool.false 111530462771461079 9007199254740992 300000001256541 76154000000000000000 Bool.false 2618802078060777 562949953421312 600000000114231 76154000000000000000 Bool.false

noncomputable def ep634 := nat_lit 1339523925455815566789542334693376

noncomputable def ep635 := nat_lit 1955463298605287102493503782912

noncomputable def ep636 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz9 3) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.logSumC qz9 2) (Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz22 qz553))) Bool.false 111530462771461079 9007199254740992 300000001256541 76154000000000000000 Bool.false 2618802078060777 562949953421312 600000000114231 76154000000000000000

noncomputable def ep637 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz9 2) (Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz22 qz553)) Bool.false 37175162350616221 4503599627370496 100000000418847 38077000000000000000 Bool.false 877471122097571 281474976710656 200000000038077 38077000000000000000 Bool.false

noncomputable def ep638 := nat_lit 502288550578011091964392776925184

noncomputable def ep639 := nat_lit 737127253931974742202711539712

noncomputable def ep640 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz9 2) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.logSumC qz9 1) (Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz22 qz590))) Bool.false 37175162350616221 4503599627370496 100000000418847 38077000000000000000 Bool.false 877471122097571 281474976710656 200000000038077 38077000000000000000

noncomputable def ep641 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz9 1) (Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz22 qz590)) Bool.false 37174284029804189 9007199254740992 100000000418847 76154000000000000000 Bool.false 882010365658531 562949953421312 200000000038077 76154000000000000000 Bool.false

noncomputable def ep642 := nat_lit 669688189238691620264013897662464

noncomputable def ep643 := nat_lit 987944654626747938514669666304

noncomputable abbrev qz898 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz22 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep644 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz9 1) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.logSumC qz9 0) qz898) Bool.false 37174284029804189 9007199254740992 100000000418847 76154000000000000000 Bool.false 882010365658531 562949953421312 200000000038077 76154000000000000000

noncomputable def ep645 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz9 0) qz898 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz899 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz258))

noncomputable def ep646 := @Enclosure.Complex.IsNear.of_eq qz898 qz899 Bool.false 37174284029804189 9007199254740992 100000000418847 76154000000000000000 Bool.false 882010365658531 562949953421312 200000000038077 76154000000000000000

noncomputable def ep647 := nat_lit 576607870217708384564499406410570821877928028605511928485866016502903380578367799990467131482112495885359796715520

noncomputable def ep648 := nat_lit 18930201044607261456099054490917137151997975385996439697112161894727842256026875771144208634422493761185622523904

noncomputable def ep649 := nat_lit 363450884115554215168524430762512454370427611139935464406417005020318361694537130830104798053423275908792320

noncomputable def ep650 := BSN.log_dyadic_bound 28740968064 94276968064 6 5 ep647 1048576 380770 ep648 ep649 660320 123017936128 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 28740968064) (BSN.artanhQ 94276968064) 0 5 ep648 ep647 ep649 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep651 := @Enclosure.Real.IsNear.mulLit_ff qz339 (Real.log (Enclosure.sfrac Bool.false 61508968064 16000000)) 1 2 0 1 37174284029804189 4503599627370496 100000000418847 38077000000000000000 37174284029804189 9007199254740992 100000000418847 76154000000000000000 qz340 (BSN.isNear_log_sfrac 61508968064 16000000 37174284029804189 4503599627370496 100000000418847 38077000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 61508968064) qz602)) Bool.false 311840496406687658278912 37778931862957161709568 1000000004188470 380770000000000000000 37174284029804189 4503599627370496 100000000418847 38077000000000000000 (BSN.log_rat_reduce_isNear 61508968064 16000000 11 123017936128 65536000000 660320 1048576 24973259072661432 36028797018963968 380770 1000000000000000 rfl rfl rfl rfl (ep650 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep652 := BSN.arctan_dyadic_bound_f 1000 248008 1 0 1048576 380770 0 1 1 0 1 1 4227 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 248008) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 248008) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz900 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable def ep653 := @Enclosure.Real.IsNear.subLit_ff_p qz348 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz900 qz604)) 884279719003555 562949953421312 1 2000000000000000 4227 1048576 1 380770 924854901180759801856 882010365658531 562949953421312 200000000038077 76154000000000000000 qz349 (ep652 rfl) rfl rfl

noncomputable abbrev qz901 := (@HAdd.hAdd Complex Complex Complex qz13 qz22 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz902 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz258)

noncomputable def ep654 := @ep645 37174284029804189 9007199254740992 100000000418847 76154000000000000000 Bool.false 882010365658531 562949953421312 200000000038077 76154000000000000000 Bool.false 37174284029804189 37174284029804189 9007199254740992 100000000418847 76154000000000000000 Bool.false 882010365658531 882010365658531 562949953421312 200000000038077 76154000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz9 0) (Complex.mk qz262 qz262) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz9) qz354) (ep646 (@congrArg Complex Complex qz901 qz902 Complex.log (BSN.w_shift_mk qz9 Bool.false 124004 1000 0 (@Eq.refl Real qz9) rfl)) (@Enclosure.Complex.IsNear.of_parts qz899 Bool.false 37174284029804189 9007199254740992 100000000418847 76154000000000000000 Bool.false 882010365658531 562949953421312 200000000038077 76154000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz899) (@HMul.hMul Real Real Real qz0 qz339 (Real.log (Enclosure.sfrac Bool.false 61508968064 16000000))) Bool.false 37174284029804189 9007199254740992 100000000418847 76154000000000000000 (Enclosure.clog_re_eq 1000 248008 4000 61508968064 16000000 rfl rfl rfl) (ep651 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz899) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz604 qz900)) Bool.false 882010365658531 562949953421312 200000000038077 76154000000000000000 (Enclosure.clog_im_eq 1000 248008 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz604 qz900)) (@HSub.hSub Real Real Real qz597 qz348 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz900 qz604))) Bool.false 882010365658531 562949953421312 200000000038077 76154000000000000000 (BSN.arctan_recip 248008 1000 rfl rfl) ep653)))) rfl rfl

noncomputable abbrev qz903 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz258))

noncomputable def ep655 := @Enclosure.Complex.IsNear.of_eq (Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz22 qz590)) qz903 Bool.false 37176040671428253 9007199254740992 100000000418847 76154000000000000000 Bool.false 872931878536611 562949953421312 200000000038077 76154000000000000000

noncomputable def ep656 := nat_lit 578077418176389904662242583195718412269794233463162844537206198227013506578855729832806587078498127564642996715520

noncomputable def ep657 := nat_lit 19001813926457098554027867251449942446788010643655415975813025914310391359937635103318560048580392061970262523904

noncomputable def ep658 := nat_lit 366497292315841454509924979414504843991873710322976364061709191474658329570654021784495409513466847108792320

noncomputable def ep659 := BSN.log_dyadic_bound 28764968064 94300968064 6 5 ep656 1048576 380770 ep657 ep658 660729 123065936128 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 28764968064) (BSN.artanhQ 94300968064) 0 5 ep657 ep656 ep658 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep660 := @Enclosure.Real.IsNear.mulLit_ff qz339 (Real.log (Enclosure.sfrac Bool.false 61532968064 16000000)) 1 2 0 1 37176040671428253 4503599627370496 100000000418847 38077000000000000000 37176040671428253 9007199254740992 100000000418847 76154000000000000000 qz340 (BSN.isNear_log_sfrac 61532968064 16000000 37176040671428253 4503599627370496 100000000418847 38077000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 61532968064) qz602)) Bool.false 311855232184668414541824 37778931862957161709568 1000000004188470 380770000000000000000 37176040671428253 4503599627370496 100000000418847 38077000000000000000 (BSN.log_rat_reduce_isNear 61532968064 16000000 11 123065936128 65536000000 660729 1048576 24973259072661432 36028797018963968 380770 1000000000000000 rfl rfl rfl rfl (ep659 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep661 := BSN.arctan_dyadic_bound_f 5000 248008 1 0 1048576 380770 0 1 1 0 1 1 21137 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 248008) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 248008) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz904 := (@Nat.cast Real Real.instNatCast 5000)

noncomputable def ep662 := @Enclosure.Real.IsNear.subLit_ff_p qz348 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz904 qz604)) 884279719003555 562949953421312 1 2000000000000000 21137 1048576 1 380770 915335417468405415936 872931878536611 562949953421312 200000000038077 76154000000000000000 qz349 (ep661 rfl) rfl rfl

noncomputable abbrev qz905 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz258)

noncomputable def ep663 := @ep641 37176040671428253 9007199254740992 100000000418847 76154000000000000000 Bool.false 872931878536611 562949953421312 200000000038077 76154000000000000000 Bool.false ep642 37175162350616221 4503599627370496 100000000418847 38077000000000000000 Bool.false ep643 877471122097571 281474976710656 200000000038077 38077000000000000000 (ep644 (BSN.log_sum_c_succ qz9 0 1 rfl) (ep654 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep655 (@congrArg Complex Complex (@HAdd.hAdd Complex Complex Complex qz13 qz22 qz590) qz905 Complex.log (BSN.w_shift_mk qz9 Bool.false 124004 1000 1 (@Eq.refl Real qz9) rfl)) (@Enclosure.Complex.IsNear.of_parts qz903 Bool.false 37176040671428253 9007199254740992 100000000418847 76154000000000000000 Bool.false 872931878536611 562949953421312 200000000038077 76154000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz903) (@HMul.hMul Real Real Real qz0 qz339 (Real.log (Enclosure.sfrac Bool.false 61532968064 16000000))) Bool.false 37176040671428253 9007199254740992 100000000418847 76154000000000000000 (Enclosure.clog_re_eq 5000 248008 4000 61532968064 16000000 rfl rfl rfl) (ep660 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz903) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz604 qz904)) Bool.false 872931878536611 562949953421312 200000000038077 76154000000000000000 (Enclosure.clog_im_eq 5000 248008 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz604 qz904)) (@HSub.hSub Real Real Real qz597 qz348 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz904 qz604))) Bool.false 872931878536611 562949953421312 200000000038077 76154000000000000000 (BSN.arctan_recip 248008 5000 rfl rfl) ep662)))) rfl rfl

noncomputable abbrev qz906 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 9000 4000) qz258))

noncomputable def ep664 := @Enclosure.Complex.IsNear.of_eq (Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz22 qz553)) qz906 Bool.false 37180138070228637 9007199254740992 100000000418847 76154000000000000000 Bool.false 863859833865635 562949953421312 200000000038077 76154000000000000000

noncomputable def ep665 := nat_lit 581519480505986217920364827714629735125493995407906505932442356447001166573364509599172771714484526816303796715520

noncomputable def ep666 := nat_lit 19169824508557229540890379026303438494131738095299727085256924288355747469368680805843670203552486497134422523904

noncomputable def ep667 := nat_lit 373695140524039564594815951957244544993756235948409711532773047142300223003868962974550510792235179908792320

noncomputable def ep668 := BSN.log_dyadic_bound 28820968064 94356968064 6 5 ep665 1048576 380770 ep666 ep667 661683 123177936128 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 28820968064) (BSN.artanhQ 94356968064) 0 5 ep666 ep665 ep667 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep669 := @Enclosure.Real.IsNear.mulLit_ff qz339 (Real.log (Enclosure.sfrac Bool.false 61588968064 16000000)) 1 2 0 1 37180138070228637 4503599627370496 100000000418847 38077000000000000000 37180138070228637 9007199254740992 100000000418847 76154000000000000000 qz340 (BSN.isNear_log_sfrac 61588968064 16000000 37180138070228637 4503599627370496 100000000418847 38077000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 61588968064) qz602)) Bool.false 311889603657024506167296 37778931862957161709568 1000000004188470 380770000000000000000 37180138070228637 4503599627370496 100000000418847 38077000000000000000 (BSN.log_rat_reduce_isNear 61588968064 16000000 11 123177936128 65536000000 661683 1048576 24973259072661432 36028797018963968 380770 1000000000000000 rfl rfl rfl rfl (ep668 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep670 := BSN.arctan_dyadic_bound_f 9000 248008 1 0 1048576 380770 0 1 1 0 1 1 38035 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 248008) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 248008) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz907 := (@Nat.cast Real Real.instNatCast 9000)

noncomputable def ep671 := @Enclosure.Real.IsNear.subLit_ff_p qz348 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz907 qz604)) 884279719003555 562949953421312 1 2000000000000000 38035 1048576 1 380770 905822689155492085760 863859833865635 562949953421312 200000000038077 76154000000000000000 qz349 (ep670 rfl) rfl rfl

noncomputable abbrev qz908 := (Complex.mk (Enclosure.sfrac Bool.false 9000 4000) qz258)

noncomputable def ep672 := @ep637 37180138070228637 9007199254740992 100000000418847 76154000000000000000 Bool.false 863859833865635 562949953421312 200000000038077 76154000000000000000 Bool.false ep638 111530462771461079 9007199254740992 300000001256541 76154000000000000000 Bool.false ep639 2618802078060777 562949953421312 600000000114231 76154000000000000000 (ep640 (BSN.log_sum_c_succ qz9 1 2 rfl) (ep663 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep664 (@congrArg Complex Complex (@HAdd.hAdd Complex Complex Complex qz13 qz22 qz553) qz908 Complex.log (BSN.w_shift_mk qz9 Bool.false 124004 1000 2 (@Eq.refl Real qz9) rfl)) (@Enclosure.Complex.IsNear.of_parts qz906 Bool.false 37180138070228637 9007199254740992 100000000418847 76154000000000000000 Bool.false 863859833865635 562949953421312 200000000038077 76154000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz906) (@HMul.hMul Real Real Real qz0 qz339 (Real.log (Enclosure.sfrac Bool.false 61588968064 16000000))) Bool.false 37180138070228637 9007199254740992 100000000418847 76154000000000000000 (Enclosure.clog_re_eq 9000 248008 4000 61588968064 16000000 rfl rfl rfl) (ep669 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz906) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz604 qz907)) Bool.false 863859833865635 562949953421312 200000000038077 76154000000000000000 (Enclosure.clog_im_eq 9000 248008 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz604 qz907)) (@HSub.hSub Real Real Real qz597 qz348 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz907 qz604))) Bool.false 863859833865635 562949953421312 200000000038077 76154000000000000000 (BSN.arctan_recip 248008 9000 rfl rfl) ep671)))) rfl rfl

noncomputable abbrev qz909 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 13000 4000) qz258))

noncomputable def ep673 := @Enclosure.Complex.IsNear.of_eq (Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz22 qz552)) qz909 Bool.false 37186567636270749 9007199254740992 100000000418847 76154000000000000000 Bool.false 854798526612899 562949953421312 200000000038077 76154000000000000000

noncomputable def ep674 := nat_lit 586965714910882487656515569294239026121814986707423342463043992332644223354889386806842752498279514440342196715520

noncomputable def ep675 := nat_lit 19436443119717839503272606884258989900781135852708270398772285533165695865602866771325784280307573226678102523904

noncomputable def ep676 := nat_lit 385263354739994037636434881440855500895704571045431360008591531679426894612395539400480520782528274308792320

noncomputable def ep677 := BSN.log_dyadic_bound 28908968064 94444968064 6 5 ep674 1048576 380770 ep675 ep676 663180 123353936128 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 28908968064) (BSN.artanhQ 94444968064) 0 5 ep675 ep674 ep676 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep678 := @Enclosure.Real.IsNear.mulLit_ff qz339 (Real.log (Enclosure.sfrac Bool.false 61676968064 16000000)) 1 2 0 1 37186567636270749 4503599627370496 100000000418847 38077000000000000000 37186567636270749 9007199254740992 100000000418847 76154000000000000000 qz340 (BSN.isNear_log_sfrac 61676968064 16000000 37186567636270749 4503599627370496 100000000418847 38077000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 61676968064) qz602)) Bool.false 311943538766161895227392 37778931862957161709568 1000000004188470 380770000000000000000 37186567636270749 4503599627370496 100000000418847 38077000000000000000 (BSN.log_rat_reduce_isNear 61676968064 16000000 11 123353936128 65536000000 663180 1048576 24973259072661432 36028797018963968 380770 1000000000000000 rfl rfl rfl rfl (ep677 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep679 := BSN.arctan_dyadic_bound_f 13000 248008 1 0 1048576 380770 0 1 1 0 1 1 54913 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 13000) (BSN.arctanEvenQ 248008) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 13000) (BSN.arctanOddQ 248008) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz910 := (@Nat.cast Real Real.instNatCast 13000)

noncomputable def ep680 := @Enclosure.Real.IsNear.subLit_ff_p qz348 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz910 qz604)) 884279719003555 562949953421312 1 2000000000000000 54913 1048576 1 380770 896321219841647181824 854798526612899 562949953421312 200000000038077 76154000000000000000 qz349 (ep679 rfl) rfl rfl

noncomputable abbrev qz911 := (Complex.mk (Enclosure.sfrac Bool.false 13000 4000) qz258)

noncomputable def ep681 := @ep633 37186567636270749 9007199254740992 100000000418847 76154000000000000000 Bool.false 854798526612899 562949953421312 200000000038077 76154000000000000000 Bool.false ep634 37179257601932957 2251799813685248 100000000418847 19038500000000000000 Bool.false ep635 868400151168419 140737488355328 200000000038077 19038500000000000000 (ep636 (BSN.log_sum_c_succ qz9 2 3 rfl) (ep672 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep673 (@congrArg Complex Complex (@HAdd.hAdd Complex Complex Complex qz13 qz22 qz552) qz911 Complex.log (BSN.w_shift_mk qz9 Bool.false 124004 1000 3 (@Eq.refl Real qz9) rfl)) (@Enclosure.Complex.IsNear.of_parts qz909 Bool.false 37186567636270749 9007199254740992 100000000418847 76154000000000000000 Bool.false 854798526612899 562949953421312 200000000038077 76154000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz909) (@HMul.hMul Real Real Real qz0 qz339 (Real.log (Enclosure.sfrac Bool.false 61676968064 16000000))) Bool.false 37186567636270749 9007199254740992 100000000418847 76154000000000000000 (Enclosure.clog_re_eq 13000 248008 4000 61676968064 16000000 rfl rfl rfl) (ep678 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz909) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz604 qz910)) Bool.false 854798526612899 562949953421312 200000000038077 76154000000000000000 (Enclosure.clog_im_eq 13000 248008 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz604 qz910)) (@HSub.hSub Real Real Real qz597 qz348 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz910 qz604))) Bool.false 854798526612899 562949953421312 200000000038077 76154000000000000000 (BSN.arctan_recip 248008 13000 rfl rfl) ep680)))) rfl rfl

noncomputable def ep682 := @ep506 ep492 Bool.false 37179257601932957 2251799813685248 100000000418847 19038500000000000000 Bool.false 868400151168419 140737488355328 200000000038077 19038500000000000000 Bool.true ep507 ep498 ep499 ep500 ep492 Bool.false ep508 ep494 ep490 ep495 ep492 (@ep509 ep499 ep503 ep492 Bool.false ep504 ep490 ep505 ep492 (BSN.logGammaStirling_unfold 2 qz5) (ep630 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep631 200000000038077 19038500000000000000 (BSN.log_sum_c_eq qz9 4) (ep632 (BSN.log_sum_c_succ qz9 3 4 rfl) (ep681 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable def ep683 := @Enclosure.Real.IsNear.mulLit_ff (@HDiv.hDiv Real Real Real qz1 qz9 (2 : Real)) (Real.log Real.pi) 124004 2000 0 1 75021 65536 1 262144 2325726021 32768000 31001 131072000 (@Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real qz1 qz9 (2 : Real)) (Enclosure.sfrac Bool.false 124004 2000) Bool.false 124004 2000 0 1 (BSN.t_half_eq qz9 Bool.false 124004 1000 (@Eq.refl Real qz9)) (Enclosure.Real.IsNear.const Bool.false 124004 2000)) EMRow41.d6 rfl

noncomputable def ep684 := @ep496 31001 131072000 ep497 ep489 ep490 ep491 ep492 (@ep501 ep495 ep492 (ep682 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep683 rfl rfl

noncomputable def ep685 := BSN.cos_dyadic_bound_f 856729 2147483648 1 0 1048576 381142 0 1 1 0 1 1 1048575 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 856729) qz266 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 856729) qz267 0 0 rfl) rfl rfl

noncomputable def ep686 := @ep488 262144 Bool.true 1048575 1048576 1 190385 (@ep493 64237083 524288 89 262144 ep684 rfl) (Enclosure.sfrac_false_div 64237083 524288) (BSN.cos_reduce2 qz895 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 30143500789015904256) qz281) 226375608064910080 72057594037927936 Bool.false 1048575 1048576 19 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q2 64237083 524288 226375608064910080 72057594037927936 19 30143500789015904256 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1048575 1048576 30143500789015904256 75557863725914323419136 856729 2147483648 381142 380770 (ep685 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep687 := nat_lit 169543667359288573029978786953779

noncomputable def ep688 := nat_lit 27149871072111399824825846008837028759

noncomputable abbrev qz609 := (@Nat.cast Complex Complex.instNatCast 32)

noncomputable abbrev qz43 := (@HPow.hPow Complex Complex Complex (@instHPow Complex Complex Complex.instPow) qz609 (@Neg.neg Complex Complex.instNeg qz259))

noncomputable abbrev qz44 := (@HAdd.hAdd Complex Complex Complex qz260 (@HDiv.hDiv Complex Complex Complex qz346 qz609 (@HSub.hSub Complex Complex Complex qz595 qz259 (1 : Complex))) qz345)

noncomputable abbrev qz45 := (@instHSub Nat instSubNat)

noncomputable abbrev qz46 := qz254

noncomputable abbrev qz47 := qz609

noncomputable def ep689 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz12 2 32) (@HAdd.hAdd Complex Complex Complex qz13 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 32, @HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast n) qz15) (@HMul.hMul Complex Complex Complex qz3 qz43 (@HAdd.hAdd Complex Complex Complex qz13 qz44 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1))))))) Bool.false ep483 ep484 ep485

noncomputable def ep690 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 32, @HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast n) qz15) (@HMul.hMul Complex Complex Complex qz3 qz43 (@HAdd.hAdd Complex Complex Complex qz13 qz44 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))))) Bool.false 571132114927 1099511627776 1210568835453179 209330521254133760

noncomputable def ep691 := nat_lit 1375101377480397648836460850308401

noncomputable def ep692 := nat_lit 351788762057967319744246777198123819

noncomputable def ep693 := nat_lit 1786735543846744488156581213046221

noncomputable def ep694 := nat_lit 351449625536593082791808248837028759

noncomputable def ep695 := nat_lit 12393263563603283084778605999824063024882253824

noncomputable def ep696 := nat_lit 186415233677324058365508228490299460764565504

noncomputable def ep697 := @ep690 Bool.false 88346611739 1099511627776 1210230994224519 209330521254133760 Bool.true ep691 ep484 ep692 ep486 Bool.true ep693 ep484 ep694 ep486 Bool.false ep695 ep483 ep484 ep485 ep486 Bool.false ep696 ep687 ep484

noncomputable def ep698 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 32, @HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast n) qz15) (BSN.headSumC qz12 32) Bool.false 571132114927 1099511627776 1210568835453179 209330521254133760 Bool.false 88346611739 1099511627776 1210230994224519

noncomputable abbrev qz912 := (@Nat.cast Complex Complex.instNatCast 31)

noncomputable def ep699 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 32) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 31) (@HPow.hPow Complex Complex Complex qz14 qz912 qz15)) Bool.false 571132114927 1099511627776 1210568835453179 209330521254133760 Bool.false 88346611739 1099511627776 1210230994224519 209330521254133760

noncomputable def ep700 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 31) (@HPow.hPow Complex Complex Complex qz14 qz912 qz15) Bool.false 543130605891 1099511627776 1185818088309559 209330521254133760 Bool.true 107135123681 1099511627776 1185310938461939 209330521254133760 Bool.false

noncomputable abbrev qz913 := (@Nat.cast Complex Complex.instNatCast 30)

noncomputable def ep701 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 31) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 30) (@HPow.hPow Complex Complex Complex qz14 qz913 qz15)) Bool.false 543130605891 1099511627776 1185818088309559 209330521254133760 Bool.true 107135123681 1099511627776 1185310938461939 209330521254133760

noncomputable def ep702 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 30) (@HPow.hPow Complex Complex Complex qz14 qz913 qz15) Bool.false 25100984303 68719476736 116054613484047 20933052125413376 Bool.false 17620613431 549755813888 116003812826035 20933052125413376 Bool.false

noncomputable abbrev qz914 := (@Nat.cast Complex Complex.instNatCast 29)

noncomputable def ep703 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 30) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 29) (@HPow.hPow Complex Complex Complex qz14 qz914 qz15)) Bool.false 25100984303 68719476736 116054613484047 20933052125413376 Bool.false 17620613431 549755813888 116003812826035 20933052125413376

noncomputable def ep704 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 29) (@HPow.hPow Complex Complex Complex qz14 qz914 qz15) Bool.false 598180346633 1099511627776 1134793198977499 209330521254133760 Bool.false 90459869567 1099511627776 1134423395153499 209330521254133760 Bool.true

noncomputable abbrev qz915 := (@Nat.cast Complex Complex.instNatCast 28)

noncomputable def ep705 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 29) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 28) (@HPow.hPow Complex Complex Complex qz14 qz915 qz15)) Bool.false 598180346633 1099511627776 1134793198977499 209330521254133760 Bool.false 90459869567 1099511627776 1134423395153499 209330521254133760

noncomputable def ep706 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 28) (@HPow.hPow Complex Complex Complex qz14 qz915 qz15) Bool.false 580114222249 1099511627776 221752494799119 41866104250826752 Bool.true 14567773881 137438953472 110821115006835 20933052125413376 Bool.false

noncomputable abbrev qz916 := (@Nat.cast Complex Complex.instNatCast 27)

noncomputable def ep707 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 28) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 27) (@HPow.hPow Complex Complex Complex qz14 qz916 qz15)) Bool.false 580114222249 1099511627776 221752494799119 41866104250826752 Bool.true 14567773881 137438953472 110821115006835 20933052125413376

noncomputable def ep708 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 27) (@HPow.hPow Complex Complex Complex qz14 qz916 qz15) Bool.false 377332461119 1099511627776 216416097834369 41866104250826752 Bool.true 56087448427 1099511627776 216332688414327 41866104250826752 Bool.false

noncomputable abbrev qz917 := (@Nat.cast Complex Complex.instNatCast 26)

noncomputable def ep709 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 27) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 26) (@HPow.hPow Complex Complex Complex qz14 qz917 qz15)) Bool.false 377332461119 1099511627776 216416097834369 41866104250826752 Bool.true 56087448427 1099511627776 216332688414327 41866104250826752

noncomputable def ep710 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 26) (@HPow.hPow Complex Complex Complex qz14 qz917 qz15) Bool.false 445598533971 1099511627776 1055022006311801 209330521254133760 Bool.false 9278344421 68719476736 527239397725473 104665260627066880 Bool.true

noncomputable abbrev qz918 := (@Nat.cast Complex Complex.instNatCast 25)

noncomputable def ep711 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz12 26) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz12 25) (@HPow.hPow Complex Complex Complex qz14 qz918 qz15)) Bool.false 445598533971 1099511627776 1055022006311801 209330521254133760 Bool.false 9278344421 68719476736 527239397725473 104665260627066880

noncomputable def ep712 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz12 25) (@HPow.hPow Complex Complex Complex qz14 qz918 qz15) Bool.false 662294107461 1099511627776 205459092604167 41866104250826752 Bool.false 111037628441 1099511627776 205383001431217 41866104250826752 Bool.true

noncomputable abbrev qz919 := (@Nat.cast Real Real.instNatCast 25)

noncomputable abbrev qz355 := (@Inv.inv Real Real.instInv (Real.sqrt qz919))

noncomputable abbrev qz356 := (@HMul.hMul Real Real Real qz0 qz9 (Real.log (Enclosure.sfrac Bool.false 25 1)))

noncomputable def ep713 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz14 qz918 qz15) (Complex.mk (@HMul.hMul Real Real Real qz0 qz355 (Real.cos qz356)) (@HMul.hMul Real Real Real qz0 qz355 (@Neg.neg Real Real.instNeg (Real.sin qz356)))) Bool.true 108347786745 549755813888 1066405511191 8051173894389760 Bool.false 37415882295 1099511627776 2120291407297 16102347788779520 (BSN.cpow_neg_s_mk qz9 124004 1000 25 (@Eq.refl Real qz9) rfl)

noncomputable abbrev qz920 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 25) qz265)

noncomputable def ep714 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz919) 5242881 1048576 1 1048576 104857 104858 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz919) (Real.sqrt qz920) Bool.false 5242881 1048576 1 1048576 (BSN.sqrt_natCast_div_one 25) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz920) Bool.false 5242881 1048576 1 1048576 5242881 1048576 1 1048576 (BSN.sqrt_enclosure 25 1 2621440 2621441 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep715 := BSN.log_dyadic_bound 9 41 5 4 7545754341519345 524288 190385 124828057765224 4519905705 233982 50 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 9) (BSN.artanhQ 41) 0 4 124828057765224 7545754341519345 4519905705 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz357 := (Real.log (Enclosure.sfrac Bool.false 25 1))

noncomputable def ep716 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz357 124004 1000 0 1 3624129903009015 1125899906842624 50000000038077 9519250000000000000 22470330224636494803 56294995342131200 53450000040704313 82062500000000000000 qz270 (BSN.isNear_log_sfrac 25 1 3624129903009015 1125899906842624 50000000038077 9519250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz920) Bool.false 60802810194841294602240 18889465931478580854784 1000000000761540 190385000000000000000 3624129903009015 1125899906842624 50000000038077 9519250000000000000 (BSN.log_rat_reduce_isNear 25 1 4 50 32 233982 524288 24973259072661432 36028797018963968 190385 1000000000000000 rfl rfl rfl rfl (ep715 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep717 := nat_lit 18176046529383754996450407980712976

noncomputable def ep718 := BSN.cos_dyadic_bound_f 367176482 2147483648 2 1 1048576 381142 ep717 ep143 ep717 ep717 ep144 ep717 1033286 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 367176482) qz266 0 1 ep717 ep143 ep717 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 367176482) qz267 0 1 ep717 ep144 ep717 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz921 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 418542515) qz268)

noncomputable def ep719 := @Enclosure.Real.IsNear.cos_image qz356 qz921 Bool.false 418542515 1048576 171 262144 Bool.true 1033286 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz356 Bool.false 22470330224636494803 56294995342131200 53450000040704313 82062500000000000000 418542515 1048576 171 262144 (ep716 rfl) rfl) (Enclosure.sfrac_false_div 418542515 1048576) (BSN.cos_reduce2 qz921 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 25837747989854824693760) qz271) 226375608064910080 72057594037927936 Bool.false 1033286 1048576 63 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q2 418542515 1048576 226375608064910080 72057594037927936 63 25837747989854824693760 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1033286 1048576 25837747989854824693760 151115727451828646838272 367176482 2147483648 381142 380770 (ep718 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep720 := BSN.sin_dyadic_bound_f 367176482 2147483648 2 1 1048576 381142 ep717 ep123 ep717 ep717 ep124 ep717 178413 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 367176482) qz272 0 1 ep717 ep123 ep717 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 367176482) qz273 0 1 ep717 ep124 ep717 rfl rfl rfl rfl) rfl rfl

noncomputable def ep721 := @Enclosure.Real.IsNear.sin_image qz356 qz921 Bool.false 418542515 1048576 171 262144 Bool.true 178413 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz356 Bool.false 22470330224636494803 56294995342131200 53450000040704313 82062500000000000000 418542515 1048576 171 262144 (ep716 rfl) rfl) (Enclosure.sfrac_false_div 418542515 1048576) (BSN.sin_reduce2 qz921 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 25837747989854824693760) qz271) 226375608064910080 72057594037927936 Bool.false 178413 1048576 63 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q2 418542515 1048576 226375608064910080 72057594037927936 63 25837747989854824693760 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 178413 1048576 25837747989854824693760 151115727451828646838272 367176482 2147483648 381142 380770 (ep720 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz610 := (@Enclosure.Real.IsNear.recentre' qz355 Bool.false 209715 1048576 1 1048576 209715 1048576 1 1048576 (ep714 rfl rfl) rfl)

noncomputable def ep722 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz355 (Real.cos qz356)) (@HMul.hMul Real Real Real qz0 qz355 (@Neg.neg Real Real.instNeg (Real.sin qz356))) Bool.true 108347786745 549755813888 1066405511191 8051173894389760 Bool.false 37415882295 1099511627776 2120291407297 16102347788779520 (@Enclosure.Real.IsNear.mulLit_ft qz355 (Real.cos qz356) 209715 1048576 1 1048576 516643 524288 32817979 49908285440 108347786745 549755813888 1066405511191 8051173894389760 qz610 (@Enclosure.Real.IsNear.recentre' (Real.cos qz356) Bool.true 1033286 1048576 32817979 49908285440 516643 524288 32817979 49908285440 (ep719 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz355 (@Neg.neg Real Real.instNeg (Real.sin qz356)) 209715 1048576 1 1048576 178413 1048576 32817979 49908285440 37415882295 1099511627776 2120291407297 16102347788779520 qz610 (@Enclosure.Real.IsNear.neg (Real.sin qz356) Bool.true 178413 1048576 32817979 49908285440 (@Enclosure.Real.IsNear.recentre' (Real.sin qz356) Bool.true 178413 1048576 32817979 49908285440 178413 1048576 32817979 49908285440 (ep721 rfl rfl) rfl)) rfl)

noncomputable def ep723 := @ep712 108347786745 549755813888 1066405511191 8051173894389760 Bool.false 37415882295 1099511627776 2120291407297 16102347788779520 Bool.false 244970384710526721589248 445598533971 1099511627776 1055022006311801 209330521254133760 Bool.false 163226361238401251803136 9278344421 68719476736 527239397725473 104665260627066880 EMRow41.d9 (ep713 ep722) rfl rfl

noncomputable abbrev qz922 := (@Nat.cast Real Real.instNatCast 26)

noncomputable abbrev qz358 := (@Inv.inv Real Real.instInv (Real.sqrt qz922))

noncomputable abbrev qz359 := (@HMul.hMul Real Real Real qz0 qz9 (Real.log (Enclosure.sfrac Bool.false 26 1)))

noncomputable def ep724 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz14 qz917 qz15) (Complex.mk (@HMul.hMul Real Real Real qz0 qz358 (Real.cos qz359)) (@HMul.hMul Real Real Real qz0 qz358 (@Neg.neg Real Real.instNeg (Real.sin qz359)))) Bool.true 17066518213 274877906944 6764620715011 52332630313533440 Bool.true 204540959163 1099511627776 27184646620689 209330521254133760 (BSN.cpow_neg_s_mk qz9 124004 1000 26 (@Eq.refl Real qz9) rfl)

noncomputable abbrev qz923 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26) qz265)

noncomputable def ep725 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz922) 5346709 1048576 1 1048576 102821 102822 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz922) (Real.sqrt qz923) Bool.false 5346709 1048576 1 1048576 (BSN.sqrt_natCast_div_one 26) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz923) Bool.false 5346709 1048576 1 1048576 5346709 1048576 1 1048576 (BSN.sqrt_enclosure 26 1 2673354 2673355 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep726 := BSN.log_dyadic_bound 10 42 5 4 9150106136613120 524288 190385 179034245376000 10500000000 254545 52 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 10) (BSN.artanhQ 42) 0 4 179034245376000 9150106136613120 10500000000 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz360 := (Real.log (Enclosure.sfrac Bool.false 26 1))

noncomputable def ep727 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz360 124004 1000 0 1 3668288609262839 1125899906842624 50000000038077 9519250000000000000 113720615175757271839 281474976710656000 53450000040704313 82062500000000000000 qz270 (BSN.isNear_log_sfrac 26 1 3668288609262839 1125899906842624 50000000038077 9519250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz923) Bool.false 61543670347942250676224 18889465931478580854784 1000000000761540 190385000000000000000 3668288609262839 1125899906842624 50000000038077 9519250000000000000 (BSN.log_rat_reduce_isNear 26 1 4 52 32 254545 524288 24973259072661432 36028797018963968 190385 1000000000000000 rfl rfl rfl rfl (ep726 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep728 := nat_lit 229000822460951664561379946655826176

noncomputable def ep729 := BSN.sin_dyadic_bound_f 691766076 2147483648 2 1 1048576 381142 ep728 ep123 ep728 ep728 ep124 ep728 331964 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 691766076) qz272 0 1 ep728 ep123 ep728 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 691766076) qz273 0 1 ep728 ep124 ep728 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz611 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6619411) (@Nat.cast Real Real.instNatCast 16384))

noncomputable def ep730 := @Enclosure.Real.IsNear.cos_image qz359 qz611 Bool.false 6619411 16384 171 262144 Bool.true 331964 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz359 Bool.false 113720615175757271839 281474976710656000 53450000040704313 82062500000000000000 6619411 16384 171 262144 (ep727 rfl) rfl) (Enclosure.sfrac_false_div 6619411 16384) (BSN.cos_reduce1 qz611 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 760604844769098596352) (@Nat.cast Real Real.instNatCast 2361183241434822606848)) 226375608064910080 72057594037927936 Bool.false 331964 1048576 64 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q1 6619411 16384 226375608064910080 72057594037927936 64 760604844769098596352 2361183241434822606848 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 331964 1048576 760604844769098596352 2361183241434822606848 691766076 2147483648 381142 380770 (ep729 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep731 := BSN.cos_dyadic_bound_f 691766076 2147483648 2 1 1048576 381142 ep728 ep143 ep728 ep728 ep144 ep728 994641 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 691766076) qz266 0 1 ep728 ep143 ep728 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 691766076) qz267 0 1 ep728 ep144 ep728 rfl rfl rfl rfl) rfl rfl

noncomputable def ep732 := @Enclosure.Real.IsNear.sin_image qz359 qz611 Bool.false 6619411 16384 171 262144 Bool.false 994641 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz359 Bool.false 113720615175757271839 281474976710656000 53450000040704313 82062500000000000000 6619411 16384 171 262144 (ep727 rfl) rfl) (Enclosure.sfrac_false_div 6619411 16384) (BSN.sin_reduce1 qz611 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 760604844769098596352) (@Nat.cast Real Real.instNatCast 2361183241434822606848)) 226375608064910080 72057594037927936 Bool.false 994641 1048576 64 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q1 6619411 16384 226375608064910080 72057594037927936 64 760604844769098596352 2361183241434822606848 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 994641 1048576 760604844769098596352 2361183241434822606848 691766076 2147483648 381142 380770 (ep731 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz612 := (@Enclosure.Real.IsNear.recentre' qz358 Bool.false 205643 1048576 1 1048576 205643 1048576 1 1048576 (ep725 rfl rfl) rfl)

noncomputable def ep733 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz358 (Real.cos qz359)) (@HMul.hMul Real Real Real qz0 qz358 (@Neg.neg Real Real.instNeg (Real.sin qz359))) Bool.true 17066518213 274877906944 6764620715011 52332630313533440 Bool.true 204540959163 1099511627776 27184646620689 209330521254133760 (@Enclosure.Real.IsNear.mulLit_ft qz358 (Real.cos qz359) 205643 1048576 1 1048576 82991 262144 32817979 49908285440 17066518213 274877906944 6764620715011 52332630313533440 qz612 (@Enclosure.Real.IsNear.recentre' (Real.cos qz359) Bool.true 331964 1048576 32817979 49908285440 82991 262144 32817979 49908285440 (ep730 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz358 (@Neg.neg Real Real.instNeg (Real.sin qz359)) 205643 1048576 1 1048576 994641 1048576 32817979 49908285440 204540959163 1099511627776 27184646620689 209330521254133760 qz612 (@Enclosure.Real.IsNear.neg (Real.sin qz359) Bool.false 994641 1048576 32817979 49908285440 (@Enclosure.Real.IsNear.recentre' (Real.sin qz359) Bool.false 994641 1048576 32817979 49908285440 994641 1048576 32817979 49908285440 (ep732 rfl rfl) rfl)) rfl)

noncomputable def ep734 := @ep710 17066518213 274877906944 6764620715011 52332630313533440 Bool.true 204540959163 1099511627776 27184646620689 209330521254133760 Bool.false 103720357134418980110336 377332461119 1099511627776 216416097834369 41866104250826752 Bool.true 3854300107360826294272 56087448427 1099511627776 216332688414327 41866104250826752 (ep711 (BSN.head_sum_c_succ qz12 25 26 rfl rfl) (ep723 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep724 ep733) rfl rfl

noncomputable abbrev qz924 := (@Nat.cast Real Real.instNatCast 27)

noncomputable abbrev qz361 := (@Inv.inv Real Real.instInv (Real.sqrt qz924))

noncomputable abbrev qz362 := (@HMul.hMul Real Real Real qz0 qz9 (Real.log (Enclosure.sfrac Bool.false 27 1)))

noncomputable def ep735 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz14 qz916 qz15) (Complex.mk (@HMul.hMul Real Real Real qz0 qz361 (Real.cos qz362)) (@HMul.hMul Real Real Real qz0 qz361 (@Neg.neg Real Real.instNeg (Real.sin qz362)))) Bool.false 101390880565 549755813888 2668198482375 20933052125413376 Bool.true 60454742621 1099511627776 5309541599343 41866104250826752 (BSN.cpow_neg_s_mk qz9 124004 1000 27 (@Eq.refl Real qz9) rfl)

noncomputable abbrev qz925 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 27) qz265)

noncomputable def ep736 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz924) 5448561 1048576 1 1048576 100899 100900 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz924) (Real.sqrt qz925) Bool.false 5448561 1048576 1 1048576 (BSN.sqrt_natCast_div_one 27) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz925) Bool.false 5448561 1048576 1 1048576 5448561 1048576 1 1048576 (BSN.sqrt_enclosure 27 1 2724280 2724281 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep737 := BSN.log_dyadic_bound 11 43 5 4 11045349262332945 524288 190385 250863800262504 22507682505 274332 54 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 11) (BSN.artanhQ 43) 0 4 250863800262504 11045349262332945 22507682505 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz363 := (Real.log (Enclosure.sfrac Bool.false 27 1))

noncomputable def ep738 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz363 124004 1000 0 1 3710780868205815 1125899906842624 50000000038077 9519250000000000000 23007583539049694163 56294995342131200 53450000040704313 82062500000000000000 qz270 (BSN.isNear_log_sfrac 27 1 3710780868205815 1125899906842624 50000000038077 9519250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz925) Bool.false 62256572154556490711040 18889465931478580854784 1000000000761540 190385000000000000000 3710780868205815 1125899906842624 50000000038077 9519250000000000000 (BSN.log_rat_reduce_isNear 27 1 4 54 32 274332 524288 24973259072661432 36028797018963968 190385 1000000000000000 rfl rfl rfl rfl (ep737 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep739 := nat_lit 149879380124216389554586986819210000

noncomputable def ep740 := BSN.cos_dyadic_bound_f 622207830 2147483648 2 1 1048576 381142 ep739 ep143 ep739 ep739 ep144 ep739 1004870 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 622207830) qz266 0 1 ep739 ep143 ep739 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 622207830) qz267 0 1 ep739 ep144 ep739 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz926 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 214274819) qz280)

noncomputable def ep741 := @Enclosure.Real.IsNear.cos_image qz362 qz926 Bool.false 214274819 524288 171 262144 Bool.false 1004870 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz362 Bool.false 23007583539049694163 56294995342131200 53450000040704313 82062500000000000000 214274819 524288 171 262144 (ep738 rfl) rfl) (Enclosure.sfrac_false_div 214274819 524288) (BSN.cos_reduce0 qz926 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 21891991809725476896768) qz281) 226375608064910080 72057594037927936 Bool.false 1004870 1048576 65 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q0 214274819 524288 226375608064910080 72057594037927936 65 21891991809725476896768 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1004870 1048576 21891991809725476896768 75557863725914323419136 622207830 2147483648 381142 380770 (ep740 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep742 := BSN.sin_dyadic_bound_f 622207830 2147483648 2 1 1048576 381142 ep739 ep123 ep739 ep739 ep124 ep739 299579 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 622207830) qz272 0 1 ep739 ep123 ep739 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 622207830) qz273 0 1 ep739 ep124 ep739 rfl rfl rfl rfl) rfl rfl

noncomputable def ep743 := @Enclosure.Real.IsNear.sin_image qz362 qz926 Bool.false 214274819 524288 171 262144 Bool.false 299579 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz362 Bool.false 23007583539049694163 56294995342131200 53450000040704313 82062500000000000000 214274819 524288 171 262144 (ep738 rfl) rfl) (Enclosure.sfrac_false_div 214274819 524288) (BSN.sin_reduce0 qz926 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 21891991809725476896768) qz281) 226375608064910080 72057594037927936 Bool.false 299579 1048576 65 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q0 214274819 524288 226375608064910080 72057594037927936 65 21891991809725476896768 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 299579 1048576 21891991809725476896768 75557863725914323419136 622207830 2147483648 381142 380770 (ep742 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz613 := (@Enclosure.Real.IsNear.recentre' qz361 Bool.false 201799 1048576 1 1048576 201799 1048576 1 1048576 (ep736 rfl rfl) rfl)

noncomputable def ep744 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz361 (Real.cos qz362)) (@HMul.hMul Real Real Real qz0 qz361 (@Neg.neg Real Real.instNeg (Real.sin qz362))) Bool.false 101390880565 549755813888 2668198482375 20933052125413376 Bool.true 60454742621 1099511627776 5309541599343 41866104250826752 (@Enclosure.Real.IsNear.mulLit_ff qz361 (Real.cos qz362) 201799 1048576 1 1048576 502435 524288 32817979 49908285440 101390880565 549755813888 2668198482375 20933052125413376 qz613 (@Enclosure.Real.IsNear.recentre' (Real.cos qz362) Bool.false 1004870 1048576 32817979 49908285440 502435 524288 32817979 49908285440 (ep741 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz361 (@Neg.neg Real Real.instNeg (Real.sin qz362)) 201799 1048576 1 1048576 299579 1048576 32817979 49908285440 60454742621 1099511627776 5309541599343 41866104250826752 qz613 (@Enclosure.Real.IsNear.neg (Real.sin qz362) Bool.false 299579 1048576 32817979 49908285440 (@Enclosure.Real.IsNear.recentre' (Real.sin qz362) Bool.false 299579 1048576 32817979 49908285440 299579 1048576 32817979 49908285440 (ep743 rfl rfl) rfl)) rfl)

noncomputable def ep745 := @ep708 101390880565 549755813888 2668198482375 20933052125413376 Bool.true 60454742621 1099511627776 5309541599343 41866104250826752 Bool.false 318921166400503112794112 580114222249 1099511627776 221752494799119 41866104250826752 Bool.true 128139494183768055349248 14567773881 137438953472 110821115006835 20933052125413376 (ep709 (BSN.head_sum_c_succ qz12 26 27 rfl rfl) (ep734 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep735 ep744) rfl rfl

noncomputable abbrev qz927 := (@Nat.cast Real Real.instNatCast 28)

noncomputable abbrev qz364 := (@Inv.inv Real Real.instInv (Real.sqrt qz927))

noncomputable abbrev qz365 := (@HMul.hMul Real Real Real qz0 qz9 (Real.log (Enclosure.sfrac Bool.false 28 1)))

noncomputable def ep746 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz14 qz915 qz15) (Complex.mk (@HMul.hMul Real Real Real qz0 qz364 (Real.cos qz365)) (@HMul.hMul Real Real Real qz0 qz364 (@Neg.neg Real Real.instNeg (Real.sin qz365)))) Bool.false 564566387 34359738368 1626920311369 13083157578383360 Bool.false 207002060615 1099511627776 26212245085149 209330521254133760 (BSN.cpow_neg_s_mk qz9 124004 1000 28 (@Eq.refl Real qz9) rfl)

noncomputable abbrev qz928 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 28) qz265)

noncomputable def ep747 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz927) 5548543 1048576 1 1048576 99081 99082 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz927) (Real.sqrt qz928) Bool.false 5548543 1048576 1 1048576 (BSN.sqrt_natCast_div_one 28) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz928) Bool.false 5548543 1048576 1 1048576 5548543 1048576 1 1048576 (BSN.sqrt_enclosure 28 1 2774271 2774272 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep748 := BSN.log_dyadic_bound 12 44 5 4 13275571325829120 524288 190385 344661139390464 45148078080 293399 56 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 12) (BSN.artanhQ 44) 0 4 344661139390464 13275571325829120 45148078080 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz366 := (Real.log (Enclosure.sfrac Bool.false 28 1))

noncomputable def ep749 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz366 124004 1000 0 1 3751726938922231 1125899906842624 50000000038077 9519250000000000000 116307286833528083231 281474976710656000 53450000040704313 82062500000000000000 qz270 (BSN.isNear_log_sfrac 28 1 3751726938922231 1125899906842624 50000000038077 9519250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz928) Bool.false 62943533227317076688896 18889465931478580854784 1000000000761540 190385000000000000000 3751726938922231 1125899906842624 50000000038077 9519250000000000000 (BSN.log_rat_reduce_isNear 28 1 4 56 32 293399 524288 24973259072661432 36028797018963968 190385 1000000000000000 rfl rfl rfl rfl (ep748 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep750 := BSN.sin_dyadic_bound_f 186948463 2147483648 1 0 1048576 381142 0 1 1 0 1 1 91168 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 186948463) qz272 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 186948463) qz273 0 0 rfl) rfl rfl

noncomputable abbrev qz929 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 433278407) qz268)

noncomputable def ep751 := @Enclosure.Real.IsNear.cos_image qz365 qz929 Bool.false 433278407 1048576 171 262144 Bool.false 91168 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz365 Bool.false 116307286833528083231 281474976710656000 53450000040704313 82062500000000000000 433278407 1048576 171 262144 (ep749 rfl) rfl) (Enclosure.sfrac_false_div 433278407 1048576) (BSN.cos_reduce3 qz929 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13155328614914393636864) qz271) 226375608064910080 72057594037927936 Bool.false 91168 1048576 65 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q3 433278407 1048576 226375608064910080 72057594037927936 65 13155328614914393636864 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 91168 1048576 13155328614914393636864 151115727451828646838272 186948463 2147483648 381142 380770 (ep750 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep752 := nat_lit 1221483474556642600272565573892161

noncomputable def ep753 := BSN.cos_dyadic_bound_f 186948463 2147483648 2 1 1048576 381142 ep752 ep143 ep752 ep752 ep144 ep752 1044605 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 186948463) qz266 0 1 ep752 ep143 ep752 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 186948463) qz267 0 1 ep752 ep144 ep752 rfl rfl rfl rfl) rfl rfl

noncomputable def ep754 := @Enclosure.Real.IsNear.sin_image qz365 qz929 Bool.false 433278407 1048576 171 262144 Bool.true 1044605 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz365 Bool.false 116307286833528083231 281474976710656000 53450000040704313 82062500000000000000 433278407 1048576 171 262144 (ep749 rfl) rfl) (Enclosure.sfrac_false_div 433278407 1048576) (BSN.sin_reduce3 qz929 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13155328614914393636864) qz271) 226375608064910080 72057594037927936 Bool.false 1044605 1048576 65 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q3 433278407 1048576 226375608064910080 72057594037927936 65 13155328614914393636864 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1044605 1048576 13155328614914393636864 151115727451828646838272 186948463 2147483648 381142 380770 (ep753 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz614 := (@Enclosure.Real.IsNear.recentre' qz364 Bool.false 198163 1048576 1 1048576 198163 1048576 1 1048576 (ep747 rfl rfl) rfl)

noncomputable def ep755 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz364 (Real.cos qz365)) (@HMul.hMul Real Real Real qz0 qz364 (@Neg.neg Real Real.instNeg (Real.sin qz365))) Bool.false 564566387 34359738368 1626920311369 13083157578383360 Bool.false 207002060615 1099511627776 26212245085149 209330521254133760 (@Enclosure.Real.IsNear.mulLit_ff qz364 (Real.cos qz365) 198163 1048576 1 1048576 2849 32768 32817979 49908285440 564566387 34359738368 1626920311369 13083157578383360 qz614 (@Enclosure.Real.IsNear.recentre' (Real.cos qz365) Bool.false 91168 1048576 32817979 49908285440 2849 32768 32817979 49908285440 (ep751 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz364 (@Neg.neg Real Real.instNeg (Real.sin qz365)) 198163 1048576 1 1048576 1044605 1048576 32817979 49908285440 207002060615 1099511627776 26212245085149 209330521254133760 qz614 (@Enclosure.Real.IsNear.neg (Real.sin qz365) Bool.true 1044605 1048576 32817979 49908285440 (@Enclosure.Real.IsNear.recentre' (Real.sin qz365) Bool.true 1044605 1048576 32817979 49908285440 1044605 1048576 32817979 49908285440 (ep754 rfl rfl) rfl)) rfl)

noncomputable def ep756 := @ep706 564566387 34359738368 1626920311369 13083157578383360 Bool.false 207002060615 1099511627776 26212245085149 209330521254133760 Bool.false 20553320207189429714944 598180346633 1099511627776 1134793198977499 209330521254133760 Bool.false 12432709804502101786624 90459869567 1099511627776 1134423395153499 209330521254133760 (ep707 (BSN.head_sum_c_succ qz12 27 28 rfl rfl) (ep745 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep746 ep755) rfl rfl

noncomputable abbrev qz930 := (@Nat.cast Real Real.instNatCast 29)

noncomputable abbrev qz367 := (@Inv.inv Real Real.instInv (Real.sqrt qz930))

noncomputable abbrev qz368 := (@HMul.hMul Real Real Real qz0 qz9 (Real.log (Enclosure.sfrac Bool.false 29 1)))

noncomputable def ep757 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz14 qz914 qz15) (Complex.mk (@HMul.hMul Real Real Real qz0 qz367 (Real.cos qz368)) (@HMul.hMul Real Real Real qz0 qz367 (@Neg.neg Real Real.instNeg (Real.sin qz368)))) Bool.true 196564597785 1099511627776 25752935862971 209330521254133760 Bool.true 55218642705 1099511627776 25614733106851 209330521254133760 (BSN.cpow_neg_s_mk qz9 124004 1000 29 (@Eq.refl Real qz9) rfl)

noncomputable abbrev qz931 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 29) qz265)

noncomputable def ep758 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz930) 5646755 1048576 1 1048576 97357 97358 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz930) (Real.sqrt qz931) Bool.false 5646755 1048576 1 1048576 (BSN.sqrt_natCast_div_one 29) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz931) Bool.false 5646755 1048576 1 1048576 5646755 1048576 1 1048576 (BSN.sqrt_enclosure 29 1 2823377 2823378 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep759 := BSN.log_dyadic_bound 13 45 6 5 353956287581982421875 524288 190385 10371179520995104305 130276274797305 311797 58 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 13) (BSN.artanhQ 45) 0 5 10371179520995104305 353956287581982421875 130276274797305 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz369 := (Real.log (Enclosure.sfrac Bool.false 29 1))

noncomputable def ep760 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz369 124004 1000 0 1 3791236343078135 1125899906842624 50000000038077 9519250000000000000 23506423574353052627 56294995342131200 53450000040704313 82062500000000000000 qz270 (BSN.isNear_log_sfrac 29 1 3791236343078135 1125899906842624 50000000038077 9519250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz931) Bool.false 63606391034871975772160 18889465931478580854784 1000000000761540 190385000000000000000 3791236343078135 1125899906842624 50000000038077 9519250000000000000 (BSN.log_rat_reduce_isNear 29 1 4 58 32 311797 524288 24973259072661432 36028797018963968 190385 1000000000000000 rfl rfl rfl rfl (ep759 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep761 := nat_lit 3873475252537841611493114757297915947087393610360583118347404294801479332290145

noncomputable def ep762 := nat_lit 3620652107572162215896476512099268234459254929481353722793691866923457601121

noncomputable def ep763 := nat_lit 10138954129424944529370515783332095331896906376296652642025345270981236462739041

noncomputable def ep764 := BSN.sin_dyadic_bound_f 2785148459 2147483648 3 2 1048576 381142 ep761 ep95 ep762 ep763 ep97 ep762 1009499 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2785148459) qz272 0 2 ep761 ep95 ep762 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2785148459) qz273 0 2 ep763 ep97 ep762 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz932 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 218920629) qz280)

noncomputable def ep765 := @Enclosure.Real.IsNear.cos_image qz368 qz932 Bool.false 218920629 524288 171 262144 Bool.true 1009499 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz368 Bool.false 23506423574353052627 56294995342131200 53450000040704313 82062500000000000000 218920629 524288 171 262144 (ep760 rfl) rfl) (Enclosure.sfrac_false_div 218920629 524288) (BSN.cos_reduce1 qz932 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 97993699718739565477888) qz281) 226375608064910080 72057594037927936 Bool.false 1009499 1048576 66 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q1 218920629 524288 226375608064910080 72057594037927936 66 97993699718739565477888 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1009499 1048576 97993699718739565477888 75557863725914323419136 2785148459 2147483648 381142 380770 (ep764 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep766 := nat_lit 2153539874568832967369906632504219645374978341280093445180910693497232276872801

noncomputable def ep767 := nat_lit 6453378319491354577677926944488460399656016513981317628097144696757849915416161

noncomputable def ep768 := BSN.cos_dyadic_bound_f 2785148459 2147483648 3 2 1048576 381142 ep766 ep88 ep762 ep767 ep91 ep762 283587 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2785148459) qz266 0 2 ep766 ep88 ep762 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2785148459) qz267 0 2 ep767 ep91 ep762 rfl rfl rfl rfl) rfl rfl

noncomputable def ep769 := @Enclosure.Real.IsNear.sin_image qz368 qz932 Bool.false 218920629 524288 171 262144 Bool.false 283587 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz368 Bool.false 23506423574353052627 56294995342131200 53450000040704313 82062500000000000000 218920629 524288 171 262144 (ep760 rfl) rfl) (Enclosure.sfrac_false_div 218920629 524288) (BSN.sin_reduce1 qz932 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 97993699718739565477888) qz281) 226375608064910080 72057594037927936 Bool.false 283587 1048576 66 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q1 218920629 524288 226375608064910080 72057594037927936 66 97993699718739565477888 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 283587 1048576 97993699718739565477888 75557863725914323419136 2785148459 2147483648 381142 380770 (ep768 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz615 := (@Enclosure.Real.IsNear.recentre' qz367 Bool.false 194715 1048576 1 1048576 194715 1048576 1 1048576 (ep758 rfl rfl) rfl)

noncomputable def ep770 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz367 (Real.cos qz368)) (@HMul.hMul Real Real Real qz0 qz367 (@Neg.neg Real Real.instNeg (Real.sin qz368))) Bool.true 196564597785 1099511627776 25752935862971 209330521254133760 Bool.true 55218642705 1099511627776 25614733106851 209330521254133760 (@Enclosure.Real.IsNear.mulLit_ft qz367 (Real.cos qz368) 194715 1048576 1 1048576 1009499 1048576 32817979 49908285440 196564597785 1099511627776 25752935862971 209330521254133760 qz615 (@Enclosure.Real.IsNear.recentre' (Real.cos qz368) Bool.true 1009499 1048576 32817979 49908285440 1009499 1048576 32817979 49908285440 (ep765 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz367 (@Neg.neg Real Real.instNeg (Real.sin qz368)) 194715 1048576 1 1048576 283587 1048576 32817979 49908285440 55218642705 1099511627776 25614733106851 209330521254133760 qz615 (@Enclosure.Real.IsNear.neg (Real.sin qz368) Bool.false 283587 1048576 32817979 49908285440 (@Enclosure.Real.IsNear.recentre' (Real.sin qz368) Bool.false 283587 1048576 32817979 49908285440 283587 1048576 32817979 49908285440 (ep769 rfl rfl) rfl)) rfl)

noncomputable def ep771 := @ep704 196564597785 1099511627776 25752935862971 209330521254133760 Bool.true 55218642705 1099511627776 25614733106851 209330521254133760 Bool.false 441581185756341676802048 25100984303 68719476736 116054613484047 20933052125413376 Bool.false 38748138711860916518912 17620613431 549755813888 116003812826035 20933052125413376 (ep705 (BSN.head_sum_c_succ qz12 28 29 rfl rfl) (ep756 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep757 ep770) rfl rfl

noncomputable abbrev qz933 := (@Nat.cast Real Real.instNatCast 30)

noncomputable abbrev qz370 := (@Inv.inv Real Real.instInv (Real.sqrt qz933))

noncomputable abbrev qz371 := (@HMul.hMul Real Real Real qz0 qz9 (Real.log (Enclosure.sfrac Bool.false 30 1)))

noncomputable def ep772 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz14 qz913 qz15) (Complex.mk (@HMul.hMul Real Real Real qz0 qz370 (Real.cos qz371)) (@HMul.hMul Real Real Real qz0 qz370 (@Neg.neg Real Real.instNeg (Real.sin qz371)))) Bool.false 141514857043 1099511627776 25271953469089 209330521254133760 Bool.true 142376350543 1099511627776 25272810201589 209330521254133760 (BSN.cpow_neg_s_mk qz9 124004 1000 30 (@Eq.refl Real qz9) rfl)

noncomputable abbrev qz934 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 30) qz265)

noncomputable def ep773 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz933) 5743287 1048576 1 1048576 95721 95722 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz933) (Real.sqrt qz934) Bool.false 5743287 1048576 1 1048576 (BSN.sqrt_natCast_div_one 30) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz934) Bool.false 5743287 1048576 1 1048576 5743287 1048576 1 1048576 (BSN.sqrt_enclosure 30 1 2871643 2871644 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep774 := BSN.log_dyadic_bound 14 46 6 5 440963670083462507520 524288 190385 14425761949190022144 273345648952320 329571 60 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 14) (BSN.artanhQ 46) 0 5 14425761949190022144 440963670083462507520 273345648952320 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz372 := (Real.log (Enclosure.sfrac Bool.false 30 1))

noncomputable def ep775 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz372 124004 1000 0 1 3829405717437687 1125899906842624 50000000038077 9519250000000000000 118715406646285734687 281474976710656000 53450000040704313 82062500000000000000 qz270 (BSN.isNear_log_sfrac 30 1 3829405717437687 1125899906842624 50000000038077 9519250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz934) Bool.false 64246766873087041339392 18889465931478580854784 1000000000761540 190385000000000000000 3829405717437687 1125899906842624 50000000038077 9519250000000000000 (BSN.log_rat_reduce_isNear 30 1 4 60 32 329571 524288 24973259072661432 36028797018963968 190385 1000000000000000 rfl rfl rfl rfl (ep774 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep776 := nat_lit 293702046112341991968563059837388692734549961009989634379991422059655846182881

noncomputable def ep777 := nat_lit 67539321528212969968692861249387730411332196170149428760523562574660780001

noncomputable def ep778 := nat_lit 880971059693969549965751793789667302742827218637628604282453219053818216988641

noncomputable def ep779 := BSN.cos_dyadic_bound_f 1693146693 2147483648 3 2 1048576 381142 ep776 ep88 ep777 ep778 ep91 ep777 739201 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1693146693) qz266 0 2 ep776 ep88 ep777 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1693146693) qz267 0 2 ep778 ep91 ep777 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz616 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 55281169) (@Nat.cast Real Real.instNatCast 131072))

noncomputable def ep780 := @Enclosure.Real.IsNear.cos_image qz371 qz616 Bool.false 55281169 131072 171 262144 Bool.false 739201 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz371 Bool.false 118715406646285734687 281474976710656000 53450000040704313 82062500000000000000 55281169 131072 171 262144 (ep775 rfl) rfl) (Enclosure.sfrac_false_div 55281169 131072) (BSN.cos_reduce0 qz616 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14893075812089686130688) (@Nat.cast Real Real.instNatCast 18889465931478580854784)) 226375608064910080 72057594037927936 Bool.false 739201 1048576 67 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q0 55281169 131072 226375608064910080 72057594037927936 67 14893075812089686130688 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 739201 1048576 14893075812089686130688 18889465931478580854784 1693146693 2147483648 381142 380770 (ep779 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep781 := nat_lit 8218231046168814665658182011280390001

noncomputable def ep782 := BSN.sin_dyadic_bound_f 1693146693 2147483648 2 1 1048576 381142 ep781 ep123 ep781 ep781 ep124 ep781 743701 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1693146693) qz272 0 1 ep781 ep123 ep781 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1693146693) qz273 0 1 ep781 ep124 ep781 rfl rfl rfl rfl) rfl rfl

noncomputable def ep783 := @Enclosure.Real.IsNear.sin_image qz371 qz616 Bool.false 55281169 131072 171 262144 Bool.false 743701 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz371 Bool.false 118715406646285734687 281474976710656000 53450000040704313 82062500000000000000 55281169 131072 171 262144 (ep775 rfl) rfl) (Enclosure.sfrac_false_div 55281169 131072) (BSN.sin_reduce0 qz616 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14893075812089686130688) (@Nat.cast Real Real.instNatCast 18889465931478580854784)) 226375608064910080 72057594037927936 Bool.false 743701 1048576 67 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q0 55281169 131072 226375608064910080 72057594037927936 67 14893075812089686130688 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 743701 1048576 14893075812089686130688 18889465931478580854784 1693146693 2147483648 381142 380770 (ep782 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz617 := (@Enclosure.Real.IsNear.recentre' qz370 Bool.false 191443 1048576 1 1048576 191443 1048576 1 1048576 (ep773 rfl rfl) rfl)

noncomputable def ep784 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz370 (Real.cos qz371)) (@HMul.hMul Real Real Real qz0 qz370 (@Neg.neg Real Real.instNeg (Real.sin qz371))) Bool.false 141514857043 1099511627776 25271953469089 209330521254133760 Bool.true 142376350543 1099511627776 25272810201589 209330521254133760 (@Enclosure.Real.IsNear.mulLit_ff qz370 (Real.cos qz371) 191443 1048576 1 1048576 739201 1048576 32817979 49908285440 141514857043 1099511627776 25271953469089 209330521254133760 qz617 (@Enclosure.Real.IsNear.recentre' (Real.cos qz371) Bool.false 739201 1048576 32817979 49908285440 739201 1048576 32817979 49908285440 (ep780 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz370 (@Neg.neg Real Real.instNeg (Real.sin qz371)) 191443 1048576 1 1048576 743701 1048576 32817979 49908285440 142376350543 1099511627776 25272810201589 209330521254133760 qz617 (@Enclosure.Real.IsNear.neg (Real.sin qz371) Bool.false 743701 1048576 32817979 49908285440 (@Enclosure.Real.IsNear.recentre' (Real.sin qz371) Bool.false 743701 1048576 32817979 49908285440 743701 1048576 32817979 49908285440 (ep783 rfl rfl) rfl)) rfl)

noncomputable def ep785 := @ep702 141514857043 1099511627776 25271953469089 209330521254133760 Bool.true 142376350543 1099511627776 25272810201589 209330521254133760 Bool.false 37323651036136159051776 543130605891 1099511627776 1185818088309559 209330521254133760 Bool.true 58898157115239697481728 107135123681 1099511627776 1185310938461939 209330521254133760 (ep703 (BSN.head_sum_c_succ qz12 29 30 rfl rfl) (ep771 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep772 ep784) rfl rfl

noncomputable abbrev qz935 := (@Nat.cast Real Real.instNatCast 31)

noncomputable abbrev qz373 := (@Inv.inv Real Real.instInv (Real.sqrt qz935))

noncomputable abbrev qz374 := (@HMul.hMul Real Real Real qz0 qz9 (Real.log (Enclosure.sfrac Bool.false 31 1)))

noncomputable def ep786 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz14 qz912 qz15) (Complex.mk (@HMul.hMul Real Real Real qz0 qz373 (Real.cos qz374)) (@HMul.hMul Real Real Real qz0 qz373 (@Neg.neg Real Real.instNeg (Real.sin qz374)))) Bool.false 7000377259 274877906944 1237537357181 10466526062706688 Bool.false 48870433855 274877906944 1246002788129 10466526062706688 (BSN.cpow_neg_s_mk qz9 124004 1000 31 (@Eq.refl Real qz9) rfl)

noncomputable abbrev qz936 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 31) qz265)

noncomputable def ep787 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz935) 5838225 1048576 1 1048576 94164 94165 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz935) (Real.sqrt qz936) Bool.false 5838225 1048576 1 1048576 (BSN.sqrt_natCast_div_one 31) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz936) Bool.false 5838225 1048576 1 1048576 5838225 1048576 1 1048576 (BSN.sqrt_enclosure 31 1 2919112 2919113 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep788 := BSN.log_dyadic_bound 15 47 6 5 546767979591453359355 524288 190385 19788004106328479625 544934619140625 346763 62 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 15) (BSN.artanhQ 47) 0 5 19788004106328479625 546767979591453359355 544934619140625 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz375 := (Real.log (Enclosure.sfrac Bool.false 31 1))

noncomputable def ep789 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz375 124004 1000 0 1 3866325256314103 1125899906842624 50000000038077 9519250000000000000 119859949270993507103 281474976710656000 53450000040704313 82062500000000000000 qz270 (BSN.isNear_log_sfrac 31 1 3866325256314103 1125899906842624 50000000038077 9519250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz936) Bool.false 64866173951437069877248 18889465931478580854784 1000000000761540 190385000000000000000 3866325256314103 1125899906842624 50000000038077 9519250000000000000 (BSN.log_rat_reduce_isNear 31 1 4 62 32 346763 524288 24973259072661432 36028797018963968 190385 1000000000000000 rfl rfl rfl rfl (ep788 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep790 := BSN.sin_dyadic_bound_f 305536606 2147483648 1 0 1048576 381142 0 1 1 0 1 1 148684 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 305536606) qz272 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 305536606) qz273 0 0 rfl) rfl rfl

noncomputable abbrev qz937 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 223256553) qz280)

noncomputable def ep791 := @Enclosure.Real.IsNear.cos_image qz374 qz937 Bool.false 223256553 524288 171 262144 Bool.false 148684 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz374 Bool.false 119859949270993507103 281474976710656000 53450000040704313 82062500000000000000 223256553 524288 171 262144 (ep789 rfl) rfl) (Enclosure.sfrac_false_div 223256553 524288) (BSN.cos_reduce3 qz937 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 10750113654543405285376) qz281) 226375608064910080 72057594037927936 Bool.false 148684 1048576 67 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q3 223256553 524288 226375608064910080 72057594037927936 67 10750113654543405285376 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 148684 1048576 10750113654543405285376 75557863725914323419136 305536606 2147483648 381142 380770 (ep790 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep792 := nat_lit 8714711213891918528436298032583696

noncomputable def ep793 := BSN.cos_dyadic_bound_f 305536606 2147483648 2 1 1048576 381142 ep792 ep143 ep792 ep792 ep144 ep792 1037980 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 305536606) qz266 0 1 ep792 ep143 ep792 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 305536606) qz267 0 1 ep792 ep144 ep792 rfl rfl rfl rfl) rfl rfl

noncomputable def ep794 := @Enclosure.Real.IsNear.sin_image qz374 qz937 Bool.false 223256553 524288 171 262144 Bool.true 1037980 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz374 Bool.false 119859949270993507103 281474976710656000 53450000040704313 82062500000000000000 223256553 524288 171 262144 (ep789 rfl) rfl) (Enclosure.sfrac_false_div 223256553 524288) (BSN.sin_reduce3 qz937 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 10750113654543405285376) qz281) 226375608064910080 72057594037927936 Bool.false 1037980 1048576 67 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q3 223256553 524288 226375608064910080 72057594037927936 67 10750113654543405285376 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1037980 1048576 10750113654543405285376 75557863725914323419136 305536606 2147483648 381142 380770 (ep793 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz618 := (@Enclosure.Real.IsNear.recentre' qz373 Bool.false 188329 1048576 1 1048576 188329 1048576 1 1048576 (ep787 rfl rfl) rfl)

noncomputable def ep795 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz373 (Real.cos qz374)) (@HMul.hMul Real Real Real qz0 qz373 (@Neg.neg Real Real.instNeg (Real.sin qz374))) Bool.false 7000377259 274877906944 1237537357181 10466526062706688 Bool.false 48870433855 274877906944 1246002788129 10466526062706688 (@Enclosure.Real.IsNear.mulLit_ff qz373 (Real.cos qz374) 188329 1048576 1 1048576 37171 262144 32817979 49908285440 7000377259 274877906944 1237537357181 10466526062706688 qz618 (@Enclosure.Real.IsNear.recentre' (Real.cos qz374) Bool.false 148684 1048576 32817979 49908285440 37171 262144 32817979 49908285440 (ep791 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz373 (@Neg.neg Real Real.instNeg (Real.sin qz374)) 188329 1048576 1 1048576 259495 262144 32817979 49908285440 48870433855 274877906944 1246002788129 10466526062706688 qz618 (@Enclosure.Real.IsNear.neg (Real.sin qz374) Bool.true 259495 262144 32817979 49908285440 (@Enclosure.Real.IsNear.recentre' (Real.sin qz374) Bool.true 1037980 1048576 32817979 49908285440 259495 262144 32817979 49908285440 (ep794 rfl rfl) rfl)) rfl)

noncomputable def ep796 := @ep700 7000377259 274877906944 1237537357181 10466526062706688 Bool.false 48870433855 274877906944 1246002788129 10466526062706688 Bool.false 156991600339633819353088 571132114927 1099511627776 1210568835453179 209330521254133760 Bool.false 24284531720410540015616 88346611739 1099511627776 1210230994224519 209330521254133760 (ep701 (BSN.head_sum_c_succ qz12 30 31 rfl rfl) (ep785 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep786 ep795) rfl rfl

noncomputable def ep797 := @Enclosure.Complex.IsNear.mul qz43 (@HAdd.hAdd Complex Complex Complex qz13 qz44 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1))))) Bool.true ep691 ep484 ep692 ep486 Bool.true

noncomputable def ep798 := nat_lit 1552012291534080100769571005721

noncomputable def ep799 := nat_lit 21641544191638604590612480000000

noncomputable def ep800 := nat_lit 242596514319334462155731180937759

noncomputable def ep801 := @Enclosure.Real.IsNear.subLit_tt_n (@HMul.hMul Real Real Real qz0 (Complex.re qz43) (Complex.re (@HAdd.hAdd Complex Complex Complex qz13 qz44 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 (Complex.im qz43) (Complex.im (@HAdd.hAdd Complex Complex Complex qz13 qz44 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1))))))) ep798 ep799 ep800

noncomputable def ep802 := nat_lit 4120225390925115734983757004800000000

noncomputable def ep803 := nat_lit 92728112623860616132326632781931

noncomputable def ep804 := nat_lit 6086684303898357541109760000000000

noncomputable def ep805 := nat_lit 169973455708439762541054307420571

noncomputable def ep806 := nat_lit 9989770613773179314346393600000000000

noncomputable def ep807 := nat_lit 7439829307181286001440823472310515557592548583939369861120000000

noncomputable def ep808 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re qz43) (Complex.re (@HAdd.hAdd Complex Complex Complex qz13 qz44 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))))) 39175172509 274877906944 6123508396411 52332630313533440 39617242047307511469

noncomputable abbrev qz376 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 32)))

noncomputable abbrev qz377 := (@HMul.hMul Real Real Real qz0 qz9 (Real.log (Enclosure.sfrac Bool.false 32 1)))

noncomputable abbrev qz938 := (@Neg.neg Real Real.instNeg (Real.sin qz377))

noncomputable def ep809 := @Enclosure.Complex.IsNear.of_eq qz43 (Complex.mk (@HMul.hMul Real Real Real qz0 qz376 (Real.cos qz377)) (@HMul.hMul Real Real Real qz0 qz376 qz938)) Bool.true 39175172509 274877906944 6123508396411 52332630313533440 Bool.true 7187079599 68719476736 382049940611 3270789394595840 (BSN.cpow_neg_s_mk qz9 124004 1000 32 (@Eq.refl Real qz9) rfl)

noncomputable abbrev qz619 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 32) qz265)

noncomputable def ep810 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 32)) 5931641 1048576 1 1048576 92681 92682 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 32)) (Real.sqrt qz619) Bool.false 5931641 1048576 1 1048576 (BSN.sqrt_natCast_div_one 32) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz619) Bool.false 5931641 1048576 1 1048576 5931641 1048576 1 1048576 (BSN.sqrt_enclosure 32 1 2965820 2965821 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep811 := BSN.log_dyadic_bound 0 64 1 0 1 524288 190385 0 1 0 64 64 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 64) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz378 := (Real.log (Enclosure.sfrac Bool.false 32 1))

noncomputable def ep812 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz378 124004 1000 0 1 15608286920413395 4503599627370496 40000000038077 7615400000000000000 96774500563947131679 225179981368524800 42760000040704313 65650000000000000000 qz270 (BSN.isNear_log_sfrac 32 1 15608286920413395 4503599627370496 40000000038077 7615400000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz619) Bool.false 65465900263437584302080 18889465931478580854784 1000000000951925 190385000000000000000 15608286920413395 4503599627370496 40000000038077 7615400000000000000 (BSN.log_rat_reduce_isNear 32 1 5 64 64 0 524288 24973259072661432 36028797018963968 190385 1000000000000000 rfl rfl rfl rfl (ep811 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep813 := nat_lit 1057839920431547125576152918822798452869619631973509794730557614604542068138240

noncomputable def ep814 := nat_lit 270405392896146696344820133939008107065088072694418784189764842694476308736

noncomputable def ep815 := nat_lit 2770095325732220139000604126223808982485184131622448974834200799933247693005056

noncomputable def ep816 := BSN.sin_dyadic_bound_f 2013733146 2147483648 3 2 1048576 381142 ep813 ep95 ep814 ep815 ep97 ep814 845372 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2013733146) qz272 0 2 ep813 ep95 ep814 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2013733146) qz273 0 2 ep815 ep97 ep814 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz939 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 450641385) qz268)

noncomputable def ep817 := @Enclosure.Real.IsNear.cos_image qz377 qz939 Bool.false 450641385 1048576 171 262144 Bool.true 845372 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz377 Bool.false 96774500563947131679 225179981368524800 42760000040704313 65650000000000000000 450641385 1048576 171 262144 (ep812 rfl) rfl) (Enclosure.sfrac_false_div 450641385 1048576) (BSN.cos_reduce1 qz939 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 141703872619150709882880) qz271) 226375608064910080 72057594037927936 Bool.false 845372 1048576 68 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q1 450641385 1048576 226375608064910080 72057594037927936 68 141703872619150709882880 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 845372 1048576 141703872619150709882880 151115727451828646838272 2013733146 2147483648 381142 380770 (ep816 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep818 := nat_lit 587809024858813357185127097183305366308484279128702960976616348043720916214016

noncomputable def ep819 := nat_lit 1762886263790647778162691651282038082711322661240720045361469514445773796024576

noncomputable def ep820 := BSN.cos_dyadic_bound_f 2013733146 2147483648 3 2 1048576 381142 ep818 ep88 ep814 ep819 ep91 ep814 620368 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2013733146) qz266 0 2 ep818 ep88 ep814 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2013733146) qz267 0 2 ep819 ep91 ep814 rfl rfl rfl rfl) rfl rfl

noncomputable def ep821 := @Enclosure.Real.IsNear.sin_image qz377 qz939 Bool.false 450641385 1048576 171 262144 Bool.false 620368 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz377 Bool.false 96774500563947131679 225179981368524800 42760000040704313 65650000000000000000 450641385 1048576 171 262144 (ep812 rfl) rfl) (Enclosure.sfrac_false_div 450641385 1048576) (BSN.sin_reduce1 qz939 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 141703872619150709882880) qz271) 226375608064910080 72057594037927936 Bool.false 620368 1048576 68 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q1 450641385 1048576 226375608064910080 72057594037927936 68 141703872619150709882880 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 620368 1048576 141703872619150709882880 151115727451828646838272 2013733146 2147483648 381142 380770 (ep820 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz620 := (@Enclosure.Real.IsNear.recentre' qz376 Bool.false 185363 1048576 1 1048576 185363 1048576 1 1048576 (ep810 rfl rfl) rfl)

noncomputable def ep822 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz376 (Real.cos qz377)) (@HMul.hMul Real Real Real qz0 qz376 qz938) Bool.true 39175172509 274877906944 6123508396411 52332630313533440 Bool.true 7187079599 68719476736 382049940611 3270789394595840 (@Enclosure.Real.IsNear.mulLit_ft qz376 (Real.cos qz377) 185363 1048576 1 1048576 211343 262144 32817979 49908285440 39175172509 274877906944 6123508396411 52332630313533440 qz620 (@Enclosure.Real.IsNear.recentre' (Real.cos qz377) Bool.true 845372 1048576 32817979 49908285440 211343 262144 32817979 49908285440 (ep817 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz376 qz938 185363 1048576 1 1048576 38773 65536 32817979 49908285440 7187079599 68719476736 382049940611 3270789394595840 qz620 (@Enclosure.Real.IsNear.neg (Real.sin qz377) Bool.false 38773 65536 32817979 49908285440 (@Enclosure.Real.IsNear.recentre' (Real.sin qz377) Bool.false 620368 1048576 32817979 49908285440 38773 65536 32817979 49908285440 (ep821 rfl rfl) rfl)) rfl)

noncomputable def ep823 := @ep808 78731479121920000000 0 1 ep798 ep799 ep800 ep802 (@Enclosure.Complex.IsNear.re_isNear qz43 Bool.true 39175172509 274877906944 6123508396411 52332630313533440 Bool.true 7187079599 68719476736 382049940611 3270789394595840 (ep809 ep822))

noncomputable def ep824 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz13 qz44 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1))))) Bool.false 39617242047307511469 78731479121920000000 0 1 Bool.false

noncomputable def ep825 := @Enclosure.Complex.IsNear.addLitP qz44 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) Bool.false 479538813 961077626 0 1 Bool.true 124004000

noncomputable def ep826 := @ep825 480538813 0 1 Bool.false 693851313 163840000000 0 1 Bool.false 74413291054313 184320000000000 0 1 Bool.false 79234484094615022938 39617242047307511469 78731479121920000000 0 1 Bool.false 12902057274663087550469 12902057274663087550469 88572914012160000000000 0 1

noncomputable abbrev qz48 := (@HDiv.hDiv Complex Complex Complex qz346 qz609 (@HSub.hSub Complex Complex Complex qz595 qz259 (1 : Complex)))

noncomputable def ep827 := @Enclosure.Complex.IsNear.addLitP qz48 qz24 Bool.true 64000000 61508968064 0 1 Bool.true 15872512000 61508968064 0 1

noncomputable def ep828 := @Enclosure.Complex.IsNear.of_eq qz48 (Complex.mk (Enclosure.sfrac Bool.true 64000000 61508968064) (Enclosure.sfrac Bool.true 15872512000 61508968064)) Bool.true 64000000 61508968064 0 1 Bool.true 15872512000 61508968064 0 1

noncomputable def ep829 := @ep827 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 61380968064 479538813 961077626 0 1 Bool.true 15872512000 124004000 480538813 0 1 (ep828 (BSN.N_div_s_sub_one_mk qz9 124004 1000 32 (@Eq.refl Real qz9) rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 64000000 61508968064) (Enclosure.sfrac Bool.true 15872512000 61508968064) Bool.true 64000000 61508968064 0 1 Bool.true 15872512000 61508968064 0 1 (Enclosure.Real.IsNear.const Bool.true 64000000 61508968064) (Enclosure.Real.IsNear.const Bool.true 15872512000 61508968064))) qz351 rfl

noncomputable abbrev qz49 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)))

noncomputable abbrev qz50 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz254 qz609 3))

noncomputable def ep830 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz13 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) qz50)) Bool.false 693851313 163840000000 0 1

noncomputable def ep831 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) qz50) Bool.false 1 768 0 1 Bool.false

noncomputable def ep832 := @ep831 31001 96000 0 1 Bool.false 1441553939 491520000000 0 1 Bool.false 14891371054313 184320000000000 0 1 Bool.false 1598633425152 693851313 163840000000 0 1 Bool.false 7143675941214048000 74413291054313 184320000000000 0

noncomputable abbrev qz51 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)))

noncomputable abbrev qz52 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz254 qz609 1))

noncomputable def ep833 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz13 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) qz52)) Bool.false 1 768 0 1

noncomputable def ep834 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) qz52) Bool.false 0 1 0 1 Bool.false

noncomputable def ep835 := @ep834 0 1 0 1 Bool.false 1 768 0 1 Bool.false 31001 96000 0 1 Bool.false 1 1 768 0 1 Bool.false 31001 31001 96000 0

noncomputable def ep836 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (Complex.mk qz262 qz262) Bool.false 0 1 0 1 Bool.false

noncomputable def ep837 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) qz52 Bool.false 1 768 0 1 Bool.false 31001 96000 0 1

noncomputable def ep838 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz52)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz52)) 1 768 0 1 0 1 0

noncomputable def ep839 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz52) 1 24 0 1 1 32 0 1 1

noncomputable def ep840 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep841 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep842 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz262) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 1 1 6 2 Bool.false BSN.bern_real_1 EMRow41.d10 rfl) qz606

noncomputable def ep843 := @ep841 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep842) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 124004 1000 0 1 ep438)

noncomputable def ep844 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 124004 1000 0 1 0 1 0

noncomputable def ep845 := @ep844 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep842) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 124004 1000 0 1 ep438)

noncomputable def ep846 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)))) 31001 3000 0 1 0 1 0 1 31001

noncomputable def ep847 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 124004 1000 0 1 31001 3000 0

noncomputable def ep848 := @ep847 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep842) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 124004 1000 0 1 ep438)

noncomputable def ep849 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep850 := @ep849 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep842) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 124004 1000 0 1 ep438)

noncomputable def ep851 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 31001 3000 0 1 (@ep840 1 24 0 1 (ep843 rfl) (ep845 rfl) rfl rfl) (@ep846 31001 3000 0 1 (ep848 rfl) (ep850 rfl) rfl rfl)

noncomputable def ep852 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 31001 3000 0 1 ep851

noncomputable abbrev qz53 := (@Enclosure.Complex.IsNear.of_eq (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz254 qz609 1)) (Complex.mk (Enclosure.sfrac Bool.false 1 32) qz262) Bool.false 1 32 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 32 1 32 EMRow41.d11 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 32) qz262 Bool.false 1 32 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 32) qz274))

noncomputable abbrev qz940 := (@Enclosure.Complex.IsNear.re_isNear qz52 Bool.false 1 32 0 1 Bool.false 0 1 0 1 qz53)

noncomputable def ep853 := @ep839 768 0 1 ep852 qz940

noncomputable def ep854 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz52) 31001 3000 0 1 0 1 0 1 0

noncomputable def ep855 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 31001 3000 0 1 ep851

noncomputable abbrev qz941 := (@Enclosure.Complex.IsNear.im_isNear qz52 Bool.false 1 32 0 1 Bool.false 0 1 0 1 qz53)

noncomputable def ep856 := @ep854 1 0 1 ep855 qz941

noncomputable def ep857 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz52)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz52)) 0 1 0 1 31001 96000 0

noncomputable def ep858 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz52) 1 24 0 1 0 1 0 1 0

noncomputable def ep859 := @ep858 1 0 1 ep852 qz941

noncomputable def ep860 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz52) 31001 3000 0 1 1 32 0 1 31001

noncomputable def ep861 := @ep860 96000 0 1 ep855 qz940

noncomputable def ep862 := @ep835 1 (@ep836 0 1 0 1 (BSN.bern_sum_base qz12 32) qz354) (ep837 (@ep838 1 1 1 768 0 1 (ep853 rfl) (ep856 rfl) rfl rfl) (@ep857 1 31001 31001 96000 0 1 (ep859 rfl) (ep861 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep863 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) qz50 Bool.false 1441553939 491520000000 0 1 Bool.false 14891371054313 184320000000000 0 1

noncomputable def ep864 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.re qz50)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.im qz50)) 1441553939 491520000000 0 1 0 1 0

noncomputable def ep865 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.re qz50) 1441553939 15000000 0 1 1 32768 0 1 1441553939

noncomputable def ep866 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)))) 1441553939 15000000 0 1 0 1 0 1 1441553939

noncomputable def ep867 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 4324661817 62500 0 1 1441553939 15000000 0

noncomputable def ep868 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (Complex.mk (Enclosure.sfrac Bool.true 1 720) qz262) Bool.true 1 720 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 2 1 30 24 Bool.true BSN.bern_real_2 EMRow41.d12 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 1 720) qz262 Bool.true 1 720 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.true 1 720) qz274)

noncomputable def ep869 := @ep867 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep868) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 4324661817 62500 0 1 Bool.true 14891371054313 7812500 0 1 EMRow41.d13)

noncomputable def ep870 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 14891371054313 7812500 0 1 0 1 0

noncomputable def ep871 := @ep870 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep868) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 4324661817 62500 0 1 Bool.true 14891371054313 7812500 0 1 EMRow41.d13)

noncomputable def ep872 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)))) 14891371054313 5625000000 0 1 0 1 0 1 14891371054313

noncomputable def ep873 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 14891371054313 7812500 0 1 14891371054313 5625000000 0

noncomputable def ep874 := @ep873 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep868) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 4324661817 62500 0 1 Bool.true 14891371054313 7812500 0 1 EMRow41.d13)

noncomputable def ep875 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 4324661817 62500 0 1 0 1 0

noncomputable def ep876 := @ep875 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep868) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 4324661817 62500 0 1 Bool.true 14891371054313 7812500 0 1 EMRow41.d13)

noncomputable def ep877 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 1441553939 15000000 0 1 Bool.false 14891371054313 5625000000 0 1 (@ep866 1441553939 15000000 0 1 (ep869 rfl) (ep871 rfl) rfl rfl) (@ep872 14891371054313 5625000000 0 1 (ep874 rfl) (ep876 rfl) rfl rfl)

noncomputable def ep878 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 1441553939 15000000 0 1 Bool.false 14891371054313 5625000000 0 1 ep877

noncomputable abbrev qz54 := (@Enclosure.Complex.IsNear.of_eq (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz254 qz609 3)) (Complex.mk (Enclosure.sfrac Bool.false 1 32768) qz262) Bool.false 1 32768 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 32 3 32768 EMRow41.d14 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 32768) qz262 Bool.false 1 32768 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 32768) qz274))

noncomputable abbrev qz942 := (@Enclosure.Complex.IsNear.re_isNear qz50 Bool.false 1 32768 0 1 Bool.false 0 1 0 1 qz54)

noncomputable def ep879 := @ep865 491520000000 0 1 ep878 qz942

noncomputable def ep880 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.im qz50) 14891371054313 5625000000 0 1 0 1 0 1 0

noncomputable def ep881 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 1441553939 15000000 0 1 Bool.false 14891371054313 5625000000 0 1 ep877

noncomputable abbrev qz943 := (@Enclosure.Complex.IsNear.im_isNear qz50 Bool.false 1 32768 0 1 Bool.false 0 1 0 1 qz54)

noncomputable def ep882 := @ep880 1 0 1 ep881 qz943

noncomputable def ep883 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.im qz50)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.re qz50)) 0 1 0 1 14891371054313 184320000000000 0

noncomputable def ep884 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.im qz50) 1441553939 15000000 0 1 0 1 0 1 0

noncomputable def ep885 := @ep884 1 0 1 ep878 qz943

noncomputable def ep886 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.re qz50) 14891371054313 5625000000 0 1 1 32768 0 1 14891371054313

noncomputable def ep887 := @ep886 184320000000000 0 1 ep881 qz942

noncomputable def ep888 := @ep832 1 (@ep833 Bool.false 31001 96000 0 1 (BSN.bern_sum_succ qz12 32 0 1 1 rfl rfl) (ep862 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep863 (@ep864 1 1441553939 1441553939 491520000000 0 1 (ep879 rfl) (ep882 rfl) rfl rfl) (@ep883 1 14891371054313 14891371054313 184320000000000 0 1 (ep885 rfl) (ep887 rfl) rfl rfl)) rfl rfl rfl rfl

noncomputable def ep889 := ep826 (ep829 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep830 Bool.false 74413291054313 184320000000000 0 1 (BSN.bern_sum_succ qz12 32 1 2 3 rfl rfl) (ep888 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep890 := @Enclosure.Real.IsNear.mulLit_tf (Complex.im qz43) (Complex.im (@HAdd.hAdd Complex Complex Complex qz13 qz44 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))))) 7187079599 68719476736 382049940611 3270789394595840 12902057274663087550469

noncomputable def ep891 := @ep890 88572914012160000000000 0 1 ep803 ep804 ep805 ep806 (@Enclosure.Complex.IsNear.im_isNear qz43 Bool.true 39175172509 274877906944 6123508396411 52332630313533440 Bool.true 7187079599 68719476736 382049940611 3270789394595840 (ep809 ep822))

noncomputable def ep892 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz13 qz44 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1))))) Bool.false 39617242047307511469 78731479121920000000 0 1 Bool.false

noncomputable def ep893 := nat_lit 505440319455924849644193318856721

noncomputable def ep894 := nat_lit 2724339863875001387119535317964371

noncomputable def ep895 := @Enclosure.Real.IsNear.addLit_tt (@HMul.hMul Real Real Real qz0 (Complex.re qz43) (Complex.im (@HAdd.hAdd Complex Complex Complex qz13 qz44 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 (Complex.im qz43) (Complex.re (@HAdd.hAdd Complex Complex Complex qz13 qz44 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1))))))) ep893 ep484 ep894

noncomputable def ep896 := nat_lit 159836329820370869029542297600000000000

noncomputable def ep897 := nat_lit 284732272086848808558308420931

noncomputable def ep898 := nat_lit 5410386047909651147653120000000

noncomputable def ep899 := nat_lit 15135764971345446809185651367559

noncomputable def ep900 := nat_lit 257514086932819733436484812800000000

noncomputable def ep901 := nat_lit 9666929057732689123109336380552356240629359618530234859520000000

noncomputable def ep902 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re qz43) (Complex.im (@HAdd.hAdd Complex Complex Complex qz13 qz44 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))))) 39175172509 274877906944 6123508396411 52332630313533440 12902057274663087550469

noncomputable def ep903 := @ep902 88572914012160000000000 0 1 ep893 ep484 ep894 ep896 (@Enclosure.Complex.IsNear.re_isNear qz43 Bool.true 39175172509 274877906944 6123508396411 52332630313533440 Bool.true 7187079599 68719476736 382049940611 3270789394595840 (ep809 ep822))

noncomputable def ep904 := @Enclosure.Real.IsNear.mulLit_tf (Complex.im qz43) (Complex.re (@HAdd.hAdd Complex Complex Complex qz13 qz44 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))))) 7187079599 68719476736 382049940611 3270789394595840 39617242047307511469

noncomputable def ep905 := @ep904 78731479121920000000 0 1 ep897 ep898 ep899 ep900 (@Enclosure.Complex.IsNear.im_isNear qz43 Bool.true 39175172509 274877906944 6123508396411 52332630313533440 Bool.true 7187079599 68719476736 382049940611 3270789394595840 (ep809 ep822))

noncomputable abbrev qz944 := (ep889 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep906 := @ep797 ep693 ep484 ep694 ep486 (@ep801 ep802 ep803 ep804 ep805 ep806 ep807 ep691 ep484 ep692 ep486 (ep823 (@ep824 12902057274663087550469 88572914012160000000000 0 1 qz944) rfl) (ep891 (@ep892 12902057274663087550469 88572914012160000000000 0 1 qz944) rfl) rfl rfl) (@ep895 ep896 ep897 ep898 ep899 ep900 ep901 ep693 ep484 ep694 ep486 (ep903 (@ep892 12902057274663087550469 88572914012160000000000 0 1 qz944) rfl) (ep905 (@ep824 12902057274663087550469 88572914012160000000000 0 1 qz944) rfl) rfl rfl)

noncomputable def ep907 := @ep697 ep688 ep486 (@ep698 209330521254133760 (BSN.head_sum_c_eq qz12 32) (ep699 (BSN.head_sum_c_succ qz12 31 32 rfl rfl) (ep796 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep906 rfl rfl rfl

noncomputable def ep908 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz12 2 32) Bool.false ep483 ep484 ep485 ep486 Bool.false ep687 ep484 ep688 ep486 (@ep689 ep486 Bool.false ep687 ep484 ep688 ep486 (BSN.zetaApproximant_eq_folded' qz12 2 32 rfl) (ep907 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep909 := @Enclosure.Real.IsNear.mulLit_tf (Real.sin (@HSub.hSub Real Real Real qz597 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz21 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz22 (@Nat.cast Complex Complex.instNatCast j))))) qz342)) (Complex.im (zetaApproximant qz12 2 32)) 209 524288 17206409

noncomputable def ep910 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz597 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz21 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz22 (@Nat.cast Complex Complex.instNatCast j))))) qz342)) Bool.true 418 1048576 17206409

noncomputable def ep911 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz597 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz21 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz22 (@Nat.cast Complex Complex.instNatCast j))))) qz342) qz895 Bool.false 64237083 524288 89

noncomputable def ep912 := BSN.sin_dyadic_bound_f 856729 2147483648 1 0 1048576 381142 0 1 1 0 1 1 418 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 856729) qz272 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 856729) qz273 0 0 rfl) rfl rfl

noncomputable def ep913 := @ep911 262144 Bool.true 418 1048576 1 190385 (@ep493 64237083 524288 89 262144 ep684 rfl) (Enclosure.sfrac_false_div 64237083 524288) (BSN.sin_reduce2 qz895 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 30143500789015904256) qz281) 226375608064910080 72057594037927936 Bool.false 418 1048576 19 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q2 64237083 524288 226375608064910080 72057594037927936 19 30143500789015904256 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 418 1048576 30143500789015904256 75557863725914323419136 856729 2147483648 381142 380770 (ep912 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep914 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz12 2 32) Bool.false ep483 ep484 ep485 ep486 Bool.false ep687 ep484 ep688 ep486 (@ep689 ep486 Bool.false ep687 ep484 ep688 ep486 (BSN.zetaApproximant_eq_folded' qz12 2 32 rfl) (ep907 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow41.d15 : Enclosure.Real.IsNear (hardyZApproximantEM 2 32 qz9) Bool.true ep467 ep468 ep469 ep470 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 2 32 qz9) ep471 Bool.true ep467 ep468 ep469 ep470 (@Eq.refl Real ep471) (@ep472 Bool.true ep467 ep468 ep469 ep470 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz597 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz21 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz22 (@Nat.cast Complex Complex.instNatCast j))))) qz342) (zetaApproximant qz12 2 32)) (@ep474 ep475 ep476 ep470 ep477 ep478 ep479 ep480 ep481 ep467 ep468 ep469 ep470 (@ep482 49908285440 ep483 ep484 ep485 ep486 ep473 ep475 ep476 ep470 (@ep487 49908285440 1048575 1048576 17206409 49908285440 (ep686 rfl rfl) rfl) ep908 rfl) (@ep909 49908285440 ep687 ep484 ep688 ep486 ep477 ep478 ep479 ep480 (@ep910 49908285440 209 524288 17206409 49908285440 (ep913 rfl rfl) rfl) ep914 rfl) rfl rfl))

noncomputable abbrev qz621 := (@HAdd.hAdd Complex Complex Complex qz813 (@HAdd.hAdd Complex Complex Complex qz813 qz814 (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I (@HDiv.hDiv Complex Complex Complex qz815 (↑(Enclosure.sfrac Bool.false 126105 1000)) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 4))

noncomputable abbrev qz379 := (@HPow.hPow Complex Nat Complex qz543 qz621 3)

noncomputable abbrev qz55 := qz379

noncomputable def ep915 := Enclosure.Complex.IsNear qz55 Bool.true 32391910891 640000 0 1 Bool.true 15824382798861 64000000 0 1

noncomputable abbrev qz380 := qz621

noncomputable abbrev qz56 := (@HPow.hPow Complex Nat Complex qz254 qz380 2)

noncomputable abbrev qz57 := qz380

noncomputable def ep916 := @Enclosure.Complex.IsNear.of_eq qz55 (@HMul.hMul Complex Complex Complex qz3 qz56 qz57) Bool.true 32391910891 640000 0 1 Bool.true 15824382798861 64000000

noncomputable def ep917 := @Enclosure.Complex.IsNear.mul qz56 qz57 Bool.true 32391910891 640000 0 1 Bool.true 15824382798861 64000000 0

noncomputable def ep918 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re qz56) (Complex.re qz57)) (@HMul.hMul Real Real Real qz0 (Complex.im qz56) (Complex.im qz57)) 10764550297 640000 0 1 10813680297 320000

noncomputable def ep919 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re qz56) (Complex.re qz57) 633208841 160000 0 1 17000 4000 0 1

noncomputable def ep920 := @Enclosure.Complex.IsNear.re_isNear qz56 Bool.true 633208841 160000 0 1 Bool.false 428757 800 0 1

noncomputable abbrev qz381 := (@HPow.hPow Complex Nat Complex qz543 qz621 1)

noncomputable abbrev qz58 := qz381

noncomputable def ep921 := @Enclosure.Complex.IsNear.of_eq qz56 (@HMul.hMul Complex Complex Complex qz3 qz58 qz57) Bool.true 633208841 160000 0 1 Bool.false 428757 800

noncomputable def ep922 := @Enclosure.Complex.IsNear.mul qz58 qz57 Bool.true 633208841 160000 0 1 Bool.false 428757 800 0

noncomputable abbrev qz59 := (Complex.re qz381)

noncomputable abbrev qz60 := (Complex.im qz381)

noncomputable def ep923 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz59 (Complex.re qz57)) (@HMul.hMul Real Real Real qz0 qz60 (Complex.im qz57)) 289 16 0 1 636098841 160000

noncomputable def ep924 := @Enclosure.Real.IsNear.mulLit_ff qz59 (Complex.re qz57) 17000 4000 0 1 17000 4000 0 1

noncomputable def ep925 := @Enclosure.Complex.IsNear.re_isNear qz58 Bool.false 17000 4000 0 1 Bool.false 252210 4000 0 1

noncomputable def ep926 := @Enclosure.Complex.IsNear.of_eq qz58 qz57 Bool.false 17000 4000 0 1 Bool.false 252210 4000 0

noncomputable abbrev qz382 := (Enclosure.sfrac Bool.false 126105 1000)

noncomputable abbrev qz61 := qz382

noncomputable abbrev qz383 := (Enclosure.sfrac Bool.false 252210 4000)

noncomputable abbrev qz622 := (Complex.mk (Enclosure.sfrac Bool.false 17000 4000) qz383)

noncomputable def ep927 := @Enclosure.Complex.IsNear.of_eq qz57 qz622 Bool.false 17000 4000 0 1 Bool.false 252210 4000 0 1 (BSN.w_shift_mk qz61 Bool.false 126105 1000 4 (@Eq.refl Real qz61) rfl)

noncomputable abbrev qz62 := (@ep926 1 (BSN.pow_one_c qz380) (ep927 (@Enclosure.Complex.IsNear.mk qz547 qz383 Bool.false 17000 4000 0 1 Bool.false 252210 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 17000 4000) (Enclosure.Real.IsNear.const Bool.false 252210 4000))))

noncomputable abbrev qz63 := (ep927 (@Enclosure.Complex.IsNear.mk qz547 qz383 Bool.false 17000 4000 0 1 Bool.false 252210 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 17000 4000) (Enclosure.Real.IsNear.const Bool.false 252210 4000)))

noncomputable abbrev qz945 := (@Enclosure.Complex.IsNear.re_isNear qz57 Bool.false 17000 4000 0 1 Bool.false 252210 4000 0 1 qz63)

noncomputable def ep928 := @ep924 289 16 0 1 (ep925 qz62) qz945

noncomputable def ep929 := @Enclosure.Real.IsNear.mulLit_ff qz60 (Complex.im qz57) 252210 4000 0 1 252210 4000 0 1

noncomputable def ep930 := @Enclosure.Complex.IsNear.im_isNear qz58 Bool.false 17000 4000 0 1 Bool.false 252210 4000 0 1

noncomputable abbrev qz946 := (@Enclosure.Complex.IsNear.im_isNear qz57 Bool.false 17000 4000 0 1 Bool.false 252210 4000 0 1 qz63)

noncomputable def ep931 := @ep929 636098841 160000 0 1 (ep930 qz62) qz946

noncomputable def ep932 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz59 (Complex.im qz57)) (@HMul.hMul Real Real Real qz0 qz60 (Complex.re qz57)) 428757 1600 0 1 428757 1600

noncomputable def ep933 := @Enclosure.Real.IsNear.mulLit_ff qz59 (Complex.im qz57) 17000 4000 0 1 252210 4000 0 1

noncomputable def ep934 := @ep933 428757 1600 0 1 (ep925 qz62) qz946

noncomputable def ep935 := @Enclosure.Real.IsNear.mulLit_ff qz60 (Complex.re qz57) 252210 4000 0 1 17000 4000 0 1

noncomputable def ep936 := @ep935 428757 1600 0 1 (ep930 qz62) qz945

noncomputable abbrev qz623 := (@ep921 0 1 (BSN.pow_succ_c qz57 1 2 rfl) (@ep922 1 (@ep923 0 1 10131341456 633208841 160000 0 1 (ep928 rfl) (ep931 rfl) rfl rfl) (@ep932 0 1 1372022400 428757 800 0 1 (ep934 rfl) (ep936 rfl) rfl rfl)))

noncomputable def ep937 := @ep919 10764550297 640000 0 1 (ep920 qz623) qz945

noncomputable def ep938 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz56) (Complex.im qz57) 428757 800 0 1 252210 4000 0 1

noncomputable def ep939 := @Enclosure.Complex.IsNear.im_isNear qz56 Bool.true 633208841 160000 0 1 Bool.false 428757 800 0 1

noncomputable def ep940 := @ep938 10813680297 320000 0 1 (ep939 qz623) qz946

noncomputable def ep941 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re qz56) (Complex.im qz57)) (@HMul.hMul Real Real Real qz0 (Complex.im qz56) (Complex.re qz57)) 15970160178861 64000000 0 1 7288869 3200

noncomputable def ep942 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re qz56) (Complex.im qz57) 633208841 160000 0 1 252210 4000 0 1

noncomputable def ep943 := @ep942 15970160178861 64000000 0 1 (ep920 qz623) qz946

noncomputable def ep944 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz56) (Complex.re qz57) 428757 800 0 1 17000 4000 0 1

noncomputable def ep945 := @ep944 7288869 3200 0 1 (ep939 qz623) qz945

theorem EMRow41.d16 : ep915 := @ep916 0 1 (BSN.pow_succ_c qz57 2 3 rfl) (@ep917 1 (@ep918 0 1 10365411485120000 32391910891 640000 0 1 (ep937 rfl) (ep940 rfl) rfl rfl) (@ep941 0 1 50638024956355200 15824382798861 64000000 0 1 (ep943 rfl) (ep945 rfl) rfl rfl))

noncomputable abbrev qz384 := (@HAdd.hAdd Complex Complex Complex qz549 qz550 (@HMul.hMul Complex Complex Complex qz545 Complex.I ↑(Enclosure.sfrac Bool.false 126105 1000)))

noncomputable abbrev qz64 := qz384

noncomputable abbrev qz65 := (@Neg.neg Complex Complex.instNeg qz384)

noncomputable def ep946 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 9) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 8) (@HPow.hPow Complex Complex Complex qz14 qz818 qz65)) Bool.false 3241342526577 1099511627776 473063329695157 209330521254133760 Bool.false 299101308825 549755813888 236499765174481 104665260627066880

noncomputable def ep947 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 8) (@HPow.hPow Complex Complex Complex qz14 qz818 qz65) Bool.false 3278220965629 1099511627776 423531243478689 209330521254133760 Bool.false 26402590201 137438953472 105821912562511 52332630313533440 Bool.true

noncomputable def ep948 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 8) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 7) (@HPow.hPow Complex Complex Complex qz14 qz819 qz65)) Bool.false 3278220965629 1099511627776 423531243478689 209330521254133760 Bool.false 26402590201 137438953472 105821912562511 52332630313533440

noncomputable def ep949 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 7) (@HPow.hPow Complex Complex Complex qz14 qz819 qz65) Bool.false 721767893451 274877906944 92602854257417 52332630313533440 Bool.false 351598640283 1099511627776 370288288386693 209330521254133760 Bool.false

noncomputable def ep950 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 7) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 6) (@HPow.hPow Complex Complex Complex qz14 qz820 qz65)) Bool.false 721767893451 274877906944 92602854257417 52332630313533440 Bool.false 351598640283 1099511627776 370288288386693 209330521254133760

noncomputable def ep951 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 6) (@HPow.hPow Complex Complex Complex qz14 qz820 qz65) Bool.false 612899698329 274877906944 6020093495559 4025586947194880 Bool.false 242738150583 1099511627776 24082076273101 16102347788779520 Bool.false

noncomputable def ep952 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 6) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 5) (@HPow.hPow Complex Complex Complex qz14 qz16 qz65)) Bool.false 612899698329 274877906944 6020093495559 4025586947194880 Bool.false 242738150583 1099511627776 24082076273101 16102347788779520

noncomputable def ep953 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 5) (@HPow.hPow Complex Complex Complex qz14 qz16 qz65) Bool.false 1304351502465 549755813888 25035134372683 20933052125413376 Bool.false 354340493919 549755813888 25024808727977 20933052125413376 Bool.true

noncomputable def ep954 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 5) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 4) (@HPow.hPow Complex Complex Complex qz14 qz17 qz65)) Bool.false 1304351502465 549755813888 25035134372683 20933052125413376 Bool.false 354340493919 549755813888 25024808727977 20933052125413376

noncomputable def ep955 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 4) (@HPow.hPow Complex Complex Complex qz14 qz17 qz65) Bool.false 591143239419 274877906944 3466165448621 4025586947194880 Bool.false 27013251415 137438953472 216402798991 251599184199680 Bool.false

noncomputable def ep956 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 4) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 3) (@HPow.hPow Complex Complex Complex qz14 qz552 qz65)) Bool.false 591143239419 274877906944 3466165448621 4025586947194880 Bool.false 27013251415 137438953472 216402798991 251599184199680

noncomputable def ep957 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 3) (@HPow.hPow Complex Complex Complex qz14 qz552 qz65) Bool.false 220012572457 137438953472 12399489475847 26166315156766720 Bool.false 102495031925 274877906944 24782891609579 52332630313533440 Bool.false

noncomputable def ep958 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 3) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 2) (@HPow.hPow Complex Complex Complex qz14 qz553 qz65)) Bool.false 220012572457 137438953472 12399489475847 26166315156766720 Bool.false 102495031925 274877906944 24782891609579 52332630313533440

noncomputable def ep959 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 2) (@HPow.hPow Complex Complex Complex qz14 qz553 qz65) Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable def ep960 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz262) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz64)

noncomputable abbrev qz385 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 2 1)))

noncomputable def ep961 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz14 qz553 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz263 (Real.cos qz385)) (@HMul.hMul Real Real Real qz0 qz263 (@Neg.neg Real Real.instNeg (Real.sin qz385)))) Bool.false 82573618985 137438953472 12399489475847 26166315156766720 Bool.false 102495031925 274877906944 24782891609579 52332630313533440 (BSN.cpow_neg_s_mk qz61 126105 1000 2 (@Eq.refl Real qz61) rfl)

noncomputable def ep962 := nat_lit 1454220631524441439005750057963046453620031420371757686697716071582476900000000

noncomputable def ep963 := nat_lit 510919978468558600972428221803233440067911155408771682411006289062500000000

noncomputable def ep964 := nat_lit 3807845878789349912042056696591725952959019959102989263389162367771814500000000

noncomputable def ep965 := BSN.sin_dyadic_bound_f 2180439850 2147483648 3 2 1048576 381142 ep962 ep95 ep963 ep964 ep97 ep963 890936 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2180439850) qz272 0 2 ep962 ep95 ep963 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2180439850) qz273 0 2 ep964 ep97 ep963 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz386 := (Enclosure.Real.IsNear.const Bool.false 126105 1000)

noncomputable abbrev qz947 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 91655131) qz268)

noncomputable def ep966 := @Enclosure.Real.IsNear.cos_image qz385 qz947 Bool.false 91655131 1048576 87 131072 Bool.false 890936 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz385 Bool.false 572844573 6553600 25221 38077000 91655131 1048576 87 131072 (@Enclosure.Real.IsNear.mulLit_ff qz61 qz269 126105 1000 0 1 363408 524288 1 190385 572844573 6553600 25221 38077000 qz386 qz554 rfl) rfl) (Enclosure.sfrac_false_div 91655131 1048576) (BSN.cos_reduce3 qz947 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 153434814057294522744832) qz271) 226375608064910080 72057594037927936 Bool.false 890936 1048576 13 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q3 91655131 1048576 226375608064910080 72057594037927936 13 153434814057294522744832 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 890936 1048576 153434814057294522744832 151115727451828646838272 2180439850 2147483648 381142 380770 (ep965 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep967 := nat_lit 808127426392897936603626666966938355762269860720047057802024931452070500000000

noncomputable def ep968 := nat_lit 2423360439221756692608935144457208600406673759849323630041252781778086500000000

noncomputable def ep969 := BSN.cos_dyadic_bound_f 2180439850 2147483648 3 2 1048576 381142 ep967 ep88 ep963 ep968 ep91 ep963 552940 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2180439850) qz266 0 2 ep967 ep88 ep963 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2180439850) qz267 0 2 ep968 ep91 ep963 rfl rfl rfl rfl) rfl rfl

noncomputable def ep970 := @Enclosure.Real.IsNear.sin_image qz385 qz947 Bool.false 91655131 1048576 87 131072 Bool.true 552940 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz385 Bool.false 572844573 6553600 25221 38077000 91655131 1048576 87 131072 (@Enclosure.Real.IsNear.mulLit_ff qz61 qz269 126105 1000 0 1 363408 524288 1 190385 572844573 6553600 25221 38077000 qz386 qz554 rfl) rfl) (Enclosure.sfrac_false_div 91655131 1048576) (BSN.sin_reduce3 qz947 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 153434814057294522744832) qz271) 226375608064910080 72057594037927936 Bool.false 552940 1048576 13 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q3 91655131 1048576 226375608064910080 72057594037927936 13 153434814057294522744832 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 552940 1048576 153434814057294522744832 151115727451828646838272 2180439850 2147483648 381142 380770 (ep969 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep971 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz263 (Real.cos qz385)) (@HMul.hMul Real Real Real qz0 qz263 (@Neg.neg Real Real.instNeg (Real.sin qz385))) Bool.false 82573618985 137438953472 12399489475847 26166315156766720 Bool.false 102495031925 274877906944 24782891609579 52332630313533440 (@Enclosure.Real.IsNear.mulLit_ff qz263 (Real.cos qz385) 741455 1048576 1 1048576 111367 131072 16694567 24954142720 82573618985 137438953472 12399489475847 26166315156766720 qz555 (@Enclosure.Real.IsNear.recentre' (Real.cos qz385) Bool.false 890936 1048576 16694567 24954142720 111367 131072 16694567 24954142720 (ep966 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz263 (@Neg.neg Real Real.instNeg (Real.sin qz385)) 741455 1048576 1 1048576 138235 262144 16694567 24954142720 102495031925 274877906944 24782891609579 52332630313533440 qz555 (@Enclosure.Real.IsNear.neg (Real.sin qz385) Bool.true 138235 262144 16694567 24954142720 (@Enclosure.Real.IsNear.recentre' (Real.sin qz385) Bool.true 552940 1048576 16694567 24954142720 138235 262144 16694567 24954142720 (ep970 rfl rfl) rfl)) rfl)

noncomputable def ep972 := @ep959 82573618985 137438953472 12399489475847 26166315156766720 Bool.false 102495031925 274877906944 24782891609579 52332630313533440 Bool.false 220012572457 220012572457 137438953472 12399489475847 26166315156766720 Bool.false 102495031925 102495031925 274877906944 24782891609579 52332630313533440 (ep960 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz262 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz274)) (ep961 ep971) rfl rfl

noncomputable abbrev qz387 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 3 1)))

noncomputable def ep973 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz14 qz552 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz275 (Real.cos qz387)) (@HMul.hMul Real Real Real qz0 qz275 (@Neg.neg Real Real.instNeg (Real.sin qz387)))) Bool.false 151118094505 274877906944 20261171880379 52332630313533440 Bool.true 48468529095 274877906944 20228890580549 52332630313533440 (BSN.cpow_neg_s_mk qz61 126105 1000 3 (@Eq.refl Real qz61) rfl)

noncomputable def ep974 := nat_lit 197344516330915999038070806643360000

noncomputable def ep975 := BSN.cos_dyadic_bound_f 666509380 2147483648 2 1 1048576 381142 ep974 ep143 ep974 ep974 ep144 ep974 998476 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 666509380) qz266 0 1 ep974 ep143 ep974 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 666509380) qz267 0 1 ep974 ep144 ep974 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz948 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 145270185) qz268)

noncomputable def ep976 := @Enclosure.Real.IsNear.cos_image qz387 qz948 Bool.false 145270185 1048576 87 131072 Bool.false 998476 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz387 Bool.false 14527018569 104857600 25221 38077000 145270185 1048576 87 131072 (@Enclosure.Real.IsNear.mulLit_ff qz61 qz277 126105 1000 0 1 575989 524288 1 190385 14527018569 104857600 25221 38077000 qz386 qz556 rfl) rfl) (Enclosure.sfrac_false_div 145270185 1048576) (BSN.cos_reduce0 qz948 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 46901428089515178721280) qz271) 226375608064910080 72057594037927936 Bool.false 998476 1048576 22 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q0 145270185 1048576 226375608064910080 72057594037927936 22 46901428089515178721280 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 998476 1048576 46901428089515178721280 151115727451828646838272 666509380 2147483648 381142 380770 (ep975 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep977 := BSN.sin_dyadic_bound_f 666509380 2147483648 2 1 1048576 381142 ep974 ep123 ep974 ep974 ep124 ep974 320244 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 666509380) qz272 0 1 ep974 ep123 ep974 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 666509380) qz273 0 1 ep974 ep124 ep974 rfl rfl rfl rfl) rfl rfl

noncomputable def ep978 := @Enclosure.Real.IsNear.sin_image qz387 qz948 Bool.false 145270185 1048576 87 131072 Bool.false 320244 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz387 Bool.false 14527018569 104857600 25221 38077000 145270185 1048576 87 131072 (@Enclosure.Real.IsNear.mulLit_ff qz61 qz277 126105 1000 0 1 575989 524288 1 190385 14527018569 104857600 25221 38077000 qz386 qz556 rfl) rfl) (Enclosure.sfrac_false_div 145270185 1048576) (BSN.sin_reduce0 qz948 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 46901428089515178721280) qz271) 226375608064910080 72057594037927936 Bool.false 320244 1048576 22 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q0 145270185 1048576 226375608064910080 72057594037927936 22 46901428089515178721280 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 320244 1048576 46901428089515178721280 151115727451828646838272 666509380 2147483648 381142 380770 (ep977 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep979 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz275 (Real.cos qz387)) (@HMul.hMul Real Real Real qz0 qz275 (@Neg.neg Real Real.instNeg (Real.sin qz387))) Bool.false 151118094505 274877906944 20261171880379 52332630313533440 Bool.true 48468529095 274877906944 20228890580549 52332630313533440 (@Enclosure.Real.IsNear.mulLit_ff qz275 (Real.cos qz387) 605395 1048576 1 1048576 249619 262144 16694567 24954142720 151118094505 274877906944 20261171880379 52332630313533440 qz557 (@Enclosure.Real.IsNear.recentre' (Real.cos qz387) Bool.false 998476 1048576 16694567 24954142720 249619 262144 16694567 24954142720 (ep976 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz275 (@Neg.neg Real Real.instNeg (Real.sin qz387)) 605395 1048576 1 1048576 80061 262144 16694567 24954142720 48468529095 274877906944 20228890580549 52332630313533440 qz557 (@Enclosure.Real.IsNear.neg (Real.sin qz387) Bool.false 80061 262144 16694567 24954142720 (@Enclosure.Real.IsNear.recentre' (Real.sin qz387) Bool.false 320244 1048576 16694567 24954142720 80061 262144 16694567 24954142720 (ep978 rfl rfl) rfl)) rfl)

noncomputable def ep980 := @ep957 151118094505 274877906944 20261171880379 52332630313533440 Bool.true 48468529095 274877906944 20228890580549 52332630313533440 Bool.false 81246108177795297312768 591143239419 274877906944 3466165448621 4025586947194880 Bool.false 14850692017414492651520 27013251415 137438953472 216402798991 251599184199680 (ep958 (BSN.head_sum_c_succ qz64 2 3 rfl rfl) (ep972 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep973 ep979) rfl rfl

noncomputable abbrev qz388 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 4 1)))

noncomputable def ep981 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz14 qz17 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz278 (Real.cos qz388)) (@HMul.hMul Real Real Real qz0 qz278 (@Neg.neg Real Real.instNeg (Real.sin qz388)))) Bool.false 122065023627 549755813888 35055370199269 104665260627066880 Bool.false 246287488259 549755813888 35100479259629 104665260627066880 (BSN.cpow_neg_s_mk qz61 126105 1000 4 (@Eq.refl Real qz61) rfl)

noncomputable def ep982 := nat_lit 953391202858218704683582771246232721

noncomputable def ep983 := BSN.sin_dyadic_bound_f 988138419 2147483648 2 1 1048576 381142 ep982 ep123 ep982 ep982 ep124 ep982 465642 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 988138419) qz272 0 1 ep982 ep123 ep982 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 988138419) qz273 0 1 ep982 ep124 ep982 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz949 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 183310515) qz268)

noncomputable def ep984 := @Enclosure.Real.IsNear.cos_image qz388 qz949 Bool.false 183310515 1048576 87 131072 Bool.false 465642 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz388 Bool.false 18331051557 104857600 25221 38077000 183310515 1048576 87 131072 (@Enclosure.Real.IsNear.mulLit_ff qz61 qz279 126105 1000 0 1 726817 524288 1 190385 18331051557 104857600 25221 38077000 qz386 qz559 rfl) rfl) (Enclosure.sfrac_false_div 183310515 1048576) (BSN.cos_reduce3 qz949 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 69534059654901084979200) qz271) 226375608064910080 72057594037927936 Bool.false 465642 1048576 27 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q3 183310515 1048576 226375608064910080 72057594037927936 27 69534059654901084979200 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 465642 1048576 69534059654901084979200 151115727451828646838272 988138419 2147483648 381142 380770 (ep983 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep985 := BSN.cos_dyadic_bound_f 988138419 2147483648 2 1 1048576 381142 ep982 ep143 ep982 ep982 ep144 ep982 939514 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 988138419) qz266 0 1 ep982 ep143 ep982 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 988138419) qz267 0 1 ep982 ep144 ep982 rfl rfl rfl rfl) rfl rfl

noncomputable def ep986 := @Enclosure.Real.IsNear.sin_image qz388 qz949 Bool.false 183310515 1048576 87 131072 Bool.true 939514 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz388 Bool.false 18331051557 104857600 25221 38077000 183310515 1048576 87 131072 (@Enclosure.Real.IsNear.mulLit_ff qz61 qz279 126105 1000 0 1 726817 524288 1 190385 18331051557 104857600 25221 38077000 qz386 qz559 rfl) rfl) (Enclosure.sfrac_false_div 183310515 1048576) (BSN.sin_reduce3 qz949 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 69534059654901084979200) qz271) 226375608064910080 72057594037927936 Bool.false 939514 1048576 27 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q3 183310515 1048576 226375608064910080 72057594037927936 27 69534059654901084979200 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 939514 1048576 69534059654901084979200 151115727451828646838272 988138419 2147483648 381142 380770 (ep985 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep987 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz278 (Real.cos qz388)) (@HMul.hMul Real Real Real qz0 qz278 (@Neg.neg Real Real.instNeg (Real.sin qz388))) Bool.false 122065023627 549755813888 35055370199269 104665260627066880 Bool.false 246287488259 549755813888 35100479259629 104665260627066880 (@Enclosure.Real.IsNear.mulLit_ff qz278 (Real.cos qz388) 524287 1048576 1 1048576 232821 524288 16694567 24954142720 122065023627 549755813888 35055370199269 104665260627066880 qz560 (@Enclosure.Real.IsNear.recentre' (Real.cos qz388) Bool.false 465642 1048576 16694567 24954142720 232821 524288 16694567 24954142720 (ep984 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz278 (@Neg.neg Real Real.instNeg (Real.sin qz388)) 524287 1048576 1 1048576 469757 524288 16694567 24954142720 246287488259 549755813888 35100479259629 104665260627066880 qz560 (@Enclosure.Real.IsNear.neg (Real.sin qz388) Bool.true 469757 524288 16694567 24954142720 (@Enclosure.Real.IsNear.recentre' (Real.sin qz388) Bool.true 939514 1048576 16694567 24954142720 469757 524288 16694567 24954142720 (ep986 rfl rfl) rfl)) rfl)

noncomputable def ep988 := @ep955 122065023627 549755813888 35055370199269 104665260627066880 Bool.false 246287488259 549755813888 35100479259629 104665260627066880 Bool.false 358537410916840856616960 1304351502465 549755813888 25035134372683 20933052125413376 Bool.false 48700186656978939936768 354340493919 549755813888 25024808727977 20933052125413376 (ep956 (BSN.head_sum_c_succ qz64 3 4 rfl rfl) (ep980 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep981 ep987) rfl rfl

noncomputable abbrev qz389 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 5 1)))

noncomputable def ep989 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz14 qz16 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz282 (Real.cos qz389)) (@HMul.hMul Real Real Real qz0 qz282 (@Neg.neg Real Real.instNeg (Real.sin qz389)))) Bool.true 78552105807 549755813888 31346759021119 104665260627066880 Bool.true 465942837255 1099511627776 62818904270543 209330521254133760 (BSN.cpow_neg_s_mk qz61 126105 1000 5 (@Eq.refl Real qz61) rfl)

noncomputable def ep990 := nat_lit 237873004611978689568010362143200401

noncomputable def ep991 := BSN.sin_dyadic_bound_f 698371149 2147483648 2 1 1048576 381142 ep990 ep123 ep990 ep990 ep124 ep990 335022 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 698371149) qz272 0 1 ep990 ep123 ep990 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 698371149) qz273 0 1 ep990 ep124 ep990 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz950 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 212816815) qz268)

noncomputable def ep992 := @Enclosure.Real.IsNear.cos_image qz389 qz950 Bool.false 212816815 1048576 87 131072 Bool.true 335022 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz389 Bool.false 665052549 3276800 25221 38077000 212816815 1048576 87 131072 (@Enclosure.Real.IsNear.mulLit_ff qz61 qz283 126105 1000 0 1 843808 524288 1 190385 665052549 3276800 25221 38077000 qz386 qz563 rfl) rfl) (Enclosure.sfrac_false_div 212816815 1048576) (BSN.cos_reduce1 qz950 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 49143500736646464143360) qz271) 226375608064910080 72057594037927936 Bool.false 335022 1048576 32 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q1 212816815 1048576 226375608064910080 72057594037927936 32 49143500736646464143360 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 335022 1048576 49143500736646464143360 151115727451828646838272 698371149 2147483648 381142 380770 (ep991 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep993 := BSN.cos_dyadic_bound_f 698371149 2147483648 2 1 1048576 381142 ep990 ep143 ep990 ep990 ep144 ep990 993615 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 698371149) qz266 0 1 ep990 ep143 ep990 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 698371149) qz267 0 1 ep990 ep144 ep990 rfl rfl rfl rfl) rfl rfl

noncomputable def ep994 := @Enclosure.Real.IsNear.sin_image qz389 qz950 Bool.false 212816815 1048576 87 131072 Bool.false 993615 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz389 Bool.false 665052549 3276800 25221 38077000 212816815 1048576 87 131072 (@Enclosure.Real.IsNear.mulLit_ff qz61 qz283 126105 1000 0 1 843808 524288 1 190385 665052549 3276800 25221 38077000 qz386 qz563 rfl) rfl) (Enclosure.sfrac_false_div 212816815 1048576) (BSN.sin_reduce1 qz950 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 49143500736646464143360) qz271) 226375608064910080 72057594037927936 Bool.false 993615 1048576 32 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q1 212816815 1048576 226375608064910080 72057594037927936 32 49143500736646464143360 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 993615 1048576 49143500736646464143360 151115727451828646838272 698371149 2147483648 381142 380770 (ep993 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep995 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz282 (Real.cos qz389)) (@HMul.hMul Real Real Real qz0 qz282 (@Neg.neg Real Real.instNeg (Real.sin qz389))) Bool.true 78552105807 549755813888 31346759021119 104665260627066880 Bool.true 465942837255 1099511627776 62818904270543 209330521254133760 (@Enclosure.Real.IsNear.mulLit_ft qz282 (Real.cos qz389) 468937 1048576 1 1048576 167511 524288 16694567 24954142720 78552105807 549755813888 31346759021119 104665260627066880 qz564 (@Enclosure.Real.IsNear.recentre' (Real.cos qz389) Bool.true 335022 1048576 16694567 24954142720 167511 524288 16694567 24954142720 (ep992 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz282 (@Neg.neg Real Real.instNeg (Real.sin qz389)) 468937 1048576 1 1048576 993615 1048576 16694567 24954142720 465942837255 1099511627776 62818904270543 209330521254133760 qz564 (@Enclosure.Real.IsNear.neg (Real.sin qz389) Bool.false 993615 1048576 16694567 24954142720 (@Enclosure.Real.IsNear.recentre' (Real.sin qz389) Bool.false 993615 1048576 16694567 24954142720 993615 1048576 16694567 24954142720 (ep994 rfl rfl) rfl)) rfl)

noncomputable def ep996 := @ep953 78552105807 549755813888 31346759021119 104665260627066880 Bool.true 465942837255 1099511627776 62818904270543 209330521254133760 Bool.false 673890344973138137186304 612899698329 274877906944 6020093495559 4025586947194880 Bool.false 133446709535425066696704 242738150583 1099511627776 24082076273101 16102347788779520 (ep954 (BSN.head_sum_c_succ qz64 4 5 rfl rfl) (ep988 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep989 ep995) rfl rfl

noncomputable abbrev qz390 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 6 1)))

noncomputable def ep997 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz14 qz820 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz284 (Real.cos qz390)) (@HMul.hMul Real Real Real qz0 qz284 (@Neg.neg Real Real.instNeg (Real.sin qz390)))) Bool.false 54434097561 137438953472 1434163881515 5233263031353344 Bool.false 27215122425 274877906944 2861064841819 10466526062706688 (BSN.cpow_neg_s_mk qz61 126105 1000 6 (@Eq.refl Real qz61) rfl)

noncomputable def ep998 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz285 126105 1000 0 1 4034681531866359 2251799813685248 100000000038077 19038500000000000000 101758702915201440339 450359962737049600 2522100000960340017 3807700000000000000000 qz386 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 100000000038077 19038500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz826) Bool.false 33845361775666394038272 18889465931478580854784 1000000000380770 190385000000000000000 4034681531866359 2251799813685248 100000000038077 19038500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 212580 524288 24973259072661432 36028797018963968 190385 1000000000000000 rfl rfl rfl rfl (ep151 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep999 := nat_lit 4230786746899766757701209955865600189031979957383255094680741764853663689793665

noncomputable def ep1000 := nat_lit 4318696476088847683770573856300229326928210292754193504960393325240644984961

noncomputable def ep1001 := nat_lit 11073639780919054802491349907690181076173492309815494648965340175899681952817281

noncomputable def ep1002 := BSN.sin_dyadic_bound_f 2847207279 2147483648 3 2 1048576 381142 ep999 ep95 ep1000 ep1001 ep97 ep1000 1017272 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2847207279) qz272 0 2 ep999 ep95 ep1000 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2847207279) qz273 0 2 ep1001 ep97 ep1000 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz951 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 118462721) qz280)

noncomputable def ep1003 := @Enclosure.Real.IsNear.cos_image qz390 qz951 Bool.false 118462721 524288 87 131072 Bool.false 1017272 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz390 Bool.false 101758702915201440339 450359962737049600 2522100000960340017 3807700000000000000000 118462721 524288 87 131072 (ep998 rfl) rfl) (Enclosure.sfrac_false_div 118462721 524288) (BSN.cos_reduce3 qz951 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 100177200330253629652992) qz281) 226375608064910080 72057594037927936 Bool.false 1017272 1048576 35 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q3 118462721 524288 226375608064910080 72057594037927936 35 100177200330253629652992 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1017272 1048576 100177200330253629652992 75557863725914323419136 2847207279 2147483648 381142 380770 (ep1002 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1004 := nat_lit 2352356502267021019915681341639244651385290292009699138602616710841031225434241

noncomputable def ep1005 := nat_lit 7048432113848885364379502877205133495502014455443589028797929345872612386332801

noncomputable def ep1006 := BSN.cos_dyadic_bound_f 2847207279 2147483648 3 2 1048576 381142 ep1004 ep88 ep1000 ep1005 ep91 ep1000 254300 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2847207279) qz266 0 2 ep1004 ep88 ep1000 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2847207279) qz267 0 2 ep1005 ep91 ep1000 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1007 := @Enclosure.Real.IsNear.sin_image qz390 qz951 Bool.false 118462721 524288 87 131072 Bool.true 254300 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz390 Bool.false 101758702915201440339 450359962737049600 2522100000960340017 3807700000000000000000 118462721 524288 87 131072 (ep998 rfl) rfl) (Enclosure.sfrac_false_div 118462721 524288) (BSN.sin_reduce3 qz951 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 100177200330253629652992) qz281) 226375608064910080 72057594037927936 Bool.false 254300 1048576 35 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q3 118462721 524288 226375608064910080 72057594037927936 35 100177200330253629652992 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 254300 1048576 100177200330253629652992 75557863725914323419136 2847207279 2147483648 381142 380770 (ep1006 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1008 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz284 (Real.cos qz390)) (@HMul.hMul Real Real Real qz0 qz284 (@Neg.neg Real Real.instNeg (Real.sin qz390))) Bool.false 54434097561 137438953472 1434163881515 5233263031353344 Bool.false 27215122425 274877906944 2861064841819 10466526062706688 (@Enclosure.Real.IsNear.mulLit_ff qz284 (Real.cos qz390) 428079 1048576 1 1048576 127159 131072 16694567 24954142720 54434097561 137438953472 1434163881515 5233263031353344 qz566 (@Enclosure.Real.IsNear.recentre' (Real.cos qz390) Bool.false 1017272 1048576 16694567 24954142720 127159 131072 16694567 24954142720 (ep1003 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz284 (@Neg.neg Real Real.instNeg (Real.sin qz390)) 428079 1048576 1 1048576 63575 262144 16694567 24954142720 27215122425 274877906944 2861064841819 10466526062706688 qz566 (@Enclosure.Real.IsNear.neg (Real.sin qz390) Bool.true 63575 262144 16694567 24954142720 (@Enclosure.Real.IsNear.recentre' (Real.sin qz390) Bool.true 254300 1048576 16694567 24954142720 63575 262144 16694567 24954142720 (ep1007 rfl rfl) rfl)) rfl)

noncomputable def ep1009 := @ep951 54434097561 137438953472 1434163881515 5233263031353344 Bool.false 27215122425 274877906944 2861064841819 10466526062706688 Bool.false 99199023925595442511872 721767893451 274877906944 92602854257417 52332630313533440 Bool.false 96646698325347403825152 351598640283 1099511627776 370288288386693 209330521254133760 (ep952 (BSN.head_sum_c_succ qz64 5 6 rfl rfl) (ep996 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep997 ep1008) rfl rfl

noncomputable abbrev qz391 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 7 1)))

noncomputable def ep1010 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz14 qz819 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz286 (Real.cos qz391)) (@HMul.hMul Real Real Real qz0 qz286 (@Neg.neg Real Real.instNeg (Real.sin qz391)))) Bool.false 391149391825 1099511627776 53119826449021 209330521254133760 Bool.true 140377918675 1099511627776 52999361863351 209330521254133760 (BSN.cpow_neg_s_mk qz61 126105 1000 7 (@Eq.refl Real qz61) rfl)

noncomputable def ep1011 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz287 126105 1000 0 1 4381796493761783 2251799813685248 100000000038077 19038500000000000000 110513289369165929043 450359962737049600 2522100000960340017 3807700000000000000000 qz386 (BSN.isNear_log_sfrac 7 1 4381796493761783 2251799813685248 100000000038077 19038500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz829) Bool.false 36757173121942042968064 18889465931478580854784 1000000000380770 190385000000000000000 4381796493761783 2251799813685248 100000000038077 19038500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 293399 524288 24973259072661432 36028797018963968 190385 1000000000000000 rfl rfl rfl rfl (ep165 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1012 := nat_lit 299794477728201448504116590808946321

noncomputable def ep1013 := BSN.cos_dyadic_bound_f 739956019 2147483648 2 1 1048576 381142 ep1012 ep143 ep1012 ep1012 ep144 ep1012 986941 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 739956019) qz266 0 1 ep1012 ep143 ep1012 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 739956019) qz267 0 1 ep1012 ep144 ep1012 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz952 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 128654401) qz280)

noncomputable def ep1014 := @Enclosure.Real.IsNear.cos_image qz391 qz952 Bool.false 128654401 524288 87 131072 Bool.false 986941 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz391 Bool.false 110513289369165929043 450359962737049600 2522100000960340017 3807700000000000000000 128654401 524288 87 131072 (ep1011 rfl) rfl) (Enclosure.sfrac_false_div 128654401 524288) (BSN.cos_reduce0 qz952 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26034887924429914898432) qz281) 226375608064910080 72057594037927936 Bool.false 986941 1048576 39 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q0 128654401 524288 226375608064910080 72057594037927936 39 26034887924429914898432 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 986941 1048576 26034887924429914898432 75557863725914323419136 739956019 2147483648 381142 380770 (ep1013 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1015 := BSN.sin_dyadic_bound_f 739956019 2147483648 2 1 1048576 381142 ep1012 ep123 ep1012 ep1012 ep124 ep1012 354199 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 739956019) qz272 0 1 ep1012 ep123 ep1012 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 739956019) qz273 0 1 ep1012 ep124 ep1012 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1016 := @Enclosure.Real.IsNear.sin_image qz391 qz952 Bool.false 128654401 524288 87 131072 Bool.false 354199 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz391 Bool.false 110513289369165929043 450359962737049600 2522100000960340017 3807700000000000000000 128654401 524288 87 131072 (ep1011 rfl) rfl) (Enclosure.sfrac_false_div 128654401 524288) (BSN.sin_reduce0 qz952 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26034887924429914898432) qz281) 226375608064910080 72057594037927936 Bool.false 354199 1048576 39 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q0 128654401 524288 226375608064910080 72057594037927936 39 26034887924429914898432 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 354199 1048576 26034887924429914898432 75557863725914323419136 739956019 2147483648 381142 380770 (ep1015 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1017 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz286 (Real.cos qz391)) (@HMul.hMul Real Real Real qz0 qz286 (@Neg.neg Real Real.instNeg (Real.sin qz391))) Bool.false 391149391825 1099511627776 53119826449021 209330521254133760 Bool.true 140377918675 1099511627776 52999361863351 209330521254133760 (@Enclosure.Real.IsNear.mulLit_ff qz286 (Real.cos qz391) 396325 1048576 1 1048576 986941 1048576 16694567 24954142720 391149391825 1099511627776 53119826449021 209330521254133760 qz568 (@Enclosure.Real.IsNear.recentre' (Real.cos qz391) Bool.false 986941 1048576 16694567 24954142720 986941 1048576 16694567 24954142720 (ep1014 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz286 (@Neg.neg Real Real.instNeg (Real.sin qz391)) 396325 1048576 1 1048576 354199 1048576 16694567 24954142720 140377918675 1099511627776 52999361863351 209330521254133760 qz568 (@Enclosure.Real.IsNear.neg (Real.sin qz391) Bool.false 354199 1048576 16694567 24954142720 (@Enclosure.Real.IsNear.recentre' (Real.sin qz391) Bool.false 354199 1048576 16694567 24954142720 354199 1048576 16694567 24954142720 (ep1016 rfl rfl) rfl)) rfl)

noncomputable def ep1018 := @ep949 391149391825 1099511627776 53119826449021 209330521254133760 Bool.true 140377918675 1099511627776 52999361863351 209330521254133760 Bool.false 901110517532038084427776 3278220965629 1099511627776 423531243478689 209330521254133760 Bool.false 232239639435233416183808 26402590201 137438953472 105821912562511 52332630313533440 (ep950 (BSN.head_sum_c_succ qz64 6 7 rfl rfl) (ep1009 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1010 ep1017) rfl rfl

noncomputable abbrev qz392 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 8 1)))

noncomputable def ep1019 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz14 qz818 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz288 (Real.cos qz392)) (@HMul.hMul Real Real Real qz0 qz288 (@Neg.neg Real Real.instNeg (Real.sin qz392)))) Bool.true 9219609763 274877906944 12383021554117 52332630313533440 Bool.false 193490948021 549755813888 24855940049459 104665260627066880 (BSN.cpow_neg_s_mk qz61 126105 1000 8 (@Eq.refl Real qz61) rfl)

noncomputable def ep1020 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz289 126105 1000 0 1 9364972152248037 4503599627370496 200000000114231 38077000000000000000 236193962651847741177 900719925474099200 5044200002881020051 7615400000000000000000 qz386 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 200000000114231 38077000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz832) Bool.false 39279540158062550581248 18889465931478580854784 1000000000571155 190385000000000000000 9364972152248037 4503599627370496 200000000114231 38077000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 524288 24973259072661432 36028797018963968 190385 1000000000000000 rfl rfl rfl rfl (ep180 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1021 := nat_lit 3614636604562466648095731567201159377722001558056326646949358220426347440800000

noncomputable def ep1022 := nat_lit 10177071369042294369000015993864368797211624692580371973574718491408100000000

noncomputable def ep1023 := nat_lit 10823555670949315355549194669615749395571581424783819196900925224296226122400000

noncomputable def ep1024 := BSN.cos_dyadic_bound_f 3169223390 2147483648 3 2 1048576 381142 ep1021 ep88 ep1022 ep1023 ep91 ep1022 99476 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3169223390) qz266 0 2 ep1021 ep88 ep1022 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3169223390) qz267 0 2 ep1023 ep91 ep1022 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz953 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 274965961) qz268)

noncomputable def ep1025 := @Enclosure.Real.IsNear.cos_image qz392 qz953 Bool.false 274965961 1048576 87 131072 Bool.true 99476 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz392 Bool.false 236193962651847741177 900719925474099200 5044200002881020051 7615400000000000000000 274965961 1048576 87 131072 (ep1020 rfl) rfl) (Enclosure.sfrac_false_div 274965961 1048576) (BSN.cos_reduce2 qz953 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 223014269996439502323712) qz271) 226375608064910080 72057594037927936 Bool.false 99476 1048576 41 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q2 274965961 1048576 226375608064910080 72057594037927936 41 223014269996439502323712 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 99476 1048576 223014269996439502323712 151115727451828646838272 3169223390 2147483648 381142 380770 (ep1024 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1026 := nat_lit 6498204231117206131077116808166995384861833504747323666929985021974298913440000

noncomputable def ep1027 := nat_lit 17002629156423757104795020185971112268014078453407384239716554084756122135200000

noncomputable def ep1028 := BSN.sin_dyadic_bound_f 3169223390 2147483648 3 2 1048576 381142 ep1026 ep95 ep1022 ep1027 ep97 ep1022 1043846 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3169223390) qz272 0 2 ep1026 ep95 ep1022 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3169223390) qz273 0 2 ep1027 ep97 ep1022 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1029 := @Enclosure.Real.IsNear.sin_image qz392 qz953 Bool.false 274965961 1048576 87 131072 Bool.true 1043846 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz392 Bool.false 236193962651847741177 900719925474099200 5044200002881020051 7615400000000000000000 274965961 1048576 87 131072 (ep1020 rfl) rfl) (Enclosure.sfrac_false_div 274965961 1048576) (BSN.sin_reduce2 qz953 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 223014269996439502323712) qz271) 226375608064910080 72057594037927936 Bool.false 1043846 1048576 41 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q2 274965961 1048576 226375608064910080 72057594037927936 41 223014269996439502323712 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1043846 1048576 223014269996439502323712 151115727451828646838272 3169223390 2147483648 381142 380770 (ep1028 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1030 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz288 (Real.cos qz392)) (@HMul.hMul Real Real Real qz0 qz288 (@Neg.neg Real Real.instNeg (Real.sin qz392))) Bool.true 9219609763 274877906944 12383021554117 52332630313533440 Bool.false 193490948021 549755813888 24855940049459 104665260627066880 (@Enclosure.Real.IsNear.mulLit_ft qz288 (Real.cos qz392) 370727 1048576 1 1048576 24869 262144 16694567 24954142720 9219609763 274877906944 12383021554117 52332630313533440 qz570 (@Enclosure.Real.IsNear.recentre' (Real.cos qz392) Bool.true 99476 1048576 16694567 24954142720 24869 262144 16694567 24954142720 (ep1025 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz288 (@Neg.neg Real Real.instNeg (Real.sin qz392)) 370727 1048576 1 1048576 521923 524288 16694567 24954142720 193490948021 549755813888 24855940049459 104665260627066880 qz570 (@Enclosure.Real.IsNear.neg (Real.sin qz392) Bool.true 521923 524288 16694567 24954142720 (@Enclosure.Real.IsNear.recentre' (Real.sin qz392) Bool.true 1043846 1048576 16694567 24954142720 521923 524288 16694567 24954142720 (ep1029 rfl rfl) rfl)) rfl)

noncomputable def ep1031 := @ep947 9219609763 274877906944 12383021554117 52332630313533440 Bool.false 193490948021 549755813888 24855940049459 104665260627066880 Bool.false 890973449394062452850688 3241342526577 1099511627776 473063329695157 209330521254133760 Bool.false 41108170867013477990400 299101308825 549755813888 236499765174481 104665260627066880 (ep948 (BSN.head_sum_c_succ qz64 7 8 rfl rfl) (ep1018 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1019 ep1030) rfl rfl

theorem EMRow41.d17 : Enclosure.Complex.IsNear (BSN.headSumC qz64 9) Bool.false 3241342526577 1099511627776 473063329695157 209330521254133760 Bool.false 299101308825 549755813888 236499765174481 104665260627066880 := ep946 (BSN.head_sum_c_succ qz64 8 9 rfl rfl) (ep1031 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz954 := (@Nat.cast Complex Complex.instNatCast 16)

noncomputable def ep1032 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 17) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 16) (@HPow.hPow Complex Complex Complex qz14 qz954 qz65)) Bool.false 3722361836107 1099511627776 795137534619713 209330521254133760 Bool.false 12435306791 274877906944 12420902565787 3270789394595840

noncomputable def ep1033 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 16) (@HPow.hPow Complex Complex Complex qz14 qz954 qz65) Bool.false 1944387334469 549755813888 47503471168589 13083157578383360 Bool.true 42259257301 274877906944 47488608573179 13083157578383360 Bool.true

noncomputable def ep1034 := nat_lit 2046390060794633850454016

noncomputable abbrev qz955 := (@Nat.cast Complex Complex.instNatCast 15)

noncomputable def ep1035 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 16) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 15) (@HPow.hPow Complex Complex Complex qz14 qz955 qz65)) Bool.false 1944387334469 549755813888 47503471168589 13083157578383360 Bool.true 42259257301 274877906944 47488608573179 13083157578383360

noncomputable def ep1036 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 15) (@HPow.hPow Complex Complex Complex qz14 qz955 qz65) Bool.false 4057317709963 1099511627776 723777655605587 209330521254133760 Bool.false 59410165481 1099511627776 723497729493927 209330521254133760 Bool.true

noncomputable def ep1037 := nat_lit 4275752966298095885221888

noncomputable abbrev qz956 := (@Nat.cast Complex Complex.instNatCast 14)

noncomputable def ep1038 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 15) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 14) (@HPow.hPow Complex Complex Complex qz14 qz956 qz65)) Bool.false 4057317709963 1099511627776 723777655605587 209330521254133760 Bool.false 59410165481 1099511627776 723497729493927 209330521254133760

noncomputable def ep1039 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 14) (@HPow.hPow Complex Complex Complex qz14 qz956 qz65) Bool.false 3769960461165 1099511627776 686154019617193 209330521254133760 Bool.true 511991287 274877906944 42876722476093 13083157578383360 Bool.false

noncomputable def ep1040 := nat_lit 2230533999842905391366144

noncomputable abbrev qz957 := (@Nat.cast Complex Complex.instNatCast 13)

noncomputable def ep1041 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 14) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 13) (@HPow.hPow Complex Complex Complex qz14 qz957 qz65)) Bool.false 3769960461165 1099511627776 686154019617193 209330521254133760 Bool.true 511991287 274877906944 42876722476093 13083157578383360

noncomputable def ep1042 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 13) (@HPow.hPow Complex Complex Complex qz14 qz957 qz65) Bool.false 4072284347523 1099511627776 647170028153559 209330521254133760 Bool.false 18942470491 549755813888 323607670177357 104665260627066880 Bool.true

noncomputable def ep1043 := nat_lit 2072557681653344391659520

noncomputable def ep1044 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 13) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 12) (@HPow.hPow Complex Complex Complex qz14 qz838 qz65)) Bool.false 4072284347523 1099511627776 647170028153559 209330521254133760 Bool.false 18942470491 549755813888 323607670177357 104665260627066880

noncomputable def ep1045 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 12) (@HPow.hPow Complex Complex Complex qz14 qz838 qz65) Bool.false 3851201723451 1099511627776 606603679184671 209330521254133760 Bool.true 47463800227 274877906944 75830600507267 26166315156766720 Bool.false

noncomputable def ep1046 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 12) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 11) (@HPow.hPow Complex Complex Complex qz14 qz839 qz65)) Bool.false 3851201723451 1099511627776 606603679184671 209330521254133760 Bool.true 47463800227 274877906944 75830600507267 26166315156766720

noncomputable def ep1047 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 11) (@HPow.hPow Complex Complex Complex qz14 qz839 qz65) Bool.false 226169393677 68719476736 70529838628711 26166315156766720 Bool.false 5808703417 137438953472 141069381371257 52332630313533440 Bool.false

noncomputable def ep1048 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 11) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 10) (@HPow.hPow Complex Complex Complex qz14 qz840 qz65)) Bool.false 226169393677 68719476736 70529838628711 26166315156766720 Bool.false 5808703417 137438953472 141069381371257 52332630313533440

noncomputable def ep1049 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 10) (@HPow.hPow Complex Complex Complex qz14 qz840 qz65) Bool.false 3539462185777 1099511627776 39992861245721 16102347788779520 Bool.false 48126754775 137438953472 9996098753789 4025586947194880 Bool.false

noncomputable def ep1050 := nat_lit 3978814051118547711557632

noncomputable def ep1051 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 10) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 9) (@HPow.hPow Complex Complex Complex qz14 qz841 qz65)) Bool.false 3539462185777 1099511627776 39992861245721 16102347788779520 Bool.false 48126754775 137438953472 9996098753789 4025586947194880

noncomputable def ep1052 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 9) (@HPow.hPow Complex Complex Complex qz14 qz841 qz65) Bool.false 3241342526577 1099511627776 473063329695157 209330521254133760 Bool.false 299101308825 549755813888 236499765174481 104665260627066880 Bool.false

noncomputable abbrev qz393 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 9 1)))

noncomputable def ep1053 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz14 qz841 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz290 (Real.cos qz393)) (@HMul.hMul Real Real Real qz0 qz290 (@Neg.neg Real Real.instNeg (Real.sin qz393)))) Bool.false 4658119675 17179869184 2927741656201 13083157578383360 Bool.true 106594289725 549755813888 23398802424033 104665260627066880 (BSN.cpow_neg_s_mk qz61 126105 1000 9 (@Eq.refl Real qz61) rfl)

noncomputable def ep1054 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz291 126105 1000 0 1 9895417793173221 4503599627370496 200000000114231 38077000000000000000 249572332161621806841 900719925474099200 5044200002881020051 7615400000000000000000 qz386 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 200000000114231 38077000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz842) Bool.false 41504390431577613533184 18889465931478580854784 1000000000571155 190385000000000000000 9895417793173221 4503599627370496 200000000114231 38077000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 61752 524288 24973259072661432 36028797018963968 190385 1000000000000000 rfl rfl rfl rfl (ep207 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1055 := nat_lit 3158734921273968130809377457518750625

noncomputable def ep1056 := BSN.cos_dyadic_bound_f 1333147785 2147483648 2 1 1048576 381142 ep1055 ep143 ep1055 ep1055 ep144 ep1055 852928 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1333147785) qz266 0 1 ep1055 ep143 ep1055 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1333147785) qz267 0 1 ep1055 ep144 ep1055 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz958 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 290540433) qz268)

noncomputable def ep1057 := @Enclosure.Real.IsNear.cos_image qz393 qz958 Bool.false 290540433 1048576 87 131072 Bool.false 852928 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz393 Bool.false 249572332161621806841 900719925474099200 5044200002881020051 7615400000000000000000 290540433 1048576 87 131072 (ep1054 rfl) rfl) (Enclosure.sfrac_false_div 290540433 1048576) (BSN.cos_reduce0 qz958 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 93811935435879136362496) qz271) 226375608064910080 72057594037927936 Bool.false 852928 1048576 44 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q0 290540433 1048576 226375608064910080 72057594037927936 44 93811935435879136362496 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 852928 1048576 93811935435879136362496 151115727451828646838272 1333147785 2147483648 381142 380770 (ep1056 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1058 := BSN.sin_dyadic_bound_f 1333147785 2147483648 2 1 1048576 381142 ep1055 ep123 ep1055 ep1055 ep124 ep1055 609938 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1333147785) qz272 0 1 ep1055 ep123 ep1055 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1333147785) qz273 0 1 ep1055 ep124 ep1055 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1059 := @Enclosure.Real.IsNear.sin_image qz393 qz958 Bool.false 290540433 1048576 87 131072 Bool.false 609938 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz393 Bool.false 249572332161621806841 900719925474099200 5044200002881020051 7615400000000000000000 290540433 1048576 87 131072 (ep1054 rfl) rfl) (Enclosure.sfrac_false_div 290540433 1048576) (BSN.sin_reduce0 qz958 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 93811935435879136362496) qz271) 226375608064910080 72057594037927936 Bool.false 609938 1048576 44 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q0 290540433 1048576 226375608064910080 72057594037927936 44 93811935435879136362496 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 609938 1048576 93811935435879136362496 151115727451828646838272 1333147785 2147483648 381142 380770 (ep1058 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1060 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz290 (Real.cos qz393)) (@HMul.hMul Real Real Real qz0 qz290 (@Neg.neg Real Real.instNeg (Real.sin qz393))) Bool.false 4658119675 17179869184 2927741656201 13083157578383360 Bool.true 106594289725 549755813888 23398802424033 104665260627066880 (@Enclosure.Real.IsNear.mulLit_ff qz290 (Real.cos qz393) 349525 1048576 1 1048576 13327 16384 16694567 24954142720 4658119675 17179869184 2927741656201 13083157578383360 qz572 (@Enclosure.Real.IsNear.recentre' (Real.cos qz393) Bool.false 852928 1048576 16694567 24954142720 13327 16384 16694567 24954142720 (ep1057 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz290 (@Neg.neg Real Real.instNeg (Real.sin qz393)) 349525 1048576 1 1048576 304969 524288 16694567 24954142720 106594289725 549755813888 23398802424033 104665260627066880 qz572 (@Enclosure.Real.IsNear.neg (Real.sin qz393) Bool.false 304969 524288 16694567 24954142720 (@Enclosure.Real.IsNear.recentre' (Real.sin qz393) Bool.false 609938 1048576 16694567 24954142720 304969 524288 16694567 24954142720 (ep1059 rfl rfl) rfl)) rfl)

noncomputable def ep1061 := @ep1052 4658119675 17179869184 2927741656201 13083157578383360 Bool.true 106594289725 549755813888 23398802424033 104665260627066880 Bool.false 60807497333363565395968 3539462185777 1099511627776 39992861245721 16102347788779520 Bool.false 105831852964473261260800 48126754775 137438953472 9996098753789 4025586947194880 EMRow41.d17 (ep1053 ep1060) rfl rfl

noncomputable abbrev qz394 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 10 1)))

noncomputable def ep1062 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz14 qz840 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz292 (Real.cos qz394)) (@HMul.hMul Real Real Real qz0 qz292 (@Neg.neg Real Real.instNeg (Real.sin qz394)))) Bool.false 79248113055 1099511627776 8866302567063 41866104250826752 Bool.true 21159025679 68719476736 69500609825 327078939459584 (BSN.cpow_neg_s_mk qz61 126105 1000 10 (@Eq.refl Real qz61) rfl)

noncomputable def ep1063 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz294 126105 1000 0 1 10369917190100709 4503599627370496 200000000114231 38077000000000000000 261539681451529981689 900719925474099200 5044200002881020051 7615400000000000000000 qz386 (BSN.isNear_log_sfrac 10 1 10369917190100709 4503599627370496 200000000114231 38077000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz845) Bool.false 43494585150108164161536 18889465931478580854784 1000000000571155 190385000000000000000 10369917190100709 4503599627370496 200000000114231 38077000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 116991 524288 24973259072661432 36028797018963968 190385 1000000000000000 rfl rfl rfl rfl (ep221 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1064 := nat_lit 2460964775248608499201890163838960411617272709838787582037417208063962983078721

noncomputable def ep1065 := nat_lit 4725891171912053091240043381005909581807815853117331505629896277516713106241

noncomputable def ep1066 := nat_lit 7373442543402001391423190404754869415688202497810128083100991831636855523023681

noncomputable def ep1067 := BSN.cos_dyadic_bound_f 2879456119 2147483648 3 2 1048576 381142 ep1064 ep88 ep1065 ep1066 ep91 ep1065 238995 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2879456119) qz266 0 2 ep1064 ep88 ep1065 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2879456119) qz267 0 2 ep1066 ep91 ep1065 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz959 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 304472261) qz268)

noncomputable def ep1068 := @Enclosure.Real.IsNear.cos_image qz394 qz959 Bool.false 304472261 1048576 87 131072 Bool.false 238995 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz394 Bool.false 261539681451529981689 900719925474099200 5044200002881020051 7615400000000000000000 304472261 1048576 87 131072 (ep1063 rfl) rfl) (Enclosure.sfrac_false_div 304472261 1048576) (BSN.cos_reduce0 qz959 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 202623711078184881487872) qz271) 226375608064910080 72057594037927936 Bool.false 238995 1048576 46 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q0 304472261 1048576 226375608064910080 72057594037927936 46 202623711078184881487872 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 238995 1048576 202623711078184881487872 151115727451828646838272 2879456119 2147483648 381142 380770 (ep1067 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1069 := nat_lit 4425955882509965656090410260205324013245644625027323782462847057493119999056705

noncomputable def ep1070 := nat_lit 11584137773247766727612876325539934276320428030356991369726912937556477700119361

noncomputable def ep1071 := BSN.sin_dyadic_bound_f 2879456119 2147483648 3 2 1048576 381142 ep1069 ep95 ep1065 ep1070 ep97 ep1065 1020976 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2879456119) qz272 0 2 ep1069 ep95 ep1065 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2879456119) qz273 0 2 ep1070 ep97 ep1065 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1072 := @Enclosure.Real.IsNear.sin_image qz394 qz959 Bool.false 304472261 1048576 87 131072 Bool.false 1020976 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz394 Bool.false 261539681451529981689 900719925474099200 5044200002881020051 7615400000000000000000 304472261 1048576 87 131072 (ep1063 rfl) rfl) (Enclosure.sfrac_false_div 304472261 1048576) (BSN.sin_reduce0 qz959 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 202623711078184881487872) qz271) 226375608064910080 72057594037927936 Bool.false 1020976 1048576 46 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q0 304472261 1048576 226375608064910080 72057594037927936 46 202623711078184881487872 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1020976 1048576 202623711078184881487872 151115727451828646838272 2879456119 2147483648 381142 380770 (ep1071 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1073 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz292 (Real.cos qz394)) (@HMul.hMul Real Real Real qz0 qz292 (@Neg.neg Real Real.instNeg (Real.sin qz394))) Bool.false 79248113055 1099511627776 8866302567063 41866104250826752 Bool.true 21159025679 68719476736 69500609825 327078939459584 (@Enclosure.Real.IsNear.mulLit_ff qz292 (Real.cos qz394) 331589 1048576 1 1048576 238995 1048576 16694567 24954142720 79248113055 1099511627776 8866302567063 41866104250826752 qz573 (@Enclosure.Real.IsNear.recentre' (Real.cos qz394) Bool.false 238995 1048576 16694567 24954142720 238995 1048576 16694567 24954142720 (ep1068 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz292 (@Neg.neg Real Real.instNeg (Real.sin qz394)) 331589 1048576 1 1048576 63811 65536 16694567 24954142720 21159025679 68719476736 69500609825 327078939459584 qz573 (@Enclosure.Real.IsNear.neg (Real.sin qz394) Bool.false 63811 65536 16694567 24954142720 (@Enclosure.Real.IsNear.recentre' (Real.sin qz394) Bool.false 1020976 1048576 16694567 24954142720 63811 65536 16694567 24954142720 (ep1072 rfl rfl) rfl)) rfl)

noncomputable def ep1074 := @ep1049 79248113055 1099511627776 8866302567063 41866104250826752 Bool.true 21159025679 68719476736 69500609825 327078939459584 Bool.false ep1050 226169393677 68719476736 70529838628711 26166315156766720 Bool.false 399171059330855206912 5808703417 137438953472 141069381371257 52332630313533440 (ep1051 (BSN.head_sum_c_succ qz64 9 10 rfl rfl) (ep1061 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1062 ep1073) rfl rfl

noncomputable abbrev qz395 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 11 1)))

noncomputable def ep1075 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz14 qz839 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz295 (Real.cos qz395)) (@HMul.hMul Real Real Real qz0 qz295 (@Neg.neg Real Real.instNeg (Real.sin qz395)))) Bool.false 232491424619 1099511627776 1460861039827 7218293836349440 Bool.true 59081207061 274877906944 365235160113 1804573459087360 (BSN.cpow_neg_s_mk qz61 126105 1000 11 (@Eq.refl Real qz61) rfl)

noncomputable def ep1076 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz297 126105 1000 0 1 10799156221662949 4503599627370496 200000000114231 38077000000000000000 272365519066561236729 900719925474099200 5044200002881020051 7615400000000000000000 qz386 (BSN.isNear_log_sfrac 11 1 10799156221662949 4503599627370496 200000000114231 38077000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz848) Bool.false 45294944137145793642496 18889465931478580854784 1000000000571155 190385000000000000000 10799156221662949 4503599627370496 200000000114231 38077000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 166961 524288 24973259072661432 36028797018963968 190385 1000000000000000 rfl rfl rfl rfl (ep236 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1077 := nat_lit 301441359521495382177585668173647087963919050073089392806094038193410560368896

noncomputable def ep1078 := nat_lit 71144800674469709112912754953768940762633861065748116044705288175919964416

noncomputable def ep1079 := nat_lit 904181788963137207114531179011033726010231882497136682186192704003879841177856

noncomputable def ep1080 := BSN.cos_dyadic_bound_f 1704189542 2147483648 3 2 1048576 381142 ep1077 ep88 ep1078 ep1079 ep91 ep1078 735367 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1704189542) qz266 0 2 ep1077 ep88 ep1078 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1704189542) qz267 0 2 ep1079 ep91 ep1078 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz960 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 317075195) qz268)

noncomputable def ep1081 := @Enclosure.Real.IsNear.cos_image qz395 qz960 Bool.false 317075195 1048576 87 131072 Bool.false 735367 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz395 Bool.false 272365519066561236729 900719925474099200 5044200002881020051 7615400000000000000000 317075195 1048576 87 131072 (ep1076 rfl) rfl) (Enclosure.sfrac_false_div 317075195 1048576) (BSN.cos_reduce0 qz960 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 119921677977614213447680) qz271) 226375608064910080 72057594037927936 Bool.false 735367 1048576 48 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q0 317075195 1048576 226375608064910080 72057594037927936 48 119921677977614213447680 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 735367 1048576 119921677977614213447680 151115727451828646838272 1704189542 2147483648 381142 380770 (ep1080 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1082 := nat_lit 8434737735962494590650503439555815696

noncomputable def ep1083 := BSN.sin_dyadic_bound_f 1704189542 2147483648 2 1 1048576 381142 ep1082 ep123 ep1082 ep1082 ep124 ep1082 747492 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1704189542) qz272 0 1 ep1082 ep123 ep1082 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1704189542) qz273 0 1 ep1082 ep124 ep1082 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1084 := @Enclosure.Real.IsNear.sin_image qz395 qz960 Bool.false 317075195 1048576 87 131072 Bool.false 747492 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz395 Bool.false 272365519066561236729 900719925474099200 5044200002881020051 7615400000000000000000 317075195 1048576 87 131072 (ep1076 rfl) rfl) (Enclosure.sfrac_false_div 317075195 1048576) (BSN.sin_reduce0 qz960 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 119921677977614213447680) qz271) 226375608064910080 72057594037927936 Bool.false 747492 1048576 48 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q0 317075195 1048576 226375608064910080 72057594037927936 48 119921677977614213447680 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 747492 1048576 119921677977614213447680 151115727451828646838272 1704189542 2147483648 381142 380770 (ep1083 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1085 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz295 (Real.cos qz395)) (@HMul.hMul Real Real Real qz0 qz295 (@Neg.neg Real Real.instNeg (Real.sin qz395))) Bool.false 232491424619 1099511627776 1460861039827 7218293836349440 Bool.true 59081207061 274877906944 365235160113 1804573459087360 (@Enclosure.Real.IsNear.mulLit_ff qz295 (Real.cos qz395) 316157 1048576 1 1048576 735367 1048576 16694567 24954142720 232491424619 1099511627776 1460861039827 7218293836349440 qz574 (@Enclosure.Real.IsNear.recentre' (Real.cos qz395) Bool.false 735367 1048576 16694567 24954142720 735367 1048576 16694567 24954142720 (ep1081 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz295 (@Neg.neg Real Real.instNeg (Real.sin qz395)) 316157 1048576 1 1048576 186873 262144 16694567 24954142720 59081207061 274877906944 365235160113 1804573459087360 qz574 (@Enclosure.Real.IsNear.neg (Real.sin qz395) Bool.false 186873 262144 16694567 24954142720 (@Enclosure.Real.IsNear.recentre' (Real.sin qz395) Bool.false 747492 1048576 16694567 24954142720 186873 262144 16694567 24954142720 (ep1084 rfl rfl) rfl)) rfl)

noncomputable def ep1086 := @ep1047 232491424619 1099511627776 1460861039827 7218293836349440 Bool.true 59081207061 274877906944 365235160113 1804573459087360 Bool.false 264652567240334100135936 3851201723451 1099511627776 606603679184671 209330521254133760 Bool.true 6523375031002956038144 47463800227 274877906944 75830600507267 26166315156766720 (ep1048 (BSN.head_sum_c_succ qz64 10 11 rfl rfl) (ep1074 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1075 ep1085) rfl rfl

noncomputable abbrev qz396 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 12 1)))

noncomputable def ep1087 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz14 qz838 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz298 (Real.cos qz396)) (@HMul.hMul Real Real Real qz0 qz298 (@Neg.neg Real Real.instNeg (Real.sin qz396)))) Bool.false 27635328009 137438953472 5070793621111 26166315156766720 Bool.false 113870070945 549755813888 20285268148289 104665260627066880 (BSN.cpow_neg_s_mk qz61 126105 1000 12 (@Eq.refl Real qz61) rfl)

noncomputable def ep1088 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz300 126105 1000 0 1 11191020447815397 4503599627370496 200000000114231 38077000000000000000 282248726714352127737 900719925474099200 5044200002881020051 7615400000000000000000 qz386 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 200000000114231 38077000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz851) Bool.false 46938541828353910898688 18889465931478580854784 1000000000571155 190385000000000000000 11191020447815397 4503599627370496 200000000114231 38077000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 212580 524288 24973259072661432 36028797018963968 190385 1000000000000000 rfl rfl rfl rfl (ep247 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1089 := nat_lit 7498212064756477041900723427847704576

noncomputable def ep1090 := BSN.sin_dyadic_bound_f 1654776824 2147483648 2 1 1048576 381142 ep1089 ep123 ep1089 ep1089 ep124 ep1089 730376 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1654776824) qz272 0 1 ep1089 ep123 ep1089 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1654776824) qz273 0 1 ep1089 ep124 ep1089 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz961 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 328580763) qz268)

noncomputable def ep1091 := @Enclosure.Real.IsNear.cos_image qz396 qz961 Bool.false 328580763 1048576 87 131072 Bool.false 730376 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz396 Bool.false 282248726714352127737 900719925474099200 5044200002881020051 7615400000000000000000 328580763 1048576 87 131072 (ep1088 rfl) rfl) (Enclosure.sfrac_false_div 328580763 1048576) (BSN.cos_reduce3 qz961 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 116444567001265042620416) qz271) 226375608064910080 72057594037927936 Bool.false 730376 1048576 49 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q3 328580763 1048576 226375608064910080 72057594037927936 49 116444567001265042620416 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 730376 1048576 116444567001265042620416 151115727451828646838272 1654776824 2147483648 381142 380770 (ep1090 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1092 := nat_lit 267964704836567527115272825734971461312892707467582773573897637742083787718656

noncomputable def ep1093 := nat_lit 56223184168059590660010333308953052881668929534062998303275206952171339776

noncomputable def ep1094 := nat_lit 803781668141366462164498456538296477832914784543680194725086362812347020476416

noncomputable def ep1095 := BSN.cos_dyadic_bound_f 1654776824 2147483648 3 2 1048576 381142 ep1092 ep88 ep1093 ep1094 ep91 ep1093 752370 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1654776824) qz266 0 2 ep1092 ep88 ep1093 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1654776824) qz267 0 2 ep1094 ep91 ep1093 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1096 := @Enclosure.Real.IsNear.sin_image qz396 qz961 Bool.false 328580763 1048576 87 131072 Bool.true 752370 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz396 Bool.false 282248726714352127737 900719925474099200 5044200002881020051 7615400000000000000000 328580763 1048576 87 131072 (ep1088 rfl) rfl) (Enclosure.sfrac_false_div 328580763 1048576) (BSN.sin_reduce3 qz961 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 116444567001265042620416) qz271) 226375608064910080 72057594037927936 Bool.false 752370 1048576 49 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q3 328580763 1048576 226375608064910080 72057594037927936 49 116444567001265042620416 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 752370 1048576 116444567001265042620416 151115727451828646838272 1654776824 2147483648 381142 380770 (ep1095 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1097 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz298 (Real.cos qz396)) (@HMul.hMul Real Real Real qz0 qz298 (@Neg.neg Real Real.instNeg (Real.sin qz396))) Bool.false 27635328009 137438953472 5070793621111 26166315156766720 Bool.false 113870070945 549755813888 20285268148289 104665260627066880 (@Enclosure.Real.IsNear.mulLit_ff qz298 (Real.cos qz396) 302697 1048576 1 1048576 91297 131072 16694567 24954142720 27635328009 137438953472 5070793621111 26166315156766720 qz575 (@Enclosure.Real.IsNear.recentre' (Real.cos qz396) Bool.false 730376 1048576 16694567 24954142720 91297 131072 16694567 24954142720 (ep1091 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz298 (@Neg.neg Real Real.instNeg (Real.sin qz396)) 302697 1048576 1 1048576 376185 524288 16694567 24954142720 113870070945 549755813888 20285268148289 104665260627066880 qz575 (@Enclosure.Real.IsNear.neg (Real.sin qz396) Bool.true 376185 524288 16694567 24954142720 (@Enclosure.Real.IsNear.recentre' (Real.sin qz396) Bool.true 752370 1048576 16694567 24954142720 376185 524288 16694567 24954142720 (ep1096 rfl rfl) rfl)) rfl)

noncomputable def ep1098 := @ep1045 27635328009 137438953472 5070793621111 26166315156766720 Bool.false 113870070945 549755813888 20285268148289 104665260627066880 Bool.false 559690498963967475449856 4072284347523 1099511627776 647170028153559 209330521254133760 Bool.false 5206866640914563989504 18942470491 549755813888 323607670177357 104665260627066880 (ep1046 (BSN.head_sum_c_succ qz64 11 12 rfl rfl) (ep1086 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1087 ep1097) rfl rfl

noncomputable abbrev qz397 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 13 1)))

noncomputable def ep1099 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz14 qz957 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz301 (Real.cos qz397)) (@HMul.hMul Real Real Real qz0 qz301 (@Neg.neg Real Real.instNeg (Real.sin qz397)))) Bool.true 151161943179 549755813888 19491995731817 104665260627066880 Bool.true 19966453065 549755813888 19406109631387 104665260627066880 (BSN.cpow_neg_s_mk qz61 126105 1000 13 (@Eq.refl Real qz61) rfl)

noncomputable def ep1100 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz303 126105 1000 0 1 11551497052968677 4503599627370496 200000000114231 38077000000000000000 291340307172923002617 900719925474099200 5044200002881020051 7615400000000000000000 qz386 (BSN.isNear_log_sfrac 13 1 11551497052968677 4503599627370496 200000000114231 38077000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz854) Bool.false 48450490295254733815808 18889465931478580854784 1000000000571155 190385000000000000000 11551497052968677 4503599627370496 200000000114231 38077000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 254545 524288 24973259072661432 36028797018963968 190385 1000000000000000 rfl rfl rfl rfl (ep258 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1101 := nat_lit 5880945572960703645150861672942410328751171193459785235269393430745496865975905

noncomputable def ep1102 := nat_lit 8337953527113809309886947946005404741767696793179454628244333951589244972641

noncomputable def ep1103 := nat_lit 15388976956805563379369582656269923062861633997586670784878872920792775871409761

noncomputable def ep1104 := BSN.sin_dyadic_bound_f 3091237931 2147483648 3 2 1048576 381142 ep1101 ep95 ep1102 ep1103 ep97 ep1102 1039546 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3091237931) qz272 0 2 ep1101 ep95 ep1102 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3091237931) qz273 0 2 ep1103 ep97 ep1102 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz962 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 84791189) qz313)

noncomputable def ep1105 := @Enclosure.Real.IsNear.cos_image qz397 qz962 Bool.false 84791189 262144 695 1048576 Bool.true 1039546 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz397 Bool.false 291340307172923002617 900719925474099200 5044200002881020051 7615400000000000000000 84791189 262144 695 1048576 (ep1100 rfl) rfl) (Enclosure.sfrac_false_div 84791189 262144) (BSN.cos_reduce1 qz962 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 54381632794045037150208) qz314) 226375608064910080 72057594037927936 Bool.false 1039546 1048576 51 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q1 84791189 262144 226375608064910080 72057594037927936 51 54381632794045037150208 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1039546 1048576 54381632794045037150208 37778931862957161709568 3091237931 2147483648 381142 380770 (ep1104 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1106 := nat_lit 3270897742101330384777095128499563695858102972719071554984438276614871256641121

noncomputable def ep1107 := nat_lit 9796017319249763535711511489606680278090773524570855755696826161941435279978081

noncomputable def ep1108 := BSN.cos_dyadic_bound_f 3091237931 2147483648 3 2 1048576 381142 ep1106 ep88 ep1102 ep1107 ep91 ep1102 137310 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3091237931) qz266 0 2 ep1106 ep88 ep1102 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3091237931) qz267 0 2 ep1107 ep91 ep1102 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1109 := @Enclosure.Real.IsNear.sin_image qz397 qz962 Bool.false 84791189 262144 695 1048576 Bool.false 137310 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz397 Bool.false 291340307172923002617 900719925474099200 5044200002881020051 7615400000000000000000 84791189 262144 695 1048576 (ep1100 rfl) rfl) (Enclosure.sfrac_false_div 84791189 262144) (BSN.sin_reduce1 qz962 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 54381632794045037150208) qz314) 226375608064910080 72057594037927936 Bool.false 137310 1048576 51 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q1 84791189 262144 226375608064910080 72057594037927936 51 54381632794045037150208 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 137310 1048576 54381632794045037150208 37778931862957161709568 3091237931 2147483648 381142 380770 (ep1108 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1110 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz301 (Real.cos qz397)) (@HMul.hMul Real Real Real qz0 qz301 (@Neg.neg Real Real.instNeg (Real.sin qz397))) Bool.true 151161943179 549755813888 19491995731817 104665260627066880 Bool.true 19966453065 549755813888 19406109631387 104665260627066880 (@Enclosure.Real.IsNear.mulLit_ft qz301 (Real.cos qz397) 290823 1048576 1 1048576 519773 524288 133366151 199633141760 151161943179 549755813888 19491995731817 104665260627066880 qz576 (@Enclosure.Real.IsNear.recentre' (Real.cos qz397) Bool.true 1039546 1048576 133366151 199633141760 519773 524288 133366151 199633141760 (ep1105 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz301 (@Neg.neg Real Real.instNeg (Real.sin qz397)) 290823 1048576 1 1048576 68655 524288 133366151 199633141760 19966453065 549755813888 19406109631387 104665260627066880 qz576 (@Enclosure.Real.IsNear.neg (Real.sin qz397) Bool.false 68655 524288 133366151 199633141760 (@Enclosure.Real.IsNear.recentre' (Real.sin qz397) Bool.false 137310 1048576 133366151 199633141760 68655 524288 133366151 199633141760 (ep1109 rfl rfl) rfl)) rfl)

noncomputable def ep1111 := @ep1042 151161943179 549755813888 19491995731817 104665260627066880 Bool.true 19966453065 549755813888 19406109631387 104665260627066880 Bool.false ep1043 3769960461165 1099511627776 686154019617193 209330521254133760 Bool.true 562940373376499187712 511991287 274877906944 42876722476093 13083157578383360 (ep1044 (BSN.head_sum_c_succ qz64 12 13 rfl rfl) (ep1098 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1099 ep1110) rfl rfl

noncomputable abbrev qz398 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 14 1)))

noncomputable def ep1112 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz14 qz956 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz304 (Real.cos qz398)) (@HMul.hMul Real Real Real qz0 qz304 (@Neg.neg Real Real.instNeg (Real.sin qz398)))) Bool.false 143678624399 549755813888 18811817994197 104665260627066880 Bool.false 61458130629 1099511627776 37470169876439 209330521254133760 (BSN.cpow_neg_s_mk qz61 126105 1000 14 (@Eq.refl Real qz61) rfl)

noncomputable def ep1113 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz306 126105 1000 0 1 11885250371606245 4503599627370496 200000000114231 38077000000000000000 59951579924456221029 180143985094819840 5044200002881020051 7615400000000000000000 qz386 (BSN.isNear_log_sfrac 14 1 11885250371606245 4503599627370496 200000000114231 38077000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz857) Bool.false 49850353174629559828480 18889465931478580854784 1000000000571155 190385000000000000000 11885250371606245 4503599627370496 200000000114231 38077000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 293399 524288 24973259072661432 36028797018963968 190385 1000000000000000 rfl rfl rfl rfl (ep272 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1114 := nat_lit 4685875828884074865837356331724457786736353542611735806501318929065561991840000

noncomputable def ep1115 := nat_lit 5296594250509652758099395115207522695570579174156073975492620637200100000000

noncomputable def ep1116 := nat_lit 12263956494481275687013296133853720118992859292939245849638371047473386007200000

noncomputable def ep1117 := BSN.sin_dyadic_bound_f 2920784990 2147483648 3 2 1048576 381142 ep1114 ep95 ep1115 ep1116 ep97 ep1115 1025386 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2920784990) qz272 0 2 ep1114 ep95 ep1115 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2920784990) qz273 0 2 ep1116 ep97 ep1115 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz963 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 348964123) qz268)

noncomputable def ep1118 := @Enclosure.Real.IsNear.cos_image qz398 qz963 Bool.false 348964123 1048576 87 131072 Bool.false 1025386 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz398 Bool.false 59951579924456221029 180143985094819840 5044200002881020051 7615400000000000000000 348964123 1048576 87 131072 (ep1113 rfl) rfl) (Enclosure.sfrac_false_div 348964123 1048576) (BSN.cos_reduce3 qz963 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 205531971791888765157376) qz271) 226375608064910080 72057594037927936 Bool.false 1025386 1048576 52 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q3 348964123 1048576 226375608064910080 72057594037927936 52 205531971791888765157376 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1025386 1048576 205531971791888765157376 151115727451828646838272 2920784990 2147483648 381142 380770 (ep1117 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1119 := nat_lit 2605618391269156993357686582120346558273783336639478147600951680875178928800000

noncomputable def ep1120 := nat_lit 7806261985306451674556860956130624629430208851570122294851869801351136586400000

noncomputable def ep1121 := BSN.cos_dyadic_bound_f 2920784990 2147483648 3 2 1048576 381142 ep1119 ep88 ep1115 ep1120 ep91 ep1115 219303 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2920784990) qz266 0 2 ep1119 ep88 ep1115 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2920784990) qz267 0 2 ep1120 ep91 ep1115 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1122 := @Enclosure.Real.IsNear.sin_image qz398 qz963 Bool.false 348964123 1048576 87 131072 Bool.true 219303 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz398 Bool.false 59951579924456221029 180143985094819840 5044200002881020051 7615400000000000000000 348964123 1048576 87 131072 (ep1113 rfl) rfl) (Enclosure.sfrac_false_div 348964123 1048576) (BSN.sin_reduce3 qz963 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 205531971791888765157376) qz271) 226375608064910080 72057594037927936 Bool.false 219303 1048576 52 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q3 348964123 1048576 226375608064910080 72057594037927936 52 205531971791888765157376 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 219303 1048576 205531971791888765157376 151115727451828646838272 2920784990 2147483648 381142 380770 (ep1121 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1123 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz304 (Real.cos qz398)) (@HMul.hMul Real Real Real qz0 qz304 (@Neg.neg Real Real.instNeg (Real.sin qz398))) Bool.false 143678624399 549755813888 18811817994197 104665260627066880 Bool.false 61458130629 1099511627776 37470169876439 209330521254133760 (@Enclosure.Real.IsNear.mulLit_ff qz304 (Real.cos qz398) 280243 1048576 1 1048576 512693 524288 16694567 24954142720 143678624399 549755813888 18811817994197 104665260627066880 qz577 (@Enclosure.Real.IsNear.recentre' (Real.cos qz398) Bool.false 1025386 1048576 16694567 24954142720 512693 524288 16694567 24954142720 (ep1118 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz304 (@Neg.neg Real Real.instNeg (Real.sin qz398)) 280243 1048576 1 1048576 219303 1048576 16694567 24954142720 61458130629 1099511627776 37470169876439 209330521254133760 qz577 (@Enclosure.Real.IsNear.neg (Real.sin qz398) Bool.true 219303 1048576 16694567 24954142720 (@Enclosure.Real.IsNear.recentre' (Real.sin qz398) Bool.true 219303 1048576 16694567 24954142720 219303 1048576 16694567 24954142720 (ep1122 rfl rfl) rfl)) rfl)

noncomputable def ep1124 := @ep1039 143678624399 549755813888 18811817994197 104665260627066880 Bool.false 61458130629 1099511627776 37470169876439 209330521254133760 Bool.false ep1040 4057317709963 1099511627776 723777655605587 209330521254133760 Bool.false 16330541938613959000064 59410165481 1099511627776 723497729493927 209330521254133760 (ep1041 (BSN.head_sum_c_succ qz64 13 14 rfl rfl) (ep1111 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1112 ep1123) rfl rfl

noncomputable abbrev qz399 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 15 1)))

noncomputable def ep1125 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz14 qz955 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz307 (Real.cos qz399)) (@HMul.hMul Real Real Real qz0 qz307 (@Neg.neg Real Real.instNeg (Real.sin qz399)))) Bool.true 168543041025 1099511627776 36277883091837 209330521254133760 Bool.true 228447194685 1099511627776 36320007676937 209330521254133760 (BSN.cpow_neg_s_mk qz61 126105 1000 15 (@Eq.refl Real qz61) rfl)

noncomputable def ep1126 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz309 126105 1000 0 1 12195965485668069 4503599627370496 200000000114231 38077000000000000000 307594445514034368249 900719925474099200 5044200002881020051 7615400000000000000000 qz386 (BSN.isNear_log_sfrac 15 1 12195965485668069 4503599627370496 200000000114231 38077000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz860) Bool.false 51153586820399524478976 18889465931478580854784 1000000000571155 190385000000000000000 12195965485668069 4503599627370496 200000000114231 38077000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 329571 524288 24973259072661432 36028797018963968 190385 1000000000000000 rfl rfl rfl rfl (ep283 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1127 := nat_lit 3471704586306030605807534711158716481

noncomputable def ep1128 := BSN.sin_dyadic_bound_f 1365009553 2147483648 2 1 1048576 381142 ep1127 ep123 ep1127 ep1127 ep124 ep1127 622525 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1365009553) qz272 0 1 ep1127 ep123 ep1127 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1365009553) qz273 0 1 ep1127 ep124 ep1127 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz964 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 358087063) qz268)

noncomputable def ep1129 := @Enclosure.Real.IsNear.cos_image qz399 qz964 Bool.false 358087063 1048576 87 131072 Bool.true 622525 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz399 Bool.false 307594445514034368249 900719925474099200 5044200002881020051 7615400000000000000000 358087063 1048576 87 131072 (ep1126 rfl) rfl) (Enclosure.sfrac_false_div 358087063 1048576) (BSN.cos_reduce1 qz964 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 96054008083010421784576) qz271) 226375608064910080 72057594037927936 Bool.false 622525 1048576 54 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q1 358087063 1048576 226375608064910080 72057594037927936 54 96054008083010421784576 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 622525 1048576 96054008083010421784576 151115727451828646838272 1365009553 2147483648 381142 380770 (ep1128 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1130 := nat_lit 124054837389976404429134276354341885381614277332994688054076883206229162688641

noncomputable def ep1131 := nat_lit 12052732734578327111370407711858729460003880553133993666255734903341023361

noncomputable def ep1132 := nat_lit 372140406704460056633180088247601938685922824237877796174898138148880806019201

noncomputable def ep1133 := BSN.cos_dyadic_bound_f 1365009553 2147483648 3 2 1048576 381142 ep1130 ep88 ep1131 ep1132 ep91 ep1131 843785 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1365009553) qz266 0 2 ep1130 ep88 ep1131 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1365009553) qz267 0 2 ep1132 ep91 ep1131 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1134 := @Enclosure.Real.IsNear.sin_image qz399 qz964 Bool.false 358087063 1048576 87 131072 Bool.false 843785 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz399 Bool.false 307594445514034368249 900719925474099200 5044200002881020051 7615400000000000000000 358087063 1048576 87 131072 (ep1126 rfl) rfl) (Enclosure.sfrac_false_div 358087063 1048576) (BSN.sin_reduce1 qz964 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 96054008083010421784576) qz271) 226375608064910080 72057594037927936 Bool.false 843785 1048576 54 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q1 358087063 1048576 226375608064910080 72057594037927936 54 96054008083010421784576 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 843785 1048576 96054008083010421784576 151115727451828646838272 1365009553 2147483648 381142 380770 (ep1133 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1135 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz307 (Real.cos qz399)) (@HMul.hMul Real Real Real qz0 qz307 (@Neg.neg Real Real.instNeg (Real.sin qz399))) Bool.true 168543041025 1099511627776 36277883091837 209330521254133760 Bool.true 228447194685 1099511627776 36320007676937 209330521254133760 (@Enclosure.Real.IsNear.mulLit_ft qz307 (Real.cos qz399) 270741 1048576 1 1048576 622525 1048576 16694567 24954142720 168543041025 1099511627776 36277883091837 209330521254133760 qz578 (@Enclosure.Real.IsNear.recentre' (Real.cos qz399) Bool.true 622525 1048576 16694567 24954142720 622525 1048576 16694567 24954142720 (ep1129 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz307 (@Neg.neg Real Real.instNeg (Real.sin qz399)) 270741 1048576 1 1048576 843785 1048576 16694567 24954142720 228447194685 1099511627776 36320007676937 209330521254133760 qz578 (@Enclosure.Real.IsNear.neg (Real.sin qz399) Bool.false 843785 1048576 16694567 24954142720 (@Enclosure.Real.IsNear.recentre' (Real.sin qz399) Bool.false 843785 1048576 16694567 24954142720 843785 1048576 16694567 24954142720 (ep1134 rfl rfl) rfl)) rfl)

noncomputable def ep1136 := @ep1036 168543041025 1099511627776 36277883091837 209330521254133760 Bool.true 228447194685 1099511627776 36320007676937 209330521254133760 Bool.false ep1037 1944387334469 549755813888 47503471168589 13083157578383360 Bool.true 185858179134509289570304 42259257301 274877906944 47488608573179 13083157578383360 (ep1038 (BSN.head_sum_c_succ qz64 14 15 rfl rfl) (ep1124 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1125 ep1135) rfl rfl

noncomputable abbrev qz400 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 16 1)))

noncomputable def ep1137 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz14 qz954 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz310 (Real.cos qz400)) (@HMul.hMul Real Real Real qz0 qz310 (@Neg.neg Real Real.instNeg (Real.sin qz400)))) Bool.true 166412832831 1099511627776 35081995922289 209330521254133760 Bool.false 13673641023 68719476736 2195001689969 13083157578383360 (BSN.cpow_neg_s_mk qz61 126105 1000 16 (@Eq.refl Real qz61) rfl)

noncomputable def ep1138 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz312 126105 1000 0 1 3121657384082679 1125899906842624 50000000038077 9519250000000000000 78731320883949247059 225179981368524800 1261050000960340017 1903850000000000000000 qz386 (BSN.isNear_log_sfrac 16 1 3121657384082679 1125899906842624 50000000038077 9519250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz863) Bool.false 52372720210750067441664 18889465931478580854784 1000000000761540 190385000000000000000 3121657384082679 1125899906842624 50000000038077 9519250000000000000 (BSN.log_rat_reduce_isNear 16 1 4 32 32 0 524288 24973259072661432 36028797018963968 190385 1000000000000000 rfl rfl rfl rfl (ep298 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1139 := nat_lit 545832052583610012655187045713109713249516189920150325308538771513568232690625

noncomputable def ep1140 := nat_lit 233179003465094466852194071996735434711034899619785303829251782844187890625

noncomputable def ep1141 := nat_lit 1637029799743899849031856748995335668879126499961211405317957810975016322290625

noncomputable def ep1142 := BSN.cos_dyadic_bound_f 1976792935 2147483648 3 2 1048576 381142 ep1139 ep88 ep1140 ep1141 ep91 ep1140 634817 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1976792935) qz266 0 2 ep1139 ep88 ep1140 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1976792935) qz267 0 2 ep1141 ep91 ep1140 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz965 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 183310641) qz280)

noncomputable def ep1143 := @Enclosure.Real.IsNear.cos_image qz400 qz965 Bool.false 183310641 524288 695 1048576 Bool.true 634817 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz400 Bool.false 78731320883949247059 225179981368524800 1261050000960340017 1903850000000000000000 183310641 524288 695 1048576 (ep1138 rfl) rfl) (Enclosure.sfrac_false_div 183310641 524288) (BSN.cos_reduce2 qz965 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 69552218168598642819072) qz281) 226375608064910080 72057594037927936 Bool.false 634817 1048576 55 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q2 183310641 524288 226375608064910080 72057594037927936 55 69552218168598642819072 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 634817 1048576 69552218168598642819072 75557863725914323419136 1976792935 2147483648 381142 380770 (ep1142 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1144 := nat_lit 982311151447725947205854927026000095501360313936574757312306387298147468530625

noncomputable def ep1145 := nat_lit 2572342154452719708783287923237243630847363908567835188183174130513400399090625

noncomputable def ep1146 := BSN.sin_dyadic_bound_f 1976792935 2147483648 3 2 1048576 381142 ep1144 ep95 ep1140 ep1145 ep97 ep1140 834576 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1976792935) qz272 0 2 ep1144 ep95 ep1140 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1976792935) qz273 0 2 ep1145 ep97 ep1140 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1147 := @Enclosure.Real.IsNear.sin_image qz400 qz965 Bool.false 183310641 524288 695 1048576 Bool.true 834576 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz400 Bool.false 78731320883949247059 225179981368524800 1261050000960340017 1903850000000000000000 183310641 524288 695 1048576 (ep1138 rfl) rfl) (Enclosure.sfrac_false_div 183310641 524288) (BSN.sin_reduce2 qz965 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 69552218168598642819072) qz281) 226375608064910080 72057594037927936 Bool.false 834576 1048576 55 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q2 183310641 524288 226375608064910080 72057594037927936 55 69552218168598642819072 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 834576 1048576 69552218168598642819072 75557863725914323419136 1976792935 2147483648 381142 380770 (ep1146 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1148 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz310 (Real.cos qz400)) (@HMul.hMul Real Real Real qz0 qz310 (@Neg.neg Real Real.instNeg (Real.sin qz400))) Bool.true 166412832831 1099511627776 35081995922289 209330521254133760 Bool.false 13673641023 68719476736 2195001689969 13083157578383360 (@Enclosure.Real.IsNear.mulLit_ft qz310 (Real.cos qz400) 262143 1048576 1 1048576 634817 1048576 133366151 199633141760 166412832831 1099511627776 35081995922289 209330521254133760 qz579 (@Enclosure.Real.IsNear.recentre' (Real.cos qz400) Bool.true 634817 1048576 133366151 199633141760 634817 1048576 133366151 199633141760 (ep1143 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz310 (@Neg.neg Real Real.instNeg (Real.sin qz400)) 262143 1048576 1 1048576 52161 65536 133366151 199633141760 13673641023 68719476736 2195001689969 13083157578383360 qz579 (@Enclosure.Real.IsNear.neg (Real.sin qz400) Bool.true 52161 65536 133366151 199633141760 (@Enclosure.Real.IsNear.recentre' (Real.sin qz400) Bool.true 834576 1048576 133366151 199633141760 52161 65536 133366151 199633141760 (ep1147 rfl rfl) rfl)) rfl)

noncomputable def ep1149 := @ep1033 166412832831 1099511627776 35081995922289 209330521254133760 Bool.false 13673641023 68719476736 2195001689969 13083157578383360 Bool.false ep1034 3722361836107 1099511627776 795137534619713 209330521254133760 Bool.false 854547775729147314176 12435306791 274877906944 12420902565787 3270789394595840 (ep1035 (BSN.head_sum_c_succ qz64 15 16 rfl rfl) (ep1136 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1137 ep1148) rfl rfl

theorem EMRow41.d18 : Enclosure.Complex.IsNear (BSN.headSumC qz64 17) Bool.false 3722361836107 1099511627776 795137534619713 209330521254133760 Bool.false 12435306791 274877906944 12420902565787 3270789394595840 := ep1032 (BSN.head_sum_c_succ qz64 16 17 rfl rfl) (ep1149 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep1150 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 25) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 24) (@HPow.hPow Complex Complex Complex qz14 qz865 qz65)) Bool.false 2605246211759 549755813888 104482462938899 20933052125413376 Bool.false 16809981067 549755813888 104424412953165 20933052125413376

noncomputable def ep1151 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 24) (@HPow.hPow Complex Complex Complex qz14 qz865 qz65) Bool.false 5162544476933 1099511627776 203247257866635 41866104250826752 Bool.true 185634526179 1099511627776 203100682892063 41866104250826752 Bool.false

noncomputable def ep1152 := nat_lit 5728997006096791364435968

noncomputable def ep1153 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 24) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 23) (@HPow.hPow Complex Complex Complex qz14 qz866 qz65)) Bool.false 5162544476933 1099511627776 203247257866635 41866104250826752 Bool.true 185634526179 1099511627776 203100682892063 41866104250826752

noncomputable def ep1154 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 23) (@HPow.hPow Complex Complex Complex qz14 qz866 qz65) Bool.false 2477530398505 549755813888 493447956336973 104665260627066880 Bool.true 70791425601 274877906944 246564694938049 52332630313533440 Bool.false

noncomputable def ep1155 := nat_lit 2838138840649300657045504

noncomputable def ep1156 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 23) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 22) (@HPow.hPow Complex Complex Complex qz14 qz867 qz65)) Bool.false 2477530398505 549755813888 493447956336973 104665260627066880 Bool.true 70791425601 274877906944 246564694938049 52332630313533440

noncomputable def ep1157 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 22) (@HPow.hPow Complex Complex Complex qz14 qz867 qz65) Bool.false 1181817295079 274877906944 478443425708009 104665260627066880 Bool.true 227830203093 1099511627776 956396585100583 209330521254133760 Bool.false

noncomputable def ep1158 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 22) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 21) (@HPow.hPow Complex Complex Complex qz14 qz868 qz65)) Bool.false 1181817295079 274877906944 478443425708009 104665260627066880 Bool.true 227830203093 1099511627776 956396585100583 209330521254133760

noncomputable def ep1159 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 21) (@HPow.hPow Complex Complex Complex qz14 qz868 qz65) Bool.false 141781226047 34359738368 463026692771509 104665260627066880 Bool.true 81661951147 1099511627776 925636507695073 209330521254133760 Bool.false

noncomputable def ep1160 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 21) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 20) (@HPow.hPow Complex Complex Complex qz14 qz869 qz65)) Bool.false 141781226047 34359738368 463026692771509 104665260627066880 Bool.true 81661951147 1099511627776 925636507695073 209330521254133760

noncomputable def ep1161 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 20) (@HPow.hPow Complex Complex Complex qz14 qz869 qz65) Bool.false 2181591571681 549755813888 34409303395793 8051173894389760 Bool.false 11527268629 137438953472 4299158454171 1006396736798720 Bool.false

noncomputable def ep1162 := nat_lit 1247120853112111839051776

noncomputable def ep1163 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 20) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 19) (@HPow.hPow Complex Complex Complex qz14 qz870 qz65)) Bool.false 2181591571681 549755813888 34409303395793 8051173894389760 Bool.false 11527268629 137438953472 4299158454171 1006396736798720

noncomputable def ep1164 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 19) (@HPow.hPow Complex Complex Complex qz14 qz870 qz65) Bool.false 2077536813995 549755813888 431197311709739 104665260627066880 Bool.false 234757776097 1099511627776 862029587407033 209330521254133760 Bool.false

noncomputable def ep1165 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 19) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 18) (@HPow.hPow Complex Complex Complex qz14 qz871 qz65)) Bool.false 2077536813995 549755813888 431197311709739 104665260627066880 Bool.false 234757776097 1099511627776 862029587407033 209330521254133760

noncomputable def ep1166 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 18) (@HPow.hPow Complex Complex Complex qz14 qz871 qz65) Bool.false 3896473357915 1099511627776 829233707882401 209330521254133760 Bool.false 251727163757 1099511627776 829054804620981 209330521254133760 Bool.false

noncomputable def ep1167 := nat_lit 4568551768240414775050240

noncomputable def ep1168 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 18) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 17) (@HPow.hPow Complex Complex Complex qz14 qz872 qz65)) Bool.false 3896473357915 1099511627776 829233707882401 209330521254133760 Bool.false 251727163757 1099511627776 829054804620981 209330521254133760

noncomputable def ep1169 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 17) (@HPow.hPow Complex Complex Complex qz14 qz872 qz65) Bool.false 3722361836107 1099511627776 795137534619713 209330521254133760 Bool.false 12435306791 274877906944 12420902565787 3270789394595840 Bool.false

noncomputable abbrev qz401 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 17 1)))

noncomputable def ep1170 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz14 qz872 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz315 (Real.cos qz401)) (@HMul.hMul Real Real Real qz0 qz315 (@Neg.neg Real Real.instNeg (Real.sin qz401)))) Bool.false 10881970113 68719476736 10549558559 64768106823680 Bool.false 201985936593 1099511627776 337792479313 2072579418357760 (BSN.cpow_neg_s_mk qz61 126105 1000 17 (@Eq.refl Real qz61) rfl)

noncomputable def ep1171 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz317 126105 1000 0 1 3189913004350711 1125899906842624 50000000038077 9519250000000000000 80452795882729282131 225179981368524800 1261050000960340017 1903850000000000000000 qz386 (BSN.isNear_log_sfrac 17 1 3189913004350711 1125899906842624 50000000038077 9519250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz874) Bool.false 53517859495200818200576 18889465931478580854784 1000000000761540 190385000000000000000 3189913004350711 1125899906842624 50000000038077 9519250000000000000 (BSN.log_rat_reduce_isNear 17 1 4 34 32 31784 524288 24973259072661432 36028797018963968 190385 1000000000000000 rfl rfl rfl rfl (ep329 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1172 := nat_lit 5447784012707174492917906716684960000

noncomputable def ep1173 := BSN.sin_dyadic_bound_f 1527759420 2147483648 2 1 1048576 381142 ep1172 ep123 ep1172 ep1172 ep124 ep1172 684624 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1527759420) qz272 0 1 ep1172 ep123 ep1172 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1527759420) qz273 0 1 ep1172 ep124 ep1172 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz966 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 93659381) qz313)

noncomputable def ep1174 := @Enclosure.Real.IsNear.cos_image qz401 qz966 Bool.false 93659381 262144 87 131072 Bool.false 684624 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz401 Bool.false 80452795882729282131 225179981368524800 1261050000960340017 1903850000000000000000 93659381 262144 87 131072 (ep1171 rfl) rfl) (Enclosure.sfrac_false_div 93659381 262144) (BSN.cos_reduce3 qz966 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26876627954354138120192) qz314) 226375608064910080 72057594037927936 Bool.false 684624 1048576 56 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q3 93659381 262144 226375608064910080 72057594037927936 56 26876627954354138120192 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 684624 1048576 26876627954354138120192 37778931862957161709568 1527759420 2147483648 381142 380770 (ep1173 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1175 := nat_lit 194677086374043858038559921801728488074545796726662326476894473614766284800000

noncomputable def ep1176 := nat_lit 29678350649107883936924854642761175954711741764616003424851890201600000000

noncomputable def ep1177 := nat_lit 583971902420833358347805915695899941871727966696457747423833717063895654400000

noncomputable def ep1178 := BSN.cos_dyadic_bound_f 1527759420 2147483648 3 2 1048576 381142 ep1175 ep88 ep1176 ep1177 ep91 ep1176 794229 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1527759420) qz266 0 2 ep1175 ep88 ep1176 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1527759420) qz267 0 2 ep1177 ep91 ep1176 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1179 := @Enclosure.Real.IsNear.sin_image qz401 qz966 Bool.false 93659381 262144 87 131072 Bool.true 794229 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz401 Bool.false 80452795882729282131 225179981368524800 1261050000960340017 1903850000000000000000 93659381 262144 87 131072 (ep1171 rfl) rfl) (Enclosure.sfrac_false_div 93659381 262144) (BSN.sin_reduce3 qz966 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26876627954354138120192) qz314) 226375608064910080 72057594037927936 Bool.false 794229 1048576 56 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q3 93659381 262144 226375608064910080 72057594037927936 56 26876627954354138120192 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 794229 1048576 26876627954354138120192 37778931862957161709568 1527759420 2147483648 381142 380770 (ep1178 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1180 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz315 (Real.cos qz401)) (@HMul.hMul Real Real Real qz0 qz315 (@Neg.neg Real Real.instNeg (Real.sin qz401))) Bool.false 10881970113 68719476736 10549558559 64768106823680 Bool.false 201985936593 1099511627776 337792479313 2072579418357760 (@Enclosure.Real.IsNear.mulLit_ff qz315 (Real.cos qz401) 254317 1048576 1 1048576 42789 65536 16694567 24954142720 10881970113 68719476736 10549558559 64768106823680 qz580 (@Enclosure.Real.IsNear.recentre' (Real.cos qz401) Bool.false 684624 1048576 16694567 24954142720 42789 65536 16694567 24954142720 (ep1174 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz315 (@Neg.neg Real Real.instNeg (Real.sin qz401)) 254317 1048576 1 1048576 794229 1048576 16694567 24954142720 201985936593 1099511627776 337792479313 2072579418357760 qz580 (@Enclosure.Real.IsNear.neg (Real.sin qz401) Bool.true 794229 1048576 16694567 24954142720 (@Enclosure.Real.IsNear.recentre' (Real.sin qz401) Bool.true 794229 1048576 16694567 24954142720 794229 1048576 16694567 24954142720 (ep1179 rfl rfl) rfl)) rfl)

noncomputable def ep1181 := @ep1169 10881970113 68719476736 10549558559 64768106823680 Bool.false 201985936593 1099511627776 337792479313 2072579418357760 Bool.false 267763610271683643965440 3896473357915 1099511627776 829233707882401 209330521254133760 Bool.false 69194235894473695428608 251727163757 1099511627776 829054804620981 209330521254133760 EMRow41.d18 (ep1170 ep1180) rfl rfl

noncomputable abbrev qz402 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 18 1)))

noncomputable def ep1182 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz14 qz871 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz318 (Real.cos qz402)) (@HMul.hMul Real Real Real qz0 qz318 (@Neg.neg Real Real.instNeg (Real.sin qz402)))) Bool.false 258600270075 1099511627776 33160915537077 209330521254133760 Bool.true 4242346915 274877906944 8243695696513 52332630313533440 (BSN.cpow_neg_s_mk qz61 126105 1000 18 (@Eq.refl Real qz61) rfl)

noncomputable def ep1183 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz320 126105 1000 0 1 3254268794313975 1125899906842624 50000000038077 9519250000000000000 3283036530455710539 9007199254740992 1261050000960340017 1903850000000000000000 qz386 (BSN.isNear_log_sfrac 18 1 3254268794313975 1125899906842624 50000000038077 9519250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz877) Bool.false 54597570484265130393600 18889465931478580854784 1000000000761540 190385000000000000000 3254268794313975 1125899906842624 50000000038077 9519250000000000000 (BSN.log_rat_reduce_isNear 18 1 4 36 32 61752 524288 24973259072661432 36028797018963968 190385 1000000000000000 rfl rfl rfl rfl (ep344 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1184 := nat_lit 392094122431228610283379426966081

noncomputable def ep1185 := BSN.cos_dyadic_bound_f 140717329 2147483648 2 1 1048576 381142 ep1184 ep143 ep1184 ep1184 ep144 ep1184 1046325 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 140717329) qz266 0 1 ep1184 ep143 ep1184 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 140717329) qz267 0 1 ep1184 ep144 ep1184 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz967 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 191097877) qz280)

noncomputable def ep1186 := @Enclosure.Real.IsNear.cos_image qz402 qz967 Bool.false 191097877 524288 695 1048576 Bool.false 1046325 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz402 Bool.false 3283036530455710539 9007199254740992 1261050000960340017 1903850000000000000000 191097877 524288 695 1048576 (ep1183 rfl) rfl) (Enclosure.sfrac_false_div 191097877 524288) (BSN.cos_reduce0 qz967 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4951050888318459838464) qz281) 226375608064910080 72057594037927936 Bool.false 1046325 1048576 58 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q0 191097877 524288 226375608064910080 72057594037927936 58 4951050888318459838464 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1046325 1048576 4951050888318459838464 75557863725914323419136 140717329 2147483648 381142 380770 (ep1185 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1187 := BSN.sin_dyadic_bound_f 140717329 2147483648 1 0 1048576 381142 0 1 1 0 1 1 68660 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 140717329) qz272 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 140717329) qz273 0 0 rfl) rfl rfl

noncomputable def ep1188 := @Enclosure.Real.IsNear.sin_image qz402 qz967 Bool.false 191097877 524288 695 1048576 Bool.false 68660 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz402 Bool.false 3283036530455710539 9007199254740992 1261050000960340017 1903850000000000000000 191097877 524288 695 1048576 (ep1183 rfl) rfl) (Enclosure.sfrac_false_div 191097877 524288) (BSN.sin_reduce0 qz967 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4951050888318459838464) qz281) 226375608064910080 72057594037927936 Bool.false 68660 1048576 58 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q0 191097877 524288 226375608064910080 72057594037927936 58 4951050888318459838464 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 68660 1048576 4951050888318459838464 75557863725914323419136 140717329 2147483648 381142 380770 (ep1187 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1189 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz318 (Real.cos qz402)) (@HMul.hMul Real Real Real qz0 qz318 (@Neg.neg Real Real.instNeg (Real.sin qz402))) Bool.false 258600270075 1099511627776 33160915537077 209330521254133760 Bool.true 4242346915 274877906944 8243695696513 52332630313533440 (@Enclosure.Real.IsNear.mulLit_ff qz318 (Real.cos qz402) 247151 1048576 1 1048576 1046325 1048576 133366151 199633141760 258600270075 1099511627776 33160915537077 209330521254133760 qz581 (@Enclosure.Real.IsNear.recentre' (Real.cos qz402) Bool.false 1046325 1048576 133366151 199633141760 1046325 1048576 133366151 199633141760 (ep1186 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz318 (@Neg.neg Real Real.instNeg (Real.sin qz402)) 247151 1048576 1 1048576 17165 262144 133366151 199633141760 4242346915 274877906944 8243695696513 52332630313533440 qz581 (@Enclosure.Real.IsNear.neg (Real.sin qz402) Bool.false 17165 262144 133366151 199633141760 (@Enclosure.Real.IsNear.recentre' (Real.sin qz402) Bool.false 68660 1048576 133366151 199633141760 17165 262144 133366151 199633141760 (ep1188 rfl rfl) rfl)) rfl)

noncomputable def ep1190 := @ep1166 258600270075 1099511627776 33160915537077 209330521254133760 Bool.true 4242346915 274877906944 8243695696513 52332630313533440 Bool.false ep1167 2077536813995 549755813888 431197311709739 104665260627066880 Bool.false 64529726132371553517568 234757776097 1099511627776 862029587407033 209330521254133760 (ep1168 (BSN.head_sum_c_succ qz64 17 18 rfl rfl) (ep1181 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1182 ep1189) rfl rfl

noncomputable abbrev qz403 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 19 1)))

noncomputable def ep1191 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz14 qz870 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz321 (Real.cos qz403)) (@HMul.hMul Real Real Real qz0 qz321 (@Neg.neg Real Real.instNeg (Real.sin qz403)))) Bool.false 52027378843 274877906944 1612363243557 10466526062706688 Bool.true 142539627065 1099511627776 6439074212107 41866104250826752 (BSN.cpow_neg_s_mk qz61 126105 1000 19 (@Eq.refl Real qz61) rfl)

noncomputable def ep1192 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz323 126105 1000 0 1 3315143513283831 1125899906842624 50000000038077 9519250000000000000 83611234548531501651 225179981368524800 1261050000960340017 1903850000000000000000 qz386 (BSN.isNear_log_sfrac 19 1 3315143513283831 1125899906842624 50000000038077 9519250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz880) Bool.false 55618878793361701994496 18889465931478580854784 1000000000761540 190385000000000000000 3315143513283831 1125899906842624 50000000038077 9519250000000000000 (BSN.log_rat_reduce_isNear 19 1 4 38 32 90099 524288 24973259072661432 36028797018963968 190385 1000000000000000 rfl rfl rfl rfl (ep355 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1193 := nat_lit 2766179032785019555387120109763081121

noncomputable def ep1194 := BSN.cos_dyadic_bound_f 1289644681 2147483648 2 1 1048576 381142 ep1193 ep143 ep1193 ep1193 ep144 ep1193 865108 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1289644681) qz266 0 1 ep1193 ep143 ep1193 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1289644681) qz267 0 1 ep1193 ep144 ep1193 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz968 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 389345151) qz268)

noncomputable def ep1195 := @Enclosure.Real.IsNear.cos_image qz403 qz968 Bool.false 389345151 1048576 695 1048576 Bool.false 865108 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz403 Bool.false 83611234548531501651 225179981368524800 1261050000960340017 1903850000000000000000 389345151 1048576 695 1048576 (ep1192 rfl) rfl) (Enclosure.sfrac_false_div 389345151 1048576) (BSN.cos_reduce0 qz968 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 90750676651512055201792) qz271) 226375608064910080 72057594037927936 Bool.false 865108 1048576 59 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q0 389345151 1048576 226375608064910080 72057594037927936 59 90750676651512055201792 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 865108 1048576 90750676651512055201792 151115727451828646838272 1289644681 2147483648 381142 380770 (ep1194 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1196 := BSN.sin_dyadic_bound_f 1289644681 2147483648 2 1 1048576 381142 ep1193 ep123 ep1193 ep1193 ep124 ep1193 592535 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1289644681) qz272 0 1 ep1193 ep123 ep1193 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1289644681) qz273 0 1 ep1193 ep124 ep1193 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1197 := @Enclosure.Real.IsNear.sin_image qz403 qz968 Bool.false 389345151 1048576 695 1048576 Bool.false 592535 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz403 Bool.false 83611234548531501651 225179981368524800 1261050000960340017 1903850000000000000000 389345151 1048576 695 1048576 (ep1192 rfl) rfl) (Enclosure.sfrac_false_div 389345151 1048576) (BSN.sin_reduce0 qz968 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 90750676651512055201792) qz271) 226375608064910080 72057594037927936 Bool.false 592535 1048576 59 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q0 389345151 1048576 226375608064910080 72057594037927936 59 90750676651512055201792 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 592535 1048576 90750676651512055201792 151115727451828646838272 1289644681 2147483648 381142 380770 (ep1196 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1198 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz321 (Real.cos qz403)) (@HMul.hMul Real Real Real qz0 qz321 (@Neg.neg Real Real.instNeg (Real.sin qz403))) Bool.false 52027378843 274877906944 1612363243557 10466526062706688 Bool.true 142539627065 1099511627776 6439074212107 41866104250826752 (@Enclosure.Real.IsNear.mulLit_ff qz321 (Real.cos qz403) 240559 1048576 1 1048576 216277 262144 133366151 199633141760 52027378843 274877906944 1612363243557 10466526062706688 qz582 (@Enclosure.Real.IsNear.recentre' (Real.cos qz403) Bool.false 865108 1048576 133366151 199633141760 216277 262144 133366151 199633141760 (ep1195 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz321 (@Neg.neg Real Real.instNeg (Real.sin qz403)) 240559 1048576 1 1048576 592535 1048576 133366151 199633141760 142539627065 1099511627776 6439074212107 41866104250826752 qz582 (@Enclosure.Real.IsNear.neg (Real.sin qz403) Bool.false 592535 1048576 133366151 199633141760 (@Enclosure.Real.IsNear.recentre' (Real.sin qz403) Bool.false 592535 1048576 133366151 199633141760 592535 1048576 133366151 199633141760 (ep1197 rfl rfl) rfl)) rfl)

noncomputable def ep1199 := @ep1164 52027378843 274877906944 1612363243557 10466526062706688 Bool.true 142539627065 1099511627776 6439074212107 41866104250826752 Bool.false 599671325030344623652864 2181591571681 549755813888 34409303395793 8051173894389760 Bool.false 101394927152664078712832 11527268629 137438953472 4299158454171 1006396736798720 (ep1165 (BSN.head_sum_c_succ qz64 18 19 rfl rfl) (ep1190 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1191 ep1198) rfl rfl

noncomputable abbrev qz404 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 20 1)))

noncomputable def ep1200 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz14 qz869 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz324 (Real.cos qz404)) (@HMul.hMul Real Real Real qz0 qz324 (@Neg.neg Real Real.instNeg (Real.sin qz404)))) Bool.false 86908045071 549755813888 392643715655 2616631515676672 Bool.true 173880100179 1099511627776 6282309845501 41866104250826752 (BSN.cpow_neg_s_mk qz61 126105 1000 20 (@Eq.refl Real qz61) rfl)

noncomputable def ep1201 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz326 126105 1000 0 1 3372893643545847 1125899906842624 50000000038077 9519250000000000000 85067750583869807187 225179981368524800 1261050000960340017 1903850000000000000000 qz386 (BSN.isNear_log_sfrac 20 1 3372893643545847 1125899906842624 50000000038077 9519250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz883) Bool.false 56587765202795681021952 18889465931478580854784 1000000000761540 190385000000000000000 3372893643545847 1125899906842624 50000000038077 9519250000000000000 (BSN.log_rat_reduce_isNear 20 1 4 40 32 116991 524288 24973259072661432 36028797018963968 190385 1000000000000000 rfl rfl rfl rfl (ep369 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1202 := nat_lit 289476922198028061978477733260823497878103571767701933985686054668650399399936

noncomputable def ep1203 := nat_lit 65610525318967557971080741579696641102474239289892975104468863182077689856

noncomputable def ep1204 := nat_lit 868299545543446250819491038299311100352105766824526016006849226279587042820096

noncomputable def ep1205 := BSN.cos_dyadic_bound_f 1687025664 2147483648 3 2 1048576 381142 ep1202 ep88 ep1203 ep1204 ep91 ep1203 741318 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1687025664) qz266 0 2 ep1202 ep88 ep1203 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1687025664) qz267 0 2 ep1204 ep91 ep1203 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz969 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 198063791) qz280)

noncomputable def ep1206 := @Enclosure.Real.IsNear.cos_image qz404 qz969 Bool.false 198063791 524288 695 1048576 Bool.false 741318 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz404 Bool.false 85067750583869807187 225179981368524800 1261050000960340017 1903850000000000000000 198063791 524288 695 1048576 (ep1201 rfl) rfl) (Enclosure.sfrac_false_div 198063791 524288) (BSN.cos_reduce0 qz969 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 59356938709471332401152) qz281) 226375608064910080 72057594037927936 Bool.false 741318 1048576 60 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q0 198063791 524288 226375608064910080 72057594037927936 60 59356938709471332401152 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 741318 1048576 59356938709471332401152 75557863725914323419136 1687025664 2147483648 381142 380770 (ep1205 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1207 := nat_lit 8100032427031854665196127791995682816

noncomputable def ep1208 := BSN.sin_dyadic_bound_f 1687025664 2147483648 2 1 1048576 381142 ep1207 ep123 ep1207 ep1207 ep124 ep1207 741591 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1687025664) qz272 0 1 ep1207 ep123 ep1207 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1687025664) qz273 0 1 ep1207 ep124 ep1207 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1209 := @Enclosure.Real.IsNear.sin_image qz404 qz969 Bool.false 198063791 524288 695 1048576 Bool.false 741591 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz404 Bool.false 85067750583869807187 225179981368524800 1261050000960340017 1903850000000000000000 198063791 524288 695 1048576 (ep1201 rfl) rfl) (Enclosure.sfrac_false_div 198063791 524288) (BSN.sin_reduce0 qz969 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 59356938709471332401152) qz281) 226375608064910080 72057594037927936 Bool.false 741591 1048576 60 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q0 198063791 524288 226375608064910080 72057594037927936 60 59356938709471332401152 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 741591 1048576 59356938709471332401152 75557863725914323419136 1687025664 2147483648 381142 380770 (ep1208 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1210 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz324 (Real.cos qz404)) (@HMul.hMul Real Real Real qz0 qz324 (@Neg.neg Real Real.instNeg (Real.sin qz404))) Bool.false 86908045071 549755813888 392643715655 2616631515676672 Bool.true 173880100179 1099511627776 6282309845501 41866104250826752 (@Enclosure.Real.IsNear.mulLit_ff qz324 (Real.cos qz404) 234469 1048576 1 1048576 370659 524288 133366151 199633141760 86908045071 549755813888 392643715655 2616631515676672 qz583 (@Enclosure.Real.IsNear.recentre' (Real.cos qz404) Bool.false 741318 1048576 133366151 199633141760 370659 524288 133366151 199633141760 (ep1206 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz324 (@Neg.neg Real Real.instNeg (Real.sin qz404)) 234469 1048576 1 1048576 741591 1048576 133366151 199633141760 173880100179 1099511627776 6282309845501 41866104250826752 qz583 (@Enclosure.Real.IsNear.neg (Real.sin qz404) Bool.false 741591 1048576 133366151 199633141760 (@Enclosure.Real.IsNear.recentre' (Real.sin qz404) Bool.false 741591 1048576 133366151 199633141760 741591 1048576 133366151 199633141760 (ep1209 rfl rfl) rfl)) rfl)

noncomputable def ep1211 := @ep1161 86908045071 549755813888 392643715655 2616631515676672 Bool.true 173880100179 1099511627776 6282309845501 41866104250826752 Bool.false ep1162 141781226047 34359738368 463026692771509 104665260627066880 Bool.true 11223533104125270032384 81661951147 1099511627776 925636507695073 209330521254133760 (ep1163 (BSN.head_sum_c_succ qz64 19 20 rfl rfl) (ep1199 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1200 ep1210) rfl rfl

noncomputable abbrev qz405 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 21 1)))

noncomputable def ep1212 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz14 qz868 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz327 (Real.cos qz405)) (@HMul.hMul Real Real Real qz0 qz327 (@Neg.neg Real Real.instNeg (Real.sin qz405)))) Bool.false 47567486703 274877906944 770836646825 5233263031353344 Bool.true 73084125973 549755813888 3076007740551 20933052125413376 (BSN.cpow_neg_s_mk qz61 126105 1000 21 (@Eq.refl Real qz61) rfl)

noncomputable def ep1213 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz329 126105 1000 0 1 3427826275261687 1125899906842624 50000000038077 9519250000000000000 86453206488375007827 225179981368524800 1261050000960340017 1903850000000000000000 qz386 (BSN.isNear_log_sfrac 21 1 3427826275261687 1125899906842624 50000000038077 9519250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz886) Bool.false 57509381830540779323392 18889465931478580854784 1000000000761540 190385000000000000000 3427826275261687 1125899906842624 50000000038077 9519250000000000000 (BSN.log_rat_reduce_isNear 21 1 4 42 32 142571 524288 24973259072661432 36028797018963968 190385 1000000000000000 rfl rfl rfl rfl (ep383 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1214 := nat_lit 139930947643370753793669986308603997708922531014025445153031412774369614626816

noncomputable def ep1215 := nat_lit 15334685403920025094927037905098155012895720652584986556026350635147329536

noncomputable def ep1216 := nat_lit 419762173559304421330820104850001796816741801600771165485982185621838549221376

noncomputable def ep1217 := BSN.cos_dyadic_bound_f 1406725496 2147483648 3 2 1048576 381142 ep1214 ep88 ep1215 ep1216 ep91 ep1215 831534 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1406725496) qz266 0 2 ep1214 ep88 ep1215 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1406725496) qz267 0 2 ep1216 ep91 ep1215 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz970 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 201289557) qz280)

noncomputable def ep1218 := @Enclosure.Real.IsNear.cos_image qz405 qz970 Bool.false 201289557 524288 695 1048576 Bool.false 831534 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz405 Bool.false 86453206488375007827 225179981368524800 1261050000960340017 1903850000000000000000 201289557 524288 695 1048576 (ep1213 rfl) rfl) (Enclosure.sfrac_false_div 201289557 524288) (BSN.cos_reduce0 qz970 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 49494753283630321106944) qz281) 226375608064910080 72057594037927936 Bool.false 831534 1048576 61 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q0 201289557 524288 226375608064910080 72057594037927936 61 49494753283630321106944 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 831534 1048576 49494753283630321106944 75557863725914323419136 1406725496 2147483648 381142 380770 (ep1217 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1219 := nat_lit 3915952681522087173511285706002272256

noncomputable def ep1220 := BSN.sin_dyadic_bound_f 1406725496 2147483648 2 1 1048576 381142 ep1219 ep123 ep1219 ep1219 ep124 ep1219 638797 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1406725496) qz272 0 1 ep1219 ep123 ep1219 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1406725496) qz273 0 1 ep1219 ep124 ep1219 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1221 := @Enclosure.Real.IsNear.sin_image qz405 qz970 Bool.false 201289557 524288 695 1048576 Bool.false 638797 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz405 Bool.false 86453206488375007827 225179981368524800 1261050000960340017 1903850000000000000000 201289557 524288 695 1048576 (ep1213 rfl) rfl) (Enclosure.sfrac_false_div 201289557 524288) (BSN.sin_reduce0 qz970 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 49494753283630321106944) qz281) 226375608064910080 72057594037927936 Bool.false 638797 1048576 61 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q0 201289557 524288 226375608064910080 72057594037927936 61 49494753283630321106944 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 638797 1048576 49494753283630321106944 75557863725914323419136 1406725496 2147483648 381142 380770 (ep1220 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1222 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz327 (Real.cos qz405)) (@HMul.hMul Real Real Real qz0 qz327 (@Neg.neg Real Real.instNeg (Real.sin qz405))) Bool.false 47567486703 274877906944 770836646825 5233263031353344 Bool.true 73084125973 549755813888 3076007740551 20933052125413376 (@Enclosure.Real.IsNear.mulLit_ff qz327 (Real.cos qz405) 114409 524288 1 524288 415767 524288 133366151 199633141760 47567486703 274877906944 770836646825 5233263031353344 qz585 (@Enclosure.Real.IsNear.recentre' (Real.cos qz405) Bool.false 831534 1048576 133366151 199633141760 415767 524288 133366151 199633141760 (ep1218 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz327 (@Neg.neg Real Real.instNeg (Real.sin qz405)) 114409 524288 1 524288 638797 1048576 133366151 199633141760 73084125973 549755813888 3076007740551 20933052125413376 qz585 (@Enclosure.Real.IsNear.neg (Real.sin qz405) Bool.false 638797 1048576 133366151 199633141760 (@Enclosure.Real.IsNear.recentre' (Real.sin qz405) Bool.false 638797 1048576 133366151 199633141760 638797 1048576 133366151 199633141760 (ep1221 rfl rfl) rfl)) rfl)

noncomputable def ep1223 := @ep1159 47567486703 274877906944 770836646825 5233263031353344 Bool.true 73084125973 549755813888 3076007740551 20933052125413376 Bool.false 40606933057691893891072 1181817295079 274877906944 478443425708009 104665260627066880 Bool.true 125250978729660549955584 227830203093 1099511627776 956396585100583 209330521254133760 (ep1160 (BSN.head_sum_c_succ qz64 20 21 rfl rfl) (ep1211 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1212 ep1222) rfl rfl

noncomputable abbrev qz406 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 22 1)))

noncomputable def ep1224 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz14 qz867 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz330 (Real.cos qz406)) (@HMul.hMul Real Real Real qz0 qz330 (@Neg.neg Real Real.instNeg (Real.sin qz406)))) Bool.false 113895808347 549755813888 3751132657241 26166315156766720 Bool.true 55335499311 1099511627776 29862194651613 209330521254133760 (BSN.cpow_neg_s_mk qz61 126105 1000 22 (@Eq.refl Real qz61) rfl)

noncomputable def ep1225 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz332 126105 1000 0 1 3480203401436407 1125899906842624 50000000038077 9519250000000000000 87774209987627620947 225179981368524800 1261050000960340017 1903850000000000000000 qz386 (BSN.isNear_log_sfrac 22 1 3480203401436407 1125899906842624 50000000038077 9519250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz888) Bool.false 58388124189833310502912 18889465931478580854784 1000000000761540 190385000000000000000 3480203401436407 1125899906842624 50000000038077 9519250000000000000 (BSN.log_rat_reduce_isNear 22 1 4 44 32 166961 524288 24973259072661432 36028797018963968 190385 1000000000000000 rfl rfl rfl rfl (ep394 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1226 := nat_lit 68590228812914234272344785938397761

noncomputable def ep1227 := BSN.cos_dyadic_bound_f 511759087 2147483648 2 1 1048576 381142 ep1226 ep143 ep1226 ep1226 ep144 ep1226 1018942 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 511759087) qz266 0 1 ep1226 ep143 ep1226 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 511759087) qz267 0 1 ep1226 ep144 ep1226 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz971 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 102182629) qz313)

noncomputable def ep1228 := @Enclosure.Real.IsNear.cos_image qz406 qz971 Bool.false 102182629 262144 695 1048576 Bool.false 1018942 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz406 Bool.false 87774209987627620947 225179981368524800 1261050000960340017 1903850000000000000000 102182629 262144 695 1048576 (ep1225 rfl) rfl) (Enclosure.sfrac_false_div 102182629 262144) (BSN.cos_reduce0 qz971 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9002961079592999190528) qz314) 226375608064910080 72057594037927936 Bool.false 1018942 1048576 62 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q0 102182629 262144 226375608064910080 72057594037927936 62 9002961079592999190528 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1018942 1048576 9002961079592999190528 37778931862957161709568 511759087 2147483648 381142 380770 (ep1227 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1229 := BSN.sin_dyadic_bound_f 511759087 2147483648 2 1 1048576 381142 ep1226 ep123 ep1226 ep1226 ep124 ep1226 247523 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 511759087) qz272 0 1 ep1226 ep123 ep1226 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 511759087) qz273 0 1 ep1226 ep124 ep1226 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1230 := @Enclosure.Real.IsNear.sin_image qz406 qz971 Bool.false 102182629 262144 695 1048576 Bool.false 247523 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz406 Bool.false 87774209987627620947 225179981368524800 1261050000960340017 1903850000000000000000 102182629 262144 695 1048576 (ep1225 rfl) rfl) (Enclosure.sfrac_false_div 102182629 262144) (BSN.sin_reduce0 qz971 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9002961079592999190528) qz314) 226375608064910080 72057594037927936 Bool.false 247523 1048576 62 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q0 102182629 262144 226375608064910080 72057594037927936 62 9002961079592999190528 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 247523 1048576 9002961079592999190528 37778931862957161709568 511759087 2147483648 381142 380770 (ep1229 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1231 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz330 (Real.cos qz406)) (@HMul.hMul Real Real Real qz0 qz330 (@Neg.neg Real Real.instNeg (Real.sin qz406))) Bool.false 113895808347 549755813888 3751132657241 26166315156766720 Bool.true 55335499311 1099511627776 29862194651613 209330521254133760 (@Enclosure.Real.IsNear.mulLit_ff qz330 (Real.cos qz406) 223557 1048576 1 1048576 509471 524288 133366151 199633141760 113895808347 549755813888 3751132657241 26166315156766720 qz586 (@Enclosure.Real.IsNear.recentre' (Real.cos qz406) Bool.false 1018942 1048576 133366151 199633141760 509471 524288 133366151 199633141760 (ep1228 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz330 (@Neg.neg Real Real.instNeg (Real.sin qz406)) 223557 1048576 1 1048576 247523 1048576 133366151 199633141760 55335499311 1099511627776 29862194651613 209330521254133760 qz586 (@Enclosure.Real.IsNear.neg (Real.sin qz406) Bool.false 247523 1048576 133366151 199633141760 (@Enclosure.Real.IsNear.recentre' (Real.sin qz406) Bool.false 247523 1048576 133366151 199633141760 247523 1048576 133366151 199633141760 (ep1230 rfl rfl) rfl)) rfl)

noncomputable def ep1232 := @ep1157 113895808347 549755813888 3751132657241 26166315156766720 Bool.true 55335499311 1099511627776 29862194651613 209330521254133760 Bool.false 681018370331188626718720 2477530398505 549755813888 493447956336973 104665260627066880 Bool.true 311343982380556436373504 70791425601 274877906944 246564694938049 52332630313533440 (ep1158 (BSN.head_sum_c_succ qz64 21 22 rfl rfl) (ep1223 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1224 ep1231) rfl rfl

noncomputable abbrev qz407 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 23 1)))

noncomputable def ep1233 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz14 qz866 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz333 (Real.cos qz407)) (@HMul.hMul Real Real Real qz0 qz333 (@Neg.neg Real Real.instNeg (Real.sin qz407)))) Bool.false 207483679923 1099511627776 29340376659229 209330521254133760 Bool.false 97531176225 1099511627776 29244634708119 209330521254133760 (BSN.cpow_neg_s_mk qz61 126105 1000 23 (@Eq.refl Real qz61) rfl)

noncomputable def ep1234 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz335 126105 1000 0 1 3530250507853047 1125899906842624 50000000038077 9519250000000000000 89036448058561698387 225179981368524800 1261050000960340017 1903850000000000000000 qz386 (BSN.isNear_log_sfrac 23 1 3530250507853047 1125899906842624 50000000038077 9519250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz891) Bool.false 59227775304360265777152 18889465931478580854784 1000000000761540 190385000000000000000 3530250507853047 1125899906842624 50000000038077 9519250000000000000 (BSN.log_rat_reduce_isNear 23 1 4 46 32 190266 524288 24973259072661432 36028797018963968 190385 1000000000000000 rfl rfl rfl rfl (ep404 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1235 := nat_lit 2242284036809976768294291563015925996900097477105270114783348344987416501989185

noncomputable def ep1236 := nat_lit 1214250421281616827059202154204501108181565524768607418831076503137384968001

noncomputable def ep1237 := nat_lit 5870682738582149870669810623458713180563199429187986840992566779676249358118721

noncomputable def ep1238 := BSN.sin_dyadic_bound_f 2429621001 2147483648 3 2 1048576 381142 ep1235 ep95 ep1236 ep1237 ep97 ep1236 948961 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2429621001) qz272 0 2 ep1235 ep95 ep1236 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2429621001) qz273 0 2 ep1237 ep97 ep1236 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz972 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 207304135) qz280)

noncomputable def ep1239 := @Enclosure.Real.IsNear.cos_image qz407 qz972 Bool.false 207304135 524288 695 1048576 Bool.false 948961 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz407 Bool.false 89036448058561698387 225179981368524800 1261050000960340017 1903850000000000000000 207304135 524288 695 1048576 (ep1234 rfl) rfl) (Enclosure.sfrac_false_div 207304135 524288) (BSN.cos_reduce3 qz972 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 85484689342586347847680) qz281) 226375608064910080 72057594037927936 Bool.false 948961 1048576 62 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q3 207304135 524288 226375608064910080 72057594037927936 62 85484689342586347847680 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 948961 1048576 85484689342586347847680 75557863725914323419136 2429621001 2147483648 381142 380770 (ep1238 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1240 := nat_lit 1246253020637223367642188291521827554325912627513936111510229558994403561090881

noncomputable def ep1241 := nat_lit 3736330561069106869272446470257073660761374751492271119693026523976935913336641

noncomputable def ep1242 := BSN.cos_dyadic_bound_f 2429621001 2147483648 3 2 1048576 381142 ep1240 ep88 ep1236 ep1241 ep91 ep1236 446075 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2429621001) qz266 0 2 ep1240 ep88 ep1236 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2429621001) qz267 0 2 ep1241 ep91 ep1236 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1243 := @Enclosure.Real.IsNear.sin_image qz407 qz972 Bool.false 207304135 524288 695 1048576 Bool.true 446075 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz407 Bool.false 89036448058561698387 225179981368524800 1261050000960340017 1903850000000000000000 207304135 524288 695 1048576 (ep1234 rfl) rfl) (Enclosure.sfrac_false_div 207304135 524288) (BSN.sin_reduce3 qz972 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 85484689342586347847680) qz281) 226375608064910080 72057594037927936 Bool.false 446075 1048576 62 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q3 207304135 524288 226375608064910080 72057594037927936 62 85484689342586347847680 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 446075 1048576 85484689342586347847680 75557863725914323419136 2429621001 2147483648 381142 380770 (ep1242 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1244 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz333 (Real.cos qz407)) (@HMul.hMul Real Real Real qz0 qz333 (@Neg.neg Real Real.instNeg (Real.sin qz407))) Bool.false 207483679923 1099511627776 29340376659229 209330521254133760 Bool.false 97531176225 1099511627776 29244634708119 209330521254133760 (@Enclosure.Real.IsNear.mulLit_ff qz333 (Real.cos qz407) 218643 1048576 1 1048576 948961 1048576 133366151 199633141760 207483679923 1099511627776 29340376659229 209330521254133760 qz587 (@Enclosure.Real.IsNear.recentre' (Real.cos qz407) Bool.false 948961 1048576 133366151 199633141760 948961 1048576 133366151 199633141760 (ep1239 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz333 (@Neg.neg Real Real.instNeg (Real.sin qz407)) 218643 1048576 1 1048576 446075 1048576 133366151 199633141760 97531176225 1099511627776 29244634708119 209330521254133760 qz587 (@Enclosure.Real.IsNear.neg (Real.sin qz407) Bool.true 446075 1048576 133366151 199633141760 (@Enclosure.Real.IsNear.recentre' (Real.sin qz407) Bool.true 446075 1048576 133366151 199633141760 446075 1048576 133366151 199633141760 (ep1243 rfl rfl) rfl)) rfl)

noncomputable def ep1245 := @ep1154 207483679923 1099511627776 29340376659229 209330521254133760 Bool.false 97531176225 1099511627776 29244634708119 209330521254133760 Bool.false ep1155 5162544476933 1099511627776 203247257866635 41866104250826752 Bool.true 51026830012624693886976 185634526179 1099511627776 203100682892063 41866104250826752 (ep1156 (BSN.head_sum_c_succ qz64 22 23 rfl rfl) (ep1232 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1233 ep1244) rfl rfl

noncomputable abbrev qz408 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 24 1)))

noncomputable def ep1246 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz14 qz865 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz336 (Real.cos qz408)) (@HMul.hMul Real Real Real qz0 qz336 (@Neg.neg Real Real.instNeg (Real.sin qz408)))) Bool.false 47947946585 1099511627776 5717668011163 41866104250826752 Bool.false 219254488313 1099511627776 5748143014267 41866104250826752 (BSN.cpow_neg_s_mk qz61 126105 1000 24 (@Eq.refl Real qz61) rfl)

noncomputable def ep1247 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz338 126105 1000 0 1 3578169457974519 1125899906842624 50000000038077 9519250000000000000 90245011899575343699 225179981368524800 1261050000960340017 1903850000000000000000 qz386 (BSN.isNear_log_sfrac 24 1 3578169457974519 1125899906842624 50000000038077 9519250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz894) Bool.false 60031721881041427759104 18889465931478580854784 1000000000761540 190385000000000000000 3578169457974519 1125899906842624 50000000038077 9519250000000000000 (BSN.log_rat_reduce_isNear 24 1 4 48 32 212580 524288 24973259072661432 36028797018963968 190385 1000000000000000 rfl rfl rfl rfl (ep418 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1248 := nat_lit 45695117811812308835466864047947776

noncomputable def ep1249 := BSN.sin_dyadic_bound_f 462346368 2147483648 2 1 1048576 381142 ep1248 ep123 ep1248 ep1248 ep124 ep1248 224015 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 462346368) qz272 0 1 ep1248 ep123 ep1248 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 462346368) qz273 0 1 ep1248 ep124 ep1248 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz973 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 105059021) qz313)

noncomputable def ep1250 := @Enclosure.Real.IsNear.cos_image qz408 qz973 Bool.false 105059021 262144 695 1048576 Bool.false 224015 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz408 Bool.false 90245011899575343699 225179981368524800 1261050000960340017 1903850000000000000000 105059021 262144 695 1048576 (ep1247 rfl) rfl) (Enclosure.sfrac_false_div 105059021 262144) (BSN.cos_reduce3 qz973 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8133683335505706483712) qz314) 226375608064910080 72057594037927936 Bool.false 224015 1048576 63 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q3 105059021 262144 226375608064910080 72057594037927936 63 8133683335505706483712 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 224015 1048576 8133683335505706483712 37778931862957161709568 462346368 2147483648 381142 380770 (ep1249 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1251 := BSN.cos_dyadic_bound_f 462346368 2147483648 2 1 1048576 381142 ep1248 ep143 ep1248 ep1248 ep144 ep1248 1024367 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 462346368) qz266 0 1 ep1248 ep143 ep1248 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 462346368) qz267 0 1 ep1248 ep144 ep1248 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1252 := @Enclosure.Real.IsNear.sin_image qz408 qz973 Bool.false 105059021 262144 695 1048576 Bool.true 1024367 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz408 Bool.false 90245011899575343699 225179981368524800 1261050000960340017 1903850000000000000000 105059021 262144 695 1048576 (ep1247 rfl) rfl) (Enclosure.sfrac_false_div 105059021 262144) (BSN.sin_reduce3 qz973 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8133683335505706483712) qz314) 226375608064910080 72057594037927936 Bool.false 1024367 1048576 63 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q3 105059021 262144 226375608064910080 72057594037927936 63 8133683335505706483712 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1024367 1048576 8133683335505706483712 37778931862957161709568 462346368 2147483648 381142 380770 (ep1251 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1253 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz336 (Real.cos qz408)) (@HMul.hMul Real Real Real qz0 qz336 (@Neg.neg Real Real.instNeg (Real.sin qz408))) Bool.false 47947946585 1099511627776 5717668011163 41866104250826752 Bool.false 219254488313 1099511627776 5748143014267 41866104250826752 (@Enclosure.Real.IsNear.mulLit_ff qz336 (Real.cos qz408) 214039 1048576 1 1048576 224015 1048576 133366151 199633141760 47947946585 1099511627776 5717668011163 41866104250826752 qz589 (@Enclosure.Real.IsNear.recentre' (Real.cos qz408) Bool.false 224015 1048576 133366151 199633141760 224015 1048576 133366151 199633141760 (ep1250 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz336 (@Neg.neg Real Real.instNeg (Real.sin qz408)) 214039 1048576 1 1048576 1024367 1048576 133366151 199633141760 219254488313 1099511627776 5748143014267 41866104250826752 qz589 (@Enclosure.Real.IsNear.neg (Real.sin qz408) Bool.true 1024367 1048576 133366151 199633141760 (@Enclosure.Real.IsNear.recentre' (Real.sin qz408) Bool.true 1024367 1048576 133366151 199633141760 1024367 1048576 133366151 199633141760 (ep1252 rfl rfl) rfl)) rfl)

noncomputable def ep1254 := @ep1151 47947946585 1099511627776 5717668011163 41866104250826752 Bool.false 219254488313 1099511627776 5748143014267 41866104250826752 Bool.false ep1152 2605246211759 549755813888 104482462938899 20933052125413376 Bool.false 36965539291721822633984 16809981067 549755813888 104424412953165 20933052125413376 (ep1153 (BSN.head_sum_c_succ qz64 23 24 rfl rfl) (ep1245 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1246 ep1253) rfl rfl

theorem EMRow41.d19 : Enclosure.Complex.IsNear (BSN.headSumC qz64 25) Bool.false 2605246211759 549755813888 104482462938899 20933052125413376 Bool.false 16809981067 549755813888 104424412953165 20933052125413376 := ep1150 (BSN.head_sum_c_succ qz64 24 25 rfl rfl) (ep1254 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz66 := (@HAdd.hAdd Complex Complex Complex qz260 qz384 qz553)

noncomputable def ep1255 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz3 (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2)) qz66) Bool.true 5724739569 80000 0 1 Bool.true 16037248038861 8000000 0 1

noncomputable def ep1256 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.re qz66)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.im qz66)) 636068841 16000 0 1 636098841 20000 0 1

noncomputable def ep1257 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.re qz66) 636068841 40000 0 1 5 2 0 1 636068841 16000

noncomputable abbrev qz67 := (@HAdd.hAdd Complex Complex Complex qz260 qz384 qz590)

noncomputable def ep1258 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz3 (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)) qz67) Bool.true 636068841 40000 0 1 Bool.false 25221 100 0 1

noncomputable def ep1259 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.re qz67)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.im qz67)) 3 4 0 1 636098841 40000 0 1

noncomputable def ep1260 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.re qz67) 1 2 0 1 3 2 0 1 3 4

noncomputable def ep1261 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)) qz64 Bool.false 1 2 0 1 Bool.false 126105 1000 0 1 (BSN.ascPochhammer_one_eval qz64)

noncomputable def ep1262 := ep1261 (@Enclosure.Complex.IsNear.of_eq qz64 (Complex.mk qz339 qz61) Bool.false 1 2 0 1 Bool.false 126105 1000 0 1 (BSN.s_crit_mk qz61 Bool.false 126105 1000 (@Eq.refl Real qz61)) (@Enclosure.Complex.IsNear.mk qz339 qz61 Bool.false 1 2 0 1 Bool.false 126105 1000 0 1 qz340 qz386))

noncomputable def ep1263 := @ep1260 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 126105 1000 0 1 ep1262)

noncomputable def ep1264 := @Enclosure.Complex.IsNear.of_eq qz67 (Complex.mk (Enclosure.sfrac Bool.false 3 2) qz61) Bool.false 3 2 0 1 Bool.false 126105 1000 0 1 (BSN.s_add_nat_mk qz61 Bool.false 126105 1000 1 (@Eq.refl Real qz61))

noncomputable abbrev qz624 := (ep1264 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz61 Bool.false 3 2 0 1 Bool.false 126105 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz386))

noncomputable def ep1265 := ep1263 (@Enclosure.Complex.IsNear.re_isNear qz67 Bool.false 3 2 0 1 Bool.false 126105 1000 0 1 qz624)

noncomputable def ep1266 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.im qz67) 126105 1000 0 1 126105 1000 0 1 636098841 40000

noncomputable def ep1267 := @ep1266 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 126105 1000 0 1 ep1262)

noncomputable def ep1268 := ep1267 (@Enclosure.Complex.IsNear.im_isNear qz67 Bool.false 3 2 0 1 Bool.false 126105 1000 0 1 qz624)

noncomputable def ep1269 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)) qz67 Bool.true 636068841 40000 0 1 Bool.false 25221 100 0 1 (@ep1259 2544275364 636068841 40000 0 1 (ep1265 rfl) (ep1268 rfl) rfl rfl)

noncomputable def ep1270 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.im qz67)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.re qz67)) 25221 400 0 1 75663 400 0 1

noncomputable def ep1271 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.im qz67) 1 2 0 1 126105 1000 0 1 25221 400

noncomputable def ep1272 := @ep1271 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 126105 1000 0 1 ep1262)

noncomputable def ep1273 := ep1272 (@Enclosure.Complex.IsNear.im_isNear qz67 Bool.false 3 2 0 1 Bool.false 126105 1000 0 1 qz624)

noncomputable def ep1274 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.re qz67) 126105 1000 0 1 3 2 0 1 75663 400

noncomputable def ep1275 := @ep1274 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 126105 1000 0 1 ep1262)

noncomputable def ep1276 := ep1275 (@Enclosure.Complex.IsNear.re_isNear qz67 Bool.false 3 2 0 1 Bool.false 126105 1000 0 1 qz624)

noncomputable abbrev qz625 := (ep1258 (BSN.ascPochhammer_succ_eval_c 1 2 qz64 rfl) (ep1269 (@ep1270 40353600 25221 100 0 1 (ep1273 rfl) (ep1276 rfl) rfl rfl)))

noncomputable def ep1277 := @ep1257 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 636068841 40000 0 1 Bool.false 25221 100 0 1 qz625)

noncomputable def ep1278 := @Enclosure.Complex.IsNear.of_eq qz66 (Complex.mk (Enclosure.sfrac Bool.false 5 2) qz61) Bool.false 5 2 0 1 Bool.false 126105 1000 0 1 (BSN.s_add_nat_mk qz61 Bool.false 126105 1000 2 (@Eq.refl Real qz61))

noncomputable abbrev qz626 := (ep1278 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz61 Bool.false 5 2 0 1 Bool.false 126105 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz386))

noncomputable def ep1279 := ep1277 (@Enclosure.Complex.IsNear.re_isNear qz66 Bool.false 5 2 0 1 Bool.false 126105 1000 0 1 qz626)

noncomputable def ep1280 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.im qz66) 25221 100 0 1 126105 1000 0 1 636098841 20000

noncomputable def ep1281 := @ep1280 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 636068841 40000 0 1 Bool.false 25221 100 0 1 qz625)

noncomputable def ep1282 := ep1281 (@Enclosure.Complex.IsNear.im_isNear qz66 Bool.false 5 2 0 1 Bool.false 126105 1000 0 1 qz626)

noncomputable def ep1283 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2)) qz66 Bool.true 5724739569 80000 0 1 Bool.true 16037248038861 8000000 0 1 (@ep1256 22898958276000 5724739569 80000 0 1 (ep1279 rfl) (ep1282 rfl) rfl rfl)

noncomputable def ep1284 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.im qz66)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.re qz66)) 16042292238861 8000000 0 1 25221 40 0 1

noncomputable def ep1285 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.im qz66) 636068841 40000 0 1 126105 1000 0 1 16042292238861 8000000

noncomputable def ep1286 := @ep1285 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 636068841 40000 0 1 Bool.false 25221 100 0 1 qz625)

noncomputable def ep1287 := ep1286 (@Enclosure.Complex.IsNear.im_isNear qz66 Bool.false 5 2 0 1 Bool.false 126105 1000 0 1 qz626)

noncomputable def ep1288 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.re qz66) 25221 100 0 1 5 2 0 1 25221 40

noncomputable def ep1289 := @ep1288 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 636068841 40000 0 1 Bool.false 25221 100 0 1 qz625)

noncomputable def ep1290 := ep1289 (@Enclosure.Complex.IsNear.re_isNear qz66 Bool.false 5 2 0 1 Bool.false 126105 1000 0 1 qz626)

noncomputable abbrev qz627 := (ep1283 (@ep1284 641489921554440 16037248038861 8000000 0 1 (ep1287 rfl) (ep1290 rfl) rfl rfl))

theorem EMRow41.d20 : Enclosure.Complex.IsNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 5724739569 80000 0 1 Bool.true 16037248038861 8000000 0 1 := ep1255 (BSN.ascPochhammer_succ_eval_c 2 3 qz64 rfl) qz627

noncomputable def ep1291 := nat_lit 70254335238253937981181810480319308066249

noncomputable def ep1292 := nat_lit 15380168039400736619342642618040320000000

noncomputable def ep1293 := nat_lit 4221126217457242184540824559269245004017795502657

noncomputable def ep1294 := nat_lit 557476464531938559899864629189476909842432000000000

noncomputable abbrev qz68 := (Complex.Stirling.logGammaStirling 2 qz380)

noncomputable abbrev qz628 := (@HAdd.hAdd Complex Complex Complex qz813 qz814 (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I (@HDiv.hDiv Complex Complex Complex qz815 (↑(Enclosure.sfrac Bool.false 126105 1000)) (2 : Complex))))

noncomputable abbrev qz409 := qz628

noncomputable abbrev qz69 := qz409

noncomputable abbrev qz410 := (@HMul.hMul Real Real Real qz0 (@HDiv.hDiv Real Real Real qz1 qz61 (2 : Real)) (Real.log Real.pi))

noncomputable def ep1295 := Complex.re (@HMul.hMul Complex Complex Complex qz3 (Complex.exp (@HMul.hMul Complex Complex Complex qz3 Complex.I ↑(@HSub.hSub Real Real Real qz597 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz410))) (zetaApproximant qz64 2 32))

noncomputable def ep1296 := @Enclosure.Real.IsNear.of_eq ep1295 (@HSub.hSub Real Real Real qz597 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz597 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz410)) (Complex.re (zetaApproximant qz64 2 32))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz597 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz410)) (Complex.im (zetaApproximant qz64 2 32))))

noncomputable def ep1297 := nat_lit 2810175519754450754647501739848823407971

noncomputable def ep1298 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz597 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz410)) (Complex.re (zetaApproximant qz64 2 32))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz597 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz410)) (Complex.im (zetaApproximant qz64 2 32))) ep1297

noncomputable def ep1299 := nat_lit 615206721576029464773705704721612800000

noncomputable def ep1300 := nat_lit 4216694540922004442771304248903433070883705932131

noncomputable def ep1301 := nat_lit 26377803665442502866507950638566513

noncomputable def ep1302 := nat_lit 7690084019700368309671321309020160000000

noncomputable def ep1303 := nat_lit 2215838267618870884760155182905966567044785263

noncomputable def ep1304 := nat_lit 278738232265969279949932314594738454921216000000000

noncomputable def ep1305 := nat_lit 21610469629214763038032064738445887652935757180539134961249310986022263193600000

noncomputable def ep1306 := @Enclosure.Real.IsNear.mulLit_ff (Real.cos (@HSub.hSub Real Real Real qz597 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz410)) (Complex.re (zetaApproximant qz64 2 32)) 1048575 1048576 34983973

noncomputable def ep1307 := nat_lit 66999869340639695649989312634976597

noncomputable def ep1308 := nat_lit 14667671241188751811354296320000000

noncomputable def ep1309 := nat_lit 16645723142009041975142865534202079641

noncomputable def ep1310 := nat_lit 2792504589253720513604687704883200000000

noncomputable def ep1311 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz597 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz410)) Bool.false 1048575 1048576 34983973

noncomputable abbrev qz974 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 131768673) qz268)

noncomputable def ep1312 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz597 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz410) qz974 Bool.false 131768673 1048576 181

noncomputable def ep1313 := nat_lit 23180990219729120892415477463

noncomputable def ep1314 := nat_lit 184467440737095516160000000

noncomputable def ep1315 := nat_lit 1813383076869147968202770647367277

noncomputable def ep1316 := nat_lit 5276417323427273113600000000000000000

noncomputable def ep1317 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz597 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz410) Bool.false ep1313 ep1314 ep1315 ep1316

noncomputable def ep1318 := nat_lit 36495492963719099186277877463

noncomputable def ep1319 := nat_lit 544266471929122112202770647367277

noncomputable def ep1320 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz410 ep1318 ep1314 ep1319 ep1316 1892104641 26214400

noncomputable def ep1321 := nat_lit 607675750016067066722136292406067200

noncomputable def ep1322 := nat_lit 1646256678234580851496087577

noncomputable def ep1323 := nat_lit 16602069666338596454400000

noncomputable def ep1324 := nat_lit 27421703549347179512193913630705711

noncomputable def ep1325 := nat_lit 154335206710247738572800000000000000000

noncomputable def ep1326 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz20 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz69 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true ep1322 ep1323 ep1324 ep1325 Bool.false ep1318 ep1314

noncomputable def ep1327 := nat_lit 1371026949375982308136087577

noncomputable def ep1328 := nat_lit 26611055613025115684568463382104111

noncomputable def ep1329 := nat_lit 37634068624079923444837877463

noncomputable def ep1330 := nat_lit 6354888194562121248226909314821001

noncomputable def ep1331 := @Enclosure.Complex.IsNear.subLitP qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz69 (@Nat.cast Complex Complex.instNatCast j))) Bool.true ep1327 ep1323 ep1328 ep1325 Bool.false ep1329 ep1314 ep1330

noncomputable def ep1332 := nat_lit 68593425204554550476800000000000000000

noncomputable def ep1333 := nat_lit 3707040481326724427779160835446214120964096

noncomputable def ep1334 := nat_lit 5136284016003371680911972619776178587172864

noncomputable abbrev qz411 := (@HSub.hSub Complex Complex Complex qz595 qz621 qz550)

noncomputable abbrev qz412 := (Complex.log qz621)

noncomputable abbrev qz70 := (@HSub.hSub Complex Complex Complex qz595 (@HMul.hMul Complex Complex Complex qz253 qz411 qz412) qz380)

noncomputable def ep1335 := @Enclosure.Complex.IsNear.of_eq qz68 (@HAdd.hAdd Complex Complex Complex qz13 (@HAdd.hAdd Complex Complex Complex qz13 qz70 qz896) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz20 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz27 qz57 (@HSub.hSub Int Int Int qz28 qz29 (@HMul.hMul Int Int Int qz30 qz31 (@Nat.cast Int instNatCastInt k)))))) Bool.true ep1327

noncomputable def ep1336 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz13 qz70 qz896) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz20 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz27 qz57 (@HSub.hSub Int Int Int qz28 qz29 (@HMul.hMul Int Int Int qz30 qz31 (@Nat.cast Int instNatCastInt k))))) Bool.true 74383052393324189377 900719925474099200

noncomputable def ep1337 := nat_lit 1234911291664916361263257403650344336385638400

noncomputable def ep1338 := nat_lit 135591021945473614666646028267565728439625318400

noncomputable def ep1339 := @ep1336 5252300892701891767 30461600000000000000000 Bool.false 735045143062607631057 3602879701896396800 2822100010620855687 30461600000000000000000 Bool.false 1472337769150460776423 ep1323 1369053217510891 ep1323 Bool.true 242700725587265280522537 ep1314 225675446123955429 ep1314 Bool.true ep1337 ep1327 ep1323 ep1328 ep1325 Bool.false ep1338

noncomputable def ep1340 := @Enclosure.Complex.IsNear.addLitP qz70 qz896 Bool.true 75210757874766288577 900719925474099200 5194200001588610517 30461600000000000000000

noncomputable def ep1341 := nat_lit 9749535443297788150022144

noncomputable def ep1342 := @ep1340 Bool.false 735045143062607631057 3602879701896396800 2822100010620855687 30461600000000000000000 Bool.false 120447 131072 1 524288 Bool.false 0 1 0 1 Bool.true ep1341 74383052393324189377 900719925474099200 5252300892701891767 30461600000000000000000 Bool.false 735045143062607631057 735045143062607631057 3602879701896396800

noncomputable abbrev qz71 := (@HMul.hMul Complex Complex Complex qz253 qz411 qz412)

noncomputable def ep1343 := @Enclosure.Complex.IsNear.subLitP qz71 qz57 Bool.true 71382698191501366977 900719925474099200 5194200001588610517 30461600000000000000000 Bool.false 962215715466430190289

noncomputable def ep1344 := nat_lit 2940180572250430524228000

noncomputable def ep1345 := @ep1343 3602879701896396800 2822100010620855687 30461600000000000000000 Bool.false 17000 4000 0 1 Bool.false 252210 4000 0 1 Bool.true 300843031499065154308000 75210757874766288577 900719925474099200 5194200001588610517 30461600000000000000000 Bool.false ep1344 735045143062607631057 3602879701896396800 2822100010620855687 30461600000000000000000

noncomputable abbrev qz72 := qz411

noncomputable abbrev qz73 := qz412

noncomputable def ep1346 := @Enclosure.Complex.IsNear.mul qz72 qz73 Bool.true 71382698191501366977 900719925474099200 5194200001588610517 30461600000000000000000 Bool.false 962215715466430190289 3602879701896396800 2822100010620855687

noncomputable def ep1347 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re qz72) (Complex.re qz73)) (@HMul.hMul Real Real Real qz0 (Complex.im qz72) (Complex.im qz73)) 560189308089379635 36028797018963968 300000001256541 60923200000000000000 21346857723433964463 225179981368524800

noncomputable def ep1348 := nat_lit 642958185951892270073531616077021184

noncomputable def ep1349 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz72) (Complex.re qz73) 15000 4000 0 1 37345953872625309 9007199254740992 100000000418847 76154000000000000000

noncomputable def ep1350 := @Enclosure.Complex.IsNear.re_isNear qz72 Bool.false 15000 4000 0 1 Bool.false 252210 4000 0 1

noncomputable def ep1351 := @Enclosure.Complex.IsNear.of_eq qz72 (Complex.mk (Enclosure.sfrac Bool.false 15000 4000) qz383) Bool.false 15000 4000 0 1 Bool.false 252210 4000 0

noncomputable abbrev qz629 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 17000 4000) qz383))

noncomputable def ep1352 := @Enclosure.Complex.IsNear.of_eq qz73 qz629 Bool.false 37345953872625309 9007199254740992 100000000418847 76154000000000000000 Bool.false 846392201872803 562949953421312 200000000038077 76154000000000000000

noncomputable def ep1353 := nat_lit 89970573014285087454733610841386393075972831221847868398854677381808133253580038730268747699487367823131574551935000000000000000000000000

noncomputable def ep1354 := nat_lit 3319479390513273759681411241170736973725897886294724688193149059430257338345252873113771604829566677639454698032000000000000000000000000

noncomputable def ep1355 := nat_lit 8612355507267603924782258488500142356502964681904640552156835009776995307976521367802708525196611594103995000000000000000000000000

noncomputable def ep1356 := BSN.log_dyadic_bound 31130884100 96666884100 7 6 ep1353 1048576 380770 ep1354 ep1355 700290 127797768200 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 31130884100) (BSN.artanhQ 96666884100) 0 6 ep1354 ep1353 ep1355 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1357 := @Enclosure.Real.IsNear.mulLit_ff qz339 (Real.log (Enclosure.sfrac Bool.false 63898884100 16000000)) 1 2 0 1 37345953872625309 4503599627370496 100000000418847 38077000000000000000 37345953872625309 9007199254740992 100000000418847 76154000000000000000 qz340 (BSN.isNear_log_sfrac 63898884100 16000000 37345953872625309 4503599627370496 100000000418847 38077000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 63898884100) qz602)) Bool.false 313280567423535648079872 37778931862957161709568 1000000004188470 380770000000000000000 37345953872625309 4503599627370496 100000000418847 38077000000000000000 (BSN.log_rat_reduce_isNear 63898884100 16000000 11 127797768200 65536000000 700290 1048576 24973259072661432 36028797018963968 380770 1000000000000000 rfl rfl rfl rfl (ep1356 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1358 := BSN.arctan_dyadic_bound_f 17000 252210 1 0 1048576 380770 0 1 1 0 1 1 70571 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 17000) (BSN.arctanEvenQ 252210) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 17000) (BSN.arctanOddQ 252210) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz630 := (@Nat.cast Real Real.instNatCast 252210)

noncomputable def ep1359 := @Enclosure.Real.IsNear.subLit_ff_p qz348 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz603 qz630)) 884279719003555 562949953421312 1 2000000000000000 70571 1048576 1 380770 887506549470976278528 846392201872803 562949953421312 200000000038077 76154000000000000000 qz349 (ep1358 rfl) rfl rfl

noncomputable abbrev qz631 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 252210) (@Nat.cast Real Real.instNatCast 17000)))

noncomputable def ep1360 := @Enclosure.Complex.IsNear.re_isNear qz73 Bool.false 37345953872625309 9007199254740992 100000000418847 76154000000000000000 Bool.false 846392201872803 562949953421312 200000000038077 76154000000000000000 (ep1352 (@congrArg Complex Complex qz57 qz622 Complex.log (BSN.w_shift_mk qz61 Bool.false 126105 1000 4 (@Eq.refl Real qz61) rfl)) (@Enclosure.Complex.IsNear.of_parts qz629 Bool.false 37345953872625309 9007199254740992 100000000418847 76154000000000000000 Bool.false 846392201872803 562949953421312 200000000038077 76154000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz629) (@HMul.hMul Real Real Real qz0 qz339 (Real.log (Enclosure.sfrac Bool.false 63898884100 16000000))) Bool.false 37345953872625309 9007199254740992 100000000418847 76154000000000000000 (Enclosure.clog_re_eq 17000 252210 4000 63898884100 16000000 rfl rfl rfl) (ep1357 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz629) qz631 Bool.false 846392201872803 562949953421312 200000000038077 76154000000000000000 (Enclosure.clog_im_eq 17000 252210 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz631 (@HSub.hSub Real Real Real qz597 qz348 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz603 qz630))) Bool.false 846392201872803 562949953421312 200000000038077 76154000000000000000 (BSN.arctan_recip 252210 17000 rfl rfl) ep1359))))

noncomputable def ep1361 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz72) (Complex.im qz73) 252210 4000 0 1 846392201872803 562949953421312 200000000038077 76154000000000000000

noncomputable def ep1362 := @Enclosure.Complex.IsNear.im_isNear qz72 Bool.false 15000 4000 0 1 Bool.false 252210 4000 0 1

noncomputable def ep1363 := @Enclosure.Complex.IsNear.im_isNear qz73 Bool.false 37345953872625309 9007199254740992 100000000418847 76154000000000000000 Bool.false 846392201872803 562949953421312 200000000038077 76154000000000000000 (ep1352 (@congrArg Complex Complex qz57 qz622 Complex.log (BSN.w_shift_mk qz61 Bool.false 126105 1000 4 (@Eq.refl Real qz61) rfl)) (@Enclosure.Complex.IsNear.of_parts qz629 Bool.false 37345953872625309 9007199254740992 100000000418847 76154000000000000000 Bool.false 846392201872803 562949953421312 200000000038077 76154000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz629) (@HMul.hMul Real Real Real qz0 qz339 (Real.log (Enclosure.sfrac Bool.false 63898884100 16000000))) Bool.false 37345953872625309 9007199254740992 100000000418847 76154000000000000000 (Enclosure.clog_re_eq 17000 252210 4000 63898884100 16000000 rfl rfl rfl) (ep1357 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz629) qz631 Bool.false 846392201872803 562949953421312 200000000038077 76154000000000000000 (Enclosure.clog_im_eq 17000 252210 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz631 (@HSub.hSub Real Real Real qz597 qz348 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz603 qz630))) Bool.false 846392201872803 562949953421312 200000000038077 76154000000000000000 (BSN.arctan_recip 252210 17000 rfl rfl) ep1359))))

noncomputable abbrev qz413 := (@ep1351 1 (BSN.w_sub_half_mk qz61 Bool.false 126105 1000 4 (@Eq.refl Real qz61) rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 15000 4000) (Enclosure.sfrac Bool.false 252210 4000) Bool.false 15000 4000 0 1 Bool.false 252210 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 15000 4000) (Enclosure.Real.IsNear.const Bool.false 252210 4000)))

noncomputable def ep1364 := @ep1347 5044200000960340017 30461600000000000000000 ep1348 71382698191501366977 900719925474099200 5194200001588610517 30461600000000000000000 (@ep1349 560189308089379635 36028797018963968 300000001256541 60923200000000000000 (ep1350 qz413) ep1360 rfl) (@ep1361 21346857723433964463 225179981368524800 5044200000960340017 30461600000000000000000 (ep1362 qz413) ep1363 rfl) rfl

noncomputable def ep1365 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re qz72) (Complex.im qz73)) (@HMul.hMul Real Real Real qz0 (Complex.im qz72) (Complex.re qz73)) 12695883028092045 2251799813685248 600000000114231 60923200000000000000 941902302621482918289 3602879701896396800

noncomputable def ep1366 := nat_lit 2166717168812325104862264970992156672

noncomputable def ep1367 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz72) (Complex.im qz73) 15000 4000 0 1 846392201872803 562949953421312 200000000038077 76154000000000000000

noncomputable def ep1368 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz72) (Complex.re qz73) 252210 4000 0 1 37345953872625309 9007199254740992 100000000418847 76154000000000000000

noncomputable def ep1369 := @ep1365 2522100010563740187 30461600000000000000000 ep1366 962215715466430190289 3602879701896396800 2822100010620855687 30461600000000000000000 (@ep1367 12695883028092045 2251799813685248 600000000114231 60923200000000000000 (ep1350 qz413) ep1363 rfl) (@ep1368 941902302621482918289 3602879701896396800 2522100010563740187 30461600000000000000000 (ep1362 qz413) ep1360 rfl) rfl

noncomputable def ep1370 := ep1345 (@ep1346 30461600000000000000000 (ep1364 rfl) (ep1369 rfl)) qz63 rfl rfl rfl rfl rfl rfl

noncomputable def ep1371 := @ep1342 2822100010620855687 30461600000000000000000 (ep1370 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz24 (↑qz251) Bool.false 120447 131072 1 524288 Bool.false 0 1 0 1 (@ep547 131072 1 524288 (ep549 rfl) (ep551 rfl) rfl rfl) (@ep552 1 0 1 (ep554 rfl) (ep556 rfl) rfl rfl))

noncomputable abbrev qz74 := (@HPow.hPow Complex Int Complex qz599 qz380 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) qz347 (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) qz600 (@Nat.cast Int instNatCastInt 2))))

noncomputable def ep1372 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz20 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz27 qz57 (@HSub.hSub Int Int Int qz28 qz29 (@HMul.hMul Int Int Int qz30 qz31 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz13 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz20 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz27 qz57 (@HSub.hSub Int Int Int qz28 qz29 (@HMul.hMul Int Int Int qz30 qz31 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz35)) qz36) qz74)) Bool.false 1472337769150460776423 ep1323 1369053217510891 ep1323

noncomputable def ep1373 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz20 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz27 qz57 (@HSub.hSub Int Int Int qz28 qz29 (@HMul.hMul Int Int Int qz30 qz31 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz35)) qz36) qz74) Bool.false 18282497 206158430208 17 206158430208 Bool.true

noncomputable def ep1374 := nat_lit 303534843224007683427242537385984

noncomputable def ep1375 := nat_lit 1667826686580439638272899529519923200

noncomputable def ep1376 := @ep1373 9041232487 6871947673600 8407 6871947673600 Bool.false 36643446371176423 ep1323 32391910891 ep1323 Bool.true 1989042279373322537 ep1314 1758264755429 ep1314 Bool.false ep1374 1472337769150460776423 ep1323 1369053217510891 ep1323 Bool.true ep1375 242700725587265280522537 ep1314 225675446123955429

noncomputable abbrev qz75 := (@HPow.hPow Complex Int Complex qz599 qz380 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) qz347 (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) qz600 (@Nat.cast Int instNatCastInt 1))))

noncomputable def ep1377 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz20 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz27 qz57 (@HSub.hSub Int Int Int qz28 qz29 (@HMul.hMul Int Int Int qz30 qz31 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz13 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz20 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz27 qz57 (@HSub.hSub Int Int Int qz28 qz29 (@HMul.hMul Int Int Int qz30 qz31 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz38)) qz39) qz75)) Bool.false 18282497 206158430208 17 206158430208

noncomputable def ep1378 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz20 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz27 qz57 (@HSub.hSub Int Int Int qz28 qz29 (@HMul.hMul Int Int Int qz30 qz31 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz38)) qz39) qz75) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1379 := @ep1378 0 1 0 1 Bool.false 18282497 206158430208 17 206158430208 Bool.true 9041232487 6871947673600 8407 6871947673600 Bool.false 18282497 18282497 206158430208 17 206158430208 Bool.true 9041232487 9041232487 6871947673600 8407

noncomputable def ep1380 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz20 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz27 qz57 (@HSub.hSub Int Int Int qz28 qz29 (@HMul.hMul Int Int Int qz30 qz31 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz262 qz262) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1381 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz38)) qz39) qz75 Bool.false 18282497 206158430208 17 206158430208 Bool.true 9041232487 6871947673600 8407 6871947673600

noncomputable def ep1382 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz38)) qz39)) (Complex.re qz75)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz38)) qz39)) (Complex.im qz75)) 18282497 206158430208 17 206158430208 0 1 0

noncomputable def ep1383 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz38)) qz39)) (Complex.re qz75) 1 12 0 1 18282497 17179869184 17 17179869184 18282497

noncomputable def ep1384 := @Enclosure.Complex.IsNear.re_isNear qz75 Bool.false 18282497 17179869184 17 17179869184 Bool.true 27123697461 1717986918400 25221 1717986918400

noncomputable def ep1385 := @Enclosure.Complex.IsNear.of_eq qz75 (@Inv.inv Complex Complex.instInv qz58) Bool.false 18282497 17179869184 17 17179869184 Bool.true 27123697461 1717986918400 25221

noncomputable def ep1386 := @Enclosure.Complex.IsNear.of_parts (@Inv.inv Complex Complex.instInv qz58) Bool.false 18282497 17179869184 17 17179869184 Bool.true 27123697461 1717986918400 25221

noncomputable def ep1387 := @Enclosure.Real.IsNear.mulLit_ff qz59 (@Inv.inv Real Real.instInv (@DFunLike.coe qz352 Complex (fun (x : Complex) => Real) qz353 Complex.normSq qz58)) 17000 4000 0 1 1075441 4294967296 1 4294967296

noncomputable def ep1388 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz352 Complex (fun (x : Complex) => Real) qz353 Complex.normSq qz58)) Bool.false 1075441 4294967296 1 4294967296 1075441 4294967296 1

noncomputable def ep1389 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz352 Complex (fun (x : Complex) => Real) qz353 Complex.normSq qz58) (@HAdd.hAdd Real Real Real qz607 (@HMul.hMul Real Real Real qz0 qz59 qz59) (@HMul.hMul Real Real Real qz0 qz60 qz60)) Bool.false 638988841 160000 0 1

noncomputable def ep1390 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz59 qz59) (@HMul.hMul Real Real Real qz0 qz60 qz60) 289 16 0 1 636098841 160000

noncomputable def ep1391 := @Enclosure.Real.IsNear.mulLit_ff qz59 qz59 17000 4000 0 1 17000 4000 0 1

noncomputable def ep1392 := @Enclosure.Real.IsNear.mulLit_ff qz60 qz60 252210 4000 0 1 252210 4000 0 1

noncomputable def ep1393 := @ep1390 0 1 10223821456 638988841 160000 0 1 (@ep1391 289 16 0 1 (ep925 qz62) (ep925 qz62) rfl) (@ep1392 636098841 160000 0 1 (ep930 qz62) (ep930 qz62) rfl)

noncomputable def ep1394 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz352 Complex (fun (x : Complex) => Real) qz353 Complex.normSq qz58) 638988841 160000 0 1 537720 537721 2147483648 (ep1389 (Enclosure.Complex.normSq_eq_mul_add_mul qz58) (ep1393 rfl rfl)) rfl

noncomputable def ep1395 := @Enclosure.Real.IsNear.of_eq (Complex.re (@Inv.inv Complex Complex.instInv qz58)) (@HMul.hMul Real Real Real qz0 qz59 (@Inv.inv Real Real.instInv (@DFunLike.coe qz352 Complex (fun (x : Complex) => Real) qz353 Complex.normSq qz58))) Bool.false 18282497 17179869184 17 17179869184 (Enclosure.Complex.inv_re_eq_mul qz58) (@ep1387 18282497 17179869184 17 17179869184 (ep925 qz62) (@ep1388 4294967296 (ep1394 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep1396 := @Enclosure.Real.IsNear.of_eq (Complex.im (@Inv.inv Complex Complex.instInv qz58)) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz60) (@Inv.inv Real Real.instInv (@DFunLike.coe qz352 Complex (fun (x : Complex) => Real) qz353 Complex.normSq qz58))) Bool.true 27123697461 1717986918400 25221 1717986918400 (Enclosure.Complex.inv_im_eq_mul qz58)

noncomputable def ep1397 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz60) (@Inv.inv Real Real.instInv (@DFunLike.coe qz352 Complex (fun (x : Complex) => Real) qz353 Complex.normSq qz58)) 252210 4000 0 1 1075441 4294967296 1

noncomputable def ep1398 := @ep1397 4294967296 27123697461 1717986918400 25221 1717986918400 (@Enclosure.Real.IsNear.neg qz60 Bool.false 252210 4000 0 1 (ep930 qz62)) (@ep1388 4294967296 (ep1394 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep1399 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz38)) qz39)) (Complex.im qz75) 0 1 0 1 27123697461 1717986918400 25221 1717986918400 0

noncomputable def ep1400 := @Enclosure.Complex.IsNear.im_isNear qz75 Bool.false 18282497 17179869184 17 17179869184 Bool.true 27123697461 1717986918400 25221 1717986918400

noncomputable abbrev qz632 := (@ep1385 1717986918400 (BSN.zpow_one_sub_two_mul qz57 1 1 rfl rfl) (@ep1386 1717986918400 ep1395 (ep1396 ep1398)))

noncomputable def ep1401 := @ep1382 1 18282497 18282497 206158430208 17 206158430208 (@ep1383 206158430208 17 206158430208 ep571 (ep1384 qz632) rfl) (@ep1399 1 0 1 ep588 (ep1400 qz632) rfl) rfl

noncomputable def ep1402 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz38)) qz39)) (Complex.im qz75)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz38)) qz39)) (Complex.re qz75)) 9041232487 6871947673600 8407 6871947673600 0 1 0

noncomputable def ep1403 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz38)) qz39)) (Complex.im qz75) 1 12 0 1 27123697461 1717986918400 25221 1717986918400 9041232487

noncomputable def ep1404 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz38)) qz39)) (Complex.re qz75) 0 1 0 1 18282497 17179869184 17 17179869184 0

noncomputable def ep1405 := @ep1402 1 9041232487 9041232487 6871947673600 8407 6871947673600 (@ep1403 6871947673600 8407 6871947673600 ep571 (ep1400 qz632) rfl) (@ep1404 1 0 1 ep588 (ep1384 qz632) rfl) rfl

noncomputable def ep1406 := @ep1379 6871947673600 (@ep1380 0 1 0 1 (BSN.stirling_sum_base qz57) qz354) (ep1381 (ep1401 rfl) (ep1405 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep1407 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz35)) qz36) qz74 Bool.false 36643446371176423 ep1323 32391910891 ep1323 Bool.true 1989042279373322537 ep1314 1758264755429 ep1314

noncomputable def ep1408 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz35)) qz36)) (Complex.re qz74)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz35)) qz36)) (Complex.im qz74)) 36643446371176423 ep1323 32391910891 ep1323 0 1 0

noncomputable def ep1409 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz35)) qz36)) (Complex.re qz74) 1 360 0 1 36643446371176423 46116860184273879040000 32391910891 46116860184273879040000 36643446371176423

noncomputable def ep1410 := nat_lit 4611686018427387904000000

noncomputable def ep1411 := @Enclosure.Complex.IsNear.re_isNear qz74 Bool.true 36643446371176423 46116860184273879040000 32391910891 46116860184273879040000 Bool.false 17901380514359902833 ep1410 15824382798861 ep1410

noncomputable def ep1412 := @Enclosure.Complex.IsNear.of_eq qz74 (@Inv.inv Complex Complex.instInv qz55) Bool.true 36643446371176423 46116860184273879040000 32391910891 46116860184273879040000 Bool.false 17901380514359902833 ep1410 15824382798861

noncomputable def ep1413 := @Enclosure.Complex.IsNear.of_parts (@Inv.inv Complex Complex.instInv qz55) Bool.true 36643446371176423 46116860184273879040000 32391910891 46116860184273879040000 Bool.false 17901380514359902833 ep1410 15824382798861

noncomputable abbrev qz76 := (Complex.re qz379)

noncomputable def ep1414 := @Enclosure.Real.IsNear.mulLit_tf qz76 (@Inv.inv Real Real.instInv (@DFunLike.coe qz352 Complex (fun (x : Complex) => Real) qz353 Complex.normSq qz55)) 32391910891 640000 0 1 1131253 72057594037927936 1 72057594037927936

noncomputable def ep1415 := @Enclosure.Complex.IsNear.re_isNear qz55 Bool.true 32391910891 640000 0 1 Bool.true 15824382798861 64000000 0 1

noncomputable def ep1416 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz352 Complex (fun (x : Complex) => Real) qz353 Complex.normSq qz55)) Bool.false 1131253 72057594037927936 1 72057594037927936 1131253 72057594037927936 1

noncomputable def ep1417 := nat_lit 260903449876592740121707321

noncomputable abbrev qz77 := (Complex.im qz379)

noncomputable def ep1418 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz352 Complex (fun (x : Complex) => Real) qz353 Complex.normSq qz55) (@HAdd.hAdd Real Real Real qz607 (@HMul.hMul Real Real Real qz0 qz76 qz76) (@HMul.hMul Real Real Real qz0 qz77 qz77)) Bool.false ep1417 4096000000000000 0 1

noncomputable def ep1419 := nat_lit 250411090964887895982897321

noncomputable def ep1420 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz76 qz76) (@HMul.hMul Real Real Real qz0 qz77 qz77) 1049235891170484413881 409600000000 0 1 ep1419 4096000000000000

noncomputable def ep1421 := nat_lit 106866053069452386353851318681600000000

noncomputable def ep1422 := @Enclosure.Real.IsNear.mulLit_tt qz76 qz76 32391910891 640000 0 1 32391910891 640000 0 1

noncomputable def ep1423 := @Enclosure.Real.IsNear.mulLit_tt qz77 qz77 15824382798861 64000000 0 1 15824382798861 64000000 0 1

noncomputable def ep1424 := @Enclosure.Complex.IsNear.im_isNear qz55 Bool.true 32391910891 640000 0 1 Bool.true 15824382798861 64000000 0 1

noncomputable def ep1425 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz352 Complex (fun (x : Complex) => Real) qz353 Complex.normSq qz55) ep1417 4096000000000000 0 1 565626 565627 36028797018963968 (ep1418 (Enclosure.Complex.normSq_eq_mul_add_mul qz55) (@ep1420 0 1 ep1421 ep1417 4096000000000000 0 1 (@ep1422 1049235891170484413881 409600000000 0 1 (ep1415 EMRow41.d16) (ep1415 EMRow41.d16) rfl) (@ep1423 ep1419 4096000000000000 0 1 (ep1424 EMRow41.d16) (ep1424 EMRow41.d16) rfl) rfl rfl)) rfl

noncomputable def ep1426 := @Enclosure.Real.IsNear.of_eq (Complex.re (@Inv.inv Complex Complex.instInv qz55)) (@HMul.hMul Real Real Real qz0 qz76 (@Inv.inv Real Real.instInv (@DFunLike.coe qz352 Complex (fun (x : Complex) => Real) qz353 Complex.normSq qz55))) Bool.true 36643446371176423 46116860184273879040000 32391910891 46116860184273879040000 (Enclosure.Complex.inv_re_eq_mul qz55) (@ep1414 36643446371176423 46116860184273879040000 32391910891 46116860184273879040000 (ep1415 EMRow41.d16) (@ep1416 72057594037927936 (ep1425 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep1427 := @Enclosure.Real.IsNear.of_eq (Complex.im (@Inv.inv Complex Complex.instInv qz55)) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz77) (@Inv.inv Real Real.instInv (@DFunLike.coe qz352 Complex (fun (x : Complex) => Real) qz353 Complex.normSq qz55))) Bool.false 17901380514359902833 ep1410 15824382798861 ep1410 (Enclosure.Complex.inv_im_eq_mul qz55)

noncomputable def ep1428 := @Enclosure.Real.IsNear.mulLit_ff (@Neg.neg Real Real.instNeg qz77) (@Inv.inv Real Real.instInv (@DFunLike.coe qz352 Complex (fun (x : Complex) => Real) qz353 Complex.normSq qz55)) 15824382798861 64000000 0 1 1131253 72057594037927936 1

noncomputable def ep1429 := @ep1428 72057594037927936 17901380514359902833 ep1410 15824382798861 ep1410 (@Enclosure.Real.IsNear.neg qz77 Bool.true 15824382798861 64000000 0 1 (ep1424 EMRow41.d16)) (@ep1416 72057594037927936 (ep1425 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep1430 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz35)) qz36)) (Complex.im qz74) 0 1 0 1 17901380514359902833 ep1410 15824382798861 ep1410 0

noncomputable def ep1431 := @Enclosure.Complex.IsNear.im_isNear qz74 Bool.true 36643446371176423 46116860184273879040000 32391910891 46116860184273879040000 Bool.false 17901380514359902833 ep1410 15824382798861 ep1410

noncomputable abbrev qz975 := (@ep1412 ep1410 (BSN.zpow_one_sub_two_mul qz57 2 3 rfl rfl) (@ep1413 ep1410 ep1426 (ep1427 ep1429)))

noncomputable def ep1432 := @ep1408 1 36643446371176423 36643446371176423 ep1323 32391910891 ep1323 (@ep1409 ep1323 32391910891 ep1323 ep600 (ep1411 qz975) rfl) (@ep1430 1 0 1 ep622 (ep1431 qz975) rfl) rfl

noncomputable def ep1433 := @Enclosure.Real.IsNear.addLit_tt (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz35)) qz36)) (Complex.im qz74)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz35)) qz36)) (Complex.re qz74)) 1989042279373322537 ep1314 1758264755429 ep1314 0 1 0

noncomputable def ep1434 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz35)) qz36)) (Complex.im qz74) 1 360 0 1 17901380514359902833 ep1410 15824382798861 ep1410 1989042279373322537

noncomputable def ep1435 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 (@Rat.cast Complex Complex.instRatCast (bernoulli qz35)) qz36)) (Complex.re qz74) 0 1 0 1 36643446371176423 46116860184273879040000 32391910891 46116860184273879040000 0

noncomputable def ep1436 := @ep1433 1 1989042279373322537 1989042279373322537 ep1314 1758264755429 ep1314 (@ep1434 ep1314 1758264755429 ep1314 ep600 (ep1431 qz975) rfl) (@ep1435 1 0 1 ep622 (ep1411 qz975) rfl) rfl

noncomputable def ep1437 := @ep1376 ep1314 (@ep1377 Bool.true 9041232487 6871947673600 8407 6871947673600 (BSN.stirling_sum_succ qz57 0 1 rfl) (ep1406 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1407 (ep1432 rfl) (ep1436 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep1438 := @ep1339 ep1329 ep1314 ep1330 ep1332 (ep1371 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep1372 Bool.true 242700725587265280522537 ep1314 225675446123955429 ep1314 (BSN.stirling_sum_succ qz57 1 2 rfl) (ep1437 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep1439 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz69 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz61 4) Bool.false 37330421123399325 2251799813685248 100000000418847 19038500000000000000 Bool.false 868664291657123 140737488355328

noncomputable def ep1440 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz61 4) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.logSumC qz61 3) (Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz69 qz552))) Bool.false 37330421123399325 2251799813685248 100000000418847 19038500000000000000 Bool.false 868664291657123 140737488355328 200000000038077 19038500000000000000

noncomputable def ep1441 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz61 3) (Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz69 qz552)) Bool.false 111984196001512407 9007199254740992 300000001256541 76154000000000000000 Bool.false 2619368476872937 562949953421312 600000000114231 76154000000000000000 Bool.false

noncomputable def ep1442 := nat_lit 1344970165287399141972693850521600

noncomputable def ep1443 := nat_lit 1956058090108537500047459221504

noncomputable def ep1444 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz61 3) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.logSumC qz61 2) (Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz69 qz553))) Bool.false 111984196001512407 9007199254740992 300000001256541 76154000000000000000 Bool.false 2619368476872937 562949953421312 600000000114231 76154000000000000000

noncomputable def ep1445 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz61 2) (Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz69 qz553)) Bool.false 37326461163552413 4503599627370496 100000000418847 38077000000000000000 Bool.false 877584401860003 281474976710656 200000000038077 38077000000000000000 Bool.false

noncomputable def ep1446 := nat_lit 504331983383795864282848529743872

noncomputable def ep1447 := nat_lit 737286681024436421425125916672

noncomputable def ep1448 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz61 2) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.logSumC qz61 1) (Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz69 qz590))) Bool.false 37326461163552413 4503599627370496 100000000418847 38077000000000000000 Bool.false 877584401860003 281474976710656 200000000038077 38077000000000000000

noncomputable def ep1449 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz61 1) (Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz69 qz590)) Bool.false 37325612907511453 9007199254740992 100000000418847 76154000000000000000 Bool.false 882047946622371 562949953421312 200000000038077 76154000000000000000 Bool.false

noncomputable def ep1450 := nat_lit 672413746348935750948005863227392

noncomputable def ep1451 := nat_lit 988072196300717281892601167872

noncomputable abbrev qz976 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz69 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep1452 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz61 1) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.logSumC qz61 0) qz976) Bool.false 37325612907511453 9007199254740992 100000000418847 76154000000000000000 Bool.false 882047946622371 562949953421312 200000000038077 76154000000000000000

noncomputable def ep1453 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz61 0) qz976 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz977 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz383))

noncomputable def ep1454 := @Enclosure.Complex.IsNear.of_eq qz976 qz977 Bool.false 37325612907511453 9007199254740992 100000000418847 76154000000000000000 Bool.false 882047946622371 562949953421312 200000000038077 76154000000000000000

noncomputable def ep1455 := nat_lit 86806164880873954488569946036875020913097829914134132804302732210538205940935177274184739223059746871901564951935000000000000000000000000

noncomputable def ep1456 := nat_lit 3159860731180558998594250880393764200109442808239747303714160701475522720406929467615978909242884080735129578032000000000000000000000000

noncomputable def ep1457 := nat_lit 7703432410921730887628644086776547617171058961004132829452507833404614019275656496093505252794992054903995000000000000000000000000

noncomputable def ep1458 := BSN.log_dyadic_bound 30842884100 96378884100 7 6 ep1455 1048576 380770 ep1456 ep1457 695554 127221768200 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 30842884100) (BSN.artanhQ 96378884100) 0 6 ep1456 ep1455 ep1457 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1459 := @Enclosure.Real.IsNear.mulLit_ff qz339 (Real.log (Enclosure.sfrac Bool.false 63610884100 16000000)) 1 2 0 1 37325612907511453 4503599627370496 100000000418847 38077000000000000000 37325612907511453 9007199254740992 100000000418847 76154000000000000000 qz340 (BSN.isNear_log_sfrac 63610884100 16000000 37325612907511453 4503599627370496 100000000418847 38077000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 63610884100) qz602)) Bool.false 313109935040853834727424 37778931862957161709568 1000000004188470 380770000000000000000 37325612907511453 4503599627370496 100000000418847 38077000000000000000 (BSN.log_rat_reduce_isNear 63610884100 16000000 11 127221768200 65536000000 695554 1048576 24973259072661432 36028797018963968 380770 1000000000000000 rfl rfl rfl rfl (ep1458 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1460 := BSN.arctan_dyadic_bound_f 1000 252210 1 0 1048576 380770 0 1 1 0 1 1 4157 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 252210) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 252210) 0 0 rfl) rfl rfl rfl

noncomputable def ep1461 := @Enclosure.Real.IsNear.subLit_ff_p qz348 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz900 qz630)) 884279719003555 562949953421312 1 2000000000000000 4157 1048576 1 380770 924894307677499293696 882047946622371 562949953421312 200000000038077 76154000000000000000 qz349 (ep1460 rfl) rfl rfl

noncomputable abbrev qz978 := (@HAdd.hAdd Complex Complex Complex qz13 qz69 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz979 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz383)

noncomputable def ep1462 := @ep1453 37325612907511453 9007199254740992 100000000418847 76154000000000000000 Bool.false 882047946622371 562949953421312 200000000038077 76154000000000000000 Bool.false 37325612907511453 37325612907511453 9007199254740992 100000000418847 76154000000000000000 Bool.false 882047946622371 882047946622371 562949953421312 200000000038077 76154000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz61 0) (Complex.mk qz262 qz262) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz61) qz354) (ep1454 (@congrArg Complex Complex qz978 qz979 Complex.log (BSN.w_shift_mk qz61 Bool.false 126105 1000 0 (@Eq.refl Real qz61) rfl)) (@Enclosure.Complex.IsNear.of_parts qz977 Bool.false 37325612907511453 9007199254740992 100000000418847 76154000000000000000 Bool.false 882047946622371 562949953421312 200000000038077 76154000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz977) (@HMul.hMul Real Real Real qz0 qz339 (Real.log (Enclosure.sfrac Bool.false 63610884100 16000000))) Bool.false 37325612907511453 9007199254740992 100000000418847 76154000000000000000 (Enclosure.clog_re_eq 1000 252210 4000 63610884100 16000000 rfl rfl rfl) (ep1459 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz977) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz630 qz900)) Bool.false 882047946622371 562949953421312 200000000038077 76154000000000000000 (Enclosure.clog_im_eq 1000 252210 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz630 qz900)) (@HSub.hSub Real Real Real qz597 qz348 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz900 qz630))) Bool.false 882047946622371 562949953421312 200000000038077 76154000000000000000 (BSN.arctan_recip 252210 1000 rfl rfl) ep1461)))) rfl rfl

noncomputable abbrev qz980 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz383))

noncomputable def ep1463 := @Enclosure.Complex.IsNear.of_eq (Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz69 qz590)) qz980 Bool.false 37327309419593373 9007199254740992 100000000418847 76154000000000000000 Bool.false 873120857097635 562949953421312 200000000038077 76154000000000000000

noncomputable def ep1464 := nat_lit 87065915180560400899433459180947997032327860604791834849982515870973302491362213870478701755403200992728065751935000000000000000000000000

noncomputable def ep1465 := nat_lit 3172895538474371735115915320549211646155698345553405038152146309491441636343634971911976039885730164996623338032000000000000000000000000

noncomputable def ep1466 := nat_lit 7775673003424676706858484593598113244170145323728169042796521782238442286764061208765357218980375016503995000000000000000000000000

noncomputable def ep1467 := BSN.log_dyadic_bound 30866884100 96402884100 7 6 ep1464 1048576 380770 ep1465 ep1466 695949 127269768200 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 30866884100) (BSN.artanhQ 96402884100) 0 6 ep1465 ep1464 ep1466 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1468 := @Enclosure.Real.IsNear.mulLit_ff qz339 (Real.log (Enclosure.sfrac Bool.false 63634884100 16000000)) 1 2 0 1 37327309419593373 4503599627370496 100000000418847 38077000000000000000 37327309419593373 9007199254740992 100000000418847 76154000000000000000 qz340 (BSN.isNear_log_sfrac 63634884100 16000000 37327309419593373 4503599627370496 100000000418847 38077000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 63634884100) qz602)) Bool.false 313124166415676325494784 37778931862957161709568 1000000004188470 380770000000000000000 37327309419593373 4503599627370496 100000000418847 38077000000000000000 (BSN.log_rat_reduce_isNear 63634884100 16000000 11 127269768200 65536000000 695949 1048576 24973259072661432 36028797018963968 380770 1000000000000000 rfl rfl rfl rfl (ep1467 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1469 := BSN.arctan_dyadic_bound_f 5000 252210 1 0 1048576 380770 0 1 1 0 1 1 20785 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 252210) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 252210) 0 0 rfl) rfl rfl rfl

noncomputable def ep1470 := @Enclosure.Real.IsNear.subLit_ff_p qz348 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz904 qz630)) 884279719003555 562949953421312 1 2000000000000000 20785 1048576 1 380770 915533575852009717760 873120857097635 562949953421312 200000000038077 76154000000000000000 qz349 (ep1469 rfl) rfl rfl

noncomputable abbrev qz981 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz383)

noncomputable def ep1471 := @ep1449 37327309419593373 9007199254740992 100000000418847 76154000000000000000 Bool.false 873120857097635 562949953421312 200000000038077 76154000000000000000 Bool.false ep1450 37326461163552413 4503599627370496 100000000418847 38077000000000000000 Bool.false ep1451 877584401860003 281474976710656 200000000038077 38077000000000000000 (ep1452 (BSN.log_sum_c_succ qz61 0 1 rfl) (ep1462 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1463 (@congrArg Complex Complex (@HAdd.hAdd Complex Complex Complex qz13 qz69 qz590) qz981 Complex.log (BSN.w_shift_mk qz61 Bool.false 126105 1000 1 (@Eq.refl Real qz61) rfl)) (@Enclosure.Complex.IsNear.of_parts qz980 Bool.false 37327309419593373 9007199254740992 100000000418847 76154000000000000000 Bool.false 873120857097635 562949953421312 200000000038077 76154000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz980) (@HMul.hMul Real Real Real qz0 qz339 (Real.log (Enclosure.sfrac Bool.false 63634884100 16000000))) Bool.false 37327309419593373 9007199254740992 100000000418847 76154000000000000000 (Enclosure.clog_re_eq 5000 252210 4000 63634884100 16000000 rfl rfl rfl) (ep1468 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz980) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz630 qz904)) Bool.false 873120857097635 562949953421312 200000000038077 76154000000000000000 (Enclosure.clog_im_eq 5000 252210 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz630 qz904)) (@HSub.hSub Real Real Real qz597 qz348 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz904 qz630))) Bool.false 873120857097635 562949953421312 200000000038077 76154000000000000000 (BSN.arctan_recip 252210 5000 rfl rfl) ep1470)))) rfl rfl

noncomputable abbrev qz982 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 9000 4000) qz383))

noncomputable def ep1472 := @Enclosure.Complex.IsNear.of_eq (Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz69 qz553)) qz982 Bool.false 37331273674407581 9007199254740992 100000000418847 76154000000000000000 Bool.false 864199673152931 562949953421312 200000000038077 76154000000000000000

noncomputable def ep1473 := nat_lit 87674772349118177994076332398344099090596295246919851298228248114731071284953159096127010762181326551669900951935000000000000000000000000

noncomputable def ep1474 := nat_lit 3203496921167671947147720799502670000732509004207276125957695424258757835618647133900309938235774774236108778032000000000000000000000000

noncomputable def ep1475 := nat_lit 7946655864602808443717027304479830310368778752064250608146774235554482664885869143011920858382961926903995000000000000000000000000

noncomputable def ep1476 := BSN.log_dyadic_bound 30922884100 96458884100 7 6 ep1473 1048576 380770 ep1474 ep1475 696872 127381768200 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 30922884100) (BSN.artanhQ 96458884100) 0 6 ep1474 ep1473 ep1475 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1477 := @Enclosure.Real.IsNear.mulLit_ff qz339 (Real.log (Enclosure.sfrac Bool.false 63690884100 16000000)) 1 2 0 1 37331273674407581 4503599627370496 100000000418847 38077000000000000000 37331273674407581 9007199254740992 100000000418847 76154000000000000000 qz340 (BSN.isNear_log_sfrac 63690884100 16000000 37331273674407581 4503599627370496 100000000418847 38077000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 63690884100) qz602)) Bool.false 313157420995324829237248 37778931862957161709568 1000000004188470 380770000000000000000 37331273674407581 4503599627370496 100000000418847 38077000000000000000 (BSN.log_rat_reduce_isNear 63690884100 16000000 11 127381768200 65536000000 696872 1048576 24973259072661432 36028797018963968 380770 1000000000000000 rfl rfl rfl rfl (ep1476 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1478 := BSN.arctan_dyadic_bound_f 9000 252210 1 0 1048576 380770 0 1 1 0 1 1 37402 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 252210) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 252210) 0 0 rfl) rfl rfl rfl

noncomputable def ep1479 := @Enclosure.Real.IsNear.subLit_ff_p qz348 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz907 qz630)) 884279719003555 562949953421312 1 2000000000000000 37402 1048576 1 380770 906179036476007776256 864199673152931 562949953421312 200000000038077 76154000000000000000 qz349 (ep1478 rfl) rfl rfl

noncomputable abbrev qz983 := (Complex.mk (Enclosure.sfrac Bool.false 9000 4000) qz383)

noncomputable def ep1480 := @ep1445 37331273674407581 9007199254740992 100000000418847 76154000000000000000 Bool.false 864199673152931 562949953421312 200000000038077 76154000000000000000 Bool.false ep1446 111984196001512407 9007199254740992 300000001256541 76154000000000000000 Bool.false ep1447 2619368476872937 562949953421312 600000000114231 76154000000000000000 (ep1448 (BSN.log_sum_c_succ qz61 1 2 rfl) (ep1471 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1472 (@congrArg Complex Complex (@HAdd.hAdd Complex Complex Complex qz13 qz69 qz553) qz983 Complex.log (BSN.w_shift_mk qz61 Bool.false 126105 1000 2 (@Eq.refl Real qz61) rfl)) (@Enclosure.Complex.IsNear.of_parts qz982 Bool.false 37331273674407581 9007199254740992 100000000418847 76154000000000000000 Bool.false 864199673152931 562949953421312 200000000038077 76154000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz982) (@HMul.hMul Real Real Real qz0 qz339 (Real.log (Enclosure.sfrac Bool.false 63690884100 16000000))) Bool.false 37331273674407581 9007199254740992 100000000418847 76154000000000000000 (Enclosure.clog_re_eq 9000 252210 4000 63690884100 16000000 rfl rfl rfl) (ep1477 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz982) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz630 qz907)) Bool.false 864199673152931 562949953421312 200000000038077 76154000000000000000 (Enclosure.clog_im_eq 9000 252210 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz630 qz907)) (@HSub.hSub Real Real Real qz597 qz348 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz907 qz630))) Bool.false 864199673152931 562949953421312 200000000038077 76154000000000000000 (BSN.arctan_recip 252210 9000 rfl rfl) ep1479)))) rfl rfl

noncomputable abbrev qz984 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 13000 4000) qz383))

noncomputable def ep1481 := @Enclosure.Complex.IsNear.of_eq (Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz69 qz552)) qz984 Bool.false 37337488492084893 9007199254740992 100000000418847 76154000000000000000 Bool.false 855288689755555 562949953421312 200000000038077 76154000000000000000

noncomputable def ep1482 := nat_lit 88639437615366382369813167110081762578060953305859921041349668575360665766270944120957738876161885013559070551935000000000000000000000000

noncomputable def ep1483 := nat_lit 3252117322201942213208335122712750375924822966387560923036872000730500842457307918977345699147481938763985898032000000000000000000000000

noncomputable def ep1484 := nat_lit 8222317978095509378772380836038796055444341460373583905608025440194566133714155498742852941330816786103995000000000000000000000000

noncomputable def ep1485 := BSN.log_dyadic_bound 31010884100 96546884100 7 6 ep1482 1048576 380770 ep1483 ep1484 698319 127557768200 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 31010884100) (BSN.artanhQ 96546884100) 0 6 ep1483 ep1482 ep1484 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1486 := @Enclosure.Real.IsNear.mulLit_ff qz339 (Real.log (Enclosure.sfrac Bool.false 63778884100 16000000)) 1 2 0 1 37337488492084893 4503599627370496 100000000418847 38077000000000000000 37337488492084893 9007199254740992 100000000418847 76154000000000000000 qz340 (BSN.isNear_log_sfrac 63778884100 16000000 37337488492084893 4503599627370496 100000000418847 38077000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 63778884100) qz602)) Bool.false 313209554664611270098944 37778931862957161709568 1000000004188470 380770000000000000000 37337488492084893 4503599627370496 100000000418847 38077000000000000000 (BSN.log_rat_reduce_isNear 63778884100 16000000 11 127557768200 65536000000 698319 1048576 24973259072661432 36028797018963968 380770 1000000000000000 rfl rfl rfl rfl (ep1485 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1487 := BSN.arctan_dyadic_bound_f 13000 252210 1 0 1048576 380770 0 1 1 0 1 1 54000 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 13000) (BSN.arctanEvenQ 252210) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 13000) (BSN.arctanOddQ 252210) 0 0 rfl) rfl rfl rfl

noncomputable def ep1488 := @Enclosure.Real.IsNear.subLit_ff_p qz348 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz910 qz630)) 884279719003555 562949953421312 1 2000000000000000 54000 1048576 1 380770 896835193149120839680 855288689755555 562949953421312 200000000038077 76154000000000000000 qz349 (ep1487 rfl) rfl rfl

noncomputable abbrev qz985 := (Complex.mk (Enclosure.sfrac Bool.false 13000 4000) qz383)

noncomputable def ep1489 := @ep1441 37337488492084893 9007199254740992 100000000418847 76154000000000000000 Bool.false 855288689755555 562949953421312 200000000038077 76154000000000000000 Bool.false ep1442 37330421123399325 2251799813685248 100000000418847 19038500000000000000 Bool.false ep1443 868664291657123 140737488355328 200000000038077 19038500000000000000 (ep1444 (BSN.log_sum_c_succ qz61 2 3 rfl) (ep1480 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1481 (@congrArg Complex Complex (@HAdd.hAdd Complex Complex Complex qz13 qz69 qz552) qz985 Complex.log (BSN.w_shift_mk qz61 Bool.false 126105 1000 3 (@Eq.refl Real qz61) rfl)) (@Enclosure.Complex.IsNear.of_parts qz984 Bool.false 37337488492084893 9007199254740992 100000000418847 76154000000000000000 Bool.false 855288689755555 562949953421312 200000000038077 76154000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz984) (@HMul.hMul Real Real Real qz0 qz339 (Real.log (Enclosure.sfrac Bool.false 63778884100 16000000))) Bool.false 37337488492084893 9007199254740992 100000000418847 76154000000000000000 (Enclosure.clog_re_eq 13000 252210 4000 63778884100 16000000 rfl rfl rfl) (ep1486 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz984) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz630 qz910)) Bool.false 855288689755555 562949953421312 200000000038077 76154000000000000000 (Enclosure.clog_im_eq 13000 252210 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz630 qz910)) (@HSub.hSub Real Real Real qz597 qz348 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz910 qz630))) Bool.false 855288689755555 562949953421312 200000000038077 76154000000000000000 (BSN.arctan_recip 252210 13000 rfl rfl) ep1488)))) rfl rfl

noncomputable def ep1490 := @ep1331 ep1332 Bool.false 37330421123399325 2251799813685248 100000000418847 19038500000000000000 Bool.false 868664291657123 140737488355328 200000000038077 19038500000000000000 Bool.true ep1333 ep1322 ep1323 ep1324 ep1325 Bool.false ep1334 ep1318 ep1314 ep1319 ep1316 (@ep1335 ep1323 ep1328 ep1325 Bool.false ep1329 ep1314 ep1330 ep1332 (BSN.logGammaStirling_unfold 2 qz57) (ep1438 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep1439 200000000038077 19038500000000000000 (BSN.log_sum_c_eq qz61 4) (ep1440 (BSN.log_sum_c_succ qz61 3 4 rfl) (ep1489 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable def ep1491 := @Enclosure.Real.IsNear.mulLit_ff (@HDiv.hDiv Real Real Real qz1 qz61 (2 : Real)) (Real.log Real.pi) 126105 2000 0 1 75021 65536 1 262144 1892104641 26214400 25221 104857600 (@Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real qz1 qz61 (2 : Real)) (Enclosure.sfrac Bool.false 126105 2000) Bool.false 126105 2000 0 1 (BSN.t_half_eq qz61 Bool.false 126105 1000 (@Eq.refl Real qz61)) (Enclosure.Real.IsNear.const Bool.false 126105 2000)) EMRow41.d6 rfl

noncomputable def ep1492 := @ep1320 25221 104857600 ep1321 ep1313 ep1314 ep1315 ep1316 (@ep1326 ep1319 ep1316 (ep1490 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep1491 rfl rfl

noncomputable def ep1493 := BSN.cos_dyadic_bound_f 1488213 2147483648 1 0 1048576 381142 0 1 1 0 1 1 1048575 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 1488213) qz266 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 1488213) qz267 0 0 rfl) rfl rfl

noncomputable def ep1494 := @ep1312 524288 Bool.false 1048575 1048576 1 190385 (@ep1317 131768673 1048576 181 524288 ep1492 rfl) (Enclosure.sfrac_false_div 131768673 1048576) (BSN.cos_reduce0 qz974 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 104723719259429011456) qz271) 226375608064910080 72057594037927936 Bool.false 1048575 1048576 20 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q0 131768673 1048576 226375608064910080 72057594037927936 20 104723719259429011456 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1048575 1048576 104723719259429011456 151115727451828646838272 1488213 2147483648 381142 380770 (ep1493 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1495 := nat_lit 72666125800117087786523279996051

noncomputable def ep1496 := nat_lit 16637420087224589460210909516990392311

noncomputable abbrev qz78 := (@HPow.hPow Complex Complex Complex (@instHPow Complex Complex Complex.instPow) qz609 (@Neg.neg Complex Complex.instNeg qz384))

noncomputable abbrev qz79 := (@HAdd.hAdd Complex Complex Complex qz260 (@HDiv.hDiv Complex Complex Complex qz346 qz609 (@HSub.hSub Complex Complex Complex qz595 qz384 (1 : Complex))) qz345)

noncomputable def ep1497 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz64 2 32) (@HAdd.hAdd Complex Complex Complex qz13 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 32, @HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast n) qz65) (@HMul.hMul Complex Complex Complex qz3 qz78 (@HAdd.hAdd Complex Complex Complex qz13 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1))))))) Bool.false ep1307 ep1308 ep1309

noncomputable def ep1498 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 32, @HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast n) qz65) (@HMul.hMul Complex Complex Complex qz3 qz78 (@HAdd.hAdd Complex Complex Complex qz13 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))))) Bool.false 2562436763661 549755813888 615636032755247 104665260627066880

noncomputable def ep1499 := nat_lit 1366811058618976598704406405023403

noncomputable def ep1500 := nat_lit 220345356876031736520905424122079641

noncomputable def ep1501 := nat_lit 79584297008556769102813839996051

noncomputable def ep1502 := nat_lit 219817324740888657292697605310392311

noncomputable def ep1503 := nat_lit 36833567699753033796620487746143240939567579136

noncomputable def ep1504 := nat_lit 39948625131331164801776450192088326930956288

noncomputable def ep1505 := @ep1498 Bool.true 259298479 549755813888 615344618812687 104665260627066880 Bool.true ep1499 ep1308 ep1500 ep1310 Bool.false ep1501 ep1308 ep1502 ep1310 Bool.false ep1503 ep1307 ep1308 ep1309 ep1310 Bool.false ep1504 ep1495 ep1308

noncomputable def ep1506 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 32, @HPow.hPow Complex Complex Complex qz14 (@Nat.cast Complex Complex.instNatCast n) qz65) (BSN.headSumC qz64 32) Bool.false 2562436763661 549755813888 615636032755247 104665260627066880 Bool.true 259298479 549755813888 615344618812687

noncomputable def ep1507 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 32) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 31) (@HPow.hPow Complex Complex Complex qz14 qz912 qz65)) Bool.false 2562436763661 549755813888 615636032755247 104665260627066880 Bool.true 259298479 549755813888 615344618812687 104665260627066880

noncomputable def ep1508 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 31) (@HPow.hPow Complex Complex Complex qz14 qz912 qz65) Bool.false 1237819564577 274877906944 150742984083213 26166315156766720 Bool.true 1479005535 17179869184 301360342433791 52332630313533440 Bool.false

noncomputable def ep1509 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 31) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 30) (@HPow.hPow Complex Complex Complex qz14 qz913 qz65)) Bool.false 1237819564577 274877906944 150742984083213 26166315156766720 Bool.true 1479005535 17179869184 301360342433791 52332630313533440

noncomputable def ep1510 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 30) (@HPow.hPow Complex Complex Complex qz14 qz913 qz65) Bool.false 1241848291069 274877906944 59019784870295 10466526062706688 Bool.false 105438146373 1099511627776 235942046326917 41866104250826752 Bool.true

noncomputable def ep1511 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 30) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 29) (@HPow.hPow Complex Complex Complex qz14 qz914 qz65)) Bool.false 1241848291069 274877906944 59019784870295 10466526062706688 Bool.false 105438146373 1099511627776 235942046326917 41866104250826752

noncomputable def ep1512 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 29) (@HPow.hPow Complex Complex Complex qz14 qz914 qz65) Bool.false 5144817666991 1099511627776 1154216623939739 209330521254133760 Bool.false 4407153183 1099511627776 1153605852867399 209330521254133760 Bool.true

noncomputable def ep1513 := nat_lit 5461706543856480132530176

noncomputable def ep1514 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 29) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 28) (@HPow.hPow Complex Complex Complex qz14 qz915 qz65)) Bool.false 5144817666991 1099511627776 1154216623939739 209330521254133760 Bool.false 4407153183 1099511627776 1153605852867399 209330521254133760

noncomputable def ep1515 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 28) (@HPow.hPow Complex Complex Complex qz14 qz915 qz65) Bool.false 4995061924631 1099511627776 225528875248155 41866104250826752 Bool.true 17454914373 137438953472 112703909035067 20933052125413376 Bool.false

noncomputable def ep1516 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 28) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 27) (@HPow.hPow Complex Complex Complex qz14 qz916 qz65)) Bool.false 4995061924631 1099511627776 225528875248155 41866104250826752 Bool.true 17454914373 137438953472 112703909035067 20933052125413376

noncomputable def ep1517 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 27) (@HPow.hPow Complex Complex Complex qz14 qz916 qz65) Bool.false 4868746647777 1099511627776 220122383247953 41866104250826752 Bool.false 15062046883 549755813888 54998281984881 10466526062706688 Bool.false

noncomputable def ep1518 := nat_lit 2746064333796475119075328

noncomputable def ep1519 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 27) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 26) (@HPow.hPow Complex Complex Complex qz14 qz917 qz65)) Bool.false 4868746647777 1099511627776 220122383247953 41866104250826752 Bool.false 15062046883 549755813888 54998281984881 10466526062706688

noncomputable def ep1520 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 26) (@HPow.hPow Complex Complex Complex qz14 qz917 qz65) Bool.false 1258879597747 274877906944 268248104523609 52332630313533440 Bool.false 166815201509 1099511627776 1072373990308551 209330521254133760 Bool.true

noncomputable def ep1521 := nat_lit 1338310887981558150463488

noncomputable def ep1522 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 26) (@HAdd.hAdd Complex Complex Complex qz13 (BSN.headSumC qz64 25) (@HPow.hPow Complex Complex Complex qz14 qz918 qz65)) Bool.false 1258879597747 274877906944 268248104523609 52332630313533440 Bool.false 166815201509 1099511627776 1072373990308551 209330521254133760

noncomputable def ep1523 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 25) (@HPow.hPow Complex Complex Complex qz14 qz918 qz65) Bool.false 2605246211759 549755813888 104482462938899 20933052125413376 Bool.false 16809981067 549755813888 104424412953165 20933052125413376 Bool.true

noncomputable def ep1524 := nat_lit 1384152755692800072220672

noncomputable abbrev qz414 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 25 1)))

noncomputable def ep1525 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz14 qz918 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz355 (Real.cos qz414)) (@HMul.hMul Real Real Real qz0 qz355 (@Neg.neg Real Real.instNeg (Real.sin qz414)))) Bool.true 87487016265 549755813888 1083376488671 8051173894389760 Bool.false 133195239375 1099511627776 2163835444377 16102347788779520 (BSN.cpow_neg_s_mk qz61 126105 1000 25 (@Eq.refl Real qz61) rfl)

noncomputable def ep1526 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz357 126105 1000 0 1 3624129903009015 1125899906842624 50000000038077 9519250000000000000 18280836056758073463 45035996273704960 1261050000960340017 1903850000000000000000 qz386 (BSN.isNear_log_sfrac 25 1 3624129903009015 1125899906842624 50000000038077 9519250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz920) Bool.false 60802810194841294602240 18889465931478580854784 1000000000761540 190385000000000000000 3624129903009015 1125899906842624 50000000038077 9519250000000000000 (BSN.log_rat_reduce_isNear 25 1 4 50 32 233982 524288 24973259072661432 36028797018963968 190385 1000000000000000 rfl rfl rfl rfl (ep715 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1527 := nat_lit 136201528325902623962249428998671118658646834294802701327138975172338241904896

noncomputable def ep1528 := nat_lit 14528267193532052579716796838958540632357826889133078072359449151284060416

noncomputable def ep1529 := nat_lit 408575528443320807781588853402335438894675787230629837825272206618712157593856

noncomputable def ep1530 := BSN.cos_dyadic_bound_f 1397258394 2147483648 3 2 1048576 381142 ep1527 ep88 ep1528 ep1529 ep91 ep1528 834342 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1397258394) qz266 0 2 ep1527 ep88 ep1528 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1397258394) qz267 0 2 ep1529 ep91 ep1528 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz986 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 212816941) qz280)

noncomputable def ep1531 := @Enclosure.Real.IsNear.cos_image qz414 qz986 Bool.false 212816941 524288 87 131072 Bool.true 834342 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz414 Bool.false 18280836056758073463 45035996273704960 1261050000960340017 1903850000000000000000 212816941 524288 87 131072 (ep1526 rfl) rfl) (Enclosure.sfrac_false_div 212816941 524288) (BSN.cos_reduce2 qz986 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 49161659250344021983232) qz281) 226375608064910080 72057594037927936 Bool.false 834342 1048576 64 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q2 212816941 524288 226375608064910080 72057594037927936 64 49161659250344021983232 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 834342 1048576 49161659250344021983232 75557863725914323419136 1397258394 2147483648 381142 380770 (ep1530 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1532 := nat_lit 3811596410105882731653846017513703696

noncomputable def ep1533 := BSN.sin_dyadic_bound_f 1397258394 2147483648 2 1 1048576 381142 ep1532 ep123 ep1532 ep1532 ep124 ep1532 635125 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1397258394) qz272 0 1 ep1532 ep123 ep1532 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1397258394) qz273 0 1 ep1532 ep124 ep1532 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1534 := @Enclosure.Real.IsNear.sin_image qz414 qz986 Bool.false 212816941 524288 87 131072 Bool.true 635125 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz414 Bool.false 18280836056758073463 45035996273704960 1261050000960340017 1903850000000000000000 212816941 524288 87 131072 (ep1526 rfl) rfl) (Enclosure.sfrac_false_div 212816941 524288) (BSN.sin_reduce2 qz986 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 49161659250344021983232) qz281) 226375608064910080 72057594037927936 Bool.false 635125 1048576 64 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q2 212816941 524288 226375608064910080 72057594037927936 64 49161659250344021983232 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 635125 1048576 49161659250344021983232 75557863725914323419136 1397258394 2147483648 381142 380770 (ep1533 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1535 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz355 (Real.cos qz414)) (@HMul.hMul Real Real Real qz0 qz355 (@Neg.neg Real Real.instNeg (Real.sin qz414))) Bool.true 87487016265 549755813888 1083376488671 8051173894389760 Bool.false 133195239375 1099511627776 2163835444377 16102347788779520 (@Enclosure.Real.IsNear.mulLit_ft qz355 (Real.cos qz414) 209715 1048576 1 1048576 417171 524288 16694567 24954142720 87487016265 549755813888 1083376488671 8051173894389760 qz610 (@Enclosure.Real.IsNear.recentre' (Real.cos qz414) Bool.true 834342 1048576 16694567 24954142720 417171 524288 16694567 24954142720 (ep1531 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz355 (@Neg.neg Real Real.instNeg (Real.sin qz414)) 209715 1048576 1 1048576 635125 1048576 16694567 24954142720 133195239375 1099511627776 2163835444377 16102347788779520 qz610 (@Enclosure.Real.IsNear.neg (Real.sin qz414) Bool.true 635125 1048576 16694567 24954142720 (@Enclosure.Real.IsNear.recentre' (Real.sin qz414) Bool.true 635125 1048576 16694567 24954142720 635125 1048576 16694567 24954142720 (ep1534 rfl rfl) rfl)) rfl)

noncomputable def ep1536 := @ep1523 87487016265 549755813888 1083376488671 8051173894389760 Bool.false 133195239375 1099511627776 2163835444377 16102347788779520 Bool.false ep1524 1258879597747 274877906944 268248104523609 52332630313533440 Bool.false 91707626874471020756992 166815201509 1099511627776 1072373990308551 209330521254133760 EMRow41.d19 (ep1525 ep1535) rfl rfl

noncomputable abbrev qz415 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 26 1)))

noncomputable def ep1537 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz14 qz917 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz358 (Real.cos qz415)) (@HMul.hMul Real Real Real qz0 qz358 (@Neg.neg Real Real.instNeg (Real.sin qz415)))) Bool.true 166771743211 1099511627776 27619498145329 209330521254133760 Bool.true 136691107743 1099511627776 27591649389069 209330521254133760 (BSN.cpow_neg_s_mk qz61 126105 1000 26 (@Eq.refl Real qz61) rfl)

noncomputable def ep1538 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz360 126105 1000 0 1 3668288609262839 1125899906842624 50000000038077 9519250000000000000 92517907014218062419 225179981368524800 1261050000960340017 1903850000000000000000 qz386 (BSN.isNear_log_sfrac 26 1 3668288609262839 1125899906842624 50000000038077 9519250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz923) Bool.false 61543670347942250676224 18889465931478580854784 1000000000761540 190385000000000000000 3668288609262839 1125899906842624 50000000038077 9519250000000000000 (BSN.log_rat_reduce_isNear 26 1 4 52 32 254545 524288 24973259072661432 36028797018963968 190385 1000000000000000 rfl rfl rfl rfl (ep726 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1539 := nat_lit 836201379006121383515171730616073363165133780910990459452379020481497072251425

noncomputable def ep1540 := nat_lit 168983271783598853661797381220293225161178011964040493313864928560565826081

noncomputable def ep1541 := nat_lit 2189777638766477796776664003472502143067946566557033233005151177091013320749601

noncomputable def ep1542 := BSN.sin_dyadic_bound_f 1898805427 2147483648 3 2 1048576 381142 ep1539 ep95 ep1540 ep1541 ep97 ep1540 810977 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1898805427) qz272 0 2 ep1539 ep95 ep1540 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1898805427) qz273 0 2 ep1541 ep97 ep1540 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz987 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 107705019) qz313)

noncomputable def ep1543 := @Enclosure.Real.IsNear.cos_image qz415 qz987 Bool.false 107705019 262144 87 131072 Bool.true 810977 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz415 Bool.false 92517907014218062419 225179981368524800 1261050000960340017 1903850000000000000000 107705019 262144 87 131072 (ep1538 rfl) rfl) (Enclosure.sfrac_false_div 107705019 262144) (BSN.cos_reduce1 qz987 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 33404138350437464014848) qz314) 226375608064910080 72057594037927936 Bool.false 810977 1048576 65 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q1 107705019 262144 226375608064910080 72057594037927936 65 33404138350437464014848 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 810977 1048576 33404138350437464014848 37778931862957161709568 1898805427 2147483648 381142 380770 (ep1542 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1544 := nat_lit 464631425346415701443389538067249776525145957400312051026127840235747513840161

noncomputable def ep1545 := nat_lit 1393556309495679906622845019439308743125115516177008072091755790850121409868321

noncomputable def ep1546 := BSN.cos_dyadic_bound_f 1898805427 2147483648 3 2 1048576 381142 ep1544 ep88 ep1540 ep1545 ep91 ep1540 664701 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1898805427) qz266 0 2 ep1544 ep88 ep1540 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1898805427) qz267 0 2 ep1545 ep91 ep1540 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1547 := @Enclosure.Real.IsNear.sin_image qz415 qz987 Bool.false 107705019 262144 87 131072 Bool.false 664701 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz415 Bool.false 92517907014218062419 225179981368524800 1261050000960340017 1903850000000000000000 107705019 262144 87 131072 (ep1538 rfl) rfl) (Enclosure.sfrac_false_div 107705019 262144) (BSN.sin_reduce1 qz987 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 33404138350437464014848) qz314) 226375608064910080 72057594037927936 Bool.false 664701 1048576 65 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q1 107705019 262144 226375608064910080 72057594037927936 65 33404138350437464014848 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 664701 1048576 33404138350437464014848 37778931862957161709568 1898805427 2147483648 381142 380770 (ep1546 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1548 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz358 (Real.cos qz415)) (@HMul.hMul Real Real Real qz0 qz358 (@Neg.neg Real Real.instNeg (Real.sin qz415))) Bool.true 166771743211 1099511627776 27619498145329 209330521254133760 Bool.true 136691107743 1099511627776 27591649389069 209330521254133760 (@Enclosure.Real.IsNear.mulLit_ft qz358 (Real.cos qz415) 205643 1048576 1 1048576 810977 1048576 16694567 24954142720 166771743211 1099511627776 27619498145329 209330521254133760 qz612 (@Enclosure.Real.IsNear.recentre' (Real.cos qz415) Bool.true 810977 1048576 16694567 24954142720 810977 1048576 16694567 24954142720 (ep1543 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz358 (@Neg.neg Real Real.instNeg (Real.sin qz415)) 205643 1048576 1 1048576 664701 1048576 16694567 24954142720 136691107743 1099511627776 27591649389069 209330521254133760 qz612 (@Enclosure.Real.IsNear.neg (Real.sin qz415) Bool.false 664701 1048576 16694567 24954142720 (@Enclosure.Real.IsNear.recentre' (Real.sin qz415) Bool.false 664701 1048576 16694567 24954142720 664701 1048576 16694567 24954142720 (ep1547 rfl rfl) rfl)) rfl)

noncomputable def ep1549 := @ep1520 166771743211 1099511627776 27619498145329 209330521254133760 Bool.true 136691107743 1099511627776 27591649389069 209330521254133760 Bool.false ep1521 4868746647777 1099511627776 220122383247953 41866104250826752 Bool.false 33121791371931514044416 15062046883 549755813888 54998281984881 10466526062706688 (ep1522 (BSN.head_sum_c_succ qz64 25 26 rfl rfl) (ep1536 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1537 ep1548) rfl rfl

noncomputable abbrev qz416 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 27 1)))

noncomputable def ep1550 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz14 qz916 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz361 (Real.cos qz416)) (@HMul.hMul Real Real Real qz0 qz361 (@Neg.neg Real Real.instNeg (Real.sin qz416)))) Bool.false 63157638427 549755813888 2703246000101 20933052125413376 Bool.true 84881704375 549755813888 2707345065305 20933052125413376 (BSN.cpow_neg_s_mk qz61 126105 1000 27 (@Eq.refl Real qz61) rfl)

noncomputable def ep1551 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz363 126105 1000 0 1 3710780868205815 1125899906842624 50000000038077 9519250000000000000 18717920855403772023 45035996273704960 1261050000960340017 1903850000000000000000 qz386 (BSN.isNear_log_sfrac 27 1 3710780868205815 1125899906842624 50000000038077 9519250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz925) Bool.false 62256572154556490711040 18889465931478580854784 1000000000761540 190385000000000000000 3710780868205815 1125899906842624 50000000038077 9519250000000000000 (BSN.log_rat_reduce_isNear 27 1 4 54 32 274332 524288 24973259072661432 36028797018963968 190385 1000000000000000 rfl rfl rfl rfl (ep737 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1552 := nat_lit 571392927157484896296957714170407182540751430990243266510645526788428281507361

noncomputable def ep1553 := nat_lit 255519308884725388643124324120781021821936401727011784346533061048594165281

noncomputable def ep1554 := nat_lit 1713667742854685238113586893862979985578610420167275775963243514243187656191521

noncomputable def ep1555 := BSN.cos_dyadic_bound_f 1999530189 2147483648 3 2 1048576 381142 ep1552 ep88 ep1553 ep1554 ep91 ep1553 625946 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1999530189) qz266 0 2 ep1552 ep88 ep1553 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1999530189) qz267 0 2 ep1554 ep91 ep1553 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz988 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 108952639) qz313)

noncomputable def ep1556 := @Enclosure.Real.IsNear.cos_image qz416 qz988 Bool.false 108952639 262144 695 1048576 Bool.false 625946 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz416 Bool.false 18717920855403772023 45035996273704960 1261050000960340017 1903850000000000000000 108952639 262144 695 1048576 (ep1551 rfl) rfl) (Enclosure.sfrac_false_div 108952639 262144) (BSN.cos_reduce0 qz988 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 35176107095933403004928) qz314) 226375608064910080 72057594037927936 Bool.false 625946 1048576 66 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q0 108952639 262144 226375608064910080 72057594037927936 66 35176107095933403004928 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 625946 1048576 35176107095933403004928 37778931862957161709568 1999530189 2147483648 381142 380770 (ep1555 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1557 := nat_lit 1028302853436365033023609386047436303755895026661056270291684721770332031381025

noncomputable def ep1558 := nat_lit 2692760442023714102527840476456613816753918125176160784065470360632981405920801

noncomputable def ep1559 := BSN.sin_dyadic_bound_f 1999530189 2147483648 3 2 1048576 381142 ep1557 ep95 ep1553 ep1558 ep97 ep1553 841250 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1999530189) qz272 0 2 ep1557 ep95 ep1553 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1999530189) qz273 0 2 ep1558 ep97 ep1553 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1560 := @Enclosure.Real.IsNear.sin_image qz416 qz988 Bool.false 108952639 262144 695 1048576 Bool.false 841250 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz416 Bool.false 18717920855403772023 45035996273704960 1261050000960340017 1903850000000000000000 108952639 262144 695 1048576 (ep1551 rfl) rfl) (Enclosure.sfrac_false_div 108952639 262144) (BSN.sin_reduce0 qz988 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 35176107095933403004928) qz314) 226375608064910080 72057594037927936 Bool.false 841250 1048576 66 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q0 108952639 262144 226375608064910080 72057594037927936 66 35176107095933403004928 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 841250 1048576 35176107095933403004928 37778931862957161709568 1999530189 2147483648 381142 380770 (ep1559 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1561 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz361 (Real.cos qz416)) (@HMul.hMul Real Real Real qz0 qz361 (@Neg.neg Real Real.instNeg (Real.sin qz416))) Bool.false 63157638427 549755813888 2703246000101 20933052125413376 Bool.true 84881704375 549755813888 2707345065305 20933052125413376 (@Enclosure.Real.IsNear.mulLit_ff qz361 (Real.cos qz416) 201799 1048576 1 1048576 312973 524288 133366151 199633141760 63157638427 549755813888 2703246000101 20933052125413376 qz613 (@Enclosure.Real.IsNear.recentre' (Real.cos qz416) Bool.false 625946 1048576 133366151 199633141760 312973 524288 133366151 199633141760 (ep1556 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz361 (@Neg.neg Real Real.instNeg (Real.sin qz416)) 201799 1048576 1 1048576 420625 524288 133366151 199633141760 84881704375 549755813888 2707345065305 20933052125413376 qz613 (@Enclosure.Real.IsNear.neg (Real.sin qz416) Bool.false 420625 524288 133366151 199633141760 (@Enclosure.Real.IsNear.recentre' (Real.sin qz416) Bool.false 841250 1048576 133366151 199633141760 420625 524288 133366151 199633141760 (ep1560 rfl rfl) rfl)) rfl)

noncomputable def ep1562 := @ep1517 63157638427 549755813888 2703246000101 20933052125413376 Bool.true 84881704375 549755813888 2707345065305 20933052125413376 Bool.false ep1518 4995061924631 1099511627776 225528875248155 41866104250826752 Bool.true 38383762629895856848896 17454914373 137438953472 112703909035067 20933052125413376 (ep1519 (BSN.head_sum_c_succ qz64 26 27 rfl rfl) (ep1549 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1550 ep1561) rfl rfl

noncomputable abbrev qz417 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 28 1)))

noncomputable def ep1563 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz14 qz915 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz364 (Real.cos qz417)) (@HMul.hMul Real Real Real qz0 qz364 (@Neg.neg Real Real.instNeg (Real.sin qz417)))) Bool.false 18719467795 137438953472 6643061924741 52332630313533440 Bool.false 144046468167 1099511627776 26566762516729 209330521254133760 (BSN.cpow_neg_s_mk qz61 126105 1000 28 (@Eq.refl Real qz61) rfl)

noncomputable def ep1564 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz366 126105 1000 0 1 3751726938922231 1125899906842624 50000000038077 9519250000000000000 94622305126557588051 225179981368524800 1261050000960340017 1903850000000000000000 qz386 (BSN.isNear_log_sfrac 28 1 3751726938922231 1125899906842624 50000000038077 9519250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz928) Bool.false 62943533227317076688896 18889465931478580854784 1000000000761540 190385000000000000000 3751726938922231 1125899906842624 50000000038077 9519250000000000000 (BSN.log_rat_reduce_isNear 28 1 4 56 32 293399 524288 24973259072661432 36028797018963968 190385 1000000000000000 rfl rfl rfl rfl (ep748 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1565 := nat_lit 8923419991413162371693876859135750625

noncomputable def ep1566 := BSN.sin_dyadic_bound_f 1728354535 2147483648 2 1 1048576 381142 ep1565 ep123 ep1565 ep1565 ep124 ep1565 755720 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1728354535) qz272 0 1 ep1565 ep123 ep1565 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1728354535) qz273 0 1 ep1565 ep124 ep1565 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz989 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 110154861) qz313)

noncomputable def ep1567 := @Enclosure.Real.IsNear.cos_image qz417 qz989 Bool.false 110154861 262144 695 1048576 Bool.false 755720 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz417 Bool.false 94622305126557588051 225179981368524800 1261050000960340017 1903850000000000000000 110154861 262144 695 1048576 (ep1564 rfl) rfl) (Enclosure.sfrac_false_div 110154861 262144) (BSN.cos_reduce3 qz989 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 30405534533161637117952) qz314) 226375608064910080 72057594037927936 Bool.false 755720 1048576 66 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q3 110154861 262144 226375608064910080 72057594037927936 66 30405534533161637117952 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 755720 1048576 30405534533161637117952 37778931862957161709568 1728354535 2147483648 381142 380770 (ep1566 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1568 := nat_lit 318910287373650735549634283433213920832345465614415453236204157009732024690625

noncomputable def ep1569 := nat_lit 79627424343152082815374929739592205477918073323823558065583001982187890625

noncomputable def ep1570 := nat_lit 956571607272265902483272100440162578086080560696598712592481305025231698290625

noncomputable def ep1571 := BSN.cos_dyadic_bound_f 1728354535 2147483648 3 2 1048576 381142 ep1568 ep88 ep1569 ep1570 ep91 ep1569 726909 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1728354535) qz266 0 2 ep1568 ep88 ep1569 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1728354535) qz267 0 2 ep1570 ep91 ep1569 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1572 := @Enclosure.Real.IsNear.sin_image qz417 qz989 Bool.false 110154861 262144 695 1048576 Bool.true 726909 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz417 Bool.false 94622305126557588051 225179981368524800 1261050000960340017 1903850000000000000000 110154861 262144 695 1048576 (ep1564 rfl) rfl) (Enclosure.sfrac_false_div 110154861 262144) (BSN.sin_reduce3 qz989 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 30405534533161637117952) qz314) 226375608064910080 72057594037927936 Bool.false 726909 1048576 66 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q3 110154861 262144 226375608064910080 72057594037927936 66 30405534533161637117952 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 726909 1048576 30405534533161637117952 37778931862957161709568 1728354535 2147483648 381142 380770 (ep1571 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1573 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz364 (Real.cos qz417)) (@HMul.hMul Real Real Real qz0 qz364 (@Neg.neg Real Real.instNeg (Real.sin qz417))) Bool.false 18719467795 137438953472 6643061924741 52332630313533440 Bool.false 144046468167 1099511627776 26566762516729 209330521254133760 (@Enclosure.Real.IsNear.mulLit_ff qz364 (Real.cos qz417) 198163 1048576 1 1048576 94465 131072 133366151 199633141760 18719467795 137438953472 6643061924741 52332630313533440 qz614 (@Enclosure.Real.IsNear.recentre' (Real.cos qz417) Bool.false 755720 1048576 133366151 199633141760 94465 131072 133366151 199633141760 (ep1567 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz364 (@Neg.neg Real Real.instNeg (Real.sin qz417)) 198163 1048576 1 1048576 726909 1048576 133366151 199633141760 144046468167 1099511627776 26566762516729 209330521254133760 qz614 (@Enclosure.Real.IsNear.neg (Real.sin qz417) Bool.true 726909 1048576 133366151 199633141760 (@Enclosure.Real.IsNear.recentre' (Real.sin qz417) Bool.true 726909 1048576 133366151 199633141760 726909 1048576 133366151 199633141760 (ep1572 rfl rfl) rfl)) rfl)

noncomputable def ep1574 := @ep1515 18719467795 137438953472 6643061924741 52332630313533440 Bool.false 144046468167 1099511627776 26566762516729 209330521254133760 Bool.false 707098355955499639242752 5144817666991 1099511627776 1154216623939739 209330521254133760 Bool.false 605714521262313701376 4407153183 1099511627776 1153605852867399 209330521254133760 (ep1516 (BSN.head_sum_c_succ qz64 27 28 rfl rfl) (ep1562 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1563 ep1573) rfl rfl

noncomputable abbrev qz418 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 29 1)))

noncomputable def ep1575 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz14 qz914 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz367 (Real.cos qz418)) (@HMul.hMul Real Real Real qz0 qz367 (@Neg.neg Real Real.instNeg (Real.sin qz418)))) Bool.true 177424502715 1099511627776 26179073466161 209330521254133760 Bool.false 50515496595 549755813888 13052189383593 104665260627066880 (BSN.cpow_neg_s_mk qz61 126105 1000 29 (@Eq.refl Real qz61) rfl)

noncomputable def ep1576 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz369 126105 1000 0 1 3791236343078135 1125899906842624 50000000038077 9519250000000000000 19123754361754728567 45035996273704960 1261050000960340017 1903850000000000000000 qz386 (BSN.isNear_log_sfrac 29 1 3791236343078135 1125899906842624 50000000038077 9519250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz931) Bool.false 63606391034871975772160 18889465931478580854784 1000000000761540 190385000000000000000 3791236343078135 1125899906842624 50000000038077 9519250000000000000 (BSN.log_rat_reduce_isNear 29 1 4 58 32 311797 524288 24973259072661432 36028797018963968 190385 1000000000000000 rfl rfl rfl rfl (ep759 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1577 := nat_lit 1526962452566304297187037714040487936

noncomputable def ep1578 := BSN.cos_dyadic_bound_f 1111621888 2147483648 2 1 1048576 381142 ep1577 ep143 ep1577 ep1577 ep144 ep1577 911201 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1111621888) qz266 0 1 ep1577 ep143 ep1577 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1111621888) qz267 0 1 ep1577 ep144 ep1577 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz990 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 445259603) qz268)

noncomputable def ep1579 := @Enclosure.Real.IsNear.cos_image qz418 qz990 Bool.false 445259603 1048576 87 131072 Bool.true 911201 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz418 Bool.false 19123754361754728567 45035996273704960 1261050000960340017 1903850000000000000000 445259603 1048576 87 131072 (ep1576 rfl) rfl) (Enclosure.sfrac_false_div 445259603 1048576) (BSN.cos_reduce2 qz990 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 78223436312708399497216) qz271) 226375608064910080 72057594037927936 Bool.false 911201 1048576 67 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q2 445259603 1048576 226375608064910080 72057594037927936 67 78223436312708399497216 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 911201 1048576 78223436312708399497216 151115727451828646838272 1111621888 2147483648 381142 380770 (ep1578 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1580 := BSN.sin_dyadic_bound_f 1111621888 2147483648 2 1 1048576 381142 ep1577 ep123 ep1577 ep1577 ep124 ep1577 518866 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1111621888) qz272 0 1 ep1577 ep123 ep1577 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1111621888) qz273 0 1 ep1577 ep124 ep1577 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1581 := @Enclosure.Real.IsNear.sin_image qz418 qz990 Bool.false 445259603 1048576 87 131072 Bool.true 518866 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz418 Bool.false 19123754361754728567 45035996273704960 1261050000960340017 1903850000000000000000 445259603 1048576 87 131072 (ep1576 rfl) rfl) (Enclosure.sfrac_false_div 445259603 1048576) (BSN.sin_reduce2 qz990 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 78223436312708399497216) qz271) 226375608064910080 72057594037927936 Bool.false 518866 1048576 67 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q2 445259603 1048576 226375608064910080 72057594037927936 67 78223436312708399497216 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 518866 1048576 78223436312708399497216 151115727451828646838272 1111621888 2147483648 381142 380770 (ep1580 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1582 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz367 (Real.cos qz418)) (@HMul.hMul Real Real Real qz0 qz367 (@Neg.neg Real Real.instNeg (Real.sin qz418))) Bool.true 177424502715 1099511627776 26179073466161 209330521254133760 Bool.false 50515496595 549755813888 13052189383593 104665260627066880 (@Enclosure.Real.IsNear.mulLit_ft qz367 (Real.cos qz418) 194715 1048576 1 1048576 911201 1048576 16694567 24954142720 177424502715 1099511627776 26179073466161 209330521254133760 qz615 (@Enclosure.Real.IsNear.recentre' (Real.cos qz418) Bool.true 911201 1048576 16694567 24954142720 911201 1048576 16694567 24954142720 (ep1579 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz367 (@Neg.neg Real Real.instNeg (Real.sin qz418)) 194715 1048576 1 1048576 259433 524288 16694567 24954142720 50515496595 549755813888 13052189383593 104665260627066880 qz615 (@Enclosure.Real.IsNear.neg (Real.sin qz418) Bool.true 259433 524288 16694567 24954142720 (@Enclosure.Real.IsNear.recentre' (Real.sin qz418) Bool.true 518866 1048576 16694567 24954142720 259433 524288 16694567 24954142720 (ep1581 rfl rfl) rfl)) rfl)

noncomputable def ep1583 := @ep1512 177424502715 1099511627776 26179073466161 209330521254133760 Bool.false 50515496595 549755813888 13052189383593 104665260627066880 Bool.false ep1513 1241848291069 274877906944 59019784870295 10466526062706688 Bool.false 57965233974130690228224 105438146373 1099511627776 235942046326917 41866104250826752 (ep1514 (BSN.head_sum_c_succ qz64 28 29 rfl rfl) (ep1574 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1575 ep1582) rfl rfl

noncomputable abbrev qz419 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 30 1)))

noncomputable def ep1584 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz14 qz913 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz370 (Real.cos qz419)) (@HMul.hMul Real Real Real qz0 qz370 (@Neg.neg Real Real.instNeg (Real.sin qz419)))) Bool.true 1007181623 68719476736 6387043814951 52332630313533440 Bool.true 200094500613 1099511627776 25731138100579 209330521254133760 (BSN.cpow_neg_s_mk qz61 126105 1000 30 (@Eq.refl Real qz61) rfl)

noncomputable def ep1585 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz372 126105 1000 0 1 3829405717437687 1125899906842624 50000000038077 9519250000000000000 96581441599495903827 225179981368524800 1261050000960340017 1903850000000000000000 qz386 (BSN.isNear_log_sfrac 30 1 3829405717437687 1125899906842624 50000000038077 9519250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz934) Bool.false 64246766873087041339392 18889465931478580854784 1000000000761540 190385000000000000000 3829405717437687 1125899906842624 50000000038077 9519250000000000000 (BSN.log_rat_reduce_isNear 30 1 4 60 32 329571 524288 24973259072661432 36028797018963968 190385 1000000000000000 rfl rfl rfl rfl (ep774 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1586 := BSN.sin_dyadic_bound_f 172579098 2147483648 1 0 1048576 381142 0 1 1 0 1 1 84176 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 172579098) qz272 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 172579098) qz273 0 0 rfl) rfl rfl

noncomputable abbrev qz633 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 28108899) (@Nat.cast Real Real.instNatCast 65536))

noncomputable def ep1587 := @Enclosure.Real.IsNear.cos_image qz419 qz633 Bool.false 28108899 65536 695 1048576 Bool.true 84176 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz419 Bool.false 96581441599495903827 225179981368524800 1261050000960340017 1903850000000000000000 28108899 65536 695 1048576 (ep1585 rfl) rfl) (Enclosure.sfrac_false_div 28108899 65536) (BSN.cos_reduce1 qz633 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 759010901485512818688) (@Nat.cast Real Real.instNatCast 9444732965739290427392)) 226375608064910080 72057594037927936 Bool.false 84176 1048576 68 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q1 28108899 65536 226375608064910080 72057594037927936 68 759010901485512818688 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 84176 1048576 759010901485512818688 9444732965739290427392 172579098 2147483648 381142 380770 (ep1586 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1588 := nat_lit 887059556727855498313759372908816

noncomputable def ep1589 := BSN.cos_dyadic_bound_f 172579098 2147483648 2 1 1048576 381142 ep1588 ep143 ep1588 ep1588 ep144 ep1588 1045191 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 172579098) qz266 0 1 ep1588 ep143 ep1588 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 172579098) qz267 0 1 ep1588 ep144 ep1588 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1590 := @Enclosure.Real.IsNear.sin_image qz419 qz633 Bool.false 28108899 65536 695 1048576 Bool.false 1045191 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz419 Bool.false 96581441599495903827 225179981368524800 1261050000960340017 1903850000000000000000 28108899 65536 695 1048576 (ep1585 rfl) rfl) (Enclosure.sfrac_false_div 28108899 65536) (BSN.sin_reduce1 qz633 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 759010901485512818688) (@Nat.cast Real Real.instNatCast 9444732965739290427392)) 226375608064910080 72057594037927936 Bool.false 1045191 1048576 68 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q1 28108899 65536 226375608064910080 72057594037927936 68 759010901485512818688 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1045191 1048576 759010901485512818688 9444732965739290427392 172579098 2147483648 381142 380770 (ep1589 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1591 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz370 (Real.cos qz419)) (@HMul.hMul Real Real Real qz0 qz370 (@Neg.neg Real Real.instNeg (Real.sin qz419))) Bool.true 1007181623 68719476736 6387043814951 52332630313533440 Bool.true 200094500613 1099511627776 25731138100579 209330521254133760 (@Enclosure.Real.IsNear.mulLit_ft qz370 (Real.cos qz419) 191443 1048576 1 1048576 5261 65536 133366151 199633141760 1007181623 68719476736 6387043814951 52332630313533440 qz617 (@Enclosure.Real.IsNear.recentre' (Real.cos qz419) Bool.true 84176 1048576 133366151 199633141760 5261 65536 133366151 199633141760 (ep1587 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz370 (@Neg.neg Real Real.instNeg (Real.sin qz419)) 191443 1048576 1 1048576 1045191 1048576 133366151 199633141760 200094500613 1099511627776 25731138100579 209330521254133760 qz617 (@Enclosure.Real.IsNear.neg (Real.sin qz419) Bool.false 1045191 1048576 133366151 199633141760 (@Enclosure.Real.IsNear.recentre' (Real.sin qz419) Bool.false 1045191 1048576 133366151 199633141760 1045191 1048576 133366151 199633141760 (ep1590 rfl rfl) rfl)) rfl)

noncomputable def ep1592 := @ep1510 1007181623 68719476736 6387043814951 52332630313533440 Bool.true 200094500613 1099511627776 25731138100579 209330521254133760 Bool.false 85062312771314801180672 1237819564577 274877906944 150742984083213 26166315156766720 Bool.true 104075762129764079370240 1479005535 17179869184 301360342433791 52332630313533440 (ep1511 (BSN.head_sum_c_succ qz64 29 30 rfl rfl) (ep1583 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1584 ep1591) rfl rfl

noncomputable abbrev qz420 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 31 1)))

noncomputable def ep1593 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz14 qz912 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz373 (Real.cos qz420)) (@HMul.hMul Real Real Real qz0 qz373 (@Neg.neg Real Real.instNeg (Real.sin qz420)))) Bool.false 86797634507 549755813888 2532819284479 20933052125413376 Bool.false 47068878641 549755813888 2524786789021 20933052125413376 (BSN.cpow_neg_s_mk qz61 126105 1000 31 (@Eq.refl Real qz61) rfl)

noncomputable def ep1594 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz375 126105 1000 0 1 3866325256314103 1125899906842624 50000000038077 9519250000000000000 97512589289497991763 225179981368524800 1261050000960340017 1903850000000000000000 qz386 (BSN.isNear_log_sfrac 31 1 3866325256314103 1125899906842624 50000000038077 9519250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz936) Bool.false 64866173951437069877248 18889465931478580854784 1000000000761540 190385000000000000000 3866325256314103 1125899906842624 50000000038077 9519250000000000000 (BSN.log_rat_reduce_isNear 31 1 4 62 32 346763 524288 24973259072661432 36028797018963968 190385 1000000000000000 rfl rfl rfl rfl (ep788 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1595 := nat_lit 1819960561202640299066267651641358923912965446567172756710116080002960966836480

noncomputable def ep1596 := nat_lit 800091252567746961116214530531213674972650716311956666224726361594366812416

noncomputable def ep1597 := nat_lit 4765267988740853002474608073630318073822096639849518813924035414469935462113536

noncomputable def ep1598 := BSN.sin_dyadic_bound_f 2306175958 2147483648 3 2 1048576 381142 ep1595 ep95 ep1596 ep1597 ep97 ep1596 921766 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2306175958) qz272 0 2 ep1595 ep95 ep1596 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2306175958) qz273 0 2 ep1597 ep97 ep1596 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz991 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 227039189) qz280)

noncomputable def ep1599 := @Enclosure.Real.IsNear.cos_image qz420 qz991 Bool.false 227039189 524288 87 131072 Bool.false 921766 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz420 Bool.false 97512589289497991763 225179981368524800 1261050000960340017 1903850000000000000000 227039189 524288 87 131072 (ep1594 rfl) rfl) (Enclosure.sfrac_false_div 227039189 524288) (BSN.cos_reduce3 qz991 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 81141353012504253431808) qz281) 226375608064910080 72057594037927936 Bool.false 921766 1048576 68 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q3 227039189 524288 226375608064910080 72057594037927936 68 81141353012504253431808 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 921766 1048576 81141353012504253431808 75557863725914323419136 2306175958 2147483648 381142 380770 (ep1598 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1600 := nat_lit 1011444796780385831463978124036546608251635315077901290023942145051242477936896

noncomputable def ep1601 := nat_lit 3032734207836022000469701943048577397404960643801079956739376982430538700185856

noncomputable def ep1602 := BSN.cos_dyadic_bound_f 2306175958 2147483648 3 2 1048576 381142 ep1600 ep88 ep1596 ep1601 ep91 ep1596 499858 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2306175958) qz266 0 2 ep1600 ep88 ep1596 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2306175958) qz267 0 2 ep1601 ep91 ep1596 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1603 := @Enclosure.Real.IsNear.sin_image qz420 qz991 Bool.false 227039189 524288 87 131072 Bool.true 499858 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz420 Bool.false 97512589289497991763 225179981368524800 1261050000960340017 1903850000000000000000 227039189 524288 87 131072 (ep1594 rfl) rfl) (Enclosure.sfrac_false_div 227039189 524288) (BSN.sin_reduce3 qz991 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 81141353012504253431808) qz281) 226375608064910080 72057594037927936 Bool.false 499858 1048576 68 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q3 227039189 524288 226375608064910080 72057594037927936 68 81141353012504253431808 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 499858 1048576 81141353012504253431808 75557863725914323419136 2306175958 2147483648 381142 380770 (ep1602 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1604 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz373 (Real.cos qz420)) (@HMul.hMul Real Real Real qz0 qz373 (@Neg.neg Real Real.instNeg (Real.sin qz420))) Bool.false 86797634507 549755813888 2532819284479 20933052125413376 Bool.false 47068878641 549755813888 2524786789021 20933052125413376 (@Enclosure.Real.IsNear.mulLit_ff qz373 (Real.cos qz420) 188329 1048576 1 1048576 460883 524288 16694567 24954142720 86797634507 549755813888 2532819284479 20933052125413376 qz618 (@Enclosure.Real.IsNear.recentre' (Real.cos qz420) Bool.false 921766 1048576 16694567 24954142720 460883 524288 16694567 24954142720 (ep1599 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz373 (@Neg.neg Real Real.instNeg (Real.sin qz420)) 188329 1048576 1 1048576 249929 524288 16694567 24954142720 47068878641 549755813888 2524786789021 20933052125413376 qz618 (@Enclosure.Real.IsNear.neg (Real.sin qz420) Bool.true 249929 524288 16694567 24954142720 (@Enclosure.Real.IsNear.recentre' (Real.sin qz420) Bool.true 499858 1048576 16694567 24954142720 249929 524288 16694567 24954142720 (ep1603 rfl rfl) rfl)) rfl)

noncomputable def ep1605 := @ep1508 86797634507 549755813888 2532819284479 20933052125413376 Bool.false 47068878641 549755813888 2524786789021 20933052125413376 Bool.false 704357254271492878761984 2562436763661 549755813888 615636032755247 104665260627066880 Bool.true 4454713948830171136 259298479 549755813888 615344618812687 104665260627066880 (ep1509 (BSN.head_sum_c_succ qz64 30 31 rfl rfl) (ep1592 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1593 ep1604) rfl rfl

noncomputable def ep1606 := @Enclosure.Complex.IsNear.mul qz78 (@HAdd.hAdd Complex Complex Complex qz13 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1))))) Bool.true ep1499 ep1308 ep1500 ep1310 Bool.false

noncomputable def ep1607 := nat_lit 12189884316334599543624905170221

noncomputable def ep1608 := nat_lit 146676712411887518113542963200000

noncomputable def ep1609 := nat_lit 1674798956362831095119607833361519

noncomputable def ep1610 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re qz78) (Complex.re (@HAdd.hAdd Complex Complex Complex qz13 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 (Complex.im qz78) (Complex.im (@HAdd.hAdd Complex Complex Complex qz13 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1))))))) ep1607 ep1608 ep1609

noncomputable def ep1611 := nat_lit 27925045892537205136046877048832000000

noncomputable def ep1612 := nat_lit 147822626985516644341915888001303

noncomputable def ep1613 := nat_lit 4066573941519125154534203137379057

noncomputable def ep1614 := nat_lit 214808045327209270277283669606400000000

noncomputable def ep1615 := nat_lit 200479352566443162967620348071140507687683777707170541967769600000

noncomputable def ep1616 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re qz78) (Complex.re (@HAdd.hAdd Complex Complex Complex qz13 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))))) 181545819741 1099511627776 24943038140799 209330521254133760 67144946293586603281

noncomputable abbrev qz421 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 32 1)))

noncomputable abbrev qz992 := (@Neg.neg Real Real.instNeg (Real.sin qz421))

noncomputable def ep1617 := @Enclosure.Complex.IsNear.of_eq qz78 (Complex.mk (@HMul.hMul Real Real Real qz0 qz376 (Real.cos qz421)) (@HMul.hMul Real Real Real qz0 qz376 qz992)) Bool.true 181545819741 1099511627776 24943038140799 209330521254133760 Bool.false 69423819027 1099511627776 24827878442769 209330521254133760 (BSN.cpow_neg_s_mk qz61 126105 1000 32 (@Eq.refl Real qz61) rfl)

noncomputable def ep1618 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz378 126105 1000 0 1 15608286920413395 4503599627370496 40000000038077 7615400000000000000 78731320883949247059 180143985094819840 1008840000960340017 1523080000000000000000 qz386 (BSN.isNear_log_sfrac 32 1 15608286920413395 4503599627370496 40000000038077 7615400000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz619) Bool.false 65465900263437584302080 18889465931478580854784 1000000000951925 190385000000000000000 15608286920413395 4503599627370496 40000000038077 7615400000000000000 (BSN.log_rat_reduce_isNear 32 1 5 64 64 0 524288 24973259072661432 36028797018963968 190385 1000000000000000 rfl rfl rfl rfl (ep811 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1619 := nat_lit 378497230401131300640896298590189121

noncomputable def ep1620 := BSN.cos_dyadic_bound_f 784360431 2147483648 2 1 1048576 381142 ep1619 ep143 ep1619 ep1619 ep144 ep1619 979407 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 784360431) qz266 0 1 ep1619 ep143 ep1619 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 784360431) qz267 0 1 ep1619 ep144 ep1619 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz993 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 229138301) qz280)

noncomputable def ep1621 := @Enclosure.Real.IsNear.cos_image qz421 qz993 Bool.false 229138301 524288 87 131072 Bool.true 979407 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz421 Bool.false 78731320883949247059 180143985094819840 1008840000960340017 1523080000000000000000 229138301 524288 87 131072 (ep1618 rfl) rfl) (Enclosure.sfrac_false_div 229138301 524288) (BSN.cos_reduce2 qz993 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 27597229281383496548352) qz281) 226375608064910080 72057594037927936 Bool.false 979407 1048576 69 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q2 229138301 524288 226375608064910080 72057594037927936 69 27597229281383496548352 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 979407 1048576 27597229281383496548352 75557863725914323419136 784360431 2147483648 381142 380770 (ep1620 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1622 := BSN.sin_dyadic_bound_f 784360431 2147483648 2 1 1048576 381142 ep1619 ep123 ep1619 ep1619 ep124 ep1619 374529 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 784360431) qz272 0 1 ep1619 ep123 ep1619 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 784360431) qz273 0 1 ep1619 ep124 ep1619 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1623 := @Enclosure.Real.IsNear.sin_image qz421 qz993 Bool.false 229138301 524288 87 131072 Bool.true 374529 1048576 1 190385 (@Enclosure.Real.IsNear.recentre' qz421 Bool.false 78731320883949247059 180143985094819840 1008840000960340017 1523080000000000000000 229138301 524288 87 131072 (ep1618 rfl) rfl) (Enclosure.sfrac_false_div 229138301 524288) (BSN.sin_reduce2 qz993 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 27597229281383496548352) qz281) 226375608064910080 72057594037927936 Bool.false 374529 1048576 69 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q2 229138301 524288 226375608064910080 72057594037927936 69 27597229281383496548352 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 374529 1048576 27597229281383496548352 75557863725914323419136 784360431 2147483648 381142 380770 (ep1622 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1624 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz376 (Real.cos qz421)) (@HMul.hMul Real Real Real qz0 qz376 qz992) Bool.true 181545819741 1099511627776 24943038140799 209330521254133760 Bool.false 69423819027 1099511627776 24827878442769 209330521254133760 (@Enclosure.Real.IsNear.mulLit_ft qz376 (Real.cos qz421) 185363 1048576 1 1048576 979407 1048576 16694567 24954142720 181545819741 1099511627776 24943038140799 209330521254133760 qz620 (@Enclosure.Real.IsNear.recentre' (Real.cos qz421) Bool.true 979407 1048576 16694567 24954142720 979407 1048576 16694567 24954142720 (ep1621 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz376 qz992 185363 1048576 1 1048576 374529 1048576 16694567 24954142720 69423819027 1099511627776 24827878442769 209330521254133760 qz620 (@Enclosure.Real.IsNear.neg (Real.sin qz421) Bool.true 374529 1048576 16694567 24954142720 (@Enclosure.Real.IsNear.recentre' (Real.sin qz421) Bool.true 374529 1048576 16694567 24954142720 374529 1048576 16694567 24954142720 (ep1623 rfl rfl) rfl)) rfl)

noncomputable def ep1625 := @ep1616 133401692812083200000 0 1 ep1607 ep1608 ep1609 ep1611 (@Enclosure.Complex.IsNear.re_isNear qz78 Bool.true 181545819741 1099511627776 24943038140799 209330521254133760 Bool.false 69423819027 1099511627776 24827878442769 209330521254133760 (ep1617 ep1624))

noncomputable def ep1626 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz13 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1))))) Bool.false 67144946293586603281 133401692812083200000 0 1 Bool.false

noncomputable def ep1627 := @Enclosure.Complex.IsNear.addLitP qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) Bool.false 634828841 1272217682 0 1 Bool.true 161414400

noncomputable def ep1628 := @ep1627 636108841 0 1 Bool.false 909148841 209715200000 0 1 Bool.false 26006792546287 62914560000000 0 1 Bool.false 134289892587173206562 67144946293586603281 133401692812083200000 0 1 Bool.false 6387834711082062423367 6387834711082062423367 40020507843624960000000 0 1

noncomputable abbrev qz80 := (@HDiv.hDiv Complex Complex Complex qz346 qz609 (@HSub.hSub Complex Complex Complex qz595 qz384 (1 : Complex)))

noncomputable def ep1629 := @Enclosure.Complex.IsNear.addLitP qz80 qz24 Bool.true 64000000 63610884100 0 1 Bool.true 16141440000 63610884100 0 1

noncomputable def ep1630 := @Enclosure.Complex.IsNear.of_eq qz80 (Complex.mk (Enclosure.sfrac Bool.true 64000000 63610884100) (Enclosure.sfrac Bool.true 16141440000 63610884100)) Bool.true 64000000 63610884100 0 1 Bool.true 16141440000 63610884100 0 1

noncomputable def ep1631 := @ep1629 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 63482884100 634828841 1272217682 0 1 Bool.true 16141440000 161414400 636108841 0 1 (ep1630 (BSN.N_div_s_sub_one_mk qz61 126105 1000 32 (@Eq.refl Real qz61) rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 64000000 63610884100) (Enclosure.sfrac Bool.true 16141440000 63610884100) Bool.true 64000000 63610884100 0 1 Bool.true 16141440000 63610884100 0 1 (Enclosure.Real.IsNear.const Bool.true 64000000 63610884100) (Enclosure.Real.IsNear.const Bool.true 16141440000 63610884100))) qz351 rfl

noncomputable def ep1632 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz13 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) qz50)) Bool.false 909148841 209715200000 0 1

noncomputable def ep1633 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) qz50) Bool.false 1 768 0 1 Bool.false

noncomputable def ep1634 := @ep1633 8407 25600 0 1 Bool.false 1908246523 629145600000 0 1 Bool.false 5345749346287 62914560000000 0 1 Bool.false 2094678929664 909148841 209715200000 0 1 Bool.false 665773889184947200 26006792546287 62914560000000 0

noncomputable def ep1635 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz13 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) qz52)) Bool.false 1 768 0 1

noncomputable def ep1636 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) qz52) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1637 := @ep1636 0 1 0 1 Bool.false 1 768 0 1 Bool.false 8407 25600 0 1 Bool.false 1 1 768 0 1 Bool.false 8407 8407 25600 0

noncomputable def ep1638 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (Complex.mk qz262 qz262) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1639 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) qz52 Bool.false 1 768 0 1 Bool.false 8407 25600 0 1

noncomputable def ep1640 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz52)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz52)) 1 768 0 1 0 1 0

noncomputable def ep1641 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz52) 1 24 0 1 1 32 0 1 1

noncomputable def ep1642 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep1643 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep1644 := @ep1643 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep842) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 126105 1000 0 1 ep1262)

noncomputable def ep1645 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 126105 1000 0 1 0 1 0

noncomputable def ep1646 := @ep1645 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep842) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 126105 1000 0 1 ep1262)

noncomputable def ep1647 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)))) 8407 800 0 1 0 1 0 1 8407

noncomputable def ep1648 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 126105 1000 0 1 8407 800 0

noncomputable def ep1649 := @ep1648 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep842) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 126105 1000 0 1 ep1262)

noncomputable def ep1650 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep1651 := @ep1650 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep842) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 126105 1000 0 1 ep1262)

noncomputable def ep1652 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 8407 800 0 1 (@ep1642 1 24 0 1 (ep1644 rfl) (ep1646 rfl) rfl rfl) (@ep1647 8407 800 0 1 (ep1649 rfl) (ep1651 rfl) rfl rfl)

noncomputable def ep1653 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 8407 800 0 1 ep1652

noncomputable def ep1654 := @ep1641 768 0 1 ep1653 qz940

noncomputable def ep1655 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz52) 8407 800 0 1 0 1 0 1 0

noncomputable def ep1656 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 8407 800 0 1 ep1652

noncomputable def ep1657 := @ep1655 1 0 1 ep1656 qz941

noncomputable def ep1658 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz52)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz52)) 0 1 0 1 8407 25600 0

noncomputable def ep1659 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz52) 1 24 0 1 0 1 0 1 0

noncomputable def ep1660 := @ep1659 1 0 1 ep1653 qz941

noncomputable def ep1661 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz38)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz52) 8407 800 0 1 1 32 0 1 8407

noncomputable def ep1662 := @ep1661 25600 0 1 ep1656 qz940

noncomputable def ep1663 := @ep1637 1 (@ep1638 0 1 0 1 (BSN.bern_sum_base qz64 32) qz354) (ep1639 (@ep1640 1 1 1 768 0 1 (ep1654 rfl) (ep1657 rfl) rfl rfl) (@ep1658 1 8407 8407 25600 0 1 (ep1660 rfl) (ep1662 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep1664 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) qz50 Bool.false 1908246523 629145600000 0 1 Bool.false 5345749346287 62914560000000 0 1

noncomputable def ep1665 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.re qz50)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.im qz50)) 1908246523 629145600000 0 1 0 1 0

noncomputable def ep1666 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.re qz50) 1908246523 19200000 0 1 1 32768 0 1 1908246523

noncomputable def ep1667 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)))) 1908246523 19200000 0 1 0 1 0 1 1908246523

noncomputable def ep1668 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 5724739569 80000 0 1 1908246523 19200000 0

noncomputable def ep1669 := @ep1668 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep868) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 5724739569 80000 0 1 Bool.true 16037248038861 8000000 0 1 EMRow41.d20)

noncomputable def ep1670 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 16037248038861 8000000 0 1 0 1 0

noncomputable def ep1671 := @ep1670 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep868) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 5724739569 80000 0 1 Bool.true 16037248038861 8000000 0 1 EMRow41.d20)

noncomputable def ep1672 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)))) 5345749346287 1920000000 0 1 0 1 0 1 5345749346287

noncomputable def ep1673 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 16037248038861 8000000 0 1 5345749346287 1920000000 0

noncomputable def ep1674 := @ep1673 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep868) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 5724739569 80000 0 1 Bool.true 16037248038861 8000000 0 1 EMRow41.d20)

noncomputable def ep1675 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 5724739569 80000 0 1 0 1 0

noncomputable def ep1676 := @ep1675 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep868) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 5724739569 80000 0 1 Bool.true 16037248038861 8000000 0 1 EMRow41.d20)

noncomputable def ep1677 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 1908246523 19200000 0 1 Bool.false 5345749346287 1920000000 0 1 (@ep1667 1908246523 19200000 0 1 (ep1669 rfl) (ep1671 rfl) rfl rfl) (@ep1672 5345749346287 1920000000 0 1 (ep1674 rfl) (ep1676 rfl) rfl rfl)

noncomputable def ep1678 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 1908246523 19200000 0 1 Bool.false 5345749346287 1920000000 0 1 ep1677

noncomputable def ep1679 := @ep1666 629145600000 0 1 ep1678 qz942

noncomputable def ep1680 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.im qz50) 5345749346287 1920000000 0 1 0 1 0 1 0

noncomputable def ep1681 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 1908246523 19200000 0 1 Bool.false 5345749346287 1920000000 0 1 ep1677

noncomputable def ep1682 := @ep1680 1 0 1 ep1681 qz943

noncomputable def ep1683 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.im qz50)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.re qz50)) 0 1 0 1 5345749346287 62914560000000 0

noncomputable def ep1684 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.im qz50) 1908246523 19200000 0 1 0 1 0 1 0

noncomputable def ep1685 := @ep1684 1 0 1 ep1678 qz943

noncomputable def ep1686 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz35)) ↑qz49) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.re qz50) 5345749346287 1920000000 0 1 1 32768 0 1 5345749346287

noncomputable def ep1687 := @ep1686 62914560000000 0 1 ep1681 qz942

noncomputable def ep1688 := @ep1634 1 (@ep1635 Bool.false 8407 25600 0 1 (BSN.bern_sum_succ qz64 32 0 1 1 rfl rfl) (ep1663 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1664 (@ep1665 1 1908246523 1908246523 629145600000 0 1 (ep1679 rfl) (ep1682 rfl) rfl rfl) (@ep1683 1 5345749346287 5345749346287 62914560000000 0 1 (ep1685 rfl) (ep1687 rfl) rfl rfl)) rfl rfl rfl rfl

noncomputable def ep1689 := ep1628 (ep1631 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep1632 Bool.false 26006792546287 62914560000000 0 1 (BSN.bern_sum_succ qz64 32 1 2 3 rfl rfl) (ep1688 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep1690 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz78) (Complex.im (@HAdd.hAdd Complex Complex Complex qz13 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))))) 69423819027 1099511627776 24827878442769 209330521254133760 6387834711082062423367

noncomputable def ep1691 := @ep1690 40020507843624960000000 0 1 ep1612 ep1308 ep1613 ep1614 (@Enclosure.Complex.IsNear.im_isNear qz78 Bool.true 181545819741 1099511627776 24943038140799 209330521254133760 Bool.false 69423819027 1099511627776 24827878442769 209330521254133760 (ep1617 ep1624))

noncomputable def ep1692 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz13 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1))))) Bool.false 67144946293586603281 133401692812083200000 0 1 Bool.false

noncomputable def ep1693 := nat_lit 386561562997802306590365002762649

noncomputable def ep1694 := nat_lit 4085436021426657528975858361375647

noncomputable def ep1695 := @Enclosure.Real.IsNear.addLit_tf_p (@HMul.hMul Real Real Real qz0 (Complex.re qz78) (Complex.im (@HAdd.hAdd Complex Complex Complex qz13 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 (Complex.im qz78) (Complex.re (@HAdd.hAdd Complex Complex Complex qz13 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1))))))) ep1693 ep1308 ep1694

noncomputable def ep1696 := nat_lit 4661458600063590756931788427587

noncomputable def ep1697 := nat_lit 1667066564623421094160114466125089

noncomputable def ep1698 := nat_lit 11673163044826321333009433293112364355686265042540306838323200000

noncomputable def ep1699 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re qz78) (Complex.im (@HAdd.hAdd Complex Complex Complex qz13 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))))) 181545819741 1099511627776 24943038140799 209330521254133760 6387834711082062423367

noncomputable def ep1700 := @ep1699 40020507843624960000000 0 1 ep1693 ep1308 ep1694 ep1614 (@Enclosure.Complex.IsNear.re_isNear qz78 Bool.true 181545819741 1099511627776 24943038140799 209330521254133760 Bool.false 69423819027 1099511627776 24827878442769 209330521254133760 (ep1617 ep1624))

noncomputable def ep1701 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz78) (Complex.re (@HAdd.hAdd Complex Complex Complex qz13 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz26 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz26 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz46 qz47 (@HSub.hSub Nat Nat Nat qz45 (@HMul.hMul Nat Nat Nat qz26 2 k) 1)))))) 69423819027 1099511627776 24827878442769 209330521254133760 67144946293586603281

noncomputable def ep1702 := @ep1701 133401692812083200000 0 1 ep1696 ep1608 ep1697 ep1611 (@Enclosure.Complex.IsNear.im_isNear qz78 Bool.true 181545819741 1099511627776 24943038140799 209330521254133760 Bool.false 69423819027 1099511627776 24827878442769 209330521254133760 (ep1617 ep1624))

noncomputable abbrev qz994 := (ep1689 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep1703 := @ep1606 ep1501 ep1308 ep1502 ep1310 (@ep1610 ep1611 ep1612 ep1308 ep1613 ep1614 ep1615 ep1499 ep1308 ep1500 ep1310 (ep1625 (@ep1626 6387834711082062423367 40020507843624960000000 0 1 qz994) rfl) (ep1691 (@ep1692 6387834711082062423367 40020507843624960000000 0 1 qz994) rfl) rfl rfl) (@ep1695 ep1614 ep1696 ep1608 ep1697 ep1611 ep1698 ep1501 ep1308 ep1502 ep1310 (ep1700 (@ep1692 6387834711082062423367 40020507843624960000000 0 1 qz994) rfl) (ep1702 (@ep1626 6387834711082062423367 40020507843624960000000 0 1 qz994) rfl) rfl rfl)

noncomputable def ep1704 := @ep1505 ep1496 ep1310 (@ep1506 104665260627066880 (BSN.head_sum_c_eq qz64 32) (ep1507 (BSN.head_sum_c_succ qz64 31 32 rfl rfl) (ep1605 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep1703 rfl rfl rfl

noncomputable def ep1705 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz64 2 32) Bool.false ep1307 ep1308 ep1309 ep1310 Bool.false ep1495 ep1308 ep1496 ep1310 (@ep1497 ep1310 Bool.false ep1495 ep1308 ep1496 ep1310 (BSN.zetaApproximant_eq_folded' qz64 2 32 rfl) (ep1704 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep1706 := @Enclosure.Real.IsNear.mulLit_ff (Real.sin (@HSub.hSub Real Real Real qz597 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz410)) (Complex.im (zetaApproximant qz64 2 32)) 363 524288 34983973

noncomputable def ep1707 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz597 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz410)) Bool.false 726 1048576 34983973

noncomputable def ep1708 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz597 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz410) qz974 Bool.false 131768673 1048576 181

noncomputable def ep1709 := BSN.sin_dyadic_bound_f 1488213 2147483648 1 0 1048576 381142 0 1 1 0 1 1 726 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 1488213) qz272 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 1488213) qz273 0 0 rfl) rfl rfl

noncomputable def ep1710 := @ep1708 524288 Bool.false 726 1048576 1 190385 (@ep1317 131768673 1048576 181 524288 ep1492 rfl) (Enclosure.sfrac_false_div 131768673 1048576) (BSN.sin_reduce0 qz974 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 104723719259429011456) qz271) 226375608064910080 72057594037927936 Bool.false 726 1048576 20 1000000000000000 380770 190385 (BSN.sin_reduce_arg_pos_rat_q0 131768673 1048576 226375608064910080 72057594037927936 20 104723719259429011456 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 726 1048576 104723719259429011456 151115727451828646838272 1488213 2147483648 381142 380770 (ep1709 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1711 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz64 2 32) Bool.false ep1307 ep1308 ep1309 ep1310 Bool.false ep1495 ep1308 ep1496 ep1310 (@ep1497 ep1310 Bool.false ep1495 ep1308 ep1496 ep1310 (BSN.zetaApproximant_eq_folded' qz64 2 32 rfl) (ep1704 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow41.d21 : Enclosure.Real.IsNear (hardyZApproximantEM 2 32 qz61) Bool.false ep1291 ep1292 ep1293 ep1294 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 2 32 qz61) ep1295 Bool.false ep1291 ep1292 ep1293 ep1294 (@Eq.refl Real ep1295) (@ep1296 Bool.false ep1291 ep1292 ep1293 ep1294 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz597 (Complex.im (@HSub.hSub Complex Complex Complex qz20 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz13 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz410) (zetaApproximant qz64 2 32)) (@ep1298 ep1299 ep1300 ep1294 ep1301 ep1302 ep1303 ep1304 ep1305 ep1291 ep1292 ep1293 ep1294 (@ep1306 99816570880 ep1307 ep1308 ep1309 ep1310 ep1297 ep1299 ep1300 ep1294 (@ep1311 99816570880 1048575 1048576 34983973 99816570880 (ep1494 rfl rfl) rfl) ep1705 rfl) (@ep1706 99816570880 ep1495 ep1308 ep1496 ep1310 ep1301 ep1302 ep1303 ep1304 (@ep1707 99816570880 363 524288 34983973 99816570880 (ep1710 rfl rfl) rfl) ep1711 rfl) rfl rfl))

theorem EMRow41.d22 : @Eq Nat (Nat.mul (BSN.factNat (Nat.succ (Nat.mul 2 2))) (Nat.pow 4 (Nat.mul 2 2))) 30720 := @Eq.refl Nat 30720

theorem EMRow41.d23 : @Eq Nat (Nat.mul (Nat.mul 2 2) (Nat.pow (Nat.succ (Nat.mul 4 4)) (Nat.mul 2 2))) 334084 := @Eq.refl Nat 334084

theorem EMRow41.d177 : @Eq Nat (TangentNumbers.tangentNumber 3) 16 := Height20.tangent_three

noncomputable abbrev qz232 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 3)

theorem EMRow41.d178 : @Eq Real (@Rat.cast Real Real.instRatCast (bernoulli qz232)) (Enclosure.sfrac Bool.false 1 42) := BSN.bern_real_tangent_pos 2 16 1 42 EMRow41.d177 rfl rfl rfl

theorem EMRow41.d179 : @Eq Nat (BSN.factNat (Nat.mul 2 3)) 720 := @Eq.refl Nat 720

theorem EMRow41.d180 : @Eq Nat (Nat.pow 32 (Nat.succ (Nat.mul 2 5))) 36028797018963968 := @Eq.refl Nat 36028797018963968

noncomputable def ep1845 := nat_lit 1181671153346359170692730265957638242378174781758650

noncomputable def ep1846 := nat_lit 5986310706507378352962293074805895248510699696029696

noncomputable def ep1847 := nat_lit 2000000000000000000000000000000000000000000000000000

noncomputable def ep1848 := nat_lit 1499028120395240233173640088155429295548437777754679499662777369540625

noncomputable def ep1849 := nat_lit 4680297997409431328241185462095581837349556053595733828842639923095703125

noncomputable def ep1850 := nat_lit 13442882392639581675476766202062253719655739830178303899086159055189875

noncomputable def ep1851 := nat_lit 19584239746202378791298717228947477708711488730841665528714656829833984375

noncomputable def ep1852 := nat_lit 2442358029135994033939875

noncomputable def ep1853 := nat_lit 37260822860694382775919147000

noncomputable def ep1854 := nat_lit 116336546489037573337554931640625

noncomputable def ep1855 := nat_lit 57493278893883548332405996866302358825

noncomputable def ep1856 := nat_lit 40230676762013536063022911548614501953125

noncomputable def ep1857 := nat_lit 236310350532676991248348623960

noncomputable def ep1858 := nat_lit 344268321641720831394195556640625

noncomputable def ep1859 := nat_lit 81801971833623620377505564448994707675

noncomputable def ep1860 := nat_lit 56886557708273976459167897701263427734375

noncomputable def ep1861 := BSN.arctan_dyadic_bound_f 1 5 18 17 ep1846 ep1847 ep1848 ep1849 200200021673987500790625 ep1850 ep1851 ep1852 ep1845 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 17 8 ep1853 ep1854 151412625 ep1855 ep1856 1322214852783825 ep1848 ep1849 200200021673987500790625 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 8 ep1853 ep1854 151412625 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 8 17 ep1855 ep1856 1322214852783825 rfl rfl rfl rfl)) (@BSN.binarySplit_rec (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 17 8 ep1857 ep1858 1267389585 ep1859 ep1860 1927077560082675 ep1850 ep1851 ep1852 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 8 ep1857 ep1858 1267389585 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 8 17 ep1859 ep1860 1927077560082675 rfl rfl rfl rfl)) rfl

theorem EMRow41.d181 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz265 qz561)) Bool.false ep1845 ep1846 1 ep1847 := ep1861 rfl rfl rfl

noncomputable def ep1862 := nat_lit 25047178968060507272880539293402373975644382030403

noncomputable def ep1863 := nat_lit 4733915408010924740926662591654183582145509

noncomputable def ep1864 := nat_lit 77229300481955664312677298336960122659119574530232845

noncomputable def ep1865 := nat_lit 24516194103503660983641551147684725335332607

noncomputable def ep1866 := nat_lit 186647183216068817672719845704257068688983305564016735

noncomputable def ep1867 := BSN.arctan_dyadic_bound_f 1 239 6 5 ep1846 ep1847 ep1863 ep1864 9945 ep1865 ep1866 65835 ep1862 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 239) 0 5 ep1863 ep1864 9945 rfl rfl rfl rfl) (@BSN.binarySplit_of_base5 (BSN.arctanOddP 1) (BSN.arctanOddQ 239) 0 5 ep1865 ep1866 65835 rfl rfl rfl rfl) rfl rfl rfl

theorem EMRow41.d182 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz265 (@Nat.cast Real Real.instNatCast 239))) Bool.false ep1862 ep1846 1 ep1847 := ep1867 rfl

noncomputable def ep1868 := nat_lit 18806549737669504701992162098148602382148218980016788

noncomputable def ep1869 := nat_lit 100000000000000000000000000000000000000000000000000

theorem EMRow41.d183 : Enclosure.Real.IsNear Real.pi Bool.false ep1868 ep1846 1 ep1869 := BSN.pi_combine ep1845 ep1862 ep1846 ep1847 ep1869 ep1868 rfl rfl rfl rfl EMRow41.d181 EMRow41.d182

noncomputable def ep1870 := nat_lit 3913763998985653921324077

noncomputable def ep1871 := nat_lit 33895191259166500131438592

noncomputable def ep1872 := nat_lit 8473797814791625032859648

noncomputable abbrev qz536 := (@HAdd.hAdd Complex Complex Complex qz549 (@HAdd.hAdd Complex Complex Complex qz549 qz550 (@HMul.hMul Complex Complex Complex qz545 Complex.I ↑(Enclosure.sfrac Bool.false 124004 1000))) (@Nat.cast Complex Complex.instNatCast 5))

noncomputable abbrev qz233 := (@Norm.norm Complex Complex.instNorm qz536)

noncomputable abbrev qz234 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 3)))

noncomputable abbrev qz235 := (@HPow.hPow Complex Complex Complex (@instHPow Complex Complex Complex.instPow) qz609 (@HSub.hSub Complex Complex Complex qz595 (@Neg.neg Complex Complex.instNeg qz259) (@Nat.cast Complex Complex.instNatCast 5)))

noncomputable abbrev qz790 := (@HDiv.hDiv Real Real Real qz1 qz233 (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (Complex.re qz12) (@Nat.cast Real Real.instNatCast 5)))

noncomputable def ep1873 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 2 4) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz12 2 32))) (@HMul.hMul Real Real Real qz0 qz790 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235))) 612594885 22419997720576 17779125 44839995441152 46848551389312750317 405828369621610135552 2227089510157

noncomputable def ep1874 := nat_lit 1050593023744097547828816733274112

noncomputable def ep1875 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 2 4) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz12 2 32)) 10095 171051008 15 171051008 60683 131072 3157 524288 612594885 22419997720576

noncomputable abbrev qz537 := (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid)))

noncomputable abbrev qz538 := (@HMul.hMul Real Real Real qz0 (2 : Real) Real.pi)

noncomputable abbrev qz1120 := (@Inv.inv Real Real.instInv (@HPow.hPow Real Nat Real qz537 qz538 4))

noncomputable def ep1876 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 30720 334084) qz1120 30720 334084 0 1 673 1048576 1 1048576 10095 171051008 15 171051008

noncomputable def ep1877 := nat_lit 611446774371975769155682509262542103857872115376664175900625

noncomputable def ep1878 := nat_lit 392318858461667547739736838950479151006397215279002157056

noncomputable def ep1879 := nat_lit 19652562622312316682495810535216024035134795670488584765154486969712234385047

noncomputable def ep1880 := nat_lit 9903520314283042199192993792000000000000000000000000000000000000000000000000000000000000

noncomputable def ep1881 := nat_lit 691463075802508163054686763366652189853178875

noncomputable def ep1882 := nat_lit 2787593149816327892691964784081045188247552

noncomputable def ep1883 := nat_lit 2184744797947834540264818678394244808492865883128339

noncomputable def ep1884 := nat_lit 9223372036854775808000000000000000000000000000000000000000000000

noncomputable def ep1885 := @Enclosure.Real.IsNear.mulLit_ff (@HPow.hPow Real Nat Real qz537 qz538 3) qz538 ep1881 ep1882 ep1883 ep1884 884279719003555 140737488355328 1 500000000000000 ep1877 ep1878 ep1879 ep1880

noncomputable def ep1886 := nat_lit 781950621441006189802102638025

noncomputable def ep1887 := nat_lit 19807040628566084398385987584

noncomputable def ep1888 := nat_lit 26986075409044041160201671

noncomputable def ep1889 := nat_lit 1073741824000000000000000000000000000000

noncomputable def ep1890 := @Enclosure.Real.IsNear.mulLit_ff (@HPow.hPow Real Nat Real qz537 qz538 2) qz538 ep1886 ep1887 ep1888 ep1889 884279719003555 140737488355328 1 500000000000000 ep1881 ep1882 ep1883 ep1884

noncomputable def ep1891 := @Enclosure.Real.IsNear.mulLit_ff (@HPow.hPow Real Nat Real qz537 qz538 1) qz538 884279719003555 140737488355328 1 500000000000000 884279719003555 140737488355328 1 500000000000000 ep1886 ep1887 ep1888 ep1889

noncomputable abbrev qz539 := (@Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 (2 : Real) Real.pi) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 2 1) Real.pi) Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 2 1) Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) BSN.pi_near_15 rfl))

noncomputable def ep1892 := ep1891 (@Enclosure.Real.IsNear.of_eq (@HPow.hPow Real Nat Real qz537 qz538 1) qz538 Bool.false 884279719003555 140737488355328 1 500000000000000 (BSN.pow_one_r qz538) qz539) qz539 rfl

noncomputable def ep1893 := @Enclosure.Real.IsNear.of_eq (@HPow.hPow Real Nat Real qz537 qz538 3) (@HMul.hMul Real Real Real qz0 (@HPow.hPow Real Nat Real qz537 qz538 2) qz538) Bool.false ep1881 ep1882 ep1883 ep1884 (BSN.pow_succ_r qz538 2 3 rfl) (ep1890 (@Enclosure.Real.IsNear.of_eq (@HPow.hPow Real Nat Real qz537 qz538 2) (@HMul.hMul Real Real Real qz0 (@HPow.hPow Real Nat Real qz537 qz538 1) qz538) Bool.false ep1886 ep1887 ep1888 ep1889 (BSN.pow_succ_r qz538 1 2 rfl) ep1892) qz539 rfl)

noncomputable def ep1894 := @Enclosure.Real.IsNear.inv_image (@HPow.hPow Real Nat Real qz537 qz538 4) ep1877 ep1878 ep1879 ep1880 336 337 524288 (@Enclosure.Real.IsNear.of_eq (@HPow.hPow Real Nat Real qz537 qz538 4) (@HMul.hMul Real Real Real qz0 (@HPow.hPow Real Nat Real qz537 qz538 3) qz538) Bool.false ep1877 ep1878 ep1879 ep1880 (BSN.pow_succ_r qz538 3 4 rfl) (ep1885 ep1893 qz539 rfl))

noncomputable def ep1895 := ep1876 (Enclosure.Real.IsNear.const Bool.false 30720 334084) (@Enclosure.Real.IsNear.recentre' qz1120 Bool.false 673 1048576 1 1048576 673 1048576 1 1048576 (ep1894 rfl rfl rfl rfl rfl rfl) rfl)

noncomputable def ep1896 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz12 2 32)) (Real.sqrt (@HAdd.hAdd Real Real Real qz607 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz12 2 32)) (Complex.re (zetaApproximant qz12 2 32))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz12 2 32)) (Complex.im (zetaApproximant qz12 2 32))))) Bool.false 60683 131072 3157 524288

noncomputable def ep1897 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz607 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz12 2 32)) (Complex.re (zetaApproximant qz12 2 32))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz12 2 32)) (Complex.im (zetaApproximant qz12 2 32))))) Bool.false 485464 1048576 6314 1048576

noncomputable def ep1898 := nat_lit 132224368095622049915198677999209736062328921200223014863017

noncomputable def ep1899 := nat_lit 616769756166566021758012758996236736921600000000000000000000

noncomputable def ep1900 := nat_lit 59892598409387662856464147926945517367802573266383470385327220425310362426591

noncomputable def ep1901 := nat_lit 10742787804952701915970578425567046985290994970018269102080000000000000000000000

noncomputable def ep1902 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz607 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz12 2 32)) (Complex.re (zetaApproximant qz12 2 32))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz12 2 32)) (Complex.im (zetaApproximant qz12 2 32)))) ep1898 ep1899 ep1900 ep1901 239575 245889

noncomputable def ep1903 := nat_lit 127049136733548943632258158682164293708363794342849451725136811176801

noncomputable def ep1904 := nat_lit 592763613045162132763455248893813346054597876121600000000000000000000

noncomputable def ep1905 := nat_lit 117295363231475335023688424065106078267715076650044952637988877066325250292131

noncomputable def ep1906 := nat_lit 21485575609905403831941156851134093970581989940036538204160000000000000000000000

noncomputable def ep1907 := nat_lit 28745055141637093494488087654629302505873275401954069974282380841

noncomputable def ep1908 := nat_lit 829944529099996896413290596261652155963356627573996044221854594765158187017

noncomputable def ep1909 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz12 2 32)) (Complex.re (zetaApproximant qz12 2 32))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz12 2 32)) (Complex.im (zetaApproximant qz12 2 32))) ep1903 ep1904 ep1905 ep1906 ep1907 ep1904 ep1908

noncomputable def ep1910 := nat_lit 7161858536635134610647052283711364656860663313345512734720000000000000000000000

noncomputable def ep1911 := nat_lit 75327144347190239338704817027367098626783560557789384719592544960206672112103884218181069552497567727102045745001267200000000000000000000

noncomputable def ep1912 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz12 2 32)) (Complex.re (zetaApproximant qz12 2 32)) ep483 ep484 ep485 ep486 ep483 ep484 ep485 ep486 ep1903

noncomputable def ep1913 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (zetaApproximant qz12 2 32)) (Complex.im (zetaApproximant qz12 2 32)) ep687 ep484 ep688 ep486 ep687 ep484 ep688 ep486 ep1907

noncomputable def ep1914 := @ep1873 101457092405402533888 ep1874 ep1870 ep1871 3545882201743646797 ep1872 (@ep1875 17779125 44839995441152 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 2 4) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 30720 334084) qz1120) Bool.false 10095 171051008 15 171051008 (BSN.theta_err_eq 2 4 30720 334084 EMRow41.d22 EMRow41.d23 rfl) (ep1895 rfl)) (ep1896 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz12 2 32)) (@ep1897 60683 131072 3157 524288 (@ep1902 524288 (@ep1909 ep1910 ep1911 ep1898 ep1899 ep1900 ep1901 (@ep1912 ep1904 ep1905 ep1906 ep908 ep908 rfl) (@ep1913 ep1904 ep1908 ep1910 ep914 ep914 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable def ep1915 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz790 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz233 (Enclosure.sfrac Bool.false 2 11)) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235))) Bool.false 46848551389312750317 405828369621610135552 2227089510157 101457092405402533888 (BSN.zrb_shape_eq qz233 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235)) qz9 5)

noncomputable def ep1916 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz233 (Enclosure.sfrac Bool.false 2 11)) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235)) 130155453 5767168 1 5767168 359943055089 70368744177664 131357 140737488355328

noncomputable def ep1917 := @Enclosure.Real.IsNear.mulLit_ff qz233 (Enclosure.sfrac Bool.false 2 11) 130155453 1048576 1 1048576 2 11 0 1 130155453 5767168

noncomputable abbrev qz236 := (Complex.re qz536)

noncomputable abbrev qz237 := (Complex.im qz536)

noncomputable abbrev qz238 := qz536

noncomputable abbrev qz1121 := (@HAdd.hAdd Real Real Real qz607 (@HMul.hMul Real Real Real qz0 qz236 qz236) (@HMul.hMul Real Real Real qz0 qz237 qz237))

noncomputable def ep1918 := @Enclosure.Real.IsNear.of_eq qz233 (Real.sqrt qz1121) Bool.false 130155453 1048576 1 1048576 (BSN.norm_eq_sqrt_mul_add qz238)

noncomputable def ep1919 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz1121) Bool.false 130155453 1048576 1 1048576 130155453

noncomputable def ep1920 := @Enclosure.Real.IsNear.sqrt_image qz1121 481476313 31250 0 1 65077726 65077727 524288

noncomputable def ep1921 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz236 qz236) (@HMul.hMul Real Real Real qz0 qz237 qz237) 121 4 0 1 961062001 62500 0 1

noncomputable def ep1922 := @Enclosure.Real.IsNear.mulLit_ff qz236 qz236 11 2 0 1 11 2 0 1 121 4

noncomputable def ep1923 := @Enclosure.Complex.IsNear.of_eq qz238 (Complex.mk (Enclosure.sfrac Bool.false 11 2) qz9) Bool.false 11 2 0 1 Bool.false 124004 1000 0 1 (BSN.s_add_nat_mk qz9 Bool.false 124004 1000 5 (@Eq.refl Real qz9))

noncomputable abbrev qz791 := (ep1923 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 11 2) qz9 Bool.false 11 2 0 1 Bool.false 124004 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 11 2) qz270))

noncomputable def ep1924 := @ep1922 0 1 (@Enclosure.Complex.IsNear.re_isNear qz238 Bool.false 11 2 0 1 Bool.false 124004 1000 0 1 qz791)

noncomputable def ep1925 := ep1924 (@Enclosure.Complex.IsNear.re_isNear qz238 Bool.false 11 2 0 1 Bool.false 124004 1000 0 1 qz791)

noncomputable def ep1926 := @Enclosure.Real.IsNear.mulLit_ff qz237 qz237 124004 1000 0 1 124004 1000 0 1 961062001 62500

noncomputable def ep1927 := @ep1926 0 1 (@Enclosure.Complex.IsNear.im_isNear qz238 Bool.false 11 2 0 1 Bool.false 124004 1000 0 1 qz791)

noncomputable def ep1928 := ep1927 (@Enclosure.Complex.IsNear.im_isNear qz238 Bool.false 11 2 0 1 Bool.false 124004 1000 0 1 qz791)

noncomputable def ep1929 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235)) (Real.sqrt (@HAdd.hAdd Real Real Real qz607 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235)) (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235)) (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235))))) Bool.false 359943055089 70368744177664

noncomputable def ep1930 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz607 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235)) (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235)) (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235))))) Bool.false 5759088881424 1125899906842624

noncomputable def ep1931 := nat_lit 5846079802052660841218023970015132795374119830906183769688149237750767094900257050021

noncomputable def ep1932 := nat_lit 223437849858246595548646996558515078971612164014369197260800000000000000000000000000000000

noncomputable def ep1933 := nat_lit 3789179720294718713103487351894249042324491456650415963560607474854968115515431436267593461

noncomputable def ep1934 := nat_lit 396842594363220681926990892648438529648490000838625021962871552081920000000000000000000000000000000000

noncomputable def ep1935 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz607 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235)) (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235)) (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235)))) ep1931 ep1932 ep1933 ep1934

noncomputable def ep1936 := nat_lit 3011606629349433448304268198962101055693421386780557657557021383797988087432487875761

noncomputable def ep1937 := nat_lit 446875699716493191097293993117030157943224328028738394521600000000000000000000000000000000

noncomputable def ep1938 := nat_lit 2379978056873559624854940433369354160632095421602900554786872086483186454913239461836300111

noncomputable def ep1939 := nat_lit 793685188726441363853981785296877059296980001677250043925743104163840000000000000000000000000000000000

noncomputable def ep1940 := nat_lit 8680552974755888234131779741068164535054818275031809881819277091703546102368026224281

noncomputable def ep1941 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235)) (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235)) (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235))) ep1936 ep1937 ep1938 ep1939 ep1940

noncomputable def ep1942 := nat_lit 5198381383715877801352034270419143924016887491697931372334342863226749776117623410698886811

noncomputable def ep1943 := nat_lit 5224942004281481642022760474373668883202043259627597557635930050799341177462218174164933344715197952944206149047483054633198410785510567129907200000000000000000000000000000000

noncomputable def ep1944 := nat_lit 1735398118400914208016772782040202978495431

noncomputable def ep1945 := nat_lit 668487621214105348445527080960000000000000000

noncomputable def ep1946 := nat_lit 514532744750147931811360737864112965638899

noncomputable def ep1947 := nat_lit 890890110353932127346611713159987200000000000000000

noncomputable def ep1948 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235)) (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235)) ep1944 ep1945 ep1946 ep1947 ep1944 ep1945 ep1946

noncomputable def ep1949 := nat_lit 2946277816967688509588153293395876943094341

noncomputable def ep1950 := nat_lit 661962888287527779181106662073641513709599

noncomputable def ep1951 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235) Bool.false ep1944 ep1945 ep1946 ep1947 Bool.true ep1949 ep1945 ep1950

noncomputable def ep1952 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235 Bool.false ep1944 ep1945 ep1946 ep1947 Bool.true ep1949 ep1945 ep1950 ep1947

noncomputable def ep1953 := nat_lit 29583388480804782993880074764074011947

noncomputable def ep1954 := nat_lit 71305346262837903834189555302400000000000

noncomputable def ep1955 := nat_lit 65809166522939080064863703275571483

noncomputable def ep1956 := nat_lit 940874043938146141092131182215168000000000000

noncomputable def ep1957 := nat_lit 503185596352114762146099620738349210124639

noncomputable def ep1958 := nat_lit 167121905303526337111381770240000000000000000

noncomputable def ep1959 := nat_lit 7796891210323103282326602048707865821953

noncomputable def ep1960 := @Enclosure.Real.IsNear.subLit_tt_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.re qz235)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.im qz235)) ep1953 ep1954 ep1955 ep1956 ep1957 ep1958 ep1959

noncomputable def ep1961 := nat_lit 15360174316447105643907098502758400000000000000000

noncomputable def ep1962 := nat_lit 30935790934113639519311236351568482983473963881680045787732134030055833600000000000

noncomputable def ep1963 := nat_lit 633825300114114700748351602688

noncomputable def ep1964 := nat_lit 120670829762225727301974919877754880

noncomputable def ep1965 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.re qz235) 230767387107886469 2362500000000 0 1 2692109859555060160923 ep1963 86408125976346361521 ep1964 ep1953

noncomputable def ep1966 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5)))) 230767387107886469 2362500000000 0 1 0 1 0 1 230767387107886469

noncomputable def ep1967 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) 1 30240 0 1 230767387107886469 78125000 0 1 230767387107886469 2362500000000 0

noncomputable def ep1968 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (Complex.mk (Enclosure.sfrac Bool.false 1 30240) qz262) Bool.false 1 30240 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 3 1 42 720 Bool.false EMRow41.d178 EMRow41.d179 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 30240) qz262 Bool.false 1 30240 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 30240) qz274)

noncomputable abbrev qz239 := (@HAdd.hAdd Complex Complex Complex qz260 qz259 qz261)

noncomputable def ep1969 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5)) (@HMul.hMul Complex Complex Complex qz3 (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 4)) qz239) Bool.false 230767387107886469 78125000 0 1 Bool.false 7131677479731368925469 244140625000 0 1

noncomputable def ep1970 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.re qz239)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.im qz239)) 2075284728758353221 1953125000 0 1 461737493617351063 244140625 0 1

noncomputable def ep1971 := nat_lit 1408492352953408624267578125

noncomputable def ep1972 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.re qz239) 230587192084261469 976562500 0 1 9 2 0 1 2075284728758353221 1953125000

noncomputable abbrev qz240 := (@HAdd.hAdd Complex Complex Complex qz260 qz259 qz552)

noncomputable def ep1973 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 4)) (@HMul.hMul Complex Complex Complex qz3 (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)) qz240) Bool.false 230587192084261469 976562500 0 1 Bool.true 29788554796126 1953125 0 1

noncomputable def ep1974 := @Enclosure.Real.IsNear.subLit_tt_p (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.re qz240)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.im qz240)) 30272632719 125000 0 1 461647394054757313 1953125000 0 1

noncomputable def ep1975 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.re qz240) 4324661817 62500 0 1 7 2 0 1 30272632719 125000

noncomputable abbrev qz792 := (ep431 (BSN.ascPochhammer_succ_eval_c 2 3 qz12 rfl) (ep459 (@ep460 744568552715650 14891371054313 7812500 0 1 (ep463 rfl) (ep466 rfl) rfl rfl)))

noncomputable def ep1976 := @ep1975 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 4324661817 62500 0 1 Bool.true 14891371054313 7812500 0 1 qz792)

noncomputable def ep1977 := @Enclosure.Complex.IsNear.of_eq qz240 (Complex.mk (Enclosure.sfrac Bool.false 7 2) qz9) Bool.false 7 2 0 1 Bool.false 124004 1000 0 1 (BSN.s_add_nat_mk qz9 Bool.false 124004 1000 3 (@Eq.refl Real qz9))

noncomputable abbrev qz793 := (ep1977 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz9 Bool.false 7 2 0 1 Bool.false 124004 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz270))

noncomputable def ep1978 := ep1976 (@Enclosure.Complex.IsNear.re_isNear qz240 Bool.false 7 2 0 1 Bool.false 124004 1000 0 1 qz793)

noncomputable def ep1979 := @Enclosure.Real.IsNear.mulLit_tf (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.im qz240) 14891371054313 7812500 0 1 124004 1000 0 1 461647394054757313 1953125000

noncomputable def ep1980 := @ep1979 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 4324661817 62500 0 1 Bool.true 14891371054313 7812500 0 1 qz792)

noncomputable def ep1981 := ep1980 (@Enclosure.Complex.IsNear.im_isNear qz240 Bool.false 7 2 0 1 Bool.false 124004 1000 0 1 qz793)

noncomputable def ep1982 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)) qz240 Bool.false 230587192084261469 976562500 0 1 Bool.true 29788554796126 1953125 0 1 (@ep1974 57646798021065367250000 230587192084261469 976562500 0 1 (ep1978 rfl) (ep1981 rfl) rfl rfl)

noncomputable def ep1983 := @Enclosure.Real.IsNear.addLit_tt (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.im qz240)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.re qz240)) 134068840988817 15625000 0 1 104239597380191 15625000 0 1

noncomputable def ep1984 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.im qz240) 4324661817 62500 0 1 124004 1000 0 1 134068840988817 15625000

noncomputable def ep1985 := @ep1984 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 4324661817 62500 0 1 Bool.true 14891371054313 7812500 0 1 qz792)

noncomputable def ep1986 := ep1985 (@Enclosure.Complex.IsNear.im_isNear qz240 Bool.false 7 2 0 1 Bool.false 124004 1000 0 1 qz793)

noncomputable def ep1987 := @Enclosure.Real.IsNear.mulLit_tf (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.re qz240) 14891371054313 7812500 0 1 7 2 0 1 104239597380191 15625000

noncomputable def ep1988 := @ep1987 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 4324661817 62500 0 1 Bool.true 14891371054313 7812500 0 1 qz792)

noncomputable def ep1989 := ep1988 (@Enclosure.Complex.IsNear.re_isNear qz240 Bool.false 7 2 0 1 Bool.false 124004 1000 0 1 qz793)

noncomputable abbrev qz794 := (ep1973 (BSN.ascPochhammer_succ_eval_c 3 4 qz12 rfl) (ep1982 (@ep1983 3723569349515750000000 29788554796126 1953125 0 1 (ep1986 rfl) (ep1989 rfl) rfl rfl)))

noncomputable def ep1990 := @ep1972 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 4)) Bool.false 230587192084261469 976562500 0 1 Bool.true 29788554796126 1953125 0 1 qz794)

noncomputable def ep1991 := @Enclosure.Complex.IsNear.of_eq qz239 (Complex.mk (Enclosure.sfrac Bool.false 9 2) qz9) Bool.false 9 2 0 1 Bool.false 124004 1000 0 1 (BSN.s_add_nat_mk qz9 Bool.false 124004 1000 4 (@Eq.refl Real qz9))

noncomputable abbrev qz795 := (ep1991 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9 2) qz9 Bool.false 9 2 0 1 Bool.false 124004 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 9 2) qz270))

noncomputable def ep1992 := ep1990 (@Enclosure.Complex.IsNear.re_isNear qz239 Bool.false 9 2 0 1 Bool.false 124004 1000 0 1 qz795)

noncomputable def ep1993 := @Enclosure.Real.IsNear.mulLit_tf (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.im qz239) 29788554796126 1953125 0 1 124004 1000 0 1 461737493617351063 244140625

noncomputable def ep1994 := @ep1993 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 4)) Bool.false 230587192084261469 976562500 0 1 Bool.true 29788554796126 1953125 0 1 qz794)

noncomputable def ep1995 := ep1994 (@Enclosure.Complex.IsNear.im_isNear qz239 Bool.false 9 2 0 1 Bool.false 124004 1000 0 1 qz795)

noncomputable def ep1996 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 4)) qz239 Bool.false 230767387107886469 78125000 0 1 Bool.false 7131677479731368925469 244140625000 0 1 (@ep1970 ep1971 230767387107886469 78125000 0 1 (ep1992 rfl) (ep1995 rfl) rfl rfl)

noncomputable def ep1997 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.im qz239)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.re qz239)) 7148433541804189800469 244140625000 0 1 134048496582567 1953125 0 1

noncomputable def ep1998 := nat_lit 13929057577600329932556640625

noncomputable def ep1999 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.im qz239) 230587192084261469 976562500 0 1 124004 1000 0 1 7148433541804189800469 244140625000

noncomputable def ep2000 := @ep1999 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 4)) Bool.false 230587192084261469 976562500 0 1 Bool.true 29788554796126 1953125 0 1 qz794)

noncomputable def ep2001 := ep2000 (@Enclosure.Complex.IsNear.im_isNear qz239 Bool.false 9 2 0 1 Bool.false 124004 1000 0 1 qz795)

noncomputable def ep2002 := @Enclosure.Real.IsNear.mulLit_tf (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.re qz239) 29788554796126 1953125 0 1 9 2 0 1 134048496582567 1953125

noncomputable def ep2003 := @ep2002 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 4)) Bool.false 230587192084261469 976562500 0 1 Bool.true 29788554796126 1953125 0 1 qz794)

noncomputable def ep2004 := ep2003 (@Enclosure.Complex.IsNear.re_isNear qz239 Bool.false 9 2 0 1 Bool.false 124004 1000 0 1 qz795)

noncomputable abbrev qz796 := (ep1969 (BSN.ascPochhammer_succ_eval_c 4 5 qz12 rfl) (ep1996 (@ep1997 ep1998 7131677479731368925469 244140625000 0 1 (ep2001 rfl) (ep2004 rfl) rfl rfl)))

noncomputable def ep2005 := @ep1967 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) Bool.false 1 30240 0 1 Bool.false 0 1 0 1 ep1968) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5)) Bool.false 230767387107886469 78125000 0 1 Bool.false 7131677479731368925469 244140625000 0 1 qz796)

noncomputable def ep2006 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) 0 1 0 1 7131677479731368925469 244140625000 0 1 0 1 0

noncomputable def ep2007 := @ep2006 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) Bool.false 1 30240 0 1 Bool.false 0 1 0 1 ep1968) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5)) Bool.false 230767387107886469 78125000 0 1 Bool.false 7131677479731368925469 244140625000 0 1 qz796)

noncomputable def ep2008 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5)))) 7131677479731368925469 7382812500000000 0 1 0 1 0 1 7131677479731368925469

noncomputable def ep2009 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) 1 30240 0 1 7131677479731368925469 244140625000 0 1 7131677479731368925469 7382812500000000 0

noncomputable def ep2010 := @ep2009 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) Bool.false 1 30240 0 1 Bool.false 0 1 0 1 ep1968) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5)) Bool.false 230767387107886469 78125000 0 1 Bool.false 7131677479731368925469 244140625000 0 1 qz796)

noncomputable def ep2011 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) 0 1 0 1 230767387107886469 78125000 0 1 0 1 0

noncomputable def ep2012 := @ep2011 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) Bool.false 1 30240 0 1 Bool.false 0 1 0 1 ep1968) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5)) Bool.false 230767387107886469 78125000 0 1 Bool.false 7131677479731368925469 244140625000 0 1 qz796)

noncomputable def ep2013 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5)) Bool.false 230767387107886469 2362500000000 0 1 Bool.false 7131677479731368925469 7382812500000000 0 1 (@ep1966 230767387107886469 2362500000000 0 1 (ep2005 rfl) (ep2007 rfl) rfl rfl) (@ep2008 7131677479731368925469 7382812500000000 0 1 (ep2010 rfl) (ep2012 rfl) rfl rfl)

noncomputable def ep2014 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) Bool.false 230767387107886469 2362500000000 0 1 Bool.false 7131677479731368925469 7382812500000000 0 1 ep2013

noncomputable def ep2015 := nat_lit 158456325028528675187087900672

noncomputable def ep2016 := nat_lit 60335414881112863650987459938877440

noncomputable def ep2017 := @Enclosure.Complex.IsNear.re_isNear qz235 Bool.true 2692109859555060160923 ep1963 86408125976346361521 ep1964 Bool.true 493894905437798745517 ep2015 31705001486955484673 ep2016

noncomputable abbrev qz540 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 36028797018963968)))

noncomputable def ep2018 := @Enclosure.Complex.IsNear.of_eq qz235 (Complex.mk (@HMul.hMul Real Real Real qz0 qz540 (Real.cos qz377)) (@HMul.hMul Real Real Real qz0 qz540 qz938)) Bool.true 2692109859555060160923 ep1963 86408125976346361521 ep1964 Bool.true 493894905437798745517 ep2015 31705001486955484673

noncomputable abbrev qz541 := (Real.sqrt (@Nat.cast Real Real.instNatCast 36028797018963968))

noncomputable def ep2019 := @Enclosure.Real.IsNear.inv_image qz541 213709911250252303767135 1125899906842624 1 1125899906842624 2965820 2965821 562949953421312 (@Enclosure.Real.IsNear.of_eq qz541 (Real.sqrt (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 36028797018963968) qz265)) Bool.false 213709911250252303767135 1125899906842624 1 1125899906842624 (BSN.sqrt_natCast_div_one 36028797018963968) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 36028797018963968) qz265)) Bool.false 213709911250252303767135 1125899906842624 1 1125899906842624 213709911250252303767135 1125899906842624 1 1125899906842624 (BSN.sqrt_enclosure 36028797018963968 1 106854955625126151883567 106854955625126151883568 562949953421312 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep2020 := nat_lit 115080671083665587713217658880

noncomputable def ep2021 := nat_lit 2151219200000000000000000

noncomputable def ep2022 := nat_lit 70293475158665552278669146193920

noncomputable def ep2023 := nat_lit 20282409603651670423947251286016

noncomputable def ep2024 := nat_lit 204424337162240000000000000000

noncomputable def ep2025 := BSN.log_dyadic_bound 0 64 1 0 1 562949953421312 204424337162240 0 1 0 64 64 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 64) 0 0 rfl) rfl rfl rfl

noncomputable def ep2026 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz378 124004 1000 0 1 15608286920413395 4503599627370496 2468410261 249541427200000000000000 96774500563947131679 225179981368524800 2638730569009 ep2021 qz270 (BSN.isNear_log_sfrac 32 1 15608286920413395 4503599627370496 2468410261 249541427200000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz619) Bool.false ep2022 ep2023 2022121685811200 ep2024 15608286920413395 4503599627370496 2468410261 249541427200000000000000 (BSN.log_rat_reduce_isNear 32 1 5 64 64 0 562949953421312 24973259072661432 36028797018963968 204424337162240 1000000000000000 rfl rfl rfl rfl (ep2025 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep2027 := nat_lit 6320204631903813004853318088270782519686956084851959394190260961280

noncomputable def ep2028 := nat_lit 6739986666787659948666753771754907668409286105635143120275902562304

noncomputable def ep2029 := nat_lit 1464072154119698882026295591372973396092038878105186174758693934793222242108953435629351913954296924071753269194875627243793044116582535838309994664231251164746706817010536971428932209384355452210540510382769817825640848713397476237205438236671525840927899439148456124091949742195444565215326434700579373056

noncomputable def ep2030 := nat_lit 227166498108393291591690474249109426965528421018278839661455426590473243066834650624926416047854179247596172938820614485527445924608820872880385787908168637421617142754592441181269508473347051925777211342581761153821293384735107078859788885002196634811247029175151612501537270086431278076342027182518829056000

noncomputable def ep2031 := nat_lit 228259786692632971012076749163304803568562605576346574609085515818746481508970847393408768133408166189268333177810212837264043651900596239207916831722687177341465043266103318052452652558148313949458605722053571973799955298618709689865655012447301549449473883172145175386585098662544272470900736

noncomputable def ep2032 := nat_lit 11919846417187979768266919085876388482207177559806296901100003593481542504845872812868338424397393077049960121767495152976700799915938324338086601254092235617992888001949710203374656506273623828481961291166113763702912557288974495463022890952206446863342363131569940488914147472885263643186861685607397130240

noncomputable def ep2033 := nat_lit 12948490392178417620726357032199237337035119998041893860702959315656974854809575085620805714727688217112981857512775025675064417702702789754181989910765612333032177137011769147332361982980781959769301046527160385767813722929901103495007966445125208184241080662983641912587624394926582850351495549403573256192000

noncomputable def ep2034 := BSN.sin_dyadic_bound_f 2162229747291359598 2305843009213693952 5 4 1125899906842624 409247940608001 ep2029 ep2030 ep2031 ep2032 ep2033 ep2031 907711663452006 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.sinEvenP 2162229747291359598) (BSN.sinEvenQ 2305843009213693952) 0 4 ep2029 ep2030 ep2031 rfl rfl rfl rfl) (@BSN.binarySplit_of_base4 (BSN.sinOddP 2162229747291359598) (BSN.sinOddQ 2305843009213693952) 0 4 ep2032 ep2033 ep2031 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz797 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 241936251409867829) (@Nat.cast Real Real.instNatCast 562949953421312))

noncomputable def ep2035 := @Enclosure.Real.IsNear.cos_image qz377 qz797 Bool.false 241936251409867829 562949953421312 691 562949953421312 Bool.true 907711663452006 1125899906842624 1 204424337162240 (@Enclosure.Real.IsNear.recentre' qz377 Bool.false 96774500563947131679 225179981368524800 2638730569009 ep2021 241936251409867829 562949953421312 691 562949953421312 (ep2026 rfl) rfl) (Enclosure.sfrac_false_div 241936251409867829 562949953421312) (BSN.cos_reduce1 qz797 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep2027) (@Nat.cast Real Real.instNatCast ep2028)) ep1868 ep1846 Bool.false 907711663452006 1125899906842624 68 ep1869 408848674324480 204424337162240 (BSN.sin_reduce_arg_pos_rat_q1 241936251409867829 562949953421312 ep1868 ep1846 68 ep2027 ep2028 rfl rfl rfl rfl) EMRow41.d183 (@BSN.sin_arg_round Bool.false 907711663452006 1125899906842624 ep2027 ep2028 2162229747291359598 2305843009213693952 409247940608001 408848674324480 (ep2034 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep2036 := nat_lit 430697523094984268294462265029492837485872262111891676981611709701388415304991176621034644148555090762777153754753347088911956868584114359542286625915241416573573854299242233436262343556219841682978642518426197191293576624843728305038168122454240403506910080288176772417633025955954369947907894526691311616

noncomputable def ep2037 := nat_lit 13362735182846664211275910249947613350913436530486990568320907446498426062754979448525083296932598779270363114048271440325143877918165933698846222818127566907153949573799555363604088733726297172104541843681280067871840787337359239932928757941305684400661589951479506617737486475672428122137766304854048768000

noncomputable def ep2038 := nat_lit 4391767337317640146672041883684767422085618437437178812341546325535575512011645955922186389486345065370270566313544119678264363981090568223547877207915423781652066952006738410883334611740650366558154624757645181220109528077363433796301085293002549032684424765183954877362450188295266581251599730179938779136

noncomputable def ep2039 := nat_lit 2044498482975539624325214268241984842689755789164509556953098839314259187601511855624337744430687613228365556449385530369747013321479387855923472091173517736794554284791331970631425576260123467331994902083235850384391640462615963709738099965019769713301223262576364512513835430777881502687078244642669461504000

noncomputable def ep2040 := BSN.cos_dyadic_bound_f 2162229747291359598 2305843009213693952 5 4 1125899906842624 409247940608001 ep2036 ep2037 ep2031 ep2038 ep2039 ep2031 666115707862696 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.cosEvenP 2162229747291359598) (BSN.cosEvenQ 2305843009213693952) 0 4 ep2036 ep2037 ep2031 rfl rfl rfl rfl) (@BSN.binarySplit_of_base4 (BSN.cosOddP 2162229747291359598) (BSN.cosOddQ 2305843009213693952) 0 4 ep2038 ep2039 ep2031 rfl rfl rfl rfl) rfl rfl

noncomputable def ep2041 := @Enclosure.Real.IsNear.sin_image qz377 qz797 Bool.false 241936251409867829 562949953421312 691 562949953421312 Bool.false 666115707862696 1125899906842624 1 204424337162240 (@Enclosure.Real.IsNear.recentre' qz377 Bool.false 96774500563947131679 225179981368524800 2638730569009 ep2021 241936251409867829 562949953421312 691 562949953421312 (ep2026 rfl) rfl) (Enclosure.sfrac_false_div 241936251409867829 562949953421312) (BSN.sin_reduce1 qz797 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep2027) (@Nat.cast Real Real.instNatCast ep2028)) ep1868 ep1846 Bool.false 666115707862696 1125899906842624 68 ep1869 408848674324480 204424337162240 (BSN.sin_reduce_arg_pos_rat_q1 241936251409867829 562949953421312 ep1868 ep1846 68 ep2027 ep2028 rfl rfl rfl rfl) EMRow41.d183 (@BSN.cos_arg_round Bool.false 666115707862696 1125899906842624 ep2027 ep2028 2162229747291359598 2305843009213693952 409247940608001 408848674324480 (ep2040 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz798 := (@Enclosure.Real.IsNear.recentre' qz540 Bool.false 5931641 1125899906842624 1 1125899906842624 5931641 1125899906842624 1 1125899906842624 (ep2019 rfl rfl) rfl)

noncomputable def ep2042 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz540 (Real.cos qz377)) (@HMul.hMul Real Real Real qz0 qz540 qz938) Bool.true 2692109859555060160923 ep1963 86408125976346361521 ep1964 Bool.true 493894905437798745517 ep2015 31705001486955484673 ep2016 (@Enclosure.Real.IsNear.mulLit_ft qz540 (Real.cos qz377) 5931641 1125899906842624 1 1125899906842624 453855831726003 562949953421312 132080323 107177226882116485120 2692109859555060160923 ep1963 86408125976346361521 ep1964 qz798 (@Enclosure.Real.IsNear.recentre' (Real.cos qz377) Bool.true 907711663452006 1125899906842624 141820166932529152 ep2020 453855831726003 562949953421312 132080323 107177226882116485120 (ep2035 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz540 qz938 5931641 1125899906842624 1 1125899906842624 83264463482837 140737488355328 132080323 107177226882116485120 493894905437798745517 ep2015 31705001486955484673 ep2016 qz798 (@Enclosure.Real.IsNear.neg (Real.sin qz377) Bool.false 83264463482837 140737488355328 132080323 107177226882116485120 (@Enclosure.Real.IsNear.recentre' (Real.sin qz377) Bool.false 666115707862696 1125899906842624 141820166932529152 ep2020 83264463482837 140737488355328 132080323 107177226882116485120 (ep2041 rfl rfl) rfl)) rfl)

noncomputable def ep2043 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.im qz235) 7131677479731368925469 7382812500000000 0 1 493894905437798745517 ep2015 31705001486955484673 ep2016 ep1957

noncomputable def ep2044 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) Bool.false 230767387107886469 2362500000000 0 1 Bool.false 7131677479731368925469 7382812500000000 0 1 ep2013

noncomputable def ep2045 := @Enclosure.Complex.IsNear.im_isNear qz235 Bool.true 2692109859555060160923 ep1963 86408125976346361521 ep1964 Bool.true 493894905437798745517 ep2015 31705001486955484673 ep2016

noncomputable def ep2046 := nat_lit 16282119547682497848515579980779815639

noncomputable def ep2047 := nat_lit 53479009697128427875642166476800000000000

noncomputable def ep2048 := nat_lit 72440399518775964785882537153995937

noncomputable def ep2049 := nat_lit 1411311065907219211638196773322752000000000000

noncomputable def ep2050 := nat_lit 914250440873885762160569514545376415868947

noncomputable def ep2051 := nat_lit 222829207071368449481842360320000000000000000

noncomputable def ep2052 := nat_lit 7083159610244832774827796672358408948027

noncomputable def ep2053 := @Enclosure.Real.IsNear.addLit_tt (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.im qz235)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.re qz235)) ep2046 ep2047 ep2048 ep2049 ep2050 ep2051 ep2052

noncomputable def ep2054 := nat_lit 10240116210964737095938065668505600000000000000000

noncomputable def ep2055 := nat_lit 52521339981349796380341709159395016180616043651275375381116207349995929600000000000

noncomputable def ep2056 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.im qz235) 230767387107886469 2362500000000 0 1 493894905437798745517 ep2015 31705001486955484673 ep2016 ep2046

noncomputable def ep2057 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.re qz235) 7131677479731368925469 7382812500000000 0 1 2692109859555060160923 ep1963 86408125976346361521 ep1964 ep2050

noncomputable abbrev qz799 := (@ep2018 ep2016 (BSN.cpow_neg_s_sub_mk qz9 124004 1000 32 5 36028797018963968 (@Eq.refl Real qz9) rfl EMRow41.d180) ep2042)

noncomputable def ep2058 := ep1952 (@ep1960 ep1961 ep1962 ep1944 ep1945 ep1946 ep1947 (@ep1965 ep1954 ep1955 ep1956 ep2014 (ep2017 qz799) rfl) (@ep2043 ep1958 ep1959 ep1961 ep2044 (ep2045 qz799) rfl) rfl rfl) (@ep2053 ep2054 ep2055 ep1949 ep1945 ep1950 ep1947 (@ep2056 ep2047 ep2048 ep2049 ep2014 (ep2045 qz799) rfl) (@ep2057 ep2051 ep2052 ep2054 ep2044 (ep2017 qz799) rfl) rfl rfl)

noncomputable def ep2059 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235)) (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235)) ep1949 ep1945 ep1950 ep1947 ep1949 ep1945 ep1950

noncomputable def ep2060 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235) Bool.false ep1944 ep1945 ep1946 ep1947 Bool.true ep1949 ep1945 ep1950

noncomputable def ep2061 := @ep1916 46848551389312750317 405828369621610135552 2227089510157 101457092405402533888 (@ep1917 1 5767168 (ep1918 (@ep1919 1048576 1 1048576 (ep1920 (@ep1921 3851810504 481476313 31250 0 1 (ep1925 rfl) (ep1928 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 11) rfl) (@ep1929 131357 140737488355328 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235)) (@ep1930 1050856 1125899906842624 359943055089 70368744177664 131357 140737488355328 (@ep1935 2879543915284 2879544966140 562949953421312 (@ep1941 ep1937 ep1942 ep1939 ep1943 ep1931 ep1932 ep1933 ep1934 (@ep1948 ep1947 ep1936 ep1937 ep1938 ep1939 (@ep1951 ep1947 ep2058) (@ep1951 ep1947 ep2058) rfl) (@ep2059 ep1947 ep1940 ep1937 ep1942 ep1939 (@ep2060 ep1947 ep2058) (@ep2060 ep1947 ep2058) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow41.d184 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz607 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 2 4) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz12 2 32))) (@HMul.hMul Real Real Real qz0 qz790 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235)))) Bool.false ep1870 ep1871 3545882201743646797 ep1872 := ep1914 (ep1915 ep2061) rfl rfl

noncomputable def ep2062 := nat_lit 69386381120164520525846229

noncomputable def ep2063 := nat_lit 542323060146664002103017472

noncomputable def ep2064 := nat_lit 49302096376969454736637952

noncomputable abbrev qz542 := (@HAdd.hAdd Complex Complex Complex qz549 (@HAdd.hAdd Complex Complex Complex qz549 qz550 (@HMul.hMul Complex Complex Complex qz545 Complex.I ↑(Enclosure.sfrac Bool.false 126105 1000))) (@Nat.cast Complex Complex.instNatCast 5))

noncomputable abbrev qz241 := (@Norm.norm Complex Complex.instNorm qz542)

noncomputable abbrev qz242 := (@HPow.hPow Complex Complex Complex (@instHPow Complex Complex Complex.instPow) qz609 (@HSub.hSub Complex Complex Complex qz595 (@Neg.neg Complex Complex.instNeg qz384) (@Nat.cast Complex Complex.instNatCast 5)))

noncomputable abbrev qz800 := (@HDiv.hDiv Real Real Real qz1 qz241 (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (Complex.re qz64) (@Nat.cast Real Real.instNatCast 5)))

noncomputable def ep2065 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 2 4) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz64 2 32))) (@HMul.hMul Real Real Real qz0 qz800 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242))) 48352495965 179359981764608 135205575 179359981764608 829015214837159146389 6493253913945762168832 14078051275169

noncomputable def ep2066 := nat_lit 149006118849449230899015138139963392

noncomputable def ep2067 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 2 4) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz64 2 32)) 10095 171051008 15 171051008 4789747 1048576 6267 1048576 48352495965 179359981764608

noncomputable def ep2068 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz64 2 32)) (Real.sqrt (@HAdd.hAdd Real Real Real qz607 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz64 2 32)) (Complex.re (zetaApproximant qz64 2 32))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz64 2 32)) (Complex.im (zetaApproximant qz64 2 32))))) Bool.false 4789747 1048576 6267 1048576

noncomputable def ep2069 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz607 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz64 2 32)) (Complex.re (zetaApproximant qz64 2 32))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz64 2 32)) (Complex.im (zetaApproximant qz64 2 32))))) Bool.false 4789747 1048576 6267 1048576

noncomputable def ep2070 := nat_lit 705694919280115756790115341079881118674422075575333791642261

noncomputable def ep2071 := nat_lit 33821347192939828847813760544101884932799856640000000000000

noncomputable def ep2072 := nat_lit 212836130936897231370752506590906732018112725776474848106974038087698930856931

noncomputable def ep2073 := nat_lit 3899040940501545159096714397310126968375381719300055988562821120000000000000000

noncomputable def ep2074 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz607 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz64 2 32)) (Complex.re (zetaApproximant qz64 2 32))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz64 2 32)) (Complex.im (zetaApproximant qz64 2 32)))) ep2070 ep2071 ep2072 ep2073 2391740 2398007

noncomputable def ep2075 := nat_lit 4488982491662791085533709848404301475093841208125177243457806737700409

noncomputable def ep2076 := nat_lit 215140579639595579111211766035601794105186796922365542400000000000000

noncomputable def ep2077 := nat_lit 424935116007254562108511154972412744289563948436443340052745971160759918440171

noncomputable def ep2078 := nat_lit 7798081881003090318193428794620253936750763438600111977125642240000000000000000

noncomputable def ep2079 := nat_lit 5280365838798442271650302127193083859620265222620439134575594601

noncomputable def ep2080 := nat_lit 737145866539900632993858209400719746661503116506356161202105014637943273691

noncomputable def ep2081 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz64 2 32)) (Complex.re (zetaApproximant qz64 2 32))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz64 2 32)) (Complex.im (zetaApproximant qz64 2 32))) ep2075 ep2076 ep2077 ep2078 ep2079 ep2076 ep2080

noncomputable def ep2082 := nat_lit 965763431269296171489095274782834873810183918603388781928714226393673011247734657418340925959074227609662756826280229863424000000000000000

noncomputable def ep2083 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz64 2 32)) (Complex.re (zetaApproximant qz64 2 32)) ep1307 ep1308 ep1309 ep1310 ep1307 ep1308 ep1309 ep1310 ep2075

noncomputable def ep2084 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (zetaApproximant qz64 2 32)) (Complex.im (zetaApproximant qz64 2 32)) ep1495 ep1308 ep1496 ep1310 ep1495 ep1308 ep1496 ep1310 ep2079

noncomputable def ep2085 := @ep2065 590295810358705651712 ep2066 ep2062 ep2063 38340838383713402849 ep2064 (@ep2067 135205575 179359981764608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 2 4) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 30720 334084) qz1120) Bool.false 10095 171051008 15 171051008 (BSN.theta_err_eq 2 4 30720 334084 EMRow41.d22 EMRow41.d23 rfl) (ep1895 rfl)) (ep2068 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz64 2 32)) (@ep2069 4789747 1048576 6267 1048576 (@ep2074 524288 (@ep2081 ep2078 ep2082 ep2070 ep2071 ep2072 ep2073 (@ep2083 ep2076 ep2077 ep2078 ep1705 ep1705 rfl) (@ep2084 ep2076 ep2080 ep2078 ep1711 ep1711 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable def ep2086 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz800 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz241 (Enclosure.sfrac Bool.false 2 11)) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242))) Bool.false 829015214837159146389 6493253913945762168832 14078051275169 590295810358705651712 (BSN.zrb_shape_eq qz241 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242)) qz61 5)

noncomputable def ep2087 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz241 (Enclosure.sfrac Bool.false 2 11)) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242)) 132356383 5767168 1 5767168 6263507630283 1125899906842624 1122689 1125899906842624

noncomputable def ep2088 := @Enclosure.Real.IsNear.mulLit_ff qz241 (Enclosure.sfrac Bool.false 2 11) 132356383 1048576 1 1048576 2 11 0 1 132356383 5767168

noncomputable abbrev qz243 := (Complex.re qz542)

noncomputable abbrev qz244 := (Complex.im qz542)

noncomputable abbrev qz245 := qz542

noncomputable abbrev qz1122 := (@HAdd.hAdd Real Real Real qz607 (@HMul.hMul Real Real Real qz0 qz243 qz243) (@HMul.hMul Real Real Real qz0 qz244 qz244))

noncomputable def ep2089 := @Enclosure.Real.IsNear.of_eq qz241 (Real.sqrt qz1122) Bool.false 132356383 1048576 1 1048576 (BSN.norm_eq_sqrt_mul_add qz245)

noncomputable def ep2090 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz1122) Bool.false 132356383 1048576 1 1048576 132356383

noncomputable def ep2091 := @Enclosure.Real.IsNear.sqrt_image qz1122 637308841 40000 0 1 66178191 66178192 524288

noncomputable def ep2092 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz243 qz243) (@HMul.hMul Real Real Real qz0 qz244 qz244) 121 4 0 1 636098841 40000 0 1

noncomputable def ep2093 := @Enclosure.Real.IsNear.mulLit_ff qz243 qz243 11 2 0 1 11 2 0 1 121 4

noncomputable def ep2094 := @Enclosure.Complex.IsNear.of_eq qz245 (Complex.mk (Enclosure.sfrac Bool.false 11 2) qz61) Bool.false 11 2 0 1 Bool.false 126105 1000 0 1 (BSN.s_add_nat_mk qz61 Bool.false 126105 1000 5 (@Eq.refl Real qz61))

noncomputable abbrev qz801 := (ep2094 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 11 2) qz61 Bool.false 11 2 0 1 Bool.false 126105 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 11 2) qz386))

noncomputable def ep2095 := @ep2093 0 1 (@Enclosure.Complex.IsNear.re_isNear qz245 Bool.false 11 2 0 1 Bool.false 126105 1000 0 1 qz801)

noncomputable def ep2096 := ep2095 (@Enclosure.Complex.IsNear.re_isNear qz245 Bool.false 11 2 0 1 Bool.false 126105 1000 0 1 qz801)

noncomputable def ep2097 := @Enclosure.Real.IsNear.mulLit_ff qz244 qz244 126105 1000 0 1 126105 1000 0 1 636098841 40000

noncomputable def ep2098 := @ep2097 0 1 (@Enclosure.Complex.IsNear.im_isNear qz245 Bool.false 11 2 0 1 Bool.false 126105 1000 0 1 qz801)

noncomputable def ep2099 := ep2098 (@Enclosure.Complex.IsNear.im_isNear qz245 Bool.false 11 2 0 1 Bool.false 126105 1000 0 1 qz801)

noncomputable def ep2100 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242)) (Real.sqrt (@HAdd.hAdd Real Real Real qz607 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242)) (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242)) (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242))))) Bool.false 6263507630283 1125899906842624

noncomputable def ep2101 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz607 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242)) (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242)) (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242))))) Bool.false 6263507630283 1125899906842624

noncomputable def ep2102 := nat_lit 586661007545844876423476961548507582613468551800674562264067687917110698383479281489

noncomputable def ep2103 := nat_lit 18956212500340293605625244983060677817401117172098840025775975956480000000000000000000000

noncomputable def ep2104 := nat_lit 3021391374562416503003667461700451907214713611494616064717786286075248010912565158397

noncomputable def ep2105 := nat_lit 272332689233326296891634566401684447301559888083883876169974862447640576000000000000000000000000

noncomputable def ep2106 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz607 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242)) (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242)) (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242)))) ep2102 ep2103 ep2104 ep2105

noncomputable def ep2107 := nat_lit 235319810246915439366506185915789236714526605143497475277360214730478177658092409009

noncomputable def ep2108 := nat_lit 37912425000680587211250489966121355634802234344197680051551951912960000000000000000000000

noncomputable def ep2109 := nat_lit 3419723620451943242495170989867521555693709422922456894221485839614435251972258777271

noncomputable def ep2110 := nat_lit 1633996135399957781349807398410106683809359328503303257019849174685843456000000000000000000000000

noncomputable def ep2111 := nat_lit 104222467204974923720049748575691769834712277606427961027863906789304802123207350441

noncomputable def ep2112 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242)) (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242)) (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242))) ep2107 ep2108 ep2109 ep2110 ep2111

noncomputable def ep2113 := nat_lit 4212491666742287467916721107346817292755803816021964450172439101440000000000000000000000

noncomputable def ep2114 := nat_lit 14708624626922555775526833780335189887594572246045239494085231876837052813503132173111

noncomputable def ep2115 := nat_lit 4942609210979011537358748390872055660770781960058649934978169111396828935073768188511223945308025714384249049660663052554396575117118187781639970488320000000000000000000000

noncomputable def ep2116 := nat_lit 485097732675504719645029756244128334557753

noncomputable def ep2117 := nat_lit 194711132195056036069893612345753600000000000

noncomputable def ep2118 := nat_lit 536904446459584277265956109917116816091

noncomputable def ep2119 := nat_lit 1278278582860542876798851565049872384000000000000

noncomputable def ep2120 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242)) (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242)) ep2116 ep2117 ep2118 ep2119 ep2116 ep2117 ep2118

noncomputable def ep2121 := nat_lit 322835046432345885293269529426601962324979

noncomputable def ep2122 := nat_lit 64903710731685345356631204115251200000000000

noncomputable def ep2123 := nat_lit 1156659074549703983932679676005932375651

noncomputable def ep2124 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242) Bool.true ep2116 ep2117 ep2118 ep2119 Bool.true ep2121 ep2122 ep2123

noncomputable def ep2125 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242 Bool.true ep2116 ep2117 ep2118 ep2119 Bool.true ep2121 ep2122 ep2123 ep2119

noncomputable def ep2126 := nat_lit 40039363799969510605548584703669631097

noncomputable def ep2127 := nat_lit 77884452878022414427957444938301440000000

noncomputable def ep2128 := nat_lit 1285134235829195706887358019671789599

noncomputable def ep2129 := nat_lit 14828031561182297370866678154578519654400000000

noncomputable def ep2130 := nat_lit 384999323175580943131158294484954256815253

noncomputable def ep2131 := nat_lit 12357393357754954773494332138416913669139

noncomputable def ep2132 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.re qz242)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.im qz242)) ep2126 ep2127 ep2128 ep2129 ep2130 ep2117 ep2131

noncomputable def ep2133 := nat_lit 37070078902955743427166695386446299136000000000000

noncomputable def ep2134 := nat_lit 37781571501800861390241295921061945573389041346461822667769452123673403064320000000

noncomputable def ep2135 := nat_lit 1267650600228229401496703205376

noncomputable def ep2136 := nat_lit 241341659524451454603949839755509760

noncomputable def ep2137 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.re qz242) 6418730503840687 61440000000 0 1 6237894514501225785431 ep2135 200216263178556524177 ep2136 ep2126

noncomputable def ep2138 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)))) 6418730503840687 61440000000 0 1 0 1 0 1 6418730503840687

noncomputable def ep2139 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) 1 30240 0 1 404380021741963281 128000000 0 1 6418730503840687 61440000000 0

noncomputable abbrev qz246 := (@HAdd.hAdd Complex Complex Complex qz260 qz384 qz261)

noncomputable def ep2140 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)) (@HMul.hMul Complex Complex Complex qz3 (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4)) qz246) Bool.false 404380021741963281 128000000 0 1 Bool.false 10168070039017362790101 320000000000 0 1

noncomputable def ep2141 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.re qz246)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.im qz246)) 3636672309164549529 3200000000 0 1 404551764649033281 200000000 0 1

noncomputable def ep2142 := nat_lit 2021900108709816405000000000

noncomputable def ep2143 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.re qz246) 404074701018283281 1600000000 0 1 9 2 0 1 3636672309164549529 3200000000

noncomputable abbrev qz247 := (@HAdd.hAdd Complex Complex Complex qz260 qz384 qz552)

noncomputable def ep2144 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4)) (@HMul.hMul Complex Complex Complex qz3 (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) qz247) Bool.false 404074701018283281 1600000000 0 1 Bool.true 16040274558861 1000000 0 1

noncomputable def ep2145 := @Enclosure.Real.IsNear.subLit_tt_p (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.re qz247)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.im qz247)) 40073176983 160000 0 1 404475432788113281 1600000000 0 1

noncomputable def ep2146 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.re qz247) 5724739569 80000 0 1 7 2 0 1 40073176983 160000

noncomputable abbrev qz802 := (ep1255 (BSN.ascPochhammer_succ_eval_c 2 3 qz64 rfl) (ep1283 (@ep1284 641489921554440 16037248038861 8000000 0 1 (ep1287 rfl) (ep1290 rfl) rfl rfl)))

noncomputable def ep2147 := @ep2146 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 5724739569 80000 0 1 Bool.true 16037248038861 8000000 0 1 qz802)

noncomputable def ep2148 := @Enclosure.Complex.IsNear.of_eq qz247 (Complex.mk (Enclosure.sfrac Bool.false 7 2) qz61) Bool.false 7 2 0 1 Bool.false 126105 1000 0 1 (BSN.s_add_nat_mk qz61 Bool.false 126105 1000 3 (@Eq.refl Real qz61))

noncomputable abbrev qz803 := (ep2148 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz61 Bool.false 7 2 0 1 Bool.false 126105 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz386))

noncomputable def ep2149 := ep2147 (@Enclosure.Complex.IsNear.re_isNear qz247 Bool.false 7 2 0 1 Bool.false 126105 1000 0 1 qz803)

noncomputable def ep2150 := @Enclosure.Real.IsNear.mulLit_tf (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.im qz247) 16037248038861 8000000 0 1 126105 1000 0 1 404475432788113281 1600000000

noncomputable def ep2151 := @ep2150 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 5724739569 80000 0 1 Bool.true 16037248038861 8000000 0 1 qz802)

noncomputable def ep2152 := ep2151 (@Enclosure.Complex.IsNear.im_isNear qz247 Bool.false 7 2 0 1 Bool.false 126105 1000 0 1 qz803)

noncomputable def ep2153 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) qz247 Bool.false 404074701018283281 1600000000 0 1 Bool.true 16040274558861 1000000 0 1 (@ep2145 64651952162925324960000 404074701018283281 1600000000 0 1 (ep2149 rfl) (ep2152 rfl) rfl rfl)

noncomputable def ep2154 := @Enclosure.Real.IsNear.addLit_tt (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.im qz247)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.re qz247)) 144383656669749 16000000 0 1 112260736272027 16000000 0 1

noncomputable def ep2155 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.im qz247) 5724739569 80000 0 1 126105 1000 0 1 144383656669749 16000000

noncomputable def ep2156 := @ep2155 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 5724739569 80000 0 1 Bool.true 16037248038861 8000000 0 1 qz802)

noncomputable def ep2157 := ep2156 (@Enclosure.Complex.IsNear.im_isNear qz247 Bool.false 7 2 0 1 Bool.false 126105 1000 0 1 qz803)

noncomputable def ep2158 := @Enclosure.Real.IsNear.mulLit_tf (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.re qz247) 16037248038861 8000000 0 1 7 2 0 1 112260736272027 16000000

noncomputable def ep2159 := @ep2158 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 5724739569 80000 0 1 Bool.true 16037248038861 8000000 0 1 qz802)

noncomputable def ep2160 := ep2159 (@Enclosure.Complex.IsNear.re_isNear qz247 Bool.false 7 2 0 1 Bool.false 126105 1000 0 1 qz803)

noncomputable abbrev qz804 := (ep2144 (BSN.ascPochhammer_succ_eval_c 3 4 qz64 rfl) (ep2153 (@ep2154 4106310287068416000000 16040274558861 1000000 0 1 (ep2157 rfl) (ep2160 rfl) rfl rfl)))

noncomputable def ep2161 := @ep2143 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4)) Bool.false 404074701018283281 1600000000 0 1 Bool.true 16040274558861 1000000 0 1 qz804)

noncomputable def ep2162 := @Enclosure.Complex.IsNear.of_eq qz246 (Complex.mk (Enclosure.sfrac Bool.false 9 2) qz61) Bool.false 9 2 0 1 Bool.false 126105 1000 0 1 (BSN.s_add_nat_mk qz61 Bool.false 126105 1000 4 (@Eq.refl Real qz61))

noncomputable abbrev qz805 := (ep2162 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9 2) qz61 Bool.false 9 2 0 1 Bool.false 126105 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 9 2) qz386))

noncomputable def ep2163 := ep2161 (@Enclosure.Complex.IsNear.re_isNear qz246 Bool.false 9 2 0 1 Bool.false 126105 1000 0 1 qz805)

noncomputable def ep2164 := @Enclosure.Real.IsNear.mulLit_tf (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.im qz246) 16040274558861 1000000 0 1 126105 1000 0 1 404551764649033281 200000000

noncomputable def ep2165 := @ep2164 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4)) Bool.false 404074701018283281 1600000000 0 1 Bool.true 16040274558861 1000000 0 1 qz804)

noncomputable def ep2166 := ep2165 (@Enclosure.Complex.IsNear.im_isNear qz246 Bool.false 9 2 0 1 Bool.false 126105 1000 0 1 qz805)

noncomputable def ep2167 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4)) qz246 Bool.false 404380021741963281 128000000 0 1 Bool.false 10168070039017362790101 320000000000 0 1 (@ep2141 ep2142 404380021741963281 128000000 0 1 (ep2163 rfl) (ep2166 rfl) rfl rfl)

noncomputable def ep2168 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.im qz246)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.re qz246)) 10191168034382122630101 320000000000 0 1 144362471029749 2000000 0 1

noncomputable def ep2169 := nat_lit 20336140078034725580202000000

noncomputable def ep2170 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.im qz246) 404074701018283281 1600000000 0 1 126105 1000 0 1 10191168034382122630101 320000000000

noncomputable def ep2171 := @ep2170 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4)) Bool.false 404074701018283281 1600000000 0 1 Bool.true 16040274558861 1000000 0 1 qz804)

noncomputable def ep2172 := ep2171 (@Enclosure.Complex.IsNear.im_isNear qz246 Bool.false 9 2 0 1 Bool.false 126105 1000 0 1 qz805)

noncomputable def ep2173 := @Enclosure.Real.IsNear.mulLit_tf (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.re qz246) 16040274558861 1000000 0 1 9 2 0 1 144362471029749 2000000

noncomputable def ep2174 := @ep2173 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4)) Bool.false 404074701018283281 1600000000 0 1 Bool.true 16040274558861 1000000 0 1 qz804)

noncomputable def ep2175 := ep2174 (@Enclosure.Complex.IsNear.re_isNear qz246 Bool.false 9 2 0 1 Bool.false 126105 1000 0 1 qz805)

noncomputable abbrev qz806 := (ep2140 (BSN.ascPochhammer_succ_eval_c 4 5 qz64 rfl) (ep2167 (@ep2168 ep2169 10168070039017362790101 320000000000 0 1 (ep2172 rfl) (ep2175 rfl) rfl rfl)))

noncomputable def ep2176 := @ep2139 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) Bool.false 1 30240 0 1 Bool.false 0 1 0 1 ep1968) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)) Bool.false 404380021741963281 128000000 0 1 Bool.false 10168070039017362790101 320000000000 0 1 qz806)

noncomputable def ep2177 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) 0 1 0 1 10168070039017362790101 320000000000 0 1 0 1 0

noncomputable def ep2178 := @ep2177 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) Bool.false 1 30240 0 1 Bool.false 0 1 0 1 ep1968) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)) Bool.false 404380021741963281 128000000 0 1 Bool.false 10168070039017362790101 320000000000 0 1 qz806)

noncomputable def ep2179 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)))) 161397937127259726827 153600000000000 0 1 0 1 0 1 161397937127259726827

noncomputable def ep2180 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) 1 30240 0 1 10168070039017362790101 320000000000 0 1 161397937127259726827 153600000000000 0

noncomputable def ep2181 := @ep2180 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) Bool.false 1 30240 0 1 Bool.false 0 1 0 1 ep1968) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)) Bool.false 404380021741963281 128000000 0 1 Bool.false 10168070039017362790101 320000000000 0 1 qz806)

noncomputable def ep2182 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) 0 1 0 1 404380021741963281 128000000 0 1 0 1 0

noncomputable def ep2183 := @ep2182 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) Bool.false 1 30240 0 1 Bool.false 0 1 0 1 ep1968) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)) Bool.false 404380021741963281 128000000 0 1 Bool.false 10168070039017362790101 320000000000 0 1 qz806)

noncomputable def ep2184 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)) Bool.false 6418730503840687 61440000000 0 1 Bool.false 161397937127259726827 153600000000000 0 1 (@ep2138 6418730503840687 61440000000 0 1 (ep2176 rfl) (ep2178 rfl) rfl rfl) (@ep2179 161397937127259726827 153600000000000 0 1 (ep2181 rfl) (ep2183 rfl) rfl rfl)

noncomputable def ep2185 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) Bool.false 6418730503840687 61440000000 0 1 Bool.false 161397937127259726827 153600000000000 0 1 ep2184

noncomputable def ep2186 := @Enclosure.Complex.IsNear.re_isNear qz242 Bool.true 6237894514501225785431 ep2135 200216263178556524177 ep2136 Bool.false 2385404237676315847039 ep2135 76564754034070120057 ep2136

noncomputable def ep2187 := @Enclosure.Complex.IsNear.of_eq qz242 (Complex.mk (@HMul.hMul Real Real Real qz0 qz540 (Real.cos qz421)) (@HMul.hMul Real Real Real qz0 qz540 qz992)) Bool.true 6237894514501225785431 ep2135 200216263178556524177 ep2136 Bool.false 2385404237676315847039 ep2135 76564754034070120057

noncomputable def ep2188 := nat_lit 230161342167331175426435317760

noncomputable def ep2189 := nat_lit 49908285440000000000000000

noncomputable def ep2190 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz378 126105 1000 0 1 15608286920413395 4503599627370496 2468410261 249541427200000000000000 78731320883949247059 180143985094819840 62255775192681 ep2189 qz386 (BSN.isNear_log_sfrac 32 1 15608286920413395 4503599627370496 2468410261 249541427200000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz619) Bool.false ep2022 ep2023 2022121685811200 ep2024 15608286920413395 4503599627370496 2468410261 249541427200000000000000 (BSN.log_rat_reduce_isNear 32 1 5 64 64 0 562949953421312 24973259072661432 36028797018963968 204424337162240 1000000000000000 rfl rfl rfl rfl (ep2025 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep2191 := nat_lit 2461761079998752937312170879915687449923848839543876864188042182656

noncomputable def ep2192 := nat_lit 8024807154630944646919935575810204348699159150904685486676007233737690079084769254838480574340126183260485435135217528472749002795728790775707209342887389706950214012249842851309019772381692343902085112435920185820708864000000

noncomputable def ep2193 := nat_lit 10821657637148560913492946031921314191599039087545316774779112146610557800425141274980107660439910087336441848082102652922524673568245877354709081054961510112752972936751739152800669431482567824842593065617095249443484864190873600

noncomputable def ep2194 := nat_lit 127350071353308034516856488911544211442273018238525077896032146009937213686569887015986657642515437542681229316143314370651595049235313670453536373871152523878169212189209640879268611144089276069098295296000000000000

noncomputable def ep2195 := nat_lit 48683486254015698836921553044170277487166781286266902210435060119609211920326299212232369458126850967486044353442329459943730918008556725707174888496469964715411751916500071522518162590636733886485627983680618382573279641600000

noncomputable def ep2196 := nat_lit 984770844980519043127858088904839591435512556966623826504899205341560759838687856023189797100031817947616208175471341415949745294710374839278526376001497420260520537244408262904860918264913672060675968971155667699357122641369497600

noncomputable def ep2197 := BSN.cos_dyadic_bound_f 842202641830287020 2305843009213693952 4 3 1125899906842624 409247940608001 ep2192 ep2193 ep2194 ep2195 ep2196 ep2194 1051630487162191 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 842202641830287020) (BSN.cosEvenQ 2305843009213693952) 0 3 ep2192 ep2193 ep2194 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 842202641830287020) (BSN.cosOddQ 2305843009213693952) 0 3 ep2195 ep2196 ep2194 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz807 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 246035377762341397) (@Nat.cast Real Real.instNatCast 562949953421312))

noncomputable def ep2198 := @Enclosure.Real.IsNear.cos_image qz421 qz807 Bool.false 246035377762341397 562949953421312 1405 1125899906842624 Bool.true 1051630487162191 1125899906842624 1 204424337162240 (@Enclosure.Real.IsNear.recentre' qz421 Bool.false 78731320883949247059 180143985094819840 62255775192681 ep2189 246035377762341397 562949953421312 1405 1125899906842624 (ep2190 rfl) rfl) (Enclosure.sfrac_false_div 246035377762341397 562949953421312) (BSN.cos_reduce2 qz807 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep2191) (@Nat.cast Real Real.instNatCast ep2028)) ep1868 ep1846 Bool.false 1051630487162191 1125899906842624 69 ep1869 408848674324480 204424337162240 (BSN.sin_reduce_arg_pos_rat_q2 246035377762341397 562949953421312 ep1868 ep1846 69 ep2191 ep2028 rfl rfl rfl rfl) EMRow41.d183 (@BSN.cos_arg_round Bool.false 1051630487162191 1125899906842624 ep2191 ep2028 842202641830287020 2305843009213693952 409247940608001 408848674324480 (ep2197 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep2199 := nat_lit 43010023744333649872446483504660947366344059006649120745535371278591497585952444550322820424551178695083038427324134722655930362446995263155773440000

noncomputable def ep2200 := nat_lit 290001949168298818796481024703320112391693131266627771193285344642266853525226636346689709741998071422586367171926025040972841322112034040818324241121280

noncomputable def ep2201 := nat_lit 253123691248942627845348618615227894819137556430788235073455935045826488617821491776130959919199746317652095441849921043574634404986905600000000

noncomputable def ep2202 := nat_lit 112644890463468965663581421471586627971452352128037285438307282039082895672703402111287368328460836925628205396742018421369556590334046186608435200000

noncomputable def ep2203 := nat_lit 5316702401418811677935485452894202060514374073221509138543564651774892314629154999689311345269964642747416731485310459084502090905387290748335944420556800

noncomputable def ep2204 := BSN.sin_dyadic_bound_f 842202641830287020 2305843009213693952 3 2 1125899906842624 409247940608001 ep2199 ep2200 ep2201 ep2202 ep2203 ep2201 402149124951479 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 842202641830287020) (BSN.sinEvenQ 2305843009213693952) 0 2 ep2199 ep2200 ep2201 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 842202641830287020) (BSN.sinOddQ 2305843009213693952) 0 2 ep2202 ep2203 ep2201 rfl rfl rfl rfl) rfl rfl

noncomputable def ep2205 := @Enclosure.Real.IsNear.sin_image qz421 qz807 Bool.false 246035377762341397 562949953421312 1405 1125899906842624 Bool.true 402149124951479 1125899906842624 1 204424337162240 (@Enclosure.Real.IsNear.recentre' qz421 Bool.false 78731320883949247059 180143985094819840 62255775192681 ep2189 246035377762341397 562949953421312 1405 1125899906842624 (ep2190 rfl) rfl) (Enclosure.sfrac_false_div 246035377762341397 562949953421312) (BSN.sin_reduce2 qz807 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep2191) (@Nat.cast Real Real.instNatCast ep2028)) ep1868 ep1846 Bool.false 402149124951479 1125899906842624 69 ep1869 408848674324480 204424337162240 (BSN.sin_reduce_arg_pos_rat_q2 246035377762341397 562949953421312 ep1868 ep1846 69 ep2191 ep2028 rfl rfl rfl rfl) EMRow41.d183 (@BSN.sin_arg_round Bool.false 402149124951479 1125899906842624 ep2191 ep2028 842202641830287020 2305843009213693952 409247940608001 408848674324480 (ep2204 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep2206 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz540 (Real.cos qz421)) (@HMul.hMul Real Real Real qz0 qz540 qz992) Bool.true 6237894514501225785431 ep2135 200216263178556524177 ep2136 Bool.false 2385404237676315847039 ep2135 76564754034070120057 ep2136 (@Enclosure.Real.IsNear.mulLit_ft qz540 (Real.cos qz421) 5931641 1125899906842624 1 1125899906842624 1051630487162191 1125899906842624 268539501 214354453764232970240 6237894514501225785431 ep2135 200216263178556524177 ep2136 qz798 (@Enclosure.Real.IsNear.recentre' (Real.cos qz421) Bool.true 1051630487162191 1125899906842624 288342093619789824 ep2188 1051630487162191 1125899906842624 268539501 214354453764232970240 (ep2198 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz540 qz992 5931641 1125899906842624 1 1125899906842624 402149124951479 1125899906842624 268539501 214354453764232970240 2385404237676315847039 ep2135 76564754034070120057 ep2136 qz798 (@Enclosure.Real.IsNear.neg (Real.sin qz421) Bool.true 402149124951479 1125899906842624 268539501 214354453764232970240 (@Enclosure.Real.IsNear.recentre' (Real.sin qz421) Bool.true 402149124951479 1125899906842624 288342093619789824 ep2188 402149124951479 1125899906842624 268539501 214354453764232970240 (ep2205 rfl rfl) rfl)) rfl)

noncomputable def ep2207 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.im qz242) 161397937127259726827 153600000000000 0 1 2385404237676315847039 ep2135 76564754034070120057 ep2136 ep2130

noncomputable def ep2208 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) Bool.false 6418730503840687 61440000000 0 1 Bool.false 161397937127259726827 153600000000000 0 1 ep2184

noncomputable def ep2209 := @Enclosure.Complex.IsNear.im_isNear qz242 Bool.true 6237894514501225785431 ep2135 200216263178556524177 ep2136 Bool.false 2385404237676315847039 ep2135 76564754034070120057 ep2136

noncomputable def ep2210 := nat_lit 15311266944363808700410900471116675793

noncomputable def ep2211 := nat_lit 491448522237545174225378305691359159

noncomputable def ep2212 := nat_lit 1006783306657947177630835839457597576457437

noncomputable def ep2213 := nat_lit 32314491856347552598484264839943640996379

noncomputable def ep2214 := @Enclosure.Real.IsNear.addLit_ft_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.im qz242)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.re qz242)) ep2210 ep2127 ep2211 ep2129 ep2212 ep2117 ep2213

noncomputable def ep2215 := nat_lit 75431492883702663843033720250731093544669653208392291751173917250088631009280000000

noncomputable def ep2216 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.im qz242) 6418730503840687 61440000000 0 1 2385404237676315847039 ep2135 76564754034070120057 ep2136 ep2210

noncomputable def ep2217 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.re qz242) 161397937127259726827 153600000000000 0 1 6237894514501225785431 ep2135 200216263178556524177 ep2136 ep2212

noncomputable abbrev qz808 := (@ep2187 ep2136 (BSN.cpow_neg_s_sub_mk qz61 126105 1000 32 5 36028797018963968 (@Eq.refl Real qz61) rfl EMRow41.d180) ep2206)

noncomputable def ep2218 := ep2125 (@ep2132 ep2133 ep2134 ep2116 ep2117 ep2118 ep2119 (@ep2137 ep2127 ep2128 ep2129 ep2185 (ep2186 qz808) rfl) (@ep2207 ep2117 ep2131 ep2133 ep2208 (ep2209 qz808) rfl) rfl rfl) (@ep2214 ep2133 ep2215 ep2121 ep2122 ep2123 ep2119 (@ep2216 ep2127 ep2211 ep2129 ep2185 (ep2209 qz808) rfl) (@ep2217 ep2117 ep2213 ep2133 ep2208 (ep2186 qz808) rfl) rfl rfl)

noncomputable def ep2219 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242)) (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242)) ep2121 ep2122 ep2123 ep2119 ep2121 ep2122 ep2123

noncomputable def ep2220 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242) Bool.true ep2116 ep2117 ep2118 ep2119 Bool.true ep2121 ep2122 ep2123

noncomputable def ep2221 := @ep2087 829015214837159146389 6493253913945762168832 14078051275169 590295810358705651712 (@ep2088 1 5767168 (ep2089 (@ep2090 1048576 1 1048576 (ep2091 (@ep2092 2549235364 637308841 40000 0 1 (ep2096 rfl) (ep2099 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 11) rfl) (@ep2100 1122689 1125899906842624 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242)) (@ep2101 1122689 1125899906842624 6263507630283 1125899906842624 1122689 1125899906842624 (@ep2106 3131753253797 3131754376486 562949953421312 (@ep2112 ep2113 ep2114 ep2110 ep2115 ep2102 ep2103 ep2104 ep2105 (@ep2120 ep2119 ep2107 ep2108 ep2109 ep2110 (@ep2124 ep2119 ep2218) (@ep2124 ep2119 ep2218) rfl) (@ep2219 ep2119 ep2111 ep2113 ep2114 ep2110 (@ep2220 ep2119 ep2218) (@ep2220 ep2119 ep2218) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow41.d185 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz607 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 2 4) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz64 2 32))) (@HMul.hMul Real Real Real qz0 qz800 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242)))) Bool.false ep2062 ep2063 38340838383713402849 ep2064 := ep2085 (ep2086 ep2221) rfl rfl

noncomputable def EMRow41.d186 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J))

noncomputable abbrev qz248 := (@Enclosure.dec_le_dec qz257 qz382 124004 1000 126105 1000 (@Eq.refl Real qz257) (@Eq.refl Real qz382) rfl rfl rfl)

noncomputable abbrev qz809 := (EMRow41.d3 qz9 qz61 qz248 32 32 2 2)

noncomputable def ep2222 := @Zeta.Certificates.ZIntervalEM.Certificate.mk qz809 (@Enclosure.dec_nonneg qz9 124004 1000 (@Eq.refl Real qz9)) (@Enclosure.pos_of_ble 2 rfl) (@Enclosure.pos_of_ble 32 rfl)

noncomputable def ep2223 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalEM.fstVal qz809) ep467 ep468

noncomputable def ep2224 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalEM.fstVal qz809) (hardyZApproximantEM 2 32 qz9) Bool.true

noncomputable def ep2225 := BSN.mul_neg_of_neg_pos_r (Zeta.Certificates.ZIntervalEM.fstVal qz809) (Zeta.Certificates.ZIntervalEM.sndVal qz809) (@ep2223 ep469 ep470 (@ep2224 ep467 ep468 ep469 ep470 (@Eq.refl Real (hardyZApproximantEM 2 32 qz9)) EMRow41.d15) rfl rfl rfl)

noncomputable def ep2226 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalEM.sndVal qz809) ep1291 ep1292

noncomputable def ep2227 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalEM.sndVal qz809) (hardyZApproximantEM 2 32 qz61) Bool.false

noncomputable def ep2228 := BSN.gt_trans_le (@Norm.norm Real Real.norm (Zeta.Certificates.ZIntervalEM.fstVal qz809)) (BSN.hardyZErrorBoundStrong 2 32 qz9)

noncomputable def ep2229 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalEM.fstVal qz809) (BSN.hardyZErrorBoundStrong 2 32 qz9) Bool.true

noncomputable def ep2230 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 2 32 qz9) (@HAdd.hAdd Real Real Real qz607 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 2 4) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz12 2 32))) (@HMul.hMul Real Real Real qz0 qz790 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235)))) Bool.false ep1870 ep1871 3545882201743646797 ep1872 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz607 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 2 4) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz12 2 32))) (@HMul.hMul Real Real Real qz0 qz790 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz12 (@ascPochhammer Complex Complex.instSemiring 5))) qz235)))))

noncomputable def ep2231 := BSN.gt_trans_le (@Norm.norm Real Real.norm (Zeta.Certificates.ZIntervalEM.sndVal qz809)) (BSN.hardyZErrorBoundStrong 2 32 qz61)

noncomputable def ep2232 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalEM.sndVal qz809) (BSN.hardyZErrorBoundStrong 2 32 qz61) Bool.false

noncomputable def ep2233 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 2 32 qz61) (@HAdd.hAdd Real Real Real qz607 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 2 4) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz64 2 32))) (@HMul.hMul Real Real Real qz0 qz800 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242)))) Bool.false ep2062 ep2063 38340838383713402849 ep2064 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz607 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 2 4) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz64 2 32))) (@HMul.hMul Real Real Real qz0 qz800 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz25 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz232)) ↑qz234) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz242)))))

noncomputable def ep2234 := @List.cons EMRow41.d0 (@PSigma.mk Zeta.Certificates.ZIntervalEM Zeta.Certificates.ZIntervalEM.Certificate qz809 (ep2222 (@Enclosure.pos_of_ble 2 rfl) (@Enclosure.pos_of_ble 32 rfl) (ep2225 (@ep2226 ep1293 ep1294 (@ep2227 ep1291 ep1292 ep1293 ep1294 (@Eq.refl Real (hardyZApproximantEM 2 32 qz61)) EMRow41.d21) rfl rfl rfl)) (ep2228 (hardyZErrorBoundEM 2 32 qz9) (BSN.hardyZErrorBoundEM_le_strong 2 32 qz9 rfl) (@ep2229 Bool.false ep467 ep468 ep469 ep470 ep1870 ep1871 3545882201743646797 ep1872 (@ep2224 ep467 ep468 ep469 ep470 (@Eq.refl Real (hardyZApproximantEM 2 32 qz9)) EMRow41.d15) (ep2230 EMRow41.d184) rfl rfl rfl rfl rfl)) (ep2231 (hardyZErrorBoundEM 2 32 qz61) (BSN.hardyZErrorBoundEM_le_strong 2 32 qz61 rfl) (@ep2232 Bool.false ep1291 ep1292 ep1293 ep1294 ep2062 ep2063 38340838383713402849 ep2064 (@ep2227 ep1291 ep1292 ep1293 ep1294 (@Eq.refl Real (hardyZApproximantEM 2 32 qz61)) EMRow41.d21) (ep2233 EMRow41.d185) rfl rfl rfl rfl rfl)))) (@List.nil EMRow41.d0)

noncomputable abbrev qz810 := (@NonemptyInterval Real Real.instLE)

noncomputable abbrev qz811 := (Zeta.Certificates.CertifiedZeroIntervals.intervals (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep2234 (@List.IsChain.singleton EMRow41.d1 EMRow41.d186 (EMRow41.d2 qz9 qz61 qz248))))

noncomputable def ep2235 := And (@Eq (Option Real) (@Option.map qz810 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz810 qz811)) (@Option.some Real qz9))

noncomputable def ep2236 := ep2235 (@Eq (Option Real) (@Option.map qz810 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz810 qz811)) (@Option.some Real qz61))

noncomputable def ep2237 := @And.intro (@Eq Nat (@List.length qz810 qz811) 1) ep2236

noncomputable def ep2238 := @And.intro (@Eq (Option Real) (@Option.map qz810 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz810 qz811)) (@Option.some Real qz9))

noncomputable def ep2239 := @ep2238 (@Eq (Option Real) (@Option.map qz810 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz810 qz811)) (@Option.some Real qz61))

noncomputable abbrev qz812 := (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep2234 (@List.IsChain.singleton EMRow41.d1 EMRow41.d186 (EMRow41.d2 qz9 qz61 qz248)))

theorem EMRow41.d187 : Zeta.Certificates.BatchSpec 1 124004 1000 126105 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz810 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 1) (And (@Eq (Option Real) (@Option.map qz810 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz810 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz9)) (@Eq (Option Real) (@Option.map qz810 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz810 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz61)))) qz812 (ep2237 (@Eq.refl Nat 1) (ep2239 (@Eq.refl (Option Real) (@Option.some Real qz9)) (@Eq.refl (Option Real) (@Option.some Real qz61))))

theorem solution : Zeta.Certificates.BatchSpec 1 124004 1000 126105 1000 := EMRow41.d187
#print axioms solution
#check solution
