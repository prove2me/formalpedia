-- Prove2me | solution 1 for RHHeight1000.em_main_0035_0035
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T09:37:46.302618+00:00
-- url     : https://prove2.me/submissions/9b063856-c0d1-499d-8934-09bfad17641b

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

noncomputable def EMRow35.d0 := @PSigma Zeta.Certificates.ZIntervalEM fun (I : Zeta.Certificates.ZIntervalEM) => Zeta.Certificates.ZIntervalEM.Certificate I

noncomputable def EMRow35.d1 := @NonemptyInterval Real Real.instLE

noncomputable def EMRow35.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h

noncomputable def EMRow35.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) (fc sc fb sb : Nat) => Zeta.Certificates.ZIntervalEM.mk (EMRow35.d2 a b h) fc sc fb sb

noncomputable def ep0 := nat_lit 26986075409044028275299783

noncomputable def ep1 := nat_lit 4294967296000000000000000

noncomputable def ep2 := nat_lit 26986075409044045455168967

noncomputable abbrev qz0 := (@instHMul Real Real.instMul)

noncomputable abbrev qz251 := (Enclosure.sfrac Bool.false 2 1)

noncomputable def ep3 := @BSN.isNear_log_image_fff (@HMul.hMul Real Real Real qz0 qz251 Real.pi) 884279719003555 140737488355328 1 500000000000000 ep0 ep1 ep2 ep1 4138529546116343 2251799813685248 125000000068807 34403500000000000000 4138529546116343 2251799813685248 125000000068807 34403500000000000000 963576 524288

noncomputable abbrev qz252 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 2 1) Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) BSN.pi_near_15 rfl)

noncomputable def ep4 := @ep3 3 524288 qz252 rfl rfl rfl rfl

noncomputable def ep5 := nat_lit 53972150818088056550599566

noncomputable def ep6 := nat_lit 34359738368000000000000000

noncomputable def ep7 := nat_lit 9806206225044028275299783

noncomputable def ep8 := nat_lit 44165944593044028275299783

noncomputable def ep9 := nat_lit 13681445815609410487519367394620474863599256634174726093703677122907123617368241606644861540940610176751640793056574796245399519365549113997355475306157239709119582688278313060810592403844863400465080549957745

noncomputable def ep10 := nat_lit 231714499556395493334623298703961145503103241611736774613091488581016477543539392410113701224645713379230392133956226737605624599560350113120270717249177907454870984269546186598262646369758174842349131395304

noncomputable def ep11 := nat_lit 8978369550011295664474073352761810093897501552430546263638635096022803738134167562509900960712119243631997923545019968443113540909076206607473711060286601587364321108377403290080403445693385008949995305

noncomputable def ep12 := BSN.log_dyadic_bound ep7 ep8 5 4 ep9 1048576 275228 ep10 ep11 473518 ep5 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep7) (BSN.artanhQ ep8) 0 4 ep10 ep9 ep11 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz1 := (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))

noncomputable def ep13 := ep4 rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep1 4138529546116343 2251799813685248 125000000068807 34403500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep0) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 69433004117575847641088 37778931862957161709568 1000000000550456 275228000000000000000 4138529546116343 2251799813685248 125000000068807 34403500000000000000 (BSN.log_rat_reduce_isNear ep0 ep1 2 ep5 ep6 473518 1048576 24973259072661432 36028797018963968 275228 1000000000000000 rfl rfl rfl rfl (ep12 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep14 := nat_lit 53972150818088090910337934

noncomputable def ep15 := nat_lit 9806206225044045455168967

noncomputable def ep16 := nat_lit 44165944593044045455168967

noncomputable def ep17 := nat_lit 13681445815609453062485491347592146866046743284321690683909457683007658987562290830600045658905080811372395010565947827677605470036294121079488508864180301737865471494204890974265645509835068840465080549957745

noncomputable def ep18 := nat_lit 231714499556396865510889920206523150079811393376960301632499817942333196803513131357563499488546302200815366867712007119763002650772307103678175657719139104636874731038771518520299266622696414842349131395304

noncomputable def ep19 := nat_lit 8978369550011421500876706511871067098718760264493934208903156435737864998391937547068187824077011975074541700434630537294838404525415248443919841847024664017658842168336182958576672102333385008949995305

noncomputable def ep20 := BSN.log_dyadic_bound ep15 ep16 5 4 ep17 1048576 275228 ep18 ep19 473518 ep14 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep15) (BSN.artanhQ ep16) 0 4 ep18 ep17 ep19 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep21 := ep13 (BSN.isNear_log_sfrac ep2 ep1 4138529546116343 2251799813685248 125000000068807 34403500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep2) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 69433004117575847641088 37778931862957161709568 1000000000550456 275228000000000000000 4138529546116343 2251799813685248 125000000068807 34403500000000000000 (BSN.log_rat_reduce_isNear ep2 ep1 2 ep14 ep6 473518 1048576 24973259072661432 36028797018963968 275228 1000000000000000 rfl rfl rfl rfl (ep20 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable abbrev qz253 := (Real.log (@HMul.hMul Real Real Real qz0 (2 : Real) Real.pi))

theorem EMRow35.d4 : Enclosure.Real.IsNear qz253 Bool.false 120447 65536 3 524288 := @Enclosure.Real.IsNear.of_eq qz253 (Real.log (@HMul.hMul Real Real Real qz0 qz251 Real.pi)) Bool.false 120447 65536 3 524288 BSN.log_two_pi_eq (@Enclosure.Real.IsNear.recentre' (Real.log (@HMul.hMul Real Real Real qz0 qz251 Real.pi)) Bool.false 963576 524288 3 524288 120447 65536 3 524288 (ep21 rfl rfl rfl rfl rfl rfl rfl rfl) rfl)

noncomputable abbrev qz543 := (@instHPow Complex Nat (@NPow.toPow Complex (@Monoid.toNPow Complex (@Semiring.toMonoid Complex Complex.instSemiring))))

noncomputable abbrev qz812 := (@instHAdd Complex Complex.instAdd)

noncomputable abbrev qz813 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (4 : Complex))

noncomputable abbrev qz814 := (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid))

noncomputable abbrev qz544 := (@HAdd.hAdd Complex Complex Complex qz812 (@HAdd.hAdd Complex Complex Complex qz812 qz813 (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I (@HDiv.hDiv Complex Complex Complex qz814 (↑(Enclosure.sfrac Bool.false 111131 1000)) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 4))

noncomputable abbrev qz254 := (@HPow.hPow Complex Nat Complex qz543 qz544 3)

noncomputable abbrev qz2 := qz254

noncomputable def ep22 := Enclosure.Complex.IsNear qz2 Bool.true 628626807211 16000000 0 1 Bool.true 1348391225611091 8000000000 0 1

noncomputable abbrev qz545 := (@instHMul Complex Complex.instMul)

noncomputable abbrev qz255 := qz545

noncomputable abbrev qz3 := qz255

noncomputable abbrev qz256 := qz543

noncomputable abbrev qz257 := qz544

noncomputable abbrev qz4 := (@HPow.hPow Complex Nat Complex qz256 qz257 2)

noncomputable abbrev qz5 := qz257

noncomputable def ep23 := @Enclosure.Complex.IsNear.of_eq qz2 (@HMul.hMul Complex Complex Complex qz3 qz4 qz5) Bool.true 628626807211 16000000 0 1 Bool.true 1348391225611091 8000000000

noncomputable def ep24 := @Enclosure.Complex.IsNear.mul qz4 qz5 Bool.true 628626807211 16000000 0 1 Bool.true 1348391225611091 8000000000 0

noncomputable abbrev qz6 := (Complex.re qz257)

noncomputable abbrev qz7 := (Complex.im qz257)

noncomputable def ep25 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re qz4) qz6) (@HMul.hMul Real Real Real qz0 (Complex.im qz4) qz7) 208723435737 16000000 0 1 209951685737 8000000

noncomputable def ep26 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re qz4) qz6 12277849161 4000000 0 1 17000 4000 0 1

noncomputable def ep27 := @Enclosure.Complex.IsNear.re_isNear qz4 Bool.true 12277849161 4000000 0 1 Bool.false 1889227 4000 0 1

noncomputable abbrev qz258 := (@HPow.hPow Complex Nat Complex qz543 qz544 1)

noncomputable abbrev qz8 := qz258

noncomputable def ep28 := @Enclosure.Complex.IsNear.of_eq qz4 (@HMul.hMul Complex Complex Complex qz3 qz8 qz5) Bool.true 12277849161 4000000 0 1 Bool.false 1889227 4000

noncomputable def ep29 := @Enclosure.Complex.IsNear.mul qz8 qz5 Bool.true 12277849161 4000000 0 1 Bool.false 1889227 4000 0

noncomputable abbrev qz9 := (Complex.re qz258)

noncomputable abbrev qz10 := (Complex.im qz258)

noncomputable def ep30 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz9 qz6) (@HMul.hMul Real Real Real qz0 qz10 qz7) 289 16 0 1 12350099161 4000000

noncomputable def ep31 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz6 17000 4000 0 1 17000 4000 0 1

noncomputable def ep32 := @Enclosure.Complex.IsNear.re_isNear qz8 Bool.false 17000 4000 0 1 Bool.false 222262 4000 0 1

noncomputable def ep33 := @Enclosure.Complex.IsNear.of_eq qz8 qz5 Bool.false 17000 4000 0 1 Bool.false 222262 4000 0

noncomputable abbrev qz259 := (Enclosure.sfrac Bool.false 111131 1000)

noncomputable abbrev qz11 := qz259

noncomputable abbrev qz260 := (Enclosure.sfrac Bool.false 222262 4000)

noncomputable abbrev qz546 := (Complex.mk (Enclosure.sfrac Bool.false 17000 4000) qz260)

noncomputable def ep34 := @Enclosure.Complex.IsNear.of_eq qz5 qz546 Bool.false 17000 4000 0 1 Bool.false 222262 4000 0 1 (BSN.w_shift_mk qz11 Bool.false 111131 1000 4 (@Eq.refl Real qz11) rfl)

noncomputable abbrev qz547 := (Enclosure.sfrac Bool.false 17000 4000)

noncomputable abbrev qz12 := (@ep33 1 (BSN.pow_one_c qz257) (ep34 (@Enclosure.Complex.IsNear.mk qz547 qz260 Bool.false 17000 4000 0 1 Bool.false 222262 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 17000 4000) (Enclosure.Real.IsNear.const Bool.false 222262 4000))))

noncomputable abbrev qz13 := (ep34 (@Enclosure.Complex.IsNear.mk qz547 qz260 Bool.false 17000 4000 0 1 Bool.false 222262 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 17000 4000) (Enclosure.Real.IsNear.const Bool.false 222262 4000)))

noncomputable abbrev qz815 := (@Enclosure.Complex.IsNear.re_isNear qz5 Bool.false 17000 4000 0 1 Bool.false 222262 4000 0 1 qz13)

noncomputable def ep35 := @ep31 289 16 0 1 (ep32 qz12) qz815

noncomputable def ep36 := @Enclosure.Real.IsNear.mulLit_ff qz10 qz7 222262 4000 0 1 222262 4000 0 1

noncomputable def ep37 := @Enclosure.Complex.IsNear.im_isNear qz8 Bool.false 17000 4000 0 1 Bool.false 222262 4000 0 1

noncomputable abbrev qz816 := (@Enclosure.Complex.IsNear.im_isNear qz5 Bool.false 17000 4000 0 1 Bool.false 222262 4000 0 1 qz13)

noncomputable def ep38 := @ep36 12350099161 4000000 0 1 (ep37 qz12) qz816

noncomputable def ep39 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz9 qz7) (@HMul.hMul Real Real Real qz0 qz10 qz6) 1889227 8000 0 1 1889227 8000

noncomputable def ep40 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz7 17000 4000 0 1 222262 4000 0 1

noncomputable def ep41 := @ep40 1889227 8000 0 1 (ep32 qz12) qz816

noncomputable def ep42 := @Enclosure.Real.IsNear.mulLit_ff qz10 qz6 222262 4000 0 1 17000 4000 0 1

noncomputable def ep43 := @ep42 1889227 8000 0 1 (ep37 qz12) qz815

noncomputable abbrev qz548 := (@ep28 0 1 (BSN.pow_succ_c qz5 1 2 rfl) (@ep29 1 (@ep30 0 1 196445586576 12277849161 4000000 0 1 (ep35 rfl) (ep38 rfl) rfl rfl) (@ep39 0 1 30227632000 1889227 4000 0 1 (ep41 rfl) (ep43 rfl) rfl rfl)))

noncomputable def ep44 := @ep26 208723435737 16000000 0 1 (ep27 qz548) qz815

noncomputable def ep45 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz4) qz7 1889227 4000 0 1 222262 4000 0 1

noncomputable def ep46 := @Enclosure.Complex.IsNear.im_isNear qz4 Bool.true 12277849161 4000000 0 1 Bool.false 1889227 4000 0 1

noncomputable def ep47 := @ep45 209951685737 8000000 0 1 (ep46 qz548) qz816

noncomputable def ep48 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re qz4) qz7) (@HMul.hMul Real Real Real qz0 (Complex.im qz4) qz6) 1364449655111091 8000000000 0 1 32116859 16000

noncomputable def ep49 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re qz4) qz7 12277849161 4000000 0 1 222262 4000 0 1

noncomputable def ep50 := @ep49 1364449655111091 8000000000 0 1 (ep27 qz548) qz816

noncomputable def ep51 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz4) qz6 1889227 4000 0 1 17000 4000 0 1

noncomputable def ep52 := @ep51 32116859 16000 0 1 (ep46 qz548) qz815

theorem EMRow35.d5 : ep22 := @ep23 0 1 (BSN.pow_succ_c qz5 2 3 rfl) (@ep24 1 (@ep25 0 1 5029014457688000000 628626807211 16000000 0 1 (ep44 rfl) (ep47 rfl) rfl rfl) (@ep48 0 1 21574259609777456000 1348391225611091 8000000000 0 1 (ep50 rfl) (ep52 rfl) rfl rfl))

noncomputable def ep53 := nat_lit 8589934592000000000000000

noncomputable def ep54 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 ep0 ep53 ep2 ep53 1200336 1048576 1 275228 1200336 1048576 1 275228 600168 524288 2 524288 BSN.pi_near_15 rfl rfl rfl

noncomputable def ep55 := nat_lit 17179869184000000000000000

noncomputable def ep56 := nat_lit 18396140817044028275299783

noncomputable def ep57 := nat_lit 35576010001044028275299783

noncomputable def ep58 := nat_lit 145019262663961446558303139663424756232419223153299357158415217874016130572233056993847515999529612750616182853355499335896178729185698845314776375864537073527142908641610750276034469165612529925303649396973267518946591078603565291376312767403717761600170009932259137778521478520425507632472584532570900560707662248426541531715360699177249902784721815296292248142738824858695953661559845440650653128788875447728828657762006237171740033404723254477174341920697506370253193455781322964835857351124092897592956162654178130575

noncomputable def ep59 := nat_lit 15500762873619990602332184736899274490522931101512051618692838888825382235673431503644115344741331161500627469184702974962114537943617674254904297224139410345221262767191485292268260077615645253784097850065864022184521411511133693085443040736512010941548648374196772723338837137976260321103066698629790037694560548409922339907589559883712609967105556007429010014773911317423638534096849366294542840133852248768895750397896505791271178551667935288585787166713880920071720072716082683081155281219708172458141800988558163320

noncomputable def ep60 := nat_lit 12900190794487083783367107939442176642390171280542213571554777169279725287102813254708993369099729304728646904879886535518616983985412662170766446331701281703998252143668221340329975389245922410714088123244705567402747658401492589451585970559635763980329972215329212888079422466283203384882259392047898400615815810081169907384366653346471604103896809335921621947903075223769953790093549808584241881353287841076643853121427928248525828402335494512605306631304432120211393210317325496757155861061354331245840675149075

noncomputable def ep61 := BSN.log_dyadic_bound ep56 ep57 11 10 ep58 1048576 275228 ep59 ep60 1200336 ep5 ep55 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep56) (BSN.artanhQ ep57) 0 10 ep59 ep58 ep60 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep62 := nat_lit 18396140817044045455168967

noncomputable def ep63 := nat_lit 35576010001044045455168967

noncomputable def ep64 := nat_lit 145019262663962847171784895425483977818796535899227200426399035286881207006285364467913811844950531107314785650583974625982406238691319033447632878979985852280879486690814033867010958364699188952871572448188560932645032521756218245629809291975913196623825614492380080480004685076434733043183791438169545293975334857826316990371107134320667652578346815517853870648072772035977941843998949310557583393428557296298890786965786350523173236912472938174255438182435383147950274229549088258679583524155427309880956162654178130575

noncomputable def ep65 := nat_lit 15500762873620157189619721156942591192100275120160672416764593300158228469749443299607348495591439275767946573253526107895503597951484257520435868240203420954375895980141891044871083424251900562230440202302413072793440172565998181227591194192658878334739610458454844032013325963992941389843551995646587189684848765634635122388286241104146031552341815777883628509454807838726994150833304950745987647656768534710890974432620160470644835720379148964170536679305861738540146791997074363921127776563807649880221800988558163320

noncomputable def ep66 := nat_lit 12900190794487324729109480814509220959173684627296055849229843377126536688487849343376525559792931631054411655715865486295286288812423905434305314401904993536755333953308594664509631000767632482919425633906965368325056855874260596615770736441041599390097968820060635361729170158825410327022636428624381203910573184452046894301676992229743752846881064485858738985580654099214803581683226335297196686880535448467637789069028262446657986458573827723305156755787640135484017403116612632808333639900906331245840675149075

noncomputable def ep67 := BSN.log_dyadic_bound ep62 ep63 11 10 ep64 1048576 275228 ep65 ep66 1200336 ep14 ep55 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep62) (BSN.artanhQ ep63) 0 10 ep65 ep64 ep66 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep68 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 600168 524288 2 524288 75021 65536 1 262144 (ep54 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep53 1200336 1048576 1 275228 Bool.false (BSN.logfrac_isNear ep5 ep55 1 ep0 ep53 1200336 1048576 275228 rfl rfl rfl (ep61 rfl))) (BSN.isNear_log_sfrac ep2 ep53 1200336 1048576 1 275228 Bool.false (BSN.logfrac_isNear ep14 ep55 1 ep2 ep53 1200336 1048576 275228 rfl rfl rfl (ep67 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl

theorem EMRow35.d6 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 75021 65536 1 262144 := ep68

noncomputable abbrev qz549 := qz812

noncomputable abbrev qz550 := (@HDiv.hDiv Complex Complex Complex qz814 (1 : Complex) (2 : Complex))

noncomputable abbrev qz261 := (@HAdd.hAdd Complex Complex Complex qz549 qz550 (@HMul.hMul Complex Complex Complex qz545 Complex.I ↑(Enclosure.sfrac Bool.false 111131 1000)))

noncomputable abbrev qz14 := qz261

noncomputable abbrev qz262 := qz549

noncomputable abbrev qz15 := qz262

noncomputable abbrev qz16 := (@instHPow Complex Complex Complex.instPow)

noncomputable abbrev qz17 := (@Neg.neg Complex Complex.instNeg qz261)

noncomputable abbrev qz817 := (@Nat.cast Complex Complex.instNatCast 8)

noncomputable def ep69 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 9) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz14 8) (@HPow.hPow Complex Complex Complex qz16 qz817 qz17)) Bool.true 1003345547239 1099511627776 208337984489107 75654096572383232 Bool.true 484384381091 1099511627776 208324189511291 75654096572383232

noncomputable def ep70 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz14 8) (@HPow.hPow Complex Complex Complex qz16 qz817 qz17) Bool.true 537112235821 549755813888 23315575984851 9456762071547904 Bool.true 866603176637 1099511627776 186453028163129 75654096572383232 Bool.false

noncomputable abbrev qz818 := (@Nat.cast Complex Complex.instNatCast 7)

noncomputable def ep71 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 8) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz14 7) (@HPow.hPow Complex Complex Complex qz16 qz818 qz17)) Bool.true 537112235821 549755813888 23315575984851 9456762071547904 Bool.true 866603176637 1099511627776 186453028163129 75654096572383232

noncomputable def ep72 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz14 7) (@HPow.hPow Complex Complex Complex qz16 qz818 qz17) Bool.true 89174985899 137438953472 81564606308801 37827048286191616 Bool.true 82553125439 137438953472 81542240731065 37827048286191616 Bool.true

noncomputable abbrev qz819 := (@Nat.cast Complex Complex.instNatCast 6)

noncomputable def ep73 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 7) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz14 6) (@HPow.hPow Complex Complex Complex qz16 qz819 qz17)) Bool.true 89174985899 137438953472 81564606308801 37827048286191616 Bool.true 82553125439 137438953472 81542240731065 37827048286191616

noncomputable def ep74 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz14 6) (@HPow.hPow Complex Complex Complex qz16 qz819 qz17) Bool.true 275285738981 549755813888 34475211904273 18913524143095808 Bool.true 539362055339 549755813888 34453763386233 18913524143095808 Bool.true

noncomputable abbrev qz18 := (@Nat.cast Complex Complex.instNatCast 5)

noncomputable def ep75 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 6) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz14 5) (@HPow.hPow Complex Complex Complex qz16 qz18 qz17)) Bool.true 275285738981 549755813888 34475211904273 18913524143095808 Bool.true 539362055339 549755813888 34453763386233 18913524143095808

noncomputable def ep76 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz14 5) (@HPow.hPow Complex Complex Complex qz16 qz18 qz17) Bool.true 69920900639 1099511627776 110222711333727 75654096572383232 Bool.true 487498561013 549755813888 6887013947403 4728381035773952 Bool.true

noncomputable abbrev qz551 := (@Nat.cast Complex Complex.instNatCast 4)

noncomputable abbrev qz263 := qz551

noncomputable abbrev qz19 := qz263

noncomputable def ep77 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 5) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz14 4) (@HPow.hPow Complex Complex Complex qz16 qz19 qz17)) Bool.true 69920900639 1099511627776 110222711333727 75654096572383232 Bool.true 487498561013 549755813888 6887013947403 4728381035773952

noncomputable def ep78 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz14 4) (@HPow.hPow Complex Complex Complex qz16 qz19 qz17) Bool.false 118934664729 274877906944 19830240952269 18913524143095808 Bool.true 1041973213415 1099511627776 79353297663323 75654096572383232 Bool.true

noncomputable abbrev qz552 := (@Nat.cast Complex Complex.instNatCast 3)

noncomputable def ep79 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 4) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz14 3) (@HPow.hPow Complex Complex Complex qz16 qz552 qz17)) Bool.false 118934664729 274877906944 19830240952269 18913524143095808 Bool.true 1041973213415 1099511627776 79353297663323 75654096572383232

noncomputable def ep80 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz14 3) (@HPow.hPow Complex Complex Complex qz16 qz552 qz17) Bool.false 1052146740921 1099511627776 43655855760511 75654096572383232 Bool.true 776026822285 1099511627776 43723475564533 75654096572383232 Bool.true

noncomputable abbrev qz553 := (@Nat.cast Complex Complex.instNatCast 2)

noncomputable def ep81 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 3) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz14 2) (@HPow.hPow Complex Complex Complex qz16 qz553 qz17)) Bool.false 1052146740921 1099511627776 43655855760511 75654096572383232 Bool.true 776026822285 1099511627776 43723475564533 75654096572383232

noncomputable def ep82 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz14 2) (@HPow.hPow Complex Complex Complex qz16 qz553 qz17) Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.true

noncomputable abbrev qz554 := (Enclosure.sfrac Bool.false 0 1)

noncomputable abbrev qz264 := qz554

noncomputable def ep83 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz264) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz14)

noncomputable abbrev qz265 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2)))

noncomputable abbrev qz266 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 2 1)))

noncomputable def ep84 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz553 qz17) (Complex.mk (@HMul.hMul Real Real Real qz0 qz265 (Real.cos qz266)) (@HMul.hMul Real Real Real qz0 qz265 (@Neg.neg Real Real.instNeg (Real.sin qz266)))) Bool.true 47364886855 1099511627776 43655855760511 75654096572383232 Bool.true 776026822285 1099511627776 43723475564533 75654096572383232 (BSN.cpow_neg_s_mk qz11 111131 1000 2 (@Eq.refl Real qz11) rfl)

noncomputable abbrev qz267 := (@Nat.cast Real Real.instNatCast 1)

noncomputable def ep85 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 2)) 1482911 1048576 1 1048576 370727 370728 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 2)) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2) qz267)) Bool.false 1482911 1048576 1 1048576 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2) qz267)) Bool.false 1482911 1048576 1 1048576 1482911 1048576 1 1048576 (BSN.sqrt_enclosure 2 1 741455 741456 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep86 := BSN.log_dyadic_bound 1 3 6 5 613814355 524288 137614 24381081 945 363408 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 1) (BSN.artanhQ 3) 0 5 24381081 613814355 945 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz268 := (BSN.sinEvenQ 2147483648)

noncomputable abbrev qz269 := (BSN.sinOddQ 2147483648)

noncomputable def ep87 := BSN.sin_dyadic_bound_f 130909943 2147483648 1 0 1048576 275497 0 1 1 0 1 1 63881 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 130909943) qz268 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 130909943) qz269 0 0 rfl) rfl rfl

noncomputable abbrev qz270 := (Real.log (Enclosure.sfrac Bool.false 2 1))

noncomputable abbrev qz271 := (Enclosure.Real.IsNear.const Bool.false 111131 1000)

noncomputable abbrev qz555 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 20192947) (@Nat.cast Real Real.instNatCast 262144))

noncomputable abbrev qz556 := (BSN.isNear_log_sfrac 2 1 363408 524288 1 137614 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 363408 524288 137614 rfl rfl rfl (ep86 rfl)))

noncomputable abbrev qz557 := (@Nat.cast Real Real.instNatCast 37778931862957161709568)

noncomputable def ep88 := @Enclosure.Real.IsNear.cos_image qz266 qz555 Bool.false 20192947 262144 53 65536 Bool.true 63881 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz266 Bool.false 2524118403 32768000 111131 137614000 20192947 262144 53 65536 (@Enclosure.Real.IsNear.mulLit_ff qz11 qz270 111131 1000 0 1 363408 524288 1 137614 2524118403 32768000 111131 137614000 qz271 qz556 rfl) rfl) (Enclosure.sfrac_false_div 20192947 262144) (BSN.cos_reduce1 qz555 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2302992082967990370304) qz557) 226375608064910080 72057594037927936 Bool.false 63881 1048576 12 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q1 20192947 262144 226375608064910080 72057594037927936 12 2302992082967990370304 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 63881 1048576 2302992082967990370304 37778931862957161709568 130909943 2147483648 275497 275228 (ep87 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz272 := (BSN.cosEvenQ 2147483648)

noncomputable abbrev qz273 := (BSN.cosOddQ 2147483648)

noncomputable def ep89 := BSN.cos_dyadic_bound_f 130909943 2147483648 1 0 1048576 275497 0 1 1 0 1 1 1046627 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 130909943) qz272 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 130909943) qz273 0 0 rfl) rfl rfl

noncomputable def ep90 := @Enclosure.Real.IsNear.sin_image qz266 qz555 Bool.false 20192947 262144 53 65536 Bool.false 1046627 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz266 Bool.false 2524118403 32768000 111131 137614000 20192947 262144 53 65536 (@Enclosure.Real.IsNear.mulLit_ff qz11 qz270 111131 1000 0 1 363408 524288 1 137614 2524118403 32768000 111131 137614000 qz271 qz556 rfl) rfl) (Enclosure.sfrac_false_div 20192947 262144) (BSN.sin_reduce1 qz555 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2302992082967990370304) qz557) 226375608064910080 72057594037927936 Bool.false 1046627 1048576 12 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q1 20192947 262144 226375608064910080 72057594037927936 12 2302992082967990370304 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1046627 1048576 2302992082967990370304 37778931862957161709568 130909943 2147483648 275497 275228 (ep89 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz558 := (@Enclosure.Real.IsNear.recentre' qz265 Bool.false 741455 1048576 1 1048576 741455 1048576 1 1048576 (ep85 rfl rfl) rfl)

noncomputable def ep91 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz265 (Real.cos qz266)) (@HMul.hMul Real Real Real qz0 qz265 (@Neg.neg Real Real.instNeg (Real.sin qz266))) Bool.true 47364886855 1099511627776 43655855760511 75654096572383232 Bool.true 776026822285 1099511627776 43723475564533 75654096572383232 (@Enclosure.Real.IsNear.mulLit_ft qz265 (Real.cos qz266) 741455 1048576 1 1048576 63881 1048576 3679539 4509335552 47364886855 1099511627776 43655855760511 75654096572383232 qz558 (@Enclosure.Real.IsNear.recentre' (Real.cos qz266) Bool.true 63881 1048576 7359078 9018671104 63881 1048576 3679539 4509335552 (ep88 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz265 (@Neg.neg Real Real.instNeg (Real.sin qz266)) 741455 1048576 1 1048576 1046627 1048576 3679539 4509335552 776026822285 1099511627776 43723475564533 75654096572383232 qz558 (@Enclosure.Real.IsNear.neg (Real.sin qz266) Bool.false 1046627 1048576 3679539 4509335552 (@Enclosure.Real.IsNear.recentre' (Real.sin qz266) Bool.false 1046627 1048576 7359078 9018671104 1046627 1048576 3679539 4509335552 (ep90 rfl rfl) rfl)) rfl)

noncomputable abbrev qz820 := (Enclosure.Real.IsNear.const Bool.false 0 1)

noncomputable abbrev qz274 := qz820

noncomputable def ep92 := @ep82 47364886855 1099511627776 43655855760511 75654096572383232 Bool.true 776026822285 1099511627776 43723475564533 75654096572383232 Bool.false 1052146740921 1052146740921 1099511627776 43655855760511 75654096572383232 Bool.true 776026822285 776026822285 1099511627776 43723475564533 75654096572383232 (ep83 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz264 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz274)) (ep84 ep91) rfl rfl

noncomputable abbrev qz275 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 3)))

noncomputable abbrev qz276 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 3 1)))

noncomputable def ep93 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz552 qz17) (Complex.mk (@HMul.hMul Real Real Real qz0 qz275 (Real.cos qz276)) (@HMul.hMul Real Real Real qz0 qz275 (@Neg.neg Real Real.instNeg (Real.sin qz276)))) Bool.true 576408082005 1099511627776 35665108048565 75654096572383232 Bool.true 132973195565 549755813888 17814911049395 37827048286191616 (BSN.cpow_neg_s_mk qz11 111131 1000 3 (@Eq.refl Real qz11) rfl)

noncomputable def ep94 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 3)) 1816187 1048576 1 1048576 302697 302698 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 3)) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3) qz267)) Bool.false 1816187 1048576 1 1048576 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3) qz267)) Bool.false 1816187 1048576 1 1048576 1816187 1048576 1 1048576 (BSN.sqrt_enclosure 3 1 908093 908094 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep95 := BSN.log_dyadic_bound 1 2 10 9 171633298636800 524288 137614 16925142283965 34459425 575989 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP 1) (BSN.artanhQ 2) 0 9 16925142283965 171633298636800 34459425 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep96 := nat_lit 2299406386279153557335178946486744102073332161648201809563281872252236346807265

noncomputable def ep97 := nat_lit 164135286493895707012911871249815109382010203263545499525931125331216861264609280

noncomputable def ep98 := nat_lit 1276869470466274645747422106719803660318868477674958925937159567738493064161

noncomputable def ep99 := nat_lit 6020187508731313919784734747863926299503925112495721472499935216598566205248481

noncomputable def ep100 := nat_lit 3009146919054754628570050972913277005336853726498334157975403964405642456517836800

noncomputable def ep101 := BSN.sin_dyadic_bound_f 2444940603 2147483648 3 2 1048576 275497 ep96 ep97 ep98 ep99 ep100 ep98 952119 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2444940603) qz268 0 2 ep96 ep97 ep98 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2444940603) qz269 0 2 ep99 ep100 ep98 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz277 := (@Nat.cast Real Real.instNatCast 1048576)

noncomputable abbrev qz278 := (Real.log (Enclosure.sfrac Bool.false 3 1))

noncomputable abbrev qz279 := (@Nat.cast Real Real.instNatCast 151115727451828646838272)

noncomputable abbrev qz559 := (BSN.isNear_log_sfrac 3 1 575989 524288 1 137614 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 575989 524288 137614 rfl rfl rfl (ep95 rfl)))

noncomputable abbrev qz821 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 128020467) qz277)

noncomputable def ep102 := @Enclosure.Real.IsNear.cos_image qz276 qz821 Bool.false 128020467 1048576 847 1048576 Bool.true 952119 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz276 Bool.false 64010233559 524288000 111131 137614000 128020467 1048576 847 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz11 qz278 111131 1000 0 1 575989 524288 1 137614 64010233559 524288000 111131 137614000 qz271 qz559 rfl) rfl) (Enclosure.sfrac_false_div 128020467 1048576) (BSN.cos_reduce1 qz821 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 172047399889021450584064) qz279) 226375608064910080 72057594037927936 Bool.false 952119 1048576 19 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q1 128020467 1048576 226375608064910080 72057594037927936 19 172047399889021450584064 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 952119 1048576 172047399889021450584064 151115727451828646838272 2444940603 2147483648 275497 275228 (ep101 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep103 := nat_lit 1278015489919736987250987157873399969445326253572412098168906444392459522921441

noncomputable def ep104 := nat_lit 18237254054877300779212430138868345486890022584838388836214569481246317918289920

noncomputable def ep105 := nat_lit 3831492730818278412461466629406760301015341023761886376654845014041901582636001

noncomputable def ep106 := nat_lit 820676432469478535064559356249075546910051016317727497629655626656084306323046400

noncomputable def ep107 := BSN.cos_dyadic_bound_f 2444940603 2147483648 3 2 1048576 275497 ep103 ep104 ep98 ep105 ep106 ep98 439294 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2444940603) qz272 0 2 ep103 ep104 ep98 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2444940603) qz273 0 2 ep105 ep106 ep98 rfl rfl rfl rfl) rfl rfl

noncomputable def ep108 := @Enclosure.Real.IsNear.sin_image qz276 qz821 Bool.false 128020467 1048576 847 1048576 Bool.false 439294 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz276 Bool.false 64010233559 524288000 111131 137614000 128020467 1048576 847 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz11 qz278 111131 1000 0 1 575989 524288 1 137614 64010233559 524288000 111131 137614000 qz271 qz559 rfl) rfl) (Enclosure.sfrac_false_div 128020467 1048576) (BSN.sin_reduce1 qz821 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 172047399889021450584064) qz279) 226375608064910080 72057594037927936 Bool.false 439294 1048576 19 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q1 128020467 1048576 226375608064910080 72057594037927936 19 172047399889021450584064 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 439294 1048576 172047399889021450584064 151115727451828646838272 2444940603 2147483648 275497 275228 (ep107 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz560 := (@Enclosure.Real.IsNear.recentre' qz275 Bool.false 605395 1048576 1 1048576 605395 1048576 1 1048576 (ep94 rfl rfl) rfl)

noncomputable def ep109 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz275 (Real.cos qz276)) (@HMul.hMul Real Real Real qz0 qz275 (@Neg.neg Real Real.instNeg (Real.sin qz276))) Bool.true 576408082005 1099511627776 35665108048565 75654096572383232 Bool.true 132973195565 549755813888 17814911049395 37827048286191616 (@Enclosure.Real.IsNear.mulLit_ft qz275 (Real.cos qz276) 605395 1048576 1 1048576 952119 1048576 58803817 72149368832 576408082005 1099511627776 35665108048565 75654096572383232 qz560 (@Enclosure.Real.IsNear.recentre' (Real.cos qz276) Bool.true 952119 1048576 117607634 144298737664 952119 1048576 58803817 72149368832 (ep102 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz275 (@Neg.neg Real Real.instNeg (Real.sin qz276)) 605395 1048576 1 1048576 219647 524288 58803817 72149368832 132973195565 549755813888 17814911049395 37827048286191616 qz560 (@Enclosure.Real.IsNear.neg (Real.sin qz276) Bool.false 219647 524288 58803817 72149368832 (@Enclosure.Real.IsNear.recentre' (Real.sin qz276) Bool.false 439294 1048576 117607634 144298737664 219647 524288 58803817 72149368832 (ep108 rfl rfl) rfl)) rfl)

noncomputable def ep110 := @ep80 576408082005 1099511627776 35665108048565 75654096572383232 Bool.true 132973195565 549755813888 17814911049395 37827048286191616 Bool.false 523080187260702415650816 118934664729 274877906944 19830240952269 18913524143095808 Bool.true 572830831990458044907520 1041973213415 1099511627776 79353297663323 75654096572383232 (ep81 (BSN.head_sum_c_succ qz14 2 3 rfl rfl) (ep92 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep93 ep109) rfl rfl

noncomputable abbrev qz280 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 4)))

noncomputable abbrev qz281 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 4 1)))

noncomputable def ep111 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz19 qz17) (Complex.mk (@HMul.hMul Real Real Real qz0 qz280 (Real.cos qz281)) (@HMul.hMul Real Real Real qz0 qz280 (@Neg.neg Real Real.instNeg (Real.sin qz281)))) Bool.true 545659559555 1099511627776 30901747524651 75654096572383232 Bool.false 66976091389 1099511627776 30838925495125 75654096572383232 (BSN.cpow_neg_s_mk qz11 111131 1000 4 (@Eq.refl Real qz11) rfl)

noncomputable def ep112 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 4)) 2097153 1048576 1 1048576 262143 262144 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 4)) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4) qz267)) Bool.false 2097153 1048576 1 1048576 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4) qz267)) Bool.false 2097153 1048576 1 1048576 2097153 1048576 1 1048576 (BSN.sqrt_enclosure 4 1 1048576 1048577 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep113 := nat_lit 318077276165597140789031982421875

noncomputable def ep114 := nat_lit 49379992292270016474244603430625

noncomputable def ep115 := nat_lit 20095619060363156210525625

noncomputable def ep116 := BSN.log_dyadic_bound 3 5 14 13 ep113 524288 137614 ep114 ep115 726817 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base13 (BSN.artanhP 3) (BSN.artanhQ 5) 0 13 ep114 ep113 ep115 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep117 := nat_lit 4732075722172885665773112258367041

noncomputable def ep118 := nat_lit 510423550381407695195061911147652317184

noncomputable def ep119 := nat_lit 7656353255721115427925928667214784757760

noncomputable def ep120 := BSN.cos_dyadic_bound_f 262278639 2147483648 2 1 1048576 275497 ep117 ep118 ep117 ep117 ep119 ep117 1040765 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 262278639) qz272 0 1 ep117 ep118 ep117 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 262278639) qz273 0 1 ep117 ep119 ep117 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz282 := (Real.log (Enclosure.sfrac Bool.false 4 1))

noncomputable abbrev qz561 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 20192975) (@Nat.cast Real Real.instNatCast 131072))

noncomputable abbrev qz562 := (BSN.isNear_log_sfrac 4 1 726817 524288 1 137614 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 726817 524288 137614 rfl rfl rfl (ep116 rfl)))

noncomputable abbrev qz563 := (@Nat.cast Real Real.instNatCast 18889465931478580854784)

noncomputable def ep121 := @Enclosure.Real.IsNear.cos_image qz281 qz561 Bool.false 20192975 131072 847 1048576 Bool.true 1040765 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz281 Bool.false 80771900027 524288000 111131 137614000 20192975 131072 847 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz11 qz282 111131 1000 0 1 726817 524288 1 137614 80771900027 524288000 111131 137614000 qz271 qz562 rfl) rfl) (Enclosure.sfrac_false_div 20192975 131072) (BSN.cos_reduce2 qz561 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2307027308234114334720) qz563) 226375608064910080 72057594037927936 Bool.false 1040765 1048576 24 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q2 20192975 131072 226375608064910080 72057594037927936 24 2307027308234114334720 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1040765 1048576 2307027308234114334720 18889465931478580854784 262278639 2147483648 275497 275228 (ep120 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep122 := BSN.sin_dyadic_bound_f 262278639 2147483648 1 0 1048576 275497 0 1 1 0 1 1 127747 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 262278639) qz268 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 262278639) qz269 0 0 rfl) rfl rfl

noncomputable def ep123 := @Enclosure.Real.IsNear.sin_image qz281 qz561 Bool.false 20192975 131072 847 1048576 Bool.true 127747 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz281 Bool.false 80771900027 524288000 111131 137614000 20192975 131072 847 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz11 qz282 111131 1000 0 1 726817 524288 1 137614 80771900027 524288000 111131 137614000 qz271 qz562 rfl) rfl) (Enclosure.sfrac_false_div 20192975 131072) (BSN.sin_reduce2 qz561 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2307027308234114334720) qz563) 226375608064910080 72057594037927936 Bool.false 127747 1048576 24 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q2 20192975 131072 226375608064910080 72057594037927936 24 2307027308234114334720 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 127747 1048576 2307027308234114334720 18889465931478580854784 262278639 2147483648 275497 275228 (ep122 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz564 := (@Enclosure.Real.IsNear.recentre' qz280 Bool.false 524287 1048576 1 1048576 524287 1048576 1 1048576 (ep112 rfl rfl) rfl)

noncomputable def ep124 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz280 (Real.cos qz281)) (@HMul.hMul Real Real Real qz0 qz280 (@Neg.neg Real Real.instNeg (Real.sin qz281))) Bool.true 545659559555 1099511627776 30901747524651 75654096572383232 Bool.false 66976091389 1099511627776 30838925495125 75654096572383232 (@Enclosure.Real.IsNear.mulLit_ft qz280 (Real.cos qz281) 524287 1048576 1 1048576 1040765 1048576 58803817 72149368832 545659559555 1099511627776 30901747524651 75654096572383232 qz564 (@Enclosure.Real.IsNear.recentre' (Real.cos qz281) Bool.true 1040765 1048576 117607634 144298737664 1040765 1048576 58803817 72149368832 (ep121 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz280 (@Neg.neg Real Real.instNeg (Real.sin qz281)) 524287 1048576 1 1048576 127747 1048576 58803817 72149368832 66976091389 1099511627776 30838925495125 75654096572383232 qz564 (@Enclosure.Real.IsNear.neg (Real.sin qz281) Bool.true 127747 1048576 58803817 72149368832 (@Enclosure.Real.IsNear.recentre' (Real.sin qz281) Bool.true 127747 1048576 117607634 144298737664 127747 1048576 58803817 72149368832 (ep123 rfl rfl) rfl)) rfl)

noncomputable def ep125 := @ep78 545659559555 1099511627776 30901747524651 75654096572383232 Bool.false 66976091389 1099511627776 30838925495125 75654096572383232 Bool.true 19219710819287712137216 69920900639 1099511627776 110222711333727 75654096572383232 Bool.true 1072020672715722562994176 487498561013 549755813888 6887013947403 4728381035773952 (ep79 (BSN.head_sum_c_succ qz14 3 4 rfl rfl) (ep110 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep111 ep124) rfl rfl

noncomputable abbrev qz565 := (@Nat.cast Real Real.instNatCast 5)

noncomputable abbrev qz283 := (@Inv.inv Real Real.instInv (Real.sqrt qz565))

noncomputable abbrev qz284 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 5 1)))

noncomputable def ep126 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz18 qz17) (Complex.mk (@HMul.hMul Real Real Real qz0 qz283 (Real.cos qz284)) (@HMul.hMul Real Real Real qz0 qz283 (@Neg.neg Real Real.instNeg (Real.sin qz284)))) Bool.true 480650577323 1099511627776 27678136283365 75654096572383232 Bool.true 25931747163 274877906944 6905707596621 18913524143095808 (BSN.cpow_neg_s_mk qz11 111131 1000 5 (@Eq.refl Real qz11) rfl)

noncomputable def ep127 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz565) 2344687 1048576 1 1048576 234468 234469 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz565) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz565 qz267)) Bool.false 2344687 1048576 1 1048576 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz565 qz267)) Bool.false 2344687 1048576 1 1048576 2344687 1048576 1 1048576 (BSN.sqrt_enclosure 5 1 1172343 1172344 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep128 := nat_lit 11734546589655452485523914939250625

noncomputable def ep129 := nat_lit 2429970938528035899633153341031900

noncomputable def ep130 := nat_lit 824199001261152424427520000

noncomputable def ep131 := BSN.log_dyadic_bound 2 3 17 16 ep128 524288 137614 ep129 ep130 843808 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base16 (BSN.artanhP 2) (BSN.artanhQ 3) 0 16 ep129 ep128 ep130 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep132 := nat_lit 4660458366214177121882312546371883467567736775458058167011498635875994581641345

noncomputable def ep133 := nat_lit 5239353935325427915156407794641989501428097284785832932690943281965029435521

noncomputable def ep134 := nat_lit 12197479624189460816876755818354083955865569873452880041234330138171090047117441

noncomputable def ep135 := BSN.sin_dyadic_bound_f 2916820591 2147483648 3 2 1048576 275497 ep132 ep97 ep133 ep134 ep100 ep133 1024979 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2916820591) qz268 0 2 ep132 ep97 ep133 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2916820591) qz269 0 2 ep134 ep100 ep133 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz285 := (Real.log (Enclosure.sfrac Bool.false 5 1))

noncomputable abbrev qz566 := (BSN.isNear_log_sfrac 5 1 843808 524288 1 137614 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 843808 524288 137614 rfl rfl rfl (ep131 rfl)))

noncomputable abbrev qz822 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 187546453) qz277)

noncomputable def ep136 := @Enclosure.Real.IsNear.cos_image qz284 qz822 Bool.false 187546453 1048576 53 65536 Bool.true 1024979 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz284 Bool.false 2930413339 16384000 111131 137614000 187546453 1048576 53 65536 (@Enclosure.Real.IsNear.mulLit_ff qz11 qz285 111131 1000 0 1 843808 524288 1 137614 2930413339 16384000 111131 137614000 qz271 qz566 rfl) rfl) (Enclosure.sfrac_false_div 187546453 1048576) (BSN.cos_reduce1 qz822 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 205253001998023551614976) qz279) 226375608064910080 72057594037927936 Bool.false 1024979 1048576 28 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q1 187546453 1048576 226375608064910080 72057594037927936 28 205253001998023551614976 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1024979 1048576 205253001998023551614976 151115727451828646838272 2916820591 2147483648 275497 275228 (ep135 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep137 := nat_lit 2591472138534687480119132040337553921760488474047714907420917439167537002883201

noncomputable def ep138 := nat_lit 7763937707733411584527083305423377786278609227573573056397370430938680949778561

noncomputable def ep139 := BSN.cos_dyadic_bound_f 2916820591 2147483648 3 2 1048576 275497 ep137 ep104 ep133 ep138 ep106 ep133 221196 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2916820591) qz272 0 2 ep137 ep104 ep133 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2916820591) qz273 0 2 ep138 ep106 ep133 rfl rfl rfl rfl) rfl rfl

noncomputable def ep140 := @Enclosure.Real.IsNear.sin_image qz284 qz822 Bool.false 187546453 1048576 53 65536 Bool.false 221196 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz284 Bool.false 2930413339 16384000 111131 137614000 187546453 1048576 53 65536 (@Enclosure.Real.IsNear.mulLit_ff qz11 qz285 111131 1000 0 1 843808 524288 1 137614 2930413339 16384000 111131 137614000 qz271 qz566 rfl) rfl) (Enclosure.sfrac_false_div 187546453 1048576) (BSN.sin_reduce1 qz822 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 205253001998023551614976) qz279) 226375608064910080 72057594037927936 Bool.false 221196 1048576 28 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q1 187546453 1048576 226375608064910080 72057594037927936 28 205253001998023551614976 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 221196 1048576 205253001998023551614976 151115727451828646838272 2916820591 2147483648 275497 275228 (ep139 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz567 := (@Enclosure.Real.IsNear.recentre' qz283 Bool.false 468937 1048576 1 1048576 468937 1048576 1 1048576 (ep127 rfl rfl) rfl)

noncomputable def ep141 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz283 (Real.cos qz284)) (@HMul.hMul Real Real Real qz0 qz283 (@Neg.neg Real Real.instNeg (Real.sin qz284))) Bool.true 480650577323 1099511627776 27678136283365 75654096572383232 Bool.true 25931747163 274877906944 6905707596621 18913524143095808 (@Enclosure.Real.IsNear.mulLit_ft qz283 (Real.cos qz284) 468937 1048576 1 1048576 1024979 1048576 3679539 4509335552 480650577323 1099511627776 27678136283365 75654096572383232 qz567 (@Enclosure.Real.IsNear.recentre' (Real.cos qz284) Bool.true 1024979 1048576 7359078 9018671104 1024979 1048576 3679539 4509335552 (ep136 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz283 (@Neg.neg Real Real.instNeg (Real.sin qz284)) 468937 1048576 1 1048576 55299 262144 3679539 4509335552 25931747163 274877906944 6905707596621 18913524143095808 qz567 (@Enclosure.Real.IsNear.neg (Real.sin qz284) Bool.false 55299 262144 3679539 4509335552 (@Enclosure.Real.IsNear.recentre' (Real.sin qz284) Bool.false 221196 1048576 7359078 9018671104 55299 262144 3679539 4509335552 (ep140 rfl rfl) rfl)) rfl)

noncomputable def ep142 := @ep76 480650577323 1099511627776 27678136283365 75654096572383232 Bool.true 25931747163 274877906944 6905707596621 18913524143095808 Bool.true 605359741941036731072512 275285738981 549755813888 34475211904273 18913524143095808 Bool.true 148258712856598220374016 539362055339 549755813888 34453763386233 18913524143095808 (ep77 (BSN.head_sum_c_succ qz14 4 5 rfl rfl) (ep125 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep126 ep141) rfl rfl

noncomputable abbrev qz823 := (@Nat.cast Real Real.instNatCast 6)

noncomputable abbrev qz286 := (@Inv.inv Real Real.instInv (Real.sqrt qz823))

noncomputable abbrev qz287 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 6 1)))

noncomputable def ep143 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz819 qz17) (Complex.mk (@HMul.hMul Real Real Real qz0 qz286 (Real.cos qz287)) (@HMul.hMul Real Real Real qz0 qz286 (@Neg.neg Real Real.instNeg (Real.sin qz287)))) Bool.true 81414204615 549755813888 12614182500255 37827048286191616 Bool.false 209149553583 549755813888 12634713958599 37827048286191616 (BSN.cpow_neg_s_mk qz11 111131 1000 6 (@Eq.refl Real qz11) rfl)

noncomputable abbrev qz824 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6) qz267)

noncomputable def ep144 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz823) 2568477 1048576 1 1048576 214039 214040 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz823) (Real.sqrt qz824) Bool.false 2568477 1048576 1 1048576 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz824) Bool.false 2568477 1048576 1 1048576 2568477 1048576 1 1048576 (BSN.sqrt_enclosure 6 1 1284238 1284239 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep145 := BSN.log_dyadic_bound 2 10 4 3 105000000 524288 137614 1434560 960 212580 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 2) (BSN.artanhQ 10) 0 3 1434560 105000000 960 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz288 := (Real.log (Enclosure.sfrac Bool.false 6 1))

noncomputable def ep146 := @Enclosure.Real.IsNear.mulLit_ff qz11 qz288 111131 1000 0 1 4034681531866359 2251799813685248 250000000068807 34403500000000000000 448378193317840342029 2251799813685248000 27782750007646590717 34403500000000000000000 qz271 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 250000000068807 34403500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz824) Bool.false 33845361775666394038272 18889465931478580854784 1000000000275228 137614000000000000000 4034681531866359 2251799813685248 250000000068807 34403500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 212580 524288 24973259072661432 36028797018963968 137614 1000000000000000 rfl rfl rfl rfl (ep145 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep147 := nat_lit 1575431983185295076197479037873063889395364807763844389657757441041676025390625

noncomputable def ep148 := nat_lit 1939420139293655872948452881951842167445975600479535320930540561676025390625

noncomputable def ep149 := nat_lit 4722417109277297916846540207855287983851202472090574098331411242001676025390625

noncomputable def ep150 := BSN.cos_dyadic_bound_f 2576077875 2147483648 3 2 1048576 275497 ep147 ep104 ep148 ep149 ep106 ep148 380370 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2576077875) qz272 0 2 ep147 ep104 ep148 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2576077875) qz273 0 2 ep149 ep106 ep148 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz289 := (@Nat.cast Real Real.instNatCast 524288)

noncomputable abbrev qz290 := (@Nat.cast Real Real.instNatCast 75557863725914323419136)

noncomputable abbrev qz825 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 104396183) qz289)

noncomputable def ep151 := @Enclosure.Real.IsNear.cos_image qz287 qz825 Bool.false 104396183 524288 53 65536 Bool.true 380370 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz287 Bool.false 448378193317840342029 2251799813685248000 27782750007646590717 34403500000000000000000 104396183 524288 53 65536 (ep146 rfl) rfl) (Enclosure.sfrac_false_div 104396183 524288) (BSN.cos_reduce2 qz825 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 90637682503384916033536) qz290) 226375608064910080 72057594037927936 Bool.false 380370 1048576 31 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q2 104396183 524288 226375608064910080 72057594037927936 31 90637682503384916033536 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 380370 1048576 90637682503384916033536 75557863725914323419136 2576077875 2147483648 275497 275228 (ep150 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep152 := nat_lit 2834226033622096212457103505865953527177699873494536273127218961425676025390625

noncomputable def ep153 := nat_lit 7419832931641871780260021210697194350527634755799199562908828785681676025390625

noncomputable def ep154 := BSN.sin_dyadic_bound_f 2576077875 2147483648 3 2 1048576 275497 ep152 ep97 ep148 ep153 ep100 ep148 977154 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2576077875) qz268 0 2 ep152 ep97 ep148 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2576077875) qz269 0 2 ep153 ep100 ep148 rfl rfl rfl rfl) rfl rfl

noncomputable def ep155 := @Enclosure.Real.IsNear.sin_image qz287 qz825 Bool.false 104396183 524288 53 65536 Bool.true 977154 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz287 Bool.false 448378193317840342029 2251799813685248000 27782750007646590717 34403500000000000000000 104396183 524288 53 65536 (ep146 rfl) rfl) (Enclosure.sfrac_false_div 104396183 524288) (BSN.sin_reduce2 qz825 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 90637682503384916033536) qz290) 226375608064910080 72057594037927936 Bool.false 977154 1048576 31 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q2 104396183 524288 226375608064910080 72057594037927936 31 90637682503384916033536 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 977154 1048576 90637682503384916033536 75557863725914323419136 2576077875 2147483648 275497 275228 (ep154 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz568 := (@Enclosure.Real.IsNear.recentre' qz286 Bool.false 428079 1048576 1 1048576 428079 1048576 1 1048576 (ep144 rfl rfl) rfl)

noncomputable def ep156 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz286 (Real.cos qz287)) (@HMul.hMul Real Real Real qz0 qz286 (@Neg.neg Real Real.instNeg (Real.sin qz287))) Bool.true 81414204615 549755813888 12614182500255 37827048286191616 Bool.false 209149553583 549755813888 12634713958599 37827048286191616 (@Enclosure.Real.IsNear.mulLit_ft qz286 (Real.cos qz287) 428079 1048576 1 1048576 190185 524288 3679539 4509335552 81414204615 549755813888 12614182500255 37827048286191616 qz568 (@Enclosure.Real.IsNear.recentre' (Real.cos qz287) Bool.true 380370 1048576 7359078 9018671104 190185 524288 3679539 4509335552 (ep151 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz286 (@Neg.neg Real Real.instNeg (Real.sin qz287)) 428079 1048576 1 1048576 488577 524288 3679539 4509335552 209149553583 549755813888 12634713958599 37827048286191616 qz568 (@Enclosure.Real.IsNear.neg (Real.sin qz287) Bool.true 488577 524288 3679539 4509335552 (@Enclosure.Real.IsNear.recentre' (Real.sin qz287) Bool.true 977154 1048576 7359078 9018671104 488577 524288 3679539 4509335552 (ep155 rfl rfl) rfl)) rfl)

noncomputable def ep157 := @ep74 81414204615 549755813888 12614182500255 37827048286191616 Bool.false 209149553583 549755813888 12634713958599 37827048286191616 Bool.true 196097867805422673461248 89174985899 137438953472 81564606308801 37827048286191616 Bool.true 181536242658862409187328 82553125439 137438953472 81542240731065 37827048286191616 (ep75 (BSN.head_sum_c_succ qz14 5 6 rfl rfl) (ep142 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep143 ep156) rfl rfl

noncomputable abbrev qz826 := (@Nat.cast Real Real.instNatCast 7)

noncomputable abbrev qz291 := (@Inv.inv Real Real.instInv (Real.sqrt qz826))

noncomputable abbrev qz292 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 7 1)))

noncomputable def ep158 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz818 qz17) (Complex.mk (@HMul.hMul Real Real Real qz0 qz291 (Real.cos qz292)) (@HMul.hMul Real Real Real qz0 qz291 (@Neg.neg Real Real.instNeg (Real.sin qz292)))) Bool.true 180412292225 549755813888 11697697630603 37827048286191616 Bool.true 206178173125 1099511627776 23368546700999 75654096572383232 (BSN.cpow_neg_s_mk qz11 111131 1000 7 (@Eq.refl Real qz11) rfl)

noncomputable abbrev qz827 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 7) qz267)

noncomputable def ep159 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz826) 2774271 1048576 1 1048576 198162 198163 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz826) (Real.sqrt qz827) Bool.false 2774271 1048576 1 1048576 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz827) Bool.false 2774271 1048576 1 1048576 2774271 1048576 1 1048576 (BSN.sqrt_enclosure 7 1 1387135 1387136 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep160 := BSN.log_dyadic_bound 3 11 5 4 202569142545 524288 137614 5259111624 688905 293399 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 3) (BSN.artanhQ 11) 0 4 5259111624 202569142545 688905 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz293 := (Real.log (Enclosure.sfrac Bool.false 7 1))

noncomputable def ep161 := @Enclosure.Real.IsNear.mulLit_ff qz11 qz293 111131 1000 0 1 4381796493761783 2251799813685248 250000000068807 34403500000000000000 486953426148240706573 2251799813685248000 27782750007646590717 34403500000000000000000 qz271 (BSN.isNear_log_sfrac 7 1 4381796493761783 2251799813685248 250000000068807 34403500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz827) Bool.false 36757173121942042968064 18889465931478580854784 1000000000275228 137614000000000000000 4381796493761783 2251799813685248 250000000068807 34403500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 293399 524288 24973259072661432 36028797018963968 137614 1000000000000000 rfl rfl rfl rfl (ep160 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep162 := nat_lit 1673810890620175519722060708061001602679467472760536081262583318432967624294400

noncomputable def ep163 := nat_lit 676797894783352222474891671988886617690172101103114924884107611800202182656

noncomputable def ep164 := nat_lit 4382694659794619981388056791738450762017583102399618026761715374048191069618176

noncomputable def ep165 := BSN.sin_dyadic_bound_f 2258433852 2147483648 3 2 1048576 275497 ep162 ep97 ep163 ep164 ep100 ep163 910426 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2258433852) qz268 0 2 ep162 ep97 ep163 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2258433852) qz269 0 2 ep164 ep100 ep163 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz828 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 226755359) qz277)

noncomputable def ep166 := @Enclosure.Real.IsNear.cos_image qz292 qz828 Bool.false 226755359 1048576 53 65536 Bool.true 910426 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz292 Bool.false 486953426148240706573 2251799813685248000 27782750007646590717 34403500000000000000000 226755359 1048576 53 65536 (ep161 rfl) rfl) (Enclosure.sfrac_false_div 226755359 1048576) (BSN.cos_reduce1 qz828 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 158923153982069657305088) qz279) 226375608064910080 72057594037927936 Bool.false 910426 1048576 34 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q1 226755359 1048576 226375608064910080 72057594037927936 34 158923153982069657305088 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 910426 1048576 158923153982069657305088 151115727451828646838272 2258433852 2147483648 275497 275228 (ep165 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep167 := nat_lit 930195738297779000833355900776995951096455339134121429556939224734670992244736

noncomputable def ep168 := nat_lit 2789233619103770298055117918987010080053985673200158058821049458980412572368896

noncomputable def ep169 := BSN.cos_dyadic_bound_f 2258433852 2147483648 3 2 1048576 275497 ep167 ep104 ep163 ep168 ep106 ep163 520225 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2258433852) qz272 0 2 ep167 ep104 ep163 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2258433852) qz273 0 2 ep168 ep106 ep163 rfl rfl rfl rfl) rfl rfl

noncomputable def ep170 := @Enclosure.Real.IsNear.sin_image qz292 qz828 Bool.false 226755359 1048576 53 65536 Bool.false 520225 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz292 Bool.false 486953426148240706573 2251799813685248000 27782750007646590717 34403500000000000000000 226755359 1048576 53 65536 (ep161 rfl) rfl) (Enclosure.sfrac_false_div 226755359 1048576) (BSN.sin_reduce1 qz828 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 158923153982069657305088) qz279) 226375608064910080 72057594037927936 Bool.false 520225 1048576 34 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q1 226755359 1048576 226375608064910080 72057594037927936 34 158923153982069657305088 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 520225 1048576 158923153982069657305088 151115727451828646838272 2258433852 2147483648 275497 275228 (ep169 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz569 := (@Enclosure.Real.IsNear.recentre' qz291 Bool.false 396325 1048576 1 1048576 396325 1048576 1 1048576 (ep159 rfl rfl) rfl)

noncomputable def ep171 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz291 (Real.cos qz292)) (@HMul.hMul Real Real Real qz0 qz291 (@Neg.neg Real Real.instNeg (Real.sin qz292))) Bool.true 180412292225 549755813888 11697697630603 37827048286191616 Bool.true 206178173125 1099511627776 23368546700999 75654096572383232 (@Enclosure.Real.IsNear.mulLit_ft qz291 (Real.cos qz292) 396325 1048576 1 1048576 455213 524288 3679539 4509335552 180412292225 549755813888 11697697630603 37827048286191616 qz569 (@Enclosure.Real.IsNear.recentre' (Real.cos qz292) Bool.true 910426 1048576 7359078 9018671104 455213 524288 3679539 4509335552 (ep166 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz291 (@Neg.neg Real Real.instNeg (Real.sin qz292)) 396325 1048576 1 1048576 520225 1048576 3679539 4509335552 206178173125 1099511627776 23368546700999 75654096572383232 qz569 (@Enclosure.Real.IsNear.neg (Real.sin qz292) Bool.false 520225 1048576 3679539 4509335552 (@Enclosure.Real.IsNear.recentre' (Real.sin qz292) Bool.false 520225 1048576 7359078 9018671104 520225 1048576 3679539 4509335552 (ep170 rfl rfl) rfl)) rfl)

noncomputable def ep172 := @ep72 180412292225 549755813888 11697697630603 37827048286191616 Bool.true 206178173125 1099511627776 23368546700999 75654096572383232 Bool.true 73820143588244310720512 537112235821 549755813888 23315575984851 9456762071547904 Bool.true 119105033672500040433664 866603176637 1099511627776 186453028163129 75654096572383232 (ep73 (BSN.head_sum_c_succ qz14 6 7 rfl rfl) (ep157 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep158 ep171) rfl rfl

noncomputable abbrev qz829 := (@Nat.cast Real Real.instNatCast 8)

noncomputable abbrev qz294 := (@Inv.inv Real Real.instInv (Real.sqrt qz829))

noncomputable abbrev qz295 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 8 1)))

noncomputable def ep173 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz817 qz17) (Complex.mk (@HMul.hMul Real Real Real qz0 qz294 (Real.cos qz295)) (@HMul.hMul Real Real Real qz0 qz294 (@Neg.neg Real Real.instNeg (Real.sin qz295)))) Bool.false 70878924403 1099511627776 21813376610299 75654096572383232 Bool.false 191109397773 549755813888 10935580674081 37827048286191616 (BSN.cpow_neg_s_mk qz11 111131 1000 8 (@Eq.refl Real qz11) rfl)

noncomputable abbrev qz830 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8) qz267)

noncomputable def ep174 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz829) 2965821 1048576 1 1048576 185363 185364 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz829) (Real.sqrt qz830) Bool.false 2965821 1048576 1 1048576 (BSN.sqrt_natCast_div_one 8) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz830) Bool.false 2965821 1048576 1 1048576 2965821 1048576 1 1048576 (BSN.sqrt_enclosure 8 1 1482910 1482911 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep175 := BSN.log_dyadic_bound 0 16 1 0 1 524288 137614 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz296 := (Real.log (Enclosure.sfrac Bool.false 8 1))

noncomputable def ep176 := @Enclosure.Real.IsNear.mulLit_ff qz11 qz296 111131 1000 0 1 9364972152248037 4503599627370496 500000000206421 68807000000000000000 1040738720251476599847 4503599627370496000 55565500022939772151 68807000000000000000000 qz271 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 500000000206421 68807000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz830) Bool.false 39279540158062550581248 18889465931478580854784 1000000000412842 137614000000000000000 9364972152248037 4503599627370496 500000000206421 68807000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 524288 24973259072661432 36028797018963968 137614 1000000000000000 rfl rfl rfl rfl (ep175 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep177 := nat_lit 24039046381703152571138610046818576

noncomputable def ep178 := nat_lit 2552117751907038475975309555738261585920

noncomputable def ep179 := nat_lit 17864824263349269331827166890167831101440

noncomputable def ep180 := BSN.sin_dyadic_bound_f 393757926 2147483648 2 1 1048576 275497 ep177 ep178 ep177 ep177 ep179 ep177 191189 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 393757926) qz268 0 1 ep177 ep178 ep177 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 393757926) qz269 0 1 ep177 ep179 ep177 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz831 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 121157933) qz289)

noncomputable def ep181 := @Enclosure.Real.IsNear.cos_image qz295 qz831 Bool.false 121157933 524288 847 1048576 Bool.false 191189 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz295 Bool.false 1040738720251476599847 4503599627370496000 55565500022939772151 68807000000000000000000 121157933 524288 847 1048576 (ep176 rfl) rfl) (Enclosure.sfrac_false_div 121157933 524288) (BSN.cos_reduce3 qz831 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13854125410014982045696) qz290) 226375608064910080 72057594037927936 Bool.false 191189 1048576 36 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q3 121157933 524288 226375608064910080 72057594037927936 36 13854125410014982045696 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 191189 1048576 13854125410014982045696 75557863725914323419136 393757926 2147483648 275497 275228 (ep180 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep182 := BSN.cos_dyadic_bound_f 393757926 2147483648 2 1 1048576 275497 ep177 ep118 ep177 ep177 ep119 ep177 1030998 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 393757926) qz272 0 1 ep177 ep118 ep177 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 393757926) qz273 0 1 ep177 ep119 ep177 rfl rfl rfl rfl) rfl rfl

noncomputable def ep183 := @Enclosure.Real.IsNear.sin_image qz295 qz831 Bool.false 121157933 524288 847 1048576 Bool.true 1030998 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz295 Bool.false 1040738720251476599847 4503599627370496000 55565500022939772151 68807000000000000000000 121157933 524288 847 1048576 (ep176 rfl) rfl) (Enclosure.sfrac_false_div 121157933 524288) (BSN.sin_reduce3 qz831 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13854125410014982045696) qz290) 226375608064910080 72057594037927936 Bool.false 1030998 1048576 36 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q3 121157933 524288 226375608064910080 72057594037927936 36 13854125410014982045696 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1030998 1048576 13854125410014982045696 75557863725914323419136 393757926 2147483648 275497 275228 (ep182 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz570 := (@Enclosure.Real.IsNear.recentre' qz294 Bool.false 370727 1048576 1 1048576 370727 1048576 1 1048576 (ep174 rfl rfl) rfl)

noncomputable def ep184 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz294 (Real.cos qz295)) (@HMul.hMul Real Real Real qz0 qz294 (@Neg.neg Real Real.instNeg (Real.sin qz295))) Bool.false 70878924403 1099511627776 21813376610299 75654096572383232 Bool.false 191109397773 549755813888 10935580674081 37827048286191616 (@Enclosure.Real.IsNear.mulLit_ff qz294 (Real.cos qz295) 370727 1048576 1 1048576 191189 1048576 58803817 72149368832 70878924403 1099511627776 21813376610299 75654096572383232 qz570 (@Enclosure.Real.IsNear.recentre' (Real.cos qz295) Bool.false 191189 1048576 117607634 144298737664 191189 1048576 58803817 72149368832 (ep181 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz294 (@Neg.neg Real Real.instNeg (Real.sin qz295)) 370727 1048576 1 1048576 515499 524288 58803817 72149368832 191109397773 549755813888 10935580674081 37827048286191616 qz570 (@Enclosure.Real.IsNear.neg (Real.sin qz295) Bool.true 515499 524288 58803817 72149368832 (@Enclosure.Real.IsNear.recentre' (Real.sin qz295) Bool.true 1030998 1048576 117607634 144298737664 515499 524288 58803817 72149368832 (ep183 rfl rfl) rfl)) rfl)

noncomputable def ep185 := @ep70 70878924403 1099511627776 21813376610299 75654096572383232 Bool.false 191109397773 549755813888 10935580674081 37827048286191616 Bool.true 551595047933277196255232 1003345547239 1099511627776 208337984489107 75654096572383232 Bool.true 266293129661317862391808 484384381091 1099511627776 208324189511291 75654096572383232 (ep71 (BSN.head_sum_c_succ qz14 7 8 rfl rfl) (ep172 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep173 ep184) rfl rfl

theorem EMRow35.d7 : Enclosure.Complex.IsNear (BSN.headSumC qz14 9) Bool.true 1003345547239 1099511627776 208337984489107 75654096572383232 Bool.true 484384381091 1099511627776 208324189511291 75654096572383232 := ep69 (BSN.head_sum_c_succ qz14 8 9 rfl rfl) (ep185 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz832 := (@HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast 16) qz17)

noncomputable def ep186 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 17) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz14 16) qz832) Bool.true 637325009493 1099511627776 350214009969399 75654096572383232 Bool.false 200972922577 1099511627776 350170244451365 75654096572383232

noncomputable def ep187 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz14 16) qz832 Bool.true 452013993489 549755813888 167355450462889 37827048286191616 Bool.false 267506388835 1099511627776 334719675676067 75654096572383232 Bool.false

noncomputable abbrev qz833 := (@HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast 15) qz17)

noncomputable def ep188 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 16) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz14 15) qz833) Bool.true 452013993489 549755813888 167355450462889 37827048286191616 Bool.false 267506388835 1099511627776 334719675676067 75654096572383232

noncomputable def ep189 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz14 15) qz833 Bool.true 282731161989 274877906944 79678486175491 18913524143095808 Bool.false 96881620261 1099511627776 318737020574361 75654096572383232 Bool.false

noncomputable abbrev qz834 := (@HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast 14) qz17)

noncomputable def ep190 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 15) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz14 14) qz834) Bool.true 282731161989 274877906944 79678486175491 18913524143095808 Bool.false 96881620261 1099511627776 318737020574361 75654096572383232

noncomputable def ep191 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz14 14) qz834 Bool.true 7820247363 8589934592 37772917888625 9456762071547904 Bool.true 166687481725 1099511627776 302173607812991 75654096572383232 Bool.true

noncomputable abbrev qz835 := (@HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast 13) qz17)

noncomputable def ep192 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 14) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz14 13) qz835) Bool.true 7820247363 8589934592 37772917888625 9456762071547904 Bool.true 166687481725 1099511627776 302173607812991 75654096572383232

noncomputable def ep193 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz14 13) qz835 Bool.true 797390260863 1099511627776 285013600220615 75654096572383232 Bool.false 30169274617 549755813888 17812395174749 4728381035773952 Bool.true

noncomputable abbrev qz836 := (@HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast 12) qz17)

noncomputable def ep194 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 13) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz14 12) qz836) Bool.true 797390260863 1099511627776 285013600220615 75654096572383232 Bool.false 30169274617 549755813888 17812395174749 4728381035773952

noncomputable def ep195 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz14 12) qz836 Bool.true 549826142637 549755813888 33393136787251 9456762071547904 Bool.true 36516317947 1099511627776 267176508615507 75654096572383232 Bool.false

noncomputable abbrev qz837 := (@HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast 11) qz17)

noncomputable def ep196 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 12) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz14 11) qz837) Bool.true 549826142637 549755813888 33393136787251 9456762071547904 Bool.true 36516317947 1099511627776 267176508615507 75654096572383232

noncomputable def ep197 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz14 11) qz837 Bool.true 204473449797 274877906944 124235361289315 37827048286191616 Bool.false 8635401971 68719476736 124262720191041 37827048286191616 Bool.true

noncomputable abbrev qz838 := (@HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast 10) qz17)

noncomputable def ep198 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 11) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz14 10) qz838) Bool.true 204473449797 274877906944 124235361289315 37827048286191616 Bool.false 8635401971 68719476736 124262720191041 37827048286191616

noncomputable def ep199 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz14 10) qz838 Bool.true 382740426157 549755813888 28617284142401 9456762071547904 Bool.true 205556404741 1099511627776 228932542135371 75654096572383232 Bool.true

noncomputable abbrev qz839 := (@Nat.cast Complex Complex.instNatCast 9)

noncomputable def ep200 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 10) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz14 9) (@HPow.hPow Complex Complex Complex qz16 qz839 qz17)) Bool.true 382740426157 549755813888 28617284142401 9456762071547904 Bool.true 205556404741 1099511627776 228932542135371 75654096572383232

noncomputable def ep201 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz14 9) (@HPow.hPow Complex Complex Complex qz16 qz839 qz17) Bool.true 1003345547239 1099511627776 208337984489107 75654096572383232 Bool.true 484384381091 1099511627776 208324189511291 75654096572383232 Bool.false

noncomputable abbrev qz840 := (@Nat.cast Real Real.instNatCast 9)

noncomputable abbrev qz297 := (@Inv.inv Real Real.instInv (Real.sqrt qz840))

noncomputable abbrev qz298 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 9 1)))

noncomputable def ep202 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz839 qz17) (Complex.mk (@HMul.hMul Real Real Real qz0 qz297 (Real.cos qz298)) (@HMul.hMul Real Real Real qz0 qz297 (@Neg.neg Real Real.instNeg (Real.sin qz298)))) Bool.false 237864694925 1099511627776 20600288650101 75654096572383232 Bool.false 139413988175 549755813888 1288022039005 4728381035773952 (BSN.cpow_neg_s_mk qz11 111131 1000 9 (@Eq.refl Real qz11) rfl)

noncomputable abbrev qz841 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9) qz267)

noncomputable def ep203 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz840) 3145729 1048576 1 1048576 174762 174763 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz840) (Real.sqrt qz841) Bool.false 3145729 1048576 1 1048576 (BSN.sqrt_natCast_div_one 9) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz841) Bool.false 3145729 1048576 1 1048576 3145729 1048576 1 1048576 (BSN.sqrt_enclosure 9 1 1572864 1572865 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep204 := BSN.log_dyadic_bound 1 17 2 1 867 524288 137614 1 1 61752 18 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1) (BSN.artanhQ 17) 0 1 1 867 1 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz299 := (Real.log (Enclosure.sfrac Bool.false 9 1))

noncomputable def ep205 := @Enclosure.Real.IsNear.mulLit_ff qz11 qz299 111131 1000 0 1 9895417793173221 4503599627370496 500000000206421 68807000000000000000 1099687674773133222951 4503599627370496000 55565500022939772151 68807000000000000000000 qz271 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 500000000206421 68807000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz841) Bool.false 41504390431577613533184 18889465931478580854784 1000000000412842 137614000000000000000 9895417793173221 4503599627370496 500000000206421 68807000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 61752 524288 24973259072661432 36028797018963968 137614 1000000000000000 rfl rfl rfl rfl (ep204 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep206 := nat_lit 5292223431275151865379245355895868081

noncomputable def ep207 := BSN.sin_dyadic_bound_f 1516734421 2147483648 2 1 1048576 275497 ep206 ep178 ep206 ep206 ep179 ep206 680537 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1516734421) qz268 0 1 ep206 ep178 ep206 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1516734421) qz269 0 1 ep206 ep179 ep206 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz842 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 256040989) qz277)

noncomputable def ep208 := @Enclosure.Real.IsNear.cos_image qz298 qz842 Bool.false 256040989 1048576 847 1048576 Bool.false 680537 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz298 Bool.false 1099687674773133222951 4503599627370496000 55565500022939772151 68807000000000000000000 256040989 1048576 847 1048576 (ep205 rfl) rfl) (Enclosure.sfrac_false_div 256040989 1048576) (BSN.cos_reduce3 qz842 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 106730696511115921195008) qz279) 226375608064910080 72057594037927936 Bool.false 680537 1048576 38 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q3 256040989 1048576 226375608064910080 72057594037927936 38 106730696511115921195008 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 680537 1048576 106730696511115921195008 151115727451828646838272 1516734421 2147483648 275497 275228 (ep207 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep209 := nat_lit 189117290753066252572775964303104523916338964884895173879386719463086892895841

noncomputable def ep210 := nat_lit 28007628846537742059162508496161772467784912558530825772626607128554622561

noncomputable def ep211 := nat_lit 567295857001505682234209567892321248204081324829568459986614905175003569442401

noncomputable def ep212 := BSN.cos_dyadic_bound_f 1516734421 2147483648 3 2 1048576 275497 ep209 ep104 ep210 ep211 ep106 ep210 797734 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1516734421) qz272 0 2 ep209 ep104 ep210 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1516734421) qz273 0 2 ep211 ep106 ep210 rfl rfl rfl rfl) rfl rfl

noncomputable def ep213 := @Enclosure.Real.IsNear.sin_image qz298 qz842 Bool.false 256040989 1048576 847 1048576 Bool.true 797734 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz298 Bool.false 1099687674773133222951 4503599627370496000 55565500022939772151 68807000000000000000000 256040989 1048576 847 1048576 (ep205 rfl) rfl) (Enclosure.sfrac_false_div 256040989 1048576) (BSN.sin_reduce3 qz842 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 106730696511115921195008) qz279) 226375608064910080 72057594037927936 Bool.false 797734 1048576 38 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q3 256040989 1048576 226375608064910080 72057594037927936 38 106730696511115921195008 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 797734 1048576 106730696511115921195008 151115727451828646838272 1516734421 2147483648 275497 275228 (ep212 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz571 := (@Enclosure.Real.IsNear.recentre' qz297 Bool.false 349525 1048576 1 1048576 349525 1048576 1 1048576 (ep203 rfl rfl) rfl)

noncomputable def ep214 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz297 (Real.cos qz298)) (@HMul.hMul Real Real Real qz0 qz297 (@Neg.neg Real Real.instNeg (Real.sin qz298))) Bool.false 237864694925 1099511627776 20600288650101 75654096572383232 Bool.false 139413988175 549755813888 1288022039005 4728381035773952 (@Enclosure.Real.IsNear.mulLit_ff qz297 (Real.cos qz298) 349525 1048576 1 1048576 680537 1048576 58803817 72149368832 237864694925 1099511627776 20600288650101 75654096572383232 qz571 (@Enclosure.Real.IsNear.recentre' (Real.cos qz298) Bool.false 680537 1048576 117607634 144298737664 680537 1048576 58803817 72149368832 (ep208 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz297 (@Neg.neg Real Real.instNeg (Real.sin qz298)) 349525 1048576 1 1048576 398867 524288 58803817 72149368832 139413988175 549755813888 1288022039005 4728381035773952 qz571 (@Enclosure.Real.IsNear.neg (Real.sin qz298) Bool.true 398867 524288 58803817 72149368832 (@Enclosure.Real.IsNear.recentre' (Real.sin qz298) Bool.true 797734 1048576 117607634 144298737664 398867 524288 58803817 72149368832 (ep213 rfl rfl) rfl)) rfl)

noncomputable def ep215 := @ep201 237864694925 1099511627776 20600288650101 75654096572383232 Bool.false 139413988175 549755813888 1288022039005 4728381035773952 Bool.true 841655097959125996273664 382740426157 549755813888 28617284142401 9456762071547904 Bool.true 113005828588279596843008 205556404741 1099511627776 228932542135371 75654096572383232 EMRow35.d7 (ep202 ep214) rfl rfl

noncomputable abbrev qz843 := (@Nat.cast Real Real.instNatCast 10)

noncomputable abbrev qz300 := (@Inv.inv Real Real.instInv (Real.sqrt qz843))

noncomputable abbrev qz301 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 10 1)))

noncomputable def ep216 := @Enclosure.Complex.IsNear.of_eq qz838 (Complex.mk (@HMul.hMul Real Real Real qz0 qz300 (Real.cos qz301)) (@HMul.hMul Real Real Real qz0 qz300 (@Neg.neg Real Real.instNeg (Real.sin qz301)))) Bool.true 26206473437 549755813888 9766224719711 37827048286191616 Bool.false 343722836277 1099511627776 19592898246711 75654096572383232 (BSN.cpow_neg_s_mk qz11 111131 1000 10 (@Eq.refl Real qz11) rfl)

noncomputable abbrev qz844 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 10) qz267)

noncomputable def ep217 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz843) 3315889 1048576 1 1048576 165794 165795 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz843) (Real.sqrt qz844) Bool.false 3315889 1048576 1 1048576 (BSN.sqrt_natCast_div_one 10) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz844) Bool.false 3315889 1048576 1 1048576 3315889 1048576 1 1048576 (BSN.sqrt_enclosure 10 1 1657944 1657945 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep218 := BSN.log_dyadic_bound 2 18 3 2 1574640 524288 137614 6528 48 116991 20 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 2) (BSN.artanhQ 18) 0 2 6528 1574640 48 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz302 := (Real.log (Enclosure.sfrac Bool.false 10 1))

noncomputable def ep219 := @Enclosure.Real.IsNear.mulLit_ff qz11 qz302 111131 1000 0 1 10369917190100709 4503599627370496 500000000206421 68807000000000000000 1152419267253081891879 4503599627370496000 55565500022939772151 68807000000000000000000 qz271 (BSN.isNear_log_sfrac 10 1 10369917190100709 4503599627370496 500000000206421 68807000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz844) Bool.false 43494585150108164161536 18889465931478580854784 1000000000412842 137614000000000000000 10369917190100709 4503599627370496 500000000206421 68807000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 116991 524288 24973259072661432 36028797018963968 137614 1000000000000000 rfl rfl rfl rfl (ep218 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep220 := nat_lit 3092485999706298257700215416995818663137349515278473958225289440857882095657216

noncomputable def ep221 := nat_lit 7455237952824153409151448505822171127500981658607027209043219600910284103936

noncomputable def ep222 := nat_lit 9262547523213246466282343353975811647157046582518207820257781883371825718763776

noncomputable def ep223 := BSN.cos_dyadic_bound_f 3048299878 2147483648 3 2 1048576 275497 ep220 ep104 ep221 ep222 ep106 ep221 158066 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3048299878) qz272 0 2 ep220 ep104 ep221 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3048299878) qz273 0 2 ep222 ep106 ep221 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz845 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 268318519) qz277)

noncomputable def ep224 := @Enclosure.Real.IsNear.cos_image qz301 qz845 Bool.false 268318519 1048576 53 65536 Bool.true 158066 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz301 Bool.false 1152419267253081891879 4503599627370496000 55565500022939772151 68807000000000000000000 268318519 1048576 53 65536 (ep219 rfl) rfl) (Enclosure.sfrac_false_div 268318519 1048576) (BSN.cos_reduce2 qz845 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 214505034352180601028608) qz279) 226375608064910080 72057594037927936 Bool.false 158066 1048576 40 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q2 268318519 1048576 226375608064910080 72057594037927936 40 214505034352180601028608 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 158066 1048576 214505034352180601028608 151115727451828646838272 3048299878 2147483648 275497 275228 (ep223 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep225 := nat_lit 5560510609109077541133066591787815856745228342174367503038286417863459544899840

noncomputable def ep226 := nat_lit 14551171686219202073638453014244377062031072640152265416285632548383777395712256

noncomputable def ep227 := BSN.sin_dyadic_bound_f 3048299878 2147483648 3 2 1048576 275497 ep225 ep97 ep221 ep226 ep100 ep221 1036593 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3048299878) qz268 0 2 ep225 ep97 ep221 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3048299878) qz269 0 2 ep226 ep100 ep221 rfl rfl rfl rfl) rfl rfl

noncomputable def ep228 := @Enclosure.Real.IsNear.sin_image qz301 qz845 Bool.false 268318519 1048576 53 65536 Bool.true 1036593 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz301 Bool.false 1152419267253081891879 4503599627370496000 55565500022939772151 68807000000000000000000 268318519 1048576 53 65536 (ep219 rfl) rfl) (Enclosure.sfrac_false_div 268318519 1048576) (BSN.sin_reduce2 qz845 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 214505034352180601028608) qz279) 226375608064910080 72057594037927936 Bool.false 1036593 1048576 40 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q2 268318519 1048576 226375608064910080 72057594037927936 40 214505034352180601028608 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1036593 1048576 214505034352180601028608 151115727451828646838272 3048299878 2147483648 275497 275228 (ep227 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz572 := (@Enclosure.Real.IsNear.recentre' qz300 Bool.false 331589 1048576 1 1048576 331589 1048576 1 1048576 (ep217 rfl rfl) rfl)

noncomputable def ep229 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz300 (Real.cos qz301)) (@HMul.hMul Real Real Real qz0 qz300 (@Neg.neg Real Real.instNeg (Real.sin qz301))) Bool.true 26206473437 549755813888 9766224719711 37827048286191616 Bool.false 343722836277 1099511627776 19592898246711 75654096572383232 (@Enclosure.Real.IsNear.mulLit_ft qz300 (Real.cos qz301) 331589 1048576 1 1048576 79033 524288 3679539 4509335552 26206473437 549755813888 9766224719711 37827048286191616 qz572 (@Enclosure.Real.IsNear.recentre' (Real.cos qz301) Bool.true 158066 1048576 7359078 9018671104 79033 524288 3679539 4509335552 (ep224 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz300 (@Neg.neg Real Real.instNeg (Real.sin qz301)) 331589 1048576 1 1048576 1036593 1048576 3679539 4509335552 343722836277 1099511627776 19592898246711 75654096572383232 qz572 (@Enclosure.Real.IsNear.neg (Real.sin qz301) Bool.true 1036593 1048576 3679539 4509335552 (@Enclosure.Real.IsNear.recentre' (Real.sin qz301) Bool.true 1036593 1048576 7359078 9018671104 1036593 1048576 3679539 4509335552 (ep228 rfl rfl) rfl)) rfl)

noncomputable def ep230 := @ep199 26206473437 549755813888 9766224719711 37827048286191616 Bool.false 343722836277 1099511627776 19592898246711 75654096572383232 Bool.true 224820935623273686761472 204473449797 274877906944 124235361289315 37827048286191616 Bool.false 151915598042148619943936 8635401971 68719476736 124262720191041 37827048286191616 (ep200 (BSN.head_sum_c_succ qz14 9 10 rfl rfl) (ep215 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep216 ep229) rfl rfl

noncomputable abbrev qz846 := (@Nat.cast Real Real.instNatCast 11)

noncomputable abbrev qz303 := (@Inv.inv Real Real.instInv (Real.sqrt qz846))

noncomputable abbrev qz304 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 11 1)))

noncomputable def ep231 := @Enclosure.Complex.IsNear.of_eq qz837 (Complex.mk (@HMul.hMul Real Real Real qz0 qz303 (Real.cos qz304)) (@HMul.hMul Real Real Real qz0 qz303 (@Neg.neg Real Real.instNeg (Real.sin qz304)))) Bool.true 140879243043 549755813888 9337185859689 37827048286191616 Bool.true 174682749483 1099511627776 18651068233425 75654096572383232 (BSN.cpow_neg_s_mk qz11 111131 1000 11 (@Eq.refl Real qz11) rfl)

noncomputable abbrev qz847 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11) qz267)

noncomputable def ep232 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz846) 3477733 1048576 1 1048576 158078 158079 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz846) (Real.sqrt qz847) Bool.false 3477733 1048576 1 1048576 (BSN.sqrt_natCast_div_one 11) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz847) Bool.false 3477733 1048576 1 1048576 3477733 1048576 1 1048576 (BSN.sqrt_enclosure 11 1 1738866 1738867 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep233 := BSN.log_dyadic_bound 3 19 4 3 4939817505 524288 137614 41676111 10935 166961 22 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 3) (BSN.artanhQ 19) 0 3 41676111 4939817505 10935 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz305 := (Real.log (Enclosure.sfrac Bool.false 11 1))

noncomputable def ep234 := @Enclosure.Real.IsNear.mulLit_ff qz11 qz305 111131 1000 0 1 10799156221662949 4503599627370496 500000000206421 68807000000000000000 1200121030069625185319 4503599627370496000 55565500022939772151 68807000000000000000000 qz271 (BSN.isNear_log_sfrac 11 1 10799156221662949 4503599627370496 500000000206421 68807000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz847) Bool.false 45294944137145793642496 18889465931478580854784 1000000000412842 137614000000000000000 10799156221662949 4503599627370496 500000000206421 68807000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 166961 524288 24973259072661432 36028797018963968 137614 1000000000000000 rfl rfl rfl rfl (ep233 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep235 := nat_lit 1456936009017093812395090261407357345819120489620333225905856092471466341072705

noncomputable def ep236 := nat_lit 512829106638357208082388530312146504019208297564356994783340103725781778241

noncomputable def ep237 := nat_lit 3814954490776878835078817293684478144710236849857197108904735786781141532311361

noncomputable def ep238 := BSN.sin_dyadic_bound_f 2181456631 2147483648 3 2 1048576 275497 ep235 ep97 ep236 ep237 ep100 ep236 891198 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2181456631) qz268 0 2 ep235 ep97 ep236 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2181456631) qz269 0 2 ep237 ep100 ep236 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz848 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 279424951) qz277)

noncomputable def ep239 := @Enclosure.Real.IsNear.cos_image qz304 qz848 Bool.false 279424951 1048576 53 65536 Bool.true 891198 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz304 Bool.false 1200121030069625185319 4503599627370496000 55565500022939772151 68807000000000000000000 279424951 1048576 53 65536 (ep234 rfl) rfl) (Enclosure.sfrac_false_div 279424951 1048576) (BSN.cos_reduce1 qz848 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 153506363667986620874752) qz279) 226375608064910080 72057594037927936 Bool.false 891198 1048576 42 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q1 279424951 1048576 226375608064910080 72057594037927936 42 153506363667986620874752 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 891198 1048576 153506363667986620874752 151115727451828646838272 2181456631 2147483648 275497 275228 (ep238 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep240 := nat_lit 809636817945780276756420095684226146123519920143547061945379313641359425830721

noncomputable def ep241 := nat_lit 2427884795624064115853095509992054145362521343835512471846571260716626713935681

noncomputable def ep242 := BSN.cos_dyadic_bound_f 2181456631 2147483648 3 2 1048576 275497 ep240 ep104 ep236 ep241 ep106 ep236 552519 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2181456631) qz272 0 2 ep240 ep104 ep236 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2181456631) qz273 0 2 ep241 ep106 ep236 rfl rfl rfl rfl) rfl rfl

noncomputable def ep243 := @Enclosure.Real.IsNear.sin_image qz304 qz848 Bool.false 279424951 1048576 53 65536 Bool.false 552519 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz304 Bool.false 1200121030069625185319 4503599627370496000 55565500022939772151 68807000000000000000000 279424951 1048576 53 65536 (ep234 rfl) rfl) (Enclosure.sfrac_false_div 279424951 1048576) (BSN.sin_reduce1 qz848 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 153506363667986620874752) qz279) 226375608064910080 72057594037927936 Bool.false 552519 1048576 42 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q1 279424951 1048576 226375608064910080 72057594037927936 42 153506363667986620874752 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 552519 1048576 153506363667986620874752 151115727451828646838272 2181456631 2147483648 275497 275228 (ep242 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz573 := (@Enclosure.Real.IsNear.recentre' qz303 Bool.false 316157 1048576 1 1048576 316157 1048576 1 1048576 (ep232 rfl rfl) rfl)

noncomputable def ep244 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz303 (Real.cos qz304)) (@HMul.hMul Real Real Real qz0 qz303 (@Neg.neg Real Real.instNeg (Real.sin qz304))) Bool.true 140879243043 549755813888 9337185859689 37827048286191616 Bool.true 174682749483 1099511627776 18651068233425 75654096572383232 (@Enclosure.Real.IsNear.mulLit_ft qz303 (Real.cos qz304) 316157 1048576 1 1048576 445599 524288 3679539 4509335552 140879243043 549755813888 9337185859689 37827048286191616 qz573 (@Enclosure.Real.IsNear.recentre' (Real.cos qz304) Bool.true 891198 1048576 7359078 9018671104 445599 524288 3679539 4509335552 (ep239 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz303 (@Neg.neg Real Real.instNeg (Real.sin qz304)) 316157 1048576 1 1048576 552519 1048576 3679539 4509335552 174682749483 1099511627776 18651068233425 75654096572383232 qz573 (@Enclosure.Real.IsNear.neg (Real.sin qz304) Bool.false 552519 1048576 3679539 4509335552 (@Enclosure.Real.IsNear.recentre' (Real.sin qz304) Bool.false 552519 1048576 7359078 9018671104 552519 1048576 3679539 4509335552 (ep243 rfl rfl) rfl)) rfl)

noncomputable def ep245 := @ep197 140879243043 549755813888 9337185859689 37827048286191616 Bool.true 174682749483 1099511627776 18651068233425 75654096572383232 Bool.true 151135059271151756771328 549826142637 549755813888 33393136787251 9456762071547904 Bool.true 2509382261643245780992 36516317947 1099511627776 267176508615507 75654096572383232 (ep198 (BSN.head_sum_c_succ qz14 10 11 rfl rfl) (ep230 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep231 ep244) rfl rfl

noncomputable abbrev qz849 := (@Nat.cast Real Real.instNatCast 12)

noncomputable abbrev qz306 := (@Inv.inv Real Real.instInv (Real.sqrt qz849))

noncomputable abbrev qz307 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 12 1)))

noncomputable def ep246 := @Enclosure.Complex.IsNear.of_eq qz836 (Complex.mk (@HMul.hMul Real Real Real qz0 qz306 (Real.cos qz307)) (@HMul.hMul Real Real Real qz0 qz306 (@Neg.neg Real Real.instNeg (Real.sin qz307)))) Bool.false 302262024411 1099511627776 17868505922607 75654096572383232 Bool.false 96854867181 1099511627776 17821814180477 75654096572383232 (BSN.cpow_neg_s_mk qz11 111131 1000 12 (@Eq.refl Real qz11) rfl)

noncomputable abbrev qz850 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 12) qz267)

noncomputable def ep247 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz849) 3632373 1048576 1 1048576 151348 151349 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz849) (Real.sqrt qz850) Bool.false 3632373 1048576 1 1048576 (BSN.sqrt_natCast_div_one 12) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz850) Bool.false 3632373 1048576 1 1048576 3632373 1048576 1 1048576 (BSN.sqrt_enclosure 12 1 1816186 1816187 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep248 := BSN.log_dyadic_bound 4 20 4 3 6720000000 524288 137614 91811840 61440 212580 24 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 4) (BSN.artanhQ 20) 0 3 91811840 6720000000 61440 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz308 := (Real.log (Enclosure.sfrac Bool.false 12 1))

noncomputable def ep249 := @Enclosure.Real.IsNear.mulLit_ff qz11 qz308 111131 1000 0 1 11191020447815397 4503599627370496 500000000206421 68807000000000000000 1243669293386172884007 4503599627370496000 55565500022939772151 68807000000000000000000 qz271 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 500000000206421 68807000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz850) Bool.false 46938541828353910898688 18889465931478580854784 1000000000412842 137614000000000000000 11191020447815397 4503599627370496 500000000206421 68807000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 212580 524288 24973259072661432 36028797018963968 137614 1000000000000000 rfl rfl rfl rfl (ep248 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep250 := nat_lit 3458038893708408117517878171833516745769203697349651146050676333235496892241505

noncomputable def ep251 := nat_lit 2886236949717903131512989045694719357363161541555282477354395739192517727841

noncomputable def ep252 := nat_lit 9052095576079620845571993229680466693293135993419901591836054708229513498596961

noncomputable def ep253 := BSN.sin_dyadic_bound_f 2707331883 2147483648 3 2 1048576 275497 ep250 ep97 ep251 ep252 ep100 ep251 998563 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2707331883) qz268 0 2 ep250 ep97 ep251 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2707331883) qz269 0 2 ep252 ep100 ep251 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz851 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 144782161) qz289)

noncomputable def ep254 := @Enclosure.Real.IsNear.cos_image qz307 qz851 Bool.false 144782161 524288 847 1048576 Bool.false 998563 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz307 Bool.false 1243669293386172884007 4503599627370496000 55565500022939772151 68807000000000000000000 144782161 524288 847 1048576 (ep249 rfl) rfl) (Enclosure.sfrac_false_div 144782161 524288) (BSN.cos_reduce3 qz851 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 95255772345119268667392) qz290) 226375608064910080 72057594037927936 Bool.false 998563 1048576 43 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q3 144782161 524288 226375608064910080 72057594037927936 43 95255772345119268667392 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 998563 1048576 95255772345119268667392 75557863725914323419136 2707331883 2147483648 275497 275228 (ep253 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep255 := nat_lit 1922415490704545800012826979483373622919496792546052984462533249903806059124321

noncomputable def ep256 := nat_lit 5761473998214201593775454960358731430043764054555048388432890958233033141917281

noncomputable def ep257 := BSN.cos_dyadic_bound_f 2707331883 2147483648 3 2 1048576 275497 ep255 ep104 ep251 ep256 ep106 ep251 319973 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2707331883) qz272 0 2 ep255 ep104 ep251 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2707331883) qz273 0 2 ep256 ep106 ep251 rfl rfl rfl rfl) rfl rfl

noncomputable def ep258 := @Enclosure.Real.IsNear.sin_image qz307 qz851 Bool.false 144782161 524288 847 1048576 Bool.true 319973 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz307 Bool.false 1243669293386172884007 4503599627370496000 55565500022939772151 68807000000000000000000 144782161 524288 847 1048576 (ep249 rfl) rfl) (Enclosure.sfrac_false_div 144782161 524288) (BSN.sin_reduce3 qz851 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 95255772345119268667392) qz290) 226375608064910080 72057594037927936 Bool.false 319973 1048576 43 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q3 144782161 524288 226375608064910080 72057594037927936 43 95255772345119268667392 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 319973 1048576 95255772345119268667392 75557863725914323419136 2707331883 2147483648 275497 275228 (ep257 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz574 := (@Enclosure.Real.IsNear.recentre' qz306 Bool.false 302697 1048576 1 1048576 302697 1048576 1 1048576 (ep247 rfl rfl) rfl)

noncomputable def ep259 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz306 (Real.cos qz307)) (@HMul.hMul Real Real Real qz0 qz306 (@Neg.neg Real Real.instNeg (Real.sin qz307))) Bool.false 302262024411 1099511627776 17868505922607 75654096572383232 Bool.false 96854867181 1099511627776 17821814180477 75654096572383232 (@Enclosure.Real.IsNear.mulLit_ff qz306 (Real.cos qz307) 302697 1048576 1 1048576 998563 1048576 58803817 72149368832 302262024411 1099511627776 17868505922607 75654096572383232 qz574 (@Enclosure.Real.IsNear.recentre' (Real.cos qz307) Bool.false 998563 1048576 117607634 144298737664 998563 1048576 58803817 72149368832 (ep254 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz306 (@Neg.neg Real Real.instNeg (Real.sin qz307)) 302697 1048576 1 1048576 319973 1048576 58803817 72149368832 96854867181 1099511627776 17821814180477 75654096572383232 qz574 (@Enclosure.Real.IsNear.neg (Real.sin qz307) Bool.true 319973 1048576 58803817 72149368832 (@Enclosure.Real.IsNear.recentre' (Real.sin qz307) Bool.true 319973 1048576 117607634 144298737664 319973 1048576 58803817 72149368832 (ep258 rfl rfl) rfl)) rfl)

noncomputable def ep260 := @ep195 302262024411 1099511627776 17868505922607 75654096572383232 Bool.false 96854867181 1099511627776 17821814180477 75654096572383232 Bool.true 438369931847103198265344 797390260863 1099511627776 285013600220615 75654096572383232 Bool.false 66342936485917657923584 30169274617 549755813888 17812395174749 4728381035773952 (ep196 (BSN.head_sum_c_succ qz14 11 12 rfl rfl) (ep245 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep246 ep259) rfl rfl

noncomputable abbrev qz852 := (@Nat.cast Real Real.instNatCast 13)

noncomputable abbrev qz309 := (@Inv.inv Real Real.instInv (Real.sqrt qz852))

noncomputable abbrev qz310 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 13 1)))

noncomputable def ep261 := @Enclosure.Complex.IsNear.of_eq qz835 (Complex.mk (@HMul.hMul Real Real Real qz0 qz309 (Real.cos qz310)) (@HMul.hMul Real Real Real qz0 qz309 (@Neg.neg Real Real.instNeg (Real.sin qz310)))) Bool.true 203601401601 1099511627776 17169742888385 75654096572383232 Bool.true 227026030959 1099511627776 17175285017007 75654096572383232 (BSN.cpow_neg_s_mk qz11 111131 1000 13 (@Eq.refl Real qz11) rfl)

noncomputable abbrev qz853 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13) qz267)

noncomputable def ep262 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz852) 3780695 1048576 1 1048576 145411 145412 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz852) (Real.sqrt qz853) Bool.false 3780695 1048576 1 1048576 (BSN.sqrt_natCast_div_one 13) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz853) Bool.false 3780695 1048576 1 1048576 3780695 1048576 1 1048576 (BSN.sqrt_enclosure 13 1 1890347 1890348 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep263 := BSN.log_dyadic_bound 5 21 5 4 35742602096145 524288 137614 699352521000 41015625 254545 26 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 5) (BSN.artanhQ 21) 0 4 699352521000 35742602096145 41015625 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz311 := (Real.log (Enclosure.sfrac Bool.false 13 1))

noncomputable def ep264 := @Enclosure.Real.IsNear.mulLit_ff qz11 qz311 111131 1000 0 1 11551497052968677 4503599627370496 500000000206421 68807000000000000000 1283729418993462043687 4503599627370496000 55565500022939772151 68807000000000000000000 qz271 (BSN.isNear_log_sfrac 13 1 11551497052968677 4503599627370496 500000000206421 68807000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz853) Bool.false 48450490295254733815808 18889465931478580854784 1000000000412842 137614000000000000000 11551497052968677 4503599627370496 500000000206421 68807000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 254545 524288 24973259072661432 36028797018963968 137614 1000000000000000 rfl rfl rfl rfl (ep263 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep265 := nat_lit 6074649719671118907240163723322455056

noncomputable def ep266 := BSN.sin_dyadic_bound_f 1569930078 2147483648 2 1 1048576 275497 ep265 ep178 ep265 ep265 ep179 ep265 700087 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1569930078) qz268 0 1 ep265 ep178 ep265 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1569930078) qz269 0 1 ep265 ep179 ep265 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz854 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 149445773) qz289)

noncomputable def ep267 := @Enclosure.Real.IsNear.cos_image qz310 qz854 Bool.false 149445773 524288 53 65536 Bool.true 700087 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz310 Bool.false 1283729418993462043687 4503599627370496000 55565500022939772151 68807000000000000000000 149445773 524288 53 65536 (ep264 rfl) rfl) (Enclosure.sfrac_false_div 149445773 524288) (BSN.cos_reduce1 qz854 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 55237004031124167458816) qz290) 226375608064910080 72057594037927936 Bool.false 700087 1048576 45 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q1 149445773 524288 226375608064910080 72057594037927936 45 55237004031124167458816 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 700087 1048576 55237004031124167458816 75557863725914323419136 1569930078 2147483648 275497 275228 (ep266 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep268 := nat_lit 217082000775873584969715497717314211721720218237148416832581472020905893724416

noncomputable def ep269 := nat_lit 36901369216700403524014495842444722184693170033478792326602244239139963136

noncomputable def ep270 := nat_lit 651172199589187354102098464160257745720791268371378292913091211574239401246976

noncomputable def ep271 := BSN.cos_dyadic_bound_f 1569930078 2147483648 3 2 1048576 275497 ep268 ep104 ep269 ep270 ep106 ep269 780633 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1569930078) qz272 0 2 ep268 ep104 ep269 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1569930078) qz273 0 2 ep270 ep106 ep269 rfl rfl rfl rfl) rfl rfl

noncomputable def ep272 := @Enclosure.Real.IsNear.sin_image qz310 qz854 Bool.false 149445773 524288 53 65536 Bool.false 780633 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz310 Bool.false 1283729418993462043687 4503599627370496000 55565500022939772151 68807000000000000000000 149445773 524288 53 65536 (ep264 rfl) rfl) (Enclosure.sfrac_false_div 149445773 524288) (BSN.sin_reduce1 qz854 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 55237004031124167458816) qz290) 226375608064910080 72057594037927936 Bool.false 780633 1048576 45 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q1 149445773 524288 226375608064910080 72057594037927936 45 55237004031124167458816 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 780633 1048576 55237004031124167458816 75557863725914323419136 1569930078 2147483648 275497 275228 (ep271 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz575 := (@Enclosure.Real.IsNear.recentre' qz309 Bool.false 290823 1048576 1 1048576 290823 1048576 1 1048576 (ep262 rfl rfl) rfl)

noncomputable def ep273 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz309 (Real.cos qz310)) (@HMul.hMul Real Real Real qz0 qz309 (@Neg.neg Real Real.instNeg (Real.sin qz310))) Bool.true 203601401601 1099511627776 17169742888385 75654096572383232 Bool.true 227026030959 1099511627776 17175285017007 75654096572383232 (@Enclosure.Real.IsNear.mulLit_ft qz309 (Real.cos qz310) 290823 1048576 1 1048576 700087 1048576 3679539 4509335552 203601401601 1099511627776 17169742888385 75654096572383232 qz575 (@Enclosure.Real.IsNear.recentre' (Real.cos qz310) Bool.true 700087 1048576 7359078 9018671104 700087 1048576 3679539 4509335552 (ep267 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz309 (@Neg.neg Real Real.instNeg (Real.sin qz310)) 290823 1048576 1 1048576 780633 1048576 3679539 4509335552 227026030959 1099511627776 17175285017007 75654096572383232 qz575 (@Enclosure.Real.IsNear.neg (Real.sin qz310) Bool.false 780633 1048576 3679539 4509335552 (@Enclosure.Real.IsNear.recentre' (Real.sin qz310) Bool.false 780633 1048576 7359078 9018671104 780633 1048576 3679539 4509335552 (ep272 rfl rfl) rfl)) rfl)

noncomputable def ep274 := @ep193 203601401601 1099511627776 17169742888385 75654096572383232 Bool.true 227026030959 1099511627776 17175285017007 75654096572383232 Bool.true 1100601972185996999000064 7820247363 8589934592 37772917888625 9456762071547904 Bool.true 91637412180668501196800 166687481725 1099511627776 302173607812991 75654096572383232 (ep194 (BSN.head_sum_c_succ qz14 12 13 rfl rfl) (ep260 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep261 ep273) rfl rfl

noncomputable abbrev qz855 := (@Nat.cast Real Real.instNatCast 14)

noncomputable abbrev qz312 := (@Inv.inv Real Real.instInv (Real.sqrt qz855))

noncomputable abbrev qz313 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 14 1)))

noncomputable def ep275 := @Enclosure.Complex.IsNear.of_eq qz834 (Complex.mk (@HMul.hMul Real Real Real qz0 qz312 (Real.cos qz313)) (@HMul.hMul Real Real Real qz0 qz312 (@Neg.neg Real Real.instNeg (Real.sin qz313)))) Bool.true 32483246373 274877906944 4132650398241 18913524143095808 Bool.false 131784550993 549755813888 8281706380685 37827048286191616 (BSN.cpow_neg_s_mk qz11 111131 1000 14 (@Eq.refl Real qz11) rfl)

noncomputable abbrev qz856 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14) qz267)

noncomputable def ep276 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz855) 3923413 1048576 1 1048576 140121 140122 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz855) (Real.sqrt qz856) Bool.false 3923413 1048576 1 1048576 (BSN.sqrt_natCast_div_one 14) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz856) Bool.false 3923413 1048576 1 1048576 3923413 1048576 1 1048576 (BSN.sqrt_enclosure 14 1 1961706 1961707 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep277 := BSN.log_dyadic_bound 6 22 5 4 51857700491520 524288 137614 1346332575744 176359680 293399 28 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 6) (BSN.artanhQ 22) 0 4 1346332575744 51857700491520 176359680 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz314 := (Real.log (Enclosure.sfrac Bool.false 14 1))

noncomputable def ep278 := @Enclosure.Real.IsNear.mulLit_ff qz11 qz314 111131 1000 0 1 11885250371606245 4503599627370496 500000000206421 68807000000000000000 264163951809394722619 900719925474099200 55565500022939772151 68807000000000000000000 qz271 (BSN.isNear_log_sfrac 14 1 11885250371606245 4503599627370496 500000000206421 68807000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz856) Bool.false 49850353174629559828480 18889465931478580854784 1000000000412842 137614000000000000000 11885250371606245 4503599627370496 500000000206421 68807000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 293399 524288 24973259072661432 36028797018963968 137614 1000000000000000 rfl rfl rfl rfl (ep277 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep279 := nat_lit 1166240635062988537403940131563978920637443935371558413539118534613123063715361

noncomputable def ep280 := nat_lit 1063472929072396563282292379037366647887978648792163726081572874940094453281

noncomputable def ep281 := nat_lit 3496594959330820819085255809933862028616555848817090913165192458089489002239521

noncomputable def ep282 := BSN.cos_dyadic_bound_f 2389685811 2147483648 3 2 1048576 275497 ep279 ep104 ep280 ep281 ep106 ep280 463644 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2389685811) qz272 0 2 ep279 ep104 ep280 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2389685811) qz273 0 2 ep281 ep106 ep280 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz857 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 153763657) qz289)

noncomputable def ep283 := @Enclosure.Real.IsNear.cos_image qz313 qz857 Bool.false 153763657 524288 53 65536 Bool.true 463644 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz313 Bool.false 264163951809394722619 900719925474099200 55565500022939772151 68807000000000000000000 153763657 524288 53 65536 (ep278 rfl) rfl) (Enclosure.sfrac_false_div 153763657 524288) (BSN.cos_reduce2 qz857 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 84079594775175143358464) qz290) 226375608064910080 72057594037927936 Bool.false 463644 1048576 46 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q2 153763657 524288 226375608064910080 72057594037927936 46 84079594775175143358464 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 463644 1048576 84079594775175143358464 75557863725914323419136 2389685811 2147483648 275497 275228 (ep282 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep284 := nat_lit 2098382364770121450076466402911932163829088700749771413389548104003669439125025

noncomputable def ep285 := nat_lit 5494041522988962774812097819965190406884366060341833055701827249640659806688801

noncomputable def ep286 := BSN.sin_dyadic_bound_f 2389685811 2147483648 3 2 1048576 275497 ep284 ep97 ep280 ep285 ep100 ep280 940502 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2389685811) qz268 0 2 ep284 ep97 ep280 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2389685811) qz269 0 2 ep285 ep100 ep280 rfl rfl rfl rfl) rfl rfl

noncomputable def ep287 := @Enclosure.Real.IsNear.sin_image qz313 qz857 Bool.false 153763657 524288 53 65536 Bool.true 940502 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz313 Bool.false 264163951809394722619 900719925474099200 55565500022939772151 68807000000000000000000 153763657 524288 53 65536 (ep278 rfl) rfl) (Enclosure.sfrac_false_div 153763657 524288) (BSN.sin_reduce2 qz857 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 84079594775175143358464) qz290) 226375608064910080 72057594037927936 Bool.false 940502 1048576 46 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q2 153763657 524288 226375608064910080 72057594037927936 46 84079594775175143358464 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 940502 1048576 84079594775175143358464 75557863725914323419136 2389685811 2147483648 275497 275228 (ep286 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz576 := (@Enclosure.Real.IsNear.recentre' qz312 Bool.false 280243 1048576 1 1048576 280243 1048576 1 1048576 (ep276 rfl rfl) rfl)

noncomputable def ep288 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz312 (Real.cos qz313)) (@HMul.hMul Real Real Real qz0 qz312 (@Neg.neg Real Real.instNeg (Real.sin qz313))) Bool.true 32483246373 274877906944 4132650398241 18913524143095808 Bool.false 131784550993 549755813888 8281706380685 37827048286191616 (@Enclosure.Real.IsNear.mulLit_ft qz312 (Real.cos qz313) 280243 1048576 1 1048576 115911 262144 3679539 4509335552 32483246373 274877906944 4132650398241 18913524143095808 qz576 (@Enclosure.Real.IsNear.recentre' (Real.cos qz313) Bool.true 463644 1048576 7359078 9018671104 115911 262144 3679539 4509335552 (ep283 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz312 (@Neg.neg Real Real.instNeg (Real.sin qz313)) 280243 1048576 1 1048576 470251 524288 3679539 4509335552 131784550993 549755813888 8281706380685 37827048286191616 qz576 (@Enclosure.Real.IsNear.neg (Real.sin qz313) Bool.true 470251 524288 3679539 4509335552 (@Enclosure.Real.IsNear.recentre' (Real.sin qz313) Bool.true 940502 1048576 7359078 9018671104 470251 524288 3679539 4509335552 (ep287 rfl rfl) rfl)) rfl)

noncomputable def ep289 := @ep191 32483246373 274877906944 4132650398241 18913524143095808 Bool.false 131784550993 549755813888 8281706380685 37827048286191616 Bool.true 2428642188605666623488 282731161989 274877906944 79678486175491 18913524143095808 Bool.false 53261233997374205984768 96881620261 1099511627776 318737020574361 75654096572383232 (ep192 (BSN.head_sum_c_succ qz14 13 14 rfl rfl) (ep274 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep275 ep288) rfl rfl

noncomputable abbrev qz858 := (@Nat.cast Real Real.instNatCast 15)

noncomputable abbrev qz315 := (@Inv.inv Real Real.instInv (Real.sqrt qz858))

noncomputable abbrev qz316 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 15 1)))

noncomputable def ep290 := @Enclosure.Complex.IsNear.of_eq qz833 (Complex.mk (@HMul.hMul Real Real Real qz0 qz315 (Real.cos qz316)) (@HMul.hMul Real Real Real qz0 qz315 (@Neg.neg Real Real.instNeg (Real.sin qz316)))) Bool.false 113448330489 549755813888 7998478111907 37827048286191616 Bool.false 85312384287 549755813888 7991327550853 37827048286191616 (BSN.cpow_neg_s_mk qz11 111131 1000 15 (@Eq.refl Real qz11) rfl)

noncomputable abbrev qz859 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 15) qz267)

noncomputable def ep291 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz858) 4061117 1048576 1 1048576 135370 135371 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz858) (Real.sqrt qz859) Bool.false 4061117 1048576 1 1048576 (BSN.sqrt_natCast_div_one 15) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz859) Bool.false 4061117 1048576 1 1048576 4061117 1048576 1 1048576 (BSN.sqrt_enclosure 15 1 2030558 2030559 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep292 := BSN.log_dyadic_bound 7 23 6 5 430628584065881355 524288 137614 14087658153505881 266939110305 329571 30 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 7) (BSN.artanhQ 23) 0 5 14087658153505881 430628584065881355 266939110305 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz317 := (Real.log (Enclosure.sfrac Bool.false 15 1))

noncomputable def ep293 := @Enclosure.Real.IsNear.mulLit_ff qz11 qz317 111131 1000 0 1 12195965485668069 4503599627370496 500000000206421 68807000000000000000 1355349840387778176039 4503599627370496000 55565500022939772151 68807000000000000000000 qz271 (BSN.isNear_log_sfrac 15 1 12195965485668069 4503599627370496 500000000206421 68807000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz859) Bool.false 51153586820399524478976 18889465931478580854784 1000000000412842 137614000000000000000 12195965485668069 4503599627370496 500000000206421 68807000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 329571 524288 24973259072661432 36028797018963968 137614 1000000000000000 rfl rfl rfl rfl (ep292 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep294 := nat_lit 1006025917014010465599965214956815763428809068959226172994455933722673806401345

noncomputable def ep295 := nat_lit 244570828653818503898495788275737011223286677111312771632798277361965555521

noncomputable def ep296 := nat_lit 2634433810837921227565025617420166282390614621225507375259979105396035834437441

noncomputable def ep297 := BSN.sin_dyadic_bound_f 1988614409 2147483648 3 2 1048576 275497 ep294 ep97 ep295 ep296 ep100 ep295 838058 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1988614409) qz268 0 2 ep294 ep97 ep295 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1988614409) qz269 0 2 ep296 ep100 ep295 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz860 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 315566975) qz277)

noncomputable def ep298 := @Enclosure.Real.IsNear.cos_image qz316 qz860 Bool.false 315566975 1048576 53 65536 Bool.false 838058 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz316 Bool.false 1355349840387778176039 4503599627370496000 55565500022939772151 68807000000000000000000 315566975 1048576 53 65536 (ep293 rfl) rfl) (Enclosure.sfrac_false_div 315566975 1048576) (BSN.cos_reduce3 qz860 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 139936298620118022225920) qz279) 226375608064910080 72057594037927936 Bool.false 838058 1048576 47 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q3 315566975 1048576 226375608064910080 72057594037927936 47 139936298620118022225920 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 838058 1048576 139936298620118022225920 151115727451828646838272 1988614409 2147483648 275497 275228 (ep297 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep299 := nat_lit 559011985376074178001713339770797973909882054611619568450978984635868543803201

noncomputable def ep300 := nat_lit 1676546814470914896997343027735842447707199590480636079809671357352881700298561

noncomputable def ep301 := BSN.cos_dyadic_bound_f 1988614409 2147483648 3 2 1048576 275497 ep299 ep104 ep295 ep300 ep106 ep295 630214 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1988614409) qz272 0 2 ep299 ep104 ep295 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1988614409) qz273 0 2 ep300 ep106 ep295 rfl rfl rfl rfl) rfl rfl

noncomputable def ep302 := @Enclosure.Real.IsNear.sin_image qz316 qz860 Bool.false 315566975 1048576 53 65536 Bool.true 630214 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz316 Bool.false 1355349840387778176039 4503599627370496000 55565500022939772151 68807000000000000000000 315566975 1048576 53 65536 (ep293 rfl) rfl) (Enclosure.sfrac_false_div 315566975 1048576) (BSN.sin_reduce3 qz860 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 139936298620118022225920) qz279) 226375608064910080 72057594037927936 Bool.false 630214 1048576 47 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q3 315566975 1048576 226375608064910080 72057594037927936 47 139936298620118022225920 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 630214 1048576 139936298620118022225920 151115727451828646838272 1988614409 2147483648 275497 275228 (ep301 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz577 := (@Enclosure.Real.IsNear.recentre' qz315 Bool.false 270741 1048576 1 1048576 270741 1048576 1 1048576 (ep291 rfl rfl) rfl)

noncomputable def ep303 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz315 (Real.cos qz316)) (@HMul.hMul Real Real Real qz0 qz315 (@Neg.neg Real Real.instNeg (Real.sin qz316))) Bool.false 113448330489 549755813888 7998478111907 37827048286191616 Bool.false 85312384287 549755813888 7991327550853 37827048286191616 (@Enclosure.Real.IsNear.mulLit_ff qz315 (Real.cos qz316) 270741 1048576 1 1048576 419029 524288 3679539 4509335552 113448330489 549755813888 7998478111907 37827048286191616 qz577 (@Enclosure.Real.IsNear.recentre' (Real.cos qz316) Bool.false 838058 1048576 7359078 9018671104 419029 524288 3679539 4509335552 (ep298 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz315 (@Neg.neg Real Real.instNeg (Real.sin qz316)) 270741 1048576 1 1048576 315107 524288 3679539 4509335552 85312384287 549755813888 7991327550853 37827048286191616 qz577 (@Enclosure.Real.IsNear.neg (Real.sin qz316) Bool.true 315107 524288 3679539 4509335552 (@Enclosure.Real.IsNear.recentre' (Real.sin qz316) Bool.true 630214 1048576 7359078 9018671104 315107 524288 3679539 4509335552 (ep302 rfl rfl) rfl)) rfl)

noncomputable def ep304 := @ep189 113448330489 549755813888 7998478111907 37827048286191616 Bool.false 85312384287 549755813888 7991327550853 37827048286191616 Bool.true 124248660439655163887616 452013993489 549755813888 167355450462889 37827048286191616 Bool.false 147063192514225221140480 267506388835 1099511627776 334719675676067 75654096572383232 (ep190 (BSN.head_sum_c_succ qz14 14 15 rfl rfl) (ep289 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep290 ep303) rfl rfl

noncomputable abbrev qz861 := (@Nat.cast Real Real.instNatCast 16)

noncomputable abbrev qz318 := (@Inv.inv Real Real.instInv (Real.sqrt qz861))

noncomputable abbrev qz319 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 16 1)))

noncomputable def ep305 := @Enclosure.Complex.IsNear.of_eq qz832 (Complex.mk (@HMul.hMul Real Real Real qz0 qz318 (Real.cos qz319)) (@HMul.hMul Real Real Real qz0 qz318 (@Neg.neg Real Real.instNeg (Real.sin qz319)))) Bool.false 266702977485 1099511627776 15503109043621 75654096572383232 Bool.true 33266733129 549755813888 7725284387649 37827048286191616 (BSN.cpow_neg_s_mk qz11 111131 1000 16 (@Eq.refl Real qz11) rfl)

noncomputable abbrev qz862 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16) qz267)

noncomputable def ep306 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz861) 4194305 1048576 1 1048576 131071 131072 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz861) (Real.sqrt qz862) Bool.false 4194305 1048576 1 1048576 (BSN.sqrt_natCast_div_one 16) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz862) Bool.false 4194305 1048576 1 1048576 4194305 1048576 1 1048576 (BSN.sqrt_enclosure 16 1 2097152 2097153 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep307 := BSN.log_dyadic_bound 0 32 1 0 1 524288 137614 0 1 0 32 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 32) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz320 := (Real.log (Enclosure.sfrac Bool.false 16 1))

noncomputable def ep308 := @Enclosure.Real.IsNear.mulLit_ff qz11 qz320 111131 1000 0 1 3121657384082679 1125899906842624 125000000068807 17201750000000000000 346912906750492199949 1125899906842624000 13891375007646590717 17201750000000000000000 qz271 (BSN.isNear_log_sfrac 16 1 3121657384082679 1125899906842624 125000000068807 17201750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz862) Bool.false 52372720210750067441664 18889465931478580854784 1000000000550456 137614000000000000000 3121657384082679 1125899906842624 125000000068807 17201750000000000000 (BSN.log_rat_reduce_isNear 16 1 4 32 32 0 524288 24973259072661432 36028797018963968 137614 1000000000000000 rfl rfl rfl rfl (ep307 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep309 := nat_lit 75974862927002971140188496107136016

noncomputable def ep310 := BSN.cos_dyadic_bound_f 525009886 2147483648 2 1 1048576 275497 ep309 ep118 ep309 ep309 ep119 ep309 1017395 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 525009886) qz272 0 1 ep309 ep118 ep309 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 525009886) qz273 0 1 ep309 ep119 ep309 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz863 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 323087821) qz277)

noncomputable def ep311 := @Enclosure.Real.IsNear.cos_image qz319 qz863 Bool.false 323087821 1048576 53 65536 Bool.false 1017395 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz319 Bool.false 346912906750492199949 1125899906842624000 13891375007646590717 17201750000000000000000 323087821 1048576 53 65536 (ep308 rfl) rfl) (Enclosure.sfrac_false_div 323087821 1048576) (BSN.cos_reduce0 qz863 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 36944286388310593503232) qz279) 226375608064910080 72057594037927936 Bool.false 1017395 1048576 49 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q0 323087821 1048576 226375608064910080 72057594037927936 49 36944286388310593503232 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1017395 1048576 36944286388310593503232 151115727451828646838272 525009886 2147483648 275497 275228 (ep310 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep312 := BSN.sin_dyadic_bound_f 525009886 2147483648 2 1 1048576 275497 ep309 ep178 ep309 ep309 ep179 ep309 253806 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 525009886) qz268 0 1 ep309 ep178 ep309 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 525009886) qz269 0 1 ep309 ep179 ep309 rfl rfl rfl rfl) rfl rfl

noncomputable def ep313 := @Enclosure.Real.IsNear.sin_image qz319 qz863 Bool.false 323087821 1048576 53 65536 Bool.false 253806 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz319 Bool.false 346912906750492199949 1125899906842624000 13891375007646590717 17201750000000000000000 323087821 1048576 53 65536 (ep308 rfl) rfl) (Enclosure.sfrac_false_div 323087821 1048576) (BSN.sin_reduce0 qz863 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 36944286388310593503232) qz279) 226375608064910080 72057594037927936 Bool.false 253806 1048576 49 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q0 323087821 1048576 226375608064910080 72057594037927936 49 36944286388310593503232 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 253806 1048576 36944286388310593503232 151115727451828646838272 525009886 2147483648 275497 275228 (ep312 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz578 := (@Enclosure.Real.IsNear.recentre' qz318 Bool.false 262143 1048576 1 1048576 262143 1048576 1 1048576 (ep306 rfl rfl) rfl)

noncomputable def ep314 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz318 (Real.cos qz319)) (@HMul.hMul Real Real Real qz0 qz318 (@Neg.neg Real Real.instNeg (Real.sin qz319))) Bool.false 266702977485 1099511627776 15503109043621 75654096572383232 Bool.true 33266733129 549755813888 7725284387649 37827048286191616 (@Enclosure.Real.IsNear.mulLit_ff qz318 (Real.cos qz319) 262143 1048576 1 1048576 1017395 1048576 3679539 4509335552 266702977485 1099511627776 15503109043621 75654096572383232 qz578 (@Enclosure.Real.IsNear.recentre' (Real.cos qz319) Bool.false 1017395 1048576 7359078 9018671104 1017395 1048576 3679539 4509335552 (ep311 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz318 (@Neg.neg Real Real.instNeg (Real.sin qz319)) 262143 1048576 1 1048576 126903 524288 3679539 4509335552 33266733129 549755813888 7725284387649 37827048286191616 qz578 (@Enclosure.Real.IsNear.neg (Real.sin qz319) Bool.false 126903 524288 3679539 4509335552 (@Enclosure.Real.IsNear.recentre' (Real.sin qz319) Bool.false 253806 1048576 7359078 9018671104 126903 524288 3679539 4509335552 (ep313 rfl rfl) rfl)) rfl)

noncomputable def ep315 := @ep187 266702977485 1099511627776 15503109043621 75654096572383232 Bool.true 33266733129 549755813888 7725284387649 37827048286191616 Bool.true 350373129305001541238784 637325009493 1099511627776 350214009969399 75654096572383232 Bool.false 110486032620768645349376 200972922577 1099511627776 350170244451365 75654096572383232 (ep188 (BSN.head_sum_c_succ qz14 15 16 rfl rfl) (ep304 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep305 ep314) rfl rfl

theorem EMRow35.d8 : Enclosure.Complex.IsNear (BSN.headSumC qz14 17) Bool.true 637325009493 1099511627776 350214009969399 75654096572383232 Bool.false 200972922577 1099511627776 350170244451365 75654096572383232 := ep186 (BSN.head_sum_c_succ qz14 16 17 rfl rfl) (ep315 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz864 := (@HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast 24) qz17)

noncomputable def ep316 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 25) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz14 24) qz864) Bool.false 82834314697 1099511627776 460210098128287 75654096572383232 Bool.true 15465575669 137438953472 115031352119321 18913524143095808

noncomputable def ep317 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz14 24) qz864 Bool.false 1720642235 68719476736 223795611564123 37827048286191616 Bool.false 46895408043 549755813888 223727193736515 37827048286191616 Bool.false

noncomputable abbrev qz865 := (@HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast 23) qz17)

noncomputable def ep318 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 24) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz14 23) qz865) Bool.false 1720642235 68719476736 223795611564123 37827048286191616 Bool.false 46895408043 549755813888 223727193736515 37827048286191616

noncomputable def ep319 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz14 23) qz865 Bool.false 124353674065 549755813888 54333064611371 9456762071547904 Bool.false 77072077617 549755813888 217289146249915 37827048286191616 Bool.true

noncomputable abbrev qz866 := (@HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast 22) qz17)

noncomputable def ep320 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 23) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz14 22) qz866) Bool.false 124353674065 549755813888 54333064611371 9456762071547904 Bool.false 77072077617 549755813888 217289146249915 37827048286191616

noncomputable def ep321 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz14 22) qz866 Bool.false 359826578537 1099511627776 421468870226619 75654096572383232 Bool.true 52262222397 1099511627776 421353318090257 75654096572383232 Bool.true

noncomputable abbrev qz867 := (@HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast 21) qz17)

noncomputable def ep322 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 22) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz14 21) qz867) Bool.false 359826578537 1099511627776 421468870226619 75654096572383232 Bool.true 52262222397 1099511627776 421353318090257 75654096572383232

noncomputable def ep323 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz14 21) qz867 Bool.false 220516917323 1099511627776 407929598252357 75654096572383232 Bool.true 247609640629 1099511627776 407780344309781 75654096572383232 Bool.false

noncomputable abbrev qz868 := (@HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast 20) qz17)

noncomputable def ep324 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 21) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz14 20) qz868) Bool.false 220516917323 1099511627776 407929598252357 75654096572383232 Bool.true 247609640629 1099511627776 407780344309781 75654096572383232

noncomputable def ep325 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz14 20) qz868 Bool.true 12171053737 549755813888 74184866573 14242111553536 Bool.true 269756175555 1099511627776 4746820653511 911495139426304 Bool.false

noncomputable abbrev qz869 := (@HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast 19) qz17)

noncomputable def ep326 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 20) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz14 19) qz869) Bool.true 12171053737 549755813888 74184866573 14242111553536 Bool.true 269756175555 1099511627776 4746820653511 911495139426304

noncomputable def ep327 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz14 19) qz869 Bool.true 123285736955 549755813888 94961012156127 18913524143095808 Bool.true 37604856569 274877906944 189894790983303 37827048286191616 Bool.false

noncomputable abbrev qz870 := (@HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast 18) qz17)

noncomputable def ep328 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 19) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz14 18) qz870) Bool.true 123285736955 549755813888 94961012156127 18913524143095808 Bool.true 37604856569 274877906944 189894790983303 37827048286191616

noncomputable def ep329 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz14 18) qz870 Bool.true 216545200993 549755813888 22827602179133 4728381035773952 Bool.false 29504771667 1099511627776 365189004185407 75654096572383232 Bool.false

noncomputable abbrev qz871 := (@HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast 17) qz17)

noncomputable def ep330 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 18) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz14 17) qz871) Bool.true 216545200993 549755813888 22827602179133 4728381035773952 Bool.false 29504771667 1099511627776 365189004185407 75654096572383232

noncomputable def ep331 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz14 17) qz871 Bool.true 637325009493 1099511627776 350214009969399 75654096572383232 Bool.false 200972922577 1099511627776 350170244451365 75654096572383232 Bool.false

noncomputable abbrev qz872 := (@Nat.cast Real Real.instNatCast 17)

noncomputable abbrev qz321 := (@Inv.inv Real Real.instInv (Real.sqrt qz872))

noncomputable abbrev qz322 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 17 1)))

noncomputable def ep332 := @Enclosure.Complex.IsNear.of_eq qz871 (Complex.mk (@HMul.hMul Real Real Real qz0 qz321 (Real.cos qz322)) (@HMul.hMul Real Real Real qz0 qz321 (@Neg.neg Real Real.instNeg (Real.sin qz322)))) Bool.false 204234607507 1099511627776 15027624896729 75654096572383232 Bool.true 85734075455 549755813888 7509379867021 37827048286191616 (BSN.cpow_neg_s_mk qz11 111131 1000 17 (@Eq.refl Real qz11) rfl)

noncomputable abbrev qz873 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 17) qz267)

noncomputable def ep333 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz872) 4323389 1048576 1 1048576 127158 127159 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz872) (Real.sqrt qz873) Bool.false 4323389 1048576 1 1048576 (BSN.sqrt_natCast_div_one 17) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz873) Bool.false 4323389 1048576 1 1048576 4323389 1048576 1 1048576 (BSN.sqrt_enclosure 17 1 2161694 2161695 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep334 := BSN.log_dyadic_bound 1 33 2 1 3267 524288 137614 1 1 31784 34 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1) (BSN.artanhQ 33) 0 1 1 3267 1 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz323 := (Real.log (Enclosure.sfrac Bool.false 17 1))

noncomputable def ep335 := @Enclosure.Real.IsNear.mulLit_ff qz11 qz323 111131 1000 0 1 3189913004350711 1125899906842624 125000000068807 17201750000000000000 354498222086498864141 1125899906842624000 13891375007646590717 17201750000000000000000 qz271 (BSN.isNear_log_sfrac 17 1 3189913004350711 1125899906842624 125000000068807 17201750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz873) Bool.false 53517859495200818200576 18889465931478580854784 1000000000550456 137614000000000000000 3189913004350711 1125899906842624 125000000068807 17201750000000000000 (BSN.log_rat_reduce_isNear 17 1 4 34 32 31784 524288 24973259072661432 36028797018963968 137614 1000000000000000 rfl rfl rfl rfl (ep334 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep336 := nat_lit 180816371382791292332328884320548844282534000994067260277913377942460750785121

noncomputable def ep337 := nat_lit 25603244988452285836219481461441817236873701075369539766328777470717356641

noncomputable def ep338 := nat_lit 542397907658396972425314213998723649213128255580051041754207476272440817642081

noncomputable def ep339 := BSN.cos_dyadic_bound_f 1499812181 2147483648 3 2 1048576 275497 ep336 ep104 ep337 ep338 ep106 ep337 803071 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1499812181) qz272 0 2 ep336 ep104 ep337 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1499812181) qz273 0 2 ep338 ep106 ep337 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz579 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 82538049) (@Nat.cast Real Real.instNatCast 262144))

noncomputable def ep340 := @Enclosure.Real.IsNear.cos_image qz322 qz579 Bool.false 82538049 262144 53 65536 Bool.false 803071 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz322 Bool.false 354498222086498864141 1125899906842624000 13891375007646590717 17201750000000000000000 82538049 262144 53 65536 (ep335 rfl) rfl) (Enclosure.sfrac_false_div 82538049 262144) (BSN.cos_reduce0 qz579 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26384974935650077769728) qz557) 226375608064910080 72057594037927936 Bool.false 803071 1048576 50 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q0 82538049 262144 226375608064910080 72057594037927936 50 26384974935650077769728 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 803071 1048576 26384974935650077769728 37778931862957161709568 1499812181 2147483648 275497 275228 (ep339 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep341 := nat_lit 5059964919685934525818890888612051121

noncomputable def ep342 := BSN.sin_dyadic_bound_f 1499812181 2147483648 2 1 1048576 275497 ep341 ep178 ep341 ep341 ep179 ep341 674230 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1499812181) qz268 0 1 ep341 ep178 ep341 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1499812181) qz269 0 1 ep341 ep179 ep341 rfl rfl rfl rfl) rfl rfl

noncomputable def ep343 := @Enclosure.Real.IsNear.sin_image qz322 qz579 Bool.false 82538049 262144 53 65536 Bool.false 674230 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz322 Bool.false 354498222086498864141 1125899906842624000 13891375007646590717 17201750000000000000000 82538049 262144 53 65536 (ep335 rfl) rfl) (Enclosure.sfrac_false_div 82538049 262144) (BSN.sin_reduce0 qz579 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26384974935650077769728) qz557) 226375608064910080 72057594037927936 Bool.false 674230 1048576 50 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q0 82538049 262144 226375608064910080 72057594037927936 50 26384974935650077769728 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 674230 1048576 26384974935650077769728 37778931862957161709568 1499812181 2147483648 275497 275228 (ep342 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz580 := (@Enclosure.Real.IsNear.recentre' qz321 Bool.false 254317 1048576 1 1048576 254317 1048576 1 1048576 (ep333 rfl rfl) rfl)

noncomputable def ep344 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz321 (Real.cos qz322)) (@HMul.hMul Real Real Real qz0 qz321 (@Neg.neg Real Real.instNeg (Real.sin qz322))) Bool.false 204234607507 1099511627776 15027624896729 75654096572383232 Bool.true 85734075455 549755813888 7509379867021 37827048286191616 (@Enclosure.Real.IsNear.mulLit_ff qz321 (Real.cos qz322) 254317 1048576 1 1048576 803071 1048576 3679539 4509335552 204234607507 1099511627776 15027624896729 75654096572383232 qz580 (@Enclosure.Real.IsNear.recentre' (Real.cos qz322) Bool.false 803071 1048576 7359078 9018671104 803071 1048576 3679539 4509335552 (ep340 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz321 (@Neg.neg Real Real.instNeg (Real.sin qz322)) 254317 1048576 1 1048576 337115 524288 3679539 4509335552 85734075455 549755813888 7509379867021 37827048286191616 qz580 (@Enclosure.Real.IsNear.neg (Real.sin qz322) Bool.false 337115 524288 3679539 4509335552 (@Enclosure.Real.IsNear.recentre' (Real.sin qz322) Bool.false 674230 1048576 7359078 9018671104 337115 524288 3679539 4509335552 (ep343 rfl rfl) rfl)) rfl)

noncomputable def ep345 := @ep331 204234607507 1099511627776 15027624896729 75654096572383232 Bool.true 85734075455 549755813888 7509379867021 37827048286191616 Bool.true 476187932861789043163136 216545200993 549755813888 22827602179133 4728381035773952 Bool.false 16220419761371187511296 29504771667 1099511627776 365189004185407 75654096572383232 EMRow35.d8 (ep332 ep344) rfl rfl

noncomputable abbrev qz874 := (@Nat.cast Real Real.instNatCast 18)

noncomputable abbrev qz324 := (@Inv.inv Real Real.instInv (Real.sqrt qz874))

noncomputable abbrev qz325 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 18 1)))

noncomputable def ep346 := @Enclosure.Complex.IsNear.of_eq qz870 (Complex.mk (@HMul.hMul Real Real Real qz0 qz324 (Real.cos qz325)) (@HMul.hMul Real Real Real qz0 qz324 (@Neg.neg Real Real.instNeg (Real.sin qz325)))) Bool.false 46629732019 274877906944 3650603439595 18913524143095808 Bool.true 179924197943 1099511627776 14600577781199 75654096572383232 (BSN.cpow_neg_s_mk qz11 111131 1000 18 (@Eq.refl Real qz11) rfl)

noncomputable abbrev qz875 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 18) qz267)

noncomputable def ep347 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz874) 4448731 1048576 1 1048576 123575 123576 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz874) (Real.sqrt qz875) Bool.false 4448731 1048576 1 1048576 (BSN.sqrt_natCast_div_one 18) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz875) Bool.false 4448731 1048576 1 1048576 4448731 1048576 1 1048576 (BSN.sqrt_enclosure 18 1 2224365 2224366 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep348 := BSN.log_dyadic_bound 2 34 2 1 3468 524288 137614 4 4 61752 36 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 2) (BSN.artanhQ 34) 0 1 4 3468 4 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz326 := (Real.log (Enclosure.sfrac Bool.false 18 1))

noncomputable def ep349 := @Enclosure.Real.IsNear.mulLit_ff qz11 qz326 111131 1000 0 1 3254268794313975 1125899906842624 125000000068807 17201750000000000000 14466005815236254229 45035996273704960 13891375007646590717 17201750000000000000000 qz271 (BSN.isNear_log_sfrac 18 1 3254268794313975 1125899906842624 125000000068807 17201750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz875) Bool.false 54597570484265130393600 18889465931478580854784 1000000000550456 137614000000000000000 3254268794313975 1125899906842624 125000000068807 17201750000000000000 (BSN.log_rat_reduce_isNear 18 1 4 36 32 61752 524288 24973259072661432 36028797018963968 137614 1000000000000000 rfl rfl rfl rfl (ep348 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep350 := nat_lit 263592386618737623344230965821524339729059448248330434231782089878036301618721

noncomputable def ep351 := nat_lit 54403763854731739963104883158635830136878185759624918169385410590710046241

noncomputable def ep352 := nat_lit 790668352328503406552766687698255747526904588373472052859007498812927484763681

noncomputable def ep353 := BSN.cos_dyadic_bound_f 1647986381 2147483648 3 2 1048576 275497 ep350 ep104 ep351 ep352 ep106 ep351 754676 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1647986381) qz272 0 2 ep350 ep104 ep351 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1647986381) qz273 0 2 ep352 ep106 ep351 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz581 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 21050809) (@Nat.cast Real Real.instNatCast 65536))

noncomputable abbrev qz582 := (@Nat.cast Real Real.instNatCast 9444732965739290427392)

noncomputable def ep354 := @Enclosure.Real.IsNear.cos_image qz325 qz581 Bool.false 21050809 65536 53 65536 Bool.false 754676 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz325 Bool.false 14466005815236254229 45035996273704960 13891375007646590717 17201750000000000000000 21050809 65536 53 65536 (ep349 rfl) rfl) (Enclosure.sfrac_false_div 21050809 65536) (BSN.cos_reduce0 qz581 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 7247920754962284412928) qz582) 226375608064910080 72057594037927936 Bool.false 754676 1048576 51 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q0 21050809 65536 226375608064910080 72057594037927936 51 7247920754962284412928 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 754676 1048576 7247920754962284412928 9444732965739290427392 1647986381 2147483648 275497 275228 (ep353 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep355 := nat_lit 7375890716024183337364966073124619921

noncomputable def ep356 := BSN.sin_dyadic_bound_f 1647986381 2147483648 2 1 1048576 275497 ep355 ep178 ep355 ep355 ep179 ep355 727993 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1647986381) qz268 0 1 ep355 ep178 ep355 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1647986381) qz269 0 1 ep355 ep179 ep355 rfl rfl rfl rfl) rfl rfl

noncomputable def ep357 := @Enclosure.Real.IsNear.sin_image qz325 qz581 Bool.false 21050809 65536 53 65536 Bool.false 727993 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz325 Bool.false 14466005815236254229 45035996273704960 13891375007646590717 17201750000000000000000 21050809 65536 53 65536 (ep349 rfl) rfl) (Enclosure.sfrac_false_div 21050809 65536) (BSN.sin_reduce0 qz581 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 7247920754962284412928) qz582) 226375608064910080 72057594037927936 Bool.false 727993 1048576 51 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q0 21050809 65536 226375608064910080 72057594037927936 51 7247920754962284412928 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 727993 1048576 7247920754962284412928 9444732965739290427392 1647986381 2147483648 275497 275228 (ep356 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz583 := (@Enclosure.Real.IsNear.recentre' qz324 Bool.false 247151 1048576 1 1048576 247151 1048576 1 1048576 (ep347 rfl rfl) rfl)

noncomputable def ep358 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz324 (Real.cos qz325)) (@HMul.hMul Real Real Real qz0 qz324 (@Neg.neg Real Real.instNeg (Real.sin qz325))) Bool.false 46629732019 274877906944 3650603439595 18913524143095808 Bool.true 179924197943 1099511627776 14600577781199 75654096572383232 (@Enclosure.Real.IsNear.mulLit_ff qz324 (Real.cos qz325) 247151 1048576 1 1048576 188669 262144 3679539 4509335552 46629732019 274877906944 3650603439595 18913524143095808 qz583 (@Enclosure.Real.IsNear.recentre' (Real.cos qz325) Bool.false 754676 1048576 7359078 9018671104 188669 262144 3679539 4509335552 (ep354 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz324 (@Neg.neg Real Real.instNeg (Real.sin qz325)) 247151 1048576 1 1048576 727993 1048576 3679539 4509335552 179924197943 1099511627776 14600577781199 75654096572383232 qz583 (@Enclosure.Real.IsNear.neg (Real.sin qz325) Bool.false 727993 1048576 3679539 4509335552 (@Enclosure.Real.IsNear.recentre' (Real.sin qz325) Bool.false 727993 1048576 7359078 9018671104 727993 1048576 3679539 4509335552 (ep357 rfl rfl) rfl)) rfl)

noncomputable def ep359 := @ep329 46629732019 274877906944 3650603439595 18913524143095808 Bool.true 179924197943 1099511627776 14600577781199 75654096572383232 Bool.true 33888525330238951915520 123285736955 549755813888 94961012156127 18913524143095808 Bool.true 165387908233856785842176 37604856569 274877906944 189894790983303 37827048286191616 (ep330 (BSN.head_sum_c_succ qz14 17 18 rfl rfl) (ep345 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep346 ep358) rfl rfl

noncomputable abbrev qz876 := (@Nat.cast Real Real.instNatCast 19)

noncomputable abbrev qz327 := (@Inv.inv Real Real.instInv (Real.sqrt qz876))

noncomputable abbrev qz328 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 19 1)))

noncomputable def ep360 := @Enclosure.Complex.IsNear.of_eq qz869 (Complex.mk (@HMul.hMul Real Real Real qz0 qz327 (Real.cos qz328)) (@HMul.hMul Real Real Real qz0 qz327 (@Neg.neg Real Real.instNeg (Real.sin qz328)))) Bool.false 55557341609 274877906944 3556490652817 18913524143095808 Bool.true 119336749279 1099511627776 14196532274807 75654096572383232 (BSN.cpow_neg_s_mk qz11 111131 1000 19 (@Eq.refl Real qz11) rfl)

noncomputable abbrev qz877 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 19) qz267)

noncomputable def ep361 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz876) 4570637 1048576 1 1048576 120279 120280 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz876) (Real.sqrt qz877) Bool.false 4570637 1048576 1 1048576 (BSN.sqrt_natCast_div_one 19) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz877) Bool.false 4570637 1048576 1 1048576 4570637 1048576 1 1048576 (BSN.sqrt_enclosure 19 1 2285318 2285319 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep362 := BSN.log_dyadic_bound 3 35 3 2 22509375 524288 137614 55368 243 90099 38 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 3) (BSN.artanhQ 35) 0 2 55368 22509375 243 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz329 := (Real.log (Enclosure.sfrac Bool.false 19 1))

noncomputable def ep363 := @Enclosure.Real.IsNear.mulLit_ff qz11 qz329 111131 1000 0 1 3315143513283831 1125899906842624 125000000068807 17201750000000000000 368415213774745422861 1125899906842624000 13891375007646590717 17201750000000000000000 qz271 (BSN.isNear_log_sfrac 19 1 3315143513283831 1125899906842624 125000000068807 17201750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz877) Bool.false 55618878793361701994496 18889465931478580854784 1000000000550456 137614000000000000000 3315143513283831 1125899906842624 125000000068807 17201750000000000000 (BSN.log_rat_reduce_isNear 19 1 4 38 32 90099 524288 24973259072661432 36028797018963968 137614 1000000000000000 rfl rfl rfl rfl (ep362 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep364 := nat_lit 1254363396422956952242283591611597056

noncomputable def ep365 := BSN.cos_dyadic_bound_f 1058292804 2147483648 2 1 1048576 275497 ep364 ep118 ep364 ep364 ep119 ep364 923804 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1058292804) qz272 0 1 ep364 ep118 ep364 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1058292804) qz273 0 1 ep364 ep119 ep364 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz878 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 343113405) qz277)

noncomputable def ep366 := @Enclosure.Real.IsNear.cos_image qz328 qz878 Bool.false 343113405 1048576 53 65536 Bool.false 923804 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz328 Bool.false 368415213774745422861 1125899906842624000 13891375007646590717 17201750000000000000000 343113405 1048576 53 65536 (ep363 rfl) rfl) (Enclosure.sfrac_false_div 343113405 1048576) (BSN.cos_reduce0 qz878 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 74470735649906905579520) qz279) 226375608064910080 72057594037927936 Bool.false 923804 1048576 52 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q0 343113405 1048576 226375608064910080 72057594037927936 52 74470735649906905579520 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 923804 1048576 74470735649906905579520 151115727451828646838272 1058292804 2147483648 275497 275228 (ep365 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep367 := BSN.sin_dyadic_bound_f 1058292804 2147483648 2 1 1048576 275497 ep364 ep178 ep364 ep364 ep179 ep364 496081 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1058292804) qz268 0 1 ep364 ep178 ep364 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1058292804) qz269 0 1 ep364 ep179 ep364 rfl rfl rfl rfl) rfl rfl

noncomputable def ep368 := @Enclosure.Real.IsNear.sin_image qz328 qz878 Bool.false 343113405 1048576 53 65536 Bool.false 496081 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz328 Bool.false 368415213774745422861 1125899906842624000 13891375007646590717 17201750000000000000000 343113405 1048576 53 65536 (ep363 rfl) rfl) (Enclosure.sfrac_false_div 343113405 1048576) (BSN.sin_reduce0 qz878 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 74470735649906905579520) qz279) 226375608064910080 72057594037927936 Bool.false 496081 1048576 52 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q0 343113405 1048576 226375608064910080 72057594037927936 52 74470735649906905579520 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 496081 1048576 74470735649906905579520 151115727451828646838272 1058292804 2147483648 275497 275228 (ep367 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz584 := (@Enclosure.Real.IsNear.recentre' qz327 Bool.false 240559 1048576 1 1048576 240559 1048576 1 1048576 (ep361 rfl rfl) rfl)

noncomputable def ep369 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz327 (Real.cos qz328)) (@HMul.hMul Real Real Real qz0 qz327 (@Neg.neg Real Real.instNeg (Real.sin qz328))) Bool.false 55557341609 274877906944 3556490652817 18913524143095808 Bool.true 119336749279 1099511627776 14196532274807 75654096572383232 (@Enclosure.Real.IsNear.mulLit_ff qz327 (Real.cos qz328) 240559 1048576 1 1048576 230951 262144 3679539 4509335552 55557341609 274877906944 3556490652817 18913524143095808 qz584 (@Enclosure.Real.IsNear.recentre' (Real.cos qz328) Bool.false 923804 1048576 7359078 9018671104 230951 262144 3679539 4509335552 (ep366 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz327 (@Neg.neg Real Real.instNeg (Real.sin qz328)) 240559 1048576 1 1048576 496081 1048576 3679539 4509335552 119336749279 1099511627776 14196532274807 75654096572383232 qz584 (@Enclosure.Real.IsNear.neg (Real.sin qz328) Bool.false 496081 1048576 3679539 4509335552 (@Enclosure.Real.IsNear.recentre' (Real.sin qz328) Bool.false 496081 1048576 7359078 9018671104 496081 1048576 3679539 4509335552 (ep368 rfl rfl) rfl)) rfl)

noncomputable def ep370 := @ep327 55557341609 274877906944 3556490652817 18913524143095808 Bool.true 119336749279 1099511627776 14196532274807 75654096572383232 Bool.true 3345553776529509449728 12171053737 549755813888 74184866573 14242111553536 Bool.true 74150012921776617553920 269756175555 1099511627776 4746820653511 911495139426304 (ep328 (BSN.head_sum_c_succ qz14 18 19 rfl rfl) (ep359 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep360 ep369) rfl rfl

noncomputable abbrev qz879 := (@Nat.cast Real Real.instNatCast 20)

noncomputable abbrev qz330 := (@Inv.inv Real Real.instInv (Real.sqrt qz879))

noncomputable abbrev qz331 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 20 1)))

noncomputable def ep371 := @Enclosure.Complex.IsNear.of_eq qz868 (Complex.mk (@HMul.hMul Real Real Real qz0 qz330 (Real.cos qz331)) (@HMul.hMul Real Real Real qz0 qz330 (@Neg.neg Real Real.instNeg (Real.sin qz331)))) Bool.false 244859024797 1099511627776 13859587016581 75654096572383232 Bool.false 11073267463 549755813888 862139379273 4728381035773952 (BSN.cpow_neg_s_mk qz11 111131 1000 20 (@Eq.refl Real qz11) rfl)

noncomputable abbrev qz880 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 20) qz267)

noncomputable def ep372 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz879) 4689375 1048576 1 1048576 117234 117235 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz879) (Real.sqrt qz880) Bool.false 4689375 1048576 1 1048576 (BSN.sqrt_natCast_div_one 20) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz880) Bool.false 4689375 1048576 1 1048576 4689375 1048576 1 1048576 (BSN.sqrt_enclosure 20 1 2344687 2344688 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep373 := BSN.log_dyadic_bound 4 36 3 2 25194240 524288 137614 104448 768 116991 40 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 4) (BSN.artanhQ 36) 0 2 104448 25194240 768 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz332 := (Real.log (Enclosure.sfrac Bool.false 20 1))

noncomputable def ep374 := @Enclosure.Real.IsNear.mulLit_ff qz11 qz332 111131 1000 0 1 3372893643545847 1125899906842624 125000000068807 17201750000000000000 374833043500893522957 1125899906842624000 13891375007646590717 17201750000000000000000 qz271 (BSN.isNear_log_sfrac 20 1 3372893643545847 1125899906842624 125000000068807 17201750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz880) Bool.false 56587765202795681021952 18889465931478580854784 1000000000550456 137614000000000000000 3372893643545847 1125899906842624 125000000068807 17201750000000000000 (BSN.log_rat_reduce_isNear 20 1 4 40 32 116991 524288 24973259072661432 36028797018963968 137614 1000000000000000 rfl rfl rfl rfl (ep373 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep375 := nat_lit 6583481460047660995574288991419007881830481071314853486504547609514395164115200

noncomputable def ep376 := nat_lit 10445506827148701001563793844570969275540336656995279911763678668964204544256

noncomputable def ep377 := nat_lit 17225539670023728520120605977968096216443242260760909630511912068978426241515776

noncomputable def ep378 := BSN.sin_dyadic_bound_f 3179553886 2147483648 3 2 1048576 275497 ep375 ep97 ep376 ep377 ep100 ep376 1044313 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3179553886) qz268 0 2 ep375 ep97 ep376 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3179553886) qz269 0 2 ep377 ep100 ep376 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz881 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 349090475) qz277)

noncomputable def ep379 := @Enclosure.Real.IsNear.cos_image qz331 qz881 Bool.false 349090475 1048576 847 1048576 Bool.false 1044313 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz331 Bool.false 374833043500893522957 1125899906842624000 13891375007646590717 17201750000000000000000 349090475 1048576 847 1048576 (ep374 rfl) rfl) (Enclosure.sfrac_false_div 349090475 1048576) (BSN.cos_reduce3 qz881 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 223741214035649306296320) qz279) 226375608064910080 72057594037927936 Bool.false 1044313 1048576 52 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q3 349090475 1048576 226375608064910080 72057594037927936 52 223741214035649306296320 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1044313 1048576 223741214035649306296320 151115727451828646838272 3179553886 2147483648 275497 275228 (ep378 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep380 := nat_lit 3662132147505211086875300014719258142917174078133583172463310306916425848750336

noncomputable def ep381 := nat_lit 10965505428861335858622772456468632490200441561086758957566403563411349137162496

noncomputable def ep382 := BSN.cos_dyadic_bound_f 3179553886 2147483648 3 2 1048576 275497 ep380 ep104 ep376 ep381 ep106 ep376 94454 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3179553886) qz272 0 2 ep380 ep104 ep376 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3179553886) qz273 0 2 ep381 ep106 ep376 rfl rfl rfl rfl) rfl rfl

noncomputable def ep383 := @Enclosure.Real.IsNear.sin_image qz331 qz881 Bool.false 349090475 1048576 847 1048576 Bool.true 94454 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz331 Bool.false 374833043500893522957 1125899906842624000 13891375007646590717 17201750000000000000000 349090475 1048576 847 1048576 (ep374 rfl) rfl) (Enclosure.sfrac_false_div 349090475 1048576) (BSN.sin_reduce3 qz881 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 223741214035649306296320) qz279) 226375608064910080 72057594037927936 Bool.false 94454 1048576 52 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q3 349090475 1048576 226375608064910080 72057594037927936 52 223741214035649306296320 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 94454 1048576 223741214035649306296320 151115727451828646838272 3179553886 2147483648 275497 275228 (ep382 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz585 := (@Enclosure.Real.IsNear.recentre' qz330 Bool.false 234469 1048576 1 1048576 234469 1048576 1 1048576 (ep372 rfl rfl) rfl)

noncomputable def ep384 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz330 (Real.cos qz331)) (@HMul.hMul Real Real Real qz0 qz330 (@Neg.neg Real Real.instNeg (Real.sin qz331))) Bool.false 244859024797 1099511627776 13859587016581 75654096572383232 Bool.false 11073267463 549755813888 862139379273 4728381035773952 (@Enclosure.Real.IsNear.mulLit_ff qz330 (Real.cos qz331) 234469 1048576 1 1048576 1044313 1048576 58803817 72149368832 244859024797 1099511627776 13859587016581 75654096572383232 qz585 (@Enclosure.Real.IsNear.recentre' (Real.cos qz331) Bool.false 1044313 1048576 117607634 144298737664 1044313 1048576 58803817 72149368832 (ep379 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz330 (@Neg.neg Real Real.instNeg (Real.sin qz331)) 234469 1048576 1 1048576 47227 524288 58803817 72149368832 11073267463 549755813888 862139379273 4728381035773952 qz585 (@Enclosure.Real.IsNear.neg (Real.sin qz331) Bool.true 47227 524288 58803817 72149368832 (@Enclosure.Real.IsNear.recentre' (Real.sin qz331) Bool.true 94454 1048576 117607634 144298737664 47227 524288 58803817 72149368832 (ep383 rfl rfl) rfl)) rfl)

noncomputable def ep385 := @ep325 244859024797 1099511627776 13859587016581 75654096572383232 Bool.false 11073267463 549755813888 862139379273 4728381035773952 Bool.false 121230457358978671181824 220516917323 1099511627776 407929598252357 75654096572383232 Bool.true 136124839510511087255552 247609640629 1099511627776 407780344309781 75654096572383232 (ep326 (BSN.head_sum_c_succ qz14 19 20 rfl rfl) (ep370 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep371 ep384) rfl rfl

noncomputable abbrev qz882 := (@Nat.cast Real Real.instNatCast 21)

noncomputable abbrev qz333 := (@Inv.inv Real Real.instInv (Real.sqrt qz882))

noncomputable abbrev qz334 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 21 1)))

noncomputable def ep386 := @Enclosure.Complex.IsNear.of_eq qz867 (Complex.mk (@HMul.hMul Real Real Real qz0 qz333 (Real.cos qz334)) (@HMul.hMul Real Real Real qz0 qz333 (@Neg.neg Real Real.instNeg (Real.sin qz334)))) Bool.false 69654830607 549755813888 6769635987131 37827048286191616 Bool.false 24418427279 137438953472 3393243445119 18913524143095808 (BSN.cpow_neg_s_mk qz11 111131 1000 21 (@Eq.refl Real qz11) rfl)

noncomputable abbrev qz883 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 21) qz267)

noncomputable def ep387 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz882) 4805179 1048576 1 1048576 114408 114410 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz882) (Real.sqrt qz883) Bool.false 4805179 1048576 1 1048576 (BSN.sqrt_natCast_div_one 21) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz883) Bool.false 4805179 1048576 1 1048576 4805179 1048576 1 1048576 (BSN.sqrt_enclosure 21 1 2402589 2402590 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep388 := BSN.log_dyadic_bound 5 37 3 2 28112415 524288 137614 173000 1875 142571 42 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 5) (BSN.artanhQ 37) 0 2 173000 28112415 1875 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz335 := (Real.log (Enclosure.sfrac Bool.false 21 1))

noncomputable def ep389 := @Enclosure.Real.IsNear.mulLit_ff qz11 qz335 111131 1000 0 1 3427826275261687 1125899906842624 125000000068807 17201750000000000000 380937761796106537997 1125899906842624000 13891375007646590717 17201750000000000000000 qz271 (BSN.isNear_log_sfrac 21 1 3427826275261687 1125899906842624 125000000068807 17201750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz883) Bool.false 57509381830540779323392 18889465931478580854784 1000000000550456 137614000000000000000 3427826275261687 1125899906842624 125000000068807 17201750000000000000 (BSN.log_rat_reduce_isNear 21 1 4 42 32 142571 524288 24973259072661432 36028797018963968 137614 1000000000000000 rfl rfl rfl rfl (ep388 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep390 := nat_lit 3132230221173861028387372311052071601

noncomputable def ep391 := BSN.sin_dyadic_bound_f 1330342357 2147483648 2 1 1048576 275497 ep390 ep178 ep390 ep390 ep179 ep390 608823 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1330342357) qz268 0 1 ep390 ep178 ep390 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1330342357) qz269 0 1 ep390 ep179 ep390 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz884 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 354775937) qz277)

noncomputable def ep392 := @Enclosure.Real.IsNear.cos_image qz334 qz884 Bool.false 354775937 1048576 847 1048576 Bool.false 608823 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz334 Bool.false 380937761796106537997 1125899906842624000 13891375007646590717 17201750000000000000000 354775937 1048576 847 1048576 (ep389 rfl) rfl) (Enclosure.sfrac_false_div 354775937 1048576) (BSN.cos_reduce3 qz884 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 93614521054696375844864) qz279) 226375608064910080 72057594037927936 Bool.false 608823 1048576 53 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q3 354775937 1048576 226375608064910080 72057594037927936 53 93614521054696375844864 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 608823 1048576 93614521054696375844864 151115727451828646838272 1330342357 2147483648 275497 275228 (ep391 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep393 := BSN.cos_dyadic_bound_f 1330342357 2147483648 2 1 1048576 275497 ep390 ep118 ep390 ep390 ep119 ep390 853724 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1330342357) qz272 0 1 ep390 ep118 ep390 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1330342357) qz273 0 1 ep390 ep119 ep390 rfl rfl rfl rfl) rfl rfl

noncomputable def ep394 := @Enclosure.Real.IsNear.sin_image qz334 qz884 Bool.false 354775937 1048576 847 1048576 Bool.true 853724 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz334 Bool.false 380937761796106537997 1125899906842624000 13891375007646590717 17201750000000000000000 354775937 1048576 847 1048576 (ep389 rfl) rfl) (Enclosure.sfrac_false_div 354775937 1048576) (BSN.sin_reduce3 qz884 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 93614521054696375844864) qz279) 226375608064910080 72057594037927936 Bool.false 853724 1048576 53 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q3 354775937 1048576 226375608064910080 72057594037927936 53 93614521054696375844864 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 853724 1048576 93614521054696375844864 151115727451828646838272 1330342357 2147483648 275497 275228 (ep393 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz586 := (@Enclosure.Real.IsNear.recentre' qz333 Bool.false 228818 1048576 2 1048576 114409 524288 1 524288 (ep387 rfl rfl) rfl)

noncomputable def ep395 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz333 (Real.cos qz334)) (@HMul.hMul Real Real Real qz0 qz333 (@Neg.neg Real Real.instNeg (Real.sin qz334))) Bool.false 69654830607 549755813888 6769635987131 37827048286191616 Bool.false 24418427279 137438953472 3393243445119 18913524143095808 (@Enclosure.Real.IsNear.mulLit_ff qz333 (Real.cos qz334) 114409 524288 1 524288 608823 1048576 58803817 72149368832 69654830607 549755813888 6769635987131 37827048286191616 qz586 (@Enclosure.Real.IsNear.recentre' (Real.cos qz334) Bool.false 608823 1048576 117607634 144298737664 608823 1048576 58803817 72149368832 (ep392 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz333 (@Neg.neg Real Real.instNeg (Real.sin qz334)) 114409 524288 1 524288 213431 262144 58803817 72149368832 24418427279 137438953472 3393243445119 18913524143095808 qz586 (@Enclosure.Real.IsNear.neg (Real.sin qz334) Bool.true 213431 262144 58803817 72149368832 (@Enclosure.Real.IsNear.recentre' (Real.sin qz334) Bool.true 853724 1048576 117607634 144298737664 213431 262144 58803817 72149368832 (ep394 rfl rfl) rfl)) rfl)

noncomputable def ep396 := @ep323 69654830607 549755813888 6769635987131 37827048286191616 Bool.false 24418427279 137438953472 3393243445119 18913524143095808 Bool.false 197816753542142787321856 359826578537 1099511627776 421468870226619 75654096572383232 Bool.true 7182865152364599312384 52262222397 1099511627776 421353318090257 75654096572383232 (ep324 (BSN.head_sum_c_succ qz14 20 21 rfl rfl) (ep385 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep386 ep395) rfl rfl

noncomputable abbrev qz885 := (@Nat.cast Real Real.instNatCast 22)

noncomputable abbrev qz336 := (@Inv.inv Real Real.instInv (Real.sqrt qz885))

noncomputable abbrev qz337 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 22 1)))

noncomputable def ep397 := @Enclosure.Complex.IsNear.of_eq qz866 (Complex.mk (@HMul.hMul Real Real Real qz0 qz336 (Real.cos qz337)) (@HMul.hMul Real Real Real qz0 qz336 (@Neg.neg Real Real.instNeg (Real.sin qz337)))) Bool.true 111119230407 1099511627776 13195646664349 75654096572383232 Bool.false 206406377631 1099511627776 13224974409573 75654096572383232 (BSN.cpow_neg_s_mk qz11 111131 1000 22 (@Eq.refl Real qz11) rfl)

noncomputable abbrev qz886 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 22) qz267)

noncomputable def ep398 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz885) 4918257 1048576 1 1048576 111778 111779 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz885) (Real.sqrt qz886) Bool.false 4918257 1048576 1 1048576 (BSN.sqrt_natCast_div_one 22) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz886) Bool.false 4918257 1048576 1 1048576 4918257 1048576 1 1048576 (BSN.sqrt_enclosure 22 1 2459128 2459129 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep399 := BSN.log_dyadic_bound 6 38 4 3 316148320320 524288 137614 2667271104 699840 166961 44 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 6) (BSN.artanhQ 38) 0 3 2667271104 316148320320 699840 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz338 := (Real.log (Enclosure.sfrac Bool.false 22 1))

noncomputable def ep400 := @Enclosure.Real.IsNear.mulLit_ff qz11 qz338 111131 1000 0 1 3480203401436407 1125899906842624 125000000068807 17201750000000000000 386758484205029346317 1125899906842624000 13891375007646590717 17201750000000000000000 qz271 (BSN.isNear_log_sfrac 22 1 3480203401436407 1125899906842624 125000000068807 17201750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz886) Bool.false 58388124189833310502912 18889465931478580854784 1000000000550456 137614000000000000000 3480203401436407 1125899906842624 125000000068807 17201750000000000000 (BSN.log_rat_reduce_isNear 22 1 4 44 32 166961 524288 24973259072661432 36028797018963968 137614 1000000000000000 rfl rfl rfl rfl (ep399 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep401 := nat_lit 1022966771085343954266137219683799871562007278132354101252854992615626620357761

noncomputable def ep402 := nat_lit 818408979938159598297258672503602010875085612904823536135507971893392919681

noncomputable def ep403 := nat_lit 3067263495296155543601817141706392410664271663171252656686293961903093075233921

noncomputable def ep404 := BSN.cos_dyadic_bound_f 2312710639 2147483648 3 2 1048576 275497 ep401 ep104 ep402 ep403 ep106 ep402 497051 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2312710639) qz272 0 2 ep401 ep104 ep402 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2312710639) qz273 0 2 ep403 ep106 ep402 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz887 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 360196907) qz277)

noncomputable def ep405 := @Enclosure.Real.IsNear.cos_image qz337 qz887 Bool.false 360196907 1048576 53 65536 Bool.true 497051 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz337 Bool.false 386758484205029346317 1125899906842624000 13891375007646590717 17201750000000000000000 360196907 1048576 53 65536 (ep400 rfl) rfl) (Enclosure.sfrac_false_div 360196907 1048576) (BSN.cos_reduce2 qz887 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 162742543351455326142464) qz279) 226375608064910080 72057594037927936 Bool.false 497051 1048576 54 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q2 360196907 1048576 226375608064910080 72057594037927936 54 162742543351455326142464 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 497051 1048576 162742543351455326142464 151115727451828646838272 2312710639 2147483648 275497 275228 (ep404 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep406 := nat_lit 1840685460769668590000409188492836887202913032147913523426230580330613202308225

noncomputable def ep407 := nat_lit 4819517830333994048746685646297186015609069707490308561343527364149492893699201

noncomputable def ep408 := BSN.sin_dyadic_bound_f 2312710639 2147483648 3 2 1048576 275497 ep406 ep97 ep402 ep407 ep100 ep402 923283 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2312710639) qz268 0 2 ep406 ep97 ep402 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2312710639) qz269 0 2 ep407 ep100 ep402 rfl rfl rfl rfl) rfl rfl

noncomputable def ep409 := @Enclosure.Real.IsNear.sin_image qz337 qz887 Bool.false 360196907 1048576 53 65536 Bool.true 923283 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz337 Bool.false 386758484205029346317 1125899906842624000 13891375007646590717 17201750000000000000000 360196907 1048576 53 65536 (ep400 rfl) rfl) (Enclosure.sfrac_false_div 360196907 1048576) (BSN.sin_reduce2 qz887 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 162742543351455326142464) qz279) 226375608064910080 72057594037927936 Bool.false 923283 1048576 54 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q2 360196907 1048576 226375608064910080 72057594037927936 54 162742543351455326142464 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 923283 1048576 162742543351455326142464 151115727451828646838272 2312710639 2147483648 275497 275228 (ep408 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz587 := (@Enclosure.Real.IsNear.recentre' qz336 Bool.false 223557 1048576 1 1048576 223557 1048576 1 1048576 (ep398 rfl rfl) rfl)

noncomputable def ep410 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz336 (Real.cos qz337)) (@HMul.hMul Real Real Real qz0 qz336 (@Neg.neg Real Real.instNeg (Real.sin qz337))) Bool.true 111119230407 1099511627776 13195646664349 75654096572383232 Bool.false 206406377631 1099511627776 13224974409573 75654096572383232 (@Enclosure.Real.IsNear.mulLit_ft qz336 (Real.cos qz337) 223557 1048576 1 1048576 497051 1048576 3679539 4509335552 111119230407 1099511627776 13195646664349 75654096572383232 qz587 (@Enclosure.Real.IsNear.recentre' (Real.cos qz337) Bool.true 497051 1048576 7359078 9018671104 497051 1048576 3679539 4509335552 (ep405 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz336 (@Neg.neg Real Real.instNeg (Real.sin qz337)) 223557 1048576 1 1048576 923283 1048576 3679539 4509335552 206406377631 1099511627776 13224974409573 75654096572383232 qz587 (@Enclosure.Real.IsNear.neg (Real.sin qz337) Bool.true 923283 1048576 3679539 4509335552 (@Enclosure.Real.IsNear.recentre' (Real.sin qz337) Bool.true 923283 1048576 7359078 9018671104 923283 1048576 3679539 4509335552 (ep409 rfl rfl) rfl)) rfl)

noncomputable def ep411 := @ep321 111119230407 1099511627776 13195646664349 75654096572383232 Bool.false 206406377631 1099511627776 13224974409573 75654096572383232 Bool.false 273456621182268609658880 124353674065 549755813888 54333064611371 9456762071547904 Bool.false 169483291033491770179584 77072077617 549755813888 217289146249915 37827048286191616 (ep322 (BSN.head_sum_c_succ qz14 21 22 rfl rfl) (ep396 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep397 ep410) rfl rfl

noncomputable abbrev qz888 := (@Nat.cast Real Real.instNatCast 23)

noncomputable abbrev qz339 := (@Inv.inv Real Real.instInv (Real.sqrt qz888))

noncomputable abbrev qz340 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 23 1)))

noncomputable def ep412 := @Enclosure.Complex.IsNear.of_eq qz865 (Complex.mk (@HMul.hMul Real Real Real qz0 qz339 (Real.cos qz340)) (@HMul.hMul Real Real Real qz0 qz339 (@Neg.neg Real Real.instNeg (Real.sin qz340)))) Bool.true 110588536185 549755813888 6463353118639 37827048286191616 Bool.true 15088334787 274877906944 804755935825 4728381035773952 (BSN.cpow_neg_s_mk qz11 111131 1000 23 (@Eq.refl Real qz11) rfl)

noncomputable abbrev qz889 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 23) qz267)

noncomputable def ep413 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz888) 5028793 1048576 1 1048576 109321 109322 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz888) (Real.sqrt qz889) Bool.false 5028793 1048576 1 1048576 (BSN.sqrt_natCast_div_one 23) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz889) Bool.false 5028793 1048576 1 1048576 5028793 1048576 1 1048576 (BSN.sqrt_enclosure 23 1 2514396 2514397 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep414 := BSN.log_dyadic_bound 7 39 4 3 369468094905 524288 137614 4046006391 1764735 190266 46 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 7) (BSN.artanhQ 39) 0 3 4046006391 369468094905 1764735 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz341 := (Real.log (Enclosure.sfrac Bool.false 23 1))

noncomputable def ep415 := @Enclosure.Real.IsNear.mulLit_ff qz11 qz341 111131 1000 0 1 3530250507853047 1125899906842624 125000000068807 17201750000000000000 392320269188216966157 1125899906842624000 13891375007646590717 17201750000000000000000 qz271 (BSN.isNear_log_sfrac 23 1 3530250507853047 1125899906842624 125000000068807 17201750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz889) Bool.false 59227775304360265777152 18889465931478580854784 1000000000550456 137614000000000000000 3530250507853047 1125899906842624 125000000068807 17201750000000000000 (BSN.log_rat_reduce_isNear 23 1 4 46 32 190266 524288 24973259072661432 36028797018963968 137614 1000000000000000 rfl rfl rfl rfl (ep414 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep416 := nat_lit 3963606406600679076951072710892957443773104456991145804466405600300302354425665

noncomputable def ep417 := nat_lit 3790944235004539671052474119662031971490013772721260646755112393939472688961

noncomputable def ep418 := nat_lit 10374736202811771184928248332335435729547146888868595065888696866434413686761281

noncomputable def ep419 := BSN.sin_dyadic_bound_f 2801195529 2147483648 3 2 1048576 275497 ep416 ep97 ep417 ep418 ep100 ep417 1011590 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2801195529) qz268 0 2 ep416 ep97 ep417 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2801195529) qz269 0 2 ep418 ep100 ep417 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz890 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 365376723) qz277)

noncomputable def ep420 := @Enclosure.Real.IsNear.cos_image qz340 qz890 Bool.false 365376723 1048576 847 1048576 Bool.true 1011590 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz340 Bool.false 392320269188216966157 1125899906842624000 13891375007646590717 17201750000000000000000 365376723 1048576 847 1048576 (ep415 rfl) rfl) (Enclosure.sfrac_false_div 365376723 1048576) (BSN.cos_reduce1 qz890 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 197116611582969329483776) qz279) 226375608064910080 72057594037927936 Bool.false 1011590 1048576 55 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q1 365376723 1048576 226375608064910080 72057594037927936 55 197116611582969329483776 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1011590 1048576 197116611582969329483776 151115727451828646838272 2801195529 2147483648 275497 275228 (ep419 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep421 := nat_lit 2203688423327045949271063716771492816305720260005179340546560939008585518098241

noncomputable def ep422 := nat_lit 6603483381511128768471086202075154384974180752470095500346172592237877608916801

noncomputable def ep423 := BSN.cos_dyadic_bound_f 2801195529 2147483648 3 2 1048576 275497 ep421 ep104 ep417 ep422 ep106 ep417 276036 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2801195529) qz272 0 2 ep421 ep104 ep417 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2801195529) qz273 0 2 ep422 ep106 ep417 rfl rfl rfl rfl) rfl rfl

noncomputable def ep424 := @Enclosure.Real.IsNear.sin_image qz340 qz890 Bool.false 365376723 1048576 847 1048576 Bool.false 276036 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz340 Bool.false 392320269188216966157 1125899906842624000 13891375007646590717 17201750000000000000000 365376723 1048576 847 1048576 (ep415 rfl) rfl) (Enclosure.sfrac_false_div 365376723 1048576) (BSN.sin_reduce1 qz890 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 197116611582969329483776) qz279) 226375608064910080 72057594037927936 Bool.false 276036 1048576 55 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q1 365376723 1048576 226375608064910080 72057594037927936 55 197116611582969329483776 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 276036 1048576 197116611582969329483776 151115727451828646838272 2801195529 2147483648 275497 275228 (ep423 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz588 := (@Enclosure.Real.IsNear.recentre' qz339 Bool.false 218643 1048576 1 1048576 218643 1048576 1 1048576 (ep413 rfl rfl) rfl)

noncomputable def ep425 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz339 (Real.cos qz340)) (@HMul.hMul Real Real Real qz0 qz339 (@Neg.neg Real Real.instNeg (Real.sin qz340))) Bool.true 110588536185 549755813888 6463353118639 37827048286191616 Bool.true 15088334787 274877906944 804755935825 4728381035773952 (@Enclosure.Real.IsNear.mulLit_ft qz339 (Real.cos qz340) 218643 1048576 1 1048576 505795 524288 58803817 72149368832 110588536185 549755813888 6463353118639 37827048286191616 qz588 (@Enclosure.Real.IsNear.recentre' (Real.cos qz340) Bool.true 1011590 1048576 117607634 144298737664 505795 524288 58803817 72149368832 (ep420 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz339 (@Neg.neg Real Real.instNeg (Real.sin qz340)) 218643 1048576 1 1048576 69009 262144 58803817 72149368832 15088334787 274877906944 804755935825 4728381035773952 qz588 (@Enclosure.Real.IsNear.neg (Real.sin qz340) Bool.false 69009 262144 58803817 72149368832 (@Enclosure.Real.IsNear.recentre' (Real.sin qz340) Bool.false 276036 1048576 117607634 144298737664 69009 262144 58803817 72149368832 (ep424 rfl rfl) rfl)) rfl)

noncomputable def ep426 := @ep319 110588536185 549755813888 6463353118639 37827048286191616 Bool.true 15088334787 274877906944 804755935825 4728381035773952 Bool.false 7567464578499938877440 1720642235 68719476736 223795611564123 37827048286191616 Bool.false 12890511608144663150592 46895408043 549755813888 223727193736515 37827048286191616 (ep320 (BSN.head_sum_c_succ qz14 22 23 rfl rfl) (ep411 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep412 ep425) rfl rfl

noncomputable abbrev qz891 := (@Nat.cast Real Real.instNatCast 24)

noncomputable abbrev qz342 := (@Inv.inv Real Real.instInv (Real.sqrt qz891))

noncomputable abbrev qz343 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 24 1)))

noncomputable def ep427 := @Enclosure.Complex.IsNear.of_eq qz864 (Complex.mk (@HMul.hMul Real Real Real qz0 qz342 (Real.cos qz343)) (@HMul.hMul Real Real Real qz0 qz342 (@Neg.neg Real Real.instNeg (Real.sin qz343)))) Bool.false 55304038937 1099511627776 12618875000041 75654096572383232 Bool.true 108757710719 549755813888 6335510502127 37827048286191616 (BSN.cpow_neg_s_mk qz11 111131 1000 24 (@Eq.refl Real qz11) rfl)

noncomputable abbrev qz892 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 24) qz267)

noncomputable def ep428 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz891) 5136953 1048576 1 1048576 107019 107020 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz891) (Real.sqrt qz892) Bool.false 5136953 1048576 1 1048576 (BSN.sqrt_natCast_div_one 24) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz892) Bool.false 5136953 1048576 1 1048576 5136953 1048576 1 1048576 (BSN.sqrt_enclosure 24 1 2568476 2568477 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep429 := BSN.log_dyadic_bound 8 40 4 3 430080000000 524288 137614 5875957760 3932160 212580 48 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 8) (BSN.artanhQ 40) 0 3 5875957760 430080000000 3932160 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz344 := (Real.log (Enclosure.sfrac Bool.false 24 1))

noncomputable def ep430 := @Enclosure.Real.IsNear.mulLit_ff qz11 qz344 111131 1000 0 1 3578169457974519 1125899906842624 125000000068807 17201750000000000000 397645550034166270989 1125899906842624000 13891375007646590717 17201750000000000000000 qz271 (BSN.isNear_log_sfrac 24 1 3578169457974519 1125899906842624 125000000068807 17201750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz892) Bool.false 60031721881041427759104 18889465931478580854784 1000000000550456 137614000000000000000 3578169457974519 1125899906842624 125000000068807 17201750000000000000 (BSN.log_rat_reduce_isNear 24 1 4 48 32 212580 524288 24973259072661432 36028797018963968 137614 1000000000000000 rfl rfl rfl rfl (ep429 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep431 := nat_lit 2323935597907284292729952322234234909976220161770674537062791094970960134308096

noncomputable def ep432 := nat_lit 4215157536703191603547038371841829575321888341354432328264964353896059535616

noncomputable def ep433 := nat_lit 6963376478648446494982762889959021070778016708629314746531843356205088283853056

noncomputable def ep434 := BSN.cos_dyadic_bound_f 2838583842 2147483648 3 2 1048576 275497 ep431 ep104 ep432 ep433 ep106 ep432 258383 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2838583842) qz272 0 2 ep431 ep104 ep432 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2838583842) qz273 0 2 ep433 ep106 ep432 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz893 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 370336277) qz277)

noncomputable def ep435 := @Enclosure.Real.IsNear.cos_image qz343 qz893 Bool.false 370336277 1048576 53 65536 Bool.false 258383 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz343 Bool.false 397645550034166270989 1125899906842624000 13891375007646590717 17201750000000000000000 370336277 1048576 53 65536 (ep430 rfl) rfl) (Enclosure.sfrac_false_div 370336277 1048576) (BSN.cos_reduce0 qz893 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 199747580258519166746624) qz279) 226375608064910080 72057594037927936 Bool.false 258383 1048576 56 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q0 370336277 1048576 226375608064910080 72057594037927936 56 199747580258519166746624 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 258383 1048576 199747580258519166746624 151115727451828646838272 2838583842 2147483648 275497 275228 (ep434 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep436 := nat_lit 4179711950203749173631076549324149374296938780514130620850411999464611394126080

noncomputable def ep437 := nat_lit 10940040090712299811199457662294552065750985177365292068933888151548626697748736

noncomputable def ep438 := BSN.sin_dyadic_bound_f 2838583842 2147483648 3 2 1048576 275497 ep436 ep97 ep432 ep437 ep100 ep432 1016242 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2838583842) qz268 0 2 ep436 ep97 ep432 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2838583842) qz269 0 2 ep437 ep100 ep432 rfl rfl rfl rfl) rfl rfl

noncomputable def ep439 := @Enclosure.Real.IsNear.sin_image qz343 qz893 Bool.false 370336277 1048576 53 65536 Bool.false 1016242 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz343 Bool.false 397645550034166270989 1125899906842624000 13891375007646590717 17201750000000000000000 370336277 1048576 53 65536 (ep430 rfl) rfl) (Enclosure.sfrac_false_div 370336277 1048576) (BSN.sin_reduce0 qz893 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 199747580258519166746624) qz279) 226375608064910080 72057594037927936 Bool.false 1016242 1048576 56 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q0 370336277 1048576 226375608064910080 72057594037927936 56 199747580258519166746624 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1016242 1048576 199747580258519166746624 151115727451828646838272 2838583842 2147483648 275497 275228 (ep438 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz589 := (@Enclosure.Real.IsNear.recentre' qz342 Bool.false 214039 1048576 1 1048576 214039 1048576 1 1048576 (ep428 rfl rfl) rfl)

noncomputable def ep440 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz342 (Real.cos qz343)) (@HMul.hMul Real Real Real qz0 qz342 (@Neg.neg Real Real.instNeg (Real.sin qz343))) Bool.false 55304038937 1099511627776 12618875000041 75654096572383232 Bool.true 108757710719 549755813888 6335510502127 37827048286191616 (@Enclosure.Real.IsNear.mulLit_ff qz342 (Real.cos qz343) 214039 1048576 1 1048576 258383 1048576 3679539 4509335552 55304038937 1099511627776 12618875000041 75654096572383232 qz589 (@Enclosure.Real.IsNear.recentre' (Real.cos qz343) Bool.false 258383 1048576 7359078 9018671104 258383 1048576 3679539 4509335552 (ep435 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz342 (@Neg.neg Real Real.instNeg (Real.sin qz343)) 214039 1048576 1 1048576 508121 524288 3679539 4509335552 108757710719 549755813888 6335510502127 37827048286191616 qz589 (@Enclosure.Real.IsNear.neg (Real.sin qz343) Bool.false 508121 524288 3679539 4509335552 (@Enclosure.Real.IsNear.recentre' (Real.sin qz343) Bool.false 1016242 1048576 7359078 9018671104 508121 524288 3679539 4509335552 (ep439 rfl rfl) rfl)) rfl)

noncomputable def ep441 := @ep317 55304038937 1099511627776 12618875000041 75654096572383232 Bool.true 108757710719 549755813888 6335510502127 37827048286191616 Bool.false 5692330761762994388992 82834314697 1099511627776 460210098128287 75654096572383232 Bool.true 34009160556630180364288 15465575669 137438953472 115031352119321 18913524143095808 (ep318 (BSN.head_sum_c_succ qz14 23 24 rfl rfl) (ep426 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep427 ep440) rfl rfl

theorem EMRow35.d9 : Enclosure.Complex.IsNear (BSN.headSumC qz14 25) Bool.false 82834314697 1099511627776 460210098128287 75654096572383232 Bool.true 15465575669 137438953472 115031352119321 18913524143095808 := ep316 (BSN.head_sum_c_succ qz14 24 25 rfl rfl) (ep441 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

theorem EMRow35.d10 : @Eq Nat (BSN.factNat (Nat.mul 2 1)) 2 := @Eq.refl Nat 2

theorem EMRow35.d11 : @Eq Nat (Nat.pow 28 1) 28 := @Eq.refl Nat 28

theorem EMRow35.d12 : @Eq Nat (BSN.factNat (Nat.mul 2 2)) 24 := @Eq.refl Nat 24

noncomputable abbrev qz20 := (@HAdd.hAdd Complex Complex Complex qz262 qz261 qz553)

noncomputable def ep442 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz3 (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 2)) qz20) Bool.true 111147142449 2000000 0 1 Bool.true 1371839866611091 1000000000 0 1

noncomputable def ep443 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.re qz20)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.im qz20)) 12349349161 400000 0 1 12350099161 500000 0 1

noncomputable def ep444 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.re qz20) 12349349161 1000000 0 1 5 2 0 1 12349349161 400000

noncomputable abbrev qz590 := (@Nat.cast Complex Complex.instNatCast 1)

noncomputable abbrev qz21 := (@HAdd.hAdd Complex Complex Complex qz262 qz261 qz590)

noncomputable def ep445 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz3 (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1)) qz21) Bool.true 12349349161 1000000 0 1 Bool.false 111131 500 0 1

noncomputable def ep446 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.re qz21)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.im qz21)) 3 4 0 1 12350099161 1000000 0 1

noncomputable def ep447 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.re qz21) 1 2 0 1 3 2 0 1 3 4

noncomputable def ep448 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1)) qz14 Bool.false 1 2 0 1 Bool.false 111131 1000 0 1 (BSN.ascPochhammer_one_eval qz14)

noncomputable abbrev qz345 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz346 := (Enclosure.Real.IsNear.const Bool.false 1 2)

noncomputable def ep449 := ep448 (@Enclosure.Complex.IsNear.of_eq qz14 (Complex.mk qz345 qz11) Bool.false 1 2 0 1 Bool.false 111131 1000 0 1 (BSN.s_crit_mk qz11 Bool.false 111131 1000 (@Eq.refl Real qz11)) (@Enclosure.Complex.IsNear.mk qz345 qz11 Bool.false 1 2 0 1 Bool.false 111131 1000 0 1 qz346 qz271))

noncomputable def ep450 := @ep447 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 111131 1000 0 1 ep449)

noncomputable def ep451 := @Enclosure.Complex.IsNear.of_eq qz21 (Complex.mk (Enclosure.sfrac Bool.false 3 2) qz11) Bool.false 3 2 0 1 Bool.false 111131 1000 0 1 (BSN.s_add_nat_mk qz11 Bool.false 111131 1000 1 (@Eq.refl Real qz11))

noncomputable abbrev qz591 := (ep451 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz11 Bool.false 3 2 0 1 Bool.false 111131 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz271))

noncomputable def ep452 := ep450 (@Enclosure.Complex.IsNear.re_isNear qz21 Bool.false 3 2 0 1 Bool.false 111131 1000 0 1 qz591)

noncomputable def ep453 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.im qz21) 111131 1000 0 1 111131 1000 0 1 12350099161 1000000

noncomputable def ep454 := @ep453 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 111131 1000 0 1 ep449)

noncomputable def ep455 := ep454 (@Enclosure.Complex.IsNear.im_isNear qz21 Bool.false 3 2 0 1 Bool.false 111131 1000 0 1 qz591)

noncomputable def ep456 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1)) qz21 Bool.true 12349349161 1000000 0 1 Bool.false 111131 500 0 1 (@ep446 49397396644 12349349161 1000000 0 1 (ep452 rfl) (ep455 rfl) rfl rfl)

noncomputable def ep457 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.im qz21)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.re qz21)) 111131 2000 0 1 333393 2000 0 1

noncomputable def ep458 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.im qz21) 1 2 0 1 111131 1000 0 1 111131 2000

noncomputable def ep459 := @ep458 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 111131 1000 0 1 ep449)

noncomputable def ep460 := ep459 (@Enclosure.Complex.IsNear.im_isNear qz21 Bool.false 3 2 0 1 Bool.false 111131 1000 0 1 qz591)

noncomputable def ep461 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.re qz21) 111131 1000 0 1 3 2 0 1 333393 2000

noncomputable def ep462 := @ep461 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 111131 1000 0 1 ep449)

noncomputable def ep463 := ep462 (@Enclosure.Complex.IsNear.re_isNear qz21 Bool.false 3 2 0 1 Bool.false 111131 1000 0 1 qz591)

noncomputable abbrev qz592 := (ep445 (BSN.ascPochhammer_succ_eval_c 1 2 qz14 rfl) (ep456 (@ep457 889048000 111131 500 0 1 (ep460 rfl) (ep463 rfl) rfl rfl)))

noncomputable def ep464 := @ep444 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 12349349161 1000000 0 1 Bool.false 111131 500 0 1 qz592)

noncomputable def ep465 := @Enclosure.Complex.IsNear.of_eq qz20 (Complex.mk (Enclosure.sfrac Bool.false 5 2) qz11) Bool.false 5 2 0 1 Bool.false 111131 1000 0 1 (BSN.s_add_nat_mk qz11 Bool.false 111131 1000 2 (@Eq.refl Real qz11))

noncomputable abbrev qz593 := (ep465 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz11 Bool.false 5 2 0 1 Bool.false 111131 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz271))

noncomputable def ep466 := ep464 (@Enclosure.Complex.IsNear.re_isNear qz20 Bool.false 5 2 0 1 Bool.false 111131 1000 0 1 qz593)

noncomputable def ep467 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.im qz20) 111131 500 0 1 111131 1000 0 1 12350099161 500000

noncomputable def ep468 := @ep467 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 12349349161 1000000 0 1 Bool.false 111131 500 0 1 qz592)

noncomputable def ep469 := ep468 (@Enclosure.Complex.IsNear.im_isNear qz20 Bool.false 5 2 0 1 Bool.false 111131 1000 0 1 qz593)

noncomputable def ep470 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 2)) qz20 Bool.true 111147142449 2000000 0 1 Bool.true 1371839866611091 1000000000 0 1 (@ep443 11114714244900000 111147142449 2000000 0 1 (ep466 rfl) (ep469 rfl) rfl rfl)

noncomputable def ep471 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.im qz20)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.re qz20)) 1372395521611091 1000000000 0 1 111131 200 0 1

noncomputable def ep472 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.im qz20) 12349349161 1000000 0 1 111131 1000 0 1 1372395521611091 1000000000

noncomputable def ep473 := @ep472 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 12349349161 1000000 0 1 Bool.false 111131 500 0 1 qz592)

noncomputable def ep474 := ep473 (@Enclosure.Complex.IsNear.im_isNear qz20 Bool.false 5 2 0 1 Bool.false 111131 1000 0 1 qz593)

noncomputable def ep475 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.re qz20) 111131 500 0 1 5 2 0 1 111131 200

noncomputable def ep476 := @ep475 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 12349349161 1000000 0 1 Bool.false 111131 500 0 1 qz592)

noncomputable def ep477 := ep476 (@Enclosure.Complex.IsNear.re_isNear qz20 Bool.false 5 2 0 1 Bool.false 111131 1000 0 1 qz593)

noncomputable abbrev qz594 := (ep470 (@ep471 274367973322218200 1371839866611091 1000000000 0 1 (ep474 rfl) (ep477 rfl) rfl rfl))

theorem EMRow35.d13 : Enclosure.Complex.IsNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 111147142449 2000000 0 1 Bool.true 1371839866611091 1000000000 0 1 := ep442 (BSN.ascPochhammer_succ_eval_c 2 3 qz14 rfl) qz594

theorem EMRow35.d14 : @Eq Nat (Nat.pow 28 3) 21952 := @Eq.refl Nat 21952

noncomputable def ep478 := nat_lit 4612956288838774603924712845029832096893203

noncomputable def ep479 := nat_lit 32150484804966058555082605194117120000000000

noncomputable def ep480 := nat_lit 2389595609286275389817458371227189240764513279642019

noncomputable def ep481 := nat_lit 355164506007631690901783773486962193433886720000000000

noncomputable abbrev qz595 := (@instHSub Complex Complex.instSub)

noncomputable abbrev qz22 := qz595

noncomputable abbrev qz23 := (Complex.Stirling.logGammaStirling 2 qz257)

noncomputable abbrev qz596 := (@HAdd.hAdd Complex Complex Complex qz812 qz813 (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I (@HDiv.hDiv Complex Complex Complex qz814 (↑(Enclosure.sfrac Bool.false 111131 1000)) (2 : Complex))))

noncomputable abbrev qz347 := qz596

noncomputable abbrev qz24 := qz347

noncomputable abbrev qz348 := (@HMul.hMul Real Real Real qz0 (@HDiv.hDiv Real Real Real qz1 qz11 (2 : Real)) (Real.log Real.pi))

noncomputable abbrev qz597 := (@instHSub Real Real.instSub)

noncomputable def ep482 := Complex.re (@HMul.hMul Complex Complex Complex qz3 (Complex.exp (@HMul.hMul Complex Complex Complex qz3 Complex.I ↑(@HSub.hSub Real Real Real qz597 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz23 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz24 (@Nat.cast Complex Complex.instNatCast j))))) qz348))) (zetaApproximant qz14 2 28))

noncomputable def ep483 := @Enclosure.Real.IsNear.of_eq ep482 (@HSub.hSub Real Real Real qz597 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz597 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz23 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz24 (@Nat.cast Complex Complex.instNatCast j))))) qz348)) (Complex.re (zetaApproximant qz14 2 28))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz597 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz23 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz24 (@Nat.cast Complex Complex.instNatCast j))))) qz348)) (Complex.im (zetaApproximant qz14 2 28))))

noncomputable def ep484 := nat_lit 61506854185825121913651161840195595796951

noncomputable def ep485 := @Enclosure.Real.IsNear.subLit_tt_n (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz597 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz23 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz24 (@Nat.cast Complex Complex.instNatCast j))))) qz348)) (Complex.re (zetaApproximant qz14 2 28))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz597 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz23 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz24 (@Nat.cast Complex Complex.instNatCast j))))) qz348)) (Complex.im (zetaApproximant qz14 2 28))) ep484

noncomputable def ep486 := nat_lit 428673130732880780734434735921561600000000

noncomputable def ep487 := nat_lit 146148960748268182201680720452406974871651738738079

noncomputable def ep488 := nat_lit 21744765673936634136843904499201766944931840000000000

noncomputable def ep489 := nat_lit 28887549054769799562146492418793939061

noncomputable def ep490 := nat_lit 16075242402483029277541302597058560000000000

noncomputable def ep491 := nat_lit 3743875596842620785009905756812976791302320380093

noncomputable def ep492 := nat_lit 532746759011447536352675660230443290150830080000000000

noncomputable def ep493 := nat_lit 988725207135224290643449349704844970860827390249160821760418991775230092902400000000

noncomputable def ep494 := @Enclosure.Real.IsNear.mulLit_tf (Real.cos (@HSub.hSub Real Real Real qz597 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz23 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz24 (@Nat.cast Complex Complex.instNatCast j))))) qz348)) (Complex.re (zetaApproximant qz14 2 28)) 1048575 1048576 12578597

noncomputable def ep495 := nat_lit 4399317229513276726532519979986810371

noncomputable def ep496 := nat_lit 30661091618505533747751813120000000000

noncomputable def ep497 := nat_lit 2813814154270937241106667685222589966153

noncomputable def ep498 := nat_lit 421939546198902052116311801069568000000000

noncomputable def ep499 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz597 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz23 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz24 (@Nat.cast Complex Complex.instNatCast j))))) qz348)) Bool.true 1048575 1048576 25157194

noncomputable abbrev qz598 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6794273) (@Nat.cast Real Real.instNatCast 65536))

noncomputable def ep500 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz597 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz23 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz24 (@Nat.cast Complex Complex.instNatCast j))))) qz348) qz598 Bool.false 6794273 65536 179

noncomputable def ep501 := nat_lit 1075735033703237626529014696883

noncomputable def ep502 := nat_lit 10376293541461622784000000000

noncomputable def ep503 := nat_lit 475608160345210572969873187101230821

noncomputable def ep504 := nat_lit 1394456308022167732224000000000000000000

noncomputable def ep505 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz597 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz23 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz24 (@Nat.cast Complex Complex.instNatCast j))))) qz348) Bool.false ep501 ep502 ep503 ep504

noncomputable def ep506 := nat_lit 1735744848935640807408886696883

noncomputable def ep507 := nat_lit 180031446846500851881873187101230821

noncomputable def ep508 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz23 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz24 (@Nat.cast Complex Complex.instNatCast j))))) qz348 ep506 ep502 ep507 ep504 8337158751 131072000

noncomputable def ep509 := nat_lit 140998742337550762184411014349848576000

noncomputable def ep510 := nat_lit 1813103274779038508355890443

noncomputable def ep511 := nat_lit 20752587082923245568000000

noncomputable def ep512 := nat_lit 76287010484682862679439644109389209

noncomputable def ep513 := nat_lit 348614077005541933056000000000000000000

noncomputable def ep514 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz22 qz23 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz24 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true ep510 ep511 ep512 ep513 Bool.false ep506 ep502

noncomputable def ep515 := nat_lit 1479546142870797734211890443

noncomputable def ep516 := nat_lit 73753735686617448985317721582157209

noncomputable def ep517 := nat_lit 1799634833931350972400886696883

noncomputable def ep518 := nat_lit 159765248520544707265828851636782821

noncomputable def ep519 := @Enclosure.Complex.IsNear.subLitP qz23 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz24 (@Nat.cast Complex Complex.instNatCast j))) Bool.true ep515 ep511 ep516 ep513 Bool.false ep517 ep502 ep518

noncomputable def ep520 := nat_lit 4082745616339551922271379616769744373284864

noncomputable def ep521 := nat_lit 244284370464900306587621879410915742134042624

noncomputable abbrev qz349 := (@HSub.hSub Complex Complex Complex qz595 qz544 qz550)

noncomputable abbrev qz350 := (Complex.log qz544)

noncomputable abbrev qz25 := (@HSub.hSub Complex Complex Complex qz595 (@HMul.hMul Complex Complex Complex qz255 qz349 qz350) qz257)

noncomputable abbrev qz351 := qz550

noncomputable abbrev qz26 := qz351

noncomputable abbrev qz599 := qz814

noncomputable abbrev qz352 := qz599

noncomputable abbrev qz27 := qz352

noncomputable abbrev qz28 := (@instHMul Nat instMulNat)

noncomputable abbrev qz600 := (@instHPow Complex Int (@ZPow.toPow Complex (@DivInvMonoid.toZPow Complex Complex.instDivInvMonoid)))

noncomputable abbrev qz29 := qz600

noncomputable abbrev qz30 := (@instHSub Int Int.instSub)

noncomputable abbrev qz894 := (@OfNat.ofNat Int 1 (@instOfNat 1))

noncomputable abbrev qz353 := qz894

noncomputable abbrev qz31 := qz353

noncomputable abbrev qz32 := (@instHMul Int Int.instMul)

noncomputable abbrev qz601 := (@OfNat.ofNat Int 2 (@instOfNat 2))

noncomputable abbrev qz33 := qz601

noncomputable abbrev qz895 := (@HMul.hMul Complex Complex Complex qz3 qz26 ↑qz253)

noncomputable def ep522 := @Enclosure.Complex.IsNear.of_eq qz23 (@HAdd.hAdd Complex Complex Complex qz15 (@HAdd.hAdd Complex Complex Complex qz15 qz25 qz895) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz22 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz29 qz5 (@HSub.hSub Int Int Int qz30 qz31 (@HMul.hMul Int Int Int qz32 qz33 (@Nat.cast Int instNatCastInt k)))))) Bool.true ep515

noncomputable def ep523 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz15 qz25 qz895) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz22 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz29 qz5 (@HSub.hSub Int Int Int qz30 qz31 (@HMul.hMul Int Int Int qz32 qz33 (@Nat.cast Int instNatCastInt k))))) Bool.true 64216515174060879097 900719925474099200

noncomputable def ep524 := nat_lit 103762935414616227840000000

noncomputable def ep525 := nat_lit 15471322861480103113303117

noncomputable def ep526 := nat_lit 51881467707308113920000000000

noncomputable def ep527 := nat_lit 1332656691542075862547634803078846664513945600

noncomputable def ep528 := nat_lit 259354712559878294090974413837509752969259646976

noncomputable def ep529 := @ep523 29113966818795373171 137614000000000000000000 Bool.false 24995143128530728507 144115188075855872 31532750084628550387 275228000000000000000000 Bool.false 2366739564920182989557 ep511 17113388946807211 ep524 Bool.true ep525 ep502 111869475868985611091 ep526 Bool.true ep527 ep515 ep511 ep516 ep513 Bool.false ep528

noncomputable def ep530 := @Enclosure.Complex.IsNear.addLitP qz25 qz895 Bool.true 65044220655502978297 900719925474099200 57440500013323168217 275228000000000000000000

noncomputable def ep531 := nat_lit 8416987076894507545001984

noncomputable def ep532 := @ep530 Bool.false 24995143128530728507 144115188075855872 31532750084628550387 275228000000000000000000 Bool.false 120447 131072 3 1048576 Bool.false 0 1 0 1 Bool.true ep531 64216515174060879097 900719925474099200 29113966818795373171 137614000000000000000000 Bool.false 24995143128530728507 24995143128530728507 144115188075855872

noncomputable abbrev qz34 := (@HMul.hMul Complex Complex Complex qz255 qz349 qz350)

noncomputable def ep533 := @Enclosure.Complex.IsNear.subLitP qz34 qz5 Bool.true 61216160972238056697 900719925474099200 57440500013323168217 275228000000000000000000 Bool.false 4125371951444962245327

noncomputable def ep534 := nat_lit 12497571564265364253500000

noncomputable def ep535 := @ep533 18014398509481984000 31532750084628550387 275228000000000000000000 Bool.false 17000 4000 0 1 Bool.false 222262 4000 0 1 Bool.true 260176882622011913188000 65044220655502978297 900719925474099200 57440500013323168217 275228000000000000000000 Bool.false ep534 24995143128530728507 144115188075855872 31532750084628550387 275228000000000000000000

noncomputable abbrev qz35 := qz349

noncomputable abbrev qz36 := qz350

noncomputable def ep536 := @Enclosure.Complex.IsNear.mul qz35 qz36 Bool.true 61216160972238056697 900719925474099200 57440500013323168217 275228000000000000000000 Bool.false 4125371951444962245327 18014398509481984000 31532750084628550387

noncomputable def ep537 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re qz35) (Complex.re qz36)) (@HMul.hMul Real Real Real qz0 (Complex.im qz35) (Complex.im qz36)) 543198825488296755 36028797018963968 750000002270631 110091200000000000000 18699032902361368893 225179981368524800

noncomputable def ep538 := nat_lit 551386159487247224542768726146023424

noncomputable def ep539 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz35) (Complex.re qz36) 15000 4000 0 1 36213255032553117 9007199254740992 250000000756877 137614000000000000000

noncomputable def ep540 := @Enclosure.Complex.IsNear.re_isNear qz35 Bool.false 15000 4000 0 1 Bool.false 222262 4000 0 1

noncomputable def ep541 := @Enclosure.Complex.IsNear.of_eq qz35 (Complex.mk (Enclosure.sfrac Bool.false 15000 4000) qz260) Bool.false 15000 4000 0 1 Bool.false 222262 4000 0

noncomputable abbrev qz602 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 17000 4000) qz260))

noncomputable def ep542 := @Enclosure.Complex.IsNear.of_eq qz36 qz602 Bool.false 36213255032553117 9007199254740992 250000000756877 137614000000000000000 Bool.false 841305886852515 562949953421312 500000000068807 137614000000000000000

noncomputable def ep543 := nat_lit 2019615806948240243683879270693342133092548322167016510221876712100595619107097159043973120

noncomputable def ep544 := nat_lit 29089100871046466822528570952431614021846820267585028433485390210444305085848158487445504

noncomputable def ep545 := nat_lit 705795595761805310657761147873750365917032024664887151208546029725224322481422663680

noncomputable def ep546 := BSN.log_dyadic_bound 16921396644 82457396644 5 4 ep543 1048576 275228 ep544 ep545 436563 99378793288 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 16921396644) (BSN.artanhQ 82457396644) 0 4 ep544 ep543 ep545 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz603 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable def ep547 := @Enclosure.Real.IsNear.mulLit_ff qz345 (Real.log (Enclosure.sfrac Bool.false 49689396644 16000000)) 1 2 0 1 36213255032553117 4503599627370496 250000000756877 68807000000000000000 36213255032553117 9007199254740992 250000000756877 137614000000000000000 qz346 (BSN.isNear_log_sfrac 49689396644 16000000 36213255032553117 4503599627370496 250000000756877 68807000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 49689396644) qz603)) Bool.false 303778800872115337691136 37778931862957161709568 1000000003027508 275228000000000000000 36213255032553117 4503599627370496 250000000756877 68807000000000000000 (BSN.log_rat_reduce_isNear 49689396644 16000000 11 99378793288 65536000000 436563 1048576 24973259072661432 36028797018963968 275228 1000000000000000 rfl rfl rfl rfl (ep546 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep548 := BSN.arctan_dyadic_bound_f 17000 222262 1 0 1048576 275228 0 1 1 0 1 1 80045 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 17000) (BSN.arctanEvenQ 222262) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 17000) (BSN.arctanOddQ 222262) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz354 := (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz355 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 2) Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable abbrev qz604 := (@Nat.cast Real Real.instNatCast 17000)

noncomputable abbrev qz605 := (@Nat.cast Real Real.instNatCast 222262)

noncomputable def ep549 := @Enclosure.Real.IsNear.subLit_ff_p qz354 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz604 qz605)) 884279719003555 562949953421312 1 2000000000000000 80045 1048576 1 275228 882173161612262768640 841305886852515 562949953421312 500000000068807 137614000000000000000 qz355 (ep548 rfl) rfl rfl

noncomputable abbrev qz606 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 222262) (@Nat.cast Real Real.instNatCast 17000)))

noncomputable def ep550 := @Enclosure.Complex.IsNear.re_isNear qz36 Bool.false 36213255032553117 9007199254740992 250000000756877 137614000000000000000 Bool.false 841305886852515 562949953421312 500000000068807 137614000000000000000 (ep542 (@congrArg Complex Complex qz5 qz546 Complex.log (BSN.w_shift_mk qz11 Bool.false 111131 1000 4 (@Eq.refl Real qz11) rfl)) (@Enclosure.Complex.IsNear.of_parts qz602 Bool.false 36213255032553117 9007199254740992 250000000756877 137614000000000000000 Bool.false 841305886852515 562949953421312 500000000068807 137614000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz602) (@HMul.hMul Real Real Real qz0 qz345 (Real.log (Enclosure.sfrac Bool.false 49689396644 16000000))) Bool.false 36213255032553117 9007199254740992 250000000756877 137614000000000000000 (Enclosure.clog_re_eq 17000 222262 4000 49689396644 16000000 rfl rfl rfl) (ep547 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz602) qz606 Bool.false 841305886852515 562949953421312 500000000068807 137614000000000000000 (Enclosure.clog_im_eq 17000 222262 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz606 (@HSub.hSub Real Real Real qz597 qz354 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz604 qz605))) Bool.false 841305886852515 562949953421312 500000000068807 137614000000000000000 (BSN.arctan_recip 222262 17000 rfl rfl) ep549))))

noncomputable def ep551 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz35) (Complex.im qz36) 222262 4000 0 1 841305886852515 562949953421312 500000000068807 137614000000000000000

noncomputable def ep552 := @Enclosure.Complex.IsNear.im_isNear qz35 Bool.false 15000 4000 0 1 Bool.false 222262 4000 0 1

noncomputable def ep553 := @Enclosure.Complex.IsNear.im_isNear qz36 Bool.false 36213255032553117 9007199254740992 250000000756877 137614000000000000000 Bool.false 841305886852515 562949953421312 500000000068807 137614000000000000000 (ep542 (@congrArg Complex Complex qz5 qz546 Complex.log (BSN.w_shift_mk qz11 Bool.false 111131 1000 4 (@Eq.refl Real qz11) rfl)) (@Enclosure.Complex.IsNear.of_parts qz602 Bool.false 36213255032553117 9007199254740992 250000000756877 137614000000000000000 Bool.false 841305886852515 562949953421312 500000000068807 137614000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz602) (@HMul.hMul Real Real Real qz0 qz345 (Real.log (Enclosure.sfrac Bool.false 49689396644 16000000))) Bool.false 36213255032553117 9007199254740992 250000000756877 137614000000000000000 (Enclosure.clog_re_eq 17000 222262 4000 49689396644 16000000 rfl rfl rfl) (ep547 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz602) qz606 Bool.false 841305886852515 562949953421312 500000000068807 137614000000000000000 (Enclosure.clog_im_eq 17000 222262 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz606 (@HSub.hSub Real Real Real qz597 qz354 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz604 qz605))) Bool.false 841305886852515 562949953421312 500000000068807 137614000000000000000 (BSN.arctan_recip 222262 17000 rfl rfl) ep549))))

noncomputable abbrev qz356 := (@ep541 1 (BSN.w_sub_half_mk qz11 Bool.false 111131 1000 4 (@Eq.refl Real qz11) rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 15000 4000) (Enclosure.sfrac Bool.false 222262 4000) Bool.false 15000 4000 0 1 Bool.false 222262 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 15000 4000) (Enclosure.Real.IsNear.const Bool.false 222262 4000)))

noncomputable def ep554 := @ep537 55565500007646590717 275228000000000000000000 ep538 61216160972238056697 900719925474099200 57440500013323168217 275228000000000000000000 (@ep539 543198825488296755 36028797018963968 750000002270631 110091200000000000000 (ep540 qz356) ep550 rfl) (@ep551 18699032902361368893 225179981368524800 55565500007646590717 275228000000000000000000 (ep552 qz356) ep553 rfl) rfl

noncomputable def ep555 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re qz35) (Complex.im qz36)) (@HMul.hMul Real Real Real qz0 (Complex.im qz35) (Complex.re qz36)) 12619588302787725 2251799813685248 1500000000206421 110091200000000000000 4024415245022660445327 18014398509481984000

noncomputable def ep556 := nat_lit 9289511791646113942803156212536836096

noncomputable def ep557 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz35) (Complex.im qz36) 15000 4000 0 1 841305886852515 562949953421312 500000000068807 137614000000000000000

noncomputable def ep558 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz35) (Complex.re qz36) 222262 4000 0 1 36213255032553117 9007199254740992 250000000756877 137614000000000000000

noncomputable def ep559 := @ep555 27782750084112497887 275228000000000000000000 ep556 4125371951444962245327 18014398509481984000 31532750084628550387 275228000000000000000000 (@ep557 12619588302787725 2251799813685248 1500000000206421 110091200000000000000 (ep540 qz356) ep553 rfl) (@ep558 4024415245022660445327 18014398509481984000 27782750084112497887 275228000000000000000000 (ep552 qz356) ep550 rfl) rfl

noncomputable def ep560 := ep535 (@ep536 275228000000000000000000 (ep554 rfl) (ep559 rfl)) qz13 rfl rfl rfl rfl rfl rfl

noncomputable def ep561 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re qz26) (Complex.re ↑qz253)) (@HMul.hMul Real Real Real qz0 (Complex.im qz26) (Complex.im ↑qz253)) 120447 131072 3 1048576 0 1 0 1 120447 120447

noncomputable def ep562 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz26) (Complex.re ↑qz253) 1 2 0 1 120447 65536 3 524288 120447 131072 3 1048576

noncomputable abbrev qz357 := (@Enclosure.Complex.IsNear.of_eq qz26 (Complex.mk (Enclosure.sfrac Bool.false 1 2) qz554) Bool.false 1 2 0 1 Bool.false 0 1 0 1 BSN.half_c_mk (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 2) qz554 Bool.false 1 2 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 2) qz820))

noncomputable def ep563 := ep562 (@Enclosure.Complex.IsNear.re_isNear qz26 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz357) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz253) qz253 Bool.false 120447 65536 3 524288 (Complex.ofReal_re qz253) EMRow35.d4)

noncomputable def ep564 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz26) (Complex.im ↑qz253) 0 1 0 1 0 1 0 1 0 1 0 1

noncomputable def ep565 := ep564 (@Enclosure.Complex.IsNear.im_isNear qz26 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz357) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz253) qz264 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz253) (0 : Real) qz264 (Complex.ofReal_im qz253) Enclosure.sfrac_zero_eq) qz274)

noncomputable def ep566 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re qz26) (Complex.im ↑qz253)) (@HMul.hMul Real Real Real qz0 (Complex.im qz26) (Complex.re ↑qz253)) 0 1 0 1 0 1 0 1 0 0

noncomputable def ep567 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz26) (Complex.im ↑qz253) 1 2 0 1 0 1 0 1 0 1 0 1

noncomputable def ep568 := ep567 (@Enclosure.Complex.IsNear.re_isNear qz26 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz357) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz253) qz264 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz253) (0 : Real) qz264 (Complex.ofReal_im qz253) Enclosure.sfrac_zero_eq) qz274)

noncomputable def ep569 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz26) (Complex.re ↑qz253) 0 1 0 1 120447 65536 3 524288 0 1 0 1

noncomputable def ep570 := ep569 (@Enclosure.Complex.IsNear.im_isNear qz26 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz357) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz253) qz253 Bool.false 120447 65536 3 524288 (Complex.ofReal_re qz253) EMRow35.d4)

noncomputable def ep571 := @ep532 31532750084628550387 275228000000000000000000 (ep560 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz26 (↑qz253) Bool.false 120447 131072 3 1048576 Bool.false 0 1 0 1 (@ep561 131072 3 1048576 (ep563 rfl) (ep565 rfl) rfl rfl) (@ep566 1 0 1 (ep568 rfl) (ep570 rfl) rfl rfl))

noncomputable abbrev qz37 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)

noncomputable abbrev qz38 := (@HMul.hMul Complex Complex Complex qz255 (@HMul.hMul Complex Complex Complex qz255 (2 : Complex) qz553) (@HSub.hSub Complex Complex Complex qz595 (@HMul.hMul Complex Complex Complex qz255 (2 : Complex) qz553) (1 : Complex)))

noncomputable abbrev qz39 := (@HPow.hPow Complex Int Complex qz600 qz257 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) qz353 (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) qz601 (@Nat.cast Int instNatCastInt 2))))

noncomputable def ep572 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz22 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz29 qz5 (@HSub.hSub Int Int Int qz30 qz31 (@HMul.hMul Int Int Int qz32 qz33 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz15 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz22 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz29 qz5 (@HSub.hSub Int Int Int qz30 qz31 (@HMul.hMul Int Int Int qz32 qz33 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz37)) qz38) qz39)) Bool.false 2366739564920182989557 ep511 17113388946807211 ep524

noncomputable def ep573 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz22 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz29 qz5 (@HSub.hSub Int Int Int qz30 qz31 (@HMul.hMul Int Int Int qz32 qz33 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz37)) qz38) qz39) Bool.false 3918449 34359738368 17 103079215104 Bool.true

noncomputable def ep574 := nat_lit 81320552235851638323862596222976

noncomputable def ep575 := nat_lit 265795302863656724105378680199446528000

noncomputable def ep576 := @ep573 25615362107 17179869184000 111131 51539607552000 Bool.false 75615632758989557 ep511 628626807211 ep524 Bool.true 162193935355081303117 ep502 1348391225611091 ep526 Bool.false ep574 2366739564920182989557 ep511 17113388946807211 ep524 Bool.true ep575 ep525 ep502 111869475868985611091

noncomputable abbrev qz40 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)

noncomputable abbrev qz41 := (@HMul.hMul Complex Complex Complex qz255 (@HMul.hMul Complex Complex Complex qz255 (2 : Complex) qz590) (@HSub.hSub Complex Complex Complex qz595 (@HMul.hMul Complex Complex Complex qz255 (2 : Complex) qz590) (1 : Complex)))

noncomputable abbrev qz42 := (@HPow.hPow Complex Int Complex qz600 qz257 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) qz353 (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) qz601 (@Nat.cast Int instNatCastInt 1))))

noncomputable def ep577 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz22 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz29 qz5 (@HSub.hSub Int Int Int qz30 qz31 (@HMul.hMul Int Int Int qz32 qz33 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz15 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz22 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz29 qz5 (@HSub.hSub Int Int Int qz30 qz31 (@HMul.hMul Int Int Int qz32 qz33 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz40)) qz41) qz42)) Bool.false 3918449 34359738368 17 103079215104

noncomputable def ep578 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz22 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz29 qz5 (@HSub.hSub Int Int Int qz30 qz31 (@HMul.hMul Int Int Int qz32 qz33 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz40)) qz41) qz42) Bool.false 0 1 0 1 Bool.false

noncomputable def ep579 := @ep578 0 1 0 1 Bool.false 3918449 34359738368 17 103079215104 Bool.true 25615362107 17179869184000 111131 51539607552000 Bool.false 3918449 3918449 34359738368 17 103079215104 Bool.true 25615362107 25615362107 17179869184000 111131

noncomputable def ep580 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz22 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz29 qz5 (@HSub.hSub Int Int Int qz30 qz31 (@HMul.hMul Int Int Int qz32 qz33 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz264 qz264) Bool.false 0 1 0 1 Bool.false

noncomputable def ep581 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz40)) qz41) qz42 Bool.false 3918449 34359738368 17 103079215104 Bool.true 25615362107 17179869184000 111131 51539607552000

noncomputable def ep582 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz40)) qz41)) (Complex.re qz42)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz40)) qz41)) (Complex.im qz42)) 3918449 34359738368 17 103079215104 0 1 0

noncomputable def ep583 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz40)) qz41)) (Complex.re qz42) 1 12 0 1 11755347 8589934592 17 8589934592 3918449

noncomputable def ep584 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz40)) qz41) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz264) Bool.false 1 12 0 1 Bool.false 0 1 0 1

noncomputable abbrev qz607 := (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 12) qz264 Bool.false 1 12 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 12) qz274)

noncomputable def ep585 := @Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz40)) qz41) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep584 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz607)

noncomputable def ep586 := @Enclosure.Complex.IsNear.re_isNear qz42 Bool.false 11755347 8589934592 17 8589934592 Bool.true 76846086321 4294967296000 111131 4294967296000

noncomputable def ep587 := @Enclosure.Complex.IsNear.of_eq qz42 (@Inv.inv Complex Complex.instInv qz8) Bool.false 11755347 8589934592 17 8589934592 Bool.true 76846086321 4294967296000 111131

noncomputable def ep588 := @Enclosure.Complex.IsNear.of_parts (@Inv.inv Complex Complex.instInv qz8) Bool.false 11755347 8589934592 17 8589934592 Bool.true 76846086321 4294967296000 111131

noncomputable abbrev qz358 := (@MonoidWithZeroHom Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz359 := (@MonoidWithZeroHom.funLike Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable def ep589 := @Enclosure.Real.IsNear.mulLit_ff qz9 (@Inv.inv Real Real.instInv (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz8)) 17000 4000 0 1 691491 2147483648 1 2147483648

noncomputable def ep590 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz8)) Bool.false 691491 2147483648 1 2147483648 691491 2147483648 1

noncomputable abbrev qz608 := (@instHAdd Real Real.instAdd)

noncomputable def ep591 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz8) (@HAdd.hAdd Real Real Real qz608 (@HMul.hMul Real Real Real qz0 qz9 qz9) (@HMul.hMul Real Real Real qz0 qz10 qz10)) Bool.false 12422349161 4000000 0 1

noncomputable def ep592 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz9 qz9) (@HMul.hMul Real Real Real qz0 qz10 qz10) 289 16 0 1 12350099161 4000000

noncomputable def ep593 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz9 17000 4000 0 1 17000 4000 0 1

noncomputable def ep594 := @Enclosure.Real.IsNear.mulLit_ff qz10 qz10 222262 4000 0 1 222262 4000 0 1

noncomputable def ep595 := @ep592 0 1 198757586576 12422349161 4000000 0 1 (@ep593 289 16 0 1 (ep32 qz12) (ep32 qz12) rfl) (@ep594 12350099161 4000000 0 1 (ep37 qz12) (ep37 qz12) rfl)

noncomputable def ep596 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz8) 12422349161 4000000 0 1 345745 345746 1073741824 (ep591 (Enclosure.Complex.normSq_eq_mul_add_mul qz8) (ep595 rfl rfl)) rfl

noncomputable def ep597 := @Enclosure.Real.IsNear.of_eq (Complex.re (@Inv.inv Complex Complex.instInv qz8)) (@HMul.hMul Real Real Real qz0 qz9 (@Inv.inv Real Real.instInv (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz8))) Bool.false 11755347 8589934592 17 8589934592 (Enclosure.Complex.inv_re_eq_mul qz8) (@ep589 11755347 8589934592 17 8589934592 (ep32 qz12) (@ep590 2147483648 (ep596 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep598 := @Enclosure.Real.IsNear.of_eq (Complex.im (@Inv.inv Complex Complex.instInv qz8)) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz10) (@Inv.inv Real Real.instInv (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz8))) Bool.true 76846086321 4294967296000 111131 4294967296000 (Enclosure.Complex.inv_im_eq_mul qz8)

noncomputable def ep599 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz10) (@Inv.inv Real Real.instInv (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz8)) 222262 4000 0 1 691491 2147483648 1

noncomputable def ep600 := @ep599 2147483648 76846086321 4294967296000 111131 4294967296000 (@Enclosure.Real.IsNear.neg qz10 Bool.false 222262 4000 0 1 (ep37 qz12)) (@ep590 2147483648 (ep596 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep601 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz40)) qz41)) (Complex.im qz42) 0 1 0 1 76846086321 4294967296000 111131 4294967296000 0

noncomputable def ep602 := @Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz40)) qz41) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep584 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz607)

noncomputable def ep603 := @Enclosure.Complex.IsNear.im_isNear qz42 Bool.false 11755347 8589934592 17 8589934592 Bool.true 76846086321 4294967296000 111131 4294967296000

noncomputable abbrev qz609 := (@ep587 4294967296000 (BSN.zpow_one_sub_two_mul qz5 1 1 rfl rfl) (@ep588 4294967296000 ep597 (ep598 ep600)))

noncomputable def ep604 := @ep582 1 3918449 3918449 34359738368 17 103079215104 (@ep583 34359738368 17 103079215104 ep585 (ep586 qz609) rfl) (@ep601 1 0 1 ep602 (ep603 qz609) rfl) rfl

noncomputable def ep605 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz40)) qz41)) (Complex.im qz42)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz40)) qz41)) (Complex.re qz42)) 25615362107 17179869184000 111131 51539607552000 0 1 0

noncomputable def ep606 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz40)) qz41)) (Complex.im qz42) 1 12 0 1 76846086321 4294967296000 111131 4294967296000 25615362107

noncomputable def ep607 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz40)) qz41)) (Complex.re qz42) 0 1 0 1 11755347 8589934592 17 8589934592 0

noncomputable def ep608 := @ep605 1 25615362107 25615362107 17179869184000 111131 51539607552000 (@ep606 17179869184000 111131 51539607552000 ep585 (ep603 qz609) rfl) (@ep607 1 0 1 ep602 (ep586 qz609) rfl) rfl

noncomputable abbrev qz360 := (@Enclosure.Complex.IsNear.mk qz554 qz554 Bool.false 0 1 0 1 Bool.false 0 1 0 1 qz820 qz820)

noncomputable def ep609 := @ep579 51539607552000 (@ep580 0 1 0 1 (BSN.stirling_sum_base qz5) qz360) (ep581 (ep604 rfl) (ep608 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep610 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz37)) qz38) qz39 Bool.false 75615632758989557 ep511 628626807211 ep524 Bool.true 162193935355081303117 ep502 1348391225611091 ep526

noncomputable def ep611 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz37)) qz38)) (Complex.re qz39)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz37)) qz38)) (Complex.im qz39)) 75615632758989557 ep511 628626807211 ep524 0 1 0

noncomputable def ep612 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz37)) qz38)) (Complex.re qz39) 1 360 0 1 75615632758989557 57646075230342348800000 628626807211 288230376151711744000000 75615632758989557

noncomputable def ep613 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz37)) qz38) (Complex.mk (Enclosure.sfrac Bool.true 1 360) qz264) Bool.true 1 360 0 1 Bool.false 0 1 0 1

noncomputable def ep614 := @Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz37)) qz38) Bool.true 1 360 0 1 Bool.false 0 1 0 1 (ep613 (BSN.stirling_coeff_mk 2 1 30 Bool.true BSN.bern_real_2 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 1 360) qz264 Bool.true 1 360 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.true 1 360) qz274))

noncomputable def ep615 := nat_lit 28823037615171174400000000

noncomputable def ep616 := nat_lit 144115188075855872000000000

noncomputable def ep617 := @Enclosure.Complex.IsNear.re_isNear qz39 Bool.true 75615632758989557 57646075230342348800000 628626807211 288230376151711744000000 Bool.false 162193935355081303117 ep615 1348391225611091 ep616

noncomputable def ep618 := @Enclosure.Complex.IsNear.of_eq qz39 (@Inv.inv Complex Complex.instInv qz2) Bool.true 75615632758989557 57646075230342348800000 628626807211 288230376151711744000000 Bool.false 162193935355081303117 ep615 1348391225611091

noncomputable def ep619 := @Enclosure.Complex.IsNear.of_parts (@Inv.inv Complex Complex.instInv qz2) Bool.true 75615632758989557 57646075230342348800000 628626807211 288230376151711744000000 Bool.false 162193935355081303117 ep615 1348391225611091

noncomputable abbrev qz43 := (Complex.re qz254)

noncomputable def ep620 := @Enclosure.Real.IsNear.mulLit_tf qz43 (@Inv.inv Real Real.instInv (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz2)) 628626807211 16000000 0 1 601435 18014398509481984 1 18014398509481984

noncomputable def ep621 := @Enclosure.Complex.IsNear.re_isNear qz2 Bool.true 628626807211 16000000 0 1 Bool.true 1348391225611091 8000000000 0 1

noncomputable def ep622 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz2)) Bool.false 601435 18014398509481984 1 18014398509481984 601435 18014398509481984 1

noncomputable def ep623 := nat_lit 1916951812991054049926012460281

noncomputable abbrev qz44 := (Complex.im qz254)

noncomputable def ep624 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz2) (@HAdd.hAdd Real Real Real qz608 (@HMul.hMul Real Real Real qz0 qz43 qz43) (@HMul.hMul Real Real Real qz0 qz44 qz44)) Bool.false ep623 64000000000000000000 0 1

noncomputable def ep625 := nat_lit 1818158897304980109526382210281

noncomputable def ep626 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz43 qz43) (@HMul.hMul Real Real Real qz0 qz44 qz44) 395171662744295761598521 256000000000000 0 1 ep625 64000000000000000000

noncomputable def ep627 := nat_lit 490739664125709836781059189831936000000000000

noncomputable def ep628 := @Enclosure.Real.IsNear.mulLit_tt qz43 qz43 628626807211 16000000 0 1 628626807211 16000000 0 1

noncomputable def ep629 := @Enclosure.Real.IsNear.mulLit_tt qz44 qz44 1348391225611091 8000000000 0 1 1348391225611091 8000000000 0 1

noncomputable def ep630 := @Enclosure.Complex.IsNear.im_isNear qz2 Bool.true 628626807211 16000000 0 1 Bool.true 1348391225611091 8000000000 0 1

noncomputable def ep631 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz2) ep623 64000000000000000000 0 1 300717 300718 9007199254740992 (ep624 (Enclosure.Complex.normSq_eq_mul_add_mul qz2) (@ep626 0 1 ep627 ep623 64000000000000000000 0 1 (@ep628 395171662744295761598521 256000000000000 0 1 (ep621 EMRow35.d5) (ep621 EMRow35.d5) rfl) (@ep629 ep625 64000000000000000000 0 1 (ep630 EMRow35.d5) (ep630 EMRow35.d5) rfl) rfl rfl)) rfl

noncomputable def ep632 := @Enclosure.Real.IsNear.of_eq (Complex.re (@Inv.inv Complex Complex.instInv qz2)) (@HMul.hMul Real Real Real qz0 qz43 (@Inv.inv Real Real.instInv (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz2))) Bool.true 75615632758989557 57646075230342348800000 628626807211 288230376151711744000000 (Enclosure.Complex.inv_re_eq_mul qz2) (@ep620 75615632758989557 57646075230342348800000 628626807211 288230376151711744000000 (ep621 EMRow35.d5) (@ep622 18014398509481984 (ep631 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep633 := @Enclosure.Real.IsNear.of_eq (Complex.im (@Inv.inv Complex Complex.instInv qz2)) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz44) (@Inv.inv Real Real.instInv (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz2))) Bool.false 162193935355081303117 ep615 1348391225611091 ep616 (Enclosure.Complex.inv_im_eq_mul qz2)

noncomputable def ep634 := @Enclosure.Real.IsNear.mulLit_ff (@Neg.neg Real Real.instNeg qz44) (@Inv.inv Real Real.instInv (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz2)) 1348391225611091 8000000000 0 1 601435 18014398509481984 1

noncomputable def ep635 := @ep634 18014398509481984 162193935355081303117 ep615 1348391225611091 ep616 (@Enclosure.Real.IsNear.neg qz44 Bool.true 1348391225611091 8000000000 0 1 (ep630 EMRow35.d5)) (@ep622 18014398509481984 (ep631 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep636 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz37)) qz38)) (Complex.im qz39) 0 1 0 1 162193935355081303117 ep615 1348391225611091 ep616 0

noncomputable def ep637 := @Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz37)) qz38) Bool.true 1 360 0 1 Bool.false 0 1 0 1 (ep613 (BSN.stirling_coeff_mk 2 1 30 Bool.true BSN.bern_real_2 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 1 360) qz264 Bool.true 1 360 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.true 1 360) qz274))

noncomputable def ep638 := @Enclosure.Complex.IsNear.im_isNear qz39 Bool.true 75615632758989557 57646075230342348800000 628626807211 288230376151711744000000 Bool.false 162193935355081303117 ep615 1348391225611091 ep616

noncomputable abbrev qz896 := (@ep618 ep616 (BSN.zpow_one_sub_two_mul qz5 2 3 rfl rfl) (@ep619 ep616 ep632 (ep633 ep635)))

noncomputable def ep639 := @ep611 1 75615632758989557 75615632758989557 ep511 628626807211 ep524 (@ep612 ep511 628626807211 ep524 ep614 (ep617 qz896) rfl) (@ep636 1 0 1 ep637 (ep638 qz896) rfl) rfl

noncomputable def ep640 := @Enclosure.Real.IsNear.addLit_tt (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz37)) qz38)) (Complex.im qz39)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz37)) qz38)) (Complex.re qz39)) 162193935355081303117 ep502 1348391225611091 ep526 0 1 0

noncomputable def ep641 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz37)) qz38)) (Complex.im qz39) 1 360 0 1 162193935355081303117 ep615 1348391225611091 ep616 162193935355081303117

noncomputable def ep642 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz37)) qz38)) (Complex.re qz39) 0 1 0 1 75615632758989557 57646075230342348800000 628626807211 288230376151711744000000 0

noncomputable def ep643 := @ep640 1 162193935355081303117 162193935355081303117 ep502 1348391225611091 ep526 (@ep641 ep502 1348391225611091 ep526 ep614 (ep638 qz896) rfl) (@ep642 1 0 1 ep637 (ep617 qz896) rfl) rfl

noncomputable def ep644 := @ep576 ep526 (@ep577 Bool.true 25615362107 17179869184000 111131 51539607552000 (BSN.stirling_sum_succ qz5 0 1 rfl) (ep609 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep610 (ep639 rfl) (ep643 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep645 := @ep529 ep517 ep502 ep518 ep504 (ep571 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep572 Bool.true ep525 ep502 111869475868985611091 ep526 (BSN.stirling_sum_succ qz5 1 2 rfl) (ep644 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep646 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz24 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz11 4) Bool.false 36193265181015709 2251799813685248 250000000756877 34403500000000000000 Bool.false 866563381560739 140737488355328

noncomputable def ep647 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz11 4) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.logSumC qz11 3) (Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz24 qz552))) Bool.false 36193265181015709 2251799813685248 250000000756877 34403500000000000000 Bool.false 866563381560739 140737488355328 500000000068807 34403500000000000000

noncomputable def ep648 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz11 3) (Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz24 qz552)) Bool.false 108570697728572375 9007199254740992 750000002270631 137614000000000000000 Bool.false 2614862519308521 562949953421312 1500000000206421 137614000000000000000 Bool.false

noncomputable def ep649 := nat_lit 1303999804660351156080369112973312

noncomputable def ep650 := nat_lit 1951327261144930552429540278272

noncomputable def ep651 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz11 3) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.logSumC qz11 2) (Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz24 qz553))) Bool.false 108570697728572375 9007199254740992 750000002270631 137614000000000000000 Bool.false 2614862519308521 562949953421312 1500000000206421 137614000000000000000

noncomputable def ep652 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz11 2) (Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz24 qz553)) Bool.false 36188168128577181 4503599627370496 250000000756877 68807000000000000000 Bool.false 876682727163299 281474976710656 500000000068807 68807000000000000000 Bool.false

noncomputable def ep653 := nat_lit 488958953833753304518149275648000

noncomputable def ep654 := nat_lit 736018366723933223592212299776

noncomputable def ep655 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz11 2) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.logSumC qz11 1) (Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz24 qz590))) Bool.false 36188168128577181 4503599627370496 250000000756877 68807000000000000000 Bool.false 876682727163299 281474976710656 500000000068807 68807000000000000000

noncomputable def ep656 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz11 1) (Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz24 qz590)) Bool.false 36187072911916701 9007199254740992 250000000756877 137614000000000000000 Bool.false 881747298911651 562949953421312 500000000068807 137614000000000000000 Bool.false

noncomputable def ep657 := nat_lit 651908081996324207725107273007104

noncomputable def ep658 := nat_lit 987057000843695897043141656576

noncomputable abbrev qz897 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz24 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep659 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz11 1) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.logSumC qz11 0) qz897) Bool.false 36187072911916701 9007199254740992 250000000756877 137614000000000000000 Bool.false 881747298911651 562949953421312 500000000068807 137614000000000000000

noncomputable def ep660 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz11 0) qz897 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz898 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz260))

noncomputable def ep661 := @Enclosure.Complex.IsNear.of_eq qz897 qz898 Bool.false 36187072911916701 9007199254740992 250000000756877 137614000000000000000 Bool.false 881747298911651 562949953421312 500000000068807 137614000000000000000

noncomputable def ep662 := nat_lit 1963869352742286637537792420197133991578589731865290334665619242841473264739422709123973120

noncomputable def ep663 := nat_lit 27504021971062857114995853460414424337339579798680892811593408982366195030761734423445504

noncomputable def ep664 := nat_lit 615229073621964828606876180616615451692993332380096869782591018206584287542542663680

noncomputable def ep665 := BSN.log_dyadic_bound 16633396644 82169396644 5 4 ep662 1048576 275228 ep663 ep664 430467 98802793288 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 16633396644) (BSN.artanhQ 82169396644) 0 4 ep663 ep662 ep664 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep666 := @Enclosure.Real.IsNear.mulLit_ff qz345 (Real.log (Enclosure.sfrac Bool.false 49401396644 16000000)) 1 2 0 1 36187072911916701 4503599627370496 250000000756877 68807000000000000000 36187072911916701 9007199254740992 250000000756877 137614000000000000000 qz346 (BSN.isNear_log_sfrac 49401396644 16000000 36187072911916701 4503599627370496 250000000756877 68807000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 49401396644) qz603)) Bool.false 303559169325487733342208 37778931862957161709568 1000000003027508 275228000000000000000 36187072911916701 4503599627370496 250000000756877 68807000000000000000 (BSN.log_rat_reduce_isNear 49401396644 16000000 11 98802793288 65536000000 430467 1048576 24973259072661432 36028797018963968 275228 1000000000000000 rfl rfl rfl rfl (ep665 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep667 := BSN.arctan_dyadic_bound_f 1000 222262 1 0 1048576 275228 0 1 1 0 1 1 4717 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 222262) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 222262) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz899 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable def ep668 := @Enclosure.Real.IsNear.subLit_ff_p qz354 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz899 qz605)) 884279719003555 562949953421312 1 2000000000000000 4717 1048576 1 275228 924579055703583358976 881747298911651 562949953421312 500000000068807 137614000000000000000 qz355 (ep667 rfl) rfl rfl

noncomputable abbrev qz900 := (@HAdd.hAdd Complex Complex Complex qz15 qz24 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz901 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz260)

noncomputable def ep669 := @ep660 36187072911916701 9007199254740992 250000000756877 137614000000000000000 Bool.false 881747298911651 562949953421312 500000000068807 137614000000000000000 Bool.false 36187072911916701 36187072911916701 9007199254740992 250000000756877 137614000000000000000 Bool.false 881747298911651 881747298911651 562949953421312 500000000068807 137614000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz11 0) (Complex.mk qz264 qz264) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz11) qz360) (ep661 (@congrArg Complex Complex qz900 qz901 Complex.log (BSN.w_shift_mk qz11 Bool.false 111131 1000 0 (@Eq.refl Real qz11) rfl)) (@Enclosure.Complex.IsNear.of_parts qz898 Bool.false 36187072911916701 9007199254740992 250000000756877 137614000000000000000 Bool.false 881747298911651 562949953421312 500000000068807 137614000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz898) (@HMul.hMul Real Real Real qz0 qz345 (Real.log (Enclosure.sfrac Bool.false 49401396644 16000000))) Bool.false 36187072911916701 9007199254740992 250000000756877 137614000000000000000 (Enclosure.clog_re_eq 1000 222262 4000 49401396644 16000000 rfl rfl rfl) (ep666 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz898) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz605 qz899)) Bool.false 881747298911651 562949953421312 500000000068807 137614000000000000000 (Enclosure.clog_im_eq 1000 222262 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz605 qz899)) (@HSub.hSub Real Real Real qz597 qz354 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz899 qz605))) Bool.false 881747298911651 562949953421312 500000000068807 137614000000000000000 (BSN.arctan_recip 222262 1000 rfl rfl) ep668)))) rfl rfl

noncomputable abbrev qz902 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz260))

noncomputable def ep670 := @Enclosure.Complex.IsNear.of_eq (Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz24 qz590)) qz902 Bool.false 36189263345237661 9007199254740992 250000000756877 137614000000000000000 Bool.false 871618155414947 562949953421312 500000000068807 137614000000000000000

noncomputable def ep671 := nat_lit 1968462895103236283417634348221487780947942723147500412076356579715769789753368913283973120

noncomputable def ep672 := nat_lit 27633443041297929690376151484850333251763536782720733860757160721984679143373603095445504

noncomputable def ep673 := nat_lit 622366656216742077394161355168970791893763768464934080139802301540783917120782663680

noncomputable def ep674 := BSN.log_dyadic_bound 16657396644 82193396644 5 4 ep671 1048576 275228 ep672 ep673 430977 98850793288 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 16657396644) (BSN.artanhQ 82193396644) 0 4 ep672 ep671 ep673 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep675 := @Enclosure.Real.IsNear.mulLit_ff qz345 (Real.log (Enclosure.sfrac Bool.false 49425396644 16000000)) 1 2 0 1 36189263345237661 4503599627370496 250000000756877 68807000000000000000 36189263345237661 9007199254740992 250000000756877 137614000000000000000 qz346 (BSN.isNear_log_sfrac 49425396644 16000000 36189263345237661 4503599627370496 250000000756877 68807000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 49425396644) qz603)) Bool.false 303577544011967404965888 37778931862957161709568 1000000003027508 275228000000000000000 36189263345237661 4503599627370496 250000000756877 68807000000000000000 (BSN.log_rat_reduce_isNear 49425396644 16000000 11 98850793288 65536000000 430977 1048576 24973259072661432 36028797018963968 275228 1000000000000000 rfl rfl rfl rfl (ep674 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep676 := BSN.arctan_dyadic_bound_f 5000 222262 1 0 1048576 275228 0 1 1 0 1 1 23584 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 222262) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 222262) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz903 := (@Nat.cast Real Real.instNatCast 5000)

noncomputable def ep677 := @Enclosure.Real.IsNear.subLit_ff_p qz354 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz903 qz605)) 884279719003555 562949953421312 1 2000000000000000 23584 1048576 1 275228 913957878932383465472 871618155414947 562949953421312 500000000068807 137614000000000000000 qz355 (ep676 rfl) rfl rfl

noncomputable abbrev qz904 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz260)

noncomputable def ep678 := @ep656 36189263345237661 9007199254740992 250000000756877 137614000000000000000 Bool.false 871618155414947 562949953421312 500000000068807 137614000000000000000 Bool.false ep657 36188168128577181 4503599627370496 250000000756877 68807000000000000000 Bool.false ep658 876682727163299 281474976710656 500000000068807 68807000000000000000 (ep659 (BSN.log_sum_c_succ qz11 0 1 rfl) (ep669 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep670 (@congrArg Complex Complex (@HAdd.hAdd Complex Complex Complex qz15 qz24 qz590) qz904 Complex.log (BSN.w_shift_mk qz11 Bool.false 111131 1000 1 (@Eq.refl Real qz11) rfl)) (@Enclosure.Complex.IsNear.of_parts qz902 Bool.false 36189263345237661 9007199254740992 250000000756877 137614000000000000000 Bool.false 871618155414947 562949953421312 500000000068807 137614000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz902) (@HMul.hMul Real Real Real qz0 qz345 (Real.log (Enclosure.sfrac Bool.false 49425396644 16000000))) Bool.false 36189263345237661 9007199254740992 250000000756877 137614000000000000000 (Enclosure.clog_re_eq 5000 222262 4000 49425396644 16000000 rfl rfl rfl) (ep675 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz902) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz605 qz903)) Bool.false 871618155414947 562949953421312 500000000068807 137614000000000000000 (Enclosure.clog_im_eq 5000 222262 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz605 qz903)) (@HSub.hSub Real Real Real qz597 qz354 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz903 qz605))) Bool.false 871618155414947 562949953421312 500000000068807 137614000000000000000 (BSN.arctan_recip 222262 5000 rfl rfl) ep677)))) rfl rfl

noncomputable abbrev qz905 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 9000 4000) qz260))

noncomputable def ep679 := @Enclosure.Complex.IsNear.of_eq (Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz24 qz553)) qz905 Bool.false 36194361471418013 9007199254740992 250000000756877 137614000000000000000 Bool.false 861497064981923 562949953421312 500000000068807 137614000000000000000

noncomputable def ep680 := nat_lit 1979217739275760523387079303051256233226272286157227113117806744443348996430710056323973120

noncomputable def ep681 := nat_lit 27937296845915831822212185393253278539154643915020055280072282419972845716961296663445504

noncomputable def ep682 := nat_lit 639303466386942257372404317808876842448693604523725478033156261185210252803342663680

noncomputable def ep683 := BSN.log_dyadic_bound 16713396644 82249396644 5 4 ep680 1048576 275228 ep681 ep682 432164 98962793288 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 16713396644) (BSN.artanhQ 82249396644) 0 4 ep681 ep680 ep682 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep684 := @Enclosure.Real.IsNear.mulLit_ff qz345 (Real.log (Enclosure.sfrac Bool.false 49481396644 16000000)) 1 2 0 1 36194361471418013 4503599627370496 250000000756877 68807000000000000000 36194361471418013 9007199254740992 250000000756877 137614000000000000000 qz346 (BSN.isNear_log_sfrac 49481396644 16000000 36194361471418013 4503599627370496 250000000756877 68807000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 49481396644) qz603)) Bool.false 303620310194028915195904 37778931862957161709568 1000000003027508 275228000000000000000 36194361471418013 4503599627370496 250000000756877 68807000000000000000 (BSN.log_rat_reduce_isNear 49481396644 16000000 11 98962793288 65536000000 432164 1048576 24973259072661432 36028797018963968 275228 1000000000000000 rfl rfl rfl rfl (ep683 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep685 := BSN.arctan_dyadic_bound_f 9000 222262 1 0 1048576 275228 0 1 1 0 1 1 42436 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 222262) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 222262) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz906 := (@Nat.cast Real Real.instNatCast 9000)

noncomputable def ep686 := @Enclosure.Real.IsNear.subLit_ff_p qz354 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz906 qz605)) 884279719003555 562949953421312 1 2000000000000000 42436 1048576 1 275228 903345146410484891648 861497064981923 562949953421312 500000000068807 137614000000000000000 qz355 (ep685 rfl) rfl rfl

noncomputable abbrev qz907 := (Complex.mk (Enclosure.sfrac Bool.false 9000 4000) qz260)

noncomputable def ep687 := @ep652 36194361471418013 9007199254740992 250000000756877 137614000000000000000 Bool.false 861497064981923 562949953421312 500000000068807 137614000000000000000 Bool.false ep653 108570697728572375 9007199254740992 750000002270631 137614000000000000000 Bool.false ep654 2614862519308521 562949953421312 1500000000206421 137614000000000000000 (ep655 (BSN.log_sum_c_succ qz11 1 2 rfl) (ep678 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep679 (@congrArg Complex Complex (@HAdd.hAdd Complex Complex Complex qz15 qz24 qz553) qz907 Complex.log (BSN.w_shift_mk qz11 Bool.false 111131 1000 2 (@Eq.refl Real qz11) rfl)) (@Enclosure.Complex.IsNear.of_parts qz905 Bool.false 36194361471418013 9007199254740992 250000000756877 137614000000000000000 Bool.false 861497064981923 562949953421312 500000000068807 137614000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz905) (@HMul.hMul Real Real Real qz0 qz345 (Real.log (Enclosure.sfrac Bool.false 49481396644 16000000))) Bool.false 36194361471418013 9007199254740992 250000000756877 137614000000000000000 (Enclosure.clog_re_eq 9000 222262 4000 49481396644 16000000 rfl rfl rfl) (ep684 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz905) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz605 qz906)) Bool.false 861497064981923 562949953421312 500000000068807 137614000000000000000 (Enclosure.clog_im_eq 9000 222262 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz605 qz906)) (@HSub.hSub Real Real Real qz597 qz354 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz906 qz605))) Bool.false 861497064981923 562949953421312 500000000068807 137614000000000000000 (BSN.arctan_recip 222262 9000 rfl rfl) ep686)))) rfl rfl

noncomputable abbrev qz908 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 13000 4000) qz260))

noncomputable def ep688 := @Enclosure.Complex.IsNear.of_eq (Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz24 qz552)) qz908 Bool.false 36202362995490461 9007199254740992 250000000756877 137614000000000000000 Bool.false 851391006934435 562949953421312 500000000068807 137614000000000000000

noncomputable def ep689 := nat_lit 1996222097814185973492932615308649479921461438042296649930165087860716120718966138243973120

noncomputable def ep690 := nat_lit 28420110402632670399956021170695748647136971270368284355576322943674239497508815127445504

noncomputable def ep691 := nat_lit 666733653057852562804972738308974014296929741715767045503251033134968574590222663680

noncomputable def ep692 := BSN.log_dyadic_bound 16801396644 82337396644 5 4 ep689 1048576 275228 ep690 ep691 434027 99138793288 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 16801396644) (BSN.artanhQ 82337396644) 0 4 ep690 ep689 ep691 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep693 := @Enclosure.Real.IsNear.mulLit_ff qz345 (Real.log (Enclosure.sfrac Bool.false 49569396644 16000000)) 1 2 0 1 36202362995490461 4503599627370496 250000000756877 68807000000000000000 36202362995490461 9007199254740992 250000000756877 137614000000000000000 qz346 (BSN.isNear_log_sfrac 49569396644 16000000 36202362995490461 4503599627370496 250000000756877 68807000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 49569396644) qz603)) Bool.false 303687431842875245068288 37778931862957161709568 1000000003027508 275228000000000000000 36202362995490461 4503599627370496 250000000756877 68807000000000000000 (BSN.log_rat_reduce_isNear 49569396644 16000000 11 99138793288 65536000000 434027 1048576 24973259072661432 36028797018963968 275228 1000000000000000 rfl rfl rfl rfl (ep692 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep694 := BSN.arctan_dyadic_bound_f 13000 222262 1 0 1048576 275228 0 1 1 0 1 1 61260 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 13000) (BSN.arctanEvenQ 222262) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 13000) (BSN.arctanOddQ 222262) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz909 := (@Nat.cast Real Real.instNatCast 13000)

noncomputable def ep695 := @Enclosure.Real.IsNear.subLit_ff_p qz354 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz909 qz605)) 884279719003555 562949953421312 1 2000000000000000 61260 1048576 1 275228 892748176487282114560 851391006934435 562949953421312 500000000068807 137614000000000000000 qz355 (ep694 rfl) rfl rfl

noncomputable abbrev qz910 := (Complex.mk (Enclosure.sfrac Bool.false 13000 4000) qz260)

noncomputable def ep696 := @ep648 36202362995490461 9007199254740992 250000000756877 137614000000000000000 Bool.false 851391006934435 562949953421312 500000000068807 137614000000000000000 Bool.false ep649 36193265181015709 2251799813685248 250000000756877 34403500000000000000 Bool.false ep650 866563381560739 140737488355328 500000000068807 34403500000000000000 (ep651 (BSN.log_sum_c_succ qz11 2 3 rfl) (ep687 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep688 (@congrArg Complex Complex (@HAdd.hAdd Complex Complex Complex qz15 qz24 qz552) qz910 Complex.log (BSN.w_shift_mk qz11 Bool.false 111131 1000 3 (@Eq.refl Real qz11) rfl)) (@Enclosure.Complex.IsNear.of_parts qz908 Bool.false 36202362995490461 9007199254740992 250000000756877 137614000000000000000 Bool.false 851391006934435 562949953421312 500000000068807 137614000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz908) (@HMul.hMul Real Real Real qz0 qz345 (Real.log (Enclosure.sfrac Bool.false 49569396644 16000000))) Bool.false 36202362995490461 9007199254740992 250000000756877 137614000000000000000 (Enclosure.clog_re_eq 13000 222262 4000 49569396644 16000000 rfl rfl rfl) (ep693 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz908) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz605 qz909)) Bool.false 851391006934435 562949953421312 500000000068807 137614000000000000000 (Enclosure.clog_im_eq 13000 222262 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz605 qz909)) (@HSub.hSub Real Real Real qz597 qz354 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz909 qz605))) Bool.false 851391006934435 562949953421312 500000000068807 137614000000000000000 (BSN.arctan_recip 222262 13000 rfl rfl) ep695)))) rfl rfl

noncomputable def ep697 := @ep519 ep504 Bool.false 36193265181015709 2251799813685248 250000000756877 34403500000000000000 Bool.false 866563381560739 140737488355328 500000000068807 34403500000000000000 Bool.true ep520 ep510 ep511 ep512 ep513 Bool.false ep521 ep506 ep502 ep507 ep504 (@ep522 ep511 ep516 ep513 Bool.false ep517 ep502 ep518 ep504 (BSN.logGammaStirling_unfold 2 qz5) (ep645 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep646 500000000068807 34403500000000000000 (BSN.log_sum_c_eq qz11 4) (ep647 (BSN.log_sum_c_succ qz11 3 4 rfl) (ep696 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable def ep698 := @Enclosure.Real.IsNear.mulLit_ff (@HDiv.hDiv Real Real Real qz1 qz11 (2 : Real)) (Real.log Real.pi) 111131 2000 0 1 75021 65536 1 262144 8337158751 131072000 111131 524288000 (@Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real qz1 qz11 (2 : Real)) (Enclosure.sfrac Bool.false 111131 2000) Bool.false 111131 2000 0 1 (BSN.t_half_eq qz11 Bool.false 111131 1000 (@Eq.refl Real qz11)) (Enclosure.Real.IsNear.const Bool.false 111131 2000)) EMRow35.d6 rfl

noncomputable def ep699 := @ep508 111131 524288000 ep509 ep501 ep502 ep503 ep504 (@ep514 ep507 ep504 (ep697 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep698 rfl rfl

noncomputable def ep700 := nat_lit 8340177302352221293885160965755851914686334016922598877961530919278923004630625

noncomputable def ep701 := nat_lit 16749503384780526626398509735866071452795934267406783628029486465611250390625

noncomputable def ep702 := nat_lit 21816203262585220631351728751692971851350157579316719411644342762881427749590625

noncomputable def ep703 := BSN.sin_dyadic_bound_f 3372874965 2147483648 3 2 1048576 275497 ep700 ep97 ep701 ep702 ep100 ep701 1048575 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3372874965) qz268 0 2 ep700 ep97 ep701 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3372874965) qz269 0 2 ep702 ep100 ep701 rfl rfl rfl rfl) rfl rfl

noncomputable def ep704 := @ep500 524288 Bool.true 1048575 1048576 1 137614 (@ep505 6794273 65536 179 524288 ep699 rfl) (Enclosure.sfrac_false_div 6794273 65536) (BSN.cos_reduce1 qz598 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14834060974482947833856) qz582) 226375608064910080 72057594037927936 Bool.false 1048575 1048576 16 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q1 6794273 65536 226375608064910080 72057594037927936 16 14834060974482947833856 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1048575 1048576 14834060974482947833856 9444732965739290427392 3372874965 2147483648 275497 275228 (ep703 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep705 := nat_lit 154478871950640639369767339137935503

noncomputable def ep706 := nat_lit 15330545809252766873875906560000000000

noncomputable def ep707 := nat_lit 393869075340701176309509263382589130549

noncomputable def ep708 := nat_lit 59071536467846287296283652149739520000000

noncomputable abbrev qz45 := (@HPow.hPow Complex Complex Complex (@instHPow Complex Complex Complex.instPow) (@Nat.cast Complex Complex.instNatCast 28) (@Neg.neg Complex Complex.instNeg qz261))

noncomputable abbrev qz46 := (@HAdd.hAdd Complex Complex Complex qz262 (@HDiv.hDiv Complex Complex Complex qz352 (@Nat.cast Complex Complex.instNatCast 28) (@HSub.hSub Complex Complex Complex qz595 qz261 (1 : Complex))) qz351)

noncomputable abbrev qz47 := (@instHSub Nat instSubNat)

noncomputable abbrev qz48 := qz256

noncomputable abbrev qz49 := (@Nat.cast Complex Complex.instNatCast 28)

noncomputable def ep709 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz14 2 28) (@HAdd.hAdd Complex Complex Complex qz15 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 28, @HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast n) qz17) (@HMul.hMul Complex Complex Complex qz3 qz45 (@HAdd.hAdd Complex Complex Complex qz15 qz46 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz49 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1))))))) Bool.false ep495 ep496 ep497

noncomputable def ep710 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 28, @HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast n) qz17) (@HMul.hMul Complex Complex Complex qz3 qz45 (@HAdd.hAdd Complex Complex Complex qz15 qz46 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz49 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))))) Bool.false 74500779689 1099511627776 5984094583655 911495139426304

noncomputable def ep711 := nat_lit 2321781008895977971974112299986810371

noncomputable def ep712 := nat_lit 43721321271422190156888879462589966153

noncomputable def ep713 := nat_lit 1006762499565495585554359380862064497

noncomputable def ep714 := nat_lit 6110775967425086120070904916029130549

noncomputable def ep715 := nat_lit 4837100448125145481793307851394540814028448464896

noncomputable def ep716 := nat_lit 169851315955449157719470277817951697495631331328

noncomputable def ep717 := @ep710 Bool.true 83284600987 1099511627776 5983250585387 911495139426304 Bool.false ep711 ep496 ep712 ep498 Bool.false ep713 ep706 ep714 ep708 Bool.false ep715 ep495 ep496 ep497 ep498 Bool.true ep716 ep705 ep706

noncomputable def ep718 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 28, @HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast n) qz17) (BSN.headSumC qz14 28) Bool.false 74500779689 1099511627776 5984094583655 911495139426304 Bool.true 83284600987 1099511627776 5983250585387

noncomputable abbrev qz911 := (@HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast 27) qz17)

noncomputable def ep719 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 28) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz14 27) qz911) Bool.false 74500779689 1099511627776 5984094583655 911495139426304 Bool.true 83284600987 1099511627776 5983250585387 911495139426304

noncomputable def ep720 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz14 27) qz911 Bool.false 131746312813 1099511627776 484779836025633 75654096572383232 Bool.false 120426242739 1099511627776 484659844186403 75654096572383232 Bool.true

noncomputable abbrev qz912 := (@HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast 26) qz17)

noncomputable def ep721 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 27) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz14 26) qz912) Bool.false 131746312813 1099511627776 484779836025633 75654096572383232 Bool.false 120426242739 1099511627776 484659844186403 75654096572383232

noncomputable def ep722 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz14 26) qz912 Bool.false 70796122843 274877906944 236311181883243 37827048286191616 Bool.true 33078442327 1099511627776 472501680485713 75654096572383232 Bool.true

noncomputable abbrev qz913 := (@HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast 25) qz17)

noncomputable def ep723 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz14 26) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz14 25) qz913) Bool.false 70796122843 274877906944 236311181883243 37827048286191616 Bool.true 33078442327 1099511627776 472501680485713 75654096572383232

noncomputable def ep724 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz14 25) qz913 Bool.false 82834314697 1099511627776 460210098128287 75654096572383232 Bool.true 15465575669 137438953472 115031352119321 18913524143095808 Bool.false

noncomputable abbrev qz914 := (@Nat.cast Real Real.instNatCast 25)

noncomputable abbrev qz361 := (@Inv.inv Real Real.instInv (Real.sqrt qz914))

noncomputable abbrev qz362 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 25 1)))

noncomputable def ep725 := @Enclosure.Complex.IsNear.of_eq qz913 (Complex.mk (@HMul.hMul Real Real Real qz0 qz361 (Real.cos qz362)) (@HMul.hMul Real Real Real qz0 qz361 (@Neg.neg Real Real.instNeg (Real.sin qz362)))) Bool.false 200350176675 1099511627776 12412265638199 75654096572383232 Bool.false 90646163025 1099511627776 12376272008429 75654096572383232 (BSN.cpow_neg_s_mk qz11 111131 1000 25 (@Eq.refl Real qz11) rfl)

noncomputable abbrev qz915 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 25) qz267)

noncomputable def ep726 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz914) 5242881 1048576 1 1048576 104857 104858 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz914) (Real.sqrt qz915) Bool.false 5242881 1048576 1 1048576 (BSN.sqrt_natCast_div_one 25) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz915) Bool.false 5242881 1048576 1 1048576 5242881 1048576 1 1048576 (BSN.sqrt_enclosure 25 1 2621440 2621441 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep727 := BSN.log_dyadic_bound 9 41 5 4 7545754341519345 524288 137614 124828057765224 4519905705 233982 50 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 9) (BSN.artanhQ 41) 0 4 124828057765224 7545754341519345 4519905705 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz363 := (Real.log (Enclosure.sfrac Bool.false 25 1))

noncomputable def ep728 := @Enclosure.Real.IsNear.mulLit_ff qz11 qz363 111131 1000 0 1 3624129903009015 1125899906842624 125000000068807 17201750000000000000 80550636050258969193 225179981368524800 13891375007646590717 17201750000000000000000 qz271 (BSN.isNear_log_sfrac 25 1 3624129903009015 1125899906842624 125000000068807 17201750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz915) Bool.false 60802810194841294602240 18889465931478580854784 1000000000550456 137614000000000000000 3624129903009015 1125899906842624 125000000068807 17201750000000000000 (BSN.log_rat_reduce_isNear 25 1 4 50 32 233982 524288 24973259072661432 36028797018963968 137614 1000000000000000 rfl rfl rfl rfl (ep727 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep729 := nat_lit 2359824967363086442008053231508639839747149526053445753157047493658499700817920

noncomputable def ep730 := nat_lit 1344813171271949793571277499929539235039388660351998439159892467000289591296

noncomputable def ep731 := nat_lit 6178316645578405143688643061808456516766756415166073736986008371778070176137216

noncomputable def ep732 := BSN.sin_dyadic_bound_f 2460836412 2147483648 3 2 1048576 275497 ep729 ep97 ep730 ep731 ep100 ep730 955345 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2460836412) qz268 0 2 ep729 ep97 ep730 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2460836412) qz269 0 2 ep731 ep100 ep730 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz610 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 46886641) (@Nat.cast Real Real.instNatCast 131072))

noncomputable def ep733 := @Enclosure.Real.IsNear.cos_image qz362 qz610 Bool.false 46886641 131072 53 65536 Bool.false 955345 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz362 Bool.false 80550636050258969193 225179981368524800 13891375007646590717 17201750000000000000000 46886641 131072 53 65536 (ep728 rfl) rfl) (Enclosure.sfrac_false_div 46886641 131072) (BSN.cos_reduce3 qz610 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 21645745995691098898432) qz563) 226375608064910080 72057594037927936 Bool.false 955345 1048576 56 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q3 46886641 131072 226375608064910080 72057594037927936 56 21645745995691098898432 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 955345 1048576 21645745995691098898432 18889465931478580854784 2460836412 2147483648 275497 275228 (ep732 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep734 := nat_lit 1311611565500057778801616807504768595075100576100959639949097448684499962494976

noncomputable def ep735 := nat_lit 3932145070157629436817707867514446706755222950982174922968972561119499308302336

noncomputable def ep736 := BSN.cos_dyadic_bound_f 2460836412 2147483648 3 2 1048576 275497 ep734 ep104 ep730 ep735 ep106 ep730 432235 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2460836412) qz272 0 2 ep734 ep104 ep730 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2460836412) qz273 0 2 ep735 ep106 ep730 rfl rfl rfl rfl) rfl rfl

noncomputable def ep737 := @Enclosure.Real.IsNear.sin_image qz362 qz610 Bool.false 46886641 131072 53 65536 Bool.true 432235 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz362 Bool.false 80550636050258969193 225179981368524800 13891375007646590717 17201750000000000000000 46886641 131072 53 65536 (ep728 rfl) rfl) (Enclosure.sfrac_false_div 46886641 131072) (BSN.sin_reduce3 qz610 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 21645745995691098898432) qz563) 226375608064910080 72057594037927936 Bool.false 432235 1048576 56 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q3 46886641 131072 226375608064910080 72057594037927936 56 21645745995691098898432 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 432235 1048576 21645745995691098898432 18889465931478580854784 2460836412 2147483648 275497 275228 (ep736 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz611 := (@Enclosure.Real.IsNear.recentre' qz361 Bool.false 209715 1048576 1 1048576 209715 1048576 1 1048576 (ep726 rfl rfl) rfl)

noncomputable def ep738 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz361 (Real.cos qz362)) (@HMul.hMul Real Real Real qz0 qz361 (@Neg.neg Real Real.instNeg (Real.sin qz362))) Bool.false 200350176675 1099511627776 12412265638199 75654096572383232 Bool.false 90646163025 1099511627776 12376272008429 75654096572383232 (@Enclosure.Real.IsNear.mulLit_ff qz361 (Real.cos qz362) 209715 1048576 1 1048576 955345 1048576 3679539 4509335552 200350176675 1099511627776 12412265638199 75654096572383232 qz611 (@Enclosure.Real.IsNear.recentre' (Real.cos qz362) Bool.false 955345 1048576 7359078 9018671104 955345 1048576 3679539 4509335552 (ep733 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz361 (@Neg.neg Real Real.instNeg (Real.sin qz362)) 209715 1048576 1 1048576 432235 1048576 3679539 4509335552 90646163025 1099511627776 12376272008429 75654096572383232 qz611 (@Enclosure.Real.IsNear.neg (Real.sin qz362) Bool.true 432235 1048576 3679539 4509335552 (@Enclosure.Real.IsNear.recentre' (Real.sin qz362) Bool.true 432235 1048576 7359078 9018671104 432235 1048576 3679539 4509335552 (ep737 rfl rfl) rfl)) rfl)

noncomputable def ep739 := @ep724 200350176675 1099511627776 12412265638199 75654096572383232 Bool.false 90646163025 1099511627776 12376272008429 75654096572383232 Bool.false 311364641069346347548672 70796122843 274877906944 236311181883243 37827048286191616 Bool.true 4546266495906788409344 33078442327 1099511627776 472501680485713 75654096572383232 EMRow35.d9 (ep725 ep738) rfl rfl

noncomputable abbrev qz916 := (@Nat.cast Real Real.instNatCast 26)

noncomputable abbrev qz364 := (@Inv.inv Real Real.instInv (Real.sqrt qz916))

noncomputable abbrev qz365 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 26 1)))

noncomputable def ep740 := @Enclosure.Complex.IsNear.of_eq qz912 (Complex.mk (@HMul.hMul Real Real Real qz0 qz364 (Real.cos qz365)) (@HMul.hMul Real Real Real qz0 qz364 (@Neg.neg Real Real.instNeg (Real.sin qz365)))) Bool.true 151438178559 1099511627776 12157472259147 75654096572383232 Bool.false 76752342533 549755813888 6079081850345 37827048286191616 (BSN.cpow_neg_s_mk qz11 111131 1000 26 (@Eq.refl Real qz11) rfl)

noncomputable abbrev qz917 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26) qz267)

noncomputable def ep741 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz916) 5346709 1048576 1 1048576 102821 102822 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz916) (Real.sqrt qz917) Bool.false 5346709 1048576 1 1048576 (BSN.sqrt_natCast_div_one 26) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz917) Bool.false 5346709 1048576 1 1048576 5346709 1048576 1 1048576 (BSN.sqrt_enclosure 26 1 2673354 2673355 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep742 := BSN.log_dyadic_bound 10 42 5 4 9150106136613120 524288 137614 179034245376000 10500000000 254545 52 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 10) (BSN.artanhQ 42) 0 4 179034245376000 9150106136613120 10500000000 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz366 := (Real.log (Enclosure.sfrac Bool.false 26 1))

noncomputable def ep743 := @Enclosure.Real.IsNear.mulLit_ff qz11 qz366 111131 1000 0 1 3668288609262839 1125899906842624 125000000068807 17201750000000000000 407660581435988560909 1125899906842624000 13891375007646590717 17201750000000000000000 qz271 (BSN.isNear_log_sfrac 26 1 3668288609262839 1125899906842624 125000000068807 17201750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz917) Bool.false 61543670347942250676224 18889465931478580854784 1000000000550456 137614000000000000000 3668288609262839 1125899906842624 125000000068807 17201750000000000000 (BSN.log_rat_reduce_isNear 26 1 4 52 32 254545 524288 24973259072661432 36028797018963968 137614 1000000000000000 rfl rfl rfl rfl (ep742 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep744 := nat_lit 299320029736905653743239003517035935856841861138953696140028338096560943190625

noncomputable def ep745 := nat_lit 70147224008393941840905313251692495367183927036513149353674333425250390625

noncomputable def ep746 := nat_lit 897819794762700173346035199924604422579791215562788062121377665622832328790625

noncomputable def ep747 := BSN.cos_dyadic_bound_f 1701184085 2147483648 3 2 1048576 275497 ep744 ep104 ep745 ep746 ep106 ep745 736413 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1701184085) qz272 0 2 ep744 ep104 ep745 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1701184085) qz273 0 2 ep746 ep106 ep745 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz918 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 189831751) qz289)

noncomputable def ep748 := @Enclosure.Real.IsNear.cos_image qz365 qz918 Bool.false 189831751 524288 53 65536 Bool.true 736413 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz365 Bool.false 407660581435988560909 1125899906842624000 13891375007646590717 17201750000000000000000 189831751 524288 53 65536 (ep743 rfl) rfl) (Enclosure.sfrac_false_div 189831751 524288) (BSN.cos_reduce2 qz918 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 59855093872858520092672) qz290) 226375608064910080 72057594037927936 Bool.false 736413 1048576 57 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q2 189831751 524288 226375608064910080 72057594037927936 57 59855093872858520092672 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 736413 1048576 59855093872858520092672 75557863725914323419136 1701184085 2147483648 275497 275228 (ep747 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep749 := nat_lit 8375393961384380266154596776148200625

noncomputable def ep750 := BSN.sin_dyadic_bound_f 1701184085 2147483648 2 1 1048576 275497 ep749 ep178 ep749 ep749 ep179 ep749 746462 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1701184085) qz268 0 1 ep749 ep178 ep749 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1701184085) qz269 0 1 ep749 ep179 ep749 rfl rfl rfl rfl) rfl rfl

noncomputable def ep751 := @Enclosure.Real.IsNear.sin_image qz365 qz918 Bool.false 189831751 524288 53 65536 Bool.true 746462 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz365 Bool.false 407660581435988560909 1125899906842624000 13891375007646590717 17201750000000000000000 189831751 524288 53 65536 (ep743 rfl) rfl) (Enclosure.sfrac_false_div 189831751 524288) (BSN.sin_reduce2 qz918 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 59855093872858520092672) qz290) 226375608064910080 72057594037927936 Bool.false 746462 1048576 57 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q2 189831751 524288 226375608064910080 72057594037927936 57 59855093872858520092672 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 746462 1048576 59855093872858520092672 75557863725914323419136 1701184085 2147483648 275497 275228 (ep750 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz612 := (@Enclosure.Real.IsNear.recentre' qz364 Bool.false 205643 1048576 1 1048576 205643 1048576 1 1048576 (ep741 rfl rfl) rfl)

noncomputable def ep752 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz364 (Real.cos qz365)) (@HMul.hMul Real Real Real qz0 qz364 (@Neg.neg Real Real.instNeg (Real.sin qz365))) Bool.true 151438178559 1099511627776 12157472259147 75654096572383232 Bool.false 76752342533 549755813888 6079081850345 37827048286191616 (@Enclosure.Real.IsNear.mulLit_ft qz364 (Real.cos qz365) 205643 1048576 1 1048576 736413 1048576 3679539 4509335552 151438178559 1099511627776 12157472259147 75654096572383232 qz612 (@Enclosure.Real.IsNear.recentre' (Real.cos qz365) Bool.true 736413 1048576 7359078 9018671104 736413 1048576 3679539 4509335552 (ep748 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz364 (@Neg.neg Real Real.instNeg (Real.sin qz365)) 205643 1048576 1 1048576 373231 524288 3679539 4509335552 76752342533 549755813888 6079081850345 37827048286191616 qz612 (@Enclosure.Real.IsNear.neg (Real.sin qz365) Bool.true 373231 524288 3679539 4509335552 (@Enclosure.Real.IsNear.recentre' (Real.sin qz365) Bool.true 746462 1048576 7359078 9018671104 373231 524288 3679539 4509335552 (ep751 rfl rfl) rfl)) rfl)

noncomputable def ep753 := @ep722 151438178559 1099511627776 12157472259147 75654096572383232 Bool.false 76752342533 549755813888 6079081850345 37827048286191616 Bool.false 36214150713626928873472 131746312813 1099511627776 484779836025633 75654096572383232 Bool.false 66205027090452795359232 120426242739 1099511627776 484659844186403 75654096572383232 (ep723 (BSN.head_sum_c_succ qz14 25 26 rfl rfl) (ep739 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep740 ep752) rfl rfl

noncomputable abbrev qz919 := (@Nat.cast Real Real.instNatCast 27)

noncomputable abbrev qz367 := (@Inv.inv Real Real.instInv (Real.sqrt qz919))

noncomputable abbrev qz368 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 27 1)))

noncomputable def ep754 := @Enclosure.Complex.IsNear.of_eq qz911 (Complex.mk (@HMul.hMul Real Real Real qz0 qz367 (Real.cos qz368)) (@HMul.hMul Real Real Real qz0 qz367 (@Neg.neg Real Real.instNeg (Real.sin qz368)))) Bool.true 14311383281 274877906944 2975003604433 18913524143095808 Bool.true 101855421863 549755813888 5974977200359 37827048286191616 (BSN.cpow_neg_s_mk qz11 111131 1000 27 (@Eq.refl Real qz11) rfl)

noncomputable abbrev qz920 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 27) qz267)

noncomputable def ep755 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz919) 5448561 1048576 1 1048576 100899 100900 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz919) (Real.sqrt qz920) Bool.false 5448561 1048576 1 1048576 (BSN.sqrt_natCast_div_one 27) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz920) Bool.false 5448561 1048576 1 1048576 5448561 1048576 1 1048576 (BSN.sqrt_enclosure 27 1 2724280 2724281 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep756 := BSN.log_dyadic_bound 11 43 5 4 11045349262332945 524288 137614 250863800262504 22507682505 274332 54 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 11) (BSN.artanhQ 43) 0 4 250863800262504 11045349262332945 22507682505 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz369 := (Real.log (Enclosure.sfrac Bool.false 27 1))

noncomputable def ep757 := @Enclosure.Real.IsNear.mulLit_ff qz11 qz369 111131 1000 0 1 3710780868205815 1125899906842624 125000000068807 17201750000000000000 82476557732916085353 225179981368524800 13891375007646590717 17201750000000000000000 qz271 (BSN.isNear_log_sfrac 27 1 3710780868205815 1125899906842624 125000000068807 17201750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz920) Bool.false 62256572154556490711040 18889465931478580854784 1000000000550456 137614000000000000000 3710780868205815 1125899906842624 125000000068807 17201750000000000000 (BSN.log_rat_reduce_isNear 27 1 4 54 32 274332 524288 24973259072661432 36028797018963968 137614 1000000000000000 rfl rfl rfl rfl (ep756 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep758 := nat_lit 119783799219864110469430587318066241

noncomputable def ep759 := BSN.sin_dyadic_bound_f 588300911 2147483648 2 1 1048576 275497 ep758 ep178 ep758 ep758 ep179 ep758 283676 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 588300911) qz268 0 1 ep758 ep178 ep758 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 588300911) qz269 0 1 ep758 ep179 ep758 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz613 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 48007675) (@Nat.cast Real Real.instNatCast 131072))

noncomputable def ep760 := @Enclosure.Real.IsNear.cos_image qz368 qz613 Bool.false 48007675 131072 53 65536 Bool.true 283676 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz368 Bool.false 82476557732916085353 225179981368524800 13891375007646590717 17201750000000000000000 48007675 131072 53 65536 (ep757 rfl) rfl) (Enclosure.sfrac_false_div 48007675 131072) (BSN.cos_reduce1 qz613 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 5174749543416746475520) qz563) 226375608064910080 72057594037927936 Bool.false 283676 1048576 58 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q1 48007675 131072 226375608064910080 72057594037927936 58 5174749543416746475520 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 283676 1048576 5174749543416746475520 18889465931478580854784 588300911 2147483648 275497 275228 (ep759 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep761 := BSN.cos_dyadic_bound_f 588300911 2147483648 2 1 1048576 275497 ep758 ep118 ep758 ep758 ep119 ep758 1009474 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 588300911) qz272 0 1 ep758 ep118 ep758 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 588300911) qz273 0 1 ep758 ep119 ep758 rfl rfl rfl rfl) rfl rfl

noncomputable def ep762 := @Enclosure.Real.IsNear.sin_image qz368 qz613 Bool.false 48007675 131072 53 65536 Bool.false 1009474 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz368 Bool.false 82476557732916085353 225179981368524800 13891375007646590717 17201750000000000000000 48007675 131072 53 65536 (ep757 rfl) rfl) (Enclosure.sfrac_false_div 48007675 131072) (BSN.sin_reduce1 qz613 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 5174749543416746475520) qz563) 226375608064910080 72057594037927936 Bool.false 1009474 1048576 58 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q1 48007675 131072 226375608064910080 72057594037927936 58 5174749543416746475520 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1009474 1048576 5174749543416746475520 18889465931478580854784 588300911 2147483648 275497 275228 (ep761 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz614 := (@Enclosure.Real.IsNear.recentre' qz367 Bool.false 201799 1048576 1 1048576 201799 1048576 1 1048576 (ep755 rfl rfl) rfl)

noncomputable def ep763 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz367 (Real.cos qz368)) (@HMul.hMul Real Real Real qz0 qz367 (@Neg.neg Real Real.instNeg (Real.sin qz368))) Bool.true 14311383281 274877906944 2975003604433 18913524143095808 Bool.true 101855421863 549755813888 5974977200359 37827048286191616 (@Enclosure.Real.IsNear.mulLit_ft qz367 (Real.cos qz368) 201799 1048576 1 1048576 70919 262144 3679539 4509335552 14311383281 274877906944 2975003604433 18913524143095808 qz614 (@Enclosure.Real.IsNear.recentre' (Real.cos qz368) Bool.true 283676 1048576 7359078 9018671104 70919 262144 3679539 4509335552 (ep760 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz367 (@Neg.neg Real Real.instNeg (Real.sin qz368)) 201799 1048576 1 1048576 504737 524288 3679539 4509335552 101855421863 549755813888 5974977200359 37827048286191616 qz614 (@Enclosure.Real.IsNear.neg (Real.sin qz368) Bool.false 504737 524288 3679539 4509335552 (@Enclosure.Real.IsNear.recentre' (Real.sin qz368) Bool.false 1009474 1048576 7359078 9018671104 504737 524288 3679539 4509335552 (ep762 rfl rfl) rfl)) rfl)

noncomputable def ep764 := @ep720 14311383281 274877906944 2975003604433 18913524143095808 Bool.true 101855421863 549755813888 5974977200359 37827048286191616 Bool.false 20478618386608387260416 74500779689 1099511627776 5984094583655 911495139426304 Bool.true 45786193599945513107456 83284600987 1099511627776 5983250585387 911495139426304 (ep721 (BSN.head_sum_c_succ qz14 26 27 rfl rfl) (ep753 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep754 ep763) rfl rfl

noncomputable def ep765 := @Enclosure.Complex.IsNear.mul qz45 (@HAdd.hAdd Complex Complex Complex qz15 qz46 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz49 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1))))) Bool.false ep711 ep496 ep712 ep498 Bool.false

noncomputable def ep766 := nat_lit 42741027938429375247459323723991

noncomputable def ep767 := nat_lit 486683993944532281710346240000000

noncomputable def ep768 := nat_lit 146371822232972577743967253005327

noncomputable def ep769 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re qz45) (Complex.re (@HAdd.hAdd Complex Complex Complex qz15 qz46 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz49 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 (Complex.im qz45) (Complex.im (@HAdd.hAdd Complex Complex Complex qz15 qz46 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz49 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1))))))) ep766 ep767 ep768

noncomputable def ep770 := nat_lit 1875286871995120231628052449198080000

noncomputable def ep771 := nat_lit 370903751225072668615825094624622629

noncomputable def ep772 := nat_lit 10787661269003360164496247536391391153

noncomputable def ep773 := nat_lit 1129973654474060195004670842155121585863425722268469047632855040000000

noncomputable def ep774 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz45) (Complex.re (@HAdd.hAdd Complex Complex Complex qz15 qz46 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz49 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))))) 95818349879 549755813888 5859670251125 37827048286191616 3122441535956537057703

noncomputable abbrev qz921 := (@Nat.cast Real Real.instNatCast 28)

noncomputable abbrev qz370 := (@Inv.inv Real Real.instInv (Real.sqrt qz921))

noncomputable abbrev qz371 := (@HMul.hMul Real Real Real qz0 qz11 (Real.log (Enclosure.sfrac Bool.false 28 1)))

noncomputable abbrev qz922 := (@Neg.neg Real Real.instNeg (Real.sin qz371))

noncomputable def ep775 := @Enclosure.Complex.IsNear.of_eq qz45 (Complex.mk (@HMul.hMul Real Real Real qz0 qz370 (Real.cos qz371)) (@HMul.hMul Real Real Real qz0 qz370 qz922)) Bool.false 95818349879 549755813888 5859670251125 37827048286191616 Bool.false 80321606953 1099511627776 11680689202105 75654096572383232 (BSN.cpow_neg_s_mk qz11 111131 1000 28 (@Eq.refl Real qz11) rfl)

noncomputable abbrev qz923 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 28) qz267)

noncomputable def ep776 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz921) 5548543 1048576 1 1048576 99081 99082 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz921) (Real.sqrt qz923) Bool.false 5548543 1048576 1 1048576 (BSN.sqrt_natCast_div_one 28) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz923) Bool.false 5548543 1048576 1 1048576 5548543 1048576 1 1048576 (BSN.sqrt_enclosure 28 1 2774271 2774272 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep777 := BSN.log_dyadic_bound 12 44 5 4 13275571325829120 524288 137614 344661139390464 45148078080 293399 56 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 12) (BSN.artanhQ 44) 0 4 344661139390464 13275571325829120 45148078080 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz372 := (Real.log (Enclosure.sfrac Bool.false 28 1))

noncomputable def ep778 := @Enclosure.Real.IsNear.mulLit_ff qz11 qz372 111131 1000 0 1 3751726938922231 1125899906842624 125000000068807 17201750000000000000 416933166449366453261 1125899906842624000 13891375007646590717 17201750000000000000000 qz271 (BSN.isNear_log_sfrac 28 1 3751726938922231 1125899906842624 125000000068807 17201750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz923) Bool.false 62943533227317076688896 18889465931478580854784 1000000000550456 137614000000000000000 3751726938922231 1125899906842624 125000000068807 17201750000000000000 (BSN.log_rat_reduce_isNear 28 1 4 56 32 293399 524288 24973259072661432 36028797018963968 137614 1000000000000000 rfl rfl rfl rfl (ep777 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep779 := nat_lit 2599104888723843840002191007427931079775965121438816623270838357689870646199905

noncomputable def ep780 := nat_lit 1631172252050379984001253321728256240525489274868956645318765797020372780641

noncomputable def ep781 := nat_lit 6804538524916271346698307752171307079785724525894731893045489125516390136497761

noncomputable def ep782 := BSN.sin_dyadic_bound_f 2520939819 2147483648 3 2 1048576 275497 ep779 ep97 ep780 ep781 ep100 ep780 967066 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2520939819) qz268 0 2 ep779 ep97 ep780 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2520939819) qz269 0 2 ep781 ep100 ep780 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz924 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 194149635) qz289)

noncomputable def ep783 := @Enclosure.Real.IsNear.cos_image qz371 qz924 Bool.false 194149635 524288 847 1048576 Bool.false 967066 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz371 Bool.false 416933166449366453261 1125899906842624000 13891375007646590717 17201750000000000000000 194149635 524288 847 1048576 (ep778 rfl) rfl) (Enclosure.sfrac_false_div 194149635 524288) (BSN.cos_reduce3 qz924 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 88697684616909495992320) qz290) 226375608064910080 72057594037927936 Bool.false 967066 1048576 58 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q3 194149635 524288 226375608064910080 72057594037927936 58 88697684616909495992320 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 967066 1048576 88697684616909495992320 75557863725914323419136 2520939819 2147483648 275497 275228 (ep782 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep784 := nat_lit 1444672125847491191105217783380729824871325284921506549215051872404159413569121

noncomputable def ep785 := nat_lit 4330754033038372813347650843498732962132924876214781734354518085618437495146081

noncomputable def ep786 := BSN.cos_dyadic_bound_f 2520939819 2147483648 3 2 1048576 275497 ep784 ep104 ep780 ep785 ep106 ep780 405331 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2520939819) qz272 0 2 ep784 ep104 ep780 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2520939819) qz273 0 2 ep785 ep106 ep780 rfl rfl rfl rfl) rfl rfl

noncomputable def ep787 := @Enclosure.Real.IsNear.sin_image qz371 qz924 Bool.false 194149635 524288 847 1048576 Bool.true 405331 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz371 Bool.false 416933166449366453261 1125899906842624000 13891375007646590717 17201750000000000000000 194149635 524288 847 1048576 (ep778 rfl) rfl) (Enclosure.sfrac_false_div 194149635 524288) (BSN.sin_reduce3 qz924 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 88697684616909495992320) qz290) 226375608064910080 72057594037927936 Bool.false 405331 1048576 58 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q3 194149635 524288 226375608064910080 72057594037927936 58 88697684616909495992320 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 405331 1048576 88697684616909495992320 75557863725914323419136 2520939819 2147483648 275497 275228 (ep786 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz615 := (@Enclosure.Real.IsNear.recentre' qz370 Bool.false 198163 1048576 1 1048576 198163 1048576 1 1048576 (ep776 rfl rfl) rfl)

noncomputable def ep788 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz370 (Real.cos qz371)) (@HMul.hMul Real Real Real qz0 qz370 qz922) Bool.false 95818349879 549755813888 5859670251125 37827048286191616 Bool.false 80321606953 1099511627776 11680689202105 75654096572383232 (@Enclosure.Real.IsNear.mulLit_ff qz370 (Real.cos qz371) 198163 1048576 1 1048576 483533 524288 58803817 72149368832 95818349879 549755813888 5859670251125 37827048286191616 qz615 (@Enclosure.Real.IsNear.recentre' (Real.cos qz371) Bool.false 967066 1048576 117607634 144298737664 483533 524288 58803817 72149368832 (ep783 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz370 qz922 198163 1048576 1 1048576 405331 1048576 58803817 72149368832 80321606953 1099511627776 11680689202105 75654096572383232 qz615 (@Enclosure.Real.IsNear.neg (Real.sin qz371) Bool.true 405331 1048576 58803817 72149368832 (@Enclosure.Real.IsNear.recentre' (Real.sin qz371) Bool.true 405331 1048576 117607634 144298737664 405331 1048576 58803817 72149368832 (ep787 rfl rfl) rfl)) rfl)

noncomputable def ep789 := @ep774 6196911195023360000000 0 1 ep766 ep767 ep768 ep770 (@Enclosure.Complex.IsNear.re_isNear qz45 Bool.false 95818349879 549755813888 5859670251125 37827048286191616 Bool.false 80321606953 1099511627776 11680689202105 75654096572383232 (ep775 ep788))

noncomputable def ep790 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz15 qz46 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz49 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1))))) Bool.false 3122441535956537057703 6196911195023360000000 0 1 Bool.false

noncomputable def ep791 := nat_lit 32324132410532360285144651

noncomputable def ep792 := nat_lit 195202702643235840000000000

noncomputable def ep793 := @Enclosure.Complex.IsNear.addLitP qz46 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz49 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) Bool.false 12322349161 24700698322 0 1 Bool.true 3111668000

noncomputable def ep794 := @ep793 12350349161 0 1 Bool.false 2510907023 501760000000 0 1 Bool.false 6599442106611091 15805440000000000 0 1 Bool.false 6244883071913074115406 3122441535956537057703 6196911195023360000000 0 1 Bool.false ep791 ep791 ep792 0 1

noncomputable abbrev qz50 := (@HDiv.hDiv Complex Complex Complex qz352 (@Nat.cast Complex Complex.instNatCast 28) (@HSub.hSub Complex Complex Complex qz595 qz261 (1 : Complex)))

noncomputable def ep795 := @Enclosure.Complex.IsNear.addLitP qz50 qz26 Bool.true 56000000 49401396644 0 1 Bool.true 12446672000 49401396644 0 1

noncomputable def ep796 := @Enclosure.Complex.IsNear.of_eq qz50 (Complex.mk (Enclosure.sfrac Bool.true 56000000 49401396644) (Enclosure.sfrac Bool.true 12446672000 49401396644)) Bool.true 56000000 49401396644 0 1 Bool.true 12446672000 49401396644 0 1

noncomputable def ep797 := @ep795 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 49289396644 12322349161 24700698322 0 1 Bool.true 12446672000 3111668000 12350349161 0 1 (ep796 (BSN.N_div_s_sub_one_mk qz11 111131 1000 28 (@Eq.refl Real qz11) rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 56000000 49401396644) (Enclosure.sfrac Bool.true 12446672000 49401396644) Bool.true 56000000 49401396644 0 1 Bool.true 12446672000 49401396644 0 1 (Enclosure.Real.IsNear.const Bool.true 56000000 49401396644) (Enclosure.Real.IsNear.const Bool.true 12446672000 49401396644))) qz357 rfl

noncomputable abbrev qz51 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)))

noncomputable abbrev qz373 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz49 3))

noncomputable def ep798 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz49 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz15 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz49 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3))) qz373)) Bool.false 2510907023 501760000000 0 1

noncomputable def ep799 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz49 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3))) qz373) Bool.false 1 672 0 1 Bool.false

noncomputable def ep800 := @ep799 111131 336000 0 1 Bool.false 5292721069 1505280000000 0 1 Bool.false 1371839866611091 15805440000000000 0 1 Bool.false 5061988558368 2510907023 501760000000 0 1 Bool.false 2217412547821326576000 6599442106611091 15805440000000000 0

noncomputable abbrev qz52 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)))

noncomputable abbrev qz374 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz49 1))

noncomputable def ep801 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz49 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz15 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz49 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1))) qz374)) Bool.false 1 672 0 1

noncomputable def ep802 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz49 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1))) qz374) Bool.false 0 1 0 1 Bool.false

noncomputable def ep803 := @ep802 0 1 0 1 Bool.false 1 672 0 1 Bool.false 111131 336000 0 1 Bool.false 1 1 672 0 1 Bool.false 111131 111131 336000 0

noncomputable def ep804 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz49 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (Complex.mk qz264 qz264) Bool.false 0 1 0 1 Bool.false

noncomputable def ep805 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1))) qz374 Bool.false 1 672 0 1 Bool.false 111131 336000 0 1

noncomputable def ep806 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz374)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz374)) 1 672 0 1 0 1 0

noncomputable def ep807 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz374) 1 24 0 1 1 28 0 1 1

noncomputable def ep808 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep809 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep810 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz264) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 1 1 6 2 Bool.false BSN.bern_real_1 EMRow35.d10 rfl) qz607

noncomputable def ep811 := @ep809 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep810) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 111131 1000 0 1 ep449)

noncomputable def ep812 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 111131 1000 0 1 0 1 0

noncomputable def ep813 := @ep812 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep810) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 111131 1000 0 1 ep449)

noncomputable def ep814 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1)))) 111131 12000 0 1 0 1 0 1 111131

noncomputable def ep815 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 111131 1000 0 1 111131 12000 0

noncomputable def ep816 := @ep815 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep810) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 111131 1000 0 1 ep449)

noncomputable def ep817 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep818 := @ep817 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep810) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 111131 1000 0 1 ep449)

noncomputable def ep819 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 111131 12000 0 1 (@ep808 1 24 0 1 (ep811 rfl) (ep813 rfl) rfl rfl) (@ep814 111131 12000 0 1 (ep816 rfl) (ep818 rfl) rfl rfl)

noncomputable def ep820 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 111131 12000 0 1 ep819

noncomputable abbrev qz375 := (@Enclosure.Complex.IsNear.of_eq (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz49 1)) (Complex.mk (Enclosure.sfrac Bool.false 1 28) qz554) Bool.false 1 28 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 28 1 28 EMRow35.d11 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 28) qz554 Bool.false 1 28 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 28) qz820))

noncomputable def ep821 := @ep807 672 0 1 ep820 (@Enclosure.Complex.IsNear.re_isNear qz374 Bool.false 1 28 0 1 Bool.false 0 1 0 1 qz375)

noncomputable def ep822 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz374) 111131 12000 0 1 0 1 0 1 0

noncomputable def ep823 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 111131 12000 0 1 ep819

noncomputable def ep824 := @ep822 1 0 1 ep823 (@Enclosure.Complex.IsNear.im_isNear qz374 Bool.false 1 28 0 1 Bool.false 0 1 0 1 qz375)

noncomputable def ep825 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz374)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz374)) 0 1 0 1 111131 336000 0

noncomputable def ep826 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz374) 1 24 0 1 0 1 0 1 0

noncomputable def ep827 := @ep826 1 0 1 ep820 (@Enclosure.Complex.IsNear.im_isNear qz374 Bool.false 1 28 0 1 Bool.false 0 1 0 1 qz375)

noncomputable def ep828 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz374) 111131 12000 0 1 1 28 0 1 111131

noncomputable def ep829 := @ep828 336000 0 1 ep823 (@Enclosure.Complex.IsNear.re_isNear qz374 Bool.false 1 28 0 1 Bool.false 0 1 0 1 qz375)

noncomputable def ep830 := @ep803 1 (@ep804 0 1 0 1 (BSN.bern_sum_base qz14 28) qz360) (ep805 (@ep806 1 1 1 672 0 1 (ep821 rfl) (ep824 rfl) rfl rfl) (@ep825 1 111131 111131 336000 0 1 (ep827 rfl) (ep829 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep831 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3))) qz373 Bool.false 5292721069 1505280000000 0 1 Bool.false 1371839866611091 15805440000000000 0 1

noncomputable def ep832 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.re qz373)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.im qz373)) 5292721069 1505280000000 0 1 0 1 0

noncomputable def ep833 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.re qz373) 37049047483 480000000 0 1 1 21952 0 1 5292721069

noncomputable def ep834 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3)))) 37049047483 480000000 0 1 0 1 0 1 37049047483

noncomputable def ep835 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 111147142449 2000000 0 1 37049047483 480000000 0

noncomputable def ep836 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (Complex.mk (Enclosure.sfrac Bool.true 1 720) qz264) Bool.true 1 720 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 2 1 30 24 Bool.true BSN.bern_real_2 EMRow35.d12 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 1 720) qz264 Bool.true 1 720 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.true 1 720) qz274)

noncomputable def ep837 := @ep835 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep836) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 111147142449 2000000 0 1 Bool.true 1371839866611091 1000000000 0 1 EMRow35.d13)

noncomputable def ep838 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 1371839866611091 1000000000 0 1 0 1 0

noncomputable def ep839 := @ep838 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep836) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 111147142449 2000000 0 1 Bool.true 1371839866611091 1000000000 0 1 EMRow35.d13)

noncomputable def ep840 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3)))) 1371839866611091 720000000000 0 1 0 1 0 1 1371839866611091

noncomputable def ep841 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 1371839866611091 1000000000 0 1 1371839866611091 720000000000 0

noncomputable def ep842 := @ep841 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep836) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 111147142449 2000000 0 1 Bool.true 1371839866611091 1000000000 0 1 EMRow35.d13)

noncomputable def ep843 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 111147142449 2000000 0 1 0 1 0

noncomputable def ep844 := @ep843 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep836) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 111147142449 2000000 0 1 Bool.true 1371839866611091 1000000000 0 1 EMRow35.d13)

noncomputable def ep845 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 37049047483 480000000 0 1 Bool.false 1371839866611091 720000000000 0 1 (@ep834 37049047483 480000000 0 1 (ep837 rfl) (ep839 rfl) rfl rfl) (@ep840 1371839866611091 720000000000 0 1 (ep842 rfl) (ep844 rfl) rfl rfl)

noncomputable def ep846 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 37049047483 480000000 0 1 Bool.false 1371839866611091 720000000000 0 1 ep845

noncomputable abbrev qz376 := (@Enclosure.Complex.IsNear.of_eq (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz49 3)) (Complex.mk (Enclosure.sfrac Bool.false 1 21952) qz554) Bool.false 1 21952 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 28 3 21952 EMRow35.d14 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 21952) qz554 Bool.false 1 21952 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 21952) qz820))

noncomputable def ep847 := @ep833 1505280000000 0 1 ep846 (@Enclosure.Complex.IsNear.re_isNear qz373 Bool.false 1 21952 0 1 Bool.false 0 1 0 1 qz376)

noncomputable def ep848 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.im qz373) 1371839866611091 720000000000 0 1 0 1 0 1 0

noncomputable def ep849 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 37049047483 480000000 0 1 Bool.false 1371839866611091 720000000000 0 1 ep845

noncomputable def ep850 := @ep848 1 0 1 ep849 (@Enclosure.Complex.IsNear.im_isNear qz373 Bool.false 1 21952 0 1 Bool.false 0 1 0 1 qz376)

noncomputable def ep851 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.im qz373)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.re qz373)) 0 1 0 1 1371839866611091 15805440000000000 0

noncomputable def ep852 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.im qz373) 37049047483 480000000 0 1 0 1 0 1 0

noncomputable def ep853 := @ep852 1 0 1 ep846 (@Enclosure.Complex.IsNear.im_isNear qz373 Bool.false 1 21952 0 1 Bool.false 0 1 0 1 qz376)

noncomputable def ep854 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.re qz373) 1371839866611091 720000000000 0 1 1 21952 0 1 1371839866611091

noncomputable def ep855 := @ep854 15805440000000000 0 1 ep849 (@Enclosure.Complex.IsNear.re_isNear qz373 Bool.false 1 21952 0 1 Bool.false 0 1 0 1 qz376)

noncomputable def ep856 := @ep800 1 (@ep801 Bool.false 111131 336000 0 1 (BSN.bern_sum_succ qz14 28 0 1 1 rfl rfl) (ep830 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep831 (@ep832 1 5292721069 5292721069 1505280000000 0 1 (ep847 rfl) (ep850 rfl) rfl rfl) (@ep851 1 1371839866611091 1371839866611091 15805440000000000 0 1 (ep853 rfl) (ep855 rfl) rfl rfl)) rfl rfl rfl rfl

noncomputable def ep857 := ep794 (ep797 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep798 Bool.false 6599442106611091 15805440000000000 0 1 (BSN.bern_sum_succ qz14 28 1 2 3 rfl rfl) (ep856 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep858 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz45) (Complex.im (@HAdd.hAdd Complex Complex Complex qz15 qz46 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz49 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))))) 80321606953 1099511627776 11680689202105 75654096572383232 ep791

noncomputable def ep859 := @ep858 ep792 0 1 ep771 ep496 ep772 ep498 (@Enclosure.Complex.IsNear.im_isNear qz45 Bool.false 95818349879 549755813888 5859670251125 37827048286191616 Bool.false 80321606953 1099511627776 11680689202105 75654096572383232 (ep775 ep788))

noncomputable def ep860 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz15 qz46 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz49 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1))))) Bool.false 3122441535956537057703 6196911195023360000000 0 1 Bool.false

noncomputable def ep861 := nat_lit 442463575549644766064810625091906747

noncomputable def ep862 := nat_lit 1515270056635375257495940269856963859

noncomputable def ep863 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re qz45) (Complex.im (@HAdd.hAdd Complex Complex Complex qz15 qz46 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz49 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 (Complex.im qz45) (Complex.re (@HAdd.hAdd Complex Complex Complex qz15 qz46 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz49 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1))))))) ep861 ep706 ep862

noncomputable def ep864 := nat_lit 35828503112117512348542778144137

noncomputable def ep865 := nat_lit 973367987889064563420692480000000

noncomputable def ep866 := nat_lit 1042064832378619243214277697544709

noncomputable def ep867 := nat_lit 13394906228536573083057517494272000000

noncomputable def ep868 := nat_lit 979950388484231674912955504986796940116055097049246262162882560000000

noncomputable def ep869 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz45) (Complex.im (@HAdd.hAdd Complex Complex Complex qz15 qz46 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz49 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))))) 95818349879 549755813888 5859670251125 37827048286191616 ep791

noncomputable def ep870 := @ep869 ep792 0 1 ep861 ep706 ep862 ep708 (@Enclosure.Complex.IsNear.re_isNear qz45 Bool.false 95818349879 549755813888 5859670251125 37827048286191616 Bool.false 80321606953 1099511627776 11680689202105 75654096572383232 (ep775 ep788))

noncomputable def ep871 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz45) (Complex.re (@HAdd.hAdd Complex Complex Complex qz15 qz46 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz49 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))))) 80321606953 1099511627776 11680689202105 75654096572383232 3122441535956537057703

noncomputable def ep872 := @ep871 6196911195023360000000 0 1 ep864 ep865 ep866 ep867 (@Enclosure.Complex.IsNear.im_isNear qz45 Bool.false 95818349879 549755813888 5859670251125 37827048286191616 Bool.false 80321606953 1099511627776 11680689202105 75654096572383232 (ep775 ep788))

noncomputable abbrev qz925 := (ep857 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep873 := @ep765 ep713 ep706 ep714 ep708 (@ep769 ep770 ep771 ep496 ep772 ep498 ep773 ep711 ep496 ep712 ep498 (ep789 (@ep790 ep791 ep792 0 1 qz925) rfl) (ep859 (@ep860 ep791 ep792 0 1 qz925) rfl) rfl rfl) (@ep863 ep708 ep864 ep865 ep866 ep867 ep868 ep713 ep706 ep714 ep708 (ep870 (@ep860 ep791 ep792 0 1 qz925) rfl) (ep872 (@ep790 ep791 ep792 0 1 qz925) rfl) rfl rfl)

noncomputable def ep874 := @ep717 ep707 ep708 (@ep718 911495139426304 (BSN.head_sum_c_eq qz14 28) (ep719 (BSN.head_sum_c_succ qz14 27 28 rfl rfl) (ep764 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep873 rfl rfl rfl

noncomputable def ep875 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz14 2 28) Bool.false ep495 ep496 ep497 ep498 Bool.true ep705 ep706 ep707 ep708 (@ep709 ep498 Bool.true ep705 ep706 ep707 ep708 (BSN.zetaApproximant_eq_folded' qz14 2 28 rfl) (ep874 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep876 := @Enclosure.Real.IsNear.mulLit_ft (Real.sin (@HSub.hSub Real Real Real qz597 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz23 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz24 (@Nat.cast Complex Complex.instNatCast j))))) qz348)) (Complex.im (zetaApproximant qz14 2 28)) 187 1048576 12578597

noncomputable def ep877 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz597 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz23 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz24 (@Nat.cast Complex Complex.instNatCast j))))) qz348)) Bool.false 187 1048576 25157194

noncomputable def ep878 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz597 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz23 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz24 (@Nat.cast Complex Complex.instNatCast j))))) qz348) qz598 Bool.false 6794273 65536 179

noncomputable def ep879 := nat_lit 4640876058366692063992377651969191539915872646853624613813308060250784447190625

noncomputable def ep880 := nat_lit 13889129168330515138724335936435842476842026072026060274183865207821130840790625

noncomputable def ep881 := BSN.cos_dyadic_bound_f 3372874965 2147483648 3 2 1048576 275497 ep879 ep104 ep701 ep880 ep106 ep701 187 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3372874965) qz272 0 2 ep879 ep104 ep701 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3372874965) qz273 0 2 ep880 ep106 ep701 rfl rfl rfl rfl) rfl rfl

noncomputable def ep882 := @ep878 524288 Bool.false 187 1048576 1 137614 (@ep505 6794273 65536 179 524288 ep699 rfl) (Enclosure.sfrac_false_div 6794273 65536) (BSN.sin_reduce1 qz598 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14834060974482947833856) qz582) 226375608064910080 72057594037927936 Bool.false 187 1048576 16 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q1 6794273 65536 226375608064910080 72057594037927936 16 14834060974482947833856 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 187 1048576 14834060974482947833856 9444732965739290427392 3372874965 2147483648 275497 275228 (ep881 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep883 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz14 2 28) Bool.false ep495 ep496 ep497 ep498 Bool.true ep705 ep706 ep707 ep708 (@ep709 ep498 Bool.true ep705 ep706 ep707 ep708 (BSN.zetaApproximant_eq_folded' qz14 2 28 rfl) (ep874 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow35.d15 : Enclosure.Real.IsNear (hardyZApproximantEM 2 28 qz11) Bool.true ep478 ep479 ep480 ep481 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 2 28 qz11) ep482 Bool.true ep478 ep479 ep480 ep481 (@Eq.refl Real ep482) (@ep483 Bool.true ep478 ep479 ep480 ep481 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz597 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz23 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz24 (@Nat.cast Complex Complex.instNatCast j))))) qz348) (zetaApproximant qz14 2 28)) (@ep485 ep486 ep487 ep488 ep489 ep490 ep491 ep492 ep493 ep478 ep479 ep480 ep481 (@ep494 36074684416 ep495 ep496 ep497 ep498 ep484 ep486 ep487 ep488 (@ep499 72149368832 1048575 1048576 12578597 36074684416 (ep704 rfl rfl) rfl) ep875 rfl) (@ep876 36074684416 ep705 ep706 ep707 ep708 ep489 ep490 ep491 ep492 (@ep877 72149368832 187 1048576 12578597 36074684416 (ep882 rfl rfl) rfl) ep883 rfl) rfl rfl))

noncomputable abbrev qz616 := (@HAdd.hAdd Complex Complex Complex qz812 (@HAdd.hAdd Complex Complex Complex qz812 qz813 (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I (@HDiv.hDiv Complex Complex Complex qz814 (↑(Enclosure.sfrac Bool.false 113311 1000)) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 4))

noncomputable abbrev qz377 := (@HPow.hPow Complex Nat Complex qz543 qz616 3)

noncomputable abbrev qz53 := qz377

noncomputable def ep884 := Enclosure.Complex.IsNear qz53 Bool.true 653580268771 16000000 0 1 Bool.true 1430283136249231 8000000000 0 1

noncomputable abbrev qz378 := qz616

noncomputable abbrev qz54 := (@HPow.hPow Complex Nat Complex qz256 qz378 2)

noncomputable abbrev qz55 := qz378

noncomputable def ep885 := @Enclosure.Complex.IsNear.of_eq qz53 (@HMul.hMul Complex Complex Complex qz3 qz54 qz55) Bool.true 653580268771 16000000 0 1 Bool.true 1430283136249231 8000000000

noncomputable def ep886 := @Enclosure.Complex.IsNear.mul qz54 qz55 Bool.true 653580268771 16000000 0 1 Bool.true 1430283136249231 8000000000 0

noncomputable abbrev qz56 := (Complex.re qz378)

noncomputable abbrev qz57 := (Complex.im qz378)

noncomputable def ep887 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re qz54) qz56) (@HMul.hMul Real Real Real qz0 (Complex.im qz54) qz57) 217041256257 16000000 0 1 218269506257 8000000

noncomputable def ep888 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re qz54) qz56 12767132721 4000000 0 1 17000 4000 0 1

noncomputable def ep889 := @Enclosure.Complex.IsNear.re_isNear qz54 Bool.true 12767132721 4000000 0 1 Bool.false 1926287 4000 0 1

noncomputable abbrev qz379 := (@HPow.hPow Complex Nat Complex qz543 qz616 1)

noncomputable abbrev qz58 := qz379

noncomputable def ep890 := @Enclosure.Complex.IsNear.of_eq qz54 (@HMul.hMul Complex Complex Complex qz3 qz58 qz55) Bool.true 12767132721 4000000 0 1 Bool.false 1926287 4000

noncomputable def ep891 := @Enclosure.Complex.IsNear.mul qz58 qz55 Bool.true 12767132721 4000000 0 1 Bool.false 1926287 4000 0

noncomputable abbrev qz59 := (Complex.re qz379)

noncomputable abbrev qz60 := (Complex.im qz379)

noncomputable def ep892 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz59 qz56) (@HMul.hMul Real Real Real qz0 qz60 qz57) 289 16 0 1 12839382721 4000000

noncomputable def ep893 := @Enclosure.Real.IsNear.mulLit_ff qz59 qz56 17000 4000 0 1 17000 4000 0 1

noncomputable def ep894 := @Enclosure.Complex.IsNear.re_isNear qz58 Bool.false 17000 4000 0 1 Bool.false 226622 4000 0 1

noncomputable def ep895 := @Enclosure.Complex.IsNear.of_eq qz58 qz55 Bool.false 17000 4000 0 1 Bool.false 226622 4000 0

noncomputable abbrev qz380 := (Enclosure.sfrac Bool.false 113311 1000)

noncomputable abbrev qz61 := qz380

noncomputable abbrev qz381 := (Enclosure.sfrac Bool.false 226622 4000)

noncomputable abbrev qz617 := (Complex.mk (Enclosure.sfrac Bool.false 17000 4000) qz381)

noncomputable def ep896 := @Enclosure.Complex.IsNear.of_eq qz55 qz617 Bool.false 17000 4000 0 1 Bool.false 226622 4000 0 1 (BSN.w_shift_mk qz61 Bool.false 113311 1000 4 (@Eq.refl Real qz61) rfl)

noncomputable abbrev qz62 := (@ep895 1 (BSN.pow_one_c qz378) (ep896 (@Enclosure.Complex.IsNear.mk qz547 qz381 Bool.false 17000 4000 0 1 Bool.false 226622 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 17000 4000) (Enclosure.Real.IsNear.const Bool.false 226622 4000))))

noncomputable abbrev qz63 := (ep896 (@Enclosure.Complex.IsNear.mk qz547 qz381 Bool.false 17000 4000 0 1 Bool.false 226622 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 17000 4000) (Enclosure.Real.IsNear.const Bool.false 226622 4000)))

noncomputable abbrev qz926 := (@Enclosure.Complex.IsNear.re_isNear qz55 Bool.false 17000 4000 0 1 Bool.false 226622 4000 0 1 qz63)

noncomputable def ep897 := @ep893 289 16 0 1 (ep894 qz62) qz926

noncomputable def ep898 := @Enclosure.Real.IsNear.mulLit_ff qz60 qz57 226622 4000 0 1 226622 4000 0 1

noncomputable def ep899 := @Enclosure.Complex.IsNear.im_isNear qz58 Bool.false 17000 4000 0 1 Bool.false 226622 4000 0 1

noncomputable abbrev qz927 := (@Enclosure.Complex.IsNear.im_isNear qz55 Bool.false 17000 4000 0 1 Bool.false 226622 4000 0 1 qz63)

noncomputable def ep900 := @ep898 12839382721 4000000 0 1 (ep899 qz62) qz927

noncomputable def ep901 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz59 qz57) (@HMul.hMul Real Real Real qz0 qz60 qz56) 1926287 8000 0 1 1926287 8000

noncomputable def ep902 := @Enclosure.Real.IsNear.mulLit_ff qz59 qz57 17000 4000 0 1 226622 4000 0 1

noncomputable def ep903 := @ep902 1926287 8000 0 1 (ep894 qz62) qz927

noncomputable def ep904 := @Enclosure.Real.IsNear.mulLit_ff qz60 qz56 226622 4000 0 1 17000 4000 0 1

noncomputable def ep905 := @ep904 1926287 8000 0 1 (ep899 qz62) qz926

noncomputable abbrev qz618 := (@ep890 0 1 (BSN.pow_succ_c qz55 1 2 rfl) (@ep891 1 (@ep892 0 1 204274123536 12767132721 4000000 0 1 (ep897 rfl) (ep900 rfl) rfl rfl) (@ep901 0 1 30820592000 1926287 4000 0 1 (ep903 rfl) (ep905 rfl) rfl rfl)))

noncomputable def ep906 := @ep888 217041256257 16000000 0 1 (ep889 qz618) qz926

noncomputable def ep907 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz54) qz57 1926287 4000 0 1 226622 4000 0 1

noncomputable def ep908 := @Enclosure.Complex.IsNear.im_isNear qz54 Bool.true 12767132721 4000000 0 1 Bool.false 1926287 4000 0 1

noncomputable def ep909 := @ep907 218269506257 8000000 0 1 (ep908 qz618) qz927

noncomputable def ep910 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re qz54) qz57) (@HMul.hMul Real Real Real qz0 (Complex.im qz54) qz56) 1446656575749231 8000000000 0 1 32746879 16000

noncomputable def ep911 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re qz54) qz57 12767132721 4000000 0 1 226622 4000 0 1

noncomputable def ep912 := @ep911 1446656575749231 8000000000 0 1 (ep889 qz618) qz927

noncomputable def ep913 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz54) qz56 1926287 4000 0 1 17000 4000 0 1

noncomputable def ep914 := @ep913 32746879 16000 0 1 (ep908 qz618) qz926

theorem EMRow35.d16 : ep884 := @ep885 0 1 (BSN.pow_succ_c qz55 2 3 rfl) (@ep886 1 (@ep887 0 1 5228642150168000000 653580268771 16000000 0 1 (ep906 rfl) (ep909 rfl) rfl rfl) (@ep910 0 1 22884530179987696000 1430283136249231 8000000000 0 1 (ep912 rfl) (ep914 rfl) rfl rfl))

noncomputable abbrev qz382 := (@HAdd.hAdd Complex Complex Complex qz549 qz550 (@HMul.hMul Complex Complex Complex qz545 Complex.I ↑(Enclosure.sfrac Bool.false 113311 1000)))

noncomputable abbrev qz64 := qz382

noncomputable abbrev qz65 := (@Neg.neg Complex Complex.instNeg qz382)

noncomputable def ep915 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 9) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 8) (@HPow.hPow Complex Complex Complex qz16 qz817 qz65)) Bool.false 693346171273 549755813888 53125718170189 18913524143095808 Bool.true 32672618383 274877906944 53071064357247 18913524143095808

noncomputable def ep916 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 8) (@HPow.hPow Complex Complex Complex qz16 qz817 qz65) Bool.false 443856017507 274877906944 95098427472893 37827048286191616 Bool.true 33075969359 274877906944 47512522231679 18913524143095808 Bool.true

noncomputable def ep917 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 8) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 7) (@HPow.hPow Complex Complex Complex qz16 qz818 qz65)) Bool.false 443856017507 274877906944 95098427472893 37827048286191616 Bool.true 33075969359 274877906944 47512522231679 18913524143095808

noncomputable def ep918 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 7) (@HPow.hPow Complex Complex Complex qz16 qz818 qz65) Bool.false 1428119320303 1099511627776 166367486848459 75654096572383232 Bool.false 47956766307 549755813888 83120697943971 37827048286191616 Bool.false

noncomputable def ep919 := nat_lit 1952099409229177293897728

noncomputable def ep920 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 7) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 6) (@HPow.hPow Complex Complex Complex qz16 qz819 qz65)) Bool.false 1428119320303 1099511627776 166367486848459 75654096572383232 Bool.false 47956766307 549755813888 83120697943971 37827048286191616

noncomputable def ep921 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 6) (@HPow.hPow Complex Complex Complex qz16 qz819 qz65) Bool.false 800056664501 549755813888 17579614413969 9456762071547904 Bool.false 510528163827 1099511627776 140471826883073 75654096572383232 Bool.true

noncomputable def ep922 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 6) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 5) (@HPow.hPow Complex Complex Complex qz16 qz18 qz65)) Bool.false 800056664501 549755813888 17579614413969 9456762071547904 Bool.false 510528163827 1099511627776 140471826883073 75654096572383232

noncomputable def ep923 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 5) (@HPow.hPow Complex Complex Complex qz16 qz18 qz65) Bool.false 557124789525 549755813888 14055219328689 9456762071547904 Bool.false 586163012557 1099511627776 112336858977275 75654096572383232 Bool.false

noncomputable def ep924 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 5) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 4) (@HPow.hPow Complex Complex Complex qz16 qz19 qz65)) Bool.false 557124789525 549755813888 14055219328689 9456762071547904 Bool.false 586163012557 1099511627776 112336858977275 75654096572383232

noncomputable def ep925 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 4) (@HPow.hPow Complex Complex Complex qz16 qz19 qz65) Bool.false 282248455443 549755813888 20231550073385 18913524143095808 Bool.false 73453156125 137438953472 10111657729023 9456762071547904 Bool.false

noncomputable def ep926 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 4) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 3) (@HPow.hPow Complex Complex Complex qz16 qz552 qz65)) Bool.false 282248455443 549755813888 20231550073385 18913524143095808 Bool.false 73453156125 137438953472 10111657729023 9456762071547904

noncomputable def ep927 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 3) (@HPow.hPow Complex Complex Complex qz16 qz552 qz65) Bool.false 322040451151 1099511627776 44590904771433 75654096572383232 Bool.false 3707275 4294967296 2782427721523 4728381035773952 Bool.false

noncomputable def ep928 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 3) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 2) (@HPow.hPow Complex Complex Complex qz16 qz553 qz65)) Bool.false 322040451151 1099511627776 44590904771433 75654096572383232 Bool.false 3707275 4294967296 2782427721523 4728381035773952

noncomputable def ep929 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 2) (@HPow.hPow Complex Complex Complex qz16 qz553 qz65) Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.true

noncomputable def ep930 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz264) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz64)

noncomputable abbrev qz383 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 2 1)))

noncomputable def ep931 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz553 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz265 (Real.cos qz383)) (@HMul.hMul Real Real Real qz0 qz265 (@Neg.neg Real Real.instNeg (Real.sin qz383)))) Bool.true 777471176625 1099511627776 44590904771433 75654096572383232 Bool.false 3707275 4294967296 2782427721523 4728381035773952 (BSN.cpow_neg_s_mk qz61 113311 1000 2 (@Eq.refl Real qz61) rfl)

noncomputable def ep932 := BSN.cos_dyadic_bound_f 2622549 2147483648 1 0 1048576 275497 0 1 1 0 1 1 1048575 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 2622549) qz272 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 2622549) qz273 0 0 rfl) rfl rfl

noncomputable abbrev qz384 := (Enclosure.Real.IsNear.const Bool.false 113311 1000)

noncomputable abbrev qz928 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 82356247) qz277)

noncomputable def ep933 := @Enclosure.Real.IsNear.cos_image qz383 qz928 Bool.false 82356247 1048576 865 1048576 Bool.true 1048575 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz383 Bool.false 2573632743 32768000 113311 137614000 82356247 1048576 865 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz61 qz270 113311 1000 0 1 363408 524288 1 137614 2573632743 32768000 113311 137614000 qz384 qz556 rfl) rfl) (Enclosure.sfrac_false_div 82356247 1048576) (BSN.cos_reduce2 qz928 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 184545513083328528384) qz279) 226375608064910080 72057594037927936 Bool.false 1048575 1048576 12 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q2 82356247 1048576 226375608064910080 72057594037927936 12 184545513083328528384 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1048575 1048576 184545513083328528384 151115727451828646838272 2622549 2147483648 275497 275228 (ep932 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep934 := BSN.sin_dyadic_bound_f 2622549 2147483648 1 0 1048576 275497 0 1 1 0 1 1 1280 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 2622549) qz268 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 2622549) qz269 0 0 rfl) rfl rfl

noncomputable def ep935 := @Enclosure.Real.IsNear.sin_image qz383 qz928 Bool.false 82356247 1048576 865 1048576 Bool.true 1280 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz383 Bool.false 2573632743 32768000 113311 137614000 82356247 1048576 865 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz61 qz270 113311 1000 0 1 363408 524288 1 137614 2573632743 32768000 113311 137614000 qz384 qz556 rfl) rfl) (Enclosure.sfrac_false_div 82356247 1048576) (BSN.sin_reduce2 qz928 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 184545513083328528384) qz279) 226375608064910080 72057594037927936 Bool.false 1280 1048576 12 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q2 82356247 1048576 226375608064910080 72057594037927936 12 184545513083328528384 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1280 1048576 184545513083328528384 151115727451828646838272 2622549 2147483648 275497 275228 (ep934 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep936 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz265 (Real.cos qz383)) (@HMul.hMul Real Real Real qz0 qz265 (@Neg.neg Real Real.instNeg (Real.sin qz383))) Bool.true 777471176625 1099511627776 44590904771433 75654096572383232 Bool.false 3707275 4294967296 2782427721523 4728381035773952 (@Enclosure.Real.IsNear.mulLit_ft qz265 (Real.cos qz383) 741455 1048576 1 1048576 1048575 1048576 60042343 72149368832 777471176625 1099511627776 44590904771433 75654096572383232 qz558 (@Enclosure.Real.IsNear.recentre' (Real.cos qz383) Bool.true 1048575 1048576 120084686 144298737664 1048575 1048576 60042343 72149368832 (ep933 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz265 (@Neg.neg Real Real.instNeg (Real.sin qz383)) 741455 1048576 1 1048576 5 4096 60042343 72149368832 3707275 4294967296 2782427721523 4728381035773952 qz558 (@Enclosure.Real.IsNear.neg (Real.sin qz383) Bool.true 5 4096 60042343 72149368832 (@Enclosure.Real.IsNear.recentre' (Real.sin qz383) Bool.true 1280 1048576 120084686 144298737664 5 4096 60042343 72149368832 (ep935 rfl rfl) rfl)) rfl)

noncomputable def ep937 := @ep929 777471176625 1099511627776 44590904771433 75654096572383232 Bool.false 3707275 4294967296 2782427721523 4728381035773952 Bool.false 322040451151 322040451151 1099511627776 44590904771433 75654096572383232 Bool.false 3707275 3707275 4294967296 2782427721523 4728381035773952 (ep930 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz264 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz274)) (ep931 ep936) rfl rfl

noncomputable abbrev qz385 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 3 1)))

noncomputable def ep938 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz552 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz275 (Real.cos qz385)) (@HMul.hMul Real Real Real qz0 qz275 (@Neg.neg Real Real.instNeg (Real.sin qz385)))) Bool.false 242456459735 1099511627776 36335295522107 75654096572383232 Bool.false 73334523325 137438953472 4546802285977 9456762071547904 (BSN.cpow_neg_s_mk qz61 113311 1000 3 (@Eq.refl Real qz61) rfl)

noncomputable def ep939 := nat_lit 501648638704125244453903077862119841

noncomputable def ep940 := BSN.sin_dyadic_bound_f 841588727 2147483648 2 1 1048576 275497 ep939 ep178 ep939 ep939 ep179 ep939 400493 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 841588727) qz268 0 1 ep939 ep178 ep939 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 841588727) qz269 0 1 ep939 ep179 ep939 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz929 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 130531779) qz277)

noncomputable def ep941 := @Enclosure.Real.IsNear.cos_image qz385 qz929 Bool.false 130531779 1048576 27 32768 Bool.false 400493 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz385 Bool.false 65265889579 524288000 113311 137614000 130531779 1048576 27 32768 (@Enclosure.Real.IsNear.mulLit_ff qz61 qz278 113311 1000 0 1 575989 524288 1 137614 65265889579 524288000 113311 137614000 qz384 qz559 rfl) rfl) (Enclosure.sfrac_false_div 130531779 1048576) (BSN.cos_reduce3 qz929 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 59221541881632908115968) qz279) 226375608064910080 72057594037927936 Bool.false 400493 1048576 19 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q3 130531779 1048576 226375608064910080 72057594037927936 19 59221541881632908115968 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 400493 1048576 59221541881632908115968 151115727451828646838272 841588727 2147483648 275497 275228 (ep940 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep942 := BSN.cos_dyadic_bound_f 841588727 2147483648 2 1 1048576 275497 ep939 ep118 ep939 ep939 ep119 ep939 969080 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 841588727) qz272 0 1 ep939 ep118 ep939 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 841588727) qz273 0 1 ep939 ep119 ep939 rfl rfl rfl rfl) rfl rfl

noncomputable def ep943 := @Enclosure.Real.IsNear.sin_image qz385 qz929 Bool.false 130531779 1048576 27 32768 Bool.true 969080 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz385 Bool.false 65265889579 524288000 113311 137614000 130531779 1048576 27 32768 (@Enclosure.Real.IsNear.mulLit_ff qz61 qz278 113311 1000 0 1 575989 524288 1 137614 65265889579 524288000 113311 137614000 qz384 qz559 rfl) rfl) (Enclosure.sfrac_false_div 130531779 1048576) (BSN.sin_reduce3 qz929 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 59221541881632908115968) qz279) 226375608064910080 72057594037927936 Bool.false 969080 1048576 19 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q3 130531779 1048576 226375608064910080 72057594037927936 19 59221541881632908115968 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 969080 1048576 59221541881632908115968 151115727451828646838272 841588727 2147483648 275497 275228 (ep942 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep944 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz275 (Real.cos qz385)) (@HMul.hMul Real Real Real qz0 qz275 (@Neg.neg Real Real.instNeg (Real.sin qz385))) Bool.false 242456459735 1099511627776 36335295522107 75654096572383232 Bool.false 73334523325 137438953472 4546802285977 9456762071547904 (@Enclosure.Real.IsNear.mulLit_ff qz275 (Real.cos qz385) 605395 1048576 1 1048576 400493 1048576 1874173 2254667776 242456459735 1099511627776 36335295522107 75654096572383232 qz560 (@Enclosure.Real.IsNear.recentre' (Real.cos qz385) Bool.false 400493 1048576 3748346 4509335552 400493 1048576 1874173 2254667776 (ep941 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz275 (@Neg.neg Real Real.instNeg (Real.sin qz385)) 605395 1048576 1 1048576 121135 131072 1874173 2254667776 73334523325 137438953472 4546802285977 9456762071547904 qz560 (@Enclosure.Real.IsNear.neg (Real.sin qz385) Bool.true 121135 131072 1874173 2254667776 (@Enclosure.Real.IsNear.recentre' (Real.sin qz385) Bool.true 969080 1048576 3748346 4509335552 121135 131072 1874173 2254667776 (ep943 rfl rfl) rfl)) rfl)

noncomputable def ep945 := @ep927 242456459735 1099511627776 36335295522107 75654096572383232 Bool.false 73334523325 137438953472 4546802285977 9456762071547904 Bool.false 620670917362789474369536 282248455443 549755813888 20231550073385 18913524143095808 Bool.false 315478903344857088000 73453156125 137438953472 10111657729023 9456762071547904 (ep928 (BSN.head_sum_c_succ qz64 2 3 rfl rfl) (ep937 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep938 ep944) rfl rfl

noncomputable abbrev qz386 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 4 1)))

noncomputable def ep946 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz19 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz280 (Real.cos qz386)) (@HMul.hMul Real Real Real qz0 qz280 (@Neg.neg Real Real.instNeg (Real.sin qz386)))) Bool.false 137438167041 274877906944 7878888583993 18913524143095808 Bool.true 1462236443 1099511627776 31443597145091 75654096572383232 (BSN.cpow_neg_s_mk qz61 113311 1000 4 (@Eq.refl Real qz61) rfl)

noncomputable def ep947 := BSN.cos_dyadic_bound_f 5712042 2147483648 1 0 1048576 275497 0 1 1 0 1 1 1048572 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 5712042) qz272 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 5712042) qz273 0 0 rfl) rfl rfl

noncomputable abbrev qz930 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 82356361) qz289)

noncomputable def ep948 := @Enclosure.Real.IsNear.cos_image qz386 qz930 Bool.false 82356361 524288 27 32768 Bool.false 1048572 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz386 Bool.false 82356361087 524288000 113311 137614000 82356361 524288 27 32768 (@Enclosure.Real.IsNear.mulLit_ff qz61 qz282 113311 1000 0 1 726817 524288 1 137614 82356361087 524288000 113311 137614000 qz384 qz562 rfl) rfl) (Enclosure.sfrac_false_div 82356361 524288) (BSN.cos_reduce0 qz930 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 200974644523976097792) qz290) 226375608064910080 72057594037927936 Bool.false 1048572 1048576 25 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q0 82356361 524288 226375608064910080 72057594037927936 25 200974644523976097792 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1048572 1048576 200974644523976097792 75557863725914323419136 5712042 2147483648 275497 275228 (ep947 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep949 := BSN.sin_dyadic_bound_f 5712042 2147483648 1 0 1048576 275497 0 1 1 0 1 1 2789 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 5712042) qz268 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 5712042) qz269 0 0 rfl) rfl rfl

noncomputable def ep950 := @Enclosure.Real.IsNear.sin_image qz386 qz930 Bool.false 82356361 524288 27 32768 Bool.false 2789 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz386 Bool.false 82356361087 524288000 113311 137614000 82356361 524288 27 32768 (@Enclosure.Real.IsNear.mulLit_ff qz61 qz282 113311 1000 0 1 726817 524288 1 137614 82356361087 524288000 113311 137614000 qz384 qz562 rfl) rfl) (Enclosure.sfrac_false_div 82356361 524288) (BSN.sin_reduce0 qz930 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 200974644523976097792) qz290) 226375608064910080 72057594037927936 Bool.false 2789 1048576 25 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q0 82356361 524288 226375608064910080 72057594037927936 25 200974644523976097792 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 2789 1048576 200974644523976097792 75557863725914323419136 5712042 2147483648 275497 275228 (ep949 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep951 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz280 (Real.cos qz386)) (@HMul.hMul Real Real Real qz0 qz280 (@Neg.neg Real Real.instNeg (Real.sin qz386))) Bool.false 137438167041 274877906944 7878888583993 18913524143095808 Bool.true 1462236443 1099511627776 31443597145091 75654096572383232 (@Enclosure.Real.IsNear.mulLit_ff qz280 (Real.cos qz386) 524287 1048576 1 1048576 262143 262144 1874173 2254667776 137438167041 274877906944 7878888583993 18913524143095808 qz564 (@Enclosure.Real.IsNear.recentre' (Real.cos qz386) Bool.false 1048572 1048576 3748346 4509335552 262143 262144 1874173 2254667776 (ep948 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz280 (@Neg.neg Real Real.instNeg (Real.sin qz386)) 524287 1048576 1 1048576 2789 1048576 1874173 2254667776 1462236443 1099511627776 31443597145091 75654096572383232 qz564 (@Enclosure.Real.IsNear.neg (Real.sin qz386) Bool.false 2789 1048576 1874173 2254667776 (@Enclosure.Real.IsNear.recentre' (Real.sin qz386) Bool.false 2789 1048576 3748346 4509335552 2789 1048576 1874173 2254667776 (ep950 rfl rfl) rfl)) rfl)

noncomputable def ep952 := @ep925 137438167041 274877906944 7878888583993 18913524143095808 Bool.true 1462236443 1099511627776 31443597145091 75654096572383232 Bool.false 153141296051248535961600 557124789525 549755813888 14055219328689 9456762071547904 Bool.false 80561631009828874747904 586163012557 1099511627776 112336858977275 75654096572383232 (ep926 (BSN.head_sum_c_succ qz64 3 4 rfl rfl) (ep945 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep946 ep951) rfl rfl

noncomputable abbrev qz387 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 5 1)))

noncomputable def ep953 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz18 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz283 (Real.cos qz387)) (@HMul.hMul Real Real Real qz0 qz283 (@Neg.neg Real Real.instNeg (Real.sin qz387)))) Bool.false 7591621093 17179869184 110137346415 295523814735872 Bool.true 37817424365 549755813888 14067483952899 37827048286191616 (BSN.cpow_neg_s_mk qz61 113311 1000 5 (@Eq.refl Real qz61) rfl)

noncomputable def ep954 := nat_lit 12096786465687377101185285390340096

noncomputable def ep955 := BSN.cos_dyadic_bound_f 331640456 2147483648 2 1 1048576 275497 ep954 ep118 ep954 ep954 ep119 ep954 1036096 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 331640456) qz272 0 1 ep954 ep118 ep954 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 331640456) qz273 0 1 ep954 ep119 ep954 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz619 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11951591) (@Nat.cast Real Real.instNatCast 65536))

noncomputable def ep956 := @Enclosure.Real.IsNear.cos_image qz387 qz619 Bool.false 11951591 65536 27 32768 Bool.false 1036096 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz387 Bool.false 2987897759 16384000 113311 137614000 11951591 65536 27 32768 (@Enclosure.Real.IsNear.mulLit_ff qz61 qz285 113311 1000 0 1 843808 524288 1 137614 2987897759 16384000 113311 137614000 qz384 qz566 rfl) rfl) (Enclosure.sfrac_false_div 11951591 65536) (BSN.cos_reduce0 qz619 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 1458570154240504758272) qz582) 226375608064910080 72057594037927936 Bool.false 1036096 1048576 29 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q0 11951591 65536 226375608064910080 72057594037927936 29 1458570154240504758272 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1036096 1048576 1458570154240504758272 9444732965739290427392 331640456 2147483648 275497 275228 (ep955 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep957 := BSN.sin_dyadic_bound_f 331640456 2147483648 1 0 1048576 275497 0 1 1 0 1 1 161290 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 331640456) qz268 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 331640456) qz269 0 0 rfl) rfl rfl

noncomputable def ep958 := @Enclosure.Real.IsNear.sin_image qz387 qz619 Bool.false 11951591 65536 27 32768 Bool.false 161290 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz387 Bool.false 2987897759 16384000 113311 137614000 11951591 65536 27 32768 (@Enclosure.Real.IsNear.mulLit_ff qz61 qz285 113311 1000 0 1 843808 524288 1 137614 2987897759 16384000 113311 137614000 qz384 qz566 rfl) rfl) (Enclosure.sfrac_false_div 11951591 65536) (BSN.sin_reduce0 qz619 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 1458570154240504758272) qz582) 226375608064910080 72057594037927936 Bool.false 161290 1048576 29 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q0 11951591 65536 226375608064910080 72057594037927936 29 1458570154240504758272 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 161290 1048576 1458570154240504758272 9444732965739290427392 331640456 2147483648 275497 275228 (ep957 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep959 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz283 (Real.cos qz387)) (@HMul.hMul Real Real Real qz0 qz283 (@Neg.neg Real Real.instNeg (Real.sin qz387))) Bool.false 7591621093 17179869184 110137346415 295523814735872 Bool.true 37817424365 549755813888 14067483952899 37827048286191616 (@Enclosure.Real.IsNear.mulLit_ff qz283 (Real.cos qz387) 468937 1048576 1 1048576 16189 16384 1874173 2254667776 7591621093 17179869184 110137346415 295523814735872 qz567 (@Enclosure.Real.IsNear.recentre' (Real.cos qz387) Bool.false 1036096 1048576 3748346 4509335552 16189 16384 1874173 2254667776 (ep956 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz283 (@Neg.neg Real Real.instNeg (Real.sin qz387)) 468937 1048576 1 1048576 80645 524288 1874173 2254667776 37817424365 549755813888 14067483952899 37827048286191616 qz567 (@Enclosure.Real.IsNear.neg (Real.sin qz387) Bool.false 80645 524288 1874173 2254667776 (@Enclosure.Real.IsNear.recentre' (Real.sin qz387) Bool.false 161290 1048576 3748346 4509335552 80645 524288 1874173 2254667776 (ep958 rfl rfl) rfl)) rfl)

noncomputable def ep960 := @ep923 7591621093 17179869184 110137346415 295523814735872 Bool.true 37817424365 549755813888 14067483952899 37827048286191616 Bool.false 13744868835914556637184 800056664501 549755813888 17579614413969 9456762071547904 Bool.false 280665826217458585829376 510528163827 1099511627776 140471826883073 75654096572383232 (ep924 (BSN.head_sum_c_succ qz64 4 5 rfl rfl) (ep952 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep953 ep959) rfl rfl

noncomputable abbrev qz388 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 6 1)))

noncomputable def ep961 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz819 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz286 (Real.cos qz388)) (@HMul.hMul Real Real Real qz0 qz286 (@Neg.neg Real Real.instNeg (Real.sin qz388)))) Bool.true 171994008699 1099511627776 25730571536707 75654096572383232 Bool.true 414614631213 1099511627776 25769569004869 75654096572383232 (BSN.cpow_neg_s_mk qz61 113311 1000 6 (@Eq.refl Real qz61) rfl)

noncomputable def ep962 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz288 113311 1000 0 1 4034681531866359 2251799813685248 250000000068807 34403500000000000000 457173799057309004649 2251799813685248000 28327750007796589977 34403500000000000000000 qz384 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 250000000068807 34403500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz824) Bool.false 33845361775666394038272 18889465931478580854784 1000000000275228 137614000000000000000 4034681531866359 2251799813685248 250000000068807 34403500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 212580 524288 24973259072661432 36028797018963968 137614 1000000000000000 rfl rfl rfl rfl (ep145 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep963 := nat_lit 508488042706243186583276398909510801

noncomputable def ep964 := BSN.sin_dyadic_bound_f 844442701 2147483648 2 1 1048576 275497 ep963 ep178 ep963 ep963 ep179 ep963 401781 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 844442701) qz268 0 1 ep963 ep178 ep963 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 844442701) qz269 0 1 ep963 ep179 ep963 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz931 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 212888139) qz277)

noncomputable def ep965 := @Enclosure.Real.IsNear.cos_image qz388 qz931 Bool.false 212888139 1048576 865 1048576 Bool.true 401781 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz388 Bool.false 457173799057309004649 2251799813685248000 28327750007796589977 34403500000000000000000 212888139 1048576 865 1048576 (ep962 rfl) rfl) (Enclosure.sfrac_false_div 212888139 1048576) (BSN.cos_reduce1 qz931 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 59422372410968808357888) qz279) 226375608064910080 72057594037927936 Bool.false 401781 1048576 32 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q1 212888139 1048576 226375608064910080 72057594037927936 32 59422372410968808357888 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 401781 1048576 59422372410968808357888 151115727451828646838272 844442701 2147483648 275497 275228 (ep964 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep966 := BSN.cos_dyadic_bound_f 844442701 2147483648 2 1 1048576 275497 ep963 ep118 ep963 ep963 ep119 ep963 968547 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 844442701) qz272 0 1 ep963 ep118 ep963 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 844442701) qz273 0 1 ep963 ep119 ep963 rfl rfl rfl rfl) rfl rfl

noncomputable def ep967 := @Enclosure.Real.IsNear.sin_image qz388 qz931 Bool.false 212888139 1048576 865 1048576 Bool.false 968547 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz388 Bool.false 457173799057309004649 2251799813685248000 28327750007796589977 34403500000000000000000 212888139 1048576 865 1048576 (ep962 rfl) rfl) (Enclosure.sfrac_false_div 212888139 1048576) (BSN.sin_reduce1 qz931 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 59422372410968808357888) qz279) 226375608064910080 72057594037927936 Bool.false 968547 1048576 32 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q1 212888139 1048576 226375608064910080 72057594037927936 32 59422372410968808357888 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 968547 1048576 59422372410968808357888 151115727451828646838272 844442701 2147483648 275497 275228 (ep966 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep968 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz286 (Real.cos qz388)) (@HMul.hMul Real Real Real qz0 qz286 (@Neg.neg Real Real.instNeg (Real.sin qz388))) Bool.true 171994008699 1099511627776 25730571536707 75654096572383232 Bool.true 414614631213 1099511627776 25769569004869 75654096572383232 (@Enclosure.Real.IsNear.mulLit_ft qz286 (Real.cos qz388) 428079 1048576 1 1048576 401781 1048576 60042343 72149368832 171994008699 1099511627776 25730571536707 75654096572383232 qz568 (@Enclosure.Real.IsNear.recentre' (Real.cos qz388) Bool.true 401781 1048576 120084686 144298737664 401781 1048576 60042343 72149368832 (ep965 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz286 (@Neg.neg Real Real.instNeg (Real.sin qz388)) 428079 1048576 1 1048576 968547 1048576 60042343 72149368832 414614631213 1099511627776 25769569004869 75654096572383232 qz568 (@Enclosure.Real.IsNear.neg (Real.sin qz388) Bool.false 968547 1048576 60042343 72149368832 (@Enclosure.Real.IsNear.recentre' (Real.sin qz388) Bool.false 968547 1048576 120084686 144298737664 968547 1048576 60042343 72149368832 (ep967 rfl rfl) rfl)) rfl)

noncomputable def ep969 := @ep921 171994008699 1099511627776 25730571536707 75654096572383232 Bool.true 414614631213 1099511627776 25769569004869 75654096572383232 Bool.false 785116899262353127768064 1428119320303 1099511627776 166367486848459 75654096572383232 Bool.false 105458044370165604286464 47956766307 549755813888 83120697943971 37827048286191616 (ep922 (BSN.head_sum_c_succ qz64 5 6 rfl rfl) (ep960 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep961 ep968) rfl rfl

noncomputable abbrev qz389 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 7 1)))

noncomputable def ep970 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz818 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz291 (Real.cos qz389)) (@HMul.hMul Real Real Real qz0 qz291 (@Neg.neg Real Real.instNeg (Real.sin qz389)))) Bool.false 347304749725 1099511627776 23829368097327 75654096572383232 Bool.true 114108705025 549755813888 11904346519387 37827048286191616 (BSN.cpow_neg_s_mk qz61 113311 1000 7 (@Eq.refl Real qz61) rfl)

noncomputable def ep971 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz293 113311 1000 0 1 4381796493761783 2251799813685248 250000000068807 34403500000000000000 496505742504641393513 2251799813685248000 28327750007796589977 34403500000000000000000 qz384 (BSN.isNear_log_sfrac 7 1 4381796493761783 2251799813685248 250000000068807 34403500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz827) Bool.false 36757173121942042968064 18889465931478580854784 1000000000275228 137614000000000000000 4381796493761783 2251799813685248 250000000068807 34403500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 293399 524288 24973259072661432 36028797018963968 137614 1000000000000000 rfl rfl rfl rfl (ep160 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep972 := nat_lit 2429354288890759183312199560701800625

noncomputable def ep973 := BSN.cos_dyadic_bound_f 1248454485 2147483648 2 1 1048576 275497 ep972 ep118 ep972 ep972 ep119 ep972 876313 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1248454485) qz272 0 1 ep972 ep118 ep972 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1248454485) qz273 0 1 ep972 ep119 ep972 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz932 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 231203503) qz277)

noncomputable def ep974 := @Enclosure.Real.IsNear.cos_image qz389 qz932 Bool.false 231203503 1048576 27 32768 Bool.false 876313 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz389 Bool.false 496505742504641393513 2251799813685248000 28327750007796589977 34403500000000000000000 231203503 1048576 27 32768 (ep971 rfl) rfl) (Enclosure.sfrac_false_div 231203503 1048576) (BSN.cos_reduce0 qz932 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 87852174323746043068416) qz279) 226375608064910080 72057594037927936 Bool.false 876313 1048576 35 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q0 231203503 1048576 226375608064910080 72057594037927936 35 87852174323746043068416 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 876313 1048576 87852174323746043068416 151115727451828646838272 1248454485 2147483648 275497 275228 (ep973 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep975 := BSN.sin_dyadic_bound_f 1248454485 2147483648 2 1 1048576 275497 ep972 ep178 ep972 ep972 ep179 ep972 575834 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1248454485) qz268 0 1 ep972 ep178 ep972 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1248454485) qz269 0 1 ep972 ep179 ep972 rfl rfl rfl rfl) rfl rfl

noncomputable def ep976 := @Enclosure.Real.IsNear.sin_image qz389 qz932 Bool.false 231203503 1048576 27 32768 Bool.false 575834 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz389 Bool.false 496505742504641393513 2251799813685248000 28327750007796589977 34403500000000000000000 231203503 1048576 27 32768 (ep971 rfl) rfl) (Enclosure.sfrac_false_div 231203503 1048576) (BSN.sin_reduce0 qz932 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 87852174323746043068416) qz279) 226375608064910080 72057594037927936 Bool.false 575834 1048576 35 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q0 231203503 1048576 226375608064910080 72057594037927936 35 87852174323746043068416 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 575834 1048576 87852174323746043068416 151115727451828646838272 1248454485 2147483648 275497 275228 (ep975 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep977 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz291 (Real.cos qz389)) (@HMul.hMul Real Real Real qz0 qz291 (@Neg.neg Real Real.instNeg (Real.sin qz389))) Bool.false 347304749725 1099511627776 23829368097327 75654096572383232 Bool.true 114108705025 549755813888 11904346519387 37827048286191616 (@Enclosure.Real.IsNear.mulLit_ff qz291 (Real.cos qz389) 396325 1048576 1 1048576 876313 1048576 1874173 2254667776 347304749725 1099511627776 23829368097327 75654096572383232 qz569 (@Enclosure.Real.IsNear.recentre' (Real.cos qz389) Bool.false 876313 1048576 3748346 4509335552 876313 1048576 1874173 2254667776 (ep974 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz291 (@Neg.neg Real Real.instNeg (Real.sin qz389)) 396325 1048576 1 1048576 287917 524288 1874173 2254667776 114108705025 549755813888 11904346519387 37827048286191616 qz569 (@Enclosure.Real.IsNear.neg (Real.sin qz389) Bool.false 287917 524288 1874173 2254667776 (@Enclosure.Real.IsNear.recentre' (Real.sin qz389) Bool.false 575834 1048576 3748346 4509335552 287917 524288 1874173 2254667776 (ep976 rfl rfl) rfl)) rfl)

noncomputable def ep978 := @ep918 347304749725 1099511627776 23829368097327 75654096572383232 Bool.true 114108705025 549755813888 11904346519387 37827048286191616 Bool.false ep919 443856017507 274877906944 95098427472893 37827048286191616 Bool.true 36367412910183189315584 33075969359 274877906944 47512522231679 18913524143095808 (ep920 (BSN.head_sum_c_succ qz64 6 7 rfl rfl) (ep969 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep970 ep977) rfl rfl

noncomputable abbrev qz390 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 8 1)))

noncomputable def ep979 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz817 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz294 (Real.cos qz390)) (@HMul.hMul Real Real Real qz0 qz294 (@Neg.neg Real Real.instNeg (Real.sin qz390)))) Bool.true 194365863741 549755813888 11153008867485 37827048286191616 Bool.false 6302359 4294967296 10856527589 36940476841984 (BSN.cpow_neg_s_mk qz61 113311 1000 8 (@Eq.refl Real qz61) rfl)

noncomputable def ep980 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz296 113311 1000 0 1 9364972152248037 4503599627370496 500000000206421 68807000000000000000 1061154359543377320507 4503599627370496000 56655500023389769931 68807000000000000000000 qz384 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 500000000206421 68807000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz830) Bool.false 39279540158062550581248 18889465931478580854784 1000000000412842 137614000000000000000 9364972152248037 4503599627370496 500000000206421 68807000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 524288 24973259072661432 36028797018963968 137614 1000000000000000 rfl rfl rfl rfl (ep175 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep981 := BSN.cos_dyadic_bound_f 8914176 2147483648 1 0 1048576 275497 0 1 1 0 1 1 1048566 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 8914176) qz272 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 8914176) qz273 0 0 rfl) rfl rfl

noncomputable abbrev qz620 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 61767313) (@Nat.cast Real Real.instNatCast 262144))

noncomputable def ep982 := @Enclosure.Real.IsNear.cos_image qz390 qz620 Bool.false 61767313 262144 27 32768 Bool.true 1048566 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz390 Bool.false 1061154359543377320507 4503599627370496000 56655500023389769931 68807000000000000000000 61767313 262144 27 32768 (ep980 rfl) rfl) (Enclosure.sfrac_false_div 61767313 262144) (BSN.cos_reduce2 qz620 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 156819850089186983936) qz557) 226375608064910080 72057594037927936 Bool.false 1048566 1048576 37 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q2 61767313 262144 226375608064910080 72057594037927936 37 156819850089186983936 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1048566 1048576 156819850089186983936 37778931862957161709568 8914176 2147483648 275497 275228 (ep981 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep983 := BSN.sin_dyadic_bound_f 8914176 2147483648 1 0 1048576 275497 0 1 1 0 1 1 4352 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 8914176) qz268 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 8914176) qz269 0 0 rfl) rfl rfl

noncomputable def ep984 := @Enclosure.Real.IsNear.sin_image qz390 qz620 Bool.false 61767313 262144 27 32768 Bool.true 4352 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz390 Bool.false 1061154359543377320507 4503599627370496000 56655500023389769931 68807000000000000000000 61767313 262144 27 32768 (ep980 rfl) rfl) (Enclosure.sfrac_false_div 61767313 262144) (BSN.sin_reduce2 qz620 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 156819850089186983936) qz557) 226375608064910080 72057594037927936 Bool.false 4352 1048576 37 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q2 61767313 262144 226375608064910080 72057594037927936 37 156819850089186983936 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 4352 1048576 156819850089186983936 37778931862957161709568 8914176 2147483648 275497 275228 (ep983 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep985 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz294 (Real.cos qz390)) (@HMul.hMul Real Real Real qz0 qz294 (@Neg.neg Real Real.instNeg (Real.sin qz390))) Bool.true 194365863741 549755813888 11153008867485 37827048286191616 Bool.false 6302359 4294967296 10856527589 36940476841984 (@Enclosure.Real.IsNear.mulLit_ft qz294 (Real.cos qz390) 370727 1048576 1 1048576 524283 524288 1874173 2254667776 194365863741 549755813888 11153008867485 37827048286191616 qz570 (@Enclosure.Real.IsNear.recentre' (Real.cos qz390) Bool.true 1048566 1048576 3748346 4509335552 524283 524288 1874173 2254667776 (ep982 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz294 (@Neg.neg Real Real.instNeg (Real.sin qz390)) 370727 1048576 1 1048576 17 4096 1874173 2254667776 6302359 4294967296 10856527589 36940476841984 qz570 (@Enclosure.Real.IsNear.neg (Real.sin qz390) Bool.true 17 4096 1874173 2254667776 (@Enclosure.Real.IsNear.recentre' (Real.sin qz390) Bool.true 4352 1048576 3748346 4509335552 17 4096 1874173 2254667776 (ep984 rfl rfl) rfl)) rfl)

noncomputable def ep986 := @ep916 194365863741 549755813888 11153008867485 37827048286191616 Bool.false 6302359 4294967296 10856527589 36940476841984 Bool.false 190585544347158380019712 693346171273 549755813888 53125718170189 18913524143095808 Bool.true 140327827429673402368 32672618383 274877906944 53071064357247 18913524143095808 (ep917 (BSN.head_sum_c_succ qz64 7 8 rfl rfl) (ep978 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep979 ep985) rfl rfl

theorem EMRow35.d17 : Enclosure.Complex.IsNear (BSN.headSumC qz64 9) Bool.false 693346171273 549755813888 53125718170189 18913524143095808 Bool.true 32672618383 274877906944 53071064357247 18913524143095808 := ep915 (BSN.head_sum_c_succ qz64 8 9 rfl rfl) (ep986 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz933 := (@HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast 16) qz65)

noncomputable def ep987 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 17) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 16) qz933) Bool.false 1083916429507 1099511627776 357061257106911 75654096572383232 Bool.false 60463601213 274877906944 178445804006329 37827048286191616

noncomputable def ep988 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 16) qz933 Bool.false 404522013785 549755813888 170633703143307 37827048286191616 Bool.false 30421985353 137438953472 170584753017823 37827048286191616 Bool.false

noncomputable abbrev qz934 := (@HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast 15) qz65)

noncomputable def ep989 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 16) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 15) qz934) Bool.false 404522013785 549755813888 170633703143307 37827048286191616 Bool.false 30421985353 137438953472 170584753017823 37827048286191616

noncomputable def ep990 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 15) qz934 Bool.false 165383510653 274877906944 162486966794921 37827048286191616 Bool.false 407615275 549755813888 162425938426271 37827048286191616 Bool.false

noncomputable abbrev qz935 := (@HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast 14) qz65)

noncomputable def ep991 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 15) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 14) qz935) Bool.false 165383510653 274877906944 162486966794921 37827048286191616 Bool.false 407615275 549755813888 162425938426271 37827048286191616

noncomputable def ep992 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 14) qz935 Bool.false 113361409125 137438953472 154043592794369 37827048286191616 Bool.true 40224467907 274877906944 38498208209591 9456762071547904 Bool.true

noncomputable abbrev qz936 := (@HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast 13) qz65)

noncomputable def ep993 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 14) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 13) qz936) Bool.false 113361409125 137438953472 154043592794369 37827048286191616 Bool.true 40224467907 274877906944 38498208209591 9456762071547904

noncomputable def ep994 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 13) qz936 Bool.false 459460146963 549755813888 72660648989985 18913524143095808 Bool.false 143814544029 1099511627776 290471828889551 75654096572383232 Bool.true

noncomputable abbrev qz937 := (@HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast 12) qz65)

noncomputable def ep995 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 13) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 12) qz937) Bool.false 459460146963 549755813888 72660648989985 18913524143095808 Bool.false 143814544029 1099511627776 290471828889551 75654096572383232

noncomputable def ep996 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 12) qz937 Bool.false 796896776589 1099511627776 272460989013165 75654096572383232 Bool.true 4662275697 34359738368 68062838767575 18913524143095808 Bool.false

noncomputable abbrev qz938 := (@HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast 11) qz65)

noncomputable def ep997 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 12) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 11) qz938) Bool.false 796896776589 1099511627776 272460989013165 75654096572383232 Bool.true 4662275697 34359738368 68062838767575 18913524143095808

noncomputable def ep998 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 11) qz938 Bool.false 783654856801 1099511627776 253496993906089 75654096572383232 Bool.false 182057196719 1099511627776 253218150098239 75654096572383232 Bool.false

noncomputable abbrev qz939 := (@HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast 10) qz65)

noncomputable def ep999 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 11) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 10) qz939) Bool.false 783654856801 1099511627776 253496993906089 75654096572383232 Bool.false 182057196719 1099511627776 253218150098239 75654096572383232

noncomputable def ep1000 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 10) qz939 Bool.false 281783245099 274877906944 116758139657867 37827048286191616 Bool.false 128063233493 1099511627776 233297505463831 75654096572383232 Bool.true

noncomputable def ep1001 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 10) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 9) (@HPow.hPow Complex Complex Complex qz16 qz839 qz65)) Bool.false 281783245099 274877906944 116758139657867 37827048286191616 Bool.false 128063233493 1099511627776 233297505463831 75654096572383232

noncomputable def ep1002 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 9) (@HPow.hPow Complex Complex Complex qz16 qz839 qz65) Bool.false 693346171273 549755813888 53125718170189 18913524143095808 Bool.true 32672618383 274877906944 53071064357247 18913524143095808 Bool.true

noncomputable abbrev qz391 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 9 1)))

noncomputable def ep1003 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz839 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz297 (Real.cos qz391)) (@HMul.hMul Real Real Real qz0 qz297 (@Neg.neg Real Real.instNeg (Real.sin qz391)))) Bool.true 129779681075 549755813888 10506703317489 37827048286191616 Bool.false 258753707025 1099511627776 21013248034843 75654096572383232 (BSN.cpow_neg_s_mk qz61 113311 1000 9 (@Eq.refl Real qz61) rfl)

noncomputable def ep1004 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz299 113311 1000 0 1 9895417793173221 4503599627370496 500000000206421 68807000000000000000 1121259685562250844731 4503599627370496000 56655500023389769931 68807000000000000000000 qz384 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 500000000206421 68807000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz841) Bool.false 41504390431577613533184 18889465931478580854784 1000000000412842 137614000000000000000 9895417793173221 4503599627370496 500000000206421 68807000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 61752 524288 24973259072661432 36028797018963968 137614 1000000000000000 rfl rfl rfl rfl (ep204 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1005 := nat_lit 286922301398419029809344356857942058694256302578866218515703106885449920126081

noncomputable def ep1006 := nat_lit 64457872992477703836448652143217527371994405588985642067031279655557635201

noncomputable def ep1007 := nat_lit 860637988449272134020360173269539741028024918925420684262975258097038645107841

noncomputable def ep1008 := BSN.cos_dyadic_bound_f 1683292143 2147483648 3 2 1048576 275497 ep1005 ep104 ep1006 ep1007 ep106 ep1006 742606 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1683292143) qz272 0 2 ep1005 ep104 ep1006 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1683292143) qz273 0 2 ep1007 ep106 ep1006 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz940 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 130531807) qz289)

noncomputable def ep1009 := @Enclosure.Real.IsNear.cos_image qz391 qz940 Bool.false 130531807 524288 27 32768 Bool.true 742606 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz391 Bool.false 1121259685562250844731 4503599627370496000 56655500023389769931 68807000000000000000000 130531807 524288 27 32768 (ep1004 rfl) rfl) (Enclosure.sfrac_false_div 130531807 524288) (BSN.cos_reduce2 qz940 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 59225577106899032080384) qz290) 226375608064910080 72057594037927936 Bool.false 742606 1048576 39 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q2 130531807 524288 226375608064910080 72057594037927936 39 59225577106899032080384 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 742606 1048576 59225577106899032080384 75557863725914323419136 1683292143 2147483648 275497 275228 (ep1008 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1010 := nat_lit 8028566060790538443662236062631937601

noncomputable def ep1011 := BSN.sin_dyadic_bound_f 1683292143 2147483648 2 1 1048576 275497 ep1010 ep178 ep1010 ep1010 ep179 ep1010 740301 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1683292143) qz268 0 1 ep1010 ep178 ep1010 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1683292143) qz269 0 1 ep1010 ep179 ep1010 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1012 := @Enclosure.Real.IsNear.sin_image qz391 qz940 Bool.false 130531807 524288 27 32768 Bool.true 740301 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz391 Bool.false 1121259685562250844731 4503599627370496000 56655500023389769931 68807000000000000000000 130531807 524288 27 32768 (ep1004 rfl) rfl) (Enclosure.sfrac_false_div 130531807 524288) (BSN.sin_reduce2 qz940 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 59225577106899032080384) qz290) 226375608064910080 72057594037927936 Bool.false 740301 1048576 39 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q2 130531807 524288 226375608064910080 72057594037927936 39 59225577106899032080384 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 740301 1048576 59225577106899032080384 75557863725914323419136 1683292143 2147483648 275497 275228 (ep1011 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1013 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz297 (Real.cos qz391)) (@HMul.hMul Real Real Real qz0 qz297 (@Neg.neg Real Real.instNeg (Real.sin qz391))) Bool.true 129779681075 549755813888 10506703317489 37827048286191616 Bool.false 258753707025 1099511627776 21013248034843 75654096572383232 (@Enclosure.Real.IsNear.mulLit_ft qz297 (Real.cos qz391) 349525 1048576 1 1048576 371303 524288 1874173 2254667776 129779681075 549755813888 10506703317489 37827048286191616 qz571 (@Enclosure.Real.IsNear.recentre' (Real.cos qz391) Bool.true 742606 1048576 3748346 4509335552 371303 524288 1874173 2254667776 (ep1009 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz297 (@Neg.neg Real Real.instNeg (Real.sin qz391)) 349525 1048576 1 1048576 740301 1048576 1874173 2254667776 258753707025 1099511627776 21013248034843 75654096572383232 qz571 (@Enclosure.Real.IsNear.neg (Real.sin qz391) Bool.true 740301 1048576 1874173 2254667776 (@Enclosure.Real.IsNear.recentre' (Real.sin qz391) Bool.true 740301 1048576 3748346 4509335552 740301 1048576 1874173 2254667776 (ep1012 rfl rfl) rfl)) rfl)

noncomputable def ep1014 := @ep1002 129779681075 549755813888 10506703317489 37827048286191616 Bool.false 258753707025 1099511627776 21013248034843 75654096572383232 Bool.false 309823954498805064269824 281783245099 274877906944 116758139657867 37827048286191616 Bool.false 35201753579036598075392 128063233493 1099511627776 233297505463831 75654096572383232 EMRow35.d17 (ep1003 ep1013) rfl rfl

noncomputable abbrev qz392 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 10 1)))

noncomputable def ep1015 := @Enclosure.Complex.IsNear.of_eq qz939 (Complex.mk (@HMul.hMul Real Real Real qz0 qz300 (Real.cos qz392)) (@HMul.hMul Real Real Real qz0 qz300 (@Neg.neg Real Real.instNeg (Real.sin qz392)))) Bool.true 343478123595 1099511627776 19980714590355 75654096572383232 Bool.false 26996981613 549755813888 2490080579301 9456762071547904 (BSN.cpow_neg_s_mk qz61 113311 1000 10 (@Eq.refl Real qz61) rfl)

noncomputable def ep1016 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz302 113311 1000 0 1 10369917190100709 4503599627370496 500000000206421 68807000000000000000 1175025686727501437499 4503599627370496000 56655500023389769931 68807000000000000000000 qz384 (BSN.isNear_log_sfrac 10 1 10369917190100709 4503599627370496 500000000206421 68807000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz844) Bool.false 43494585150108164161536 18889465931478580854784 1000000000412842 137614000000000000000 10369917190100709 4503599627370496 500000000206421 68807000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 116991 524288 24973259072661432 36028797018963968 137614 1000000000000000 rfl rfl rfl rfl (ep218 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1017 := nat_lit 12570795752063643790941672045610000

noncomputable def ep1018 := BSN.cos_dyadic_bound_f 334842590 2147483648 2 1 1048576 275497 ep1017 ep118 ep1017 ep1017 ep119 ep1017 1035855 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 334842590) qz272 0 1 ep1017 ep118 ep1017 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 334842590) qz273 0 1 ep1017 ep119 ep1017 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz941 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 136790993) qz289)

noncomputable def ep1019 := @Enclosure.Real.IsNear.cos_image qz392 qz941 Bool.false 136790993 524288 865 1048576 Bool.true 1035855 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz392 Bool.false 1175025686727501437499 4503599627370496000 56655500023389769931 68807000000000000000000 136790993 524288 865 1048576 (ep1016 rfl) rfl) (Enclosure.sfrac_false_div 136790993 524288) (BSN.cos_reduce2 qz941 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11781226289578435936256) qz290) 226375608064910080 72057594037927936 Bool.false 1035855 1048576 41 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q2 136790993 524288 226375608064910080 72057594037927936 41 11781226289578435936256 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1035855 1048576 11781226289578435936256 75557863725914323419136 334842590 2147483648 275497 275228 (ep1018 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1020 := BSN.sin_dyadic_bound_f 334842590 2147483648 1 0 1048576 275497 0 1 1 0 1 1 162834 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 334842590) qz268 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 334842590) qz269 0 0 rfl) rfl rfl

noncomputable def ep1021 := @Enclosure.Real.IsNear.sin_image qz392 qz941 Bool.false 136790993 524288 865 1048576 Bool.true 162834 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz392 Bool.false 1175025686727501437499 4503599627370496000 56655500023389769931 68807000000000000000000 136790993 524288 865 1048576 (ep1016 rfl) rfl) (Enclosure.sfrac_false_div 136790993 524288) (BSN.sin_reduce2 qz941 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11781226289578435936256) qz290) 226375608064910080 72057594037927936 Bool.false 162834 1048576 41 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q2 136790993 524288 226375608064910080 72057594037927936 41 11781226289578435936256 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 162834 1048576 11781226289578435936256 75557863725914323419136 334842590 2147483648 275497 275228 (ep1020 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1022 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz300 (Real.cos qz392)) (@HMul.hMul Real Real Real qz0 qz300 (@Neg.neg Real Real.instNeg (Real.sin qz392))) Bool.true 343478123595 1099511627776 19980714590355 75654096572383232 Bool.false 26996981613 549755813888 2490080579301 9456762071547904 (@Enclosure.Real.IsNear.mulLit_ft qz300 (Real.cos qz392) 331589 1048576 1 1048576 1035855 1048576 60042343 72149368832 343478123595 1099511627776 19980714590355 75654096572383232 qz572 (@Enclosure.Real.IsNear.recentre' (Real.cos qz392) Bool.true 1035855 1048576 120084686 144298737664 1035855 1048576 60042343 72149368832 (ep1019 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz300 (@Neg.neg Real Real.instNeg (Real.sin qz392)) 331589 1048576 1 1048576 81417 524288 60042343 72149368832 26996981613 549755813888 2490080579301 9456762071547904 qz572 (@Enclosure.Real.IsNear.neg (Real.sin qz392) Bool.true 81417 524288 60042343 72149368832 (@Enclosure.Real.IsNear.recentre' (Real.sin qz392) Bool.true 162834 1048576 120084686 144298737664 81417 524288 60042343 72149368832 (ep1021 rfl rfl) rfl)) rfl)

noncomputable def ep1023 := @ep1000 343478123595 1099511627776 19980714590355 75654096572383232 Bool.false 26996981613 549755813888 2490080579301 9456762071547904 Bool.false 215409406803958923526144 783654856801 1099511627776 253496993906089 75654096572383232 Bool.false 100087002356421568233472 182057196719 1099511627776 253218150098239 75654096572383232 (ep1001 (BSN.head_sum_c_succ qz64 9 10 rfl rfl) (ep1014 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1015 ep1022) rfl rfl

noncomputable abbrev qz393 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 11 1)))

noncomputable def ep1024 := @Enclosure.Complex.IsNear.of_eq qz938 (Complex.mk (@HMul.hMul Real Real Real qz0 qz303 (Real.cos qz393)) (@HMul.hMul Real Real Real qz0 qz303 (@Neg.neg Real Real.instNeg (Real.sin qz393)))) Bool.false 3310479947 274877906944 4740998776769 18913524143095808 Bool.true 331250019023 1099511627776 19033204972061 75654096572383232 (BSN.cpow_neg_s_mk qz61 113311 1000 11 (@Eq.refl Real qz61) rfl)

noncomputable def ep1025 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz305 113311 1000 0 1 10799156221662949 4503599627370496 500000000206421 68807000000000000000 1223663190632850414139 4503599627370496000 56655500023389769931 68807000000000000000000 qz384 (BSN.isNear_log_sfrac 11 1 10799156221662949 4503599627370496 500000000206421 68807000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz847) Bool.false 45294944137145793642496 18889465931478580854784 1000000000412842 137614000000000000000 10799156221662949 4503599627370496 500000000206421 68807000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 166961 524288 24973259072661432 36028797018963968 137614 1000000000000000 rfl rfl rfl rfl (ep233 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1026 := nat_lit 4186838417331224283526583238110094872816508873838006513880745625983003313370241

noncomputable def ep1027 := nat_lit 13642066111666223297202063605850810748535111553696677320417695242882533880961

noncomputable def ep1028 := nat_lit 12533231119770340403985345587118582996952456398406626187001401487463244872348801

noncomputable def ep1029 := BSN.cos_dyadic_bound_f 3287456529 2147483648 3 2 1048576 275497 ep1026 ep104 ep1027 ep1028 ep106 ep1027 41884 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3287456529) qz272 0 2 ep1026 ep104 ep1027 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3287456529) qz273 0 2 ep1028 ep106 ep1027 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz621 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 17806643) (@Nat.cast Real Real.instNatCast 65536))

noncomputable def ep1030 := @Enclosure.Real.IsNear.cos_image qz393 qz621 Bool.false 17806643 65536 27 32768 Bool.false 41884 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz393 Bool.false 1223663190632850414139 4503599627370496000 56655500023389769931 68807000000000000000000 17806643 65536 27 32768 (ep1025 rfl) rfl) (Enclosure.sfrac_false_div 17806643 65536) (BSN.cos_reduce0 qz621 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14458386720207547662336) qz582) 226375608064910080 72057594037927936 Bool.false 41884 1048576 43 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q0 17806643 65536 226375608064910080 72057594037927936 43 14458386720207547662336 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 41884 1048576 14458386720207547662336 9444732965739290427392 3287456529 2147483648 275497 275228 (ep1029 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1031 := nat_lit 7525395498306870731710088177713490122470887883665454383129007970575099936961665

noncomputable def ep1032 := nat_lit 19687282007575297078664284743411572817640411419465443049676249368732023351473281

noncomputable def ep1033 := BSN.sin_dyadic_bound_f 3287456529 2147483648 3 2 1048576 275497 ep1031 ep97 ep1027 ep1032 ep100 ep1027 1047739 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3287456529) qz268 0 2 ep1031 ep97 ep1027 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3287456529) qz269 0 2 ep1032 ep100 ep1027 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1034 := @Enclosure.Real.IsNear.sin_image qz393 qz621 Bool.false 17806643 65536 27 32768 Bool.false 1047739 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz393 Bool.false 1223663190632850414139 4503599627370496000 56655500023389769931 68807000000000000000000 17806643 65536 27 32768 (ep1025 rfl) rfl) (Enclosure.sfrac_false_div 17806643 65536) (BSN.sin_reduce0 qz621 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14458386720207547662336) qz582) 226375608064910080 72057594037927936 Bool.false 1047739 1048576 43 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q0 17806643 65536 226375608064910080 72057594037927936 43 14458386720207547662336 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1047739 1048576 14458386720207547662336 9444732965739290427392 3287456529 2147483648 275497 275228 (ep1033 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1035 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz303 (Real.cos qz393)) (@HMul.hMul Real Real Real qz0 qz303 (@Neg.neg Real Real.instNeg (Real.sin qz393))) Bool.false 3310479947 274877906944 4740998776769 18913524143095808 Bool.true 331250019023 1099511627776 19033204972061 75654096572383232 (@Enclosure.Real.IsNear.mulLit_ff qz303 (Real.cos qz393) 316157 1048576 1 1048576 10471 262144 1874173 2254667776 3310479947 274877906944 4740998776769 18913524143095808 qz573 (@Enclosure.Real.IsNear.recentre' (Real.cos qz393) Bool.false 41884 1048576 3748346 4509335552 10471 262144 1874173 2254667776 (ep1030 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz303 (@Neg.neg Real Real.instNeg (Real.sin qz393)) 316157 1048576 1 1048576 1047739 1048576 1874173 2254667776 331250019023 1099511627776 19033204972061 75654096572383232 qz573 (@Enclosure.Real.IsNear.neg (Real.sin qz393) Bool.false 1047739 1048576 1874173 2254667776 (@Enclosure.Real.IsNear.recentre' (Real.sin qz393) Bool.false 1047739 1048576 3748346 4509335552 1047739 1048576 1874173 2254667776 (ep1034 rfl rfl) rfl)) rfl)

noncomputable def ep1036 := @ep998 3310479947 274877906944 4740998776769 18913524143095808 Bool.true 331250019023 1099511627776 19033204972061 75654096572383232 Bool.false 219049317999204699734016 796896776589 1099511627776 272460989013165 75654096572383232 Bool.true 164039242903966558715904 4662275697 34359738368 68062838767575 18913524143095808 (ep999 (BSN.head_sum_c_succ qz64 10 11 rfl rfl) (ep1023 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1024 ep1035) rfl rfl

noncomputable abbrev qz394 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 12 1)))

noncomputable def ep1037 := @Enclosure.Complex.IsNear.of_eq qz937 (Complex.mk (@HMul.hMul Real Real Real qz0 qz306 (Real.cos qz394)) (@HMul.hMul Real Real Real qz0 qz306 (@Neg.neg Real Real.instNeg (Real.sin qz394)))) Bool.false 122023517337 1099511627776 18181606946775 75654096572383232 Bool.false 293007366333 1099511627776 18220473819251 75654096572383232 (BSN.cpow_neg_s_mk qz61 113311 1000 12 (@Eq.refl Real qz61) rfl)

noncomputable def ep1038 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz308 113311 1000 0 1 11191020447815397 4503599627370496 500000000206421 68807000000000000000 1268065717962410449467 4503599627370496000 56655500023389769931 68807000000000000000000 qz384 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 500000000206421 68807000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz850) Bool.false 46938541828353910898688 18889465931478580854784 1000000000412842 137614000000000000000 11191020447815397 4503599627370496 500000000206421 68807000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 212580 524288 24973259072661432 36028797018963968 137614 1000000000000000 rfl rfl rfl rfl (ep248 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1039 := nat_lit 515686221104367347942452630630855696

noncomputable def ep1040 := BSN.sin_dyadic_bound_f 847415458 2147483648 2 1 1048576 275497 ep1039 ep178 ep1039 ep1039 ep179 ep1039 403121 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 847415458) qz268 0 1 ep1039 ep178 ep1039 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 847415458) qz269 0 1 ep1039 ep179 ep1039 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz942 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 295244557) qz277)

noncomputable def ep1041 := @Enclosure.Real.IsNear.cos_image qz394 qz942 Bool.false 295244557 1048576 27 32768 Bool.false 403121 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz394 Bool.false 1268065717962410449467 4503599627370496000 56655500023389769931 68807000000000000000000 295244557 1048576 27 32768 (ep1038 rfl) rfl) (Enclosure.sfrac_false_div 295244557 1048576) (BSN.cos_reduce3 qz942 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 59631561621213108240384) qz279) 226375608064910080 72057594037927936 Bool.false 403121 1048576 44 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q3 295244557 1048576 226375608064910080 72057594037927936 44 59631561621213108240384 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 403121 1048576 59631561621213108240384 151115727451828646838272 847415458 2147483648 275497 275228 (ep1040 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1042 := BSN.cos_dyadic_bound_f 847415458 2147483648 2 1 1048576 275497 ep1039 ep118 ep1039 ep1039 ep119 ep1039 967989 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 847415458) qz272 0 1 ep1039 ep118 ep1039 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 847415458) qz273 0 1 ep1039 ep119 ep1039 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1043 := @Enclosure.Real.IsNear.sin_image qz394 qz942 Bool.false 295244557 1048576 27 32768 Bool.true 967989 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz394 Bool.false 1268065717962410449467 4503599627370496000 56655500023389769931 68807000000000000000000 295244557 1048576 27 32768 (ep1038 rfl) rfl) (Enclosure.sfrac_false_div 295244557 1048576) (BSN.sin_reduce3 qz942 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 59631561621213108240384) qz279) 226375608064910080 72057594037927936 Bool.false 967989 1048576 44 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q3 295244557 1048576 226375608064910080 72057594037927936 44 59631561621213108240384 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 967989 1048576 59631561621213108240384 151115727451828646838272 847415458 2147483648 275497 275228 (ep1042 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1044 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz306 (Real.cos qz394)) (@HMul.hMul Real Real Real qz0 qz306 (@Neg.neg Real Real.instNeg (Real.sin qz394))) Bool.false 122023517337 1099511627776 18181606946775 75654096572383232 Bool.false 293007366333 1099511627776 18220473819251 75654096572383232 (@Enclosure.Real.IsNear.mulLit_ff qz306 (Real.cos qz394) 302697 1048576 1 1048576 403121 1048576 1874173 2254667776 122023517337 1099511627776 18181606946775 75654096572383232 qz574 (@Enclosure.Real.IsNear.recentre' (Real.cos qz394) Bool.false 403121 1048576 3748346 4509335552 403121 1048576 1874173 2254667776 (ep1041 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz306 (@Neg.neg Real Real.instNeg (Real.sin qz394)) 302697 1048576 1 1048576 967989 1048576 1874173 2254667776 293007366333 1099511627776 18220473819251 75654096572383232 qz574 (@Enclosure.Real.IsNear.neg (Real.sin qz394) Bool.true 967989 1048576 1874173 2254667776 (@Enclosure.Real.IsNear.recentre' (Real.sin qz394) Bool.true 967989 1048576 3748346 4509335552 967989 1048576 1874173 2254667776 (ep1043 rfl rfl) rfl)) rfl)

noncomputable def ep1045 := @ep996 122023517337 1099511627776 18181606946775 75654096572383232 Bool.false 293007366333 1099511627776 18220473819251 75654096572383232 Bool.false 1010363548170976625688576 459460146963 549755813888 72660648989985 18913524143095808 Bool.false 4941430106349656604672 143814544029 1099511627776 290471828889551 75654096572383232 (ep997 (BSN.head_sum_c_succ qz64 11 12 rfl rfl) (ep1036 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1037 ep1044) rfl rfl

noncomputable abbrev qz395 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 13 1)))

noncomputable def ep1046 := @Enclosure.Complex.IsNear.of_eq qz936 (Complex.mk (@HMul.hMul Real Real Real qz0 qz309 (Real.cos qz395)) (@HMul.hMul Real Real Real qz0 qz309 (@Neg.neg Real Real.instNeg (Real.sin qz395)))) Bool.true 6014510463 549755813888 8722294814399 37827048286191616 Bool.true 304712415657 1099511627776 17513836787177 75654096572383232 (BSN.cpow_neg_s_mk qz61 113311 1000 13 (@Eq.refl Real qz61) rfl)

noncomputable def ep1047 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz311 113311 1000 0 1 11551497052968677 4503599627370496 500000000206421 68807000000000000000 1308911682568933759547 4503599627370496000 56655500023389769931 68807000000000000000000 qz384 (BSN.isNear_log_sfrac 13 1 11551497052968677 4503599627370496 500000000206421 68807000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz853) Bool.false 48450490295254733815808 18889465931478580854784 1000000000412842 137614000000000000000 11551497052968677 4503599627370496 500000000206421 68807000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 254545 524288 24973259072661432 36028797018963968 137614 1000000000000000 rfl rfl rfl rfl (ep263 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1048 := BSN.sin_dyadic_bound_f 84732117 2147483648 1 0 1048576 275497 0 1 1 0 1 1 41362 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 84732117) qz268 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 84732117) qz269 0 0 rfl) rfl rfl

noncomputable abbrev qz943 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 304754749) qz277)

noncomputable def ep1049 := @Enclosure.Real.IsNear.cos_image qz395 qz943 Bool.false 304754749 1048576 27 32768 Bool.true 41362 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz395 Bool.false 1308911682568933759547 4503599627370496000 56655500023389769931 68807000000000000000000 304754749 1048576 27 32768 (ep1047 rfl) rfl) (Enclosure.sfrac_false_div 304754749 1048576) (BSN.cos_reduce1 qz943 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 5962492725086103011328) qz279) 226375608064910080 72057594037927936 Bool.false 41362 1048576 46 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q1 304754749 1048576 226375608064910080 72057594037927936 46 5962492725086103011328 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 41362 1048576 5962492725086103011328 151115727451828646838272 84732117 2147483648 275497 275228 (ep1048 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1050 := BSN.cos_dyadic_bound_f 84732117 2147483648 1 0 1048576 275497 0 1 1 0 1 1 1047759 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 84732117) qz272 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 84732117) qz273 0 0 rfl) rfl rfl

noncomputable def ep1051 := @Enclosure.Real.IsNear.sin_image qz395 qz943 Bool.false 304754749 1048576 27 32768 Bool.false 1047759 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz395 Bool.false 1308911682568933759547 4503599627370496000 56655500023389769931 68807000000000000000000 304754749 1048576 27 32768 (ep1047 rfl) rfl) (Enclosure.sfrac_false_div 304754749 1048576) (BSN.sin_reduce1 qz943 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 5962492725086103011328) qz279) 226375608064910080 72057594037927936 Bool.false 1047759 1048576 46 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q1 304754749 1048576 226375608064910080 72057594037927936 46 5962492725086103011328 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1047759 1048576 5962492725086103011328 151115727451828646838272 84732117 2147483648 275497 275228 (ep1050 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1052 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz309 (Real.cos qz395)) (@HMul.hMul Real Real Real qz0 qz309 (@Neg.neg Real Real.instNeg (Real.sin qz395))) Bool.true 6014510463 549755813888 8722294814399 37827048286191616 Bool.true 304712415657 1099511627776 17513836787177 75654096572383232 (@Enclosure.Real.IsNear.mulLit_ft qz309 (Real.cos qz395) 290823 1048576 1 1048576 20681 524288 1874173 2254667776 6014510463 549755813888 8722294814399 37827048286191616 qz575 (@Enclosure.Real.IsNear.recentre' (Real.cos qz395) Bool.true 41362 1048576 3748346 4509335552 20681 524288 1874173 2254667776 (ep1049 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz309 (@Neg.neg Real Real.instNeg (Real.sin qz395)) 290823 1048576 1 1048576 1047759 1048576 1874173 2254667776 304712415657 1099511627776 17513836787177 75654096572383232 qz575 (@Enclosure.Real.IsNear.neg (Real.sin qz395) Bool.false 1047759 1048576 1874173 2254667776 (@Enclosure.Real.IsNear.recentre' (Real.sin qz395) Bool.false 1047759 1048576 3748346 4509335552 1047759 1048576 1874173 2254667776 (ep1051 rfl rfl) rfl)) rfl)

noncomputable def ep1053 := @ep994 6014510463 549755813888 8722294814399 37827048286191616 Bool.true 304712415657 1099511627776 17513836787177 75654096572383232 Bool.false 249284374948019699712000 113361409125 137438953472 154043592794369 37827048286191616 Bool.true 176909080739396167139328 40224467907 274877906944 38498208209591 9456762071547904 (ep995 (BSN.head_sum_c_succ qz64 12 13 rfl rfl) (ep1045 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1046 ep1052) rfl rfl

noncomputable abbrev qz396 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 14 1)))

noncomputable def ep1054 := @Enclosure.Complex.IsNear.of_eq qz935 (Complex.mk (@HMul.hMul Real Real Real qz0 qz312 (Real.cos qz396)) (@HMul.hMul Real Real Real qz0 qz312 (@Neg.neg Real Real.instNeg (Real.sin qz396)))) Bool.true 61339307597 274877906944 1055421750069 4728381035773952 Bool.false 80856551089 549755813888 8433105587907 37827048286191616 (BSN.cpow_neg_s_mk qz61 113311 1000 14 (@Eq.refl Real qz61) rfl)

noncomputable def ep1055 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz314 113311 1000 0 1 11885250371606245 4503599627370496 500000000206421 68807000000000000000 269345920971415045439 900719925474099200 56655500023389769931 68807000000000000000000 qz384 (BSN.isNear_log_sfrac 14 1 11885250371606245 4503599627370496 500000000206421 68807000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz856) Bool.false 49850353174629559828480 18889465931478580854784 1000000000412842 137614000000000000000 11885250371606245 4503599627370496 500000000206421 68807000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 293399 524288 24973259072661432 36028797018963968 137614 1000000000000000 rfl rfl rfl rfl (ep277 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1056 := nat_lit 2452559642735656945715091234983400625

noncomputable def ep1057 := BSN.cos_dyadic_bound_f 1251425195 2147483648 2 1 1048576 275497 ep1056 ep118 ep1056 ep1056 ep119 ep1056 875516 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1251425195) qz272 0 1 ep1056 ep118 ep1056 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1251425195) qz273 0 1 ep1056 ep119 ep1056 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz622 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 19597495) (@Nat.cast Real Real.instNatCast 65536))

noncomputable def ep1058 := @Enclosure.Real.IsNear.cos_image qz396 qz622 Bool.false 19597495 65536 865 1048576 Bool.true 875516 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz396 Bool.false 269345920971415045439 900719925474099200 56655500023389769931 68807000000000000000000 19597495 65536 865 1048576 (ep1055 rfl) rfl) (Enclosure.sfrac_false_div 19597495 65536) (BSN.cos_reduce2 qz622 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 5503826213675141693440) qz582) 226375608064910080 72057594037927936 Bool.false 875516 1048576 47 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q2 19597495 65536 226375608064910080 72057594037927936 47 5503826213675141693440 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 875516 1048576 5503826213675141693440 9444732965739290427392 1251425195 2147483648 275497 275228 (ep1057 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1059 := BSN.sin_dyadic_bound_f 1251425195 2147483648 2 1 1048576 275497 ep1056 ep178 ep1056 ep1056 ep179 ep1056 577046 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1251425195) qz268 0 1 ep1056 ep178 ep1056 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1251425195) qz269 0 1 ep1056 ep179 ep1056 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1060 := @Enclosure.Real.IsNear.sin_image qz396 qz622 Bool.false 19597495 65536 865 1048576 Bool.true 577046 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz396 Bool.false 269345920971415045439 900719925474099200 56655500023389769931 68807000000000000000000 19597495 65536 865 1048576 (ep1055 rfl) rfl) (Enclosure.sfrac_false_div 19597495 65536) (BSN.sin_reduce2 qz622 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 5503826213675141693440) qz582) 226375608064910080 72057594037927936 Bool.false 577046 1048576 47 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q2 19597495 65536 226375608064910080 72057594037927936 47 5503826213675141693440 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 577046 1048576 5503826213675141693440 9444732965739290427392 1251425195 2147483648 275497 275228 (ep1059 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1061 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz312 (Real.cos qz396)) (@HMul.hMul Real Real Real qz0 qz312 (@Neg.neg Real Real.instNeg (Real.sin qz396))) Bool.true 61339307597 274877906944 1055421750069 4728381035773952 Bool.false 80856551089 549755813888 8433105587907 37827048286191616 (@Enclosure.Real.IsNear.mulLit_ft qz312 (Real.cos qz396) 280243 1048576 1 1048576 218879 262144 60042343 72149368832 61339307597 274877906944 1055421750069 4728381035773952 qz576 (@Enclosure.Real.IsNear.recentre' (Real.cos qz396) Bool.true 875516 1048576 120084686 144298737664 218879 262144 60042343 72149368832 (ep1058 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz312 (@Neg.neg Real Real.instNeg (Real.sin qz396)) 280243 1048576 1 1048576 288523 524288 60042343 72149368832 80856551089 549755813888 8433105587907 37827048286191616 qz576 (@Enclosure.Real.IsNear.neg (Real.sin qz396) Bool.true 288523 524288 60042343 72149368832 (@Enclosure.Real.IsNear.recentre' (Real.sin qz396) Bool.true 577046 1048576 120084686 144298737664 288523 524288 60042343 72149368832 (ep1060 rfl rfl) rfl)) rfl)

noncomputable def ep1062 := @ep992 61339307597 274877906944 1055421750069 4728381035773952 Bool.false 80856551089 549755813888 8433105587907 37827048286191616 Bool.false 22730136625673683337216 165383510653 274877906944 162486966794921 37827048286191616 Bool.false 112044433630402969600 407615275 549755813888 162425938426271 37827048286191616 (ep993 (BSN.head_sum_c_succ qz64 13 14 rfl rfl) (ep1053 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1054 ep1061) rfl rfl

noncomputable abbrev qz397 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 15 1)))

noncomputable def ep1063 := @Enclosure.Complex.IsNear.of_eq qz934 (Complex.mk (@HMul.hMul Real Real Real qz0 qz315 (Real.cos qz397)) (@HMul.hMul Real Real Real qz0 qz315 (@Neg.neg Real Real.instNeg (Real.sin qz397)))) Bool.false 73754992479 549755813888 4073368174193 18913524143095808 Bool.false 121280326137 549755813888 127481477993 591047629471744 (BSN.cpow_neg_s_mk qz61 113311 1000 15 (@Eq.refl Real qz61) rfl)

noncomputable def ep1064 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz317 113311 1000 0 1 12195965485668069 4503599627370496 500000000206421 68807000000000000000 1381937045146534566459 4503599627370496000 56655500023389769931 68807000000000000000000 qz384 (BSN.isNear_log_sfrac 15 1 12195965485668069 4503599627370496 500000000206421 68807000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz859) Bool.false 51153586820399524478976 18889465931478580854784 1000000000412842 137614000000000000000 12195965485668069 4503599627370496 500000000206421 68807000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 329571 524288 24973259072661432 36028797018963968 137614 1000000000000000 rfl rfl rfl rfl (ep292 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1065 := nat_lit 1895401578537178987333898467547283456

noncomputable def ep1066 := BSN.sin_dyadic_bound_f 1173343872 2147483648 2 1 1048576 275497 ep1065 ep178 ep1065 ep1065 ep179 ep1065 544838 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1173343872) qz268 0 1 ep1065 ep178 ep1065 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1173343872) qz269 0 1 ep1065 ep179 ep1065 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz944 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 321757291) qz277)

noncomputable def ep1067 := @Enclosure.Real.IsNear.cos_image qz397 qz944 Bool.false 321757291 1048576 865 1048576 Bool.false 544838 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz397 Bool.false 1381937045146534566459 4503599627370496000 56655500023389769931 68807000000000000000000 321757291 1048576 865 1048576 (ep1064 rfl) rfl) (Enclosure.sfrac_false_div 321757291 1048576) (BSN.cos_reduce3 qz944 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 82566734800013232177152) qz279) 226375608064910080 72057594037927936 Bool.false 544838 1048576 48 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q3 321757291 1048576 226375608064910080 72057594037927936 48 82566734800013232177152 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 544838 1048576 82566734800013232177152 151115727451828646838272 1173343872 2147483648 275497 275228 (ep1066 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1068 := BSN.cos_dyadic_bound_f 1173343872 2147483648 2 1 1048576 275497 ep1065 ep118 ep1065 ep1065 ep119 ep1065 895914 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1173343872) qz272 0 1 ep1065 ep118 ep1065 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1173343872) qz273 0 1 ep1065 ep119 ep1065 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1069 := @Enclosure.Real.IsNear.sin_image qz397 qz944 Bool.false 321757291 1048576 865 1048576 Bool.true 895914 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz397 Bool.false 1381937045146534566459 4503599627370496000 56655500023389769931 68807000000000000000000 321757291 1048576 865 1048576 (ep1064 rfl) rfl) (Enclosure.sfrac_false_div 321757291 1048576) (BSN.sin_reduce3 qz944 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 82566734800013232177152) qz279) 226375608064910080 72057594037927936 Bool.false 895914 1048576 48 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q3 321757291 1048576 226375608064910080 72057594037927936 48 82566734800013232177152 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 895914 1048576 82566734800013232177152 151115727451828646838272 1173343872 2147483648 275497 275228 (ep1068 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1070 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz315 (Real.cos qz397)) (@HMul.hMul Real Real Real qz0 qz315 (@Neg.neg Real Real.instNeg (Real.sin qz397))) Bool.false 73754992479 549755813888 4073368174193 18913524143095808 Bool.false 121280326137 549755813888 127481477993 591047629471744 (@Enclosure.Real.IsNear.mulLit_ff qz315 (Real.cos qz397) 270741 1048576 1 1048576 272419 524288 60042343 72149368832 73754992479 549755813888 4073368174193 18913524143095808 qz577 (@Enclosure.Real.IsNear.recentre' (Real.cos qz397) Bool.false 544838 1048576 120084686 144298737664 272419 524288 60042343 72149368832 (ep1067 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz315 (@Neg.neg Real Real.instNeg (Real.sin qz397)) 270741 1048576 1 1048576 447957 524288 60042343 72149368832 121280326137 549755813888 127481477993 591047629471744 qz577 (@Enclosure.Real.IsNear.neg (Real.sin qz397) Bool.true 447957 524288 60042343 72149368832 (@Enclosure.Real.IsNear.recentre' (Real.sin qz397) Bool.true 895914 1048576 120084686 144298737664 447957 524288 60042343 72149368832 (ep1069 rfl rfl) rfl)) rfl)

noncomputable def ep1071 := @ep990 73754992479 549755813888 4073368174193 18913524143095808 Bool.false 121280326137 549755813888 127481477993 591047629471744 Bool.false 111194164461992715223040 404522013785 549755813888 170633703143307 37827048286191616 Bool.false 66898653271309319929856 30421985353 137438953472 170584753017823 37827048286191616 (ep991 (BSN.head_sum_c_succ qz64 14 15 rfl rfl) (ep1062 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1063 ep1070) rfl rfl

noncomputable abbrev qz398 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 16 1)))

noncomputable def ep1072 := @Enclosure.Complex.IsNear.of_eq qz933 (Complex.mk (@HMul.hMul Real Real Real qz0 qz318 (Real.cos qz398)) (@HMul.hMul Real Real Real qz0 qz318 (@Neg.neg Real Real.instNeg (Real.sin qz398)))) Bool.false 274872401937 1099511627776 15793850820297 75654096572383232 Bool.true 380369493 274877906944 3930525494253 18913524143095808 (BSN.cpow_neg_s_mk qz61 113311 1000 16 (@Eq.refl Real qz61) rfl)

noncomputable def ep1073 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz320 113311 1000 0 1 3121657384082679 1125899906842624 125000000068807 17201750000000000000 353718119847792440169 1125899906842624000 14163875007796589977 17201750000000000000000 qz384 (BSN.isNear_log_sfrac 16 1 3121657384082679 1125899906842624 125000000068807 17201750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz862) Bool.false 52372720210750067441664 18889465931478580854784 1000000000550456 137614000000000000000 3121657384082679 1125899906842624 125000000068807 17201750000000000000 (BSN.log_rat_reduce_isNear 16 1 4 32 32 0 524288 24973259072661432 36028797018963968 137614 1000000000000000 rfl rfl rfl rfl (ep307 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1074 := BSN.cos_dyadic_bound_f 11886933 2147483648 1 0 1048576 275497 0 1 1 0 1 1 1048559 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 11886933) qz272 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 11886933) qz273 0 0 rfl) rfl rfl

noncomputable abbrev qz945 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 164712835) qz289)

noncomputable def ep1075 := @Enclosure.Real.IsNear.cos_image qz398 qz945 Bool.false 164712835 524288 27 32768 Bool.false 1048559 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz398 Bool.false 353718119847792440169 1125899906842624000 14163875007796589977 17201750000000000000000 164712835 524288 27 32768 (ep1073 rfl) rfl) (Enclosure.sfrac_false_div 164712835 524288) (BSN.cos_reduce0 qz945 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 418234305300523909120) qz290) 226375608064910080 72057594037927936 Bool.false 1048559 1048576 50 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q0 164712835 524288 226375608064910080 72057594037927936 50 418234305300523909120 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1048559 1048576 418234305300523909120 75557863725914323419136 11886933 2147483648 275497 275228 (ep1074 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1076 := BSN.sin_dyadic_bound_f 11886933 2147483648 1 0 1048576 275497 0 1 1 0 1 1 5804 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 11886933) qz268 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 11886933) qz269 0 0 rfl) rfl rfl

noncomputable def ep1077 := @Enclosure.Real.IsNear.sin_image qz398 qz945 Bool.false 164712835 524288 27 32768 Bool.false 5804 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz398 Bool.false 353718119847792440169 1125899906842624000 14163875007796589977 17201750000000000000000 164712835 524288 27 32768 (ep1073 rfl) rfl) (Enclosure.sfrac_false_div 164712835 524288) (BSN.sin_reduce0 qz945 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 418234305300523909120) qz290) 226375608064910080 72057594037927936 Bool.false 5804 1048576 50 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q0 164712835 524288 226375608064910080 72057594037927936 50 418234305300523909120 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 5804 1048576 418234305300523909120 75557863725914323419136 11886933 2147483648 275497 275228 (ep1076 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1078 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz318 (Real.cos qz398)) (@HMul.hMul Real Real Real qz0 qz318 (@Neg.neg Real Real.instNeg (Real.sin qz398))) Bool.false 274872401937 1099511627776 15793850820297 75654096572383232 Bool.true 380369493 274877906944 3930525494253 18913524143095808 (@Enclosure.Real.IsNear.mulLit_ff qz318 (Real.cos qz398) 262143 1048576 1 1048576 1048559 1048576 1874173 2254667776 274872401937 1099511627776 15793850820297 75654096572383232 qz578 (@Enclosure.Real.IsNear.recentre' (Real.cos qz398) Bool.false 1048559 1048576 3748346 4509335552 1048559 1048576 1874173 2254667776 (ep1075 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz318 (@Neg.neg Real Real.instNeg (Real.sin qz398)) 262143 1048576 1 1048576 1451 262144 1874173 2254667776 380369493 274877906944 3930525494253 18913524143095808 qz578 (@Enclosure.Real.IsNear.neg (Real.sin qz398) Bool.false 1451 262144 1874173 2254667776 (@Enclosure.Real.IsNear.recentre' (Real.sin qz398) Bool.false 5804 1048576 3748346 4509335552 1451 262144 1874173 2254667776 (ep1077 rfl rfl) rfl)) rfl)

noncomputable def ep1079 := @ep988 274872401937 1099511627776 15793850820297 75654096572383232 Bool.true 380369493 274877906944 3930525494253 18913524143095808 Bool.false 595889358890195763593216 1083916429507 1099511627776 357061257106911 75654096572383232 Bool.false 8310054073863069761536 60463601213 274877906944 178445804006329 37827048286191616 (ep989 (BSN.head_sum_c_succ qz64 15 16 rfl rfl) (ep1071 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1072 ep1078) rfl rfl

theorem EMRow35.d18 : Enclosure.Complex.IsNear (BSN.headSumC qz64 17) Bool.false 1083916429507 1099511627776 357061257106911 75654096572383232 Bool.false 60463601213 274877906944 178445804006329 37827048286191616 := ep987 (BSN.head_sum_c_succ qz64 16 17 rfl rfl) (ep1079 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz946 := (@HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast 24) qz65)

noncomputable def ep1080 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 25) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 24) qz946) Bool.false 909104708145 549755813888 117311637704719 18913524143095808 Bool.true 50130095623 1099511627776 469002372459275 75654096572383232

noncomputable def ep1081 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 24) qz946 Bool.false 952389815115 549755813888 14261476813873 2364190517886976 Bool.false 78468934093 549755813888 228042171669369 37827048286191616 Bool.true

noncomputable abbrev qz947 := (@HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast 23) qz65)

noncomputable def ep1082 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 24) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 23) qz947) Bool.false 952389815115 549755813888 14261476813873 2364190517886976 Bool.false 78468934093 549755813888 228042171669369 37827048286191616

noncomputable def ep1083 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 23) qz947 Bool.false 531185917809 274877906944 221592590753429 37827048286191616 Bool.false 92302843169 1099511627776 442951148877021 75654096572383232 Bool.true

noncomputable abbrev qz948 := (@HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast 22) qz65)

noncomputable def ep1084 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 23) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 22) qz948) Bool.false 531185917809 274877906944 221592590753429 37827048286191616 Bool.false 92302843169 1099511627776 442951148877021 75654096572383232

noncomputable def ep1085 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 22) qz948 Bool.false 2133783198531 1099511627776 429759453179419 75654096572383232 Bool.true 141939287203 1099511627776 429456107061255 75654096572383232 Bool.true

noncomputable def ep1086 := nat_lit 2336180372567448549851136

noncomputable abbrev qz949 := (@HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast 21) qz65)

noncomputable def ep1087 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 22) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 21) qz949) Bool.false 2133783198531 1099511627776 429759453179419 75654096572383232 Bool.true 141939287203 1099511627776 429456107061255 75654096572383232

noncomputable def ep1088 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 21) qz949 Bool.false 1935411263975 1099511627776 415917005315511 75654096572383232 Bool.true 276907355685 1099511627776 415651791073449 75654096572383232 Bool.false

noncomputable abbrev qz950 := (@HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast 20) qz65)

noncomputable def ep1089 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 21) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 20) qz950) Bool.false 1935411263975 1099511627776 415917005315511 75654096572383232 Bool.true 276907355685 1099511627776 415651791073449 75654096572383232

noncomputable def ep1090 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 20) qz950 Bool.false 1692588602443 1099511627776 4840768094865 911495139426304 Bool.true 238391601993 1099511627776 4838295099991 911495139426304 Bool.false

noncomputable abbrev qz951 := (@HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast 19) qz65)

noncomputable def ep1091 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 20) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 19) qz951) Bool.false 1692588602443 1099511627776 4840768094865 911495139426304 Bool.true 238391601993 1099511627776 4838295099991 911495139426304

noncomputable def ep1092 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 19) qz951 Bool.false 1488545496407 1099511627776 387281603469087 75654096572383232 Bool.true 45044812321 549755813888 193546144254275 37827048286191616 Bool.false

noncomputable abbrev qz952 := (@Nat.cast Complex Complex.instNatCast 18)

noncomputable def ep1093 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 19) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 18) (@HPow.hPow Complex Complex Complex qz16 qz952 qz65)) Bool.false 1488545496407 1099511627776 387281603469087 75654096572383232 Bool.true 45044812321 549755813888 193546144254275 37827048286191616

noncomputable def ep1094 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 18) (@HPow.hPow Complex Complex Complex qz16 qz952 qz65) Bool.false 326315752669 274877906944 93097748087021 18913524143095808 Bool.false 46565165943 549755813888 186100847397859 37827048286191616 Bool.false

noncomputable abbrev qz953 := (@Nat.cast Complex Complex.instNatCast 17)

noncomputable def ep1095 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 18) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 17) (@HPow.hPow Complex Complex Complex qz16 qz953 qz65)) Bool.false 326315752669 274877906944 93097748087021 18913524143095808 Bool.false 46565165943 549755813888 186100847397859 37827048286191616

noncomputable def ep1096 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 17) (@HPow.hPow Complex Complex Complex qz16 qz953 qz65) Bool.false 1083916429507 1099511627776 357061257106911 75654096572383232 Bool.false 60463601213 274877906944 178445804006329 37827048286191616 Bool.false

noncomputable def ep1097 := nat_lit 1435151857544171226136576

noncomputable abbrev qz399 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 17 1)))

noncomputable def ep1098 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz953 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz321 (Real.cos qz399)) (@HMul.hMul Real Real Real qz0 qz321 (@Neg.neg Real Real.instNeg (Real.sin qz399)))) Bool.false 221346581169 1099511627776 15329735241173 75654096572383232 Bool.true 74362036483 549755813888 3827521695765 18913524143095808 (BSN.cpow_neg_s_mk qz61 113311 1000 17 (@Eq.refl Real qz61) rfl)

noncomputable def ep1099 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz323 113311 1000 0 1 3189913004350711 1125899906842624 125000000068807 17201750000000000000 361452232435983414121 1125899906842624000 14163875007796589977 17201750000000000000000 qz384 (BSN.isNear_log_sfrac 17 1 3189913004350711 1125899906842624 125000000068807 17201750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz873) Bool.false 53517859495200818200576 18889465931478580854784 1000000000550456 137614000000000000000 3189913004350711 1125899906842624 125000000068807 17201750000000000000 (BSN.log_rat_reduce_isNear 17 1 4 34 32 31784 524288 24973259072661432 36028797018963968 137614 1000000000000000 rfl rfl rfl rfl (ep334 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1100 := nat_lit 2605520764947415402911536424596727441

noncomputable def ep1101 := BSN.cos_dyadic_bound_f 1270496973 2147483648 2 1 1048576 275497 ep1100 ep118 ep1100 ep1100 ep119 ep1100 870357 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1270496973) qz272 0 1 ep1100 ep118 ep1100 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1270496973) qz273 0 1 ep1100 ep119 ep1100 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz954 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 336628623) qz277)

noncomputable def ep1102 := @Enclosure.Real.IsNear.cos_image qz399 qz954 Bool.false 336628623 1048576 865 1048576 Bool.false 870357 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz399 Bool.false 361452232435983414121 1125899906842624000 14163875007796589977 17201750000000000000000 336628623 1048576 865 1048576 (ep1099 rfl) rfl) (Enclosure.sfrac_false_div 336628623 1048576) (BSN.cos_reduce0 qz954 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 89403276498066720423936) qz279) 226375608064910080 72057594037927936 Bool.false 870357 1048576 51 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q0 336628623 1048576 226375608064910080 72057594037927936 51 89403276498066720423936 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 870357 1048576 89403276498066720423936 151115727451828646838272 1270496973 2147483648 275497 275228 (ep1101 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1103 := BSN.sin_dyadic_bound_f 1270496973 2147483648 2 1 1048576 275497 ep1100 ep178 ep1100 ep1100 ep179 ep1100 584798 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1270496973) qz268 0 1 ep1100 ep178 ep1100 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1270496973) qz269 0 1 ep1100 ep179 ep1100 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1104 := @Enclosure.Real.IsNear.sin_image qz399 qz954 Bool.false 336628623 1048576 865 1048576 Bool.false 584798 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz399 Bool.false 361452232435983414121 1125899906842624000 14163875007796589977 17201750000000000000000 336628623 1048576 865 1048576 (ep1099 rfl) rfl) (Enclosure.sfrac_false_div 336628623 1048576) (BSN.sin_reduce0 qz954 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 89403276498066720423936) qz279) 226375608064910080 72057594037927936 Bool.false 584798 1048576 51 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q0 336628623 1048576 226375608064910080 72057594037927936 51 89403276498066720423936 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 584798 1048576 89403276498066720423936 151115727451828646838272 1270496973 2147483648 275497 275228 (ep1103 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1105 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz321 (Real.cos qz399)) (@HMul.hMul Real Real Real qz0 qz321 (@Neg.neg Real Real.instNeg (Real.sin qz399))) Bool.false 221346581169 1099511627776 15329735241173 75654096572383232 Bool.true 74362036483 549755813888 3827521695765 18913524143095808 (@Enclosure.Real.IsNear.mulLit_ff qz321 (Real.cos qz399) 254317 1048576 1 1048576 870357 1048576 60042343 72149368832 221346581169 1099511627776 15329735241173 75654096572383232 qz580 (@Enclosure.Real.IsNear.recentre' (Real.cos qz399) Bool.false 870357 1048576 120084686 144298737664 870357 1048576 60042343 72149368832 (ep1102 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz321 (@Neg.neg Real Real.instNeg (Real.sin qz399)) 254317 1048576 1 1048576 292399 524288 60042343 72149368832 74362036483 549755813888 3827521695765 18913524143095808 qz580 (@Enclosure.Real.IsNear.neg (Real.sin qz399) Bool.false 292399 524288 60042343 72149368832 (@Enclosure.Real.IsNear.recentre' (Real.sin qz399) Bool.false 584798 1048576 120084686 144298737664 292399 524288 60042343 72149368832 (ep1104 rfl rfl) rfl)) rfl)

noncomputable def ep1106 := @ep1096 221346581169 1099511627776 15329735241173 75654096572383232 Bool.true 74362036483 549755813888 3827521695765 18913524143095808 Bool.false ep1097 326315752669 274877906944 93097748087021 18913524143095808 Bool.false 12799735350911872008192 46565165943 549755813888 186100847397859 37827048286191616 EMRow35.d18 (ep1098 ep1105) rfl rfl

noncomputable abbrev qz400 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 18 1)))

noncomputable def ep1107 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz952 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz324 (Real.cos qz400)) (@HMul.hMul Real Real Real qz0 qz324 (@Neg.neg Real Real.instNeg (Real.sin qz400)))) Bool.false 183282485731 1099511627776 14890611121003 75654096572383232 Bool.true 11451247283 68719476736 232665526763 1182095258943488 (BSN.cpow_neg_s_mk qz61 113311 1000 18 (@Eq.refl Real qz61) rfl)

noncomputable def ep1108 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz326 113311 1000 0 1 3254268794313975 1125899906842624 125000000068807 17201750000000000000 14749778054100432849 45035996273704960 14163875007796589977 17201750000000000000000 qz384 (BSN.isNear_log_sfrac 18 1 3254268794313975 1125899906842624 125000000068807 17201750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz875) Bool.false 54597570484265130393600 18889465931478580854784 1000000000550456 137614000000000000000 3254268794313975 1125899906842624 125000000068807 17201750000000000000 (BSN.log_rat_reduce_isNear 18 1 4 36 32 61752 524288 24973259072661432 36028797018963968 137614 1000000000000000 rfl rfl rfl rfl (ep348 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1109 := nat_lit 288953594838744179471506737686975550682799418078058091408109010536733291380736

noncomputable def ep1110 := nat_lit 65373566921604362091701526445461262173196433968900515610183018462964678656

noncomputable def ep1111 := nat_lit 866730037382389329690336810008035729524051861366236473193106665573273944784896

noncomputable def ep1112 := BSN.cos_dyadic_bound_f 1686262852 2147483648 3 2 1048576 275497 ep1109 ep104 ep1110 ep1111 ep106 ep1110 741581 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1686262852) qz272 0 2 ep1109 ep104 ep1110 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1686262852) qz273 0 2 ep1111 ep106 ep1110 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz955 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 343420031) qz277)

noncomputable def ep1113 := @Enclosure.Real.IsNear.cos_image qz400 qz955 Bool.false 343420031 1048576 865 1048576 Bool.false 741581 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz400 Bool.false 14749778054100432849 45035996273704960 14163875007796589977 17201750000000000000000 343420031 1048576 865 1048576 (ep1108 rfl) rfl) (Enclosure.sfrac_false_div 343420031 1048576) (BSN.cos_reduce0 qz955 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 118660199308854288187392) qz279) 226375608064910080 72057594037927936 Bool.false 741581 1048576 52 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q0 343420031 1048576 226375608064910080 72057594037927936 52 118660199308854288187392 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 741581 1048576 118660199308854288187392 151115727451828646838272 1686262852 2147483648 275497 275228 (ep1112 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1114 := nat_lit 8085392193431581590349903251522601216

noncomputable def ep1115 := BSN.sin_dyadic_bound_f 1686262852 2147483648 2 1 1048576 275497 ep1114 ep178 ep1114 ep1114 ep179 ep1114 741328 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1686262852) qz268 0 1 ep1114 ep178 ep1114 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1686262852) qz269 0 1 ep1114 ep179 ep1114 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1116 := @Enclosure.Real.IsNear.sin_image qz400 qz955 Bool.false 343420031 1048576 865 1048576 Bool.false 741328 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz400 Bool.false 14749778054100432849 45035996273704960 14163875007796589977 17201750000000000000000 343420031 1048576 865 1048576 (ep1108 rfl) rfl) (Enclosure.sfrac_false_div 343420031 1048576) (BSN.sin_reduce0 qz955 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 118660199308854288187392) qz279) 226375608064910080 72057594037927936 Bool.false 741328 1048576 52 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q0 343420031 1048576 226375608064910080 72057594037927936 52 118660199308854288187392 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 741328 1048576 118660199308854288187392 151115727451828646838272 1686262852 2147483648 275497 275228 (ep1115 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1117 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz324 (Real.cos qz400)) (@HMul.hMul Real Real Real qz0 qz324 (@Neg.neg Real Real.instNeg (Real.sin qz400))) Bool.false 183282485731 1099511627776 14890611121003 75654096572383232 Bool.true 11451247283 68719476736 232665526763 1182095258943488 (@Enclosure.Real.IsNear.mulLit_ff qz324 (Real.cos qz400) 247151 1048576 1 1048576 741581 1048576 60042343 72149368832 183282485731 1099511627776 14890611121003 75654096572383232 qz583 (@Enclosure.Real.IsNear.recentre' (Real.cos qz400) Bool.false 741581 1048576 120084686 144298737664 741581 1048576 60042343 72149368832 (ep1113 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz324 (@Neg.neg Real Real.instNeg (Real.sin qz400)) 247151 1048576 1 1048576 46333 65536 60042343 72149368832 11451247283 68719476736 232665526763 1182095258943488 qz583 (@Enclosure.Real.IsNear.neg (Real.sin qz400) Bool.false 46333 65536 60042343 72149368832 (@Enclosure.Real.IsNear.recentre' (Real.sin qz400) Bool.false 741328 1048576 120084686 144298737664 46333 65536 60042343 72149368832 (ep1116 rfl rfl) rfl)) rfl)

noncomputable def ep1118 := @ep1094 183282485731 1099511627776 14890611121003 75654096572383232 Bool.true 11451247283 68719476736 232665526763 1182095258943488 Bool.false 409168270443273632350208 1488545496407 1099511627776 387281603469087 75654096572383232 Bool.true 3095455932370445664256 45044812321 549755813888 193546144254275 37827048286191616 (ep1095 (BSN.head_sum_c_succ qz64 17 18 rfl rfl) (ep1106 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1107 ep1117) rfl rfl

noncomputable abbrev qz401 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 19 1)))

noncomputable def ep1119 := @Enclosure.Complex.IsNear.of_eq qz951 (Complex.mk (@HMul.hMul Real Real Real qz0 qz327 (Real.cos qz401)) (@HMul.hMul Real Real Real qz0 qz327 (@Neg.neg Real Real.instNeg (Real.sin qz401)))) Bool.false 51010776509 274877906944 3625537101177 18913524143095808 Bool.true 148301977351 1099511627776 14486204790703 75654096572383232 (BSN.cpow_neg_s_mk qz61 113311 1000 19 (@Eq.refl Real qz61) rfl)

noncomputable def ep1120 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz329 113311 1000 0 1 3315143513283831 1125899906842624 125000000068807 17201750000000000000 375642226633704174441 1125899906842624000 14163875007796589977 17201750000000000000000 qz384 (BSN.isNear_log_sfrac 19 1 3315143513283831 1125899906842624 125000000068807 17201750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz877) Bool.false 55618878793361701994496 18889465931478580854784 1000000000550456 137614000000000000000 3315143513283831 1125899906842624 125000000068807 17201750000000000000 (BSN.log_rat_reduce_isNear 19 1 4 38 32 90099 524288 24973259072661432 36028797018963968 137614 1000000000000000 rfl rfl rfl rfl (ep362 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1121 := nat_lit 3318434209277067587579671385817760000

noncomputable def ep1122 := BSN.cos_dyadic_bound_f 1349687740 2147483648 2 1 1048576 275497 ep1121 ep118 ep1121 ep1121 ep119 ep1121 848204 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1349687740) qz272 0 1 ep1121 ep118 ep1121 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1349687740) qz273 0 1 ep1121 ep119 ep1121 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz956 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 349844085) qz277)

noncomputable def ep1123 := @Enclosure.Real.IsNear.cos_image qz401 qz956 Bool.false 349844085 1048576 865 1048576 Bool.false 848204 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz401 Bool.false 375642226633704174441 1125899906842624000 14163875007796589977 17201750000000000000000 349844085 1048576 865 1048576 (ep1120 rfl) rfl) (Enclosure.sfrac_false_div 349844085 1048576) (BSN.cos_reduce0 qz956 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 94975831319223897948160) qz279) 226375608064910080 72057594037927936 Bool.false 848204 1048576 53 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q0 349844085 1048576 226375608064910080 72057594037927936 53 94975831319223897948160 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 848204 1048576 94975831319223897948160 151115727451828646838272 1349687740 2147483648 275497 275228 (ep1122 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1124 := BSN.sin_dyadic_bound_f 1349687740 2147483648 2 1 1048576 275497 ep1121 ep178 ep1121 ep1121 ep179 ep1121 616489 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1349687740) qz268 0 1 ep1121 ep178 ep1121 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1349687740) qz269 0 1 ep1121 ep179 ep1121 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1125 := @Enclosure.Real.IsNear.sin_image qz401 qz956 Bool.false 349844085 1048576 865 1048576 Bool.false 616489 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz401 Bool.false 375642226633704174441 1125899906842624000 14163875007796589977 17201750000000000000000 349844085 1048576 865 1048576 (ep1120 rfl) rfl) (Enclosure.sfrac_false_div 349844085 1048576) (BSN.sin_reduce0 qz956 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 94975831319223897948160) qz279) 226375608064910080 72057594037927936 Bool.false 616489 1048576 53 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q0 349844085 1048576 226375608064910080 72057594037927936 53 94975831319223897948160 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 616489 1048576 94975831319223897948160 151115727451828646838272 1349687740 2147483648 275497 275228 (ep1124 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1126 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz327 (Real.cos qz401)) (@HMul.hMul Real Real Real qz0 qz327 (@Neg.neg Real Real.instNeg (Real.sin qz401))) Bool.false 51010776509 274877906944 3625537101177 18913524143095808 Bool.true 148301977351 1099511627776 14486204790703 75654096572383232 (@Enclosure.Real.IsNear.mulLit_ff qz327 (Real.cos qz401) 240559 1048576 1 1048576 212051 262144 60042343 72149368832 51010776509 274877906944 3625537101177 18913524143095808 qz584 (@Enclosure.Real.IsNear.recentre' (Real.cos qz401) Bool.false 848204 1048576 120084686 144298737664 212051 262144 60042343 72149368832 (ep1123 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz327 (@Neg.neg Real Real.instNeg (Real.sin qz401)) 240559 1048576 1 1048576 616489 1048576 60042343 72149368832 148301977351 1099511627776 14486204790703 75654096572383232 qz584 (@Enclosure.Real.IsNear.neg (Real.sin qz401) Bool.false 616489 1048576 60042343 72149368832 (@Enclosure.Real.IsNear.recentre' (Real.sin qz401) Bool.false 616489 1048576 120084686 144298737664 616489 1048576 60042343 72149368832 (ep1125 rfl rfl) rfl)) rfl)

noncomputable def ep1127 := @ep1092 51010776509 274877906944 3625537101177 18913524143095808 Bool.true 148301977351 1099511627776 14486204790703 75654096572383232 Bool.false 465255212356801965064192 1692588602443 1099511627776 4840768094865 911495139426304 Bool.true 131057169177725877878784 238391601993 1099511627776 4838295099991 911495139426304 (ep1093 (BSN.head_sum_c_succ qz64 18 19 rfl rfl) (ep1118 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1119 ep1126) rfl rfl

noncomputable abbrev qz402 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 20 1)))

noncomputable def ep1128 := @Enclosure.Complex.IsNear.of_eq qz950 (Complex.mk (@HMul.hMul Real Real Real qz0 qz330 (Real.cos qz402)) (@HMul.hMul Real Real Real qz0 qz330 (@Neg.neg Real Real.instNeg (Real.sin qz402)))) Bool.false 60705665383 274877906944 3533313360429 18913524143095808 Bool.true 9628938423 274877906944 3518324443549 18913524143095808 (BSN.cpow_neg_s_mk qz61 113311 1000 20 (@Eq.refl Real qz61) rfl)

noncomputable def ep1129 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz332 113311 1000 0 1 3372893643545847 1125899906842624 125000000068807 17201750000000000000 382185951643823469417 1125899906842624000 14163875007796589977 17201750000000000000000 qz384 (BSN.isNear_log_sfrac 20 1 3372893643545847 1125899906842624 125000000068807 17201750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz880) Bool.false 56587765202795681021952 18889465931478580854784 1000000000550456 137614000000000000000 3372893643545847 1125899906842624 125000000068807 17201750000000000000 (BSN.log_rat_reduce_isNear 20 1 4 40 32 116991 524288 24973259072661432 36028797018963968 137614 1000000000000000 rfl rfl rfl rfl (ep373 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1130 := nat_lit 13023193787177233728392503921307281

noncomputable def ep1131 := BSN.cos_dyadic_bound_f 337815347 2147483648 2 1 1048576 275497 ep1130 ep118 ep1130 ep1130 ep119 ep1130 1035628 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 337815347) qz272 0 1 ep1130 ep118 ep1130 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 337815347) qz273 0 1 ep1130 ep119 ep1130 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz623 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 88984601) (@Nat.cast Real Real.instNatCast 262144))

noncomputable def ep1132 := @Enclosure.Real.IsNear.cos_image qz402 qz623 Bool.false 88984601 262144 27 32768 Bool.false 1035628 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz402 Bool.false 382185951643823469417 1125899906842624000 14163875007796589977 17201750000000000000000 88984601 262144 27 32768 (ep1129 rfl) rfl) (Enclosure.sfrac_false_div 88984601 262144) (BSN.cos_reduce0 qz623 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 5942910447350292938752) qz557) 226375608064910080 72057594037927936 Bool.false 1035628 1048576 54 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q0 88984601 262144 226375608064910080 72057594037927936 54 5942910447350292938752 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1035628 1048576 5942910447350292938752 37778931862957161709568 337815347 2147483648 275497 275228 (ep1131 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1133 := BSN.sin_dyadic_bound_f 337815347 2147483648 1 0 1048576 275497 0 1 1 0 1 1 164268 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 337815347) qz268 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 337815347) qz269 0 0 rfl) rfl rfl

noncomputable def ep1134 := @Enclosure.Real.IsNear.sin_image qz402 qz623 Bool.false 88984601 262144 27 32768 Bool.false 164268 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz402 Bool.false 382185951643823469417 1125899906842624000 14163875007796589977 17201750000000000000000 88984601 262144 27 32768 (ep1129 rfl) rfl) (Enclosure.sfrac_false_div 88984601 262144) (BSN.sin_reduce0 qz623 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 5942910447350292938752) qz557) 226375608064910080 72057594037927936 Bool.false 164268 1048576 54 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q0 88984601 262144 226375608064910080 72057594037927936 54 5942910447350292938752 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 164268 1048576 5942910447350292938752 37778931862957161709568 337815347 2147483648 275497 275228 (ep1133 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1135 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz330 (Real.cos qz402)) (@HMul.hMul Real Real Real qz0 qz330 (@Neg.neg Real Real.instNeg (Real.sin qz402))) Bool.false 60705665383 274877906944 3533313360429 18913524143095808 Bool.true 9628938423 274877906944 3518324443549 18913524143095808 (@Enclosure.Real.IsNear.mulLit_ff qz330 (Real.cos qz402) 234469 1048576 1 1048576 258907 262144 1874173 2254667776 60705665383 274877906944 3533313360429 18913524143095808 qz585 (@Enclosure.Real.IsNear.recentre' (Real.cos qz402) Bool.false 1035628 1048576 3748346 4509335552 258907 262144 1874173 2254667776 (ep1132 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz330 (@Neg.neg Real Real.instNeg (Real.sin qz402)) 234469 1048576 1 1048576 41067 262144 1874173 2254667776 9628938423 274877906944 3518324443549 18913524143095808 qz585 (@Enclosure.Real.IsNear.neg (Real.sin qz402) Bool.false 41067 262144 1874173 2254667776 (@Enclosure.Real.IsNear.recentre' (Real.sin qz402) Bool.false 164268 1048576 3748346 4509335552 41067 262144 1874173 2254667776 (ep1134 rfl rfl) rfl)) rfl)

noncomputable def ep1136 := @ep1090 60705665383 274877906944 3533313360429 18913524143095808 Bool.true 9628938423 274877906944 3518324443549 18913524143095808 Bool.false 532001797317289469542400 1935411263975 1099511627776 415917005315511 75654096572383232 Bool.true 76115714348090539376640 276907355685 1099511627776 415651791073449 75654096572383232 (ep1091 (BSN.head_sum_c_succ qz64 19 20 rfl rfl) (ep1127 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1128 ep1135) rfl rfl

noncomputable abbrev qz403 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 21 1)))

noncomputable def ep1137 := @Enclosure.Complex.IsNear.of_eq qz949 (Complex.mk (@HMul.hMul Real Real Real qz0 qz333 (Real.cos qz403)) (@HMul.hMul Real Real Real qz0 qz333 (@Neg.neg Real Real.instNeg (Real.sin qz403)))) Bool.false 49592983639 274877906944 3460611965977 18913524143095808 Bool.false 67484034241 549755813888 6902157993903 37827048286191616 (BSN.cpow_neg_s_mk qz61 113311 1000 21 (@Eq.refl Real qz61) rfl)

noncomputable def ep1138 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz335 113311 1000 0 1 3427826275261687 1125899906842624 125000000068807 17201750000000000000 388410423076177015657 1125899906842624000 14163875007796589977 17201750000000000000000 qz384 (BSN.isNear_log_sfrac 21 1 3427826275261687 1125899906842624 125000000068807 17201750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz883) Bool.false 57509381830540779323392 18889465931478580854784 1000000000550456 137614000000000000000 3427826275261687 1125899906842624 125000000068807 17201750000000000000 (BSN.log_rat_reduce_isNear 21 1 4 42 32 142571 524288 24973259072661432 36028797018963968 137614 1000000000000000 rfl rfl rfl rfl (ep388 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1139 := nat_lit 1228127756247910564606606110403175100003840831947853200583460762715446765875745

noncomputable def ep1140 := nat_lit 364440645791911122190587106397846100994023610038354376008668137606409548321

noncomputable def ep1141 := nat_lit 3215935029127531241676612195740814463465592807351934380157430820603378771358241

noncomputable def ep1142 := BSN.sin_dyadic_bound_f 2090274637 2147483648 3 2 1048576 275497 ep1139 ep97 ep1140 ep1141 ep100 ep1140 866942 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2090274637) qz268 0 2 ep1139 ep97 ep1140 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2090274637) qz269 0 2 ep1141 ep100 ep1140 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz957 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 361735395) qz277)

noncomputable def ep1143 := @Enclosure.Real.IsNear.cos_image qz403 qz957 Bool.false 361735395 1048576 27 32768 Bool.false 866942 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz403 Bool.false 388410423076177015657 1125899906842624000 14163875007796589977 17201750000000000000000 361735395 1048576 27 32768 (ep1138 rfl) rfl) (Enclosure.sfrac_false_div 361735395 1048576) (BSN.cos_reduce3 qz957 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 147090001221631522897920) qz279) 226375608064910080 72057594037927936 Bool.false 866942 1048576 54 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q3 361735395 1048576 226375608064910080 72057594037927936 54 147090001221631522897920 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 866942 1048576 147090001221631522897920 151115727451828646838272 2090274637 2147483648 275497 275228 (ep1142 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1144 := nat_lit 682455171535857829724643655604607431602575583797713268935704276236406607508001

noncomputable def ep1145 := nat_lit 2046636633315989666929549792601026602605738704173063098055095492434007003427361

noncomputable def ep1146 := BSN.cos_dyadic_bound_f 2090274637 2147483648 3 2 1048576 275497 ep1144 ep104 ep1140 ep1145 ep106 ep1140 589849 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2090274637) qz272 0 2 ep1144 ep104 ep1140 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2090274637) qz273 0 2 ep1145 ep106 ep1140 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1147 := @Enclosure.Real.IsNear.sin_image qz403 qz957 Bool.false 361735395 1048576 27 32768 Bool.true 589849 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz403 Bool.false 388410423076177015657 1125899906842624000 14163875007796589977 17201750000000000000000 361735395 1048576 27 32768 (ep1138 rfl) rfl) (Enclosure.sfrac_false_div 361735395 1048576) (BSN.sin_reduce3 qz957 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 147090001221631522897920) qz279) 226375608064910080 72057594037927936 Bool.false 589849 1048576 54 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q3 361735395 1048576 226375608064910080 72057594037927936 54 147090001221631522897920 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 589849 1048576 147090001221631522897920 151115727451828646838272 2090274637 2147483648 275497 275228 (ep1146 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1148 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz333 (Real.cos qz403)) (@HMul.hMul Real Real Real qz0 qz333 (@Neg.neg Real Real.instNeg (Real.sin qz403))) Bool.false 49592983639 274877906944 3460611965977 18913524143095808 Bool.false 67484034241 549755813888 6902157993903 37827048286191616 (@Enclosure.Real.IsNear.mulLit_ff qz333 (Real.cos qz403) 114409 524288 1 524288 433471 524288 1874173 2254667776 49592983639 274877906944 3460611965977 18913524143095808 qz586 (@Enclosure.Real.IsNear.recentre' (Real.cos qz403) Bool.false 866942 1048576 3748346 4509335552 433471 524288 1874173 2254667776 (ep1143 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz333 (@Neg.neg Real Real.instNeg (Real.sin qz403)) 114409 524288 1 524288 589849 1048576 1874173 2254667776 67484034241 549755813888 6902157993903 37827048286191616 qz586 (@Enclosure.Real.IsNear.neg (Real.sin qz403) Bool.true 589849 1048576 1874173 2254667776 (@Enclosure.Real.IsNear.recentre' (Real.sin qz403) Bool.true 589849 1048576 3748346 4509335552 589849 1048576 1874173 2254667776 (ep1147 rfl rfl) rfl)) rfl)

noncomputable def ep1149 := @ep1088 49592983639 274877906944 3460611965977 18913524143095808 Bool.false 67484034241 549755813888 6902157993903 37827048286191616 Bool.false 586529859484474895499264 2133783198531 1099511627776 429759453179419 75654096572383232 Bool.true 78031948358967848075264 141939287203 1099511627776 429456107061255 75654096572383232 (ep1089 (BSN.head_sum_c_succ qz64 20 21 rfl rfl) (ep1136 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1137 ep1148) rfl rfl

noncomputable abbrev qz404 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 22 1)))

noncomputable def ep1150 := @Enclosure.Complex.IsNear.of_eq qz948 (Complex.mk (@HMul.hMul Real Real Real qz0 qz336 (Real.cos qz404)) (@HMul.hMul Real Real Real qz0 qz336 (@Neg.neg Real Real.instNeg (Real.sin qz404)))) Bool.true 9039527295 1099511627776 13425728327439 75654096572383232 Bool.false 58560532593 274877906944 6747520907883 37827048286191616 (BSN.cpow_neg_s_mk qz61 113311 1000 22 (@Eq.refl Real qz61) rfl)

noncomputable def ep1151 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz338 113311 1000 0 1 3480203401436407 1125899906842624 125000000068807 17201750000000000000 394345327620160713577 1125899906842624000 14163875007796589977 17201750000000000000000 qz384 (BSN.isNear_log_sfrac 22 1 3480203401436407 1125899906842624 125000000068807 17201750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz886) Bool.false 58388124189833310502912 18889465931478580854784 1000000000550456 137614000000000000000 3480203401436407 1125899906842624 125000000068807 17201750000000000000 (BSN.log_rat_reduce_isNear 22 1 4 44 32 166961 524288 24973259072661432 36028797018963968 137614 1000000000000000 rfl rfl rfl rfl (ep399 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1152 := nat_lit 4202042244989817360300816679233733328001041644089507679582972195422805694976961

noncomputable def ep1153 := nat_lit 13740999814019860674872641468537334976667479382720354295005345037926978130881

noncomputable def ep1154 := nat_lit 12578644735341412359552704754764125314049789973503082330158905896192563128669121

noncomputable def ep1155 := BSN.cos_dyadic_bound_f 3290427239 2147483648 3 2 1048576 275497 ep1152 ep104 ep1153 ep1154 ep106 ep1153 40435 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3290427239) qz272 0 2 ep1152 ep104 ep1153 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3290427239) qz273 0 2 ep1154 ep106 ep1153 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz958 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 367262705) qz277)

noncomputable def ep1156 := @Enclosure.Real.IsNear.cos_image qz404 qz958 Bool.false 367262705 1048576 865 1048576 Bool.true 40435 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz404 Bool.false 394345327620160713577 1125899906842624000 14163875007796589977 17201750000000000000000 367262705 1048576 865 1048576 (ep1151 rfl) rfl) (Enclosure.sfrac_false_div 367262705 1048576) (BSN.cos_reduce2 qz958 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 231543232618376986624000) qz279) 226375608064910080 72057594037927936 Bool.false 40435 1048576 55 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q2 367262705 1048576 226375608064910080 72057594037927936 55 231543232618376986624000 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 40435 1048576 231543232618376986624000 151115727451828646838272 3290427239 2147483648 275497 275228 (ep1155 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1157 := nat_lit 7552683241130455360001571909445890122420540975854937539813345675730708668453825

noncomputable def ep1158 := nat_lit 19758589727071350930340037390933032730663002827286146316366849068280926643262401

noncomputable def ep1159 := BSN.sin_dyadic_bound_f 3290427239 2147483648 3 2 1048576 275497 ep1157 ep97 ep1153 ep1158 ep100 ep1153 1047796 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3290427239) qz268 0 2 ep1157 ep97 ep1153 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3290427239) qz269 0 2 ep1158 ep100 ep1153 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1160 := @Enclosure.Real.IsNear.sin_image qz404 qz958 Bool.false 367262705 1048576 865 1048576 Bool.true 1047796 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz404 Bool.false 394345327620160713577 1125899906842624000 14163875007796589977 17201750000000000000000 367262705 1048576 865 1048576 (ep1151 rfl) rfl) (Enclosure.sfrac_false_div 367262705 1048576) (BSN.sin_reduce2 qz958 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 231543232618376986624000) qz279) 226375608064910080 72057594037927936 Bool.false 1047796 1048576 55 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q2 367262705 1048576 226375608064910080 72057594037927936 55 231543232618376986624000 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1047796 1048576 231543232618376986624000 151115727451828646838272 3290427239 2147483648 275497 275228 (ep1159 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1161 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz336 (Real.cos qz404)) (@HMul.hMul Real Real Real qz0 qz336 (@Neg.neg Real Real.instNeg (Real.sin qz404))) Bool.true 9039527295 1099511627776 13425728327439 75654096572383232 Bool.false 58560532593 274877906944 6747520907883 37827048286191616 (@Enclosure.Real.IsNear.mulLit_ft qz336 (Real.cos qz404) 223557 1048576 1 1048576 40435 1048576 60042343 72149368832 9039527295 1099511627776 13425728327439 75654096572383232 qz587 (@Enclosure.Real.IsNear.recentre' (Real.cos qz404) Bool.true 40435 1048576 120084686 144298737664 40435 1048576 60042343 72149368832 (ep1156 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz336 (@Neg.neg Real Real.instNeg (Real.sin qz404)) 223557 1048576 1 1048576 261949 262144 60042343 72149368832 58560532593 274877906944 6747520907883 37827048286191616 qz587 (@Enclosure.Real.IsNear.neg (Real.sin qz404) Bool.true 261949 262144 60042343 72149368832 (@Enclosure.Real.IsNear.recentre' (Real.sin qz404) Bool.true 1047796 1048576 120084686 144298737664 261949 262144 60042343 72149368832 (ep1160 rfl rfl) rfl)) rfl)

noncomputable def ep1162 := @ep1085 9039527295 1099511627776 13425728327439 75654096572383232 Bool.false 58560532593 274877906944 6747520907883 37827048286191616 Bool.false ep1086 531185917809 274877906944 221592590753429 37827048286191616 Bool.false 25372012335275008065536 92302843169 1099511627776 442951148877021 75654096572383232 (ep1087 (BSN.head_sum_c_succ qz64 21 22 rfl rfl) (ep1149 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1150 ep1161) rfl rfl

noncomputable abbrev qz405 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 23 1)))

noncomputable def ep1163 := @Enclosure.Complex.IsNear.of_eq qz947 (Complex.mk (@HMul.hMul Real Real Real qz0 qz339 (Real.cos qz405)) (@HMul.hMul Real Real Real qz0 qz339 (@Neg.neg Real Real.instNeg (Real.sin qz405)))) Bool.true 109982020503 549755813888 6591038268539 37827048286191616 Bool.false 64635025017 1099511627776 13133194461717 75654096572383232 (BSN.cpow_neg_s_mk qz61 113311 1000 23 (@Eq.refl Real qz61) rfl)

noncomputable def ep1164 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz341 113311 1000 0 1 3530250507853047 1125899906842624 125000000068807 17201750000000000000 400016215295336608617 1125899906842624000 14163875007796589977 17201750000000000000000 qz384 (BSN.isNear_log_sfrac 23 1 3530250507853047 1125899906842624 125000000068807 17201750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz889) Bool.false 59227775304360265777152 18889465931478580854784 1000000000550456 137614000000000000000 3530250507853047 1125899906842624 125000000068807 17201750000000000000 (BSN.log_rat_reduce_isNear 23 1 4 46 32 190266 524288 24973259072661432 36028797018963968 137614 1000000000000000 rfl rfl rfl rfl (ep414 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1165 := nat_lit 141894633161239966658523182440104976

noncomputable def ep1166 := BSN.cos_dyadic_bound_f 613749982 2147483648 2 1 1048576 275497 ep1165 ep118 ep1165 ep1165 ep119 ep1165 1006042 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 613749982) qz272 0 1 ep1165 ep118 ep1165 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 613749982) qz273 0 1 ep1165 ep119 ep1165 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz959 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 372544131) qz277)

noncomputable def ep1167 := @Enclosure.Real.IsNear.cos_image qz405 qz959 Bool.false 372544131 1048576 27 32768 Bool.true 1006042 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz405 Bool.false 400016215295336608617 1125899906842624000 14163875007796589977 17201750000000000000000 372544131 1048576 27 32768 (ep1164 rfl) rfl) (Enclosure.sfrac_false_div 372544131 1048576) (BSN.cos_reduce2 qz959 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 43188815508007553073152) qz279) 226375608064910080 72057594037927936 Bool.false 1006042 1048576 56 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q2 372544131 1048576 226375608064910080 72057594037927936 56 43188815508007553073152 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1006042 1048576 43188815508007553073152 151115727451828646838272 613749982 2147483648 275497 275228 (ep1166 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1168 := BSN.sin_dyadic_bound_f 613749982 2147483648 2 1 1048576 275497 ep1165 ep178 ep1165 ep1165 ep179 ep1165 295619 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 613749982) qz268 0 1 ep1165 ep178 ep1165 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 613749982) qz269 0 1 ep1165 ep179 ep1165 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1169 := @Enclosure.Real.IsNear.sin_image qz405 qz959 Bool.false 372544131 1048576 27 32768 Bool.true 295619 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz405 Bool.false 400016215295336608617 1125899906842624000 14163875007796589977 17201750000000000000000 372544131 1048576 27 32768 (ep1164 rfl) rfl) (Enclosure.sfrac_false_div 372544131 1048576) (BSN.sin_reduce2 qz959 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 43188815508007553073152) qz279) 226375608064910080 72057594037927936 Bool.false 295619 1048576 56 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q2 372544131 1048576 226375608064910080 72057594037927936 56 43188815508007553073152 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 295619 1048576 43188815508007553073152 151115727451828646838272 613749982 2147483648 275497 275228 (ep1168 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1170 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz339 (Real.cos qz405)) (@HMul.hMul Real Real Real qz0 qz339 (@Neg.neg Real Real.instNeg (Real.sin qz405))) Bool.true 109982020503 549755813888 6591038268539 37827048286191616 Bool.false 64635025017 1099511627776 13133194461717 75654096572383232 (@Enclosure.Real.IsNear.mulLit_ft qz339 (Real.cos qz405) 218643 1048576 1 1048576 503021 524288 1874173 2254667776 109982020503 549755813888 6591038268539 37827048286191616 qz588 (@Enclosure.Real.IsNear.recentre' (Real.cos qz405) Bool.true 1006042 1048576 3748346 4509335552 503021 524288 1874173 2254667776 (ep1167 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz339 (@Neg.neg Real Real.instNeg (Real.sin qz405)) 218643 1048576 1 1048576 295619 1048576 1874173 2254667776 64635025017 1099511627776 13133194461717 75654096572383232 qz588 (@Enclosure.Real.IsNear.neg (Real.sin qz405) Bool.true 295619 1048576 1874173 2254667776 (@Enclosure.Real.IsNear.recentre' (Real.sin qz405) Bool.true 295619 1048576 3748346 4509335552 295619 1048576 1874173 2254667776 (ep1169 rfl rfl) rfl)) rfl)

noncomputable def ep1171 := @ep1083 109982020503 549755813888 6591038268539 37827048286191616 Bool.false 64635025017 1099511627776 13133194461717 75654096572383232 Bool.false 261790918973594334658560 952389815115 549755813888 14261476813873 2364190517886976 Bool.false 172555010908884184334336 78468934093 549755813888 228042171669369 37827048286191616 (ep1084 (BSN.head_sum_c_succ qz64 22 23 rfl rfl) (ep1162 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1163 ep1170) rfl rfl

noncomputable abbrev qz406 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 24 1)))

noncomputable def ep1172 := @Enclosure.Complex.IsNear.of_eq qz946 (Complex.mk (@HMul.hMul Real Real Real qz0 qz342 (Real.cos qz406)) (@HMul.hMul Real Real Real qz0 qz342 (@Neg.neg Real Real.instNeg (Real.sin qz406)))) Bool.true 21642553485 274877906944 3219823193735 18913524143095808 Bool.true 207067963809 1099511627776 12918029120537 75654096572383232 (BSN.cpow_neg_s_mk qz61 113311 1000 24 (@Eq.refl Real qz61) rfl)

noncomputable def ep1173 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz344 113311 1000 0 1 3578169457974519 1125899906842624 125000000068807 17201750000000000000 405445959452550722409 1125899906842624000 14163875007796589977 17201750000000000000000 qz384 (BSN.isNear_log_sfrac 24 1 3578169457974519 1125899906842624 125000000068807 17201750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz892) Bool.false 60031721881041427759104 18889465931478580854784 1000000000550456 137614000000000000000 3578169457974519 1125899906842624 125000000068807 17201750000000000000 (BSN.log_rat_reduce_isNear 24 1 4 48 32 212580 524288 24973259072661432 36028797018963968 137614 1000000000000000 rfl rfl rfl rfl (ep429 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1174 := nat_lit 522955518347834530606879681300402176

noncomputable def ep1175 := BSN.sin_dyadic_bound_f 850386168 2147483648 2 1 1048576 275497 ep1174 ep178 ep1174 ep1174 ep179 ep1174 404460 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 850386168) qz268 0 1 ep1174 ep178 ep1174 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 850386168) qz269 0 1 ep1174 ep179 ep1174 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz960 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 188800487) qz289)

noncomputable def ep1176 := @Enclosure.Real.IsNear.cos_image qz406 qz960 Bool.false 188800487 524288 865 1048576 Bool.true 404460 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz406 Bool.false 405445959452550722409 1125899906842624000 14163875007796589977 17201750000000000000000 188800487 524288 865 1048576 (ep1173 rfl) rfl) (Enclosure.sfrac_false_div 188800487 524288) (BSN.cos_reduce1 qz960 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 29920303358134666133504) qz290) 226375608064910080 72057594037927936 Bool.false 404460 1048576 57 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q1 188800487 524288 226375608064910080 72057594037927936 57 29920303358134666133504 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 404460 1048576 29920303358134666133504 75557863725914323419136 850386168 2147483648 275497 275228 (ep1175 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1177 := BSN.cos_dyadic_bound_f 850386168 2147483648 2 1 1048576 275497 ep1174 ep118 ep1174 ep1174 ep119 ep1174 967431 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 850386168) qz272 0 1 ep1174 ep118 ep1174 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 850386168) qz273 0 1 ep1174 ep119 ep1174 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1178 := @Enclosure.Real.IsNear.sin_image qz406 qz960 Bool.false 188800487 524288 865 1048576 Bool.false 967431 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz406 Bool.false 405445959452550722409 1125899906842624000 14163875007796589977 17201750000000000000000 188800487 524288 865 1048576 (ep1173 rfl) rfl) (Enclosure.sfrac_false_div 188800487 524288) (BSN.sin_reduce1 qz960 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 29920303358134666133504) qz290) 226375608064910080 72057594037927936 Bool.false 967431 1048576 57 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q1 188800487 524288 226375608064910080 72057594037927936 57 29920303358134666133504 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 967431 1048576 29920303358134666133504 75557863725914323419136 850386168 2147483648 275497 275228 (ep1177 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1179 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz342 (Real.cos qz406)) (@HMul.hMul Real Real Real qz0 qz342 (@Neg.neg Real Real.instNeg (Real.sin qz406))) Bool.true 21642553485 274877906944 3219823193735 18913524143095808 Bool.true 207067963809 1099511627776 12918029120537 75654096572383232 (@Enclosure.Real.IsNear.mulLit_ft qz342 (Real.cos qz406) 214039 1048576 1 1048576 101115 262144 60042343 72149368832 21642553485 274877906944 3219823193735 18913524143095808 qz589 (@Enclosure.Real.IsNear.recentre' (Real.cos qz406) Bool.true 404460 1048576 120084686 144298737664 101115 262144 60042343 72149368832 (ep1176 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz342 (@Neg.neg Real Real.instNeg (Real.sin qz406)) 214039 1048576 1 1048576 967431 1048576 60042343 72149368832 207067963809 1099511627776 12918029120537 75654096572383232 qz589 (@Enclosure.Real.IsNear.neg (Real.sin qz406) Bool.false 967431 1048576 60042343 72149368832 (@Enclosure.Real.IsNear.recentre' (Real.sin qz406) Bool.false 967431 1048576 120084686 144298737664 967431 1048576 60042343 72149368832 (ep1178 rfl rfl) rfl)) rfl)

noncomputable def ep1180 := @ep1081 21642553485 274877906944 3219823193735 18913524143095808 Bool.true 207067963809 1099511627776 12918029120537 75654096572383232 Bool.false 249892799367833588858880 909104708145 549755813888 117311637704719 18913524143095808 Bool.true 27559311519505631412224 50130095623 1099511627776 469002372459275 75654096572383232 (ep1082 (BSN.head_sum_c_succ qz64 23 24 rfl rfl) (ep1171 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1172 ep1179) rfl rfl

theorem EMRow35.d19 : Enclosure.Complex.IsNear (BSN.headSumC qz64 25) Bool.false 909104708145 549755813888 117311637704719 18913524143095808 Bool.true 50130095623 1099511627776 469002372459275 75654096572383232 := ep1080 (BSN.head_sum_c_succ qz64 24 25 rfl rfl) (ep1180 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

theorem EMRow35.d20 : @Eq Nat (Nat.pow 29 1) 29 := @Eq.refl Nat 29

noncomputable abbrev qz66 := (@HAdd.hAdd Complex Complex Complex qz262 qz382 qz553)

noncomputable def ep1181 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz3 (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2)) qz66) Bool.true 115550694489 2000000 0 1 Bool.true 1454191757249231 1000000000 0 1

noncomputable def ep1182 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.re qz66)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.im qz66)) 12838632721 400000 0 1 12839382721 500000 0 1

noncomputable def ep1183 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.re qz66) 12838632721 1000000 0 1 5 2 0 1 12838632721 400000

noncomputable abbrev qz67 := (@HAdd.hAdd Complex Complex Complex qz262 qz382 qz590)

noncomputable def ep1184 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz3 (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)) qz67) Bool.true 12838632721 1000000 0 1 Bool.false 113311 500 0 1

noncomputable def ep1185 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.re qz67)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.im qz67)) 3 4 0 1 12839382721 1000000 0 1

noncomputable def ep1186 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.re qz67) 1 2 0 1 3 2 0 1 3 4

noncomputable def ep1187 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)) qz64 Bool.false 1 2 0 1 Bool.false 113311 1000 0 1 (BSN.ascPochhammer_one_eval qz64)

noncomputable def ep1188 := ep1187 (@Enclosure.Complex.IsNear.of_eq qz64 (Complex.mk qz345 qz61) Bool.false 1 2 0 1 Bool.false 113311 1000 0 1 (BSN.s_crit_mk qz61 Bool.false 113311 1000 (@Eq.refl Real qz61)) (@Enclosure.Complex.IsNear.mk qz345 qz61 Bool.false 1 2 0 1 Bool.false 113311 1000 0 1 qz346 qz384))

noncomputable def ep1189 := @ep1186 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 113311 1000 0 1 ep1188)

noncomputable def ep1190 := @Enclosure.Complex.IsNear.of_eq qz67 (Complex.mk (Enclosure.sfrac Bool.false 3 2) qz61) Bool.false 3 2 0 1 Bool.false 113311 1000 0 1 (BSN.s_add_nat_mk qz61 Bool.false 113311 1000 1 (@Eq.refl Real qz61))

noncomputable abbrev qz624 := (ep1190 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz61 Bool.false 3 2 0 1 Bool.false 113311 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz384))

noncomputable def ep1191 := ep1189 (@Enclosure.Complex.IsNear.re_isNear qz67 Bool.false 3 2 0 1 Bool.false 113311 1000 0 1 qz624)

noncomputable def ep1192 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.im qz67) 113311 1000 0 1 113311 1000 0 1 12839382721 1000000

noncomputable def ep1193 := @ep1192 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 113311 1000 0 1 ep1188)

noncomputable def ep1194 := ep1193 (@Enclosure.Complex.IsNear.im_isNear qz67 Bool.false 3 2 0 1 Bool.false 113311 1000 0 1 qz624)

noncomputable def ep1195 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)) qz67 Bool.true 12838632721 1000000 0 1 Bool.false 113311 500 0 1 (@ep1185 51354530884 12838632721 1000000 0 1 (ep1191 rfl) (ep1194 rfl) rfl rfl)

noncomputable def ep1196 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.im qz67)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.re qz67)) 113311 2000 0 1 339933 2000 0 1

noncomputable def ep1197 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.im qz67) 1 2 0 1 113311 1000 0 1 113311 2000

noncomputable def ep1198 := @ep1197 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 113311 1000 0 1 ep1188)

noncomputable def ep1199 := ep1198 (@Enclosure.Complex.IsNear.im_isNear qz67 Bool.false 3 2 0 1 Bool.false 113311 1000 0 1 qz624)

noncomputable def ep1200 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) (Complex.re qz67) 113311 1000 0 1 3 2 0 1 339933 2000

noncomputable def ep1201 := @ep1200 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 113311 1000 0 1 ep1188)

noncomputable def ep1202 := ep1201 (@Enclosure.Complex.IsNear.re_isNear qz67 Bool.false 3 2 0 1 Bool.false 113311 1000 0 1 qz624)

noncomputable abbrev qz625 := (ep1184 (BSN.ascPochhammer_succ_eval_c 1 2 qz64 rfl) (ep1195 (@ep1196 906488000 113311 500 0 1 (ep1199 rfl) (ep1202 rfl) rfl rfl)))

noncomputable def ep1203 := @ep1183 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 12838632721 1000000 0 1 Bool.false 113311 500 0 1 qz625)

noncomputable def ep1204 := @Enclosure.Complex.IsNear.of_eq qz66 (Complex.mk (Enclosure.sfrac Bool.false 5 2) qz61) Bool.false 5 2 0 1 Bool.false 113311 1000 0 1 (BSN.s_add_nat_mk qz61 Bool.false 113311 1000 2 (@Eq.refl Real qz61))

noncomputable abbrev qz626 := (ep1204 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz61 Bool.false 5 2 0 1 Bool.false 113311 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz384))

noncomputable def ep1205 := ep1203 (@Enclosure.Complex.IsNear.re_isNear qz66 Bool.false 5 2 0 1 Bool.false 113311 1000 0 1 qz626)

noncomputable def ep1206 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.im qz66) 113311 500 0 1 113311 1000 0 1 12839382721 500000

noncomputable def ep1207 := @ep1206 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 12838632721 1000000 0 1 Bool.false 113311 500 0 1 qz625)

noncomputable def ep1208 := ep1207 (@Enclosure.Complex.IsNear.im_isNear qz66 Bool.false 5 2 0 1 Bool.false 113311 1000 0 1 qz626)

noncomputable def ep1209 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2)) qz66 Bool.true 115550694489 2000000 0 1 Bool.true 1454191757249231 1000000000 0 1 (@ep1182 11555069448900000 115550694489 2000000 0 1 (ep1205 rfl) (ep1208 rfl) rfl rfl)

noncomputable def ep1210 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.im qz66)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.re qz66)) 1454758312249231 1000000000 0 1 113311 200 0 1

noncomputable def ep1211 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.im qz66) 12838632721 1000000 0 1 113311 1000 0 1 1454758312249231 1000000000

noncomputable def ep1212 := @ep1211 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 12838632721 1000000 0 1 Bool.false 113311 500 0 1 qz625)

noncomputable def ep1213 := ep1212 (@Enclosure.Complex.IsNear.im_isNear qz66 Bool.false 5 2 0 1 Bool.false 113311 1000 0 1 qz626)

noncomputable def ep1214 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2))) (Complex.re qz66) 113311 500 0 1 5 2 0 1 113311 200

noncomputable def ep1215 := @ep1214 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 12838632721 1000000 0 1 Bool.false 113311 500 0 1 qz625)

noncomputable def ep1216 := ep1215 (@Enclosure.Complex.IsNear.re_isNear qz66 Bool.false 5 2 0 1 Bool.false 113311 1000 0 1 qz626)

noncomputable abbrev qz627 := (ep1209 (@ep1210 290838351449846200 1454191757249231 1000000000 0 1 (ep1213 rfl) (ep1216 rfl) rfl rfl))

theorem EMRow35.d21 : Enclosure.Complex.IsNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 115550694489 2000000 0 1 Bool.true 1454191757249231 1000000000 0 1 := ep1181 (BSN.ascPochhammer_succ_eval_c 2 3 qz64 rfl) qz627

theorem EMRow35.d22 : @Eq Nat (Nat.pow 29 3) 24389 := @Eq.refl Nat 24389

noncomputable def ep1217 := nat_lit 646267616972221155830910970424383890762699

noncomputable def ep1218 := nat_lit 361032529701760601166613256863744000000000

noncomputable def ep1219 := nat_lit 12983909103578224090167975415836145864669744091391

noncomputable def ep1220 := nat_lit 1709273581614704391183406993622181143904256000000000

noncomputable abbrev qz68 := (Complex.Stirling.logGammaStirling 2 qz378)

noncomputable abbrev qz628 := (@HAdd.hAdd Complex Complex Complex qz812 qz813 (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I (@HDiv.hDiv Complex Complex Complex qz814 (↑(Enclosure.sfrac Bool.false 113311 1000)) (2 : Complex))))

noncomputable abbrev qz407 := qz628

noncomputable abbrev qz69 := qz407

noncomputable abbrev qz408 := (@HMul.hMul Real Real Real qz0 (@HDiv.hDiv Real Real Real qz1 qz61 (2 : Real)) (Real.log Real.pi))

noncomputable def ep1221 := Complex.re (@HMul.hMul Complex Complex Complex qz3 (Complex.exp (@HMul.hMul Complex Complex Complex qz3 Complex.I ↑(@HSub.hSub Real Real Real qz597 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz408))) (zetaApproximant qz64 2 29))

noncomputable def ep1222 := @Enclosure.Real.IsNear.of_eq ep1221 (@HSub.hSub Real Real Real qz597 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz597 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz408)) (Complex.re (zetaApproximant qz64 2 29))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz597 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz408)) (Complex.im (zetaApproximant qz64 2 29))))

noncomputable def ep1223 := nat_lit 206805620765359323293900818761422372573949

noncomputable def ep1224 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz597 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz408)) (Complex.re (zetaApproximant qz64 2 29))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz597 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz408)) (Complex.im (zetaApproximant qz64 2 29))) ep1223

noncomputable def ep1225 := nat_lit 115530409504563392373316242196398080000000

noncomputable def ep1226 := nat_lit 519062269212232561137396992541867786133921827157527

noncomputable def ep1227 := nat_lit 68370943264588175647336279744887245756170240000000000

noncomputable def ep1228 := nat_lit 416643786164299767294359511811752867

noncomputable def ep1229 := nat_lit 2888260237614084809332906054909952000000000

noncomputable def ep1230 := nat_lit 294094930896402469322024091578048452867936498113

noncomputable def ep1231 := nat_lit 597308499506712263776966029097693852699011776826013864177304686287054553743360000000

noncomputable def ep1232 := @Enclosure.Real.IsNear.mulLit_ff (Real.cos (@HSub.hSub Real Real Real qz597 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz408)) (Complex.re (zetaApproximant qz64 2 29)) 1048575 1048576 25638843

noncomputable def ep1233 := nat_lit 4930634927529249774548811929557312843

noncomputable def ep1234 := nat_lit 2754459607709965524037271552000000000

noncomputable def ep1235 := nat_lit 59302265167091856598563664679929675858331

noncomputable def ep1236 := nat_lit 8528674600246481901559464465530880000000000

noncomputable def ep1237 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz597 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz408)) Bool.false 1048575 1048576 51277686

noncomputable abbrev qz961 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 56001499) qz289)

noncomputable def ep1238 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz597 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz408) qz961 Bool.false 56001499 524288 365

noncomputable def ep1239 := nat_lit 11083373935385599932766230032791

noncomputable def ep1240 := nat_lit 103762935414616227840000000000

noncomputable def ep1241 := nat_lit 968335332170616773218969728023936777

noncomputable def ep1242 := nat_lit 2788912616044335464448000000000000000000

noncomputable def ep1243 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz597 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz408) Bool.false ep1239 ep1240 ep1241 ep1242

noncomputable def ep1244 := nat_lit 17812942838193892562966550032791

noncomputable def ep1245 := nat_lit 365585550682961713762969728023936777

noncomputable def ep1246 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz408 ep1244 ep1240 ep1245 ep1242 8500704531 131072000

noncomputable def ep1247 := nat_lit 1452719988458861354387535302857981952000

noncomputable def ep1248 := nat_lit 18487357794146021615782982731

noncomputable def ep1249 := nat_lit 207525870829232455680000000

noncomputable def ep1250 := nat_lit 155335290489249078583605936494168833

noncomputable def ep1251 := nat_lit 697228154011083866112000000000000000000

noncomputable def ep1252 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz22 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz69 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true ep1248 ep1249 ep1250 ep1251 Bool.false ep1244 ep1240

noncomputable def ep1253 := nat_lit 15135682368056229912742982731

noncomputable def ep1254 := nat_lit 150268740893118251195362091439704833

noncomputable def ep1255 := nat_lit 18452093640684917807126550032791

noncomputable def ep1256 := nat_lit 325053154031049424530881057095040777

noncomputable def ep1257 := @Enclosure.Complex.IsNear.subLitP qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz69 (@Nat.cast Complex Complex.instNatCast j))) Bool.true ep1253 ep1249 ep1254 ep1251 Bool.false ep1255 ep1240 ep1256

noncomputable def ep1258 := nat_lit 41629828836390528922837051382420086653452288

noncomputable def ep1259 := nat_lit 2506948835264436249063553536255101259059560448

noncomputable abbrev qz409 := (@HSub.hSub Complex Complex Complex qz595 qz616 qz550)

noncomputable abbrev qz410 := (Complex.log qz616)

noncomputable abbrev qz70 := (@HSub.hSub Complex Complex Complex qz595 (@HMul.hMul Complex Complex Complex qz255 qz409 qz410) qz378)

noncomputable def ep1260 := @Enclosure.Complex.IsNear.of_eq qz68 (@HAdd.hAdd Complex Complex Complex qz15 (@HAdd.hAdd Complex Complex Complex qz15 qz70 qz895) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz22 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz29 qz55 (@HSub.hSub Int Int Int qz30 qz31 (@HMul.hMul Int Int Int qz32 qz33 (@Nat.cast Int instNatCastInt k)))))) Bool.true ep1253

noncomputable def ep1261 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz15 qz70 qz895) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz22 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz29 qz55 (@HSub.hSub Int Int Int qz30 qz31 (@HMul.hMul Int Int Int qz32 qz33 (@Nat.cast Int instNatCastInt k))))) Bool.true 328465823319234388237 4503599627370496000

noncomputable def ep1262 := nat_lit 151770245249849133929967209

noncomputable def ep1263 := nat_lit 68165053472776223524690900531950665466904576000

noncomputable def ep1264 := nat_lit 332403368177576378984799951909374174599623737344000

noncomputable def ep1265 := @ep1261 29658966818870372801 137614000000000000000000 Bool.false 3203514828286487440323 18014398509481984000 32077750086278542247 275228000000000000000000 Bool.false 22770494090697217977269 ep1249 34226174220268771 ep1249 Bool.true ep1262 ep1240 228126604944256249231 ep1240 Bool.true ep1263 ep1253 ep1249 ep1254 ep1251 Bool.false ep1264

noncomputable def ep1266 := @Enclosure.Complex.IsNear.addLitP qz70 qz895 Bool.true 332604350726444884237 4503599627370496000 58530500013473167477 275228000000000000000000

noncomputable def ep1267 := nat_lit 43052672394098689735000064

noncomputable def ep1268 := @ep1266 Bool.false 3203514828286487440323 18014398509481984000 32077750086278542247 275228000000000000000000 Bool.false 120447 131072 3 1048576 Bool.false 0 1 0 1 Bool.true ep1267 328465823319234388237 4503599627370496000 29658966818870372801 137614000000000000000000 Bool.false 3203514828286487440323 3203514828286487440323 18014398509481984000

noncomputable abbrev qz71 := (@HMul.hMul Complex Complex Complex qz255 qz409 qz410)

noncomputable def ep1269 := @Enclosure.Complex.IsNear.subLitP qz71 qz55 Bool.true 313464052310120276237 4503599627370496000 58530500013473167477 275228000000000000000000 Bool.false 844825916608088796967

noncomputable def ep1270 := nat_lit 1330417402905779536948000

noncomputable def ep1271 := nat_lit 2562811862629189952258400

noncomputable def ep1272 := @ep1269 3602879701896396800 32077750086278542247 275228000000000000000000 Bool.false 17000 4000 0 1 Bool.false 226622 4000 0 1 Bool.true ep1270 332604350726444884237 4503599627370496000 58530500013473167477 275228000000000000000000 Bool.false ep1271 3203514828286487440323 18014398509481984000 32077750086278542247 275228000000000000000000

noncomputable abbrev qz72 := qz409

noncomputable abbrev qz73 := qz410

noncomputable def ep1273 := @Enclosure.Complex.IsNear.mul qz72 qz73 Bool.true 313464052310120276237 4503599627370496000 58530500013473167477 275228000000000000000000 Bool.false 844825916608088796967 3602879701896396800 32077750086278542247

noncomputable def ep1274 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re qz72) (Complex.re qz73)) (@HMul.hMul Real Real Real qz0 (Complex.im qz72) (Complex.im qz73)) 545808533516692275 36028797018963968 750000002270631 110091200000000000000 95422529749926702653 1125899906842624000

noncomputable def ep1275 := nat_lit 2823433178355806683821560970927407104

noncomputable def ep1276 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz72) (Complex.re qz73) 15000 4000 0 1 36387235567779485 9007199254740992 250000000756877 137614000000000000000

noncomputable def ep1277 := @Enclosure.Complex.IsNear.re_isNear qz72 Bool.false 15000 4000 0 1 Bool.false 226622 4000 0 1

noncomputable def ep1278 := @Enclosure.Complex.IsNear.of_eq qz72 (Complex.mk (Enclosure.sfrac Bool.false 15000 4000) qz381) Bool.false 15000 4000 0 1 Bool.false 226622 4000 0

noncomputable abbrev qz629 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 17000 4000) qz381))

noncomputable def ep1279 := @Enclosure.Complex.IsNear.of_eq qz73 qz629 Bool.false 36387235567779485 9007199254740992 250000000756877 137614000000000000000 Bool.false 842129446831523 562949953421312 500000000068807 137614000000000000000

noncomputable def ep1280 := nat_lit 2436517298088107100304735891669488550446840700462902774565040986916290933889173893162270720

noncomputable def ep1281 := nat_lit 41885204862023502065054233583703680737032846932526704918546286761838247869909807332327424

noncomputable def ep1282 := nat_lit 1694083673363505635841625329159522975765567260182747979427810313835770277594458030080

noncomputable def ep1283 := BSN.log_dyadic_bound 18878530884 84414530884 5 4 ep1280 1048576 275228 ep1281 ep1282 477071 103293061768 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 18878530884) (BSN.artanhQ 84414530884) 0 4 ep1281 ep1280 ep1282 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1284 := @Enclosure.Real.IsNear.mulLit_ff qz345 (Real.log (Enclosure.sfrac Bool.false 51646530884 16000000)) 1 2 0 1 36387235567779485 4503599627370496 250000000756877 68807000000000000000 36387235567779485 9007199254740992 250000000756877 137614000000000000000 qz346 (BSN.isNear_log_sfrac 51646530884 16000000 36387235567779485 4503599627370496 250000000756877 68807000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 51646530884) qz603)) Bool.false 305238255381759530106880 37778931862957161709568 1000000003027508 275228000000000000000 36387235567779485 4503599627370496 250000000756877 68807000000000000000 (BSN.log_rat_reduce_isNear 51646530884 16000000 11 103293061768 65536000000 477071 1048576 24973259072661432 36028797018963968 275228 1000000000000000 rfl rfl rfl rfl (ep1283 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1285 := BSN.arctan_dyadic_bound_f 17000 226622 1 0 1048576 275228 0 1 1 0 1 1 78511 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 17000) (BSN.arctanEvenQ 226622) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 17000) (BSN.arctanOddQ 226622) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz630 := (@Nat.cast Real Real.instNatCast 226622)

noncomputable def ep1286 := @Enclosure.Real.IsNear.subLit_ff_p qz354 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz604 qz630)) 884279719003555 562949953421312 1 2000000000000000 78511 1048576 1 275228 883036726840811061248 842129446831523 562949953421312 500000000068807 137614000000000000000 qz355 (ep1285 rfl) rfl rfl

noncomputable abbrev qz631 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 226622) (@Nat.cast Real Real.instNatCast 17000)))

noncomputable def ep1287 := @Enclosure.Complex.IsNear.re_isNear qz73 Bool.false 36387235567779485 9007199254740992 250000000756877 137614000000000000000 Bool.false 842129446831523 562949953421312 500000000068807 137614000000000000000 (ep1279 (@congrArg Complex Complex qz55 qz617 Complex.log (BSN.w_shift_mk qz61 Bool.false 113311 1000 4 (@Eq.refl Real qz61) rfl)) (@Enclosure.Complex.IsNear.of_parts qz629 Bool.false 36387235567779485 9007199254740992 250000000756877 137614000000000000000 Bool.false 842129446831523 562949953421312 500000000068807 137614000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz629) (@HMul.hMul Real Real Real qz0 qz345 (Real.log (Enclosure.sfrac Bool.false 51646530884 16000000))) Bool.false 36387235567779485 9007199254740992 250000000756877 137614000000000000000 (Enclosure.clog_re_eq 17000 226622 4000 51646530884 16000000 rfl rfl rfl) (ep1284 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz629) qz631 Bool.false 842129446831523 562949953421312 500000000068807 137614000000000000000 (Enclosure.clog_im_eq 17000 226622 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz631 (@HSub.hSub Real Real Real qz597 qz354 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz604 qz630))) Bool.false 842129446831523 562949953421312 500000000068807 137614000000000000000 (BSN.arctan_recip 226622 17000 rfl rfl) ep1286))))

noncomputable def ep1288 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz72) (Complex.im qz73) 226622 4000 0 1 842129446831523 562949953421312 500000000068807 137614000000000000000

noncomputable def ep1289 := @Enclosure.Complex.IsNear.im_isNear qz72 Bool.false 15000 4000 0 1 Bool.false 226622 4000 0 1

noncomputable def ep1290 := @Enclosure.Complex.IsNear.im_isNear qz73 Bool.false 36387235567779485 9007199254740992 250000000756877 137614000000000000000 Bool.false 842129446831523 562949953421312 500000000068807 137614000000000000000 (ep1279 (@congrArg Complex Complex qz55 qz617 Complex.log (BSN.w_shift_mk qz61 Bool.false 113311 1000 4 (@Eq.refl Real qz61) rfl)) (@Enclosure.Complex.IsNear.of_parts qz629 Bool.false 36387235567779485 9007199254740992 250000000756877 137614000000000000000 Bool.false 842129446831523 562949953421312 500000000068807 137614000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz629) (@HMul.hMul Real Real Real qz0 qz345 (Real.log (Enclosure.sfrac Bool.false 51646530884 16000000))) Bool.false 36387235567779485 9007199254740992 250000000756877 137614000000000000000 (Enclosure.clog_re_eq 17000 226622 4000 51646530884 16000000 rfl rfl rfl) (ep1284 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz629) qz631 Bool.false 842129446831523 562949953421312 500000000068807 137614000000000000000 (Enclosure.clog_im_eq 17000 226622 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz631 (@HSub.hSub Real Real Real qz597 qz354 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz604 qz630))) Bool.false 842129446831523 562949953421312 500000000068807 137614000000000000000 (BSN.arctan_recip 226622 17000 rfl rfl) ep1286))))

noncomputable abbrev qz411 := (@ep1278 1 (BSN.w_sub_half_mk qz61 Bool.false 113311 1000 4 (@Eq.refl Real qz61) rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 15000 4000) (Enclosure.sfrac Bool.false 226622 4000) Bool.false 15000 4000 0 1 Bool.false 226622 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 15000 4000) (Enclosure.Real.IsNear.const Bool.false 226622 4000)))

noncomputable def ep1291 := @ep1274 56655500007796589977 275228000000000000000000 ep1275 313464052310120276237 4503599627370496000 58530500013473167477 275228000000000000000000 (@ep1276 545808533516692275 36028797018963968 750000002270631 110091200000000000000 (ep1277 qz411) ep1287 rfl) (@ep1288 95422529749926702653 1125899906842624000 56655500007796589977 275228000000000000000000 (ep1289 qz411) ep1290 rfl) rfl

noncomputable def ep1292 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re qz72) (Complex.im qz73)) (@HMul.hMul Real Real Real qz0 (Complex.im qz72) (Complex.re qz73)) 12631941702472845 2251799813685248 1500000000206421 110091200000000000000 824614809884132244967 3602879701896396800

noncomputable def ep1293 := nat_lit 1902378841614563217001545199115042816

noncomputable def ep1294 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz72) (Complex.im qz73) 15000 4000 0 1 842129446831523 562949953421312 500000000068807 137614000000000000000

noncomputable def ep1295 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz72) (Complex.re qz73) 226622 4000 0 1 36387235567779485 9007199254740992 250000000756877 137614000000000000000

noncomputable def ep1296 := @ep1292 28327750085762489747 275228000000000000000000 ep1293 844825916608088796967 3602879701896396800 32077750086278542247 275228000000000000000000 (@ep1294 12631941702472845 2251799813685248 1500000000206421 110091200000000000000 (ep1277 qz411) ep1290 rfl) (@ep1295 824614809884132244967 3602879701896396800 28327750085762489747 275228000000000000000000 (ep1289 qz411) ep1287 rfl) rfl

noncomputable def ep1297 := ep1272 (@ep1273 275228000000000000000000 (ep1291 rfl) (ep1296 rfl)) qz63 rfl rfl rfl rfl rfl rfl

noncomputable def ep1298 := @ep1268 32077750086278542247 275228000000000000000000 (ep1297 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz26 (↑qz253) Bool.false 120447 131072 3 1048576 Bool.false 0 1 0 1 (@ep561 131072 3 1048576 (ep563 rfl) (ep565 rfl) rfl rfl) (@ep566 1 0 1 (ep568 rfl) (ep570 rfl) rfl rfl))

noncomputable abbrev qz74 := (@HPow.hPow Complex Int Complex qz600 qz378 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) qz353 (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) qz601 (@Nat.cast Int instNatCastInt 2))))

noncomputable def ep1299 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz22 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz29 qz55 (@HSub.hSub Int Int Int qz30 qz31 (@HMul.hMul Int Int Int qz32 qz33 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz15 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz22 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz29 qz55 (@HSub.hSub Int Int Int qz30 qz31 (@HMul.hMul Int Int Int qz32 qz33 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz37)) qz38) qz74)) Bool.false 22770494090697217977269 ep1249 34226174220268771 ep1249

noncomputable def ep1300 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz22 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz29 qz55 (@HSub.hSub Int Int Int qz30 qz31 (@HMul.hMul Int Int Int qz32 qz33 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz37)) qz38) qz74) Bool.false 11309879 103079215104 17 103079215104 Bool.true

noncomputable def ep1301 := nat_lit 2347164658399339417213287033470976

noncomputable def ep1302 := nat_lit 7822178878248016549957597404088762368000

noncomputable def ep1303 := @ep1300 75384335257 51539607552000 113311 51539607552000 Bool.false 700140673537977269 ep1249 653580268771 ep1249 Bool.true 1532175076592489967209 ep1240 1430283136249231 ep1240 Bool.false ep1301 22770494090697217977269 ep1249 34226174220268771 ep1249 Bool.true ep1302 ep1262 ep1240 228126604944256249231

noncomputable abbrev qz75 := (@HPow.hPow Complex Int Complex qz600 qz378 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) qz353 (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) qz601 (@Nat.cast Int instNatCastInt 1))))

noncomputable def ep1304 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz22 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz29 qz55 (@HSub.hSub Int Int Int qz30 qz31 (@HMul.hMul Int Int Int qz32 qz33 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz15 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz22 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz29 qz55 (@HSub.hSub Int Int Int qz30 qz31 (@HMul.hMul Int Int Int qz32 qz33 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz40)) qz41) qz75)) Bool.false 11309879 103079215104 17 103079215104

noncomputable def ep1305 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz22 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz29 qz55 (@HSub.hSub Int Int Int qz30 qz31 (@HMul.hMul Int Int Int qz32 qz33 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz40)) qz41) qz75) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1306 := @ep1305 0 1 0 1 Bool.false 11309879 103079215104 17 103079215104 Bool.true 75384335257 51539607552000 113311 51539607552000 Bool.false 11309879 11309879 103079215104 17 103079215104 Bool.true 75384335257 75384335257 51539607552000 113311

noncomputable def ep1307 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz22 (@HMul.hMul Complex Complex Complex qz3 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz29 qz55 (@HSub.hSub Int Int Int qz30 qz31 (@HMul.hMul Int Int Int qz32 qz33 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz264 qz264) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1308 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz40)) qz41) qz75 Bool.false 11309879 103079215104 17 103079215104 Bool.true 75384335257 51539607552000 113311 51539607552000

noncomputable def ep1309 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz40)) qz41)) (Complex.re qz75)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz40)) qz41)) (Complex.im qz75)) 11309879 103079215104 17 103079215104 0 1 0

noncomputable def ep1310 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz40)) qz41)) (Complex.re qz75) 1 12 0 1 11309879 8589934592 17 8589934592 11309879

noncomputable def ep1311 := @Enclosure.Complex.IsNear.re_isNear qz75 Bool.false 11309879 8589934592 17 8589934592 Bool.true 75384335257 4294967296000 113311 4294967296000

noncomputable def ep1312 := @Enclosure.Complex.IsNear.of_eq qz75 (@Inv.inv Complex Complex.instInv qz58) Bool.false 11309879 8589934592 17 8589934592 Bool.true 75384335257 4294967296000 113311

noncomputable def ep1313 := @Enclosure.Complex.IsNear.of_parts (@Inv.inv Complex Complex.instInv qz58) Bool.false 11309879 8589934592 17 8589934592 Bool.true 75384335257 4294967296000 113311

noncomputable def ep1314 := @Enclosure.Real.IsNear.mulLit_ff qz59 (@Inv.inv Real Real.instInv (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz58)) 17000 4000 0 1 665287 2147483648 1 2147483648

noncomputable def ep1315 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz58)) Bool.false 665287 2147483648 1 2147483648 665287 2147483648 1

noncomputable def ep1316 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz58) (@HAdd.hAdd Real Real Real qz608 (@HMul.hMul Real Real Real qz0 qz59 qz59) (@HMul.hMul Real Real Real qz0 qz60 qz60)) Bool.false 12911632721 4000000 0 1

noncomputable def ep1317 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz59 qz59) (@HMul.hMul Real Real Real qz0 qz60 qz60) 289 16 0 1 12839382721 4000000

noncomputable def ep1318 := @Enclosure.Real.IsNear.mulLit_ff qz59 qz59 17000 4000 0 1 17000 4000 0 1

noncomputable def ep1319 := @Enclosure.Real.IsNear.mulLit_ff qz60 qz60 226622 4000 0 1 226622 4000 0 1

noncomputable def ep1320 := @ep1317 0 1 206586123536 12911632721 4000000 0 1 (@ep1318 289 16 0 1 (ep894 qz62) (ep894 qz62) rfl) (@ep1319 12839382721 4000000 0 1 (ep899 qz62) (ep899 qz62) rfl)

noncomputable def ep1321 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz58) 12911632721 4000000 0 1 332643 332644 1073741824 (ep1316 (Enclosure.Complex.normSq_eq_mul_add_mul qz58) (ep1320 rfl rfl)) rfl

noncomputable def ep1322 := @Enclosure.Real.IsNear.of_eq (Complex.re (@Inv.inv Complex Complex.instInv qz58)) (@HMul.hMul Real Real Real qz0 qz59 (@Inv.inv Real Real.instInv (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz58))) Bool.false 11309879 8589934592 17 8589934592 (Enclosure.Complex.inv_re_eq_mul qz58) (@ep1314 11309879 8589934592 17 8589934592 (ep894 qz62) (@ep1315 2147483648 (ep1321 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep1323 := @Enclosure.Real.IsNear.of_eq (Complex.im (@Inv.inv Complex Complex.instInv qz58)) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz60) (@Inv.inv Real Real.instInv (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz58))) Bool.true 75384335257 4294967296000 113311 4294967296000 (Enclosure.Complex.inv_im_eq_mul qz58)

noncomputable def ep1324 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz60) (@Inv.inv Real Real.instInv (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz58)) 226622 4000 0 1 665287 2147483648 1

noncomputable def ep1325 := @ep1324 2147483648 75384335257 4294967296000 113311 4294967296000 (@Enclosure.Real.IsNear.neg qz60 Bool.false 226622 4000 0 1 (ep899 qz62)) (@ep1315 2147483648 (ep1321 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep1326 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz40)) qz41)) (Complex.im qz75) 0 1 0 1 75384335257 4294967296000 113311 4294967296000 0

noncomputable def ep1327 := @Enclosure.Complex.IsNear.im_isNear qz75 Bool.false 11309879 8589934592 17 8589934592 Bool.true 75384335257 4294967296000 113311 4294967296000

noncomputable abbrev qz632 := (@ep1312 4294967296000 (BSN.zpow_one_sub_two_mul qz55 1 1 rfl rfl) (@ep1313 4294967296000 ep1322 (ep1323 ep1325)))

noncomputable def ep1328 := @ep1309 1 11309879 11309879 103079215104 17 103079215104 (@ep1310 103079215104 17 103079215104 ep585 (ep1311 qz632) rfl) (@ep1326 1 0 1 ep602 (ep1327 qz632) rfl) rfl

noncomputable def ep1329 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz40)) qz41)) (Complex.im qz75)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz40)) qz41)) (Complex.re qz75)) 75384335257 51539607552000 113311 51539607552000 0 1 0

noncomputable def ep1330 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz40)) qz41)) (Complex.im qz75) 1 12 0 1 75384335257 4294967296000 113311 4294967296000 75384335257

noncomputable def ep1331 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz40)) qz41)) (Complex.re qz75) 0 1 0 1 11309879 8589934592 17 8589934592 0

noncomputable def ep1332 := @ep1329 1 75384335257 75384335257 51539607552000 113311 51539607552000 (@ep1330 51539607552000 113311 51539607552000 ep585 (ep1327 qz632) rfl) (@ep1331 1 0 1 ep602 (ep1311 qz632) rfl) rfl

noncomputable def ep1333 := @ep1306 51539607552000 (@ep1307 0 1 0 1 (BSN.stirling_sum_base qz55) qz360) (ep1308 (ep1328 rfl) (ep1332 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep1334 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz37)) qz38) qz74 Bool.false 700140673537977269 ep1249 653580268771 ep1249 Bool.true 1532175076592489967209 ep1240 1430283136249231 ep1240

noncomputable def ep1335 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz37)) qz38)) (Complex.re qz74)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz37)) qz38)) (Complex.im qz74)) 700140673537977269 ep1249 653580268771 ep1249 0 1 0

noncomputable def ep1336 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz37)) qz38)) (Complex.re qz74) 1 360 0 1 700140673537977269 576460752303423488000000 653580268771 576460752303423488000000 700140673537977269

noncomputable def ep1337 := nat_lit 288230376151711744000000000

noncomputable def ep1338 := @Enclosure.Complex.IsNear.re_isNear qz74 Bool.true 700140673537977269 576460752303423488000000 653580268771 576460752303423488000000 Bool.false 1532175076592489967209 ep1337 1430283136249231 ep1337

noncomputable def ep1339 := @Enclosure.Complex.IsNear.of_eq qz74 (@Inv.inv Complex Complex.instInv qz53) Bool.true 700140673537977269 576460752303423488000000 653580268771 576460752303423488000000 Bool.false 1532175076592489967209 ep1337 1430283136249231

noncomputable def ep1340 := @Enclosure.Complex.IsNear.of_parts (@Inv.inv Complex Complex.instInv qz53) Bool.true 700140673537977269 576460752303423488000000 653580268771 576460752303423488000000 Bool.false 1532175076592489967209 ep1337 1430283136249231

noncomputable abbrev qz76 := (Complex.re qz377)

noncomputable def ep1341 := @Enclosure.Real.IsNear.mulLit_tf qz76 (@Inv.inv Real Real.instInv (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz53)) 653580268771 16000000 0 1 1071239 36028797018963968 1 36028797018963968

noncomputable def ep1342 := @Enclosure.Complex.IsNear.re_isNear qz53 Bool.true 653580268771 16000000 0 1 Bool.true 1430283136249231 8000000000 0 1

noncomputable def ep1343 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz53)) Bool.false 1071239 36028797018963968 1 36028797018963968 1071239 36028797018963968 1

noncomputable def ep1344 := nat_lit 2152501641770629438061558341361

noncomputable abbrev qz77 := (Complex.im qz377)

noncomputable def ep1345 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz53) (@HAdd.hAdd Real Real Real qz608 (@HMul.hMul Real Real Real qz0 qz76 qz76) (@HMul.hMul Real Real Real qz0 qz77 qz77)) Bool.false ep1344 64000000000000000000 0 1

noncomputable def ep1346 := nat_lit 2045709849838936288598948091361

noncomputable def ep1347 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz76 qz76) (@HMul.hMul Real Real Real qz0 qz77 qz77) 427167167726772597850441 256000000000000 0 1 ep1346 64000000000000000000

noncomputable def ep1348 := nat_lit 551040420293281136143758935388416000000000000

noncomputable def ep1349 := @Enclosure.Real.IsNear.mulLit_tt qz76 qz76 653580268771 16000000 0 1 653580268771 16000000 0 1

noncomputable def ep1350 := @Enclosure.Real.IsNear.mulLit_tt qz77 qz77 1430283136249231 8000000000 0 1 1430283136249231 8000000000 0 1

noncomputable def ep1351 := @Enclosure.Complex.IsNear.im_isNear qz53 Bool.true 653580268771 16000000 0 1 Bool.true 1430283136249231 8000000000 0 1

noncomputable def ep1352 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz53) ep1344 64000000000000000000 0 1 535619 535620 18014398509481984 (ep1345 (Enclosure.Complex.normSq_eq_mul_add_mul qz53) (@ep1347 0 1 ep1348 ep1344 64000000000000000000 0 1 (@ep1349 427167167726772597850441 256000000000000 0 1 (ep1342 EMRow35.d16) (ep1342 EMRow35.d16) rfl) (@ep1350 ep1346 64000000000000000000 0 1 (ep1351 EMRow35.d16) (ep1351 EMRow35.d16) rfl) rfl rfl)) rfl

noncomputable def ep1353 := @Enclosure.Real.IsNear.of_eq (Complex.re (@Inv.inv Complex Complex.instInv qz53)) (@HMul.hMul Real Real Real qz0 qz76 (@Inv.inv Real Real.instInv (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz53))) Bool.true 700140673537977269 576460752303423488000000 653580268771 576460752303423488000000 (Enclosure.Complex.inv_re_eq_mul qz53) (@ep1341 700140673537977269 576460752303423488000000 653580268771 576460752303423488000000 (ep1342 EMRow35.d16) (@ep1343 36028797018963968 (ep1352 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep1354 := @Enclosure.Real.IsNear.of_eq (Complex.im (@Inv.inv Complex Complex.instInv qz53)) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz77) (@Inv.inv Real Real.instInv (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz53))) Bool.false 1532175076592489967209 ep1337 1430283136249231 ep1337 (Enclosure.Complex.inv_im_eq_mul qz53)

noncomputable def ep1355 := @Enclosure.Real.IsNear.mulLit_ff (@Neg.neg Real Real.instNeg qz77) (@Inv.inv Real Real.instInv (@DFunLike.coe qz358 Complex (fun (x : Complex) => Real) qz359 Complex.normSq qz53)) 1430283136249231 8000000000 0 1 1071239 36028797018963968 1

noncomputable def ep1356 := @ep1355 36028797018963968 1532175076592489967209 ep1337 1430283136249231 ep1337 (@Enclosure.Real.IsNear.neg qz77 Bool.true 1430283136249231 8000000000 0 1 (ep1351 EMRow35.d16)) (@ep1343 36028797018963968 (ep1352 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep1357 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz37)) qz38)) (Complex.im qz74) 0 1 0 1 1532175076592489967209 ep1337 1430283136249231 ep1337 0

noncomputable def ep1358 := @Enclosure.Complex.IsNear.im_isNear qz74 Bool.true 700140673537977269 576460752303423488000000 653580268771 576460752303423488000000 Bool.false 1532175076592489967209 ep1337 1430283136249231 ep1337

noncomputable abbrev qz962 := (@ep1339 ep1337 (BSN.zpow_one_sub_two_mul qz55 2 3 rfl rfl) (@ep1340 ep1337 ep1353 (ep1354 ep1356)))

noncomputable def ep1359 := @ep1335 1 700140673537977269 700140673537977269 ep1249 653580268771 ep1249 (@ep1336 ep1249 653580268771 ep1249 ep614 (ep1338 qz962) rfl) (@ep1357 1 0 1 ep637 (ep1358 qz962) rfl) rfl

noncomputable def ep1360 := @Enclosure.Real.IsNear.addLit_tt (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz37)) qz38)) (Complex.im qz74)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz37)) qz38)) (Complex.re qz74)) 1532175076592489967209 ep1240 1430283136249231 ep1240 0 1 0

noncomputable def ep1361 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz37)) qz38)) (Complex.im qz74) 1 360 0 1 1532175076592489967209 ep1337 1430283136249231 ep1337 1532175076592489967209

noncomputable def ep1362 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 (@Rat.cast Complex Complex.instRatCast (bernoulli qz37)) qz38)) (Complex.re qz74) 0 1 0 1 700140673537977269 576460752303423488000000 653580268771 576460752303423488000000 0

noncomputable def ep1363 := @ep1360 1 1532175076592489967209 1532175076592489967209 ep1240 1430283136249231 ep1240 (@ep1361 ep1240 1430283136249231 ep1240 ep614 (ep1358 qz962) rfl) (@ep1362 1 0 1 ep637 (ep1338 qz962) rfl) rfl

noncomputable def ep1364 := @ep1303 ep1240 (@ep1304 Bool.true 75384335257 51539607552000 113311 51539607552000 (BSN.stirling_sum_succ qz55 0 1 rfl) (ep1333 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1334 (ep1359 rfl) (ep1363 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep1365 := @ep1265 ep1255 ep1240 ep1256 ep1242 (ep1298 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep1299 Bool.true ep1262 ep1240 228126604944256249231 ep1240 (BSN.stirling_sum_succ qz55 1 2 rfl) (ep1364 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep1366 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz69 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz61 4) Bool.false 36368005925453469 2251799813685248 250000000756877 34403500000000000000 Bool.false 866903757718947 140737488355328

noncomputable def ep1367 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz61 4) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.logSumC qz61 3) (Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz69 qz552))) Bool.false 36368005925453469 2251799813685248 250000000756877 34403500000000000000 Bool.false 866903757718947 140737488355328 500000000068807 34403500000000000000

noncomputable def ep1368 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz61 3) (Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz69 qz552)) Bool.false 109095263559269335 9007199254740992 750000002270631 137614000000000000000 Bool.false 2615592663748841 562949953421312 1500000000206421 137614000000000000000 Bool.false

noncomputable def ep1369 := nat_lit 1310295503472641868140902971604992

noncomputable def ep1370 := nat_lit 1952093720114566227326303993856

noncomputable def ep1371 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz61 3) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.logSumC qz61 2) (Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz69 qz553))) Bool.false 109095263559269335 9007199254740992 750000002270631 137614000000000000000 Bool.false 2615592663748841 562949953421312 1500000000206421 137614000000000000000

noncomputable def ep1372 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz61 2) (Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz69 qz553)) Bool.false 36363102146543261 4503599627370496 250000000756877 68807000000000000000 Bool.false 876828756051363 281474976710656 500000000068807 68807000000000000000 Bool.false

noncomputable def ep1373 := nat_lit 491321388313411428266193096540160

noncomputable def ep1374 := nat_lit 736223884113267710551912349696

noncomputable def ep1375 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz61 2) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.logSumC qz61 1) (Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz69 qz590))) Bool.false 36363102146543261 4503599627370496 250000000756877 68807000000000000000 Bool.false 876828756051363 281474976710656 500000000068807 68807000000000000000

noncomputable def ep1376 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz61 1) (Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz69 qz590)) Bool.false 36362049879555741 9007199254740992 250000000756877 137614000000000000000 Bool.false 881796154164643 562949953421312 500000000068807 137614000000000000000 Bool.false

noncomputable def ep1377 := nat_lit 655059413108830053887397356109824

noncomputable def ep1378 := nat_lit 987221414755163486610901696512

noncomputable abbrev qz963 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz69 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep1379 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz61 1) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.logSumC qz61 0) qz963) Bool.false 36362049879555741 9007199254740992 250000000756877 137614000000000000000 Bool.false 881796154164643 562949953421312 500000000068807 137614000000000000000

noncomputable def ep1380 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz61 0) qz963 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz964 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz381))

noncomputable def ep1381 := @Enclosure.Complex.IsNear.of_eq qz963 qz964 Bool.false 36362049879555741 9007199254740992 250000000756877 137614000000000000000 Bool.false 881796154164643 562949953421312 500000000068807 137614000000000000000

noncomputable def ep1382 := nat_lit 2370803999306957184653908016586404734842273181885222713430116299596414679321864908842270720

noncomputable def ep1383 := nat_lit 39763206447346511209547633043230937096204592661216799646415684318039993195144130788327424

noncomputable def ep1384 := nat_lit 1498040775771882084201313570636934226498417994186343980031304740582671794373978030080

noncomputable def ep1385 := BSN.log_dyadic_bound 18590530884 84126530884 5 4 ep1382 1048576 275228 ep1383 ep1384 471207 102717061768 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 18590530884) (BSN.artanhQ 84126530884) 0 4 ep1383 ep1382 ep1384 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1386 := @Enclosure.Real.IsNear.mulLit_ff qz345 (Real.log (Enclosure.sfrac Bool.false 51358530884 16000000)) 1 2 0 1 36362049879555741 4503599627370496 250000000756877 68807000000000000000 36362049879555741 9007199254740992 250000000756877 137614000000000000000 qz346 (BSN.isNear_log_sfrac 51358530884 16000000 36362049879555741 4503599627370496 250000000756877 68807000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 51358530884) qz603)) Bool.false 305026982516040325398528 37778931862957161709568 1000000003027508 275228000000000000000 36362049879555741 4503599627370496 250000000756877 68807000000000000000 (BSN.log_rat_reduce_isNear 51358530884 16000000 11 102717061768 65536000000 471207 1048576 24973259072661432 36028797018963968 275228 1000000000000000 rfl rfl rfl rfl (ep1385 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1387 := BSN.arctan_dyadic_bound_f 1000 226622 1 0 1048576 275228 0 1 1 0 1 1 4626 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 226622) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 226622) 0 0 rfl) rfl rfl rfl

noncomputable def ep1388 := @Enclosure.Real.IsNear.subLit_ff_p qz354 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz899 qz630)) 884279719003555 562949953421312 1 2000000000000000 4626 1048576 1 275228 924630284149344698368 881796154164643 562949953421312 500000000068807 137614000000000000000 qz355 (ep1387 rfl) rfl rfl

noncomputable abbrev qz965 := (@HAdd.hAdd Complex Complex Complex qz15 qz69 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz966 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz381)

noncomputable def ep1389 := @ep1380 36362049879555741 9007199254740992 250000000756877 137614000000000000000 Bool.false 881796154164643 562949953421312 500000000068807 137614000000000000000 Bool.false 36362049879555741 36362049879555741 9007199254740992 250000000756877 137614000000000000000 Bool.false 881796154164643 881796154164643 562949953421312 500000000068807 137614000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz61 0) (Complex.mk qz264 qz264) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz61) qz360) (ep1381 (@congrArg Complex Complex qz965 qz966 Complex.log (BSN.w_shift_mk qz61 Bool.false 113311 1000 0 (@Eq.refl Real qz61) rfl)) (@Enclosure.Complex.IsNear.of_parts qz964 Bool.false 36362049879555741 9007199254740992 250000000756877 137614000000000000000 Bool.false 881796154164643 562949953421312 500000000068807 137614000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz964) (@HMul.hMul Real Real Real qz0 qz345 (Real.log (Enclosure.sfrac Bool.false 51358530884 16000000))) Bool.false 36362049879555741 9007199254740992 250000000756877 137614000000000000000 (Enclosure.clog_re_eq 1000 226622 4000 51358530884 16000000 rfl rfl rfl) (ep1386 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz964) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz630 qz899)) Bool.false 881796154164643 562949953421312 500000000068807 137614000000000000000 (Enclosure.clog_im_eq 1000 226622 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz630 qz899)) (@HSub.hSub Real Real Real qz597 qz354 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz899 qz630))) Bool.false 881796154164643 562949953421312 500000000068807 137614000000000000000 (BSN.arctan_recip 226622 1000 rfl rfl) ep1388)))) rfl rfl

noncomputable abbrev qz967 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz381))

noncomputable def ep1390 := @Enclosure.Complex.IsNear.of_eq (Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz69 qz590)) qz967 Bool.false 36364154413530781 9007199254740992 250000000756877 137614000000000000000 Bool.false 871861357938083 562949953421312 500000000068807 137614000000000000000

noncomputable def ep1391 := nat_lit 2376220235210559100069272835587321415933313852170218554277554889158510693518847324202270720

noncomputable def ep1392 := nat_lit 39936680487522185523698780300989234302368075603787649464641086303580364639609270500327424

noncomputable def ep1393 := nat_lit 1513582386694743338916589702925952182315160087471860778788173322801872561309018030080

noncomputable def ep1394 := BSN.log_dyadic_bound 18614530884 84150530884 5 4 ep1391 1048576 275228 ep1392 ep1393 471697 102765061768 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 18614530884) (BSN.artanhQ 84150530884) 0 4 ep1392 ep1391 ep1393 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1395 := @Enclosure.Real.IsNear.mulLit_ff qz345 (Real.log (Enclosure.sfrac Bool.false 51382530884 16000000)) 1 2 0 1 36364154413530781 4503599627370496 250000000756877 68807000000000000000 36364154413530781 9007199254740992 250000000756877 137614000000000000000 qz346 (BSN.isNear_log_sfrac 51382530884 16000000 36364154413530781 4503599627370496 250000000756877 68807000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 51382530884) qz603)) Bool.false 305044636626579617742848 37778931862957161709568 1000000003027508 275228000000000000000 36364154413530781 4503599627370496 250000000756877 68807000000000000000 (BSN.log_rat_reduce_isNear 51382530884 16000000 11 102765061768 65536000000 471697 1048576 24973259072661432 36028797018963968 275228 1000000000000000 rfl rfl rfl rfl (ep1394 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1396 := BSN.arctan_dyadic_bound_f 5000 226622 1 0 1048576 275228 0 1 1 0 1 1 23131 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 226622) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 226622) 0 0 rfl) rfl rfl rfl

noncomputable def ep1397 := @Enclosure.Real.IsNear.subLit_ff_p qz354 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz903 qz630)) 884279719003555 562949953421312 1 2000000000000000 23131 1048576 1 275228 914212895261283319808 871861357938083 562949953421312 500000000068807 137614000000000000000 qz355 (ep1396 rfl) rfl rfl

noncomputable abbrev qz968 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz381)

noncomputable def ep1398 := @ep1376 36364154413530781 9007199254740992 250000000756877 137614000000000000000 Bool.false 871861357938083 562949953421312 500000000068807 137614000000000000000 Bool.false ep1377 36363102146543261 4503599627370496 250000000756877 68807000000000000000 Bool.false ep1378 876828756051363 281474976710656 500000000068807 68807000000000000000 (ep1379 (BSN.log_sum_c_succ qz61 0 1 rfl) (ep1389 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1390 (@congrArg Complex Complex (@HAdd.hAdd Complex Complex Complex qz15 qz69 qz590) qz968 Complex.log (BSN.w_shift_mk qz61 Bool.false 113311 1000 1 (@Eq.refl Real qz61) rfl)) (@Enclosure.Complex.IsNear.of_parts qz967 Bool.false 36364154413530781 9007199254740992 250000000756877 137614000000000000000 Bool.false 871861357938083 562949953421312 500000000068807 137614000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz967) (@HMul.hMul Real Real Real qz0 qz345 (Real.log (Enclosure.sfrac Bool.false 51382530884 16000000))) Bool.false 36364154413530781 9007199254740992 250000000756877 137614000000000000000 (Enclosure.clog_re_eq 5000 226622 4000 51382530884 16000000 rfl rfl rfl) (ep1395 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz967) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz630 qz903)) Bool.false 871861357938083 562949953421312 500000000068807 137614000000000000000 (Enclosure.clog_im_eq 5000 226622 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz630 qz903)) (@HSub.hSub Real Real Real qz597 qz354 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz903 qz630))) Bool.false 871861357938083 562949953421312 500000000068807 137614000000000000000 (BSN.arctan_recip 226622 5000 rfl rfl) ep1397)))) rfl rfl

noncomputable abbrev qz969 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 9000 4000) qz381))

noncomputable def ep1399 := @Enclosure.Complex.IsNear.of_eq (Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz69 qz553)) qz969 Bool.false 36369059266182813 9007199254740992 250000000756877 137614000000000000000 Bool.false 861935151646115 562949953421312 500000000068807 137614000000000000000

noncomputable def ep1400 := nat_lit 2388900243950474885487826020045826548681521953640320117902531792141442178071272960042270720

noncomputable def ep1401 := nat_lit 40343809524351947419802109124066307069858243604453246159285556068423582095787929828327424

noncomputable def ep1402 := nat_lit 1550395985030684953182922549459226084764233460672117803968728764304240217490778030080

noncomputable def ep1403 := BSN.log_dyadic_bound 18670530884 84206530884 5 4 ep1400 1048576 275228 ep1401 ep1402 472839 102877061768 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 18670530884) (BSN.artanhQ 84206530884) 0 4 ep1401 ep1400 ep1402 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1404 := @Enclosure.Real.IsNear.mulLit_ff qz345 (Real.log (Enclosure.sfrac Bool.false 51438530884 16000000)) 1 2 0 1 36369059266182813 4503599627370496 250000000756877 68807000000000000000 36369059266182813 9007199254740992 250000000756877 137614000000000000000 qz346 (BSN.isNear_log_sfrac 51438530884 16000000 36369059266182813 4503599627370496 250000000756877 68807000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 51438530884) qz603)) Bool.false 305085781512775274594304 37778931862957161709568 1000000003027508 275228000000000000000 36369059266182813 4503599627370496 250000000756877 68807000000000000000 (BSN.log_rat_reduce_isNear 51438530884 16000000 11 102877061768 65536000000 472839 1048576 24973259072661432 36028797018963968 275228 1000000000000000 rfl rfl rfl rfl (ep1403 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1405 := BSN.arctan_dyadic_bound_f 9000 226622 1 0 1048576 275228 0 1 1 0 1 1 41620 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 226622) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 226622) 0 0 rfl) rfl rfl rfl

noncomputable def ep1406 := @Enclosure.Real.IsNear.subLit_ff_p qz354 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz906 qz630)) 884279719003555 562949953421312 1 2000000000000000 41620 1048576 1 275228 903804513572476682240 861935151646115 562949953421312 500000000068807 137614000000000000000 qz355 (ep1405 rfl) rfl rfl

noncomputable abbrev qz970 := (Complex.mk (Enclosure.sfrac Bool.false 9000 4000) qz381)

noncomputable def ep1407 := @ep1372 36369059266182813 9007199254740992 250000000756877 137614000000000000000 Bool.false 861935151646115 562949953421312 500000000068807 137614000000000000000 Bool.false ep1373 109095263559269335 9007199254740992 750000002270631 137614000000000000000 Bool.false ep1374 2615592663748841 562949953421312 1500000000206421 137614000000000000000 (ep1375 (BSN.log_sum_c_succ qz61 1 2 rfl) (ep1398 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1399 (@congrArg Complex Complex (@HAdd.hAdd Complex Complex Complex qz15 qz69 qz553) qz970 Complex.log (BSN.w_shift_mk qz61 Bool.false 113311 1000 2 (@Eq.refl Real qz61) rfl)) (@Enclosure.Complex.IsNear.of_parts qz969 Bool.false 36369059266182813 9007199254740992 250000000756877 137614000000000000000 Bool.false 861935151646115 562949953421312 500000000068807 137614000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz969) (@HMul.hMul Real Real Real qz0 qz345 (Real.log (Enclosure.sfrac Bool.false 51438530884 16000000))) Bool.false 36369059266182813 9007199254740992 250000000756877 137614000000000000000 (Enclosure.clog_re_eq 9000 226622 4000 51438530884 16000000 rfl rfl rfl) (ep1404 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz969) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz630 qz906)) Bool.false 861935151646115 562949953421312 500000000068807 137614000000000000000 (Enclosure.clog_im_eq 9000 226622 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz630 qz906)) (@HSub.hSub Real Real Real qz597 qz354 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz906 qz630))) Bool.false 861935151646115 562949953421312 500000000068807 137614000000000000000 (BSN.arctan_recip 226622 9000 rfl rfl) ep1406)))) rfl rfl

noncomputable abbrev qz971 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 13000 4000) qz381))

noncomputable def ep1408 := @Enclosure.Complex.IsNear.of_eq (Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz69 qz552)) qz971 Bool.false 36376760142544541 9007199254740992 250000000756877 137614000000000000000 Bool.false 852022367126947 562949953421312 500000000068807 137614000000000000000

noncomputable def ep1409 := nat_lit 2408945602086408676812824578474692752954803576962888207114362612315426696401861816362270720

noncomputable def ep1410 := nat_lit 40990291655043635176378461087292149252764743397534878438257426033967543369504108772327424

noncomputable def ep1411 := nat_lit 1609829494937199607679472732858167967152953141022734392917235499787932842919258030080

noncomputable def ep1412 := BSN.log_dyadic_bound 18758530884 84294530884 5 4 ep1409 1048576 275228 ep1410 ep1411 474632 103053061768 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 18758530884) (BSN.artanhQ 84294530884) 0 4 ep1410 ep1409 ep1411 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1413 := @Enclosure.Real.IsNear.mulLit_ff qz345 (Real.log (Enclosure.sfrac Bool.false 51526530884 16000000)) 1 2 0 1 36376760142544541 4503599627370496 250000000756877 68807000000000000000 36376760142544541 9007199254740992 250000000756877 137614000000000000000 qz346 (BSN.isNear_log_sfrac 51526530884 16000000 36376760142544541 4503599627370496 250000000756877 68807000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 51526530884) qz603)) Bool.false 305150381145830276988928 37778931862957161709568 1000000003027508 275228000000000000000 36376760142544541 4503599627370496 250000000756877 68807000000000000000 (BSN.log_rat_reduce_isNear 51526530884 16000000 11 103053061768 65536000000 474632 1048576 24973259072661432 36028797018963968 275228 1000000000000000 rfl rfl rfl rfl (ep1412 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1414 := BSN.arctan_dyadic_bound_f 13000 226622 1 0 1048576 275228 0 1 1 0 1 1 60084 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 13000) (BSN.arctanEvenQ 226622) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 13000) (BSN.arctanOddQ 226622) 0 0 rfl) rfl rfl rfl

noncomputable def ep1415 := @Enclosure.Real.IsNear.subLit_ff_p qz354 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz909 qz630)) 884279719003555 562949953421312 1 2000000000000000 60084 1048576 1 275228 893410205632505577472 852022367126947 562949953421312 500000000068807 137614000000000000000 qz355 (ep1414 rfl) rfl rfl

noncomputable abbrev qz972 := (Complex.mk (Enclosure.sfrac Bool.false 13000 4000) qz381)

noncomputable def ep1416 := @ep1368 36376760142544541 9007199254740992 250000000756877 137614000000000000000 Bool.false 852022367126947 562949953421312 500000000068807 137614000000000000000 Bool.false ep1369 36368005925453469 2251799813685248 250000000756877 34403500000000000000 Bool.false ep1370 866903757718947 140737488355328 500000000068807 34403500000000000000 (ep1371 (BSN.log_sum_c_succ qz61 2 3 rfl) (ep1407 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1408 (@congrArg Complex Complex (@HAdd.hAdd Complex Complex Complex qz15 qz69 qz552) qz972 Complex.log (BSN.w_shift_mk qz61 Bool.false 113311 1000 3 (@Eq.refl Real qz61) rfl)) (@Enclosure.Complex.IsNear.of_parts qz971 Bool.false 36376760142544541 9007199254740992 250000000756877 137614000000000000000 Bool.false 852022367126947 562949953421312 500000000068807 137614000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz971) (@HMul.hMul Real Real Real qz0 qz345 (Real.log (Enclosure.sfrac Bool.false 51526530884 16000000))) Bool.false 36376760142544541 9007199254740992 250000000756877 137614000000000000000 (Enclosure.clog_re_eq 13000 226622 4000 51526530884 16000000 rfl rfl rfl) (ep1413 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz971) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz630 qz909)) Bool.false 852022367126947 562949953421312 500000000068807 137614000000000000000 (Enclosure.clog_im_eq 13000 226622 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz630 qz909)) (@HSub.hSub Real Real Real qz597 qz354 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz909 qz630))) Bool.false 852022367126947 562949953421312 500000000068807 137614000000000000000 (BSN.arctan_recip 226622 13000 rfl rfl) ep1415)))) rfl rfl

noncomputable def ep1417 := @ep1257 ep1242 Bool.false 36368005925453469 2251799813685248 250000000756877 34403500000000000000 Bool.false 866903757718947 140737488355328 500000000068807 34403500000000000000 Bool.true ep1258 ep1248 ep1249 ep1250 ep1251 Bool.false ep1259 ep1244 ep1240 ep1245 ep1242 (@ep1260 ep1249 ep1254 ep1251 Bool.false ep1255 ep1240 ep1256 ep1242 (BSN.logGammaStirling_unfold 2 qz55) (ep1365 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep1366 500000000068807 34403500000000000000 (BSN.log_sum_c_eq qz61 4) (ep1367 (BSN.log_sum_c_succ qz61 3 4 rfl) (ep1416 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable def ep1418 := @Enclosure.Real.IsNear.mulLit_ff (@HDiv.hDiv Real Real Real qz1 qz61 (2 : Real)) (Real.log Real.pi) 113311 2000 0 1 75021 65536 1 262144 8500704531 131072000 113311 524288000 (@Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real qz1 qz61 (2 : Real)) (Enclosure.sfrac Bool.false 113311 2000) Bool.false 113311 2000 0 1 (BSN.t_half_eq qz61 Bool.false 113311 1000 (@Eq.refl Real qz61)) (Enclosure.Real.IsNear.const Bool.false 113311 2000)) EMRow35.d6 rfl

noncomputable def ep1419 := @ep1246 113311 524288000 ep1247 ep1239 ep1240 ep1241 ep1242 (@ep1252 ep1245 ep1242 (ep1417 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep1418 rfl rfl

noncomputable def ep1420 := BSN.cos_dyadic_bound_f 498927 2147483648 1 0 1048576 275497 0 1 1 0 1 1 1048575 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 498927) qz272 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 498927) qz273 0 0 rfl) rfl rfl

noncomputable def ep1421 := @ep1238 1048576 Bool.false 1048575 1048576 1 137614 (@ep1243 56001499 524288 365 1048576 ep1419 rfl) (Enclosure.sfrac_false_div 56001499 524288) (BSN.cos_reduce0 qz961 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 17554437635370385408) qz290) 226375608064910080 72057594037927936 Bool.false 1048575 1048576 17 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q0 56001499 524288 226375608064910080 72057594037927936 17 17554437635370385408 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1048575 1048576 17554437635370385408 75557863725914323419136 498927 2147483648 275497 275228 (ep1420 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1422 := nat_lit 1714583482157612211087899225562769

noncomputable def ep1423 := nat_lit 6585885948209023361346548989147207426647

noncomputable def ep1424 := nat_lit 947630511138497989062162718392320000000000

noncomputable abbrev qz78 := (@HPow.hPow Complex Complex Complex (@instHPow Complex Complex Complex.instPow) (@Nat.cast Complex Complex.instNatCast 29) (@Neg.neg Complex Complex.instNeg qz382))

noncomputable abbrev qz79 := (@HAdd.hAdd Complex Complex Complex qz262 (@HDiv.hDiv Complex Complex Complex qz352 (@Nat.cast Complex Complex.instNatCast 29) (@HSub.hSub Complex Complex Complex qz595 qz382 (1 : Complex))) qz351)

noncomputable abbrev qz80 := (@Nat.cast Complex Complex.instNatCast 29)

noncomputable def ep1425 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz64 2 29) (@HAdd.hAdd Complex Complex Complex qz15 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 29, @HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast n) qz65) (@HMul.hMul Complex Complex Complex qz3 qz78 (@HAdd.hAdd Complex Complex Complex qz15 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz80 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1))))))) Bool.false ep1233 ep1234 ep1235

noncomputable def ep1426 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 29, @HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast n) qz65) (@HMul.hMul Complex Complex Complex qz3 qz78 (@HAdd.hAdd Complex Complex Complex qz15 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz80 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))))) Bool.false 2014533099221 1099511627776 518357297369173 75654096572383232

noncomputable def ep1427 := nat_lit 116105743529380106483241262442687157

noncomputable def ep1428 := nat_lit 10440444672161799607150705429032239257

noncomputable def ep1429 := nat_lit 102755115665620263874210415247360000000000

noncomputable def ep1430 := nat_lit 242801755335841036243615916774437231

noncomputable def ep1431 := nat_lit 1163249337719512372411995382014547309

noncomputable def ep1432 := nat_lit 11417235073957807097134490583040000000000

noncomputable def ep1433 := nat_lit 5421290435136885213466245220634448491091400327168

noncomputable def ep1434 := nat_lit 1885204475424958454802630593314769932851871744

noncomputable def ep1435 := @ep1426 Bool.true 97604828533 1099511627776 518076260544619 75654096572383232 Bool.true ep1427 ep1234 ep1428 ep1429 Bool.false ep1430 ep1234 ep1431 ep1432 Bool.false ep1433 ep1233 ep1234 ep1235 ep1236 Bool.true ep1434 ep1422 ep1234

noncomputable def ep1436 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 29, @HPow.hPow Complex Complex Complex qz16 (@Nat.cast Complex Complex.instNatCast n) qz65) (BSN.headSumC qz64 29) Bool.false 2014533099221 1099511627776 518357297369173 75654096572383232 Bool.true 97604828533 1099511627776 518076260544619

noncomputable def ep1437 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 29) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 28) (@HPow.hPow Complex Complex Complex qz16 qz49 qz65)) Bool.false 2014533099221 1099511627776 518357297369173 75654096572383232 Bool.true 97604828533 1099511627776 518076260544619 75654096572383232

noncomputable def ep1438 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 28) (@HPow.hPow Complex Complex Complex qz16 qz49 qz65) Bool.false 1841196752513 1099511627776 6101355602379 911495139426304 Bool.false 8492156679 549755813888 1524553845263 227873784856576 Bool.false

noncomputable abbrev qz973 := (@Nat.cast Complex Complex.instNatCast 27)

noncomputable def ep1439 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 28) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 27) (@HPow.hPow Complex Complex Complex qz16 qz973 qz65)) Bool.false 1841196752513 1099511627776 6101355602379 911495139426304 Bool.false 8492156679 549755813888 1524553845263 227873784856576

noncomputable def ep1440 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 27) (@HPow.hPow Complex Complex Complex qz16 qz973 qz65) Bool.false 1018247600663 549755813888 123560816228137 18913524143095808 Bool.false 49216002075 549755813888 123505361501715 18913524143095808 Bool.true

noncomputable abbrev qz974 := (@Nat.cast Complex Complex.instNatCast 26)

noncomputable def ep1441 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 27) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 26) (@HPow.hPow Complex Complex Complex qz16 qz974 qz65)) Bool.false 1018247600663 549755813888 123560816228137 18913524143095808 Bool.false 49216002075 549755813888 123505361501715 18913524143095808

noncomputable def ep1442 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 26) (@HPow.hPow Complex Complex Complex qz16 qz974 qz65) Bool.false 1013845606605 549755813888 3764899385235 591047629471744 Bool.true 117020372593 1099511627776 481616159006969 75654096572383232 Bool.false

noncomputable abbrev qz975 := (@Nat.cast Complex Complex.instNatCast 25)

noncomputable def ep1443 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz64 26) (@HAdd.hAdd Complex Complex Complex qz15 (BSN.headSumC qz64 25) (@HPow.hPow Complex Complex Complex qz16 qz975 qz65)) Bool.false 1013845606605 549755813888 3764899385235 591047629471744 Bool.true 117020372593 1099511627776 481616159006969 75654096572383232

noncomputable def ep1444 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz64 25) (@HPow.hPow Complex Complex Complex qz16 qz975 qz65) Bool.false 909104708145 549755813888 117311637704719 18913524143095808 Bool.true 50130095623 1099511627776 469002372459275 75654096572383232 Bool.false

noncomputable abbrev qz412 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 25 1)))

noncomputable def ep1445 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz975 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz361 (Real.cos qz412)) (@HMul.hMul Real Real Real qz0 qz361 (@Neg.neg Real Real.instNeg (Real.sin qz412)))) Bool.false 26185224615 137438953472 3165142622801 18913524143095808 Bool.true 33445138485 549755813888 6306893273847 37827048286191616 (BSN.cpow_neg_s_mk qz61 113311 1000 25 (@Eq.refl Real qz61) rfl)

noncomputable def ep1446 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz363 113311 1000 0 1 3624129903009015 1125899906842624 125000000068807 17201750000000000000 82130756687970899733 225179981368524800 14163875007796589977 17201750000000000000000 qz384 (BSN.isNear_log_sfrac 25 1 3624129903009015 1125899906842624 125000000068807 17201750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz915) Bool.false 60802810194841294602240 18889465931478580854784 1000000000550456 137614000000000000000 3624129903009015 1125899906842624 125000000068807 17201750000000000000 (BSN.log_rat_reduce_isNear 25 1 4 50 32 233982 524288 24973259072661432 36028797018963968 137614 1000000000000000 rfl rfl rfl rfl (ep727 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1447 := nat_lit 194089395526158654058481105099864641

noncomputable def ep1448 := BSN.cos_dyadic_bound_f 663743761 2147483648 2 1 1048576 275497 ep1447 ep118 ep1447 ep1447 ep119 ep1447 998888 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 663743761) qz272 0 1 ep1447 ep118 ep1447 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 663743761) qz273 0 1 ep1447 ep119 ep1447 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz976 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 191225569) qz289)

noncomputable def ep1449 := @Enclosure.Real.IsNear.cos_image qz412 qz976 Bool.false 191225569 524288 865 1048576 Bool.false 998888 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz412 Bool.false 82130756687970899733 225179981368524800 14163875007796589977 17201750000000000000000 191225569 524288 865 1048576 (ep1446 rfl) rfl) (Enclosure.sfrac_false_div 191225569 524288) (BSN.cos_reduce0 qz976 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 23353407484100647845888) qz290) 226375608064910080 72057594037927936 Bool.false 998888 1048576 58 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q0 191225569 524288 226375608064910080 72057594037927936 58 23353407484100647845888 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 998888 1048576 23353407484100647845888 75557863725914323419136 663743761 2147483648 275497 275228 (ep1448 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1450 := BSN.sin_dyadic_bound_f 663743761 2147483648 2 1 1048576 275497 ep1447 ep178 ep1447 ep1447 ep179 ep1447 318958 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 663743761) qz268 0 1 ep1447 ep178 ep1447 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 663743761) qz269 0 1 ep1447 ep179 ep1447 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1451 := @Enclosure.Real.IsNear.sin_image qz412 qz976 Bool.false 191225569 524288 865 1048576 Bool.false 318958 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz412 Bool.false 82130756687970899733 225179981368524800 14163875007796589977 17201750000000000000000 191225569 524288 865 1048576 (ep1446 rfl) rfl) (Enclosure.sfrac_false_div 191225569 524288) (BSN.sin_reduce0 qz976 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 23353407484100647845888) qz290) 226375608064910080 72057594037927936 Bool.false 318958 1048576 58 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q0 191225569 524288 226375608064910080 72057594037927936 58 23353407484100647845888 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 318958 1048576 23353407484100647845888 75557863725914323419136 663743761 2147483648 275497 275228 (ep1450 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1452 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz361 (Real.cos qz412)) (@HMul.hMul Real Real Real qz0 qz361 (@Neg.neg Real Real.instNeg (Real.sin qz412))) Bool.false 26185224615 137438953472 3165142622801 18913524143095808 Bool.true 33445138485 549755813888 6306893273847 37827048286191616 (@Enclosure.Real.IsNear.mulLit_ff qz361 (Real.cos qz412) 209715 1048576 1 1048576 124861 131072 60042343 72149368832 26185224615 137438953472 3165142622801 18913524143095808 qz611 (@Enclosure.Real.IsNear.recentre' (Real.cos qz412) Bool.false 998888 1048576 120084686 144298737664 124861 131072 60042343 72149368832 (ep1449 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz361 (@Neg.neg Real Real.instNeg (Real.sin qz412)) 209715 1048576 1 1048576 159479 524288 60042343 72149368832 33445138485 549755813888 6306893273847 37827048286191616 qz611 (@Enclosure.Real.IsNear.neg (Real.sin qz412) Bool.false 159479 524288 60042343 72149368832 (@Enclosure.Real.IsNear.recentre' (Real.sin qz412) Bool.false 318958 1048576 120084686 144298737664 159479 524288 60042343 72149368832 (ep1451 rfl rfl) rfl)) rfl)

noncomputable def ep1453 := @ep1444 26185224615 137438953472 3165142622801 18913524143095808 Bool.true 33445138485 549755813888 6306893273847 37827048286191616 Bool.false 139341879153976210882560 1013845606605 549755813888 3764899385235 591047629471744 Bool.true 64332630176341723971584 117020372593 1099511627776 481616159006969 75654096572383232 EMRow35.d19 (ep1445 ep1452) rfl rfl

noncomputable abbrev qz413 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 26 1)))

noncomputable def ep1454 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz974 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz364 (Real.cos qz413)) (@HMul.hMul Real Real Real qz0 qz364 (@Neg.neg Real Real.instNeg (Real.sin qz413)))) Bool.false 2200997029 274877906944 3084035900617 18913524143095808 Bool.false 215452376743 1099511627776 12405286999891 75654096572383232 (BSN.cpow_neg_s_mk qz61 113311 1000 26 (@Eq.refl Real qz61) rfl)

noncomputable def ep1455 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz366 113311 1000 0 1 3668288609262839 1125899906842624 125000000068807 17201750000000000000 415657450604181549929 1125899906842624000 14163875007796589977 17201750000000000000000 qz384 (BSN.isNear_log_sfrac 26 1 3668288609262839 1125899906842624 125000000068807 17201750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz917) Bool.false 61543670347942250676224 18889465931478580854784 1000000000550456 137614000000000000000 3668288609262839 1125899906842624 125000000068807 17201750000000000000 (BSN.log_rat_reduce_isNear 26 1 4 52 32 254545 524288 24973259072661432 36028797018963968 137614 1000000000000000 rfl rfl rfl rfl (ep742 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1456 := BSN.sin_dyadic_bound_f 87704875 2147483648 1 0 1048576 275497 0 1 1 0 1 1 42812 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 87704875) qz268 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 87704875) qz269 0 0 rfl) rfl rfl

noncomputable abbrev qz977 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 387111167) qz277)

noncomputable def ep1457 := @Enclosure.Real.IsNear.cos_image qz413 qz977 Bool.false 387111167 1048576 27 32768 Bool.false 42812 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz413 Bool.false 415657450604181549929 1125899906842624000 14163875007796589977 17201750000000000000000 387111167 1048576 27 32768 (ep1455 rfl) rfl) (Enclosure.sfrac_false_div 387111167 1048576) (BSN.cos_reduce3 qz977 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6171681935330402893824) qz279) 226375608064910080 72057594037927936 Bool.false 42812 1048576 58 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q3 387111167 1048576 226375608064910080 72057594037927936 58 6171681935330402893824 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 42812 1048576 6171681935330402893824 151115727451828646838272 87704875 2147483648 275497 275228 (ep1456 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1458 := BSN.cos_dyadic_bound_f 87704875 2147483648 1 0 1048576 275497 0 1 1 0 1 1 1047701 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 87704875) qz272 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 87704875) qz273 0 0 rfl) rfl rfl

noncomputable def ep1459 := @Enclosure.Real.IsNear.sin_image qz413 qz977 Bool.false 387111167 1048576 27 32768 Bool.true 1047701 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz413 Bool.false 415657450604181549929 1125899906842624000 14163875007796589977 17201750000000000000000 387111167 1048576 27 32768 (ep1455 rfl) rfl) (Enclosure.sfrac_false_div 387111167 1048576) (BSN.sin_reduce3 qz977 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6171681935330402893824) qz279) 226375608064910080 72057594037927936 Bool.false 1047701 1048576 58 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q3 387111167 1048576 226375608064910080 72057594037927936 58 6171681935330402893824 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1047701 1048576 6171681935330402893824 151115727451828646838272 87704875 2147483648 275497 275228 (ep1458 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1460 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz364 (Real.cos qz413)) (@HMul.hMul Real Real Real qz0 qz364 (@Neg.neg Real Real.instNeg (Real.sin qz413))) Bool.false 2200997029 274877906944 3084035900617 18913524143095808 Bool.false 215452376743 1099511627776 12405286999891 75654096572383232 (@Enclosure.Real.IsNear.mulLit_ff qz364 (Real.cos qz413) 205643 1048576 1 1048576 10703 262144 1874173 2254667776 2200997029 274877906944 3084035900617 18913524143095808 qz612 (@Enclosure.Real.IsNear.recentre' (Real.cos qz413) Bool.false 42812 1048576 3748346 4509335552 10703 262144 1874173 2254667776 (ep1457 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz364 (@Neg.neg Real Real.instNeg (Real.sin qz413)) 205643 1048576 1 1048576 1047701 1048576 1874173 2254667776 215452376743 1099511627776 12405286999891 75654096572383232 qz612 (@Enclosure.Real.IsNear.neg (Real.sin qz413) Bool.true 1047701 1048576 1874173 2254667776 (@Enclosure.Real.IsNear.recentre' (Real.sin qz413) Bool.true 1047701 1048576 3748346 4509335552 1047701 1048576 1874173 2254667776 (ep1459 rfl rfl) rfl)) rfl)

noncomputable def ep1461 := @ep1442 2200997029 274877906944 3084035900617 18913524143095808 Bool.false 215452376743 1099511627776 12405286999891 75654096572383232 Bool.false 279893769220995386703872 1018247600663 549755813888 123560816228137 18913524143095808 Bool.false 108227133108220487270400 49216002075 549755813888 123505361501715 18913524143095808 (ep1443 (BSN.head_sum_c_succ qz64 25 26 rfl rfl) (ep1453 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1454 ep1460) rfl rfl

noncomputable abbrev qz414 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 27 1)))

noncomputable def ep1462 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz973 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz367 (Real.cos qz414)) (@HMul.hMul Real Real Real qz0 qz367 (@Neg.neg Real Real.instNeg (Real.sin qz414)))) Bool.true 195298448813 1099511627776 12169250084909 75654096572383232 Bool.true 10180961349 137438953472 1516303827557 9456762071547904 (BSN.cpow_neg_s_mk qz61 113311 1000 27 (@Eq.refl Real qz61) rfl)

noncomputable def ep1463 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz369 113311 1000 0 1 3710780868205815 1125899906842624 125000000068807 17201750000000000000 84094458191453820693 225179981368524800 14163875007796589977 17201750000000000000000 qz384 (BSN.isNear_log_sfrac 27 1 3710780868205815 1125899906842624 125000000068807 17201750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz920) Bool.false 62256572154556490711040 18889465931478580854784 1000000000550456 137614000000000000000 3710780868205815 1125899906842624 125000000068807 17201750000000000000 (BSN.log_rat_reduce_isNear 27 1 4 54 32 274332 524288 24973259072661432 36028797018963968 137614 1000000000000000 rfl rfl rfl rfl (ep756 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1464 := nat_lit 2614922370573165852690363183639686568060947400219059989528698259684297135730625

noncomputable def ep1465 := nat_lit 1651073847486493962450399983595170043864961509335784917132653573970187890625

noncomputable def ep1466 := nat_lit 6845933041462361004916507690511453593421938015272899177947423526720064575090625

noncomputable def ep1467 := BSN.sin_dyadic_bound_f 2524764135 2147483648 3 2 1048576 275497 ep1464 ep97 ep1465 ep1466 ep100 ep1465 967787 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2524764135) qz268 0 2 ep1464 ep97 ep1465 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2524764135) qz269 0 2 ep1466 ep100 ep1465 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz633 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 48949417) (@Nat.cast Real Real.instNatCast 131072))

noncomputable def ep1468 := @Enclosure.Real.IsNear.cos_image qz414 qz633 Bool.false 48949417 131072 27 32768 Bool.true 967787 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz414 Bool.false 84094458191453820693 225179981368524800 14163875007796589977 17201750000000000000000 48949417 131072 27 32768 (ep1463 rfl) rfl) (Enclosure.sfrac_false_div 48949417 131072) (BSN.cos_reduce1 qz633 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 22208060191213831061504) qz563) 226375608064910080 72057594037927936 Bool.false 967787 1048576 59 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q1 48949417 131072 226375608064910080 72057594037927936 59 22208060191213831061504 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 967787 1048576 22208060191213831061504 18889465931478580854784 2524764135 2147483648 275497 275228 (ep1467 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1469 := nat_lit 1453468460917308359922401946459201502275577427459182565256891323635262936690625

noncomputable def ep1470 := nat_lit 4357103235056952091842305039410414166739002359358876125936408663757848434290625

noncomputable def ep1471 := BSN.cos_dyadic_bound_f 2524764135 2147483648 3 2 1048576 275497 ep1469 ep104 ep1465 ep1470 ep106 ep1465 403608 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2524764135) qz272 0 2 ep1469 ep104 ep1465 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2524764135) qz273 0 2 ep1470 ep106 ep1465 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1472 := @Enclosure.Real.IsNear.sin_image qz414 qz633 Bool.false 48949417 131072 27 32768 Bool.false 403608 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz414 Bool.false 84094458191453820693 225179981368524800 14163875007796589977 17201750000000000000000 48949417 131072 27 32768 (ep1463 rfl) rfl) (Enclosure.sfrac_false_div 48949417 131072) (BSN.sin_reduce1 qz633 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 22208060191213831061504) qz563) 226375608064910080 72057594037927936 Bool.false 403608 1048576 59 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q1 48949417 131072 226375608064910080 72057594037927936 59 22208060191213831061504 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 403608 1048576 22208060191213831061504 18889465931478580854784 2524764135 2147483648 275497 275228 (ep1471 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1473 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz367 (Real.cos qz414)) (@HMul.hMul Real Real Real qz0 qz367 (@Neg.neg Real Real.instNeg (Real.sin qz414))) Bool.true 195298448813 1099511627776 12169250084909 75654096572383232 Bool.true 10180961349 137438953472 1516303827557 9456762071547904 (@Enclosure.Real.IsNear.mulLit_ft qz367 (Real.cos qz414) 201799 1048576 1 1048576 967787 1048576 1874173 2254667776 195298448813 1099511627776 12169250084909 75654096572383232 qz614 (@Enclosure.Real.IsNear.recentre' (Real.cos qz414) Bool.true 967787 1048576 3748346 4509335552 967787 1048576 1874173 2254667776 (ep1468 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz367 (@Neg.neg Real Real.instNeg (Real.sin qz414)) 201799 1048576 1 1048576 50451 131072 1874173 2254667776 10180961349 137438953472 1516303827557 9456762071547904 qz614 (@Enclosure.Real.IsNear.neg (Real.sin qz414) Bool.false 50451 131072 1874173 2254667776 (@Enclosure.Real.IsNear.recentre' (Real.sin qz414) Bool.false 403608 1048576 3748346 4509335552 50451 131072 1874173 2254667776 (ep1472 rfl rfl) rfl)) rfl)

noncomputable def ep1474 := @ep1440 195298448813 1099511627776 12169250084909 75654096572383232 Bool.true 10180961349 137438953472 1516303827557 9456762071547904 Bool.false 1012208619205726824300544 1841196752513 1099511627776 6101355602379 911495139426304 Bool.false 1167153126682015039488 8492156679 549755813888 1524553845263 227873784856576 (ep1441 (BSN.head_sum_c_succ qz64 26 27 rfl rfl) (ep1461 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1462 ep1473) rfl rfl

noncomputable abbrev qz415 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 28 1)))

noncomputable def ep1475 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz16 qz49 qz65) (Complex.mk (@HMul.hMul Real Real Real qz0 qz370 (Real.cos qz415)) (@HMul.hMul Real Real Real qz0 qz370 (@Neg.neg Real Real.instNeg (Real.sin qz415)))) Bool.false 43334086677 274877906944 2986195592929 18913524143095808 Bool.true 114589141891 1099511627776 11924383917303 75654096572383232 (BSN.cpow_neg_s_mk qz61 113311 1000 28 (@Eq.refl Real qz61) rfl)

noncomputable def ep1476 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz372 113311 1000 0 1 3751726938922231 1125899906842624 125000000068807 17201750000000000000 425111931176216916841 1125899906842624000 14163875007796589977 17201750000000000000000 qz384 (BSN.isNear_log_sfrac 28 1 3751726938922231 1125899906842624 125000000068807 17201750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz923) Bool.false 62943533227317076688896 18889465931478580854784 1000000000550456 137614000000000000000 3751726938922231 1125899906842624 125000000068807 17201750000000000000 (BSN.log_rat_reduce_isNear 28 1 4 56 32 293399 524288 24973259072661432 36028797018963968 137614 1000000000000000 rfl rfl rfl rfl (ep777 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1477 := nat_lit 2475947006778971440845514423366844416

noncomputable def ep1478 := BSN.cos_dyadic_bound_f 1254397952 2147483648 2 1 1048576 275497 ep1477 ep118 ep1477 ep1477 ep119 ep1477 874716 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1254397952) qz272 0 1 ep1477 ep118 ep1477 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1254397952) qz273 0 1 ep1477 ep119 ep1477 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz978 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 197958169) qz289)

noncomputable def ep1479 := @Enclosure.Real.IsNear.cos_image qz415 qz978 Bool.false 197958169 524288 27 32768 Bool.false 874716 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz415 Bool.false 425111931176216916841 1125899906842624000 14163875007796589977 17201750000000000000000 197958169 524288 27 32768 (ep1476 rfl) rfl) (Enclosure.sfrac_false_div 197958169 524288) (BSN.cos_reduce0 qz978 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 44135204314523283488768) qz290) 226375608064910080 72057594037927936 Bool.false 874716 1048576 60 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q0 197958169 524288 226375608064910080 72057594037927936 60 44135204314523283488768 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 874716 1048576 44135204314523283488768 75557863725914323419136 1254397952 2147483648 275497 275228 (ep1478 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1480 := BSN.sin_dyadic_bound_f 1254397952 2147483648 2 1 1048576 275497 ep1477 ep178 ep1477 ep1477 ep179 ep1477 578257 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1254397952) qz268 0 1 ep1477 ep178 ep1477 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1254397952) qz269 0 1 ep1477 ep179 ep1477 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1481 := @Enclosure.Real.IsNear.sin_image qz415 qz978 Bool.false 197958169 524288 27 32768 Bool.false 578257 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz415 Bool.false 425111931176216916841 1125899906842624000 14163875007796589977 17201750000000000000000 197958169 524288 27 32768 (ep1476 rfl) rfl) (Enclosure.sfrac_false_div 197958169 524288) (BSN.sin_reduce0 qz978 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 44135204314523283488768) qz290) 226375608064910080 72057594037927936 Bool.false 578257 1048576 60 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q0 197958169 524288 226375608064910080 72057594037927936 60 44135204314523283488768 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 578257 1048576 44135204314523283488768 75557863725914323419136 1254397952 2147483648 275497 275228 (ep1480 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1482 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz370 (Real.cos qz415)) (@HMul.hMul Real Real Real qz0 qz370 (@Neg.neg Real Real.instNeg (Real.sin qz415))) Bool.false 43334086677 274877906944 2986195592929 18913524143095808 Bool.true 114589141891 1099511627776 11924383917303 75654096572383232 (@Enclosure.Real.IsNear.mulLit_ff qz370 (Real.cos qz415) 198163 1048576 1 1048576 218679 262144 1874173 2254667776 43334086677 274877906944 2986195592929 18913524143095808 qz615 (@Enclosure.Real.IsNear.recentre' (Real.cos qz415) Bool.false 874716 1048576 3748346 4509335552 218679 262144 1874173 2254667776 (ep1479 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz370 (@Neg.neg Real Real.instNeg (Real.sin qz415)) 198163 1048576 1 1048576 578257 1048576 1874173 2254667776 114589141891 1099511627776 11924383917303 75654096572383232 qz615 (@Enclosure.Real.IsNear.neg (Real.sin qz415) Bool.false 578257 1048576 1874173 2254667776 (@Enclosure.Real.IsNear.recentre' (Real.sin qz415) Bool.false 578257 1048576 3748346 4509335552 578257 1048576 1874173 2254667776 (ep1481 rfl rfl) rfl)) rfl)

noncomputable def ep1483 := @ep1438 43334086677 274877906944 2986195592929 18913524143095808 Bool.true 114589141891 1099511627776 11924383917303 75654096572383232 Bool.false 553750641783277956890624 2014533099221 1099511627776 518357297369173 75654096572383232 Bool.true 53658821949558100066304 97604828533 1099511627776 518076260544619 75654096572383232 (ep1439 (BSN.head_sum_c_succ qz64 27 28 rfl rfl) (ep1474 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1475 ep1482) rfl rfl

noncomputable def ep1484 := @Enclosure.Complex.IsNear.mul qz78 (@HAdd.hAdd Complex Complex Complex qz15 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz80 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1))))) Bool.true ep1427 ep1234 ep1428 ep1429 Bool.false

noncomputable def ep1485 := nat_lit 78016011332232691388783196322011

noncomputable def ep1486 := nat_lit 5508919215419931048074543104000000

noncomputable def ep1487 := nat_lit 147633598241195317302872352958103493

noncomputable def ep1488 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re qz78) (Complex.re (@HAdd.hAdd Complex Complex Complex qz15 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz80 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 (Complex.im qz78) (Complex.im (@HAdd.hAdd Complex Complex Complex qz15 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz80 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1))))))) ep1485 ep1486 ep1487

noncomputable def ep1489 := nat_lit 1895261022276995978124325436784640000000

noncomputable def ep1490 := nat_lit 77097737863263760788849664281681657

noncomputable def ep1491 := nat_lit 202205715704050439530582962298210139831

noncomputable def ep1492 := nat_lit 639617161549620392212040555572144121538533740458507058783715328000000

noncomputable def ep1493 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re qz78) (Complex.re (@HAdd.hAdd Complex Complex Complex qz15 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz80 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))))) 15459786855 549755813888 5851065499173 37827048286191616 25231916864041619863841

noncomputable abbrev qz416 := (@HMul.hMul Real Real Real qz0 qz61 (Real.log (Enclosure.sfrac Bool.false 29 1)))

noncomputable abbrev qz634 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 29)))

noncomputable abbrev qz979 := (@Neg.neg Real Real.instNeg (Real.sin qz416))

noncomputable def ep1494 := @Enclosure.Complex.IsNear.of_eq qz78 (Complex.mk (@HMul.hMul Real Real Real qz0 qz634 (Real.cos qz416)) (@HMul.hMul Real Real Real qz0 qz634 qz979)) Bool.true 15459786855 549755813888 5851065499173 37827048286191616 Bool.false 100909296315 549755813888 5881261038281 37827048286191616 (BSN.cpow_neg_s_mk qz61 113311 1000 29 (@Eq.refl Real qz61) rfl)

noncomputable abbrev qz635 := (Real.sqrt (@Nat.cast Real Real.instNatCast 29))

noncomputable abbrev qz636 := (@Nat.cast Real Real.instNatCast 29)

noncomputable def ep1495 := @Enclosure.Real.IsNear.inv_image qz635 5646755 1048576 1 1048576 97357 97358 524288 (@Enclosure.Real.IsNear.of_eq qz635 (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz636 qz267)) Bool.false 5646755 1048576 1 1048576 (BSN.sqrt_natCast_div_one 29) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz636 qz267)) Bool.false 5646755 1048576 1 1048576 5646755 1048576 1 1048576 (BSN.sqrt_enclosure 29 1 2823377 2823378 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep1496 := BSN.log_dyadic_bound 13 45 6 5 353956287581982421875 524288 137614 10371179520995104305 130276274797305 311797 58 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 13) (BSN.artanhQ 45) 0 5 10371179520995104305 353956287581982421875 130276274797305 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz417 := (Real.log (Enclosure.sfrac Bool.false 29 1))

noncomputable def ep1497 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz417 113311 1000 0 1 3791236343078135 1125899906842624 125000000068807 17201750000000000000 85917756254105310997 225179981368524800 14163875007796589977 17201750000000000000000 qz384 (BSN.isNear_log_sfrac 29 1 3791236343078135 1125899906842624 125000000068807 17201750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 qz636 qz267)) Bool.false 63606391034871975772160 18889465931478580854784 1000000000550456 137614000000000000000 3791236343078135 1125899906842624 125000000068807 17201750000000000000 (BSN.log_rat_reduce_isNear 29 1 4 58 32 311797 524288 24973259072661432 36028797018963968 137614 1000000000000000 rfl rfl rfl rfl (ep1496 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1498 := nat_lit 3086356350297611786341528582559888806524399325138229574651534459283580670509056

noncomputable def ep1499 := nat_lit 7425783825811302934345630626967852883708480716215604096655252244204764594176

noncomputable def ep1500 := nat_lit 9244217483241212753155894486425730713805781013982257515761292873362332482338816

noncomputable def ep1501 := BSN.cos_dyadic_bound_f 3046791868 2147483648 3 2 1048576 275497 ep1498 ep104 ep1499 ep1500 ep106 ep1499 158794 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3046791868) qz272 0 2 ep1498 ep104 ep1499 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3046791868) qz273 0 2 ep1500 ep106 ep1499 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz980 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 400085729) qz277)

noncomputable def ep1502 := @Enclosure.Real.IsNear.cos_image qz416 qz980 Bool.false 400085729 1048576 865 1048576 Bool.true 158794 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz416 Bool.false 85917756254105310997 225179981368524800 14163875007796589977 17201750000000000000000 400085729 1048576 865 1048576 (ep1497 rfl) rfl) (Enclosure.sfrac_false_div 400085729 1048576) (BSN.cos_reduce2 qz980 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 214398917551285052899328) qz279) 226375608064910080 72057594037927936 Bool.false 158794 1048576 60 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q2 400085729 1048576 226375608064910080 72057594037927936 60 214398917551285052899328 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 158794 1048576 214398917551285052899328 151115727451828646838272 3046791868 2147483648 275497 275228 (ep1501 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1503 := nat_lit 5549500803475052173067274944106225569436952000675840751095437824915081395240960

noncomputable def ep1504 := nat_lit 14522384168621442153282493832596452348618393890134281465283942942572691178192896

noncomputable def ep1505 := BSN.sin_dyadic_bound_f 3046791868 2147483648 3 2 1048576 275497 ep1503 ep97 ep1499 ep1504 ep100 ep1499 1036482 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3046791868) qz268 0 2 ep1503 ep97 ep1499 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3046791868) qz269 0 2 ep1504 ep100 ep1499 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1506 := @Enclosure.Real.IsNear.sin_image qz416 qz980 Bool.false 400085729 1048576 865 1048576 Bool.true 1036482 1048576 1 137614 (@Enclosure.Real.IsNear.recentre' qz416 Bool.false 85917756254105310997 225179981368524800 14163875007796589977 17201750000000000000000 400085729 1048576 865 1048576 (ep1497 rfl) rfl) (Enclosure.sfrac_false_div 400085729 1048576) (BSN.sin_reduce2 qz980 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 214398917551285052899328) qz279) 226375608064910080 72057594037927936 Bool.false 1036482 1048576 60 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q2 400085729 1048576 226375608064910080 72057594037927936 60 214398917551285052899328 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1036482 1048576 214398917551285052899328 151115727451828646838272 3046791868 2147483648 275497 275228 (ep1505 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1507 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz634 (Real.cos qz416)) (@HMul.hMul Real Real Real qz0 qz634 qz979) Bool.true 15459786855 549755813888 5851065499173 37827048286191616 Bool.false 100909296315 549755813888 5881261038281 37827048286191616 (@Enclosure.Real.IsNear.mulLit_ft qz634 (Real.cos qz416) 194715 1048576 1 1048576 79397 524288 60042343 72149368832 15459786855 549755813888 5851065499173 37827048286191616 (@Enclosure.Real.IsNear.recentre' qz634 Bool.false 194715 1048576 1 1048576 194715 1048576 1 1048576 (ep1495 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' (Real.cos qz416) Bool.true 158794 1048576 120084686 144298737664 79397 524288 60042343 72149368832 (ep1502 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz634 qz979 194715 1048576 1 1048576 518241 524288 60042343 72149368832 100909296315 549755813888 5881261038281 37827048286191616 (@Enclosure.Real.IsNear.recentre' qz634 Bool.false 194715 1048576 1 1048576 194715 1048576 1 1048576 (ep1495 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg (Real.sin qz416) Bool.true 518241 524288 60042343 72149368832 (@Enclosure.Real.IsNear.recentre' (Real.sin qz416) Bool.true 1036482 1048576 120084686 144298737664 518241 524288 60042343 72149368832 (ep1506 rfl rfl) rfl)) rfl)

noncomputable def ep1508 := @ep1493 50103328389195040000000 0 1 ep1485 ep1486 ep1487 ep1489 (@Enclosure.Complex.IsNear.re_isNear qz78 Bool.true 15459786855 549755813888 5851065499173 37827048286191616 Bool.false 100909296315 549755813888 5881261038281 37827048286191616 (ep1494 ep1507))

noncomputable def ep1509 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz15 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz80 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1))))) Bool.false 25231916864041619863841 50103328389195040000000 0 1 Bool.false

noncomputable def ep1510 := nat_lit 34381353656621911559687551

noncomputable def ep1511 := nat_lit 225464977751377680000000000

noncomputable def ep1512 := @Enclosure.Complex.IsNear.addLitP qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz80 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) Bool.false 12810632721 25679265442 0 1 Bool.true 3286019000

noncomputable def ep1513 := @ep1512 12839632721 0 1 Bool.false 18445632721 3902240000000 0 1 Bool.false 7171864817249231 17560080000000000 0 1 Bool.false 50463833728083239727682 25231916864041619863841 50103328389195040000000 0 1 Bool.false ep1510 ep1510 ep1511 0 1

noncomputable abbrev qz81 := (@HDiv.hDiv Complex Complex Complex qz352 (@Nat.cast Complex Complex.instNatCast 29) (@HSub.hSub Complex Complex Complex qz595 qz382 (1 : Complex)))

noncomputable def ep1514 := @Enclosure.Complex.IsNear.addLitP qz81 qz26 Bool.true 58000000 51358530884 0 1 Bool.true 13144076000 51358530884 0 1

noncomputable def ep1515 := @Enclosure.Complex.IsNear.of_eq qz81 (Complex.mk (Enclosure.sfrac Bool.true 58000000 51358530884) (Enclosure.sfrac Bool.true 13144076000 51358530884)) Bool.true 58000000 51358530884 0 1 Bool.true 13144076000 51358530884 0 1

noncomputable def ep1516 := @ep1514 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 51242530884 12810632721 25679265442 0 1 Bool.true 13144076000 3286019000 12839632721 0 1 (ep1515 (BSN.N_div_s_sub_one_mk qz61 113311 1000 29 (@Eq.refl Real qz61) rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 58000000 51358530884) (Enclosure.sfrac Bool.true 13144076000 51358530884) Bool.true 58000000 51358530884 0 1 Bool.true 13144076000 51358530884 0 1 (Enclosure.Real.IsNear.const Bool.true 58000000 51358530884) (Enclosure.Real.IsNear.const Bool.true 13144076000 51358530884))) qz357 rfl

noncomputable abbrev qz418 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz80 3))

noncomputable def ep1517 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz80 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz15 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz80 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) qz418)) Bool.false 18445632721 3902240000000 0 1

noncomputable def ep1518 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz80 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) qz418) Bool.false 1 696 0 1 Bool.false

noncomputable def ep1519 := @ep1518 113311 348000 0 1 Bool.false 38516898163 11706720000000 0 1 Bool.false 1454191757249231 17560080000000000 0 1 Bool.false 38514481121448 18445632721 3902240000000 0 1 Bool.false 2495808956402732388000 7171864817249231 17560080000000000 0

noncomputable abbrev qz419 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz80 1))

noncomputable def ep1520 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz80 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz15 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz80 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) qz419)) Bool.false 1 696 0 1

noncomputable def ep1521 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz80 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) qz419) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1522 := @ep1521 0 1 0 1 Bool.false 1 696 0 1 Bool.false 113311 348000 0 1 Bool.false 1 1 696 0 1 Bool.false 113311 113311 348000 0

noncomputable def ep1523 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz80 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (Complex.mk qz264 qz264) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1524 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) qz419 Bool.false 1 696 0 1 Bool.false 113311 348000 0 1

noncomputable def ep1525 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz419)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz419)) 1 696 0 1 0 1 0

noncomputable def ep1526 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz419) 1 24 0 1 1 29 0 1 1

noncomputable def ep1527 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep1528 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep1529 := @ep1528 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep810) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 113311 1000 0 1 ep1188)

noncomputable def ep1530 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 113311 1000 0 1 0 1 0

noncomputable def ep1531 := @ep1530 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep810) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 113311 1000 0 1 ep1188)

noncomputable def ep1532 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)))) 113311 12000 0 1 0 1 0 1 113311

noncomputable def ep1533 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 113311 1000 0 1 113311 12000 0

noncomputable def ep1534 := @ep1533 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep810) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 113311 1000 0 1 ep1188)

noncomputable def ep1535 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep1536 := @ep1535 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep810) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 113311 1000 0 1 ep1188)

noncomputable def ep1537 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 113311 12000 0 1 (@ep1527 1 24 0 1 (ep1529 rfl) (ep1531 rfl) rfl rfl) (@ep1532 113311 12000 0 1 (ep1534 rfl) (ep1536 rfl) rfl rfl)

noncomputable def ep1538 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 113311 12000 0 1 ep1537

noncomputable abbrev qz420 := (@Enclosure.Complex.IsNear.of_eq (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz80 1)) (Complex.mk (Enclosure.sfrac Bool.false 1 29) qz554) Bool.false 1 29 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 29 1 29 EMRow35.d20 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 29) qz554 Bool.false 1 29 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 29) qz820))

noncomputable def ep1539 := @ep1526 696 0 1 ep1538 (@Enclosure.Complex.IsNear.re_isNear qz419 Bool.false 1 29 0 1 Bool.false 0 1 0 1 qz420)

noncomputable def ep1540 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz419) 113311 12000 0 1 0 1 0 1 0

noncomputable def ep1541 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 113311 12000 0 1 ep1537

noncomputable def ep1542 := @ep1540 1 0 1 ep1541 (@Enclosure.Complex.IsNear.im_isNear qz419 Bool.false 1 29 0 1 Bool.false 0 1 0 1 qz420)

noncomputable def ep1543 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz419)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz419)) 0 1 0 1 113311 348000 0

noncomputable def ep1544 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz419) 1 24 0 1 0 1 0 1 0

noncomputable def ep1545 := @ep1544 1 0 1 ep1538 (@Enclosure.Complex.IsNear.im_isNear qz419 Bool.false 1 29 0 1 Bool.false 0 1 0 1 qz420)

noncomputable def ep1546 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz40)) ↑qz52) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz419) 113311 12000 0 1 1 29 0 1 113311

noncomputable def ep1547 := @ep1546 348000 0 1 ep1541 (@Enclosure.Complex.IsNear.re_isNear qz419 Bool.false 1 29 0 1 Bool.false 0 1 0 1 qz420)

noncomputable def ep1548 := @ep1522 1 (@ep1523 0 1 0 1 (BSN.bern_sum_base qz64 29) qz360) (ep1524 (@ep1525 1 1 1 696 0 1 (ep1539 rfl) (ep1542 rfl) rfl rfl) (@ep1543 1 113311 113311 348000 0 1 (ep1545 rfl) (ep1547 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep1549 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) qz418 Bool.false 38516898163 11706720000000 0 1 Bool.false 1454191757249231 17560080000000000 0 1

noncomputable def ep1550 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.re qz418)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.im qz418)) 38516898163 11706720000000 0 1 0 1 0

noncomputable def ep1551 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.re qz418) 38516898163 480000000 0 1 1 24389 0 1 38516898163

noncomputable def ep1552 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)))) 38516898163 480000000 0 1 0 1 0 1 38516898163

noncomputable def ep1553 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 115550694489 2000000 0 1 38516898163 480000000 0

noncomputable def ep1554 := @ep1553 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep836) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 115550694489 2000000 0 1 Bool.true 1454191757249231 1000000000 0 1 EMRow35.d21)

noncomputable def ep1555 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 1454191757249231 1000000000 0 1 0 1 0

noncomputable def ep1556 := @ep1555 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep836) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 115550694489 2000000 0 1 Bool.true 1454191757249231 1000000000 0 1 EMRow35.d21)

noncomputable def ep1557 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)))) 1454191757249231 720000000000 0 1 0 1 0 1 1454191757249231

noncomputable def ep1558 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 1454191757249231 1000000000 0 1 1454191757249231 720000000000 0

noncomputable def ep1559 := @ep1558 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep836) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 115550694489 2000000 0 1 Bool.true 1454191757249231 1000000000 0 1 EMRow35.d21)

noncomputable def ep1560 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 115550694489 2000000 0 1 0 1 0

noncomputable def ep1561 := @ep1560 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep836) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 115550694489 2000000 0 1 Bool.true 1454191757249231 1000000000 0 1 EMRow35.d21)

noncomputable def ep1562 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 38516898163 480000000 0 1 Bool.false 1454191757249231 720000000000 0 1 (@ep1552 38516898163 480000000 0 1 (ep1554 rfl) (ep1556 rfl) rfl rfl) (@ep1557 1454191757249231 720000000000 0 1 (ep1559 rfl) (ep1561 rfl) rfl rfl)

noncomputable def ep1563 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 38516898163 480000000 0 1 Bool.false 1454191757249231 720000000000 0 1 ep1562

noncomputable abbrev qz421 := (@Enclosure.Complex.IsNear.of_eq (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz80 3)) (Complex.mk (Enclosure.sfrac Bool.false 1 24389) qz554) Bool.false 1 24389 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 29 3 24389 EMRow35.d22 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 24389) qz554 Bool.false 1 24389 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 24389) qz820))

noncomputable def ep1564 := @ep1551 11706720000000 0 1 ep1563 (@Enclosure.Complex.IsNear.re_isNear qz418 Bool.false 1 24389 0 1 Bool.false 0 1 0 1 qz421)

noncomputable def ep1565 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.im qz418) 1454191757249231 720000000000 0 1 0 1 0 1 0

noncomputable def ep1566 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 38516898163 480000000 0 1 Bool.false 1454191757249231 720000000000 0 1 ep1562

noncomputable def ep1567 := @ep1565 1 0 1 ep1566 (@Enclosure.Complex.IsNear.im_isNear qz418 Bool.false 1 24389 0 1 Bool.false 0 1 0 1 qz421)

noncomputable def ep1568 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.im qz418)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.re qz418)) 0 1 0 1 1454191757249231 17560080000000000 0

noncomputable def ep1569 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.im qz418) 38516898163 480000000 0 1 0 1 0 1 0

noncomputable def ep1570 := @ep1569 1 0 1 ep1563 (@Enclosure.Complex.IsNear.im_isNear qz418 Bool.false 1 24389 0 1 Bool.false 0 1 0 1 qz421)

noncomputable def ep1571 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz37)) ↑qz51) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)))) (Complex.re qz418) 1454191757249231 720000000000 0 1 1 24389 0 1 1454191757249231

noncomputable def ep1572 := @ep1571 17560080000000000 0 1 ep1566 (@Enclosure.Complex.IsNear.re_isNear qz418 Bool.false 1 24389 0 1 Bool.false 0 1 0 1 qz421)

noncomputable def ep1573 := @ep1519 1 (@ep1520 Bool.false 113311 348000 0 1 (BSN.bern_sum_succ qz64 29 0 1 1 rfl rfl) (ep1548 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1549 (@ep1550 1 38516898163 38516898163 11706720000000 0 1 (ep1564 rfl) (ep1567 rfl) rfl rfl) (@ep1568 1 1454191757249231 1454191757249231 17560080000000000 0 1 (ep1570 rfl) (ep1572 rfl) rfl rfl)) rfl rfl rfl rfl

noncomputable def ep1574 := ep1513 (ep1516 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep1517 Bool.false 7171864817249231 17560080000000000 0 1 (BSN.bern_sum_succ qz64 29 1 2 3 rfl rfl) (ep1573 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep1575 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz78) (Complex.im (@HAdd.hAdd Complex Complex Complex qz15 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz80 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))))) 100909296315 549755813888 5881261038281 37827048286191616 ep1510

noncomputable def ep1576 := @ep1575 ep1511 0 1 ep1490 ep1234 ep1491 ep1236 (@Enclosure.Complex.IsNear.im_isNear qz78 Bool.true 15459786855 549755813888 5851065499173 37827048286191616 Bool.false 100909296315 549755813888 5881261038281 37827048286191616 (ep1494 ep1507))

noncomputable def ep1577 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz15 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz80 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1))))) Bool.false 25231916864041619863841 50103328389195040000000 0 1 Bool.false

noncomputable def ep1578 := nat_lit 11811742207061102489676225530154269

noncomputable def ep1579 := nat_lit 22351950243902881532990299952858766147

noncomputable def ep1580 := @Enclosure.Real.IsNear.addLit_tf_p (@HMul.hMul Real Real Real qz0 (Complex.re qz78) (Complex.im (@HAdd.hAdd Complex Complex Complex qz15 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz80 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 (Complex.im qz78) (Complex.re (@HAdd.hAdd Complex Complex Complex qz15 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz80 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1))))))) ep1578 ep1234 ep1579

noncomputable def ep1581 := nat_lit 509226995085804277466584284609183

noncomputable def ep1582 := nat_lit 148395489573633290754410633508697321

noncomputable def ep1583 := nat_lit 1337575255507303458340485659809107851200039501644220307051905024000000

noncomputable def ep1584 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re qz78) (Complex.im (@HAdd.hAdd Complex Complex Complex qz15 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz80 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))))) 15459786855 549755813888 5851065499173 37827048286191616 ep1510

noncomputable def ep1585 := @ep1584 ep1511 0 1 ep1578 ep1234 ep1579 ep1424 (@Enclosure.Complex.IsNear.re_isNear qz78 Bool.true 15459786855 549755813888 5851065499173 37827048286191616 Bool.false 100909296315 549755813888 5881261038281 37827048286191616 (ep1494 ep1507))

noncomputable def ep1586 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz78) (Complex.re (@HAdd.hAdd Complex Complex Complex qz15 qz79 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 2, @HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz28 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz28 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz48 qz80 (@HSub.hSub Nat Nat Nat qz47 (@HMul.hMul Nat Nat Nat qz28 2 k) 1)))))) 100909296315 549755813888 5881261038281 37827048286191616 25231916864041619863841

noncomputable def ep1587 := @ep1586 50103328389195040000000 0 1 ep1581 ep1486 ep1582 ep1489 (@Enclosure.Complex.IsNear.im_isNear qz78 Bool.true 15459786855 549755813888 5851065499173 37827048286191616 Bool.false 100909296315 549755813888 5881261038281 37827048286191616 (ep1494 ep1507))

noncomputable abbrev qz981 := (ep1574 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep1588 := @ep1484 ep1430 ep1234 ep1431 ep1432 (@ep1488 ep1489 ep1490 ep1234 ep1491 ep1236 ep1492 ep1427 ep1234 ep1428 ep1429 (ep1508 (@ep1509 ep1510 ep1511 0 1 qz981) rfl) (ep1576 (@ep1577 ep1510 ep1511 0 1 qz981) rfl) rfl rfl) (@ep1580 ep1424 ep1581 ep1486 ep1582 ep1489 ep1583 ep1430 ep1234 ep1431 ep1432 (ep1585 (@ep1577 ep1510 ep1511 0 1 qz981) rfl) (ep1587 (@ep1509 ep1510 ep1511 0 1 qz981) rfl) rfl rfl)

noncomputable def ep1589 := @ep1435 ep1423 ep1424 (@ep1436 75654096572383232 (BSN.head_sum_c_eq qz64 29) (ep1437 (BSN.head_sum_c_succ qz64 28 29 rfl rfl) (ep1483 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep1588 rfl rfl rfl

noncomputable def ep1590 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz64 2 29) Bool.false ep1233 ep1234 ep1235 ep1236 Bool.true ep1422 ep1234 ep1423 ep1424 (@ep1425 ep1236 Bool.true ep1422 ep1234 ep1423 ep1424 (BSN.zetaApproximant_eq_folded' qz64 2 29 rfl) (ep1589 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep1591 := @Enclosure.Real.IsNear.mulLit_ft (Real.sin (@HSub.hSub Real Real Real qz597 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz408)) (Complex.im (zetaApproximant qz64 2 29)) 243 1048576 25638843

noncomputable def ep1592 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz597 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz408)) Bool.false 243 1048576 51277686

noncomputable def ep1593 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz597 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz408) qz961 Bool.false 56001499 524288 365

noncomputable def ep1594 := BSN.sin_dyadic_bound_f 498927 2147483648 1 0 1048576 275497 0 1 1 0 1 1 243 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 498927) qz268 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 498927) qz269 0 0 rfl) rfl rfl

noncomputable def ep1595 := @ep1593 1048576 Bool.false 243 1048576 1 137614 (@ep1243 56001499 524288 365 1048576 ep1419 rfl) (Enclosure.sfrac_false_div 56001499 524288) (BSN.sin_reduce0 qz961 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 17554437635370385408) qz290) 226375608064910080 72057594037927936 Bool.false 243 1048576 17 1000000000000000 275228 137614 (BSN.sin_reduce_arg_pos_rat_q0 56001499 524288 226375608064910080 72057594037927936 17 17554437635370385408 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 243 1048576 17554437635370385408 75557863725914323419136 498927 2147483648 275497 275228 (ep1594 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1596 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz64 2 29) Bool.false ep1233 ep1234 ep1235 ep1236 Bool.true ep1422 ep1234 ep1423 ep1424 (@ep1425 ep1236 Bool.true ep1422 ep1234 ep1423 ep1424 (BSN.zetaApproximant_eq_folded' qz64 2 29 rfl) (ep1589 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow35.d23 : Enclosure.Real.IsNear (hardyZApproximantEM 2 29 qz61) Bool.false ep1217 ep1218 ep1219 ep1220 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 2 29 qz61) ep1221 Bool.false ep1217 ep1218 ep1219 ep1220 (@Eq.refl Real ep1221) (@ep1222 Bool.false ep1217 ep1218 ep1219 ep1220 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz597 (Complex.im (@HSub.hSub Complex Complex Complex qz22 qz68 (∑ j ∈ Finset.range 4, Complex.log (@HAdd.hAdd Complex Complex Complex qz15 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz408) (zetaApproximant qz64 2 29)) (@ep1224 ep1225 ep1226 ep1227 ep1228 ep1229 ep1230 ep1227 ep1231 ep1217 ep1218 ep1219 ep1220 (@ep1232 72149368832 ep1233 ep1234 ep1235 ep1236 ep1223 ep1225 ep1226 ep1227 (@ep1237 144298737664 1048575 1048576 25638843 72149368832 (ep1421 rfl rfl) rfl) ep1590 rfl) (@ep1591 72149368832 ep1422 ep1234 ep1423 ep1424 ep1228 ep1229 ep1230 ep1227 (@ep1592 144298737664 243 1048576 25638843 72149368832 (ep1595 rfl rfl) rfl) ep1596 rfl) rfl rfl))

theorem EMRow35.d24 : @Eq Nat (Nat.mul (BSN.factNat (Nat.succ (Nat.mul 2 2))) (Nat.pow 4 (Nat.mul 2 2))) 30720 := @Eq.refl Nat 30720

theorem EMRow35.d25 : @Eq Nat (Nat.mul (Nat.mul 2 2) (Nat.pow (Nat.succ (Nat.mul 4 4)) (Nat.mul 2 2))) 334084 := @Eq.refl Nat 334084

theorem EMRow35.d179 : @Eq Nat (TangentNumbers.tangentNumber 3) 16 := Height20.tangent_three

noncomputable abbrev qz233 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 3)

theorem EMRow35.d180 : @Eq Real (@Rat.cast Real Real.instRatCast (bernoulli qz233)) (Enclosure.sfrac Bool.false 1 42) := BSN.bern_real_tangent_pos 2 16 1 42 EMRow35.d179 rfl rfl rfl

theorem EMRow35.d181 : @Eq Nat (BSN.factNat (Nat.mul 2 3)) 720 := @Eq.refl Nat 720

theorem EMRow35.d182 : @Eq Nat (Nat.pow 28 (Nat.succ (Nat.mul 2 5))) 8293509467471872 := @Eq.refl Nat 8293509467471872

noncomputable def ep1730 := nat_lit 1181671153346359170692730265957638242378174781758650

noncomputable def ep1731 := nat_lit 5986310706507378352962293074805895248510699696029696

noncomputable def ep1732 := nat_lit 2000000000000000000000000000000000000000000000000000

noncomputable def ep1733 := nat_lit 1499028120395240233173640088155429295548437777754679499662777369540625

noncomputable def ep1734 := nat_lit 4680297997409431328241185462095581837349556053595733828842639923095703125

noncomputable def ep1735 := nat_lit 13442882392639581675476766202062253719655739830178303899086159055189875

noncomputable def ep1736 := nat_lit 19584239746202378791298717228947477708711488730841665528714656829833984375

noncomputable def ep1737 := nat_lit 2442358029135994033939875

noncomputable def ep1738 := nat_lit 37260822860694382775919147000

noncomputable def ep1739 := nat_lit 116336546489037573337554931640625

noncomputable def ep1740 := nat_lit 57493278893883548332405996866302358825

noncomputable def ep1741 := nat_lit 40230676762013536063022911548614501953125

noncomputable def ep1742 := nat_lit 236310350532676991248348623960

noncomputable def ep1743 := nat_lit 344268321641720831394195556640625

noncomputable def ep1744 := nat_lit 81801971833623620377505564448994707675

noncomputable def ep1745 := nat_lit 56886557708273976459167897701263427734375

noncomputable def ep1746 := BSN.arctan_dyadic_bound_f 1 5 18 17 ep1731 ep1732 ep1733 ep1734 200200021673987500790625 ep1735 ep1736 ep1737 ep1730 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 17 8 ep1738 ep1739 151412625 ep1740 ep1741 1322214852783825 ep1733 ep1734 200200021673987500790625 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 8 ep1738 ep1739 151412625 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 8 17 ep1740 ep1741 1322214852783825 rfl rfl rfl rfl)) (@BSN.binarySplit_rec (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 17 8 ep1742 ep1743 1267389585 ep1744 ep1745 1927077560082675 ep1735 ep1736 ep1737 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 8 ep1742 ep1743 1267389585 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 8 17 ep1744 ep1745 1927077560082675 rfl rfl rfl rfl)) rfl

theorem EMRow35.d183 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz267 qz565)) Bool.false ep1730 ep1731 1 ep1732 := ep1746 rfl rfl rfl

noncomputable def ep1747 := nat_lit 25047178968060507272880539293402373975644382030403

noncomputable def ep1748 := nat_lit 4733915408010924740926662591654183582145509

noncomputable def ep1749 := nat_lit 77229300481955664312677298336960122659119574530232845

noncomputable def ep1750 := nat_lit 24516194103503660983641551147684725335332607

noncomputable def ep1751 := nat_lit 186647183216068817672719845704257068688983305564016735

noncomputable def ep1752 := BSN.arctan_dyadic_bound_f 1 239 6 5 ep1731 ep1732 ep1748 ep1749 9945 ep1750 ep1751 65835 ep1747 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 239) 0 5 ep1748 ep1749 9945 rfl rfl rfl rfl) (@BSN.binarySplit_of_base5 (BSN.arctanOddP 1) (BSN.arctanOddQ 239) 0 5 ep1750 ep1751 65835 rfl rfl rfl rfl) rfl rfl rfl

theorem EMRow35.d184 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz267 (@Nat.cast Real Real.instNatCast 239))) Bool.false ep1747 ep1731 1 ep1732 := ep1752 rfl

noncomputable def ep1753 := nat_lit 18806549737669504701992162098148602382148218980016788

noncomputable def ep1754 := nat_lit 100000000000000000000000000000000000000000000000000

theorem EMRow35.d185 : Enclosure.Real.IsNear Real.pi Bool.false ep1753 ep1731 1 ep1754 := BSN.pi_combine ep1730 ep1747 ep1731 ep1732 ep1754 ep1753 rfl rfl rfl rfl EMRow35.d183 EMRow35.d184

noncomputable def ep1755 := nat_lit 4236898907395812516429824

noncomputable def ep1756 := nat_lit 16947595629583250065719296

noncomputable abbrev qz538 := (@HAdd.hAdd Complex Complex Complex qz549 (@HAdd.hAdd Complex Complex Complex qz549 qz550 (@HMul.hMul Complex Complex Complex qz545 Complex.I ↑(Enclosure.sfrac Bool.false 111131 1000))) (@Nat.cast Complex Complex.instNatCast 5))

noncomputable abbrev qz234 := (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Norm.norm Complex Complex.instNorm qz538) (@HAdd.hAdd Real Real Real qz608 (Complex.re qz261) qz565))

noncomputable abbrev qz235 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 3)))

noncomputable abbrev qz236 := (@HPow.hPow Complex Complex Complex (@instHPow Complex Complex Complex.instPow) (@Nat.cast Complex Complex.instNatCast 28) (@HSub.hSub Complex Complex Complex qz595 (@Neg.neg Complex Complex.instNeg qz261) (@Nat.cast Complex Complex.instNatCast 5)))

noncomputable def ep1757 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 2 4) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz14 2 28))) (@HMul.hMul Real Real Real qz0 qz234 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236))) 1520518995 179359981764608 81127425 179359981764608 6327119626217751375 50728546202701266944 8880685583805

noncomputable def ep1758 := nat_lit 1134909194498999214042525235937280

noncomputable def ep1759 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 2 4) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz14 2 28)) 10095 171051008 15 171051008 150621 1048576 7801 1048576 1520518995 179359981764608

noncomputable abbrev qz539 := (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid)))

noncomputable abbrev qz540 := (@HMul.hMul Real Real Real qz0 (2 : Real) Real.pi)

noncomputable abbrev qz1106 := (@Inv.inv Real Real.instInv (@HPow.hPow Real Nat Real qz539 qz540 4))

noncomputable def ep1760 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 30720 334084) qz1106 30720 334084 0 1 673 1048576 1 1048576 10095 171051008 15 171051008

noncomputable def ep1761 := nat_lit 611446774371975769155682509262542103857872115376664175900625

noncomputable def ep1762 := nat_lit 392318858461667547739736838950479151006397215279002157056

noncomputable def ep1763 := nat_lit 19652562622312316682495810535216024035134795670488584765154486969712234385047

noncomputable def ep1764 := nat_lit 9903520314283042199192993792000000000000000000000000000000000000000000000000000000000000

noncomputable def ep1765 := nat_lit 691463075802508163054686763366652189853178875

noncomputable def ep1766 := nat_lit 2787593149816327892691964784081045188247552

noncomputable def ep1767 := nat_lit 2184744797947834540264818678394244808492865883128339

noncomputable def ep1768 := nat_lit 9223372036854775808000000000000000000000000000000000000000000000

noncomputable def ep1769 := @Enclosure.Real.IsNear.mulLit_ff (@HPow.hPow Real Nat Real qz539 qz540 3) qz540 ep1765 ep1766 ep1767 ep1768 884279719003555 140737488355328 1 500000000000000 ep1761 ep1762 ep1763 ep1764

noncomputable def ep1770 := nat_lit 781950621441006189802102638025

noncomputable def ep1771 := nat_lit 19807040628566084398385987584

noncomputable def ep1772 := nat_lit 26986075409044041160201671

noncomputable def ep1773 := nat_lit 1073741824000000000000000000000000000000

noncomputable def ep1774 := @Enclosure.Real.IsNear.mulLit_ff (@HPow.hPow Real Nat Real qz539 qz540 2) qz540 ep1770 ep1771 ep1772 ep1773 884279719003555 140737488355328 1 500000000000000 ep1765 ep1766 ep1767 ep1768

noncomputable def ep1775 := @Enclosure.Real.IsNear.mulLit_ff (@HPow.hPow Real Nat Real qz539 qz540 1) qz540 884279719003555 140737488355328 1 500000000000000 884279719003555 140737488355328 1 500000000000000 ep1770 ep1771 ep1772 ep1773

noncomputable abbrev qz541 := (@Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 (2 : Real) Real.pi) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 2 1) Real.pi) Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 2 1) Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) BSN.pi_near_15 rfl))

noncomputable def ep1776 := ep1775 (@Enclosure.Real.IsNear.of_eq (@HPow.hPow Real Nat Real qz539 qz540 1) qz540 Bool.false 884279719003555 140737488355328 1 500000000000000 (BSN.pow_one_r qz540) qz541) qz541 rfl

noncomputable def ep1777 := @Enclosure.Real.IsNear.of_eq (@HPow.hPow Real Nat Real qz539 qz540 3) (@HMul.hMul Real Real Real qz0 (@HPow.hPow Real Nat Real qz539 qz540 2) qz540) Bool.false ep1765 ep1766 ep1767 ep1768 (BSN.pow_succ_r qz540 2 3 rfl) (ep1774 (@Enclosure.Real.IsNear.of_eq (@HPow.hPow Real Nat Real qz539 qz540 2) (@HMul.hMul Real Real Real qz0 (@HPow.hPow Real Nat Real qz539 qz540 1) qz540) Bool.false ep1770 ep1771 ep1772 ep1773 (BSN.pow_succ_r qz540 1 2 rfl) ep1776) qz541 rfl)

noncomputable def ep1778 := @Enclosure.Real.IsNear.inv_image (@HPow.hPow Real Nat Real qz539 qz540 4) ep1761 ep1762 ep1763 ep1764 336 337 524288 (@Enclosure.Real.IsNear.of_eq (@HPow.hPow Real Nat Real qz539 qz540 4) (@HMul.hMul Real Real Real qz0 (@HPow.hPow Real Nat Real qz539 qz540 3) qz540) Bool.false ep1761 ep1762 ep1763 ep1764 (BSN.pow_succ_r qz540 3 4 rfl) (ep1769 ep1777 qz541 rfl))

noncomputable def ep1779 := ep1760 (Enclosure.Real.IsNear.const Bool.false 30720 334084) (@Enclosure.Real.IsNear.recentre' qz1106 Bool.false 673 1048576 1 1048576 673 1048576 1 1048576 (ep1778 rfl rfl rfl rfl rfl rfl) rfl)

noncomputable def ep1780 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz14 2 28)) (Real.sqrt (@HAdd.hAdd Real Real Real qz608 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz14 2 28)) (Complex.re (zetaApproximant qz14 2 28))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz14 2 28)) (Complex.im (zetaApproximant qz14 2 28))))) Bool.false 150621 1048576 7801 1048576

noncomputable def ep1781 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz608 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz14 2 28)) (Complex.re (zetaApproximant qz14 2 28))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz14 2 28)) (Complex.im (zetaApproximant qz14 2 28))))) Bool.false 150621 1048576 7801 1048576

noncomputable def ep1782 := nat_lit 1574809482700822116701067665712161212233655870644647840116007557

noncomputable def ep1783 := nat_lit 76119511034315630636110568142826035049031270400000000000000000000

noncomputable def ep1784 := nat_lit 31070606343930230704565501874511874366687167730002914763456226352200654889365171641

noncomputable def ep1785 := nat_lit 14539360086133724266073639105276721227082697622968032046150016040960000000000000000000

noncomputable def ep1786 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz608 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz14 2 28)) (Complex.re (zetaApproximant qz14 2 28))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz14 2 28)) (Complex.im (zetaApproximant qz14 2 28)))) ep1782 ep1783 ep1784 ep1785 71410 79211

noncomputable def ep1787 := nat_lit 19353992085892372733821926151485359415790372547904603610057599126313157641

noncomputable def ep1788 := nat_lit 940102539238390291035874051565984850136759944247404134400000000000000000000

noncomputable def ep1789 := nat_lit 581030780149599258394753863440436784758769991892713435564723014747551085530501509

noncomputable def ep1790 := nat_lit 296721634410892331960686512352586147491483624958531266247959511040000000000000000000

noncomputable def ep1791 := nat_lit 23863721879142427296837245386764819804075542518561842814899236987863009

noncomputable def ep1792 := nat_lit 235025634809597572758968512891496212534189986061851033600000000000000000000

noncomputable def ep1793 := nat_lit 26000981165998670432225625659304719135074381272599564207847986295706516983705977

noncomputable def ep1794 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz14 2 28)) (Complex.re (zetaApproximant qz14 2 28))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz14 2 28)) (Complex.im (zetaApproximant qz14 2 28))) ep1787 ep1788 ep1789 ep1790 ep1791 ep1792 ep1793

noncomputable def ep1795 := nat_lit 145393600861337242660736391052767212270826976229680320461500160409600000000000000000

noncomputable def ep1796 := nat_lit 4571118621621042900113909966939632993673450605010608286779119031617200920822972384578321959693560505309553194299222990423012147200000000000000000000

noncomputable def ep1797 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz14 2 28)) (Complex.re (zetaApproximant qz14 2 28)) ep495 ep496 ep497 ep498 ep495 ep496 ep497 ep498 ep1787

noncomputable def ep1798 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (zetaApproximant qz14 2 28)) (Complex.im (zetaApproximant qz14 2 28)) ep705 ep706 ep707 ep708 ep705 ep706 ep707 ep708 ep1791

noncomputable def ep1799 := @ep1757 202914184810805067776 ep1758 528483276487793407422735 ep1755 8407395758686219005 ep1756 (@ep1759 81127425 179359981764608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 2 4) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 30720 334084) qz1106) Bool.false 10095 171051008 15 171051008 (BSN.theta_err_eq 2 4 30720 334084 EMRow35.d24 EMRow35.d25 rfl) (ep1779 rfl)) (ep1780 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz14 2 28)) (@ep1781 150621 1048576 7801 1048576 (@ep1786 524288 (@ep1794 ep1795 ep1796 ep1782 ep1783 ep1784 ep1785 (@ep1797 ep1788 ep1789 ep1790 ep875 ep875 rfl) (@ep1798 ep1792 ep1793 ep1795 ep883 ep883 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz237 := (@Norm.norm Complex Complex.instNorm qz538)

noncomputable def ep1800 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz234 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz237 (Enclosure.sfrac Bool.false 2 11)) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236))) Bool.false 6327119626217751375 50728546202701266944 8880685583805 202914184810805067776 (BSN.zrb_shape_eq qz237 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236)) qz11 5)

noncomputable def ep1801 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz237 (Enclosure.sfrac Bool.false 2 11)) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236)) 116671925 5767168 1 5767168 54230009715 8796093022208 148515 70368744177664

noncomputable def ep1802 := @Enclosure.Real.IsNear.mulLit_ff qz237 (Enclosure.sfrac Bool.false 2 11) 116671925 1048576 1 1048576 2 11 0 1 116671925 5767168

noncomputable abbrev qz238 := (Complex.re qz538)

noncomputable abbrev qz239 := (Complex.im qz538)

noncomputable abbrev qz240 := qz538

noncomputable abbrev qz1107 := (@HAdd.hAdd Real Real Real qz608 (@HMul.hMul Real Real Real qz0 qz238 qz238) (@HMul.hMul Real Real Real qz0 qz239 qz239))

noncomputable def ep1803 := @Enclosure.Real.IsNear.of_eq qz237 (Real.sqrt qz1107) Bool.false 116671925 1048576 1 1048576 (BSN.norm_eq_sqrt_mul_add qz240)

noncomputable def ep1804 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz1107) Bool.false 116671925 1048576 1 1048576 116671925

noncomputable def ep1805 := @Enclosure.Real.IsNear.sqrt_image qz1107 12380349161 1000000 0 1 58335962 58335963 524288

noncomputable def ep1806 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz238 qz238) (@HMul.hMul Real Real Real qz0 qz239 qz239) 121 4 0 1 12350099161 1000000 0 1

noncomputable def ep1807 := @Enclosure.Real.IsNear.mulLit_ff qz238 qz238 11 2 0 1 11 2 0 1 121 4

noncomputable def ep1808 := @Enclosure.Complex.IsNear.of_eq qz240 (Complex.mk (Enclosure.sfrac Bool.false 11 2) qz11) Bool.false 11 2 0 1 Bool.false 111131 1000 0 1 (BSN.s_add_nat_mk qz11 Bool.false 111131 1000 5 (@Eq.refl Real qz11))

noncomputable abbrev qz785 := (ep1808 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 11 2) qz11 Bool.false 11 2 0 1 Bool.false 111131 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 11 2) qz271))

noncomputable def ep1809 := @ep1807 0 1 (@Enclosure.Complex.IsNear.re_isNear qz240 Bool.false 11 2 0 1 Bool.false 111131 1000 0 1 qz785)

noncomputable def ep1810 := ep1809 (@Enclosure.Complex.IsNear.re_isNear qz240 Bool.false 11 2 0 1 Bool.false 111131 1000 0 1 qz785)

noncomputable def ep1811 := @Enclosure.Real.IsNear.mulLit_ff qz239 qz239 111131 1000 0 1 111131 1000 0 1 12350099161 1000000

noncomputable def ep1812 := @ep1811 0 1 (@Enclosure.Complex.IsNear.im_isNear qz240 Bool.false 11 2 0 1 Bool.false 111131 1000 0 1 qz785)

noncomputable def ep1813 := ep1812 (@Enclosure.Complex.IsNear.im_isNear qz240 Bool.false 11 2 0 1 Bool.false 111131 1000 0 1 qz785)

noncomputable def ep1814 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236)) (Real.sqrt (@HAdd.hAdd Real Real Real qz608 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236)) (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236)) (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236))))) Bool.false 54230009715 8796093022208

noncomputable def ep1815 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz608 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236)) (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236)) (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236))))) Bool.false 1735360310880 281474976710656

noncomputable def ep1816 := nat_lit 54545947128475048654018663210038520258238771914224952237780921537234818225982755732663591413

noncomputable def ep1817 := nat_lit 1435035846974384790815860697512966733117390328522878571745011302400000000000000000000000000000000

noncomputable def ep1818 := nat_lit 489444798499195534697402669232826730762017963772694507063048700633416281777108431449106402005475771477363

noncomputable def ep1819 := nat_lit 18807647284326894317461558751626647511200127489414506429718095314232485082310398443520000000000000000000000000000000

noncomputable def ep1820 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz608 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236)) (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236)) (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236)))) ep1816 ep1817 ep1818 ep1819

noncomputable def ep1821 := nat_lit 4290396935705152533791939543163117695771874730347953071656716772891035763739432661785208209

noncomputable def ep1822 := nat_lit 4215979621291832814904301062162421541209495458971163364535503703057648493370784518114581525972003565693

noncomputable def ep1823 := nat_lit 1253843152288459621164103916775109834080008499294300428647873020948832338820693229568000000000000000000000000000000

noncomputable def ep1824 := nat_lit 256405868330458653674626141157527564094218863183045914112878595736447869705323076892236649

noncomputable def ep1825 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236)) (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236)) (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236))) ep1821 ep1817 ep1822 ep1823 ep1824

noncomputable def ep1826 := nat_lit 7321611464155024442938064783229422107741787390422849855841894400000000000000000000000000000000

noncomputable def ep1827 := nat_lit 13318909505619313827307442290637200238871110371503970518594254533985986074267083239918364972371741187249

noncomputable def ep1828 := nat_lit 587738977635215447420673710988332734725003984044203325928690478569765158822199951360000000000000000000000000000000

noncomputable def ep1829 := nat_lit 399364231819036752131341793026201629921572683817791387057636307855845290907665870837454659398930321341277419854708043059943180856805717010663669809492787200000000000000000000000000000000

noncomputable def ep1830 := nat_lit 2071327336686587674455462530633293756849519703

noncomputable def ep1831 := nat_lit 1197929817215676784414384529080320000000000000000

noncomputable def ep1832 := nat_lit 377155147998470522809683816029487828920760653863

noncomputable def ep1833 := nat_lit 387893256289169268846573609889921898014310400000000000000

noncomputable def ep1834 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236)) (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236)) ep1830 ep1831 ep1832 ep1833 ep1830 ep1831 ep1832

noncomputable def ep1835 := nat_lit 506365350641667279626152582729742936304901907

noncomputable def ep1836 := nat_lit 85566415515405484601027466362880000000000000000

noncomputable def ep1837 := nat_lit 464179241536369445323166195808825712310479398637

noncomputable def ep1838 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236) Bool.true ep1830 ep1831 ep1832 ep1833 Bool.false ep1835 ep1836 ep1837

noncomputable def ep1839 := nat_lit 242433285180730793029108506181201186258944000000000000000

noncomputable def ep1840 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236 Bool.true ep1830 ep1831 ep1832 ep1833 Bool.false ep1835 ep1836 ep1837 ep1839

noncomputable def ep1841 := nat_lit 30573561199122374215666707535879460570329

noncomputable def ep1842 := nat_lit 47917192688627071376575381163212800000000000

noncomputable def ep1843 := nat_lit 8007547489827859257585427284204062889235879

noncomputable def ep1844 := nat_lit 38789325628916926884657360988992189801431040000000000

noncomputable def ep1845 := nat_lit 945222122221549009949043406343426757035914901

noncomputable def ep1846 := nat_lit 399309939071892261471461509693440000000000000000

noncomputable def ep1847 := nat_lit 99026557700063976744609847729149066676133954621

noncomputable def ep1848 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.re qz236)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.im qz236)) ep1841 ep1842 ep1843 ep1844 ep1845 ep1846 ep1847

noncomputable def ep1849 := nat_lit 129297752096389756282191203296640632671436800000000000000

noncomputable def ep1850 := nat_lit 33084063704410647715480830033554088798247690792042066507984934034053710793932800000000000

noncomputable def ep1851 := nat_lit 80169737162940077059890379028174995456

noncomputable def ep1852 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.re qz236) 152407625707003403921 2419200000000000 0 1 200603880923246114249 ep1771 262701667737479164718995 ep1851 ep1841

noncomputable def ep1853 := nat_lit 16871344335410862913144651

noncomputable def ep1854 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5)))) 152407625707003403921 2419200000000000 0 1 0 1 0 1 152407625707003403921

noncomputable def ep1855 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) 1 30240 0 1 152407625707003403921 80000000000 0 1 152407625707003403921 2419200000000000 0

noncomputable def ep1856 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (Complex.mk (Enclosure.sfrac Bool.false 1 30240) qz264) Bool.false 1 30240 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 3 1 42 720 Bool.false EMRow35.d180 EMRow35.d181 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 30240) qz264 Bool.false 1 30240 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 30240) qz274)

noncomputable abbrev qz241 := (@HAdd.hAdd Complex Complex Complex qz262 qz261 qz263)

noncomputable def ep1857 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5)) (@HMul.hMul Complex Complex Complex qz3 (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 4)) qz241) Bool.false 152407625707003403921 80000000000 0 1 Bool.false ep1853 1000000000000000 0 1

noncomputable def ep1858 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.re qz241)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.im qz241)) 1370334858453642635289 2000000000000 0 1 152490986513840153921 125000000000 0 1

noncomputable def ep1859 := nat_lit 476273830334385637253125000000000

noncomputable def ep1860 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.re qz241) 152259428717071403921 1000000000000 0 1 9 2 0 1 1370334858453642635289 2000000000000

noncomputable abbrev qz242 := (@HAdd.hAdd Complex Complex Complex qz262 qz261 qz552)

noncomputable def ep1861 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 4)) (@HMul.hMul Complex Complex Complex qz3 (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3)) qz242) Bool.false 152259428717071403921 1000000000000 0 1 Bool.true 1372173259611091 125000000 0 1

noncomputable def ep1862 := @Enclosure.Real.IsNear.subLit_tt_p (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.re qz242)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.im qz242)) 778029997143 4000000 0 1 152453936216357153921 1000000000000 0 1

noncomputable def ep1863 := nat_lit 609037714868285615684000000

noncomputable def ep1864 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.re qz242) 111147142449 2000000 0 1 7 2 0 1 778029997143 4000000

noncomputable abbrev qz786 := (ep442 (BSN.ascPochhammer_succ_eval_c 2 3 qz14 rfl) (ep470 (@ep471 274367973322218200 1371839866611091 1000000000 0 1 (ep474 rfl) (ep477 rfl) rfl rfl)))

noncomputable def ep1865 := @ep1864 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 111147142449 2000000 0 1 Bool.true 1371839866611091 1000000000 0 1 qz786)

noncomputable def ep1866 := @Enclosure.Complex.IsNear.of_eq qz242 (Complex.mk (Enclosure.sfrac Bool.false 7 2) qz11) Bool.false 7 2 0 1 Bool.false 111131 1000 0 1 (BSN.s_add_nat_mk qz11 Bool.false 111131 1000 3 (@Eq.refl Real qz11))

noncomputable abbrev qz787 := (ep1866 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz11 Bool.false 7 2 0 1 Bool.false 111131 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz271))

noncomputable def ep1867 := ep1865 (@Enclosure.Complex.IsNear.re_isNear qz242 Bool.false 7 2 0 1 Bool.false 111131 1000 0 1 qz787)

noncomputable def ep1868 := @Enclosure.Real.IsNear.mulLit_tf (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.im qz242) 1371839866611091 1000000000 0 1 111131 1000 0 1 152453936216357153921 1000000000000

noncomputable def ep1869 := @ep1868 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 111147142449 2000000 0 1 Bool.true 1371839866611091 1000000000 0 1 qz786)

noncomputable def ep1870 := ep1869 (@Enclosure.Complex.IsNear.im_isNear qz242 Bool.false 7 2 0 1 Bool.false 111131 1000 0 1 qz787)

noncomputable def ep1871 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3)) qz242 Bool.false 152259428717071403921 1000000000000 0 1 Bool.true 1372173259611091 125000000 0 1 (@ep1862 ep1863 152259428717071403921 1000000000000 0 1 (ep1867 rfl) (ep1870 rfl) rfl rfl)

noncomputable def ep1872 := @Enclosure.Real.IsNear.addLit_tt (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.im qz242)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.re qz242)) 12351893087499819 2000000000 0 1 9602879066277637 2000000000 0 1

noncomputable def ep1873 := nat_lit 43909544307554912000000000

noncomputable def ep1874 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.im qz242) 111147142449 2000000 0 1 111131 1000 0 1 12351893087499819 2000000000

noncomputable def ep1875 := @ep1874 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 111147142449 2000000 0 1 Bool.true 1371839866611091 1000000000 0 1 qz786)

noncomputable def ep1876 := ep1875 (@Enclosure.Complex.IsNear.im_isNear qz242 Bool.false 7 2 0 1 Bool.false 111131 1000 0 1 qz787)

noncomputable def ep1877 := @Enclosure.Real.IsNear.mulLit_tf (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.re qz242) 1371839866611091 1000000000 0 1 7 2 0 1 9602879066277637 2000000000

noncomputable def ep1878 := @ep1877 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 111147142449 2000000 0 1 Bool.true 1371839866611091 1000000000 0 1 qz786)

noncomputable def ep1879 := ep1878 (@Enclosure.Complex.IsNear.re_isNear qz242 Bool.false 7 2 0 1 Bool.false 111131 1000 0 1 qz787)

noncomputable abbrev qz788 := (ep1861 (BSN.ascPochhammer_succ_eval_c 3 4 qz14 rfl) (ep1871 (@ep1872 ep1873 1372173259611091 125000000 0 1 (ep1876 rfl) (ep1879 rfl) rfl rfl)))

noncomputable def ep1880 := @ep1860 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 4)) Bool.false 152259428717071403921 1000000000000 0 1 Bool.true 1372173259611091 125000000 0 1 qz788)

noncomputable def ep1881 := @Enclosure.Complex.IsNear.of_eq qz241 (Complex.mk (Enclosure.sfrac Bool.false 9 2) qz11) Bool.false 9 2 0 1 Bool.false 111131 1000 0 1 (BSN.s_add_nat_mk qz11 Bool.false 111131 1000 4 (@Eq.refl Real qz11))

noncomputable abbrev qz789 := (ep1881 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9 2) qz11 Bool.false 9 2 0 1 Bool.false 111131 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 9 2) qz271))

noncomputable def ep1882 := ep1880 (@Enclosure.Complex.IsNear.re_isNear qz241 Bool.false 9 2 0 1 Bool.false 111131 1000 0 1 qz789)

noncomputable def ep1883 := @Enclosure.Real.IsNear.mulLit_tf (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.im qz241) 1372173259611091 125000000 0 1 111131 1000 0 1 152490986513840153921 125000000000

noncomputable def ep1884 := @ep1883 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 4)) Bool.false 152259428717071403921 1000000000000 0 1 Bool.true 1372173259611091 125000000 0 1 qz788)

noncomputable def ep1885 := ep1884 (@Enclosure.Complex.IsNear.im_isNear qz241 Bool.false 9 2 0 1 Bool.false 111131 1000 0 1 qz789)

noncomputable def ep1886 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 4)) qz241 Bool.false 152407625707003403921 80000000000 0 1 Bool.false ep1853 1000000000000000 0 1 (@ep1858 ep1859 152407625707003403921 80000000000 0 1 (ep1882 rfl) (ep1885 rfl) rfl rfl)

noncomputable def ep1887 := nat_lit 16920742572756862189144651

noncomputable def ep1888 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.im qz241)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.re qz241)) ep1887 1000000000000000 0 1 12349559336499819 250000000 0 1

noncomputable def ep1889 := nat_lit 4217836083852715728286162750000000

noncomputable def ep1890 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.im qz241) 152259428717071403921 1000000000000 0 1 111131 1000 0 1 ep1887 1000000000000000

noncomputable def ep1891 := @ep1890 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 4)) Bool.false 152259428717071403921 1000000000000 0 1 Bool.true 1372173259611091 125000000 0 1 qz788)

noncomputable def ep1892 := ep1891 (@Enclosure.Complex.IsNear.im_isNear qz241 Bool.false 9 2 0 1 Bool.false 111131 1000 0 1 qz789)

noncomputable def ep1893 := @Enclosure.Real.IsNear.mulLit_tf (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.re qz241) 1372173259611091 125000000 0 1 9 2 0 1 12349559336499819 250000000

noncomputable def ep1894 := @ep1893 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 4)) Bool.false 152259428717071403921 1000000000000 0 1 Bool.true 1372173259611091 125000000 0 1 qz788)

noncomputable def ep1895 := ep1894 (@Enclosure.Complex.IsNear.re_isNear qz241 Bool.false 9 2 0 1 Bool.false 111131 1000 0 1 qz789)

noncomputable abbrev qz790 := (ep1857 (BSN.ascPochhammer_succ_eval_c 4 5 qz14 rfl) (ep1886 (@ep1888 ep1889 ep1853 1000000000000000 0 1 (ep1892 rfl) (ep1895 rfl) rfl rfl)))

noncomputable def ep1896 := @ep1855 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) Bool.false 1 30240 0 1 Bool.false 0 1 0 1 ep1856) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5)) Bool.false 152407625707003403921 80000000000 0 1 Bool.false ep1853 1000000000000000 0 1 qz790)

noncomputable def ep1897 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) 0 1 0 1 ep1853 1000000000000000 0 1 0 1 0

noncomputable def ep1898 := @ep1897 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) Bool.false 1 30240 0 1 Bool.false 0 1 0 1 ep1856) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5)) Bool.false 152407625707003403921 80000000000 0 1 Bool.false ep1853 1000000000000000 0 1 qz790)

noncomputable def ep1899 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5)))) ep1853 30240000000000000000 0 1 0 1 0 1 ep1853

noncomputable def ep1900 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) 1 30240 0 1 ep1853 1000000000000000 0 1 ep1853 30240000000000000000 0

noncomputable def ep1901 := @ep1900 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) Bool.false 1 30240 0 1 Bool.false 0 1 0 1 ep1856) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5)) Bool.false 152407625707003403921 80000000000 0 1 Bool.false ep1853 1000000000000000 0 1 qz790)

noncomputable def ep1902 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) 0 1 0 1 152407625707003403921 80000000000 0 1 0 1 0

noncomputable def ep1903 := @ep1902 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) Bool.false 1 30240 0 1 Bool.false 0 1 0 1 ep1856) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5)) Bool.false 152407625707003403921 80000000000 0 1 Bool.false ep1853 1000000000000000 0 1 qz790)

noncomputable def ep1904 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5)) Bool.false 152407625707003403921 2419200000000000 0 1 Bool.false ep1853 30240000000000000000 0 1 (@ep1854 152407625707003403921 2419200000000000 0 1 (ep1896 rfl) (ep1898 rfl) rfl rfl) (@ep1899 ep1853 30240000000000000000 0 1 (ep1901 rfl) (ep1903 rfl) rfl rfl)

noncomputable def ep1905 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) Bool.false 152407625707003403921 2419200000000000 0 1 Bool.false ep1853 30240000000000000000 0 1 ep1904

noncomputable def ep1906 := nat_lit 39614081257132168796771975168

noncomputable def ep1907 := nat_lit 320678948651760308239561516112699981824

noncomputable def ep1908 := @Enclosure.Complex.IsNear.re_isNear qz236 Bool.false 200603880923246114249 ep1771 262701667737479164718995 ep1851 Bool.false 168075899009003948253 ep1906 440213398520736841835325 ep1907

noncomputable abbrev qz791 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 8293509467471872)))

noncomputable def ep1909 := @Enclosure.Complex.IsNear.of_eq qz236 (Complex.mk (@HMul.hMul Real Real Real qz0 qz791 (Real.cos qz371)) (@HMul.hMul Real Real Real qz0 qz791 qz922)) Bool.false 200603880923246114249 ep1771 262701667737479164718995 ep1851 Bool.false 168075899009003948253 ep1906 440213398520736841835325

noncomputable abbrev qz792 := (Real.sqrt (@Nat.cast Real Real.instNatCast 8293509467471872))

noncomputable abbrev qz793 := (@Nat.cast Real Real.instNatCast 8293509467471872)

noncomputable def ep1910 := @Enclosure.Real.IsNear.inv_image qz792 25633562294430545220073 281474976710656 1 281474976710656 1545398 1545399 140737488355328 (@Enclosure.Real.IsNear.of_eq qz792 (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz793 qz267)) Bool.false 25633562294430545220073 281474976710656 1 281474976710656 (BSN.sqrt_natCast_div_one 8293509467471872) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz793 qz267)) Bool.false 25633562294430545220073 281474976710656 1 281474976710656 25633562294430545220073 281474976710656 1 281474976710656 (BSN.sqrt_enclosure 8293509467471872 1 12816781147215272610036 12816781147215272610037 140737488355328 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep1911 := nat_lit 9332985752604445100283527168

noncomputable def ep1912 := nat_lit 505942171437500000000000000

noncomputable def ep1913 := nat_lit 16896284189627229735777967538176

noncomputable def ep1914 := nat_lit 5070602400912917605986812821504

noncomputable def ep1915 := nat_lit 66314852294656000000000000000

noncomputable def ep1916 := nat_lit 21918609655457519559609792048813734163111991050240000

noncomputable def ep1917 := nat_lit 569057034653488104001530221467611848327147657625600

noncomputable def ep1918 := nat_lit 25139617364453040909348401707587993600

noncomputable def ep1919 := BSN.log_dyadic_bound 12 44 13 12 ep1916 140737488355328 66314852294656 ep1917 ep1918 78758920438019 56 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base12 (BSN.artanhP 12) (BSN.artanhQ 44) 0 12 ep1917 ep1916 ep1918 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1920 := @Enclosure.Real.IsNear.mulLit_ff qz11 qz372 111131 1000 0 1 3751728747586831 1125899906842624 9653163217 505942171437500000000000 416933367448072115861 1125899906842624000 1072765681468427 ep1912 qz271 (BSN.isNear_log_sfrac 28 1 3751728747586831 1125899906842624 9653163217 505942171437500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz923) Bool.false ep1913 ep1914 1265259409178624 ep1915 3751728747586831 1125899906842624 9653163217 505942171437500000000000 (BSN.log_rat_reduce_isNear 28 1 4 56 32 78758920438019 140737488355328 24973259072661432 36028797018963968 66314852294656 1000000000000000 rfl rfl rfl rfl (ep1919 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1921 := nat_lit 989162653494962939526612143836131406991805235871411958132951220224

noncomputable def ep1922 := nat_lit 842498333348457493583344221469363458551160763204392890034487820288

noncomputable def ep1923 := nat_lit 838051404823506469362323538700647848434107485628876285522130534848065968159089097142843408709080278323545351532797498336987871112836621468540219612437474336615686670015062005191905231410844334373283243295495881098334453466972539468877266479203160469728073134477354666697503328176389402136942739456

noncomputable def ep1924 := nat_lit 52891321971172767596247250737880688851123773729959232653830066926421887024034431815363097947056912641878280075923682769184803106963825615327895103932397588487159726851292057237883449642301316355768873203215599328703548150308222295450928827049722111507143599254812955041773912982649933098895015936000

noncomputable def ep1925 := nat_lit 1938627972447960668957972088315174025425114841925017588773838145255214046861331843516097456491247174104796183015397495575917030879380939599398139726118636663652982784300257585955510094045165356843880037672030935903630971619221278358969935261877350320189513326534280262998368299029364736

noncomputable def ep1926 := nat_lit 6821483355492220634392802975784962120121899376672532278272915566088243287877624839822344016795595255742496750909193314606694056096180736661368584381878047810379279998466866207078701037922822785374482754362870047659621232502240975082303833865587484432175356477548064378112247610673919758150265733120

noncomputable def ep1927 := nat_lit 3014805352356847752986093292059199264514055102607676261268313814806047560369962613475696582982244020587061964327649917843533777096938060073690020924146662543768104430523647262559356629611175032278825772583289161736102244567568670840702943141834160355907185157524338437381113040011046186637015908352000

noncomputable def ep1928 := BSN.sin_dyadic_bound_f 676812552397437848 576460752303423488 5 4 281474976710656 132759225785201 ep1923 ep1924 ep1925 ep1926 ep1927 ep1925 259614437212468 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.sinEvenP 676812552397437848) (BSN.sinEvenQ 576460752303423488) 0 4 ep1923 ep1924 ep1925 rfl rfl rfl rfl) (@BSN.binarySplit_of_base4 (BSN.sinOddP 676812552397437848) (BSN.sinOddQ 576460752303423488) 0 4 ep1926 ep1927 ep1925 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz794 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26058335465504507) (@Nat.cast Real Real.instNatCast 70368744177664))

noncomputable def ep1929 := @Enclosure.Real.IsNear.cos_image qz371 qz794 Bool.false 26058335465504507 70368744177664 299 140737488355328 Bool.false 259614437212468 281474976710656 1 66314852294656 (@Enclosure.Real.IsNear.recentre' qz371 Bool.false 416933367448072115861 1125899906842624000 1072765681468427 ep1912 26058335465504507 70368744177664 299 140737488355328 (ep1920 rfl) rfl) (Enclosure.sfrac_false_div 26058335465504507 70368744177664) (BSN.cos_reduce3 qz794 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1921) (@Nat.cast Real Real.instNatCast ep1922)) ep1753 ep1731 Bool.false 259614437212468 281474976710656 58 ep1754 132629704589312 66314852294656 (BSN.sin_reduce_arg_pos_rat_q3 26058335465504507 70368744177664 ep1753 ep1731 58 ep1921 ep1922 rfl rfl rfl rfl) EMRow35.d185 (@BSN.sin_arg_round Bool.false 259614437212468 281474976710656 ep1921 ep1922 676812552397437848 576460752303423488 132759225785201 132629704589312 (ep1928 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1930 := nat_lit 246609563548755855401458222663700641105307518600962161347980591063630016991373948568461520500714931471299478956738062779398515748738247204860600794905124417240922206831499219836227813330385836430602366743125409834396457332973295032828027649548678364401899348185005465224965090862207522060648841216

noncomputable def ep1931 := nat_lit 3111254233598398093896897102228275814771986689997601920813533348613052177884378342080182232179818390698722357407275457010870770997872095019287947290141034616891748638311297484581379390723606844456992541365623489923738126488718958555936989826454241853361388191459585590692583116626466652876177408000

noncomputable def ep1932 := nat_lit 2513522587570755070713194461893133251056038712830211313096811498192685391122947484026289086715259773739568341234252590817557583038250538012013620291379349613781306846874565233701953243991022030183125286675588899293744206024512420742352766985428872077373514650539850331718541731456349110568889614336

noncomputable def ep1933 := nat_lit 476021897740554908366225256640926199660113963569633093884470602337796983216309886338267881523512213776904520683313144922663227962674430537951055935391578296384437541661628515140951046780711847201919858828940393958331933352774000659058359443447499003564292393293316595375965216843849397890055143424000

noncomputable def ep1934 := BSN.cos_dyadic_bound_f 676812552397437848 576460752303423488 5 4 281474976710656 132759225785201 ep1930 ep1931 ep1925 ep1932 ep1933 ep1925 108758937587298 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.cosEvenP 676812552397437848) (BSN.cosEvenQ 576460752303423488) 0 4 ep1930 ep1931 ep1925 rfl rfl rfl rfl) (@BSN.binarySplit_of_base4 (BSN.cosOddP 676812552397437848) (BSN.cosOddQ 576460752303423488) 0 4 ep1932 ep1933 ep1925 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1935 := @Enclosure.Real.IsNear.sin_image qz371 qz794 Bool.false 26058335465504507 70368744177664 299 140737488355328 Bool.true 108758937587298 281474976710656 1 66314852294656 (@Enclosure.Real.IsNear.recentre' qz371 Bool.false 416933367448072115861 1125899906842624000 1072765681468427 ep1912 26058335465504507 70368744177664 299 140737488355328 (ep1920 rfl) rfl) (Enclosure.sfrac_false_div 26058335465504507 70368744177664) (BSN.sin_reduce3 qz794 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1921) (@Nat.cast Real Real.instNatCast ep1922)) ep1753 ep1731 Bool.false 108758937587298 281474976710656 58 ep1754 132629704589312 66314852294656 (BSN.sin_reduce_arg_pos_rat_q3 26058335465504507 70368744177664 ep1753 ep1731 58 ep1921 ep1922 rfl rfl rfl rfl) EMRow35.d185 (@BSN.cos_arg_round Bool.false 108758937587298 281474976710656 ep1921 ep1922 676812552397437848 576460752303423488 132759225785201 132629704589312 (ep1934 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1936 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz791 (Real.cos qz371)) (@HMul.hMul Real Real Real qz0 qz791 qz922) Bool.false 200603880923246114249 ep1771 262701667737479164718995 ep1851 Bool.false 168075899009003948253 ep1906 440213398520736841835325 ep1907 (@Enclosure.Real.IsNear.mulLit_ff qz791 (Real.cos qz371) 3090797 281474976710656 1 281474976710656 64903609303117 70368744177664 2437607217341 1139280487378472302280704 200603880923246114249 ep1771 262701667737479164718995 ep1851 (@Enclosure.Real.IsNear.recentre' qz791 Bool.false 3090797 281474976710656 1 281474976710656 3090797 281474976710656 1 281474976710656 (ep1910 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' (Real.cos qz371) Bool.false 259614437212468 281474976710656 19968878324457472 ep1911 64903609303117 70368744177664 2437607217341 1139280487378472302280704 (ep1929 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz791 qz922 3090797 281474976710656 1 281474976710656 54379468793649 140737488355328 2437607217341 1139280487378472302280704 168075899009003948253 ep1906 440213398520736841835325 ep1907 (@Enclosure.Real.IsNear.recentre' qz791 Bool.false 3090797 281474976710656 1 281474976710656 3090797 281474976710656 1 281474976710656 (ep1910 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg (Real.sin qz371) Bool.true 54379468793649 140737488355328 2437607217341 1139280487378472302280704 (@Enclosure.Real.IsNear.recentre' (Real.sin qz371) Bool.true 108758937587298 281474976710656 19968878324457472 ep1911 54379468793649 140737488355328 2437607217341 1139280487378472302280704 (ep1935 rfl rfl) rfl)) rfl)

noncomputable def ep1937 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.im qz236) ep1853 30240000000000000000 0 1 168075899009003948253 ep1906 440213398520736841835325 ep1907 ep1845

noncomputable def ep1938 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) Bool.false 152407625707003403921 2419200000000000 0 1 Bool.false ep1853 30240000000000000000 0 1 ep1904

noncomputable def ep1939 := @Enclosure.Complex.IsNear.im_isNear qz236 Bool.false 200603880923246114249 ep1771 262701667737479164718995 ep1851 Bool.false 168075899009003948253 ep1906 440213398520736841835325 ep1907

noncomputable def ep1940 := nat_lit 8538682902177459361770217055866513766671

noncomputable def ep1941 := nat_lit 31944795125751380917716920775475200000000000

noncomputable def ep1942 := nat_lit 894558384972751820265535701810282292550791

noncomputable def ep1943 := nat_lit 10343820167711180502575296263731250613714944000000000

noncomputable def ep1944 := nat_lit 3384457150075843594349876509310703421009232099

noncomputable def ep1945 := nat_lit 598964908607838392207192264540160000000000000000

noncomputable def ep1946 := nat_lit 886426058777141149071385405595294442157640469149

noncomputable def ep1947 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.im qz236)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.re qz236)) ep1940 ep1941 ep1942 ep1943 ep1944 ep1945 ep1946

noncomputable def ep1948 := nat_lit 484866570361461586058217012362402372517888000000000000000

noncomputable def ep1949 := nat_lit 113230161695191252585571020302850086698972363119043418531654579316582551178444800000000000

noncomputable def ep1950 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.im qz236) 152407625707003403921 2419200000000000 0 1 168075899009003948253 ep1906 440213398520736841835325 ep1907 ep1940

noncomputable def ep1951 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.re qz236) ep1853 30240000000000000000 0 1 200603880923246114249 ep1771 262701667737479164718995 ep1851 ep1944

noncomputable abbrev qz795 := (@ep1909 ep1907 (BSN.cpow_neg_s_sub_mk qz11 111131 1000 28 5 8293509467471872 (@Eq.refl Real qz11) rfl EMRow35.d182) ep1936)

noncomputable def ep1952 := ep1840 (@ep1848 ep1849 ep1850 ep1830 ep1831 ep1832 ep1833 (@ep1852 ep1842 ep1843 ep1844 ep1905 (ep1908 qz795) rfl) (@ep1937 ep1846 ep1847 ep1849 ep1938 (ep1939 qz795) rfl) rfl rfl) (@ep1947 ep1948 ep1949 ep1835 ep1836 ep1837 ep1839 (@ep1950 ep1941 ep1942 ep1943 ep1905 (ep1939 qz795) rfl) (@ep1951 ep1945 ep1946 ep1948 ep1938 (ep1908 qz795) rfl) rfl rfl)

noncomputable def ep1953 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236)) (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236)) ep1835 ep1836 ep1837 ep1839 ep1835 ep1836 ep1837

noncomputable def ep1954 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236) Bool.true ep1830 ep1831 ep1832 ep1833 Bool.false ep1835 ep1836 ep1837

noncomputable def ep1955 := @ep1801 6327119626217751375 50728546202701266944 8880685583805 202914184810805067776 (@ep1802 1 5767168 (ep1803 (@ep1804 1048576 1 1048576 (ep1805 (@ep1806 49521396644 12380349161 1000000 0 1 (ep1810 rfl) (ep1813 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 11) rfl) (@ep1814 148515 70368744177664 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236)) (@ep1815 594060 281474976710656 54230009715 8796093022208 148515 70368744177664 (@ep1820 867679858410 867680452470 140737488355328 (@ep1825 ep1826 ep1827 ep1828 ep1829 ep1816 ep1817 ep1818 ep1819 (@ep1834 ep1833 ep1821 ep1817 ep1822 ep1823 (@ep1838 ep1839 ep1952) (@ep1838 ep1839 ep1952) rfl) (@ep1953 ep1839 ep1824 ep1826 ep1827 ep1828 (@ep1954 ep1839 ep1952) (@ep1954 ep1839 ep1952) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow35.d186 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz608 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 2 4) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz14 2 28))) (@HMul.hMul Real Real Real qz0 qz234 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236)))) Bool.false 528483276487793407422735 ep1755 8407395758686219005 ep1756 := ep1799 (ep1800 ep1955) rfl rfl

theorem EMRow35.d187 : @Eq Nat (Nat.pow 29 (Nat.succ (Nat.mul 2 5))) 12200509765705829 := @Eq.refl Nat 12200509765705829

noncomputable def ep1956 := nat_lit 15678418202388505243562571

noncomputable def ep1957 := nat_lit 135580765036666000525754368

noncomputable abbrev qz542 := (@HAdd.hAdd Complex Complex Complex qz549 (@HAdd.hAdd Complex Complex Complex qz549 qz550 (@HMul.hMul Complex Complex Complex qz545 Complex.I ↑(Enclosure.sfrac Bool.false 113311 1000))) (@Nat.cast Complex Complex.instNatCast 5))

noncomputable abbrev qz243 := (@Norm.norm Complex Complex.instNorm qz542)

noncomputable abbrev qz244 := (@HPow.hPow Complex Complex Complex (@instHPow Complex Complex Complex.instPow) (@Nat.cast Complex Complex.instNatCast 29) (@HSub.hSub Complex Complex Complex qz595 (@Neg.neg Complex Complex.instNeg qz382) (@Nat.cast Complex Complex.instNatCast 5)))

noncomputable abbrev qz796 := (@HDiv.hDiv Real Real Real qz1 qz243 (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (Complex.re qz64) (@Nat.cast Real Real.instNatCast 5)))

noncomputable def ep1958 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 2 4) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz64 2 29))) (@HMul.hMul Real Real Real qz0 qz796 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244))) 18948264525 179359981764608 102190455 179359981764608 187546783914622176651 1623313478486440542208 38708208859709

noncomputable def ep1959 := nat_lit 33669146716134869553712878487339008

noncomputable def ep1960 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 2 4) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz64 2 29)) 10095 171051008 15 171051008 1876995 1048576 7323 1048576 18948264525 179359981764608

noncomputable def ep1961 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz64 2 29)) (Real.sqrt (@HAdd.hAdd Real Real Real qz608 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz64 2 29)) (Complex.re (zetaApproximant qz64 2 29))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz64 2 29)) (Complex.im (zetaApproximant qz64 2 29))))) Bool.false 1876995 1048576 7323 1048576

noncomputable def ep1962 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz608 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz64 2 29)) (Complex.re (zetaApproximant qz64 2 29))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz64 2 29)) (Complex.im (zetaApproximant qz64 2 29))))) Bool.false 1876995 1048576 7323 1048576

noncomputable def ep1963 := nat_lit 189344697442984494416033944953986682689985487815794917839766681

noncomputable def ep1964 := nat_lit 59090847030979782541947643225502180140541542400000000000000000

noncomputable def ep1965 := nat_lit 181837090304107441618290620391857181185375936230169293678044983779512195244348821649

noncomputable def ep1966 := nat_lit 7273829043688948786644056328134795307462100104139751321564023357440000000000000000000

noncomputable def ep1967 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz608 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz64 2 29)) (Complex.re (zetaApproximant qz64 2 29))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz64 2 29)) (Complex.im (zetaApproximant qz64 2 29)))) ep1963 ep1964 ep1965 ep1966 934836 942159

noncomputable def ep1968 := nat_lit 24311160788571370176274600856319068959597552940434515878157205898972742649

noncomputable def ep1969 := nat_lit 7587047730505737166150555150269917737893335664588488704000000000000000000

noncomputable def ep1970 := nat_lit 1814228270190857193903469406288751039997967656642828773779055522835375541768378812351

noncomputable def ep1971 := nat_lit 72738290436889487866440563281347953074621001041397513215640233574400000000000000000000

noncomputable def ep1972 := nat_lit 2939796517287722911410460133545048266743313756599052543224758947361

noncomputable def ep1973 := nat_lit 51143615434780521968355526294083603157922292084742753103633518021560625618634619

noncomputable def ep1974 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz64 2 29)) (Complex.re (zetaApproximant qz64 2 29))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz64 2 29)) (Complex.im (zetaApproximant qz64 2 29))) ep1968 ep1969 ep1970 ep1971 ep1972 ep1969 ep1973

noncomputable def ep1975 := nat_lit 898003585640610961314081028164789544131123469646882879205434982400000000000000000000

noncomputable def ep1976 := nat_lit 184449959591266976238424722289124332530375368060917075224054200945273357953415031843659649774012249095759009620915514537714647040000000000000000000

noncomputable def ep1977 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz64 2 29)) (Complex.re (zetaApproximant qz64 2 29)) ep1233 ep1234 ep1235 ep1236 ep1233 ep1234 ep1235 ep1236 ep1968

noncomputable def ep1978 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (zetaApproximant qz64 2 29)) (Complex.im (zetaApproximant qz64 2 29)) ep1422 ep1234 ep1423 ep1424 ep1422 ep1234 ep1423 ep1424 ep1972

noncomputable def ep1979 := @ep1958 1623313478486440542208 ep1959 ep1956 ep1957 80480168857323059069 ep1957 (@ep1960 102190455 179359981764608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 2 4) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 30720 334084) qz1106) Bool.false 10095 171051008 15 171051008 (BSN.theta_err_eq 2 4 30720 334084 EMRow35.d24 EMRow35.d25 rfl) (ep1779 rfl)) (ep1961 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz64 2 29)) (@ep1962 1876995 1048576 7323 1048576 (@ep1967 524288 (@ep1974 ep1975 ep1976 ep1963 ep1964 ep1965 ep1966 (@ep1977 ep1969 ep1970 ep1971 ep1590 ep1590 rfl) (@ep1978 ep1969 ep1973 ep1975 ep1596 ep1596 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable def ep1980 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz796 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz243 (Enclosure.sfrac Bool.false 2 11)) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244))) Bool.false 187546783914622176651 1623313478486440542208 38708208859709 1623313478486440542208 (BSN.zrb_shape_eq qz243 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244)) qz61 5)

noncomputable def ep1981 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz243 (Enclosure.sfrac Bool.false 2 11)) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244)) 118955079 5767168 1 5767168 1576618547869 281474976710656 78037 70368744177664

noncomputable def ep1982 := @Enclosure.Real.IsNear.mulLit_ff qz243 (Enclosure.sfrac Bool.false 2 11) 118955079 1048576 1 1048576 2 11 0 1 118955079 5767168

noncomputable abbrev qz245 := (Complex.re qz542)

noncomputable abbrev qz246 := (Complex.im qz542)

noncomputable abbrev qz247 := qz542

noncomputable abbrev qz1108 := (@HAdd.hAdd Real Real Real qz608 (@HMul.hMul Real Real Real qz0 qz245 qz245) (@HMul.hMul Real Real Real qz0 qz246 qz246))

noncomputable def ep1983 := @Enclosure.Real.IsNear.of_eq qz243 (Real.sqrt qz1108) Bool.false 118955079 1048576 1 1048576 (BSN.norm_eq_sqrt_mul_add qz247)

noncomputable def ep1984 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz1108) Bool.false 118955079 1048576 1 1048576 118955079

noncomputable def ep1985 := @Enclosure.Real.IsNear.sqrt_image qz1108 12869632721 1000000 0 1 59477539 59477540 524288

noncomputable def ep1986 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz245 qz245) (@HMul.hMul Real Real Real qz0 qz246 qz246) 121 4 0 1 12839382721 1000000 0 1

noncomputable def ep1987 := @Enclosure.Real.IsNear.mulLit_ff qz245 qz245 11 2 0 1 11 2 0 1 121 4

noncomputable def ep1988 := @Enclosure.Complex.IsNear.of_eq qz247 (Complex.mk (Enclosure.sfrac Bool.false 11 2) qz61) Bool.false 11 2 0 1 Bool.false 113311 1000 0 1 (BSN.s_add_nat_mk qz61 Bool.false 113311 1000 5 (@Eq.refl Real qz61))

noncomputable abbrev qz797 := (ep1988 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 11 2) qz61 Bool.false 11 2 0 1 Bool.false 113311 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 11 2) qz384))

noncomputable def ep1989 := @ep1987 0 1 (@Enclosure.Complex.IsNear.re_isNear qz247 Bool.false 11 2 0 1 Bool.false 113311 1000 0 1 qz797)

noncomputable def ep1990 := ep1989 (@Enclosure.Complex.IsNear.re_isNear qz247 Bool.false 11 2 0 1 Bool.false 113311 1000 0 1 qz797)

noncomputable def ep1991 := @Enclosure.Real.IsNear.mulLit_ff qz246 qz246 113311 1000 0 1 113311 1000 0 1 12839382721 1000000

noncomputable def ep1992 := @ep1991 0 1 (@Enclosure.Complex.IsNear.im_isNear qz247 Bool.false 11 2 0 1 Bool.false 113311 1000 0 1 qz797)

noncomputable def ep1993 := ep1992 (@Enclosure.Complex.IsNear.im_isNear qz247 Bool.false 11 2 0 1 Bool.false 113311 1000 0 1 qz797)

noncomputable def ep1994 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244)) (Real.sqrt (@HAdd.hAdd Real Real Real qz608 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244))))) Bool.false 1576618547869 281474976710656

noncomputable def ep1995 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz608 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244))))) Bool.false 3153237095738 562949953421312

noncomputable def ep1996 := nat_lit 1440742632045343228849639395057106882738423719263142735229839778810357956968413784575535127253

noncomputable def ep1997 := nat_lit 45921147103180313306107542320414935459756490512732114295840361676800000000000000000000000000000000

noncomputable def ep1998 := nat_lit 955632209872409013361863279118711896035720515995009322185126051687079217405385425720176378735422670140761148361771

noncomputable def ep1999 := nat_lit 76922598886939156027975503333717255099440922367848557657400481620203548183108992333629305651200000000000000000000000000000000

noncomputable def ep2000 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz608 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244)))) ep1996 ep1997 ep1998 ep1999

noncomputable def ep2001 := nat_lit 115060360812770486565303395489495338774556254067640781705170071441126122519519583382665947369

noncomputable def ep2002 := nat_lit 3673691768254425064488603385633194836780519241018569143667228934144000000000000000000000000000000

noncomputable def ep2003 := nat_lit 270123693874820996236886104093794679367487929029682745716516910753652446560951053137886499519580875490918511206953

noncomputable def ep2004 := nat_lit 21977885396268330293707286666776358599840263533671016473542994748629585195173997809608373043200000000000000000000000000000000

noncomputable def ep2005 := nat_lit 4976243771424293566693902876830296112941086835265927830427771592562850948837984584421570281

noncomputable def ep2006 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244))) ep2001 ep2002 ep2003 ep2004 ep2005

noncomputable def ep2007 := nat_lit 91842294206360626612215084640829870919512981025464228591680723353600000000000000000000000000000000

noncomputable def ep2008 := nat_lit 6799520873690351021841276526953678833008509594079808118211242699530436294704493158382420277926403948364239424957

noncomputable def ep2009 := nat_lit 51281732591292770685317002222478170066293948245232371771600321080135698788739328222419537100800000000000000000000000000000000

noncomputable def ep2010 := nat_lit 10585688695036382919258153970270529130640128955050107900737572768165054041061274112121068644371071985449854521161849070585397656368896856018351369188901193252864000000000000000000000000000000

noncomputable def ep2011 := nat_lit 10726619262972396866655834503656556370192229037

noncomputable def ep2012 := nat_lit 1916687707545082855063015246528512000000000000000

noncomputable def ep2013 := nat_lit 61528901460135220053179339924060227289282681848509367

noncomputable def ep2014 := nat_lit 56033007359525319461512211045611895871252725760000000000000000

noncomputable def ep2015 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244)) ep2011 ep2012 ep2013 ep2014 ep2011 ep2012 ep2013

noncomputable def ep2016 := nat_lit 2230749598548499922310206937008264131342247341

noncomputable def ep2017 := nat_lit 9583438537725414275315076232642560000000000000000

noncomputable def ep2018 := nat_lit 111711496803000921754191309767859233970262632140900213

noncomputable def ep2019 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244) Bool.true ep2011 ep2012 ep2013 ep2014 Bool.true ep2016 ep2017 ep2018

noncomputable def ep2020 := nat_lit 392231051516677236230585477319283271098769080320000000000000000

noncomputable def ep2021 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244 Bool.true ep2011 ep2012 ep2013 ep2014 Bool.true ep2016 ep2017 ep2018 ep2020

noncomputable def ep2022 := nat_lit 7943617585231835596050997814287038323359

noncomputable def ep2023 := nat_lit 85186120335337015780578455401267200000000000

noncomputable def ep2024 := nat_lit 191384370701630316421651980186346767158898799661

noncomputable def ep2025 := nat_lit 10459494707111392966148946061847553895967175475200000000000

noncomputable def ep2026 := nat_lit 10547887867304680565744687052835098007916651537

noncomputable def ep2027 := nat_lit 423525396319635403506443430211433587256520067952278069

noncomputable def ep2028 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.re qz244)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.im qz244)) ep2022 ep2023 ep2024 ep2025 ep2026 ep2012 ep2027

noncomputable def ep2029 := nat_lit 913759079326910649230199405356821155468205525744550198474618886016797042435686400000000000

noncomputable def ep2030 := nat_lit 316912650057057350374175801344

noncomputable def ep2031 := nat_lit 3485466282427986967084497063

noncomputable def ep2032 := nat_lit 12970603555445675801275974779076827747975168

noncomputable def ep2033 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.re qz244) 164727776882963863841 2419200000000000 0 1 434004268253317732791 ep2030 ep2031 ep2032 ep2022

noncomputable def ep2034 := nat_lit 18595648341896755287687551

noncomputable def ep2035 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)))) 164727776882963863841 2419200000000000 0 1 0 1 0 1 164727776882963863841

noncomputable def ep2036 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) 1 30240 0 1 164727776882963863841 80000000000 0 1 164727776882963863841 2419200000000000 0

noncomputable abbrev qz248 := (@HAdd.hAdd Complex Complex Complex qz262 qz382 qz263)

noncomputable def ep2037 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)) (@HMul.hMul Complex Complex Complex qz3 (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4)) qz248) Bool.false 164727776882963863841 80000000000 0 1 Bool.false ep2034 1000000000000000 0 1

noncomputable def ep2038 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.re qz248)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.im qz248)) 1481163376412806774569 2000000000000 0 1 164814440353830613841 125000000000 0 1

noncomputable def ep2039 := nat_lit 514774302759262074503125000000000

noncomputable def ep2040 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.re qz248) 164573708490311863841 1000000000000 0 1 9 2 0 1 1481163376412806774569 2000000000000

noncomputable abbrev qz249 := (@HAdd.hAdd Complex Complex Complex qz262 qz382 qz552)

noncomputable def ep2041 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4)) (@HMul.hMul Complex Complex Complex qz3 (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) qz249) Bool.false 164573708490311863841 1000000000000 0 1 Bool.true 1454531690249231 125000000 0 1

noncomputable def ep2042 := @Enclosure.Real.IsNear.subLit_tt_p (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.re qz249)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.im qz249)) 808854861423 4000000 0 1 164775922205667613841 1000000000000 0 1

noncomputable def ep2043 := nat_lit 658294833961247455364000000

noncomputable def ep2044 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.re qz249) 115550694489 2000000 0 1 7 2 0 1 808854861423 4000000

noncomputable abbrev qz798 := (ep1181 (BSN.ascPochhammer_succ_eval_c 2 3 qz64 rfl) (ep1209 (@ep1210 290838351449846200 1454191757249231 1000000000 0 1 (ep1213 rfl) (ep1216 rfl) rfl rfl)))

noncomputable def ep2045 := @ep2044 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 115550694489 2000000 0 1 Bool.true 1454191757249231 1000000000 0 1 qz798)

noncomputable def ep2046 := @Enclosure.Complex.IsNear.of_eq qz249 (Complex.mk (Enclosure.sfrac Bool.false 7 2) qz61) Bool.false 7 2 0 1 Bool.false 113311 1000 0 1 (BSN.s_add_nat_mk qz61 Bool.false 113311 1000 3 (@Eq.refl Real qz61))

noncomputable abbrev qz799 := (ep2046 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz61 Bool.false 7 2 0 1 Bool.false 113311 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz384))

noncomputable def ep2047 := ep2045 (@Enclosure.Complex.IsNear.re_isNear qz249 Bool.false 7 2 0 1 Bool.false 113311 1000 0 1 qz799)

noncomputable def ep2048 := @Enclosure.Real.IsNear.mulLit_tf (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.im qz249) 1454191757249231 1000000000 0 1 113311 1000 0 1 164775922205667613841 1000000000000

noncomputable def ep2049 := @ep2048 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 115550694489 2000000 0 1 Bool.true 1454191757249231 1000000000 0 1 qz798)

noncomputable def ep2050 := ep2049 (@Enclosure.Complex.IsNear.im_isNear qz249 Bool.false 7 2 0 1 Bool.false 113311 1000 0 1 qz799)

noncomputable def ep2051 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) qz249 Bool.false 164573708490311863841 1000000000000 0 1 Bool.true 1454531690249231 125000000 0 1 (@ep2042 ep2043 164573708490311863841 1000000000000 0 1 (ep2047 rfl) (ep2050 rfl) rfl rfl)

noncomputable def ep2052 := @Enclosure.Real.IsNear.addLit_tt (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.im qz249)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.re qz249)) 13093164743243079 2000000000 0 1 10179342300744617 2000000000 0 1

noncomputable def ep2053 := nat_lit 46545014087975392000000000

noncomputable def ep2054 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.im qz249) 115550694489 2000000 0 1 113311 1000 0 1 13093164743243079 2000000000

noncomputable def ep2055 := @ep2054 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 115550694489 2000000 0 1 Bool.true 1454191757249231 1000000000 0 1 qz798)

noncomputable def ep2056 := ep2055 (@Enclosure.Complex.IsNear.im_isNear qz249 Bool.false 7 2 0 1 Bool.false 113311 1000 0 1 qz799)

noncomputable def ep2057 := @Enclosure.Real.IsNear.mulLit_tf (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3))) (Complex.re qz249) 1454191757249231 1000000000 0 1 7 2 0 1 10179342300744617 2000000000

noncomputable def ep2058 := @ep2057 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 115550694489 2000000 0 1 Bool.true 1454191757249231 1000000000 0 1 qz798)

noncomputable def ep2059 := ep2058 (@Enclosure.Complex.IsNear.re_isNear qz249 Bool.false 7 2 0 1 Bool.false 113311 1000 0 1 qz799)

noncomputable abbrev qz800 := (ep2041 (BSN.ascPochhammer_succ_eval_c 3 4 qz64 rfl) (ep2051 (@ep2052 ep2053 1454531690249231 125000000 0 1 (ep2056 rfl) (ep2059 rfl) rfl rfl)))

noncomputable def ep2060 := @ep2040 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4)) Bool.false 164573708490311863841 1000000000000 0 1 Bool.true 1454531690249231 125000000 0 1 qz800)

noncomputable def ep2061 := @Enclosure.Complex.IsNear.of_eq qz248 (Complex.mk (Enclosure.sfrac Bool.false 9 2) qz61) Bool.false 9 2 0 1 Bool.false 113311 1000 0 1 (BSN.s_add_nat_mk qz61 Bool.false 113311 1000 4 (@Eq.refl Real qz61))

noncomputable abbrev qz801 := (ep2061 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9 2) qz61 Bool.false 9 2 0 1 Bool.false 113311 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 9 2) qz384))

noncomputable def ep2062 := ep2060 (@Enclosure.Complex.IsNear.re_isNear qz248 Bool.false 9 2 0 1 Bool.false 113311 1000 0 1 qz801)

noncomputable def ep2063 := @Enclosure.Real.IsNear.mulLit_tf (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.im qz248) 1454531690249231 125000000 0 1 113311 1000 0 1 164814440353830613841 125000000000

noncomputable def ep2064 := @ep2063 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4)) Bool.false 164573708490311863841 1000000000000 0 1 Bool.true 1454531690249231 125000000 0 1 qz800)

noncomputable def ep2065 := ep2064 (@Enclosure.Complex.IsNear.im_isNear qz248 Bool.false 9 2 0 1 Bool.false 113311 1000 0 1 qz801)

noncomputable def ep2066 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4)) qz248 Bool.false 164727776882963863841 80000000000 0 1 Bool.false ep2034 1000000000000000 0 1 (@ep2038 ep2039 164727776882963863841 80000000000 0 1 (ep2062 rfl) (ep2065 rfl) rfl rfl)

noncomputable def ep2067 := nat_lit 18648011482745727603687551

noncomputable def ep2068 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.im qz248)) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.re qz248)) ep2067 1000000000000000 0 1 13090785212243079 250000000 0 1

noncomputable def ep2069 := nat_lit 4648912085474188821921887750000000

noncomputable def ep2070 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.im qz248) 164573708490311863841 1000000000000 0 1 113311 1000 0 1 ep2067 1000000000000000

noncomputable def ep2071 := @ep2070 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4)) Bool.false 164573708490311863841 1000000000000 0 1 Bool.true 1454531690249231 125000000 0 1 qz800)

noncomputable def ep2072 := ep2071 (@Enclosure.Complex.IsNear.im_isNear qz248 Bool.false 9 2 0 1 Bool.false 113311 1000 0 1 qz801)

noncomputable def ep2073 := @Enclosure.Real.IsNear.mulLit_tf (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4))) (Complex.re qz248) 1454531690249231 125000000 0 1 9 2 0 1 13090785212243079 250000000

noncomputable def ep2074 := @ep2073 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 4)) Bool.false 164573708490311863841 1000000000000 0 1 Bool.true 1454531690249231 125000000 0 1 qz800)

noncomputable def ep2075 := ep2074 (@Enclosure.Complex.IsNear.re_isNear qz248 Bool.false 9 2 0 1 Bool.false 113311 1000 0 1 qz801)

noncomputable abbrev qz802 := (ep2037 (BSN.ascPochhammer_succ_eval_c 4 5 qz64 rfl) (ep2066 (@ep2068 ep2069 ep2034 1000000000000000 0 1 (ep2072 rfl) (ep2075 rfl) rfl rfl)))

noncomputable def ep2076 := @ep2036 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) Bool.false 1 30240 0 1 Bool.false 0 1 0 1 ep1856) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)) Bool.false 164727776882963863841 80000000000 0 1 Bool.false ep2034 1000000000000000 0 1 qz802)

noncomputable def ep2077 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) 0 1 0 1 ep2034 1000000000000000 0 1 0 1 0

noncomputable def ep2078 := @ep2077 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) Bool.false 1 30240 0 1 Bool.false 0 1 0 1 ep1856) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)) Bool.false 164727776882963863841 80000000000 0 1 Bool.false ep2034 1000000000000000 0 1 qz802)

noncomputable def ep2079 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)))) ep2034 30240000000000000000 0 1 0 1 0 1 ep2034

noncomputable def ep2080 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) 1 30240 0 1 ep2034 1000000000000000 0 1 ep2034 30240000000000000000 0

noncomputable def ep2081 := @ep2080 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) Bool.false 1 30240 0 1 Bool.false 0 1 0 1 ep1856) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)) Bool.false 164727776882963863841 80000000000 0 1 Bool.false ep2034 1000000000000000 0 1 qz802)

noncomputable def ep2082 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) 0 1 0 1 164727776882963863841 80000000000 0 1 0 1 0

noncomputable def ep2083 := @ep2082 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) Bool.false 1 30240 0 1 Bool.false 0 1 0 1 ep1856) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)) Bool.false 164727776882963863841 80000000000 0 1 Bool.false ep2034 1000000000000000 0 1 qz802)

noncomputable def ep2084 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)) Bool.false 164727776882963863841 2419200000000000 0 1 Bool.false ep2034 30240000000000000000 0 1 (@ep2035 164727776882963863841 2419200000000000 0 1 (ep2076 rfl) (ep2078 rfl) rfl rfl) (@ep2079 ep2034 30240000000000000000 0 1 (ep2081 rfl) (ep2083 rfl) rfl rfl)

noncomputable def ep2085 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) Bool.false 164727776882963863841 2419200000000000 0 1 Bool.false ep2034 30240000000000000000 0 1 ep2084

noncomputable def ep2086 := nat_lit 22775511158996020909149484619

noncomputable def ep2087 := @Enclosure.Complex.IsNear.re_isNear qz244 Bool.true 434004268253317732791 ep2030 ep2031 ep2032 Bool.false 2836117266086350523435 ep2030 ep2086 ep2032

noncomputable abbrev qz803 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 12200509765705829)))

noncomputable def ep2088 := @Enclosure.Complex.IsNear.of_eq qz244 (Complex.mk (@HMul.hMul Real Real Real qz0 qz803 (Real.cos qz416)) (@HMul.hMul Real Real Real qz0 qz803 qz979)) Bool.true 434004268253317732791 ep2030 ep2031 ep2032 Bool.false 2836117266086350523435 ep2030 ep2086

noncomputable def ep2089 := nat_lit 23040420336865132002792177664

noncomputable abbrev qz804 := (Real.sqrt (@Nat.cast Real Real.instNatCast 12200509765705829))

noncomputable abbrev qz805 := (@Nat.cast Real Real.instNatCast 12200509765705829)

noncomputable def ep2090 := @Enclosure.Real.IsNear.inv_image qz804 62181153751734473178533 562949953421312 1 562949953421312 2548301 2548302 281474976710656 (@Enclosure.Real.IsNear.of_eq qz804 (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz805 qz267)) Bool.false 62181153751734473178533 562949953421312 1 562949953421312 (BSN.sqrt_natCast_div_one 12200509765705829) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz805 qz267)) Bool.false 62181153751734473178533 562949953421312 1 562949953421312 62181153751734473178533 562949953421312 1 562949953421312 (BSN.sqrt_enclosure 12200509765705829 1 31090576875867236589266 31090576875867236589267 281474976710656 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep2091 := nat_lit 46080840673730264005584355328

noncomputable def ep2092 := nat_lit 10232002062011750000000000000000

noncomputable def ep2093 := nat_lit 10232002062011750000000000000

noncomputable def ep2094 := nat_lit 34148436640226902274294903996416

noncomputable def ep2095 := nat_lit 10141204801825835211973625643008

noncomputable def ep2096 := nat_lit 81856016496094000000000000000

noncomputable def ep2097 := nat_lit 2055123328408090676726035087519655565731227397918701171875

noncomputable def ep2098 := nat_lit 60216682419407460939275284260049992295599748964071430625

noncomputable def ep2099 := nat_lit 725230276971108116281249126706877722225625

noncomputable def ep2100 := BSN.log_dyadic_bound 13 45 14 13 ep2097 281474976710656 81856016496094 ep2098 ep2099 167395169302661 58 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base13 (BSN.artanhP 13) (BSN.artanhQ 45) 0 13 ep2098 ep2097 ep2099 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep2101 := @Enclosure.Real.IsNear.mulLit_ff qz61 qz417 113311 1000 0 1 3791238061293323 1125899906842624 165928008248047 ep2093 429588975963207722453 1125899906842624000 18801468542594453617 ep2092 qz384 (BSN.isNear_log_sfrac 29 1 3791238061293323 1125899906842624 165928008248047 ep2093 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 qz636 qz267)) Bool.false ep2094 ep2095 1327424065984376 ep2096 3791238061293323 1125899906842624 165928008248047 ep2093 (BSN.log_rat_reduce_isNear 29 1 4 58 32 167395169302661 281474976710656 24973259072661432 36028797018963968 81856016496094 1000000000000000 rfl rfl rfl rfl (ep2100 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep2102 := nat_lit 9563681887625504913021167268885275427470438318670639790265057935360

noncomputable def ep2103 := nat_lit 6739986666787659948666753771754907668409286105635143120275902562304

noncomputable def ep2104 := nat_lit 34523559705992508312760050547852988564124182275570117882981296877695797779744610210239218703594666448591150781267670066524468428873914675073868097547929068018892447826190723760980543567806718465978169112725497312517703794888284042830446701515192651264380011431054903591498809532857608474315624910451521

noncomputable def ep2105 := nat_lit 203899157453104617481627048491632283796896919715682839482435721534704987529830619026566822768136578052831468415043204350664426848116545619184054913606682844652617638760369191949525279750462298158333463190937501035642101857564685667921886565266505194101891936515495401271629127131232118562893162610688000

noncomputable def ep2106 := nat_lit 2631801863426347244921845329889824736197243755624805566641311744775898918817246819257864236356313791947292928559863653068782893614891049046707218309057544451313935778004479493062393793853437646613140030465727642165612884448777728341484890938072121739853853518034560020795077079363479527519041

noncomputable def ep2107 := nat_lit 351574958051441317687608155517714659653698500093070324421613407784858725889938357686151687346223090590195583773434072834616134097747910497969597355197264619866068446053890715049446470241708127808433726697136068514453104853128514789576580311546315073311341495202283212041192061142902170127350153260331841

noncomputable def ep2108 := nat_lit 31196571090325006474688938419219739420925228716499474440812665394809863092064084711064723883524896442083214667501610265651657307761831479735160401781822475231850498730336486368277367801820731618225019868213437658453241584207396907192048644485775294697589466286870796394559256451078514140122653879435264000

noncomputable def ep2109 := BSN.cos_dyadic_bound_f 1635934172658775363 1152921504606846976 5 4 562949953421312 163871908024407 ep2104 ep2105 ep2106 ep2107 ep2108 ep2106 85155596434197 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.cosEvenP 1635934172658775363) (BSN.cosEvenQ 1152921504606846976) 0 4 ep2104 ep2105 ep2106 rfl rfl rfl rfl) (@BSN.binarySplit_of_base4 (BSN.cosOddP 1635934172658775363) (BSN.cosOddQ 1152921504606846976) 0 4 ep2107 ep2108 ep2106 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz806 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 214794487981603861) (@Nat.cast Real Real.instNatCast 562949953421312))

noncomputable def ep2110 := @Enclosure.Real.IsNear.cos_image qz416 qz806 Bool.false 214794487981603861 562949953421312 1035 562949953421312 Bool.true 85155596434197 562949953421312 1 81856016496094 (@Enclosure.Real.IsNear.recentre' qz416 Bool.false 429588975963207722453 1125899906842624000 18801468542594453617 ep2092 214794487981603861 562949953421312 1035 562949953421312 (ep2101 rfl) rfl) (Enclosure.sfrac_false_div 214794487981603861 562949953421312) (BSN.cos_reduce2 qz806 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep2102) (@Nat.cast Real Real.instNatCast ep2103)) ep1753 ep1731 Bool.false 85155596434197 562949953421312 60 ep1754 163712032992188 81856016496094 (BSN.sin_reduce_arg_pos_rat_q2 214794487981603861 562949953421312 ep1753 ep1731 60 ep2102 ep2103 rfl rfl rfl rfl) EMRow35.d185 (@BSN.cos_arg_round Bool.false 85155596434197 562949953421312 ep2102 ep2103 1635934172658775363 1152921504606846976 163871908024407 163712032992188 (ep2109 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep2111 := nat_lit 117254463804293593301005380785285329567104159467576658681719924678713864899864104722047126037265927066017328296645235185775040896776411632781366632907237246331129862516874255445180152878797021326038258174041302451665831716332796680993290892874810105923982735664437292373528144973814749437867802322301761

noncomputable def ep2112 := nat_lit 3466285676702778497187659824357748824547247635166608271201407266089984788007120523451635987058321826898134963055734473961295256417981275526128933531313608359094499858926276263141929755757859068691668874245937517605915731578599656354672071609530588299732162920763421821617695161230946015569183764381696000

noncomputable def ep2113 := nat_lit 953995931978747922516753957107932505258906623351648742301647751600093788017416947948847905098615719783836282862861719646174817988562587244798761448949868945603627579914783017585260533366283989673316606564313595245185705268648099693517363704446185197678962487082759942895397858082232887489924227296162625

noncomputable def ep2114 := nat_lit 197578283572058374339696609988391682999193115204496671458480214167129132916405869836743251262324344133193692894176865015793829615824932704989349211284875676468386491958797746999089996078197966915425125832018438503537196699980180412216308081743243533084733286483515043832208624190163922887443474569756672000

noncomputable def ep2115 := BSN.sin_dyadic_bound_f 1635934172658775363 1152921504606846976 5 4 562949953421312 163871908024407 ep2111 ep2112 ep2106 ep2113 ep2114 ep2106 556472078772145 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.sinEvenP 1635934172658775363) (BSN.sinEvenQ 1152921504606846976) 0 4 ep2111 ep2112 ep2106 rfl rfl rfl rfl) (@BSN.binarySplit_of_base4 (BSN.sinOddP 1635934172658775363) (BSN.sinOddQ 1152921504606846976) 0 4 ep2113 ep2114 ep2106 rfl rfl rfl rfl) rfl rfl

noncomputable def ep2116 := @Enclosure.Real.IsNear.sin_image qz416 qz806 Bool.false 214794487981603861 562949953421312 1035 562949953421312 Bool.true 556472078772145 562949953421312 1 81856016496094 (@Enclosure.Real.IsNear.recentre' qz416 Bool.false 429588975963207722453 1125899906842624000 18801468542594453617 ep2092 214794487981603861 562949953421312 1035 562949953421312 (ep2101 rfl) rfl) (Enclosure.sfrac_false_div 214794487981603861 562949953421312) (BSN.sin_reduce2 qz806 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep2102) (@Nat.cast Real Real.instNatCast ep2103)) ep1753 ep1731 Bool.false 556472078772145 562949953421312 60 ep1754 163712032992188 81856016496094 (BSN.sin_reduce_arg_pos_rat_q2 214794487981603861 562949953421312 ep1753 ep1731 60 ep2102 ep2103 rfl rfl rfl rfl) EMRow35.d185 (@BSN.sin_arg_round Bool.false 556472078772145 562949953421312 ep2102 ep2103 1635934172658775363 1152921504606846976 163871908024407 163712032992188 (ep2115 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep2117 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz803 (Real.cos qz416)) (@HMul.hMul Real Real Real qz0 qz803 qz979) Bool.true 434004268253317732791 ep2030 ep2031 ep2032 Bool.false 2836117266086350523435 ep2030 ep2086 ep2032 (@Enclosure.Real.IsNear.mulLit_ft qz803 (Real.cos qz416) 5096603 562949953421312 1 562949953421312 85155596434197 562949953421312 42641963513439301 ep2089 434004268253317732791 ep2030 ep2031 ep2032 (@Enclosure.Real.IsNear.recentre' qz803 Bool.false 5096603 562949953421312 1 562949953421312 5096603 562949953421312 1 562949953421312 (ep2090 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' (Real.cos qz416) Bool.true 85155596434197 562949953421312 85283927026878602 ep2091 85155596434197 562949953421312 42641963513439301 ep2089 (ep2110 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz803 qz979 5096603 562949953421312 1 562949953421312 556472078772145 562949953421312 42641963513439301 ep2089 2836117266086350523435 ep2030 ep2086 ep2032 (@Enclosure.Real.IsNear.recentre' qz803 Bool.false 5096603 562949953421312 1 562949953421312 5096603 562949953421312 1 562949953421312 (ep2090 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg (Real.sin qz416) Bool.true 556472078772145 562949953421312 42641963513439301 ep2089 (@Enclosure.Real.IsNear.recentre' (Real.sin qz416) Bool.true 556472078772145 562949953421312 85283927026878602 ep2091 556472078772145 562949953421312 42641963513439301 ep2089 (ep2116 rfl rfl) rfl)) rfl)

noncomputable def ep2118 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.im qz244) ep2034 30240000000000000000 0 1 2836117266086350523435 ep2030 ep2086 ep2032 ep2026

noncomputable def ep2119 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) Bool.false 164727776882963863841 2419200000000000 0 1 Bool.false ep2034 30240000000000000000 0 1 ep2084

noncomputable def ep2120 := @Enclosure.Complex.IsNear.im_isNear qz244 Bool.true 434004268253317732791 ep2030 ep2031 ep2032 Bool.false 2836117266086350523435 ep2030 ep2086 ep2032

noncomputable def ep2121 := nat_lit 93437458444358761050332200216572083922767

noncomputable def ep2122 := nat_lit 153335016603606628405041219722280960000000000

noncomputable def ep2123 := nat_lit 3751759320594550251114631361121131912246039761579

noncomputable def ep2124 := nat_lit 31378484121334178898446838185542661687901526425600000000000

noncomputable def ep2125 := nat_lit 896732305702324720883996605616002152946131649

noncomputable def ep2126 := nat_lit 1064826504191712697257230692515840000000000000000

noncomputable def ep2127 := nat_lit 21604835098523014538419472584615028355729045040387571

noncomputable def ep2128 := @Enclosure.Real.IsNear.addLit_ft_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.im qz244)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.re qz244)) ep2121 ep2122 ep2123 ep2124 ep2125 ep2126 ep2127

noncomputable def ep2129 := nat_lit 130743683838892412076861825773094423699589693440000000000000000

noncomputable def ep2130 := nat_lit 38005780747991450706577067611608016961612551368362298726311629101954797446103040000000000

noncomputable def ep2131 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.im qz244) 164727776882963863841 2419200000000000 0 1 2836117266086350523435 ep2030 ep2086 ep2032 ep2121

noncomputable def ep2132 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5)))) (Complex.re qz244) ep2034 30240000000000000000 0 1 434004268253317732791 ep2030 ep2031 ep2032 ep2125

noncomputable abbrev qz807 := (@ep2088 ep2032 (BSN.cpow_neg_s_sub_mk qz61 113311 1000 29 5 12200509765705829 (@Eq.refl Real qz61) rfl EMRow35.d187) ep2117)

noncomputable def ep2133 := ep2021 (@ep2028 ep2020 ep2029 ep2011 ep2012 ep2013 ep2014 (@ep2033 ep2023 ep2024 ep2025 ep2085 (ep2087 qz807) rfl) (@ep2118 ep2012 ep2027 ep2020 ep2119 (ep2120 qz807) rfl) rfl rfl) (@ep2128 ep2129 ep2130 ep2016 ep2017 ep2018 ep2020 (@ep2131 ep2122 ep2123 ep2124 ep2085 (ep2120 qz807) rfl) (@ep2132 ep2126 ep2127 ep2129 ep2119 (ep2087 qz807) rfl) rfl rfl)

noncomputable def ep2134 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244)) ep2016 ep2017 ep2018 ep2020 ep2016 ep2017 ep2018

noncomputable def ep2135 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244) Bool.true ep2011 ep2012 ep2013 ep2014 Bool.true ep2016 ep2017 ep2018

noncomputable def ep2136 := @ep1981 187546783914622176651 1623313478486440542208 38708208859709 1623313478486440542208 (@ep1982 1 5767168 (ep1983 (@ep1984 1048576 1 1048576 (ep1985 (@ep1986 51478530884 12869632721 1000000 0 1 (ep1990 rfl) (ep1993 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 11) rfl) (@ep1994 78037 70368744177664 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244)) (@ep1995 624296 562949953421312 1576618547869 281474976710656 78037 70368744177664 (@ep2000 1576618235721 1576618860017 281474976710656 (@ep2006 ep2007 ep2008 ep2009 ep2010 ep1996 ep1997 ep1998 ep1999 (@ep2015 ep2014 ep2001 ep2002 ep2003 ep2004 (@ep2019 ep2020 ep2133) (@ep2019 ep2020 ep2133) rfl) (@ep2134 ep2020 ep2005 ep2007 ep2008 ep2009 (@ep2135 ep2020 ep2133) (@ep2135 ep2020 ep2133) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow35.d188 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz608 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 2 4) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz64 2 29))) (@HMul.hMul Real Real Real qz0 qz796 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244)))) Bool.false ep1956 ep1957 80480168857323059069 ep1957 := ep1979 (ep1980 ep2136) rfl rfl

noncomputable def EMRow35.d189 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J))

noncomputable abbrev qz250 := (@Enclosure.dec_le_dec qz259 qz380 111131 1000 113311 1000 (@Eq.refl Real qz259) (@Eq.refl Real qz380) rfl rfl rfl)

noncomputable abbrev qz808 := (EMRow35.d3 qz11 qz61 qz250 28 29 2 2)

noncomputable def ep2137 := @Zeta.Certificates.ZIntervalEM.Certificate.mk qz808 (@Enclosure.dec_nonneg qz11 111131 1000 (@Eq.refl Real qz11)) (@Enclosure.pos_of_ble 2 rfl) (@Enclosure.pos_of_ble 28 rfl)

noncomputable def ep2138 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalEM.fstVal qz808) ep478 ep479

noncomputable def ep2139 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalEM.fstVal qz808) (hardyZApproximantEM 2 28 qz11) Bool.true

noncomputable def ep2140 := BSN.mul_neg_of_neg_pos_r (Zeta.Certificates.ZIntervalEM.fstVal qz808) (Zeta.Certificates.ZIntervalEM.sndVal qz808) (@ep2138 ep480 ep481 (@ep2139 ep478 ep479 ep480 ep481 (@Eq.refl Real (hardyZApproximantEM 2 28 qz11)) EMRow35.d15) rfl rfl rfl)

noncomputable def ep2141 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalEM.sndVal qz808) ep1217 ep1218

noncomputable def ep2142 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalEM.sndVal qz808) (hardyZApproximantEM 2 29 qz61) Bool.false

noncomputable def ep2143 := BSN.gt_trans_le (@Norm.norm Real Real.norm (Zeta.Certificates.ZIntervalEM.fstVal qz808)) (BSN.hardyZErrorBoundStrong 2 28 qz11)

noncomputable def ep2144 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalEM.fstVal qz808) (BSN.hardyZErrorBoundStrong 2 28 qz11) Bool.true

noncomputable def ep2145 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 2 28 qz11) (@HAdd.hAdd Real Real Real qz608 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 2 4) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz14 2 28))) (@HMul.hMul Real Real Real qz0 qz234 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236)))) Bool.false 528483276487793407422735 ep1755 8407395758686219005 ep1756 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz608 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 2 4) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz14 2 28))) (@HMul.hMul Real Real Real qz0 qz234 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz14 (@ascPochhammer Complex Complex.instSemiring 5))) qz236)))))

noncomputable def ep2146 := BSN.gt_trans_le (@Norm.norm Real Real.norm (Zeta.Certificates.ZIntervalEM.sndVal qz808)) (BSN.hardyZErrorBoundStrong 2 29 qz61)

noncomputable def ep2147 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalEM.sndVal qz808) (BSN.hardyZErrorBoundStrong 2 29 qz61) Bool.false

noncomputable def ep2148 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 2 29 qz61) (@HAdd.hAdd Real Real Real qz608 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 2 4) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz64 2 29))) (@HMul.hMul Real Real Real qz0 qz796 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244)))) Bool.false ep1956 ep1957 80480168857323059069 ep1957 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz608 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 2 4) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz64 2 29))) (@HMul.hMul Real Real Real qz0 qz796 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz3 (@HMul.hMul Complex Complex Complex qz3 (@HDiv.hDiv Complex Complex Complex qz27 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz233)) ↑qz235) (@Polynomial.eval Complex Complex.instSemiring qz64 (@ascPochhammer Complex Complex.instSemiring 5))) qz244)))))

noncomputable def ep2149 := @List.cons EMRow35.d0 (@PSigma.mk Zeta.Certificates.ZIntervalEM Zeta.Certificates.ZIntervalEM.Certificate qz808 (ep2137 (@Enclosure.pos_of_ble 2 rfl) (@Enclosure.pos_of_ble 29 rfl) (ep2140 (@ep2141 ep1219 ep1220 (@ep2142 ep1217 ep1218 ep1219 ep1220 (@Eq.refl Real (hardyZApproximantEM 2 29 qz61)) EMRow35.d23) rfl rfl rfl)) (ep2143 (hardyZErrorBoundEM 2 28 qz11) (BSN.hardyZErrorBoundEM_le_strong 2 28 qz11 rfl) (@ep2144 Bool.false ep478 ep479 ep480 ep481 528483276487793407422735 ep1755 8407395758686219005 ep1756 (@ep2139 ep478 ep479 ep480 ep481 (@Eq.refl Real (hardyZApproximantEM 2 28 qz11)) EMRow35.d15) (ep2145 EMRow35.d186) rfl rfl rfl rfl rfl)) (ep2146 (hardyZErrorBoundEM 2 29 qz61) (BSN.hardyZErrorBoundEM_le_strong 2 29 qz61 rfl) (@ep2147 Bool.false ep1217 ep1218 ep1219 ep1220 ep1956 ep1957 80480168857323059069 ep1957 (@ep2142 ep1217 ep1218 ep1219 ep1220 (@Eq.refl Real (hardyZApproximantEM 2 29 qz61)) EMRow35.d23) (ep2148 EMRow35.d188) rfl rfl rfl rfl rfl)))) (@List.nil EMRow35.d0)

noncomputable abbrev qz809 := (@NonemptyInterval Real Real.instLE)

noncomputable abbrev qz810 := (Zeta.Certificates.CertifiedZeroIntervals.intervals (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep2149 (@List.IsChain.singleton EMRow35.d1 EMRow35.d189 (EMRow35.d2 qz11 qz61 qz250))))

noncomputable def ep2150 := And (@Eq (Option Real) (@Option.map qz809 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz809 qz810)) (@Option.some Real qz11))

noncomputable def ep2151 := ep2150 (@Eq (Option Real) (@Option.map qz809 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz809 qz810)) (@Option.some Real qz61))

noncomputable def ep2152 := @And.intro (@Eq Nat (@List.length qz809 qz810) 1) ep2151

noncomputable def ep2153 := @And.intro (@Eq (Option Real) (@Option.map qz809 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz809 qz810)) (@Option.some Real qz11))

noncomputable def ep2154 := @ep2153 (@Eq (Option Real) (@Option.map qz809 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz809 qz810)) (@Option.some Real qz61))

noncomputable abbrev qz811 := (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep2149 (@List.IsChain.singleton EMRow35.d1 EMRow35.d189 (EMRow35.d2 qz11 qz61 qz250)))

theorem EMRow35.d190 : Zeta.Certificates.BatchSpec 1 111131 1000 113311 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz809 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 1) (And (@Eq (Option Real) (@Option.map qz809 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz809 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz11)) (@Eq (Option Real) (@Option.map qz809 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz809 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz61)))) qz811 (ep2152 (@Eq.refl Nat 1) (ep2154 (@Eq.refl (Option Real) (@Option.some Real qz11)) (@Eq.refl (Option Real) (@Option.some Real qz61))))

theorem solution : Zeta.Certificates.BatchSpec 1 111131 1000 113311 1000 := EMRow35.d190
#print axioms solution
#check solution
